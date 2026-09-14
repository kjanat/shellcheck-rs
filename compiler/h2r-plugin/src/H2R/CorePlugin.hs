{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- | A GHC plugin that serialises each module's Core program to JSON after the
-- full optimisation pipeline has run (simplifier, demand analysis,
-- worker/wrapper, specialisation).
--
-- This is the front end of the Haskell-to-Rust compiler: GHC does the parsing,
-- type checking, desugaring and optimisation, and we consume the result.  The
-- dumped JSON carries the information the Rust backend needs to decide where
-- laziness can be erased: for every binder its demand (strict / absent /
-- used-once), occurrence info, one-shot info and signatures, and for every
-- right-hand side whether it is already a value.
--
-- Usage:
--
-- > ghc -fplugin=H2R.CorePlugin -fplugin-opt=H2R.CorePlugin:outdir=core-json ...
module H2R.CorePlugin (plugin) where

import Control.Monad.IO.Class (liftIO)
import Data.Aeson
import qualified Data.Aeson.Key as Key
import qualified Data.ByteString.Lazy as BL
import Data.List (stripPrefix)
import qualified Data.Map.Strict as M
import Data.Maybe (fromMaybe)
import System.Directory (createDirectoryIfMissing)
import System.FilePath ((</>), (<.>))

import GHC.Plugins
import GHC.Core.Utils (exprIsCheap, exprIsHNF, exprIsTrivial, exprOkForSpeculation)
import GHC.Types.Basic
import GHC.Types.Cpr (CprSig)
import GHC.Types.Demand
import GHC.Types.Id (idOneShotInfo)
import GHC.Types.Unique (getKey)

plugin :: Plugin
plugin = defaultPlugin
    { installCoreToDos = install
    , pluginRecompile  = purePlugin
    }

-- | Run last, so we see Core as it would be handed to CorePrep/STG.
install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install opts todos =
    return $ todos ++ [CoreDoPluginPass "H2RDumpCore" (dumpPass (optOutDir opts))]

optOutDir :: [CommandLineOption] -> FilePath
optOutDir opts =
    fromMaybe "core-json" $ lookupOpt "outdir="
  where
    lookupOpt prefix =
        case [rest | o <- opts, Just rest <- [stripPrefix prefix o]] of
            (x:_) -> Just x
            []    -> Nothing

dumpPass :: FilePath -> ModGuts -> CoreM ModGuts
dumpPass outDir guts = do
    dflags <- getDynFlags
    let modName = moduleNameString (moduleName (mg_module guts))
        unitStr = unitString (moduleUnit (mg_module guts))
        binds   = mg_binds guts
        doc     = object
            [ "format"   .= (4 :: Int)
            , "module"   .= modName
            , "unit"     .= unitStr
            , "ids"      .= idTable dflags binds
            , "binds"    .= map (bindJ dflags) binds
            ]
    liftIO $ do
        createDirectoryIfMissing True outDir
        BL.writeFile (outDir </> modName <.> "core.json") (encode doc)
    return guts

--------------------------------------------------------------------------------
-- Id table: facts about every Id *referenced* in the module, keyed by unique,
-- so a `Var` node stays small and callee strictness is one lookup away.
--------------------------------------------------------------------------------

idTable :: DynFlags -> CoreProgram -> Value
idTable dflags binds =
    object [ (Key.fromString (sdoc dflags (ppr (varUnique v))), idInfoJ dflags v)
           | v <- M.elems refs ]
  where
    refs = M.fromList [ (getKey (varUnique v), v) | v <- concatMap referenced binds, isId v ]

    referenced = \case
        NonRec _ e -> exprRefs e
        Rec ps     -> concatMap (exprRefs . snd) ps

    exprRefs = \case
        Var v         -> [v]
        Lit _         -> []
        App f a       -> exprRefs f ++ exprRefs a
        Lam _ e       -> exprRefs e
        Let b e       -> referenced b ++ exprRefs e
        Case s _ _ as -> exprRefs s ++ concat [exprRefs r | Alt _ _ r <- as]
        Cast e _      -> exprRefs e
        Tick _ e      -> exprRefs e
        Type _        -> []
        Coercion _    -> []

idInfoJ :: DynFlags -> Id -> Value
idInfoJ dflags v = object $
    [ "name"       .= nameStableString (varName v)
    , "occ"        .= getOccString v
    , "arity"      .= idArity v
    , "dmdSig"     .= dmdSigJ dflags (idDmdSig v)
    , "isJoinPoint" .= isJoinId v
    , "isClassOp"  .= isClassOpId v
    , "details"    .= sdoc dflags (ppr (idDetails v))
    -- For imported ids: can specialisation / inlining see the definition?
    , "hasUnfolding" .= hasSomeUnfolding (realIdUnfolding v)
    ] ++ case isDataConId_maybe v of
        Just dc ->
            [ "dataCon" .= object
                [ "name"     .= nameStableString (dataConName dc)
                , "repArity" .= dataConRepArity dc
                , "tag"      .= dataConTag dc
                , "strictFields" .= map (\m -> case m of { HsLazy -> False; _ -> True })
                                        (dataConImplBangs dc)
                ]
            ]
        Nothing -> []

--------------------------------------------------------------------------------
-- Core -> JSON
--------------------------------------------------------------------------------

sdoc :: DynFlags -> SDoc -> String
sdoc dflags = showSDocOneLine (initSDocContext dflags defaultUserStyle)

bindJ :: DynFlags -> CoreBind -> Value
bindJ dflags = \case
    NonRec b e -> object
        [ "rec"   .= False
        , "pairs" .= [pairJ dflags b e]
        ]
    Rec pairs -> object
        [ "rec"   .= True
        , "pairs" .= map (uncurry (pairJ dflags)) pairs
        ]

pairJ :: DynFlags -> CoreBndr -> CoreExpr -> Value
pairJ dflags b e = object
    [ "binder"  .= binderJ dflags b
    , "rhs"     .= exprJ dflags e
    -- Shape facts about the RHS, computed by GHC's own predicates.
    , "whnf"    .= exprIsHNF e
    , "trivial" .= exprIsTrivial e
    , "cheap"   .= exprIsCheap e
    -- No bottom, no side effects, cheap: safe to evaluate eagerly.
    , "okForSpec" .= exprOkForSpeculation e
    ]

-- | Everything the backend needs to know about a binder, including the
-- strictness facts GHC inferred for it.
binderJ :: DynFlags -> Var -> Value
binderJ dflags v
    | isId v = object $ common ++
        [ "kind"       .= ("id" :: String)
        , "arity"      .= idArity v
        , "callArity"  .= idCallArity v
        , "exported"   .= isExportedId v
        , "dmdSig"     .= dmdSigJ dflags (idDmdSig v)
        , "cprSig"     .= sdoc dflags (ppr (idCprSig v :: CprSig))
        -- How this binder itself is demanded at its binding site.
        , "demand"     .= demandJ dflags (idDemandInfo v)
        , "occInfo"    .= occInfoJ (idOccInfo v)
        , "oneShot"    .= isOneShotInfo (idOneShotInfo v)
        , "details"    .= sdoc dflags (ppr (idDetails v))
        , "hasUnfolding" .= hasSomeUnfolding (realIdUnfolding v)
        , "isJoinPoint"  .= isJoinId v
        , "isDataCon"    .= isDataConWorkId v
        ]
    | otherwise = object $ common ++
        [ "kind" .= ("tyvar" :: String) ]
  where
    common =
        [ "name"   .= nameStableString (varName v)
        , "occ"    .= getOccString v
        , "unique" .= sdoc dflags (ppr (varUnique v))
        , "type"   .= sdoc dflags (ppr (varType v))
        ]

-- | A demand, decomposed into the three facts the backend cares about.
demandJ :: DynFlags -> Demand -> Value
demandJ dflags d = object
    [ "strict"   .= isStrictDmd d
    , "absent"   .= isAbsDmd d
    , "usedOnce" .= (case d of n :* _ -> isUsedOnce n)
    , "pretty"   .= sdoc dflags (ppr d)
    ]

dmdSigJ :: DynFlags -> DmdSig -> Value
dmdSigJ dflags sig = object
    [ "args"      .= map (demandJ dflags) args
    , "diverges"  .= isDeadEndDiv divergence
    , "pretty"    .= sdoc dflags (ppr sig)
    ]
  where
    (args, divergence) = splitDmdSig sig

occInfoJ :: OccInfo -> Value
occInfoJ = \case
    IAmDead -> object [ "kind" .= ("dead" :: String) ]
    ManyOccs { occ_tail = t } -> object
        [ "kind" .= ("many" :: String)
        , "tailCalled" .= tailJ t
        ]
    OneOcc { occ_in_lam = il, occ_n_br = n, occ_tail = t } -> object
        [ "kind"       .= ("once" :: String)
        , "insideLam"  .= (il == IsInsideLam)
        , "branches"   .= n
        , "tailCalled" .= tailJ t
        ]
    IAmALoopBreaker { occ_tail = t } -> object
        [ "kind" .= ("loopBreaker" :: String)
        , "tailCalled" .= tailJ t
        ]
  where
    tailJ = \case
        AlwaysTailCalled _ -> True
        NoTailCallInfo     -> False

exprJ :: DynFlags -> CoreExpr -> Value
exprJ dflags = go
  where
    go = \case
        Var v -> object
            [ "node"     .= ("Var" :: String)
            , "name"     .= nameStableString (varName v)
            , "occ"      .= getOccString v
            , "unique"   .= sdoc dflags (ppr (varUnique v))
            , "isGlobal" .= isGlobalId v
            ]
        Lit l -> object
            [ "node" .= ("Lit" :: String)
            , "lit"  .= litJ dflags l
            ]
        App f a -> object
            [ "node" .= ("App" :: String)
            , "fun"  .= go f
            , "arg"  .= go a
            ]
        Lam b e -> object
            [ "node"   .= ("Lam" :: String)
            , "binder" .= binderJ dflags b
            , "body"   .= go e
            ]
        Let b e -> object
            [ "node" .= ("Let" :: String)
            , "bind" .= bindJ dflags b
            , "body" .= go e
            ]
        Case scrut b ty alts -> object
            [ "node"    .= ("Case" :: String)
            , "scrut"   .= go scrut
            , "binder"  .= binderJ dflags b
            , "type"    .= sdoc dflags (ppr ty)
            , "alts"    .= map altJ alts
            ]
        Cast e _co -> object
            [ "node" .= ("Cast" :: String)
            , "expr" .= go e
            ]
        Tick _t e -> object
            [ "node" .= ("Tick" :: String)
            , "expr" .= go e
            ]
        Type t -> object
            [ "node" .= ("Type" :: String)
            , "type" .= sdoc dflags (ppr t)
            ]
        Coercion _ -> object
            [ "node" .= ("Coercion" :: String) ]

    altJ (Alt con bs rhs) = object
        [ "con"     .= altConJ con
        , "binders" .= map (binderJ dflags) bs
        , "rhs"     .= go rhs
        ]

    altConJ = \case
        DataAlt dc -> object
            [ "kind" .= ("DataAlt" :: String)
            , "name" .= nameStableString (dataConName dc)
            , "occ"  .= getOccString (dataConName dc)
            , "tag"  .= dataConTag dc
            ]
        LitAlt l -> object
            [ "kind" .= ("LitAlt" :: String)
            , "lit"  .= litJ dflags l
            ]
        DEFAULT -> object [ "kind" .= ("DEFAULT" :: String) ]

litJ :: DynFlags -> Literal -> Value
litJ dflags l = object
    [ "kind"   .= litKind
    , "pretty" .= sdoc dflags (ppr l)
    ]
  where
    litKind :: String
    litKind = case l of
        LitChar{}   -> "char"
        LitNumber{} -> "number"
        LitString{} -> "string"
        LitFloat{}  -> "float"
        LitDouble{} -> "double"
        _           -> "other"
