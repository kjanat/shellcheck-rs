{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- | A GHC plugin that serialises each module's Core program to JSON after the
-- full optimisation pipeline has run (simplifier, demand analysis,
-- worker/wrapper, specialisation).
--
-- This is the front end of the Haskell-to-Rust compiler: GHC does the parsing,
-- type checking, desugaring and optimisation, and we consume the result.  The
-- dumped JSON carries the information the Rust backend needs to decide where
-- laziness can be erased -- in particular each binder's demand signature, CPR
-- signature, arity and occurrence info.
--
-- Usage:
--
-- > ghc -fplugin=H2R.CorePlugin -fplugin-opt=H2R.CorePlugin:outdir=core-json ...
module H2R.CorePlugin (plugin) where

import Control.Monad.IO.Class (liftIO)
import Data.Aeson
import qualified Data.ByteString.Lazy as BL
import Data.List (isPrefixOf, stripPrefix)
import Data.Maybe (fromMaybe)
import System.Directory (createDirectoryIfMissing)
import System.FilePath ((</>), (<.>))

import GHC.Plugins
import GHC.Types.Cpr (CprSig)
import GHC.Types.Demand (DmdSig)

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
        doc     = object
            [ "format"   .= (1 :: Int)
            , "module"   .= modName
            , "unit"     .= unitStr
            , "binds"    .= map (bindJ dflags) (mg_binds guts)
            ]
    liftIO $ do
        createDirectoryIfMissing True outDir
        BL.writeFile (outDir </> modName <.> "core.json") (encode doc)
    return guts

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
    [ "binder" .= binderJ dflags b
    , "rhs"    .= exprJ dflags e
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
        , "dmdSig"     .= sdoc dflags (ppr (idDmdSig v :: DmdSig))
        , "cprSig"     .= sdoc dflags (ppr (idCprSig v :: CprSig))
        , "demand"     .= sdoc dflags (ppr (idDemandInfo v))
        , "occInfo"    .= sdoc dflags (ppr (idOccInfo v))
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
            , "tag"  .= sdoc dflags (ppr (dataConTag dc))
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
