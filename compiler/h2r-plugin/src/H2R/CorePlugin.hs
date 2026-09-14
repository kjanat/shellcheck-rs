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
-- Dump format 5 (see @compiler/rust/crates/h2r-core-ir/src/raw.rs@):
--
--   * The id table is keyed by /stable name/ (@$unit$Module$occ@) and holds
--     only global Ids.  Locals are resolved lexically by the Rust IR, and
--     nothing anywhere may key by a unique: GHC's simplifier duplicates
--     terms without freshening binders, so uniques are not unique in an
--     optimised dump.  Uniques are still emitted, as diagnostics only.
--   * Every type is emitted /structurally/, not only as a pretty string:
--     each module carries a hash-consed @types@ table and every binder,
--     @Type@ node and @Case@ result type carries an index into it.  The
--     pretty string stays alongside, for diagnostics.
--
-- Usage:
--
-- > ghc -fplugin=H2R.CorePlugin -fplugin-opt=H2R.CorePlugin:outdir=core-json ...
module H2R.CorePlugin (plugin) where

import Control.Monad.IO.Class (liftIO)
import Data.Aeson
import qualified Data.Aeson.Key as Key
import qualified Data.ByteString.Lazy as BL
import Data.List (foldl', stripPrefix)
import qualified Data.Map.Strict as M
import Data.Maybe (fromMaybe)
import System.Directory (createDirectoryIfMissing)
import System.FilePath ((</>), (<.>))

import GHC.Plugins
import GHC.Core.TyCo.Rep (TyLit (..), Type (..))
import GHC.Core.Type (expandTypeSynonyms)
import GHC.Core.Utils (exprIsCheap, exprIsHNF, exprIsTrivial, exprOkForSpeculation)
import GHC.Types.Basic
import GHC.Types.Cpr (CprSig)
import GHC.Types.Demand
import GHC.Types.Id (idOneShotInfo)

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
        tys     = tyTable dflags binds
        doc     = object
            [ "format"   .= (5 :: Int)
            , "module"   .= modName
            , "unit"     .= unitStr
            , "ids"      .= idTable dflags binds
            , "types"    .= tsValues tys
            , "binds"    .= map (bindJ dflags tys) binds
            ]
    liftIO $ do
        createDirectoryIfMissing True outDir
        BL.writeFile (outDir </> modName <.> "core.json") (encode doc)
    return guts

--------------------------------------------------------------------------------
-- Id table: facts about every *global* Id referenced in the module, keyed by
-- its stable name (@$unit$Module$occ@), so a `Var` node stays small and
-- callee strictness is one lookup away.
--
-- Only globals are in it, and the key is never a unique.  Uniques are not
-- unique in an optimised dump (the simplifier duplicates terms without
-- freshening binders), so anything keyed by one merges inlined copies of
-- different binders.  Locals do not need to be here at all: they are bound
-- somewhere in this module's Core and the Rust IR resolves every occurrence
-- of one lexically to its binder, which carries the authoritative `IdInfo`.
--
-- The top-level binders of the module being compiled are `LocalId`s at this
-- point in the pipeline (CoreTidy, which globalises them, runs after the
-- simplifier), so they are *not* in this table either — and they need not
-- be: they are bound in the module, so the lexical resolver owns them and
-- reads their binders.  Should a later GHC hand us an already-globalised
-- top-level binder, its entry would simply be keyed by the same stable name
-- the occurrence carries, and the lexical binder still wins.
--------------------------------------------------------------------------------

idTable :: DynFlags -> CoreProgram -> Value
idTable dflags binds =
    object [ (Key.fromString k, idInfoJ dflags v) | (k, v) <- M.toList refs ]
  where
    refs = M.fromList [ (nameStableString (varName v), v)
                      | v <- concatMap referenced binds, isId v, isGlobalId v ]

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

bindJ :: DynFlags -> TyS -> CoreBind -> Value
bindJ dflags tys = \case
    NonRec b e -> object
        [ "rec"   .= False
        , "pairs" .= [pairJ dflags tys b e]
        ]
    Rec pairs -> object
        [ "rec"   .= True
        , "pairs" .= map (uncurry (pairJ dflags tys)) pairs
        ]

pairJ :: DynFlags -> TyS -> CoreBndr -> CoreExpr -> Value
pairJ dflags tys b e = object
    [ "binder"  .= binderJ dflags tys b
    , "rhs"     .= exprJ dflags tys e
    -- Shape facts about the RHS, computed by GHC's own predicates.
    , "whnf"    .= exprIsHNF e
    , "trivial" .= exprIsTrivial e
    , "cheap"   .= exprIsCheap e
    -- No bottom, no side effects, cheap: safe to evaluate eagerly.
    , "okForSpec" .= exprOkForSpeculation e
    ]

-- | Everything the backend needs to know about a binder, including the
-- strictness facts GHC inferred for it.
binderJ :: DynFlags -> TyS -> Var -> Value
binderJ dflags tys v
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
        -- Diagnostics only: nothing may key by this (see `idTable`).
        , "unique" .= sdoc dflags (ppr (varUnique v))
        , "type"   .= sdoc dflags (ppr (varType v))
        , "ty"     .= tyIx dflags tys (varType v)
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

exprJ :: DynFlags -> TyS -> CoreExpr -> Value
exprJ dflags tys = go
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
            , "binder" .= binderJ dflags tys b
            , "body"   .= go e
            ]
        Let b e -> object
            [ "node" .= ("Let" :: String)
            , "bind" .= bindJ dflags tys b
            , "body" .= go e
            ]
        Case scrut b ty alts -> object
            [ "node"    .= ("Case" :: String)
            , "scrut"   .= go scrut
            , "binder"  .= binderJ dflags tys b
            , "type"    .= sdoc dflags (ppr ty)
            , "ty"      .= tyIx dflags tys ty
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
            , "ty"   .= tyIx dflags tys t
            ]
        Coercion _ -> object
            [ "node" .= ("Coercion" :: String) ]

    altJ (Alt con bs rhs) = object
        [ "con"     .= altConJ con
        , "binders" .= map (binderJ dflags tys) bs
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

--------------------------------------------------------------------------------
-- Structured types
--------------------------------------------------------------------------------
--
-- The dump used to carry only GHC's pretty-printed rendering of each type,
-- which made every type-based fact a *textual* comparison.  Format 5 emits
-- the `Type` itself, so "the element is `Char`" is `TyConApp` with a stable
-- `TyCon` name rather than the string @"Char"@.
--
-- Types are hash-consed into one table per module and referenced by index:
-- a module has tens of thousands of type occurrences over only ~1k distinct
-- types, so inlining them would multiply the dump several times over, and
-- the flat table is also what lets the Rust side rebuild them iteratively.
-- Every child index is smaller than its parent's, because a node is
-- interned only after its children are.
--
-- **Which form is emitted:** the `expandTypeSynonyms` form.  GHC's Core
-- types still contain type synonyms (`String`, `FilePath`, `ShowS`, …), and
-- a consumer that has to know whether a synonym is @[Char]@ would be back to
-- reading names.  Expanding once here means `String` and `FilePath` both
-- arrive as @TyConApp List [TyConApp Char []]@.  The unexpanded rendering
-- stays in the sibling @"type"@ field, which is what diagnostics print.

-- | A structural key for a type node whose children have already been
-- interned.  Equal keys mean equal types, so the table is hash-consed.
data TyKey
    = KVar    !String !String        -- ^ stable name, unique
    | KCon    !String !String [Int]  -- ^ tycon stable name, unique, args
    | KApp    !Int !Int
    | KFun    !Int !Int !Int         -- ^ multiplicity, argument, result
    | KAll    !String !String !Int   -- ^ binder stable name, unique, body
    | KLit    !String !String        -- ^ literal kind, literal text
    | KOpaque !String                -- ^ a cast or a coercion, pretty-printed
    deriving (Eq, Ord)

-- | The interning table: keys to indices, and the emitted nodes in reverse.
data TyS = TyS
    { tsMap :: !(M.Map TyKey Int)
    , tsRev :: [Value]
    , tsLen :: !Int
    }

emptyTyS :: TyS
emptyTyS = TyS M.empty [] 0

-- | The table, in index order.
tsValues :: TyS -> Value
tsValues = toJSON . reverse . tsRev

intern :: TyKey -> Value -> TyS -> (Int, TyS)
intern k v s = case M.lookup k (tsMap s) of
    Just i  -> (i, s)
    Nothing ->
        let i = tsLen s
        in (i, TyS { tsMap = M.insert k i (tsMap s)
                   , tsRev = v : tsRev s
                   , tsLen = i + 1
                   })

-- | Intern one type and all of its subterms.  Synonyms are expanded by the
-- caller ('tyTable' / 'tyIx'), once, at the top.
internTy :: DynFlags -> TyS -> Type -> (Int, TyS)
internTy dflags = go
  where
    uq :: Uniquable a => a -> String
    uq = sdoc dflags . ppr . getUnique

    str :: String -> String
    str = id

    go s0 ty = case ty of
        TyVarTy v ->
            let n = nameStableString (varName v)
                u = uq v
            in intern (KVar n u)
                 (object [ "kind"   .= str "TyVar"
                         , "name"   .= n
                         , "occ"    .= getOccString v
                         , "unique" .= u
                         ]) s0
        TyConApp tc args ->
            let (is, s1) = goMany s0 args
                nm = tyConName tc
                n  = nameStableString nm
                u  = uq tc
            in intern (KCon n u is)
                 (object [ "kind"  .= str "TyConApp"
                         , "tycon" .= object [ "name"   .= n
                                             , "occ"    .= getOccString nm
                                             , "unique" .= u
                                             ]
                         , "args"  .= is
                         ]) s1
        AppTy f a ->
            let (i1, s1) = go s0 f
                (i2, s2) = go s1 a
            in intern (KApp i1 i2)
                 (object [ "kind" .= str "AppTy", "fun" .= i1, "arg" .= i2 ]) s2
        FunTy { ft_mult = mult, ft_arg = a, ft_res = r } ->
            let (im, s1) = go s0 mult
                (ia, s2) = go s1 a
                (ir, s3) = go s2 r
            in intern (KFun im ia ir)
                 (object [ "kind" .= str "FunTy"
                         , "mult" .= im, "arg" .= ia, "res" .= ir
                         ]) s3
        ForAllTy bndr body ->
            let v = binderVar bndr
                n = nameStableString (varName v)
                u = uq v
                (ib, s1) = go s0 body
            in intern (KAll n u ib)
                 (object [ "kind"   .= str "ForAllTy"
                         , "binder" .= object [ "name"   .= n
                                              , "occ"    .= getOccString v
                                              , "unique" .= u
                                              ]
                         , "body"   .= ib
                         ]) s1
        LitTy tl ->
            let (k, t) = case tl of
                    NumTyLit n  -> (str "num",  show n)
                    StrTyLit fs -> (str "str",  unpackFS fs)
                    CharTyLit c -> (str "char", [c])
            in intern (KLit k t)
                 (object [ "kind" .= str "LitTy", "litKind" .= k, "lit" .= t ]) s0
        -- A cast or a coercion carries no information this pipeline reads.
        CastTy{}     -> opaque s0 ty
        CoercionTy{} -> opaque s0 ty

    opaque s ty =
        let p = sdoc dflags (ppr ty)
        in intern (KOpaque p) (object [ "kind" .= str "Opaque", "pretty" .= p ]) s

    goMany s [] = ([], s)
    goMany s (t:ts) =
        let (i, s1)  = go s t
            (is, s2) = goMany s1 ts
        in (i : is, s2)

-- | Every type that appears anywhere in the program, in emission order.
collectTys :: CoreProgram -> [Type]
collectTys binds = concatMap bindTys binds
  where
    bindTys = \case
        NonRec b e -> varType b : exprTys e
        Rec ps     -> concat [ varType b : exprTys e | (b, e) <- ps ]

    exprTys = \case
        Var _          -> []
        Lit _          -> []
        App f a        -> exprTys f ++ exprTys a
        Lam b e        -> varType b : exprTys e
        Let b e        -> bindTys b ++ exprTys e
        Case s b ty as -> exprTys s ++ [varType b, ty]
                            ++ concat [ map varType bs ++ exprTys r
                                      | Alt _ bs r <- as ]
        Cast e _       -> exprTys e
        Tick _ e       -> exprTys e
        Type t         -> [t]
        Coercion _     -> []

-- | The module's type table: every type in the program, interned.
tyTable :: DynFlags -> CoreProgram -> TyS
tyTable dflags binds =
    foldl' (\s t -> snd (internTy dflags s (expandTypeSynonyms t))) emptyTyS
           (collectTys binds)

-- | The index of a type in a table that already contains it.  'tyTable' is
-- built from exactly the types 'collectTys' yields, which is exactly the set
-- the emitters ask about, so this is always a lookup; interning is pure, so
-- running it against the finished table cannot disturb it.
tyIx :: DynFlags -> TyS -> Type -> Int
tyIx dflags tys t = fst (internTy dflags tys (expandTypeSynonyms t))
