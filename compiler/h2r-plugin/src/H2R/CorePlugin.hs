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
-- __Which program is serialised.__  The /structure and the names/ are
-- CoreTidy's — the program GHC hands to codegen — so a top-level binding
-- carries, in its own module's dump, the very name every downstream module
-- refers to it by.  The /IdInfo/ is the pre-tidy one, joined back on binder
-- by binder, because CoreTidy rebuilds every nested binder's `IdInfo` from
-- `vanillaIdInfo` and would otherwise throw GHC's demand analysis away on
-- every lambda, case and alternative binder.  See 'dumpPass' and the
-- alignment section below.
--
-- Dump format 5 (see @compiler/rust/crates/h2r-core-ir/src/raw.rs@):
--
--   * The id table is keyed by /stable name/ (@$unit$Module$occ@) and holds
--     only global Ids with /external/ names.  Locals are resolved lexically
--     by the Rust IR, and nothing anywhere may key by a unique: GHC's
--     simplifier duplicates terms without freshening binders, so uniques
--     are not unique in an optimised dump.  Uniques are still emitted, as
--     diagnostics only.
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
import Data.List (foldl', intercalate, stripPrefix)
import qualified Data.Map.Strict as M
import Data.Bits (xor)
import qualified Data.Set as S
import Data.Maybe (fromMaybe, isJust)
import System.Directory (createDirectoryIfMissing)
import System.FilePath ((</>), (<.>))
import System.IO (IOMode (WriteMode), hPutStr, hPutStrLn, hSetEncoding, stderr,
                  utf8, withFile)

import GHC.Plugins
import GHC.Core.DataCon (dataConFullSig)
import GHC.Core.TyCo.Rep (TyLit (..), Type (..))
import GHC.Core.Type (expandTypeSynonyms)
import GHC.Core.Utils (exprIsCheap, exprIsHNF, exprIsTrivial, exprOkForSpeculation)
import GHC.Driver.Config.Tidy (initTidyOpts)
import GHC.Iface.Tidy (TidyOpts (..), tidyProgram)
import GHC.Types.Avail (availsToNameSet)
import GHC.Types.Basic
import GHC.Types.Cpr (CprSig)
import GHC.Types.Demand
import GHC.Types.Id (idOneShotInfo)
import GHC.Types.Unique (getKey)
import GHC.Word (Word64)

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

-- | Serialise the module's Core with __CoreTidy's structure, names and
-- finalised @IdInfo@, and the pre-tidy facts CoreTidy discards joined back
-- on, field by field__.
--
-- The pass is appended at the end of @installCoreToDos@, which puts it
-- immediately before the driver's own CoreTidy — and CoreTidy is where GHC
-- decides which top-level binders become external and rewrites them.  A dump
-- taken before it carries @$_in$$wchecker@ for a binding that every
-- downstream module, which reads the tidied interface, calls
-- @$\<unit\>$ShellCheck.Checks.Commands$$wchecker@; the closed world then
-- cannot see that the two names are one binding.  So we run CoreTidy
-- ourselves, serialise its result, and hand the pipeline back the
-- /original/ 'ModGuts': the extraction must not substitute its own tidy
-- product into the normal compilation.
--
-- __What CoreTidy owns, and what is joined back.__  CoreTidy is not only a
-- renamer: @tidyTopIdInfo@ (@Iface/Tidy.hs:1223-1263@) finalises the arity
-- codegen will rely on, finalises the demand and CPR signatures, robustifies
-- the occurrence info (@zapFragileOcc@) and chooses the unfolding that
-- reaches the interface, and @tidyCbvInfoTop@ \/ @tidyCbvInfoLocal@
-- (@Core/Tidy.hs:110-118@) put the call-by-value marks on the `IdDetails`
-- codegen reads.  Replacing all of that with the pre-tidy `IdInfo` would undo
-- genuine codegen-facing work, so the emitted binder takes it from the tidied
-- side.  The join supplies only the /proof facts CoreTidy discards/:
--
--   [@demand@ (the per-binder `DemandInfo`)] taken __pre-tidy__ on
--     __top-level, lambda, case and alternative__ binders.  Dropped by
--     @tidyIdBndr@ (@Core/Tidy.hs:305-308@: @vanillaIdInfo@ + @setOccInfo@,
--     @setUnfoldingInfo@, @setOneShotInfo@, and nothing else) for lambda,
--     case and alternative binders, and by @tidyTopIdInfo@
--     (@Iface/Tidy.hs:1225-1241@, whose setter list has no
--     @setDemandInfo@) at the top level.  Kept by @tidyLetBndr@
--     (@Core/Tidy.hs:356@, @setDemandInfo demandInfo old_info@), so a
--     __let__ binder's demand is taken post-tidy.  Read by
--     @h2r-analysis/src/fields.rs:883@ (M2.3b, alternative binder),
--     @lists/mod.rs:1359@ (M2.3c, alternative binder),
--     @dictflow.rs:1623,2267@ (M2.4c, lambda binder) and
--     @classops.rs:960@ (M2.4b, lambda binder).  It is GHC's demand
--     analysis and nothing on the Rust side can recompute it.
--
--   [@oneShot@ (the `OneShotInfo`)] taken __pre-tidy__ on __top-level and
--     let__ binders, where neither @tidyTopIdInfo@ nor @tidyLetBndr@ puts it
--     back (their setter lists, @Iface/Tidy.hs:1225-1241@ and
--     @Core/Tidy.hs:352-358@, have no @setOneShotInfo@).  __Lambda__ binders
--     keep it — @tidyIdBndr@ sets it explicitly (@Core/Tidy.hs:308@, "see
--     Note [Preserve OneShotInfo]") — so there it is taken post-tidy, which
--     is the binder class @h2r-analysis/src/laziness.rs:421@
--     (@transparent_lambda@, M1) reads it on.
--
--   [@exported@] taken __pre-tidy__ on top-level binders: see 'topBindJ'.
--
-- Everything else — @arity@, @callArity@, @dmdSig@, @cprSig@, @occInfo@,
-- @details@, @hasUnfolding@, @isJoinPoint@, @isDataCon@, the type — is the
-- tidied binder's.  Two fields CoreTidy does drop are deliberately /not/
-- joined, because no analysis reads them: @cprSig@ on a __let__ binder
-- (@tidyLetBndr@ has no @setCprSigInfo@; 38 binders in the @-O1@ world) and
-- @callArity@ (dropped everywhere, and 0 on every binder of every class in
-- the @-O1@ world).  The only consumer of either is the @h2r stats@ census
-- column, which is a report, not a proof.  The census in
-- @compiler/README.md@ states, per field, which side owns it.
--
-- Three facts about CoreTidy make the join exact; each is read from GHC
-- 9.6.7's own source, cited by file and line:
--
--   (a) __@tidyExpr@ is structure-preserving.__  @Core/Tidy.hs:207-233@:
--       @Var@, @Lit@, @App@, @Lam@, @Let@, @Case@, @Cast@, @Tick@, @Type@
--       and @Coercion@ each map to the same constructor, and @tidyAlt@
--       (@:230@) rebuilds an @Alt@ with the same @AltCon@ and the same number
--       of binders, under @map (tidyAlt env') alts@ (@:223@), which keeps
--       the alternatives in order.  So a pre-tidy right-hand side and its
--       tidied counterpart are the same tree, node for node.
--
--   (b) __Nested binders keep their @Unique@; top-level binders do not.__
--       @tidyIdBndr@ (@Core/Tidy.hs:300@) and @tidyLetBndr@
--       (@Core/Tidy.hs:326@) both build @mkInternalName (idUnique id) occ'
--       noSrcSpan@ — the occurrence name is freshened, the unique is the old
--       one.  @tidyVarBndr@ does the same for type and coercion variables.
--       At the top level @tidyTopName@ (@Iface/Tidy.hs:1069-1093@) takes a
--       /fresh/ unique from the name cache for every name that was local:
--       @takeUniqFromNameCache@ (@:1084@) when it stays internal,
--       @allocateGlobalBinder@ (@:1092@) when it is externalised.  Only names
--       that were already global keep theirs (@:1073-1074@) — which is why
--       an import occurrence is the same `Var` before and after, a fact the
--       alignment log counts.
--
--   (c) __Order is preserved end to end; implicit bindings are a prefix; a
--       trimmed binding has no exported binder.__  @tidyProgram@
--       (@Iface/Tidy.hs:381-387@) builds @all_binds = implicit_binds ++
--       binds@, where @implicit_binds = concatMap getImplicitBinds tcs@
--       (@:381@) — @getImplicitBinds@ (@:611-626@) yields exactly the class
--       selectors (@getClassImplicitBinds@, `ClassOpId`) and the data
--       constructor /wrappers/ (@getTyConImplicitBinds@, `DataConWrapId`);
--       workers are never Core bindings.  @findExternalRules@ (@:976-1050@)
--       then filters that list with @trim_binds@, which keeps a @CoreBind@
--       group whole when @any needed bndrs@ and discards it whole otherwise
--       (@:1039-1045@) — and @needed bndr = isExportedId bndr || bndr
--       \`elemVarSet\` needed_fvs@ (@:1046@), so __a trimmed binding never has
--       an exported binder__, which this pass asserts.  @tidyTopBinds@ is
--       @mapAccumL tidyTopBind@ (@:1165@), one tidied group per input group
--       in order, and @tidyTopBind@ keeps @NonRec@\/@Rec@ and the order of a
--       @Rec@ group's pairs (@:1174-1190@).  The only thing that can be
--       inserted afterwards is @sptCreateStaticBinds@ (@:390-392@), which
--       runs only when @StaticPointers@ is on
--       (@Driver/Config/Tidy.hs:33-35@); the pass reads
--       @opt_static_ptr_opts@ and reports whether it could have.
--
-- __The alignment theorem, asserted per module.__  From (c) the alignment is
-- a two-pointer merge over @mg_binds@ and @cg_binds@ in order.  Order alone
-- would leave "we took the first structural match" as the justification, so
-- the pass also proves uniqueness independently of order, with a
-- /fingerprint/ CoreTidy preserves exactly: the expression-constructor tree,
-- every nested binder's `Unique`, every literal, every `AltCon`, and the
-- stable name of every global occurrence.  It then asserts, and the sidecar
-- log reports:
--
--   * every aligned tidied binding has __exactly one__ pre-tidy binding of
--     the same fingerprint, or, where several pre-tidy bindings are
--     structurally indistinguishable, that __all of them carry the same
--     joined facts__, so the tie cannot change a byte of the dump.  A tie
--     that is not vacuous in that sense aborts the extraction.
--   * every aligned pair passes the strict lockstep zip ('zipBind') — node
--     for node, alternative for alternative, binder for binder with equal
--     uniques — before any field is merged.  A mismatch aborts.
--   * every unmatched pre-tidy group is a @trim_binds@ trim, and has no
--     exported binder; a counter-example aborts.
--   * every unmatched tidied group is a @getImplicitBinds@ injection,
--     identified by `IdDetails`; anything else aborts, and the log records
--     whether SPT insertion was even possible.
--
-- Nothing is keyed by a unique across the module — uniques are not unique in
-- optimised Core, and two copies of one binder can carry different demands;
-- the zip is positional inside one aligned pair, and the fingerprint is
-- compared whole.
--
-- __This extra tidy is not side-effect free, and must not be described as if
-- it were.__  'tidyProgram' allocates names through the process-global name
-- cache (@takeUniqFromNameCache@ \/ @allocateGlobalBinder@), so it consumes
-- uniques the driver's own later tidy would otherwise have had.  Measured,
-- not assumed: against a build with the plugin but without the extra tidy,
-- the external names it picks /are/ the ones the driver reuses — @ABI hash@
-- and @export-list hash@ are unchanged on all 27 modules, and the executable
-- behaves identically over 117 invocations across every formatter.  What does
-- move is internal uniques: of the 8,793 defined symbols across the 27 object
-- files, the only ones that differ are the @\<unique\>_str@ string-literal
-- symbols and the local @.Lr\<unique\>_bytes@ labels, whose /names are
-- internal uniques/.
--
-- 'tidyProgram' also does more than rename: it trims bindings kept alive only
-- by rules it cannot use, and it injects the implicit bindings.  That is
-- wanted — the dump becomes the program GHC itself hands to codegen, so a
-- class-op selector or a constructor wrapper another module refers to is a
-- real top-level binding of this one.
dumpPass :: FilePath -> ModGuts -> CoreM ModGuts
dumpPass outDir guts = do
    dflags   <- getDynFlags
    hscEnv   <- getHscEnv
    tidyOpts <- liftIO (initTidyOpts hscEnv)
    (cgGuts, _details) <- liftIO (tidyProgram tidyOpts guts)
    let modName   = moduleNameString (moduleName (mg_module guts))
        unitStr   = unitString (moduleUnit (mg_module guts))
        exportSet = availsToNameSet (mg_exports guts)
        preBinds  = mg_binds guts
        sptOn     = isJust (opt_static_ptr_opts tidyOpts)
        (slots, mergeErrs) = alignProgram preBinds (cg_binds cgGuts)
        facts     = alignFacts dflags sptOn preBinds slots mergeErrs
        rep       = report modName exportSet facts slots
    case afErrs facts of
        (e:_) -> error ("h2r-plugin: " ++ modName ++ ": the tidy alignment failed: " ++ e)
        []    -> return ()
    liftIO $ do
        createDirectoryIfMissing True outDir
        BL.writeFile (outDir </> modName <.> "core.json")
                     (encode (moduleJ dflags modName unitStr exportSet slots))
        -- Explicit UTF-8: the compiler's locale need not be one, and the
        -- log carries GHC's own pretty-printed output.
        withFile (outDir </> modName <.> "tidy-align" <.> "txt") WriteMode $ \h ->
            hSetEncoding h utf8 >> hPutStr h rep
        hPutStrLn stderr ("h2r-plugin: " ++ modName ++ ": " ++ summary facts)
    -- The ORIGINAL guts: the pipeline must see its own CoreTidy, not ours.
    return guts

-- | The whole dump document for one module's program.  The bindings are the
-- tidied ones; 'slots' carries each one's pre-tidy counterpart, when it has
-- one, for the @IdInfo@ join.
--
-- __Dump format 6.__  Format 5 was the pre-CoreTidy program.  Format 6 is
-- the post-CoreTidy one: tidied names and structure, the implicit bindings
-- present and the rule-only-live ones trimmed, an id table of external names
-- only, and the joined pre-tidy @demand@ \/ @oneShot@ \/ @exported@ on the
-- binders.  Every format-5 field keeps its name and shape; the two added
-- ones (@externalName@, @sourceExported@) are diagnostics.  A format-5
-- consumer must not read a format-6 dump as the old contract, which is the
-- whole reason for the bump.
moduleJ :: DynFlags -> String -> String -> NameSet -> [Slot] -> Value
moduleJ dflags modName unitStr exportSet slots = object
    [ "format"   .= (6 :: Int)
    , "module"   .= modName
    , "unit"     .= unitStr
    , "ids"      .= idTable dflags binds
    , "types"    .= tsValues tys
    , "constructors" .= map (constructorJ dflags tys) (programConstructors binds)
    , "binds"    .= map (topBindJ dflags tys exportSet) emitted
    ]
  where
    emitted = filter isEmitted slots
    binds   = map slotTidy emitted
    tys     = tyTable dflags binds

--------------------------------------------------------------------------------
-- The alignment: tidied structure, pre-tidy IdInfo
--------------------------------------------------------------------------------

-- | One top-level binding of the emitted (tidied) program, with the pre-tidy
-- binding it came from — or the reason it has none.
data Slot
    = Aligned CoreBind CoreBind  -- ^ pre-tidy, tidied
    | Implicit CoreBind          -- ^ injected by @getImplicitBinds@
    | Dropped CoreBind           -- ^ discarded by @trim_binds@; not emitted

-- | A slot that contributes a binding to the dump.  A 'Dropped' one does
-- not: 'trim_binds' discarded it before codegen ever saw it.
isEmitted :: Slot -> Bool
isEmitted Dropped{} = False
isEmitted _         = True

-- | The tidied binding a slot emits.  Only ever called on an emitted slot.
slotTidy :: Slot -> CoreBind
slotTidy (Aligned _ t) = t
slotTidy (Implicit t)  = t
slotTidy (Dropped _)   = error "h2r-plugin: a dropped binding reached the emitter"

-- | A tidied top-level binding GHC injected rather than compiled: its binders
-- are the implicit ids 'getImplicitBinds' produces (class-op selectors and
-- data-constructor wrappers).  Nothing in @mg_binds@ has such a binder, so
-- this classification does not depend on the structural match.
isImplicitBind :: CoreBind -> Bool
isImplicitBind b = not (null bs) && all implicitBndr bs
  where
    bs = bindersOf b
    implicitBndr v = isClassOpId v || isDataConWrapId v

-- | The two-pointer merge.  Returns the emission plan in tidied order (plus
-- the dropped pre-tidy bindings, for the log) and any error that makes the
-- alignment unsound.
alignProgram :: [CoreBind] -> [CoreBind] -> ([Slot], [String])
alignProgram = go
  where
    go ps [] = (map Dropped ps, [])
    go [] (t:ts) =
        let (ss, es) = go [] ts
            es' | isImplicitBind t = es
                | otherwise = ("a tidied binding has no pre-tidy counterpart and is not \
                               \implicit: " ++ bindLabel t) : es
        in (Implicit t : ss, es')
    go (p:ps) (t:ts)
        | Nothing <- zipBind p t = let (ss, es) = go ps ts in (Aligned p t : ss, es)
        | isImplicitBind t       = let (ss, es) = go (p:ps) ts in (Implicit t : ss, es)
        | otherwise              = let (ss, es) = go ps (t:ts) in (Dropped p : ss, es)

-- | A label for a binding, for an error message or the alignment log: the
-- binders' occurrence names with their uniques.
bindLabel :: CoreBind -> String
bindLabel b = intercalate ", "
    [ getOccString v ++ "_" ++ show (varUnique v) | v <- bindersOf b ]

--------------------------------------------------------------------------------
-- The lockstep zip
--------------------------------------------------------------------------------
--
-- The check that every aligned pair really is one binding tidied.  It is
-- positional and total: every node of the pre-tidy tree is matched against
-- the node in the same position of the tidied tree, every alternative against
-- the alternative in the same position, every binder against the binder in
-- the same position — and binders must carry the same `Unique`, which fact
-- (b) above says they do for every binder tidy renames in place.  The first
-- mismatch is returned; `Nothing` means the trees agree.

-- | 'Nothing' when the two bindings are one binding, tidied.
zipBind :: CoreBind -> CoreBind -> Maybe String
zipBind (NonRec b1 e1) (NonRec b2 e2) = zipBndr b1 b2 `orElse'` zipExpr e1 e2
zipBind (Rec ps1) (Rec ps2)
    | length ps1 /= length ps2 =
        Just ("recursive group of " ++ show (length ps1) ++ " tidied to "
              ++ show (length ps2))
    | otherwise = firstJust
        [ zipBndr b1 b2 `orElse'` zipExpr e1 e2
        | ((b1, e1), (b2, e2)) <- zip ps1 ps2 ]
zipBind b1 b2 = Just ("binding kind: " ++ recKind b1 ++ " vs " ++ recKind b2)
  where recKind NonRec{} = "NonRec"
        recKind Rec{}    = "Rec"

-- | Two binders in the same position.  Top-level binders are renamed and
-- re-uniqued, so this is used for nested binders only — where fact (b) says
-- the unique survives — and for the /kind/ of a top-level binder.
zipBndr :: Var -> Var -> Maybe String
zipBndr v1 v2
    | isId v1 /= isId v2 = Just (varLabel v1 ++ " vs " ++ varLabel v2 ++ ": id/tyvar")
    | otherwise          = Nothing

-- | The same, also asserting the unique: for a nested binder tidy keeps it.
zipNestedBndr :: Var -> Var -> Maybe String
zipNestedBndr v1 v2
    | Just e <- zipBndr v1 v2 = Just e
    | varUnique v1 /= varUnique v2 =
        Just ("nested binder " ++ varLabel v1 ++ " tidied to " ++ varLabel v2
              ++ ": the unique moved")
    | otherwise = Nothing

varLabel :: Var -> String
varLabel v = getOccString v ++ "_" ++ show (varUnique v)

-- | 'Nothing' when the two expressions are one expression, tidied.
zipExpr :: CoreExpr -> CoreExpr -> Maybe String
zipExpr (Var _) (Var _)   = Nothing
zipExpr (Lit l1) (Lit l2)
    | l1 == l2  = Nothing
    | otherwise = Just "literal changed"
zipExpr (App f1 a1) (App f2 a2) = zipExpr f1 f2 `orElse'` zipExpr a1 a2
zipExpr (Lam b1 e1) (Lam b2 e2) = zipNestedBndr b1 b2 `orElse'` zipExpr e1 e2
zipExpr (Let b1 e1) (Let b2 e2) = zipLetBind b1 b2 `orElse'` zipExpr e1 e2
zipExpr (Case s1 b1 _ as1) (Case s2 b2 _ as2)
    | length as1 /= length as2 =
        Just ("case with " ++ show (length as1) ++ " alternative(s) tidied to "
              ++ show (length as2))
    | otherwise = zipExpr s1 s2 `orElse'` zipNestedBndr b1 b2 `orElse'` firstJust
        [ zipAlt a1 a2 | (a1, a2) <- zip as1 as2 ]
zipExpr (Cast e1 _) (Cast e2 _) = zipExpr e1 e2
zipExpr (Tick _ e1) (Tick _ e2) = zipExpr e1 e2
zipExpr (Type _) (Type _)       = Nothing
zipExpr (Coercion _) (Coercion _) = Nothing
zipExpr e1 e2 = Just ("node: " ++ nodeKind e1 ++ " vs " ++ nodeKind e2)

-- | A nested @let@ or @letrec@: like 'zipBind', but its binders are nested,
-- so their uniques must agree too.
zipLetBind :: CoreBind -> CoreBind -> Maybe String
zipLetBind (NonRec b1 e1) (NonRec b2 e2) = zipNestedBndr b1 b2 `orElse'` zipExpr e1 e2
zipLetBind (Rec ps1) (Rec ps2)
    | length ps1 /= length ps2 =
        Just ("let-recursive group of " ++ show (length ps1) ++ " tidied to "
              ++ show (length ps2))
    | otherwise = firstJust
        [ zipNestedBndr b1 b2 `orElse'` zipExpr e1 e2
        | ((b1, e1), (b2, e2)) <- zip ps1 ps2 ]
zipLetBind _ _ = Just "let binding kind changed"

zipAlt :: CoreAlt -> CoreAlt -> Maybe String
zipAlt (Alt c1 bs1 r1) (Alt c2 bs2 r2)
    | c1 /= c2 = Just "alternative constructor changed"
    | length bs1 /= length bs2 =
        Just ("alternative with " ++ show (length bs1) ++ " binder(s) tidied to "
              ++ show (length bs2))
    | otherwise = firstJust [ zipNestedBndr b1 b2 | (b1, b2) <- zip bs1 bs2 ]
                    `orElse'` zipExpr r1 r2

nodeKind :: CoreExpr -> String
nodeKind Var{}      = "Var"
nodeKind Lit{}      = "Lit"
nodeKind App{}      = "App"
nodeKind Lam{}      = "Lam"
nodeKind Let{}      = "Let"
nodeKind Case{}     = "Case"
nodeKind Cast{}     = "Cast"
nodeKind Tick{}     = "Tick"
nodeKind Type{}     = "Type"
nodeKind Coercion{} = "Coercion"

orElse' :: Maybe a -> Maybe a -> Maybe a
orElse' (Just x) _ = Just x
orElse' Nothing  y = y

firstJust :: [Maybe a] -> Maybe a
firstJust xs = case [x | Just x <- xs] of
    (x:_) -> Just x
    []    -> Nothing

--------------------------------------------------------------------------------
-- The alignment theorem: uniqueness, attribution, and the assertions
--------------------------------------------------------------------------------

-- | A structural fingerprint of a top-level binding that CoreTidy preserves
-- exactly.
--
-- The tokens carry the expression-constructor tree, every /nested/ binder's
-- `Unique` (fact (b): tidy keeps those), every literal, every `AltCon`, and
-- the stable name of every occurrence of an /import/ or of one of the
-- implicit ids (fact (b) again: an already-external name is returned
-- unchanged).  They deliberately carry nothing tidy rewrites: not the
-- top-level binder's own unique or occurrence name, not types, not `IdInfo`.
--
-- An occurrence of one of this module's /own/ top-level bindings is the one
-- thing that cannot be fingerprinted directly — tidy reallocates its unique
-- and may rename it — so it is a __hole__ ('SkRef'), filled by the
-- fingerprint of the binding it points at.  'refineColours' closes that
-- recursion the way partition refinement does: every binding starts with the
-- same colour, each round re-fingerprints with the previous round's colours
-- in the holes, and the rounds stop when the partition stops splitting.  The
-- two programs are coloured __together__, in one shared numbering, so a
-- colour means the same thing on both sides of the tidy.
data FpTok = FpTag !Int | FpUniq !Word64 | FpStr !String

-- | One token of a binding's skeleton: a fixed token, or a hole naming a
-- top-level binding of the same program.
data Sk = SkTok !FpTok | SkRef !Int

-- | A colour: a 64-bit FNV-1a hash of the token stream a binding
-- fingerprints to.  A hash collision can only merge two colours, which
-- shows up as a /tie/ and is then resolved by the vacuity check below; it
-- can never make two different structures look aligned, because the
-- lockstep zip is what admits a pair.
type Colour = Word64

-- | Where each top-level binder's unique sits, as a group index.  On the
-- tidied side the implicit groups are left out: their names were external
-- before tidy too, so their occurrences fingerprint by name and need no
-- hole.
topIndex :: Bool -> [CoreBind] -> M.Map Word64 Int
topIndex skipImplicit bs = M.fromList
    [ (ukey v, i)
    | (i, b) <- zip [0 ..] bs
    , not (skipImplicit && isImplicitBind b)
    , v <- bindersOf b ]

ukey :: Var -> Word64
ukey = getKey . varUnique

-- | The skeleton of a top-level binding.  The top binders' uniques are left
-- out — they are exactly what tidy reallocates.
skTop :: DynFlags -> M.Map Word64 Int -> CoreBind -> [Sk]
skTop dflags tops (NonRec _ e) = SkTok (FpTag 0) : skExpr dflags tops S.empty e
skTop dflags tops (Rec ps)     = SkTok (FpTag 1) : SkTok (FpTag (length ps))
    : concatMap (skExpr dflags tops S.empty . snd) ps

skExpr :: DynFlags -> M.Map Word64 Int -> S.Set Word64 -> CoreExpr -> [Sk]
skExpr dflags tops = go
  where
    tok t = SkTok t

    go sc (Var v)
        -- A binder of the right-hand side itself: tidy keeps its unique.
        | ukey v `S.member` sc = [tok (FpTag 5), tok (FpUniq (ukey v))]
        -- One of this module's own top-level bindings: a hole.
        | Just i <- M.lookup (ukey v) tops = [tok (FpTag 16), SkRef i]
        -- An import, or one of the implicit ids: already external, and
        -- returned unchanged (Iface/Tidy.hs:1073-1074).
        | isGlobalId v && isExternalName (varName v)
                               = [tok (FpTag 4), tok (FpStr (nameStableString (varName v)))]
        | otherwise            = [tok (FpTag 17)]
    go _  (Lit l)         = [tok (FpTag 6), tok (FpStr (sdoc dflags (ppr l)))]
    go sc (App f a)       = tok (FpTag 7) : go sc f ++ go sc a
    go sc (Lam b e)       = tok (FpTag 8) : tok (FpUniq (ukey b)) : go (bind sc [b]) e
    go sc (Let b e)       = let sc' = bind sc (bindersOf b)
                            in tok (FpTag 9) : skLet sc sc' b ++ go sc' e
    go sc (Case s b _ as) = let sc' = bind sc [b]
                            in tok (FpTag 10) : tok (FpUniq (ukey b)) : go sc s
                                 ++ concatMap (alt sc') as
    go sc (Cast e _)      = tok (FpTag 11) : go sc e
    go sc (Tick _ e)      = tok (FpTag 12) : go sc e
    go _  (Type _)        = [tok (FpTag 13)]
    go _  (Coercion _)    = [tok (FpTag 14)]

    skLet sc _   (NonRec b e) = tok (FpTag 2) : tok (FpUniq (ukey b)) : go sc e
    skLet _  sc' (Rec ps)     = tok (FpTag 3) : tok (FpTag (length ps))
        : concat [tok (FpUniq (ukey b)) : go sc' e | (b, e) <- ps]

    alt sc (Alt con bs rhs) = tok (FpTag 15) : tok (FpStr (con' con))
        : [tok (FpUniq (ukey b)) | b <- bs] ++ go (bind sc bs) rhs

    bind sc vs = foldl' (flip S.insert) sc (map ukey vs)

    con' (DataAlt dc) = nameStableString (dataConName dc)
    con' (LitAlt l)   = sdoc dflags (ppr l)
    con' DEFAULT      = "DEFAULT"

-- FNV-1a, 64 bit.
fnvSeed :: Word64
fnvSeed = 14695981039346656037

fnv :: Word64 -> Word64 -> Word64
fnv h x = (h `xor` x) * 1099511628211

hashTok :: Word64 -> FpTok -> Word64
hashTok h (FpTag n)  = fnv (fnv h 1) (fromIntegral n)
hashTok h (FpUniq u) = fnv (fnv h 2) u
hashTok h (FpStr t)  = foldl' (\a c -> fnv a (fromIntegral (fromEnum c))) (fnv h 3) t

-- | One round: hash each skeleton with the previous round's colours in the
-- holes.
round1 :: [Colour] -> [[Sk]] -> [Colour]
round1 prev = map (foldl' step fnvSeed)
  where
    step h (SkTok t) = hashTok h t
    step h (SkRef i) = fnv (fnv h 4) (colourAt i)
    colours = prev
    colourAt i = case drop i colours of
        (c:_) -> c
        []    -> 0

-- | Colour both programs together until the partition stops splitting, or
-- for at most 'refineRounds' rounds.  One shared numbering, so a colour
-- means the same on both sides.
refineColours :: [[Sk]] -> [[Sk]] -> ([Colour], [Colour])
refineColours preSk tidySk = go 0 (start preSk) (start tidySk)
  where
    start = map (const 0)
    go :: Int -> [Colour] -> [Colour] -> ([Colour], [Colour])
    go n p t
        | n >= refineRounds = (p, t)
        | distinct p' t' <= distinct p t = (p', t')
        | otherwise = go (n + 1) p' t'
      where
        p' = round1 p preSk
        t' = round1 t tidySk
    distinct p t = S.size (S.fromList (p ++ t))

refineRounds :: Int
refineRounds = 12

-- | Everything the join takes from the pre-tidy side, in tree order.  Two
-- pre-tidy bindings with one fingerprint are structurally indistinguishable;
-- if their payloads are equal too, then which of them the merge picked
-- cannot change a byte of the dump, and the tie is /vacuous/.
payload :: DynFlags -> CoreBind -> [String]
payload dflags = goTop
  where
    goTop (NonRec b e) = bnd b ++ goE e
    goTop (Rec ps)     = concat [bnd b ++ goE e | (b, e) <- ps]

    bnd v | isId v = [ show (isExportedId v)
                     , sdoc dflags (ppr (idDemandInfo v))
                     , show (isOneShotInfo (idOneShotInfo v)) ]
          | otherwise = ["tv"]

    goE (Var _)        = []
    goE (Lit _)        = []
    goE (App f a)      = goE f ++ goE a
    goE (Lam b e)      = bnd b ++ goE e
    goE (Let d e)      = goTop d ++ goE e
    goE (Case s b _ as) = goE s ++ bnd b
                            ++ concat [concatMap bnd bs ++ goE r | Alt _ bs r <- as]
    goE (Cast e _)     = goE e
    goE (Tick _ e)     = goE e
    goE (Type _)       = []
    goE (Coercion _)   = []

-- | What the pass asserts about the alignment, and reports.
data AlignFacts = AlignFacts
    { afAligned      :: !Int   -- ^ aligned @CoreBind@ groups
    , afImplicit     :: !Int   -- ^ injected by @getImplicitBinds@
    , afTrimmed      :: !Int   -- ^ discarded by @trim_binds@
    , afSpt          :: !Int   -- ^ inserted by @sptCreateStaticBinds@
    , afSptPossible  :: !Bool  -- ^ was @StaticPointers@ on at all?
    , afBindersOut   :: !Int   -- ^ top-level binders in the dump
    , afBindersTrim  :: !Int   -- ^ top-level binders trimmed away
    , afUnique       :: !Int   -- ^ aligned pairs with a unique fingerprint
    , afTied         :: !Int   -- ^ aligned pairs whose fingerprint is shared
    , afTiedVacuous  :: !Int   -- ^ …of which every tied candidate joins the same
    , afTrimmedNames :: [String]
    , afImplicitDesc :: [String]
    , afErrs         :: [String]
    }

-- | Establish (a)-(f).  Every error here aborts the extraction.
alignFacts :: DynFlags -> Bool -> [CoreBind] -> [Slot] -> [String] -> AlignFacts
alignFacts dflags sptOn preBinds slots mergeErrs = AlignFacts
    { afAligned      = length [() | Aligned{}  <- slots]
    , afImplicit     = length [() | Implicit{} <- slots]
    , afTrimmed      = length trimmed
    , afSpt          = 0
    , afSptPossible  = sptOn
    , afBindersOut   = sum [length (bindersOf (slotTidy s)) | s <- slots, isEmitted s]
    , afBindersTrim  = sum [length (bindersOf b) | b <- trimmed]
    , afUnique       = length [() | (_, k, _) <- ties, k == 1]
    , afTied         = length [() | (_, k, _) <- ties, k /= 1]
    , afTiedVacuous  = length [() | (_, k, True) <- ties, k /= 1]
    , afTrimmedNames = map bindLabel trimmed
    , afImplicitDesc = [ bindLabel b ++ "   " ++ sdoc dflags (ppr (map idDetails (bindersOf b)))
                       | Implicit b <- slots ]
    , afErrs         = mergeErrs ++ exportedTrimmed ++ tieErrs ++ prefixErr
    }
  where
    trimmed = [b | Dropped b <- slots]

    -- (a) and (b): uniqueness, proved by fingerprint and independently of the
    -- order the merge walked in.
    tidyBinds = [slotTidy s' | s' <- slots, isEmitted s']
    preSk  = map (skTop dflags (topIndex False preBinds))  preBinds
    tidySk = map (skTop dflags (topIndex True tidyBinds)) tidyBinds
    (preCol, tidyCol) = refineColours preSk tidySk

    -- Colour -> the pre-tidy bindings of that colour.
    fpIndex :: M.Map Colour [CoreBind]
    fpIndex = M.fromListWith (++) (zip preCol (map (: []) preBinds))

    tidyColOf :: M.Map String Colour
    tidyColOf = M.fromList (zip (map bindLabel tidyBinds) tidyCol)

    ties :: [(String, Int, Bool)]
    ties = [ (lbl, length cands, vacuous cands)
           | Aligned _ t <- slots
           , let lbl = bindLabel t
           , let cands = maybe [] (\c -> M.findWithDefault [] c fpIndex)
                                  (M.lookup lbl tidyColOf) ]

    vacuous cands = case map (payload dflags) cands of
        []     -> False
        (x:xs) -> all (== x) xs

    tieErrs =
        [ "ambiguous alignment: " ++ show k ++ " pre-tidy bindings share the \
          \fingerprint of " ++ lbl ++ ", and they do not carry the same joined facts"
        | (lbl, k, vac) <- ties, k /= 1, not vac ]
        ++ [ "no pre-tidy binding has the fingerprint of aligned binding " ++ lbl
           | (lbl, 0, _) <- ties ]

    -- (c): a trimmed group never has an exported binder (Iface/Tidy.hs:1046).
    exportedTrimmed =
        [ "a trimmed pre-tidy binding has an exported binder, which \
          \findExternalRules/trim_binds cannot do: " ++ bindLabel b
        | b <- trimmed, any isExportedId (bindersOf b) ]

    -- (c) again: the implicit bindings are a prefix of the tidied program.
    prefixErr
        | implicitFlags == takeWhile id implicitFlags
                            ++ dropWhile id implicitFlags = []
        | otherwise = ["the implicit bindings are not a prefix of the tidied program"]
    implicitFlags = [isImp s | s <- slots, isEmitted s]
    isImp Implicit{} = True
    isImp _          = False

--------------------------------------------------------------------------------
-- The alignment log
--------------------------------------------------------------------------------
--
-- Written beside the dump as @<Module>.tidy-align.txt@ and summarised on
-- stderr.  The Rust loader reads @*.core.json@ only (`h2r_core_ir::load_dir`),
-- so the sidecar is inert.

-- | An import occurrence is not renamed by tidy: it was a `GlobalId` with an
-- external `Name` before the pass and is the same `Var` after it.  Counted on
-- every aligned pair, positionally, and reported.
importAgreement :: CoreBind -> CoreBind -> (Int, Int)
importAgreement b1 b2 = goB b1 b2
  where
    goB (NonRec _ e1) (NonRec _ e2) = goE e1 e2
    goB (Rec ps1) (Rec ps2) = mconcat' [goE e1 e2 | ((_, e1), (_, e2)) <- zip ps1 ps2]
    goB _ _ = (0, 0)

    goE (Var v1) (Var v2)
        | isGlobalId v1 =
            if varName v1 == varName v2 && varUnique v1 == varUnique v2
                then (1, 0) else (0, 1)
        | otherwise = (0, 0)
    goE (App f1 a1) (App f2 a2) = goE f1 f2 <+> goE a1 a2
    goE (Lam _ e1) (Lam _ e2)   = goE e1 e2
    goE (Let d1 e1) (Let d2 e2) = goB d1 d2 <+> goE e1 e2
    goE (Case s1 _ _ as1) (Case s2 _ _ as2) =
        goE s1 s2 <+> mconcat' [goE r1 r2 | (Alt _ _ r1, Alt _ _ r2) <- zip as1 as2]
    goE (Cast e1 _) (Cast e2 _) = goE e1 e2
    goE (Tick _ e1) (Tick _ e2) = goE e1 e2
    goE _ _ = (0, 0)

    (a, b) <+> (c, d) = (a + c, b + d)
    mconcat' = foldl' (<+>) (0, 0)

-- | The one-line stderr summary.  The counts are of `CoreBind` groups — a
-- recursive group is one — with the emitted top-level binder count beside
-- them, which is the dump's top-level pair count.
summary :: AlignFacts -> String
summary f =
    "tidy alignment: " ++ show (afAligned f) ++ " aligned, "
                       ++ show (afImplicit f) ++ " implicit, "
                       ++ show (afTrimmed f) ++ " trimmed, "
                       ++ show (afSpt f) ++ " spt (groups); "
                       ++ show (afBindersOut f) ++ " top-level binders emitted, "
                       ++ show (afBindersTrim f) ++ " trimmed; "
                       ++ show (afUnique f) ++ " uniquely fingerprinted, "
                       ++ show (afTied f) ++ " tied ("
                       ++ show (afTiedVacuous f) ++ " vacuously)"

-- | The per-module alignment log.
report :: String -> NameSet -> AlignFacts -> [Slot] -> String
report modName exportSet f slots = unlines $
    [ "module " ++ modName
    , summary f
    , ""
    , "the alignment theorem, per group (Iface/Tidy.hs:381-387, 611-626, 976-1050,"
    , "1156-1190; Core/Tidy.hs:207-233, 300, 326)"
    , "  aligned                              " ++ show (afAligned f)
    , "  implicit (getImplicitBinds)          " ++ show (afImplicit f)
    , "  trimmed  (trim_binds)                " ++ show (afTrimmed f)
    , "  spt      (sptCreateStaticBinds)      " ++ show (afSpt f)
    , "  SPT insertion possible at all        " ++ show (afSptPossible f)
    , "  aligned with EXACTLY ONE pre-tidy binding of the same fingerprint"
    , "                                       " ++ show (afUnique f)
    , "  aligned where several pre-tidy bindings are structurally"
    , "  indistinguishable                    " ++ show (afTied f)
    , "    ...of which every tied candidate carries the same joined facts,"
    , "    so the tie cannot change a byte  " ++ show (afTiedVacuous f)
    , "  pre-tidy groups  = aligned + trimmed = " ++ show (afAligned f + afTrimmed f)
    , "  tidied groups    = aligned + implicit + spt = "
        ++ show (afAligned f + afImplicit f + afSpt f)
    , ""
    , "exported, on aligned top-level binders. The EMITTED value is the pre-tidy"
    , "isExportedId (the compiler's export/liveness flag, which is what M2 reads);"
    , "sourceExported and externalName are emitted beside it as diagnostics. The"
    , "three do NOT agree: the desugarer marks as exported everything that must"
    , "reach the interface (dfuns, Typeable bindings, default methods), not only"
    , "the source export list, and CoreTidy externalises more still."
    , "  pre-tidy isExportedId  [exported]    " ++ show preExported
    , "  in availsToNameSet (mg_exports)      " ++ show inExports
    , "    [sourceExported]"
    , "  post-tidy isExternalName             " ++ show externalNames
    , "    [externalName]"
    , "  exported /= sourceExported           " ++ show exportDisagree
    ] ++
    [ "    " ++ d | d <- take 40 exportDisagreeNames ] ++
    [ "    (" ++ show (exportDisagree - 40) ++ " more)" | exportDisagree > 40 ] ++
    [ ""
    , "import occurrences in aligned position, pre-tidy name+unique vs tidied"
    , "(Iface/Tidy.hs:1073-1074: an already-external name is returned unchanged)"
    , "  agree                                " ++ show impAgree
    , "  disagree                             " ++ show impDisagree
    , ""
    , "trimmed pre-tidy bindings (findExternalRules/trim_binds: kept alive only by"
    , "an auto rule; none has an exported binder -- Iface/Tidy.hs:1039-1046)"
    ] ++
    [ "  " ++ n | n <- afTrimmedNames f ] ++
    [ "  (none)" | null (afTrimmedNames f) ] ++
    [ ""
    , "implicit bindings injected by getImplicitBinds (Iface/Tidy.hs:611-626)"
    ] ++
    [ "  " ++ d | d <- afImplicitDesc f ] ++
    [ "  (none)" | null (afImplicitDesc f) ] ++
    [ "" ] ++
    (if null (afErrs f) then ["no alignment errors"]
                        else ("ALIGNMENT ERRORS" : map ("  " ++) (afErrs f)))
  where
    topPairs = [ (pre, tid)
               | Aligned p t <- slots
               , (pre, tid) <- zip (bindersOf p) (bindersOf t) ]
    inExports   = length [() | (_, t) <- topPairs, elemNameSet (varName t) exportSet]
    preExported = length [() | (p, _) <- topPairs, isExportedId p]
    externalNames = length [() | (_, t) <- topPairs, isExternalName (varName t)]
    exportDisagreeNames =
        [ getOccString p ++ " -> " ++ nameStableString (varName t)
          ++ " (exported " ++ show (isExportedId p)
          ++ ", sourceExported " ++ show (elemNameSet (varName t) exportSet)
          ++ ", externalName " ++ show (isExternalName (varName t)) ++ ")"
        | (p, t) <- topPairs, isExportedId p /= elemNameSet (varName t) exportSet ]
    exportDisagree = length exportDisagreeNames
    (impAgree, impDisagree) =
        foldl' (\(a, b) (c, d) -> (a + c, b + d)) (0, 0)
               [importAgreement p t | Aligned p t <- slots]

--------------------------------------------------------------------------------
-- Id table: facts about every referenced `GlobalId` with an *external*
-- `Name`, keyed by its stable name (@$unit$Module$occ@), so a `Var` node
-- stays small and callee strictness is one lookup away.
--
-- The key is never a unique.  Uniques are not unique in an optimised dump
-- (the simplifier duplicates terms without freshening binders), so anything
-- keyed by one merges inlined copies of different binders.  Locals are not
-- here at all: they are bound somewhere in this module's Core and the Rust
-- IR resolves every occurrence of one lexically to its binder, which carries
-- the authoritative `IdInfo`.
--
-- __External names only.__  The serialised program is CoreTidy's, and
-- `tidyTopBind` rebuilds every top-level binder as a `GlobalId` — including
-- the ones whose `Name` GHC kept *internal*.  An internal `nameStableString`
-- (@$_in$…@, @$_sys$…@) is not unique: three top-level bindings of
-- `ShellCheck.AST` render as @$_sys$$fTraversableInnerToken@.  Keying such a
-- binder here would merge distinct Ids under one key (M2.4h).
-- `isExternalName` is the admission test, and it is GHC's own.
--
-- The module's own now-external top-level binders can therefore appear in
-- this table, when the module references them.  Those entries are
-- *redundant, not harmful*: such an occurrence is bound in this module, so
-- the Rust resolver gives it `Ref::Local` and every signature is read from
-- the binder (`Scope::head_sig`), never from here.
--
-- Every fact below is read from the `Var` as it appears in the serialised
-- program — the tidied one — so `hasUnfolding`, the data-constructor record
-- and `isClassOpId` describe the Ids the dump actually contains.  Imports are
-- not renamed by tidy at all (`tidyTopName`, @Iface/Tidy.hs:1073-1074@), and
-- the alignment log reports the count of import occurrences whose name and
-- unique were checked to agree pre and post.
--------------------------------------------------------------------------------

idTable :: DynFlags -> CoreProgram -> Value
idTable dflags binds =
    object [ (Key.fromString k, idInfoJ dflags v) | (k, v) <- M.toList refs ]
  where
    refs = M.fromList [ (nameStableString (varName v), v)
                      | v <- concatMap referenced binds
                      , isId v, isGlobalId v, isExternalName (varName v) ]

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

-- | The pre-tidy counterpart of a slot's binding, when it has one.
slotPre :: Slot -> Maybe CoreBind
slotPre (Aligned p _) = Just p
slotPre (Implicit _)  = Nothing
slotPre (Dropped _)   = Nothing

-- | The pairs of a binding, lined up with their pre-tidy counterparts.  The
-- lengths always agree on an aligned pair — 'zipBind' has asserted it — and a
-- mismatch degrades to "no counterpart" rather than lining the wrong binders
-- up.
bindPairs :: Maybe CoreBind -> CoreBind
          -> (Bool, [(Maybe (CoreBndr, CoreExpr), (CoreBndr, CoreExpr))])
bindPairs mpre b = (isRecBind b, zipped)
  where
    isRecBind NonRec{} = False
    isRecBind Rec{}    = True

    pairsOf (NonRec x r) = [(x, r)]
    pairsOf (Rec ps)     = ps

    prePairs  = maybe [] pairsOf mpre
    tidyPairs = pairsOf b
    zipped
        | length prePairs == length tidyPairs = zip (map Just prePairs) tidyPairs
        | otherwise = [(Nothing, tp) | tp <- tidyPairs]

-- | Where a binder sits, which is what decides the provenance of the two
-- fields CoreTidy discards unevenly.
data BndClass = BTop | BLet | BLam | BCase | BAlt
    deriving (Eq)

-- | A top-level binding.
--
-- __@exported@ at the top level.__  After CoreTidy every top-level binder is
-- a `GlobalId`, so `isExportedId` on the emitted binder is uniformly `True`
-- and carries no information.  On an /aligned/ binder the field therefore
-- keeps its pre-tidy meaning and its pre-tidy value: the compiler's own
-- export\/liveness flag, which is the fact
-- @h2r-analysis/src/{dictflow,higher,boundary,flow,m24,verify,verify_rep,verify_m24,tuples,classops}.rs@
-- already read, and which the pre-tidy dumps carried.
--
-- Two further facts are emitted beside it, as __diagnostics only__ — no
-- analysis reads them in this milestone:
--
--   * @externalName@: the tidied `Name` is external, i.e. another module can
--     refer to this binding by its stable name.  This is the fact the
--     linkage rests on, and the Rust IR computes it from the name itself.
--   * @sourceExported@: the tidied `Name` is in @availsToNameSet (mg_exports
--     guts)@, the module's source export list.
--
-- The three are different populations and the alignment log measures the
-- gap: over the @-O1@ world, @exported@ 1200, @sourceExported@ 342,
-- @externalName@ far larger.  An /implicit/ binding has no pre-tidy binder
-- to read @exported@ from, and post-tidy `isExportedId` would say `True` for
-- all of them, so those — and only those — take @sourceExported@ as
-- @exported@.
topBindJ :: DynFlags -> TyS -> NameSet -> Slot -> Value
topBindJ dflags tys exportSet slot = object
    [ "rec"   .= rec_
    , "pairs" .= [ pairJ dflags tys BTop (Just (srcExp b)) mp b e | (mp, (b, e)) <- ps ]
    ]
  where
    (rec_, ps) = bindPairs (slotPre slot) (slotTidy slot)
    srcExp b = elemNameSet (varName b) exportSet

-- | A nested @let@ \/ @letrec@.
bindJ :: DynFlags -> TyS -> Maybe CoreBind -> CoreBind -> Value
bindJ dflags tys mpre b = object
    [ "rec"   .= rec_
    , "pairs" .= [ pairJ dflags tys BLet Nothing mp bb e | (mp, (bb, e)) <- ps ]
    ]
  where
    (rec_, ps) = bindPairs mpre b

-- | One binder-and-right-hand-side.  The shape facts are GHC's own
-- predicates run on the __tidied__ right-hand side — they describe the
-- program that is emitted.
pairJ :: DynFlags -> TyS -> BndClass -> Maybe Bool -> Maybe (CoreBndr, CoreExpr)
      -> CoreBndr -> CoreExpr -> Value
pairJ dflags tys cls msrc mpre b e = object
    [ "binder"  .= binderJ dflags tys cls msrc (fst <$> mpre) b
    , "rhs"     .= exprJ dflags tys (snd <$> mpre) e
    -- Shape facts about the RHS, computed by GHC's own predicates.
    , "whnf"    .= exprIsHNF e
    , "trivial" .= exprIsTrivial e
    , "cheap"   .= exprIsCheap e
    -- No bottom, no side effects, cheap: safe to evaluate eagerly.
    , "okForSpec" .= exprOkForSpeculation e
    ]

-- | Everything the backend needs to know about a binder, including the
-- strictness facts GHC inferred for it.
--
-- __The provenance.__  @name@, @occ@, @unique@, the type, and every
-- `IdInfo` \/ `IdDetails` field CoreTidy finalises — @arity@, @callArity@,
-- @dmdSig@, @cprSig@, @occInfo@, @details@, @hasUnfolding@, @isJoinPoint@,
-- @isDataCon@ — come from the emitted (tidied) binder @v@.  Exactly three
-- fields are joined from @mpre@, the pre-tidy binder this one was tidied
-- from, and only in the binder classes where CoreTidy discards them:
--
--   * @demand@ — pre-tidy on 'BTop', 'BLam', 'BCase', 'BAlt'; tidied on
--     'BLet', which @tidyLetBndr@ preserves.
--   * @oneShot@ — pre-tidy on 'BTop' and 'BLet'; tidied on 'BLam', which
--     @tidyIdBndr@ preserves, and on 'BCase' \/ 'BAlt', where it is never
--     set.
--   * @exported@ — pre-tidy on 'BTop' (see 'topBindJ'); tidied elsewhere,
--     where it is `False` on both sides.
--
-- 'dumpPass' carries the GHC source line that drops each of them and the
-- reader that needs it.  A binder with no pre-tidy counterpart — one of an
-- implicit binding GHC injected — reads everything from itself.
binderJ :: DynFlags -> TyS -> BndClass -> Maybe Bool -> Maybe Var -> Var -> Value
binderJ dflags tys cls msrc mpre v
    | isId v = object $ common ++
        [ "kind"       .= ("id" :: String)
        , "arity"      .= idArity v
        , "callArity"  .= idCallArity v
        , "exported"   .= exportedV
        , "dmdSig"     .= dmdSigJ dflags (idDmdSig v)
        , "cprSig"     .= sdoc dflags (ppr (idCprSig v :: CprSig))
        -- How this binder itself is demanded at its binding site.
        , "demand"     .= demandJ dflags demandV
        , "occInfo"    .= occInfoJ (idOccInfo v)
        , "oneShot"    .= isOneShotInfo oneShotV
        , "details"    .= sdoc dflags (ppr (idDetails v))
        , "hasUnfolding" .= hasSomeUnfolding (realIdUnfolding v)
        , "isJoinPoint"  .= isJoinId v
        , "isDataCon"    .= isDataConWorkId v
        ] ++ topOnly
    | otherwise = object $ common ++
        [ "kind" .= ("tyvar" :: String) ]
  where
    -- Read a fact from the pre-tidy binder when this one is aligned with one.
    fromPre :: (Var -> a) -> a
    fromPre f = case mpre of
        Just p | isId p    -> f p
        _                  -> f v

    demandV  | cls == BLet = idDemandInfo v
             | otherwise   = fromPre idDemandInfo
    oneShotV | cls == BTop || cls == BLet = fromPre idOneShotInfo
             | otherwise                  = idOneShotInfo v
    exportedV
        | cls /= BTop = isExportedId v
        | otherwise   = case mpre of
            Just p  -> isExportedId p
            Nothing -> fromMaybe False msrc

    -- Diagnostics, emitted on top-level binders only. Format 6.
    topOnly
        | cls /= BTop = []
        | otherwise =
            [ "externalName"   .= isExternalName (varName v)
            , "sourceExported" .= fromMaybe False msrc
            ]

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

-- | An expression.  @mpre@ is the pre-tidy counterpart of the node being
-- emitted, when the enclosing top-level binding is aligned; it is walked in
-- lockstep so that every binder reached from here is joined with the binder
-- in the same position of the pre-tidy tree.  The names, uniques and types
-- emitted are always the tidied ones.
exprJ :: DynFlags -> TyS -> Maybe CoreExpr -> CoreExpr -> Value
exprJ dflags tys = go
  where
    go mpre = \case
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
            , "fun"  .= go (mpre >>= \p -> case p of App g _ -> Just g; _ -> Nothing) f
            , "arg"  .= go (mpre >>= \p -> case p of App _ b -> Just b; _ -> Nothing) a
            ]
        Lam b e -> object
            [ "node"   .= ("Lam" :: String)
            , "binder" .= binderJ dflags tys BLam Nothing
                            (mpre >>= \p -> case p of Lam q _ -> Just q; _ -> Nothing) b
            , "body"   .= go (mpre >>= \p -> case p of Lam _ r -> Just r; _ -> Nothing) e
            ]
        Let b e -> object
            [ "node" .= ("Let" :: String)
            , "bind" .= bindJ dflags tys
                          (mpre >>= \p -> case p of Let d _ -> Just d; _ -> Nothing) b
            , "body" .= go (mpre >>= \p -> case p of Let _ r -> Just r; _ -> Nothing) e
            ]
        Case scrut b ty alts ->
            let preAlts = case mpre of
                    Just (Case _ _ _ pas) | length pas == length alts -> map Just pas
                    _                                                 -> map (const Nothing) alts
            in object
            [ "node"    .= ("Case" :: String)
            , "scrut"   .= go (mpre >>= \p -> case p of Case s _ _ _ -> Just s; _ -> Nothing)
                              scrut
            , "binder"  .= binderJ dflags tys BCase Nothing
                             (mpre >>= \p -> case p of Case _ q _ _ -> Just q; _ -> Nothing) b
            , "type"    .= sdoc dflags (ppr ty)
            , "ty"      .= tyIx dflags tys ty
            , "alts"    .= zipWith altJ preAlts alts
            ]
        Cast e _co -> object
            [ "node" .= ("Cast" :: String)
            , "expr" .= go (mpre >>= \p -> case p of Cast r _ -> Just r; _ -> Nothing) e
            ]
        Tick _t e -> object
            [ "node" .= ("Tick" :: String)
            , "expr" .= go (mpre >>= \p -> case p of Tick _ r -> Just r; _ -> Nothing) e
            ]
        Type t -> object
            [ "node" .= ("Type" :: String)
            , "type" .= sdoc dflags (ppr t)
            , "ty"   .= tyIx dflags tys t
            ]
        Coercion _ -> object
            [ "node" .= ("Coercion" :: String) ]

    altJ mpre (Alt con bs rhs) =
        let preBs = case mpre of
                Just (Alt _ pbs _) | length pbs == length bs -> map Just pbs
                _                                            -> map (const Nothing) bs
            preRhs = case mpre of
                Just (Alt _ _ r) -> Just r
                Nothing          -> Nothing
        in object
            [ "con"     .= altConJ con
            , "binders" .= zipWith (binderJ dflags tys BAlt Nothing) preBs bs
            , "rhs"     .= go preRhs rhs
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
           (collectTys binds ++ map (varType . dataConWorkId) (programConstructors binds))

-- Full families, including constructors only mentioned by a pattern. This is
-- optional format-6 evidence: old dumps remain readable but cannot justify
-- general algebraic lowering without it.
programConstructors :: CoreProgram -> [DataCon]
programConstructors binds = M.elems $ M.fromList
    [ (nameStableString (dataConName dc), dc)
    | found <- concatMap goBind binds ++ concatMap typeCons (collectTys binds)
    , dc <- tyConDataCons (dataConTyCon found) ]
  where
    goBind (NonRec _ e) = go e
    goBind (Rec ps) = concatMap (go . snd) ps
    go (Var v) = case isDataConId_maybe v of Just dc -> [dc]; Nothing -> []
    go (App f a) = go f ++ go a
    go (Lam _ e) = go e
    go (Let b e) = goBind b ++ go e
    go (Case s _ _ as) = go s ++ concat [con c ++ go r | Alt c _ r <- as]
    go (Cast e _) = go e
    go (Tick _ e) = go e
    go _ = []
    con (DataAlt dc) = [dc]
    con _ = []
    typeCons (TyConApp tc args) = (if isAlgTyCon tc then tyConDataCons tc else [])
                                  ++ concatMap typeCons args
    typeCons (FunTy _ _ a r) = typeCons a ++ typeCons r
    typeCons (ForAllTy _ t) = typeCons t
    typeCons (AppTy f a) = typeCons f ++ typeCons a
    typeCons _ = []

constructorJ :: DynFlags -> TyS -> DataCon -> Value
constructorJ dflags tys dc = object
    ([ "name" .= nameStableString (dataConName dc)
    , "worker" .= nameStableString (varName (dataConWorkId dc))
    , "family" .= nameStableString (tyConName (dataConTyCon dc))
    , "tag" .= dataConTag dc
    , "familySize" .= length (tyConDataCons (dataConTyCon dc))
    , "signature" .= tyIx dflags tys (varType (dataConWorkId dc))
    , "repArity" .= dataConRepArity dc
    , "strict" .= map isMarkedStrict (dataConRepStrictness dc)
    , "vanilla" .= (isVanillaDataCon dc && not (isNewTyCon (dataConTyCon dc))
                    && isLiftedTypeKind (tyConResKind (dataConTyCon dc))
                    && not (isUnboxedTupleTyCon (dataConTyCon dc))
                    && not (isUnboxedSumTyCon (dataConTyCon dc)))
    -- The reasons 'isVanillaDataCon' can be false, separately, so a class
    -- dictionary's superclass constraint field is not mistaken for an
    -- existential or a GADT equality.
    , "newtype" .= isNewTyCon (dataConTyCon dc)
    , "unlifted" .= not (isLiftedTypeKind (tyConResKind (dataConTyCon dc)))
    , "unboxed" .= (isUnboxedTupleTyCon (dataConTyCon dc)
                    || isUnboxedSumTyCon (dataConTyCon dc))
    -- Whether this family is a class's dictionary. GHC knows; nothing on the
    -- Rust side can tell a dictionary from a one-constructor record by its
    -- shape, and an occurrence name is not evidence.
    , "class" .= isClassTyCon (dataConTyCon dc)
    ] ++ constructorScopeJ dc)

-- | The two parts of a constructor's signature that make a field more than a
-- value: existentially quantified variables, and GADT equality evidence.
-- 'dataConFullSig' is the only exported way to reach the equality spec.
constructorScopeJ :: DataCon -> [(Key.Key, Value)]
constructorScopeJ dc =
    [ "existential" .= not (null exVars)
    , "equalities" .= not (null eqSpec)
    ]
  where
    (_, exVars, eqSpec, _, _, _) = dataConFullSig dc

-- | The index of a type in a table that already contains it.  'tyTable' is
-- built from the program types and constructor worker signatures, which is
-- exactly the set the emitters ask about, so this is always a lookup; interning is pure, so
-- running it against the finished table cannot disturb it.
tyIx :: DynFlags -> TyS -> Type -> Int
tyIx dflags tys t = fst (internTy dflags tys (expandTypeSynonyms t))
