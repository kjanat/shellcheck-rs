//! A flat set of headline numbers from a census, for comparing GHC
//! optimisation profiles side by side.

use serde::Serialize;

use crate::callee::{Family, Resolution, Tier};
use crate::laziness::{Census, Class, Fate, Origin, Sink, TopClass};
use crate::shape::ArgShape;
use crate::tuples::{TupleCensus, TupleFate};

#[derive(Debug, Clone, Serialize)]
pub struct Metrics {
    pub core_nodes: usize,
    pub top_level_binds: usize,
    pub local_binds: usize,
    pub functions: usize,
    pub join_points: usize,
    pub strict_shared: usize,
    pub thunk_sites: usize,
    pub memo_sites: usize,
    pub memo_under_lambda: usize,
    pub memo_ok_for_spec: usize,
    pub float_outs: usize,
    pub dictionary_lets: usize,
    pub recursive_values: usize,
    pub sink_eager: usize,
    pub cafs: usize,
    pub nontrivial_args: usize,
    pub strict_args: usize,
    pub unsaturated_args: usize,
    pub lazy_computations: usize,
    pub exact_callee: usize,
    pub class_op_sites: usize,
    pub dictionary_sites: usize,
    pub higher_order_unknown: usize,
    /// Aggregate of the five returned-closure resolutions below.
    pub past_arity: usize,
    pub global_past_sig: usize,
    pub lambda_no_demand: usize,
    pub lambda_past_arity: usize,
    pub closure_from_known_call: usize,
    pub computed_closure: usize,
    pub tier_exact: usize,
    pub tier_finite: usize,
    pub tier_producer_known: usize,
    pub tier_unresolved: usize,
    pub parsec_cps_sites: usize,
    pub tuple_sites: usize,
    // Saturated tuple constructions and their proven fates, boxed and
    // unboxed kept apart: an unboxed tuple cannot be stored in a lazy
    // field, so the two populations answer different questions.
    pub tuple_cons_boxed: usize,
    pub tuple_cons_unboxed: usize,
    pub tuple_scalar_boxed: usize,
    pub tuple_scalar_unboxed: usize,
    pub tuple_return_boxed: usize,
    pub tuple_return_unboxed: usize,
    /// Removable by def-use but crossing a boundary only a specialised
    /// clone could split ([`TupleFate::RemovableWithClone`]).
    pub tuple_clone_boxed: usize,
    pub tuple_clone_unboxed: usize,
    pub tuple_preserve_boxed: usize,
    pub tuple_preserve_unboxed: usize,
    pub tuple_unresolved_boxed: usize,
    pub tuple_unresolved_unboxed: usize,
    /// Removable constructions with at least one field read on its own.
    pub tuple_selected: usize,
    /// **Can this box disappear locally?** Constructions the def-use walk
    /// proves are transport, before any question of whether the removals
    /// agree with each other. This is the *local* answer and is the larger
    /// of the two numbers.
    pub tuple_removable_defuse: usize,
    /// **Can it disappear without cloning?** Of those, the ones whose every
    /// representation boundary is a uniform split, so the removal composes
    /// with every other removal at the same boundary. This is the *global*
    /// answer and is the one the milestone accounting calls `normalised`.
    ///
    /// The two are deliberately separate metrics rather than one number
    /// with a caveat: they answer different questions, and the difference
    /// between them is exactly the work a representation-agreement or
    /// cloning pass would have to do.
    pub tuple_removable_composable: usize,
    /// Boundaries that only a specialised **clone** of the callee could
    /// carry: the first concrete evidence for a cloning pass. No such pass
    /// is implemented, and these are counted as unsupported.
    pub tuple_removable_with_clone: usize,
    /// Representation boundaries the removable flows cross, and how many of
    /// them can be split uniformly.
    pub boundaries: usize,
    pub boundaries_uniform: usize,
    pub flows_downgraded: usize,
    pub list_cons_sites: usize,
    pub string_literal_args: usize,
}

impl Metrics {
    pub fn of(
        census: &Census,
        tuples: Option<&TupleCensus<'_>>,
        core_nodes: usize,
        top_level_binds: usize,
    ) -> Metrics {
        let tc = |boxed: bool, fate: TupleFate| {
            tuples.map(|t| t.accounting.count(boxed, fate)).unwrap_or(0)
        };
        let b = &census.bindings;
        let thunks: Vec<_> = b.iter().filter(|x| x.fate != Fate::NotAThunk).collect();
        let memo: Vec<_> = thunks.iter().filter(|x| x.fate == Fate::Memo).collect();
        let comps: Vec<_> = census
            .args
            .iter()
            .filter(|a| a.shape == ArgShape::Computation)
            .collect();
        let lazy: Vec<_> = comps.iter().filter(|a| a.position.escapes()).collect();
        let count_class = |c: Class| b.iter().filter(|x| x.class == c).count();
        let count_res = |r: Resolution| lazy.iter().filter(|a| a.callee.resolution == r).count();
        let count_tier = |t: Tier| lazy.iter().filter(|a| a.callee.tier() == t).count();
        let count_fam = |fs: &[Family]| {
            lazy.iter()
                .filter(|a| fs.contains(&a.callee.family))
                .count()
        };
        Metrics {
            core_nodes,
            top_level_binds,
            local_binds: b.len(),
            functions: count_class(Class::Function),
            join_points: count_class(Class::JoinPoint),
            strict_shared: count_class(Class::StrictShared),
            thunk_sites: thunks.len(),
            memo_sites: memo.len(),
            memo_under_lambda: memo
                .iter()
                .filter(|x| matches!(x.sink, Sink::UnderLambda { .. }))
                .count(),
            memo_ok_for_spec: memo.iter().filter(|x| x.ok_for_spec).count(),
            float_outs: thunks
                .iter()
                .filter(|x| x.origin == Origin::FloatOut)
                .count(),
            dictionary_lets: thunks
                .iter()
                .filter(|x| x.origin == Origin::Dictionary)
                .count(),
            recursive_values: count_class(Class::RecursiveValue),
            sink_eager: thunks.iter().filter(|x| x.fate == Fate::SinkEager).count(),
            cafs: census
                .top
                .iter()
                .filter(|t| t.class == TopClass::Caf)
                .count(),
            nontrivial_args: census.args.len(),
            strict_args: comps
                .iter()
                .filter(|a| a.position == crate::shape::Position::StrictArg)
                .count(),
            unsaturated_args: comps
                .iter()
                .filter(|a| a.position == crate::shape::Position::UnsaturatedArg)
                .count(),
            lazy_computations: lazy.len(),
            exact_callee: count_res(Resolution::DataCon)
                + count_res(Resolution::ExactGlobal)
                + count_res(Resolution::ExactLocal),
            class_op_sites: count_res(Resolution::ClassOp),
            dictionary_sites: count_fam(&[Family::ClassOp, Family::Dictionary, Family::MonadOps]),
            higher_order_unknown: count_res(Resolution::HigherOrderParam),
            past_arity: count_res(Resolution::PastArity)
                + count_res(Resolution::KnownLambdaNoDemand)
                + count_res(Resolution::KnownLambdaPastArity)
                + count_res(Resolution::ClosureFromKnownCall)
                + count_res(Resolution::ComputedClosure),
            global_past_sig: count_res(Resolution::PastArity),
            lambda_no_demand: count_res(Resolution::KnownLambdaNoDemand),
            lambda_past_arity: count_res(Resolution::KnownLambdaPastArity),
            closure_from_known_call: count_res(Resolution::ClosureFromKnownCall),
            computed_closure: count_res(Resolution::ComputedClosure),
            tier_exact: count_tier(Tier::Exact),
            tier_finite: count_tier(Tier::FiniteSet),
            tier_producer_known: count_tier(Tier::ProducerKnown),
            tier_unresolved: count_tier(Tier::Unresolved),
            parsec_cps_sites: count_fam(&[
                Family::Parsec,
                Family::ParsecContinuation,
                Family::EtaParam,
            ]),
            tuple_sites: count_fam(&[Family::Tuple, Family::UnboxedTuple]),
            list_cons_sites: count_fam(&[Family::ListCons]),
            string_literal_args: census
                .args
                .iter()
                .filter(|a| a.shape == ArgShape::StringLiteral)
                .count(),
            tuple_cons_boxed: tuples
                .map(|t| t.accounting.constructions_boxed)
                .unwrap_or(0),
            tuple_cons_unboxed: tuples
                .map(|t| t.accounting.constructions_unboxed)
                .unwrap_or(0),
            tuple_scalar_boxed: tc(true, TupleFate::ScalarReplace),
            tuple_scalar_unboxed: tc(false, TupleFate::ScalarReplace),
            tuple_return_boxed: tc(true, TupleFate::WorkerReturn),
            tuple_return_unboxed: tc(false, TupleFate::WorkerReturn),
            tuple_clone_boxed: tc(true, TupleFate::RemovableWithClone),
            tuple_clone_unboxed: tc(false, TupleFate::RemovableWithClone),
            tuple_preserve_boxed: tc(true, TupleFate::Preserve),
            tuple_preserve_unboxed: tc(false, TupleFate::Preserve),
            tuple_unresolved_boxed: tc(true, TupleFate::Unresolved),
            tuple_unresolved_unboxed: tc(false, TupleFate::Unresolved),
            tuple_selected: tuples
                .map(|t| {
                    t.flows
                        .iter()
                        .filter(|f| {
                            f.selected
                                && matches!(
                                    f.fate,
                                    TupleFate::ScalarReplace | TupleFate::WorkerReturn
                                )
                        })
                        .count()
                })
                .unwrap_or(0),
            boundaries: tuples
                .map(|t| t.boundaries.iter().map(|b| b.reports.len()).sum())
                .unwrap_or(0),
            boundaries_uniform: tuples
                .map(|t| {
                    t.boundaries
                        .iter()
                        .flat_map(|b| b.reports.iter())
                        .filter(|r| r.verdict.ok())
                        .count()
                })
                .unwrap_or(0),
            flows_downgraded: tuples.map(|t| t.downgrades.len()).unwrap_or(0),
            tuple_removable_defuse: tc(true, TupleFate::ScalarReplace)
                + tc(false, TupleFate::ScalarReplace)
                + tc(true, TupleFate::WorkerReturn)
                + tc(false, TupleFate::WorkerReturn)
                + tuples.map(|t| t.downgrades.len()).unwrap_or(0),
            tuple_removable_composable: tc(true, TupleFate::ScalarReplace)
                + tc(false, TupleFate::ScalarReplace)
                + tc(true, TupleFate::WorkerReturn)
                + tc(false, TupleFate::WorkerReturn),
            tuple_removable_with_clone: tc(true, TupleFate::RemovableWithClone)
                + tc(false, TupleFate::RemovableWithClone),
        }
    }

    /// (label, value) pairs in display order.
    pub fn rows(&self) -> Vec<(&'static str, usize)> {
        vec![
            ("core nodes", self.core_nodes),
            ("top-level binds", self.top_level_binds),
            ("local binds", self.local_binds),
            ("  functions", self.functions),
            ("  join points", self.join_points),
            ("  strict shared", self.strict_shared),
            ("thunk sites", self.thunk_sites),
            ("  memo (sharing)", self.memo_sites),
            ("    under many-entry lambda", self.memo_under_lambda),
            ("    ok-for-speculation", self.memo_ok_for_spec),
            ("  lvl… float-outs", self.float_outs),
            ("  $d… dictionary lets", self.dictionary_lets),
            ("  recursive values", self.recursive_values),
            ("  sink eager", self.sink_eager),
            ("genuine CAFs", self.cafs),
            ("non-trivial args", self.nontrivial_args),
            ("  strict positions", self.strict_args),
            ("  unsaturated call positions", self.unsaturated_args),
            ("  lazy/unknown computations", self.lazy_computations),
            ("    exact callee", self.exact_callee),
            ("    class-op dispatch", self.class_op_sites),
            ("    dictionary family", self.dictionary_sites),
            ("    higher-order unknown", self.higher_order_unknown),
            ("    returned closures", self.past_arity),
            ("      global past signature", self.global_past_sig),
            ("      local lambda, no demand", self.lambda_no_demand),
            ("      local lambda, past arity", self.lambda_past_arity),
            (
                "      closure from known call",
                self.closure_from_known_call,
            ),
            ("      computed closure", self.computed_closure),
            ("    tier: exact target", self.tier_exact),
            ("    tier: finite target set", self.tier_finite),
            ("    tier: producer known", self.tier_producer_known),
            ("    tier: unresolved", self.tier_unresolved),
            ("    Parsec CPS", self.parsec_cps_sites),
            ("    tuple constructors", self.tuple_sites),
            ("    list cons", self.list_cons_sites),
            ("  string literal args", self.string_literal_args),
            ("tuple constructions, boxed", self.tuple_cons_boxed),
            ("  scalar replace", self.tuple_scalar_boxed),
            ("  multi-value return", self.tuple_return_boxed),
            ("  removable, needs a clone", self.tuple_clone_boxed),
            ("  preserve", self.tuple_preserve_boxed),
            ("  unresolved", self.tuple_unresolved_boxed),
            ("tuple constructions, unboxed", self.tuple_cons_unboxed),
            ("  scalar replace", self.tuple_scalar_unboxed),
            ("  multi-value return", self.tuple_return_unboxed),
            ("  removable, needs a clone", self.tuple_clone_unboxed),
            ("  preserve", self.tuple_preserve_unboxed),
            ("  unresolved", self.tuple_unresolved_unboxed),
            ("removable, field read alone", self.tuple_selected),
            ("removable locally (def-use)", self.tuple_removable_defuse),
            ("removable without cloning", self.tuple_removable_composable),
            (
                "  …only a clone could carry",
                self.tuple_removable_with_clone,
            ),
            ("representation boundaries", self.boundaries),
            ("  uniform split", self.boundaries_uniform),
            ("  flows downgraded", self.flows_downgraded),
            (
                "tuples removable %",
                (self.tuple_scalar_boxed
                    + self.tuple_scalar_unboxed
                    + self.tuple_return_boxed
                    + self.tuple_return_unboxed)
                    * 100
                    / (self.tuple_cons_boxed + self.tuple_cons_unboxed).max(1),
            ),
            // Ratios, so profiles of different size compare.
            (
                "thunk sites / 1k nodes",
                self.thunk_sites * 1000 / self.core_nodes.max(1),
            ),
            (
                "memo sites / 1k nodes",
                self.memo_sites * 1000 / self.core_nodes.max(1),
            ),
            (
                "lazy comps / 1k nodes",
                self.lazy_computations * 1000 / self.core_nodes.max(1),
            ),
            (
                "exact callee %",
                self.exact_callee * 100 / self.lazy_computations.max(1),
            ),
            (
                "exact target tier %",
                self.tier_exact * 100 / self.lazy_computations.max(1),
            ),
            (
                "unresolved tier %",
                self.tier_unresolved * 100 / self.lazy_computations.max(1),
            ),
            (
                "higher-order unknown %",
                self.higher_order_unknown * 100 / self.lazy_computations.max(1),
            ),
            (
                "Parsec CPS %",
                self.parsec_cps_sites * 100 / self.lazy_computations.max(1),
            ),
            (
                "strict arg %",
                self.strict_args * 100 / (self.strict_args + self.lazy_computations).max(1),
            ),
        ]
    }
}
