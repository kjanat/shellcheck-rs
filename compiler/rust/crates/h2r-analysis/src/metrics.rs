//! A flat set of headline numbers from a census, for comparing GHC
//! optimisation profiles side by side.

use serde::Serialize;

use crate::callee::{Family, Resolution};
use crate::laziness::{Census, Class, Fate, Origin, Sink, TopClass};
use crate::shape::ArgShape;

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
    pub lazy_computations: usize,
    pub exact_callee: usize,
    pub class_op_sites: usize,
    pub dictionary_sites: usize,
    pub higher_order_unknown: usize,
    pub past_arity: usize,
    pub parsec_cps_sites: usize,
    pub tuple_sites: usize,
    pub list_cons_sites: usize,
}

impl Metrics {
    pub fn of(census: &Census, core_nodes: usize, top_level_binds: usize) -> Metrics {
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
            lazy_computations: lazy.len(),
            exact_callee: count_res(Resolution::DataCon)
                + count_res(Resolution::ExactGlobal)
                + count_res(Resolution::ExactLocal),
            class_op_sites: count_res(Resolution::ClassOp),
            dictionary_sites: count_fam(&[Family::ClassOp, Family::Dictionary, Family::MonadOps]),
            higher_order_unknown: count_res(Resolution::HigherOrderParam),
            past_arity: count_res(Resolution::PastArity)
                + count_res(Resolution::KnownLambdaShortSig)
                + count_res(Resolution::ClosureFromKnownCall)
                + count_res(Resolution::ComputedClosure),
            parsec_cps_sites: count_fam(&[
                Family::Parsec,
                Family::ParsecContinuation,
                Family::EtaParam,
            ]),
            tuple_sites: count_fam(&[Family::Tuple, Family::UnboxedTuple]),
            list_cons_sites: count_fam(&[Family::ListCons]),
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
            ("  lazy/unknown computations", self.lazy_computations),
            ("    exact callee", self.exact_callee),
            ("    class-op dispatch", self.class_op_sites),
            ("    dictionary family", self.dictionary_sites),
            ("    higher-order unknown", self.higher_order_unknown),
            ("    returned closures", self.past_arity),
            ("    Parsec CPS", self.parsec_cps_sites),
            ("    tuple constructors", self.tuple_sites),
            ("    list cons", self.list_cons_sites),
        ]
    }
}
