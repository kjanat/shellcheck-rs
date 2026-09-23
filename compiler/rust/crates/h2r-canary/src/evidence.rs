//! Checking a fixture's evidence against the NIR, structurally.
//!
//! Every question here is asked of `Operation`, `Rule` and `Exit` values. A
//! check that read the pretty printer's text instead would be answering a
//! question about a diagnostic format, and would keep passing after the
//! lowering it was written for stopped happening.

use h2r_core_ir::{BinderId, Module};
use h2r_lower::nir::lower::{LoweredLeaf, lower_leaf_in_world};
use h2r_lower::nir::specialize::{Instance, Specialization, survey};
use h2r_lower::nir::{Exit, FnId, Operation, Rule, UnpackString};

use crate::fixtures::{Check, Evidence, Fixture, Op, Profile, RuleKind};

/// One binding, as the canary addresses it.
#[derive(Debug, Clone)]
pub struct Binding {
    pub module: usize,
    pub binder: BinderId,
    /// The stable name CoreTidy gave it, which is what `emit-rust` takes.
    pub name: String,
}

/// The one top-level binding with this occurrence name.
///
/// GHC decides on its own whether a top-level binding's name ends up external,
/// so the occurrence is what a fixture can name and the stable name is what it
/// resolves to.
/// Fixtures are the canary program's own bindings, unit `main`; the libraries
/// loaded beside it define names of their own.
pub fn resolve(modules: &[Module], occ: &str) -> Result<Binding, String> {
    let found: Vec<Binding> = modules
        .iter()
        .enumerate()
        .filter(|(_, loaded)| loaded.unit == "main")
        .flat_map(|(module, loaded)| {
            loaded
                .top
                .iter()
                .flat_map(|bind| &bind.pairs)
                .map(move |pair| (module, loaded, pair.binder))
        })
        .filter(|(_, loaded, binder)| loaded.binder(*binder).occ == occ)
        .map(|(module, loaded, binder)| Binding {
            module,
            binder,
            name: loaded.binder(binder).name.clone(),
        })
        .collect();
    match found.as_slice() {
        [one] => Ok(one.clone()),
        other => Err(format!(
            "{occ} names {} top-level bindings; a fixture must name exactly one",
            other.len()
        )),
    }
}

/// The NIR a fixture's checks are asked of, produced once per fixture and only
/// when something asks for it.
#[derive(Default)]
pub struct Facts {
    leaf: Option<Result<LoweredLeaf, String>>,
    closure: Option<Specialization>,
    source: Option<Result<String, String>>,
}

pub struct Subject<'a> {
    pub modules: &'a [Module],
    pub binding: &'a Binding,
    pub facts: Facts,
}

impl<'a> Subject<'a> {
    pub fn new(modules: &'a [Module], binding: &'a Binding) -> Subject<'a> {
        Subject {
            modules,
            binding,
            facts: Facts::default(),
        }
    }

    /// The owner lowered at its own signature, source-verified on the way out.
    fn leaf(&mut self) -> Result<&LoweredLeaf, String> {
        let modules = self.modules;
        let binding = self.binding;
        self.facts
            .leaf
            .get_or_insert_with(|| {
                lower_leaf_in_world(modules, binding.module, binding.binder, FnId(0))
                    .map_err(|error| error.reason)
            })
            .as_ref()
            .map_err(String::clone)
    }

    /// Every instance the owner reaches, each lowered and verified once.
    fn closure(&mut self) -> &Specialization {
        let modules = self.modules;
        let binding = self.binding;
        self.facts.closure.get_or_insert_with(|| {
            survey(modules, &[Instance::whole(binding.module, binding.binder)])
        })
    }

    /// The emitted Rust. Only a check that is about the output asks for this.
    fn source(&mut self, emitted: &Result<String, String>) -> Result<&str, String> {
        self.facts
            .source
            .get_or_insert_with(|| emitted.clone())
            .as_deref()
            .map_err(String::clone)
    }
}

/// Check one fixture's evidence for one profile. Returns what failed.
pub fn check(
    subject: &mut Subject<'_>,
    fixture: &Fixture,
    profile: Profile,
    emitted: &Result<String, String>,
) -> Vec<String> {
    fixture
        .evidence
        .iter()
        .filter(|Check { when, .. }| when.covers(profile))
        .filter_map(|Check { what, .. }| one(subject, *what, emitted).err())
        .collect()
}

fn one(
    subject: &mut Subject<'_>,
    what: Evidence,
    emitted: &Result<String, String>,
) -> Result<(), String> {
    match what {
        Evidence::Operation(op) => {
            let leaf = subject.leaf()?;
            if operations(leaf).any(|operation| matches(operation, op)) {
                return Ok(());
            }
            Err(format!("no {} in its NIR", op.name()))
        }
        Evidence::Rule(kind) => {
            let leaf = subject.leaf()?;
            if rules(leaf).any(|rule| carries(rule, kind)) {
                return Ok(());
            }
            Err(format!("no {} rule in its NIR", kind.name()))
        }
        Evidence::ScalarSwitch => {
            let leaf = subject.leaf()?;
            let switches = leaf
                .function
                .blocks
                .iter()
                .any(|block| matches!(block.terminator.exit, Exit::IntSwitch { .. }));
            if switches {
                return Ok(());
            }
            Err("its NIR does not switch on an unboxed scalar".into())
        }
        Evidence::InstancesComplete => {
            let closure = subject.closure();
            match closure.refused.as_slice() {
                [] => Ok(()),
                refused => Err(format!(
                    "{} of the {} instances it needs were refused; first: {}",
                    refused.len(),
                    closure.instances.len() + refused.len(),
                    refused[0].reason
                )),
            }
        }
        Evidence::InstancesOf { occ, count } => {
            let modules = subject.modules;
            let closure = subject.closure();
            let found = closure
                .instances
                .iter()
                .filter(|instance| modules[instance.module].binder(instance.binder).occ == occ)
                .count();
            if found == count {
                return Ok(());
            }
            Err(format!("{occ} has {found} instances, expected {count}"))
        }
        Evidence::SpecializedOn {
            type_arguments,
            dictionaries,
        } => {
            let closure = subject.closure();
            let found = closure.instances.iter().any(|instance| {
                instance.type_arguments.len() == type_arguments
                    && instance.dictionaries.len() == dictionaries
            });
            if found {
                return Ok(());
            }
            Err(format!(
                "no instance was specialized on {type_arguments} type arguments and {dictionaries} dictionaries"
            ))
        }
        Evidence::ClosureOperation(op) => {
            let closure = subject.closure();
            let found = closure
                .lowered
                .iter()
                .flatten()
                .flat_map(operations)
                .any(|operation| matches(operation, op));
            if found {
                return Ok(());
            }
            Err(format!(
                "no {} anywhere in the instances it needs",
                op.name()
            ))
        }
        Evidence::ClosureRule(kind) => {
            let closure = subject.closure();
            let found = closure
                .lowered
                .iter()
                .flatten()
                .flat_map(rules)
                .any(|rule| carries(rule, kind));
            if found {
                return Ok(());
            }
            Err(format!(
                "no {} rule anywhere in the instances it needs",
                kind.name()
            ))
        }
        Evidence::Emitted(text) => {
            let source = subject.source(emitted)?;
            if source.contains(text) {
                return Ok(());
            }
            Err(format!("the emitted Rust does not contain {text:?}"))
        }
    }
}

fn operations(leaf: &LoweredLeaf) -> impl Iterator<Item = &Operation> {
    leaf.function
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .map(|instruction| &instruction.operation)
}

fn rules(leaf: &LoweredLeaf) -> impl Iterator<Item = Rule> {
    leaf.function.blocks.iter().flat_map(|block| {
        block
            .instructions
            .iter()
            .map(|instruction| instruction.origin.rule)
            .chain(std::iter::once(block.terminator.origin.rule))
    })
}

fn carries(rule: Rule, kind: RuleKind) -> bool {
    match kind {
        RuleKind::LazyBinding => rule == Rule::LazyBinding,
        RuleKind::StrictBinding => rule == Rule::StrictBinding,
        RuleKind::EraseCast => rule == Rule::EraseCast,
        RuleKind::ResolveMethod => rule == Rule::ResolveMethod,
        RuleKind::Diverge => rule == Rule::Diverge,
        RuleKind::MagicLazy => rule == Rule::MagicLazy,
    }
}

fn matches(operation: &Operation, op: Op) -> bool {
    match op {
        Op::Construct => matches!(operation, Operation::Construct { .. }),
        Op::MakeUnboxedTuple => matches!(operation, Operation::MakeUnboxedTuple { .. }),
        Op::UnboxedTupleField => matches!(operation, Operation::UnboxedTupleField { .. }),
        Op::MatchData => matches!(operation, Operation::MatchData { .. }),
        Op::MakeClosure => matches!(operation, Operation::MakeClosure { .. }),
        Op::Apply => matches!(operation, Operation::Apply { .. }),
        Op::LocalScope => matches!(operation, Operation::LocalScope { .. }),
        Op::CallLocal => matches!(operation, Operation::CallLocal { .. }),
        Op::DelayBlock => matches!(operation, Operation::DelayBlock { .. }),
        Op::EvaluateBlock => matches!(operation, Operation::EvaluateBlock { .. }),
        Op::Move => matches!(operation, Operation::Move(_)),
        Op::OrdChar => matches!(operation, Operation::OrdChar(_)),
        Op::ChrChar => matches!(operation, Operation::ChrChar(_)),
        Op::CharCompare => matches!(operation, Operation::CharCompare { .. }),
        Op::Int(op) => matches!(operation, Operation::IntBinary { op: found, .. } if *found == op),
        Op::WordCompare => matches!(operation, Operation::WordCompare { .. }),
        Op::RaiseCallStackError => matches!(operation, Operation::RaiseCallStackError(_)),
        Op::UnpackString => matches!(operation, Operation::UnpackString(_)),
        Op::UnpackStringOnto => matches!(
            operation,
            Operation::UnpackString(unpack) if onto_a_tail(unpack)
        ),
        Op::AppendList => matches!(operation, Operation::AppendList { .. }),
        Op::CompareStrings => matches!(operation, Operation::CompareStrings(_)),
        Op::DataToTag => matches!(operation, Operation::DataToTag { .. }),
        Op::TagToEnum => matches!(operation, Operation::TagToEnum { .. }),
        Op::PointerEquality => matches!(operation, Operation::PointerEquality { .. }),
        Op::ListFunction(function) => matches!(
            operation,
            Operation::ListFunction(found) if found.function == function
        ),
        Op::ListPredicate(predicate, equality) => matches!(
            operation,
            Operation::ListPredicate(found)
                if found.predicate == predicate && found.equality == equality
        ),
    }
}

fn onto_a_tail(unpack: &UnpackString) -> bool {
    unpack.tail.is_some()
}
