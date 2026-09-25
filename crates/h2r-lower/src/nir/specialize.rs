//! The specialization worklist.
//!
//! An instance is a top-level binding together with the closed types and the
//! proven-unique dictionaries its leading lambdas were bound to. Instances are
//! interned under a canonical key derived from the structured types, so the
//! same instance reached by two different paths is lowered once and a recursive
//! call cycle reuses the instance it is already inside.
//!
//! Specialization is demand-driven: an instance's own NIR names the instances
//! it needs, and nothing else is lowered. Growth is bounded explicitly — a
//! polymorphic recursion whose type arguments keep growing is refused with the
//! chain that produced it rather than being allowed to run forever.

use std::collections::BTreeMap;

use h2r_core_ir::{BinderId, Module, Ty};

use super::lower::{LoweredLeaf, lower_leaf_unverified, type_lambda_counts};
use super::subst::{type_depth, type_list_key};
use super::{DictionaryRef, FnId, Operation, same_dictionaries, same_types};

/// How many instances one owner may have before specialization refuses.
pub const OWNER_BUDGET: usize = 1024;

/// How deeply an instance's type arguments may nest.
pub const TYPE_DEPTH_BUDGET: usize = 24;

/// How many instances one program may have.
pub const PROGRAM_BUDGET: usize = 100_000;

/// One instance of a top-level binding.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Instance {
    pub module: usize,
    pub binder: BinderId,
    pub type_arguments: Vec<Ty>,
    pub dictionaries: Vec<DictionaryRef>,
}

impl Instance {
    /// The whole binding, at its own signature.
    pub fn whole(module: usize, binder: BinderId) -> Instance {
        Instance {
            module,
            binder,
            type_arguments: Vec::new(),
            dictionaries: Vec::new(),
        }
    }

    pub fn of(reference: &DictionaryRef) -> Instance {
        Instance {
            module: reference.module,
            binder: reference.binder,
            type_arguments: reference.type_arguments.clone(),
            dictionaries: reference.dictionaries.clone(),
        }
    }

    pub fn same(&self, other: &Instance) -> bool {
        self.module == other.module
            && self.binder == other.binder
            && same_types(&self.type_arguments, &other.type_arguments)
            && same_dictionaries(&self.dictionaries, &other.dictionaries)
    }

    /// A canonical identity. Equal keys are exactly alpha-equivalent instances.
    pub fn key(&self) -> String {
        format!(
            "{};{};{}{}",
            self.module,
            self.binder,
            type_list_key(&self.type_arguments),
            dictionary_key(&self.dictionaries)
        )
    }

    fn depth(&self) -> usize {
        let types = self
            .type_arguments
            .iter()
            .map(type_depth)
            .max()
            .unwrap_or(0);
        let dictionaries = self
            .dictionaries
            .iter()
            .map(|d| Instance::of(d).depth())
            .max()
            .unwrap_or(0);
        types.max(dictionaries)
    }
}

fn dictionary_key(dictionaries: &[DictionaryRef]) -> String {
    let mut out = format!("{};", dictionaries.len());
    for dictionary in dictionaries {
        let key = Instance::of(dictionary).key();
        out.push_str(&format!("{}:{key}", key.len()));
    }
    out
}

#[derive(Debug, Clone)]
pub struct SpecializeError {
    pub instance: Instance,
    pub reason: String,
    /// The Core node the refusal was raised at, in the instance's own module.
    /// A budget refusal has none: it is decided before any body is read.
    pub source: Option<h2r_core_ir::ExprId>,
    /// The subject the refusal named, where it knew one: an external stable
    /// name, a type constructor. A ranking key, never evidence.
    pub detail: Option<String>,
    /// The instances that required this one, root first. A refusal names the
    /// path that reached it, not merely the binding that failed.
    pub path: Vec<Instance>,
}

impl std::fmt::Display for SpecializeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "module {} binder {} at {} type arguments and {} dictionaries: {} (required through {} instances)",
            self.instance.module,
            self.instance.binder,
            self.instance.type_arguments.len(),
            self.instance.dictionaries.len(),
            self.reason,
            self.path.len()
        )
    }
}

/// Whether a refusal ends the pass or is recorded and stepped over.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OnRefusal {
    /// Emission needs a complete closure: the first refusal ends the pass.
    Stop,
    /// Coverage wants the whole picture: record the refusal and carry on. The
    /// instances a refused one would have required stay unknown, so a survey
    /// is a lower bound on what the program needs.
    Record,
}

/// Every instance the roots require, each lowered and source-verified once.
#[derive(Debug)]
pub struct Specialization {
    pub instances: Vec<Instance>,
    /// Parallel to `instances`; `None` only for an instance in `refused`.
    pub lowered: Vec<Option<LoweredLeaf>>,
    /// Instances that could not be lowered. Always empty under [`OnRefusal::Stop`].
    pub refused: Vec<SpecializeError>,
    index: BTreeMap<String, usize>,
}

impl Specialization {
    /// Which instance a reference names, if it is part of this program.
    pub fn resolve(&self, reference: &DictionaryRef) -> Option<usize> {
        self.index.get(&Instance::of(reference).key()).copied()
    }

    /// Every instance, in interning order. Complete only after [`specialize`].
    pub fn leaf(&self, index: usize) -> Option<&LoweredLeaf> {
        self.lowered.get(index).and_then(Option::as_ref)
    }

    pub fn instance(&self, reference: &DictionaryRef) -> Option<&LoweredLeaf> {
        self.resolve(reference).and_then(|index| self.leaf(index))
    }

    /// How many instances lowered. A budget refusal is recorded before its
    /// instance is interned, so the population is this plus `refused` and
    /// never `instances.len()`.
    pub fn lowered_count(&self) -> usize {
        self.lowered.iter().flatten().count()
    }

    /// How many instances each owner needed, for coverage reporting.
    pub fn instances_per_owner(&self) -> BTreeMap<(usize, BinderId), usize> {
        let mut counts = BTreeMap::new();
        for instance in &self.instances {
            *counts
                .entry((instance.module, instance.binder))
                .or_insert(0) += 1;
        }
        counts
    }
}

/// Lower every instance the roots reach, stopping at the first refusal.
pub fn specialize(
    modules: &[Module],
    roots: &[Instance],
) -> Result<Specialization, Box<SpecializeError>> {
    specialize_with(modules, roots, OnRefusal::Stop)
}

/// Lower every instance the roots reach and record what could not be lowered.
pub fn survey(modules: &[Module], roots: &[Instance]) -> Specialization {
    specialize_with(modules, roots, OnRefusal::Record)
        .expect("recording mode never returns a refusal")
}

pub struct Progress<'a> {
    pub lowered: usize,
    pub interned: usize,
    pub pending: usize,
    pub instance: &'a Instance,
}

pub fn survey_observed(
    modules: &[Module],
    roots: &[Instance],
    observe: &mut dyn FnMut(&Progress<'_>),
) -> Specialization {
    specialize_observed(modules, roots, OnRefusal::Record, observe)
        .expect("recording mode never returns a refusal")
}

/// Lower every instance the roots reach. Each is lowered exactly once, and an
/// instance already interned is reused, so a recursive cycle terminates.
pub fn specialize_with(
    modules: &[Module],
    roots: &[Instance],
    on_refusal: OnRefusal,
) -> Result<Specialization, Box<SpecializeError>> {
    specialize_observed(modules, roots, on_refusal, &mut |_| {})
}

fn specialize_observed(
    modules: &[Module],
    roots: &[Instance],
    on_refusal: OnRefusal,
    observe: &mut dyn FnMut(&Progress<'_>),
) -> Result<Specialization, Box<SpecializeError>> {
    let mut worklist = Worklist::default();
    let catalog = super::Catalog::of(modules);
    let mut lowered = 0;
    for root in roots {
        if let Err(error) = worklist.intern(root.clone(), None)
            && let Some(error) = worklist.refuse(*error, on_refusal)
        {
            return Err(error);
        }
    }
    while let Some(id) = worklist.pending.pop() {
        let instance = worklist.instances[id].clone();
        observe(&Progress {
            lowered,
            interned: worklist.instances.len(),
            pending: worklist.pending.len(),
            instance: &instance,
        });
        lowered += 1;
        let leaf = match lower_leaf_unverified(
            modules,
            Some(&catalog),
            instance.module,
            instance.binder,
            FnId(id as u32),
            &instance.type_arguments,
            &instance.dictionaries,
        )
        .and_then(|(leaf, verified)| verified.map(|()| leaf))
        {
            Ok(leaf) => leaf,
            Err(error) => {
                let refusal = SpecializeError {
                    instance,
                    reason: match error.source {
                        Some(source) => format!("{} (at source expression {source})", error.reason),
                        None => error.reason.clone(),
                    },
                    source: error.source,
                    detail: error.detail.clone(),
                    path: worklist.path(id),
                };
                if let Some(error) = worklist.refuse(refusal, on_refusal) {
                    return Err(error);
                }
                continue;
            }
        };
        let required: Vec<_> = leaf
            .function
            .blocks
            .iter()
            .flat_map(|block| &block.instructions)
            .filter_map(|instruction| match &instruction.operation {
                Operation::TopReference {
                    module,
                    binder,
                    type_arguments,
                    dictionaries,
                }
                | Operation::CallTop {
                    module,
                    binder,
                    type_arguments,
                    dictionaries,
                    ..
                } => Some(Instance {
                    module: *module,
                    binder: *binder,
                    type_arguments: type_arguments.clone(),
                    dictionaries: dictionaries.clone(),
                }),
                _ => None,
            })
            .collect();
        worklist.lowered[id] = Some(leaf);
        for instance in required {
            let requested = instance.key();
            let instance = complete(modules, instance);
            let instance =
                erased_recursion(modules, &instance, &worklist.instances[id]).unwrap_or(instance);
            match worklist.intern(instance, Some(id)) {
                Ok(completed) => {
                    worklist.index.entry(requested).or_insert(completed);
                }
                Err(error) => {
                    if let Some(error) = worklist.refuse(*error, on_refusal) {
                        return Err(error);
                    }
                }
            }
        }
    }
    Ok(Specialization {
        instances: worklist.instances,
        lowered: worklist.lowered,
        refused: worklist.refused,
        index: worklist.index,
    })
}

fn complete(modules: &[Module], mut instance: Instance) -> Instance {
    let Some(module) = modules.get(instance.module) else {
        return instance;
    };
    let Some(pair) = module
        .top
        .iter()
        .flat_map(|b| &b.pairs)
        .find(|pair| pair.binder == instance.binder)
    else {
        return instance;
    };
    let (leading, _) = type_lambda_counts(module, pair.rhs, instance.binder);
    if instance.type_arguments.len() < leading {
        instance
            .type_arguments
            .resize(leading, super::data::erased_ty());
    }
    instance
}

fn erased_recursion(
    modules: &[Module],
    instance: &Instance,
    caller: &Instance,
) -> Option<Instance> {
    if (caller.module, caller.binder) != (instance.module, instance.binder)
        || !instance.dictionaries.is_empty()
        || !caller.dictionaries.is_empty()
        || instance.depth() <= caller.depth()
    {
        return None;
    }
    if instance.type_arguments.len() != caller.type_arguments.len() {
        return None;
    }
    let erased = Instance {
        type_arguments: instance
            .type_arguments
            .iter()
            .zip(&caller.type_arguments)
            .map(|(requested, current)| {
                if type_depth(requested) > type_depth(current) {
                    super::data::erased_ty()
                } else {
                    requested.clone()
                }
            })
            .collect(),
        ..instance.clone()
    };
    let world = super::World::of(modules, instance.module).ok()?;
    let reference = |instance: &Instance| {
        super::dict::reference_type(
            &world,
            &DictionaryRef {
                module: instance.module,
                binder: instance.binder,
                type_arguments: instance.type_arguments.clone(),
                dictionaries: Vec::new(),
            },
        )
        .ok()
    };
    same_carriers(&world, &reference(instance)?, &reference(&erased)?).then_some(erased)
}

fn same_carriers(world: &super::World<'_>, left: &Ty, right: &Ty) -> bool {
    use super::data::{Carrier, carrier, erase_quantifiers, unboxed_tuple_fields};
    let (left, right) = (erase_quantifiers(left), erase_quantifiers(right));
    if let (
        Ty::Fun {
            arg: la, res: lr, ..
        },
        Ty::Fun {
            arg: ra, res: rr, ..
        },
    ) = (&left, &right)
    {
        return same_carriers(world, la, ra) && same_carriers(world, lr, rr);
    }
    match (carrier(world, &left), carrier(world, &right)) {
        (Some(Carrier::Tuple), Some(Carrier::Tuple)) => {
            match (
                unboxed_tuple_fields(world, &left),
                unboxed_tuple_fields(world, &right),
            ) {
                (Ok(Some(l)), Ok(Some(r))) => {
                    l.len() == r.len() && l.iter().zip(&r).all(|(l, r)| same_carriers(world, l, r))
                }
                _ => false,
            }
        }
        (Some(l), Some(r)) => l == r,
        _ => false,
    }
}

#[derive(Default)]
struct Worklist {
    instances: Vec<Instance>,
    parents: Vec<Option<usize>>,
    lowered: Vec<Option<LoweredLeaf>>,
    refused: Vec<SpecializeError>,
    index: BTreeMap<String, usize>,
    owners: BTreeMap<(usize, BinderId), usize>,
    pending: Vec<usize>,
}

impl Worklist {
    /// The instances that required `node`, root first.
    fn path(&self, mut node: usize) -> Vec<Instance> {
        let mut chain = vec![self.instances[node].clone()];
        while let Some(parent) = self.parents[node] {
            chain.push(self.instances[parent].clone());
            node = parent;
        }
        chain.reverse();
        chain
    }

    fn refuse(
        &mut self,
        error: SpecializeError,
        on_refusal: OnRefusal,
    ) -> Option<Box<SpecializeError>> {
        match on_refusal {
            OnRefusal::Stop => Some(Box::new(error)),
            OnRefusal::Record => {
                self.refused.push(error);
                None
            }
        }
    }

    fn intern(
        &mut self,
        instance: Instance,
        parent: Option<usize>,
    ) -> Result<usize, Box<SpecializeError>> {
        let key = instance.key();
        if let Some(existing) = self.index.get(&key) {
            return Ok(*existing);
        }
        let fail = |reason: &str, this: &Worklist| {
            Box::new(SpecializeError {
                instance: instance.clone(),
                reason: reason.into(),
                source: None,
                detail: None,
                path: parent.map_or_else(Vec::new, |p| this.path(p)),
            })
        };
        if instance.depth() > TYPE_DEPTH_BUDGET {
            return Err(fail(
                "specialization type arguments grew past the nesting budget; this instance chain does not terminate",
                self,
            ));
        }
        if self.instances.len() >= PROGRAM_BUDGET {
            return Err(fail(
                "the program needed more instances than the whole-program budget",
                self,
            ));
        }
        let owner = self
            .owners
            .entry((instance.module, instance.binder))
            .or_insert(0);
        *owner += 1;
        if *owner > OWNER_BUDGET {
            return Err(fail(
                "one binding needed more instances than the per-owner budget",
                self,
            ));
        }
        let id = self.instances.len();
        self.instances.push(instance);
        self.parents.push(parent);
        self.lowered.push(None);
        self.pending.push(id);
        self.index.insert(key, id);
        Ok(id)
    }
}
