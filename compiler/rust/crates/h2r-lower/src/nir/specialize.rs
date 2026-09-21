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

use super::lower::{LoweredLeaf, lower_leaf_specialized};
use super::subst::{type_depth, type_list_key};
use super::{DictionaryRef, FnId, Operation, same_dictionaries, same_types};

/// How many instances one owner may have before specialization refuses.
pub const OWNER_BUDGET: usize = 64;

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
) -> Result<Specialization, SpecializeError> {
    specialize_with(modules, roots, OnRefusal::Stop)
}

/// Lower every instance the roots reach and record what could not be lowered.
pub fn survey(modules: &[Module], roots: &[Instance]) -> Specialization {
    specialize_with(modules, roots, OnRefusal::Record)
        .expect("recording mode never returns a refusal")
}

/// Lower every instance the roots reach. Each is lowered exactly once, and an
/// instance already interned is reused, so a recursive cycle terminates.
pub fn specialize_with(
    modules: &[Module],
    roots: &[Instance],
    on_refusal: OnRefusal,
) -> Result<Specialization, SpecializeError> {
    let mut worklist = Worklist::default();
    for root in roots {
        if let Err(error) = worklist.intern(root.clone(), None)
            && let Some(error) = worklist.refuse(error, on_refusal)
        {
            return Err(error);
        }
    }
    while let Some(id) = worklist.pending.pop() {
        let instance = worklist.instances[id].clone();
        let leaf = match lower_leaf_specialized(
            modules,
            instance.module,
            instance.binder,
            FnId(id as u32),
            &instance.type_arguments,
            &instance.dictionaries,
        ) {
            Ok(leaf) => leaf,
            Err(error) => {
                let refusal = SpecializeError {
                    instance,
                    reason: match error.source {
                        Some(source) => format!("{} (at source expression {source})", error.reason),
                        None => error.reason.clone(),
                    },
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
            if let Err(error) = worklist.intern(instance, Some(id))
                && let Some(error) = worklist.refuse(error, on_refusal)
            {
                return Err(error);
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

    fn refuse(&mut self, error: SpecializeError, on_refusal: OnRefusal) -> Option<SpecializeError> {
        match on_refusal {
            OnRefusal::Stop => Some(error),
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
    ) -> Result<usize, SpecializeError> {
        let key = instance.key();
        if let Some(existing) = self.index.get(&key) {
            return Ok(*existing);
        }
        let fail = |reason: &str, this: &Worklist| SpecializeError {
            instance: instance.clone(),
            reason: reason.into(),
            path: parent.map_or_else(Vec::new, |p| this.path(p)),
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
                "one binding needed more instances than the per-owner budget; this instance chain does not terminate",
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
