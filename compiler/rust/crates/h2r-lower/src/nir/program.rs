//! Partial program lowering. Every live owner has an explicit outcome; this is
//! not an executable program and does not promise dependency closure or a runtime.

use h2r_core_ir::Module;

use crate::reachability::LiveSet;

use super::{
    FnId,
    lower::{LowerError, LoweredLeaf, lower_leaf_in_world},
};

#[derive(Debug)]
pub struct ProgramAttempt {
    pub live: usize,
    pub dead: usize,
    /// Live library bindings, which are needed only at the instantiations
    /// the program's own code asks for, so no owner is lowered for them.
    pub library: usize,
    pub lowered: Vec<LoweredLeaf>,
    pub refused: Vec<LowerError>,
}

/// Construct and audit reachability from the same immutable source used for
/// lowering. Callers cannot supply a stale or unaudited live set.
pub fn lower_program(modules: &[Module]) -> Result<ProgramAttempt, String> {
    lower_program_owners(modules, |_| true)
}

/// As [`lower_program`], with owners only in the modules `owns` accepts.
pub fn lower_program_owners(
    modules: &[Module],
    owns: impl Fn(usize) -> bool,
) -> Result<ProgramAttempt, String> {
    let selected: Vec<_> = modules.iter().collect();
    let live = LiveSet::of_modules(selected.iter().copied())
        .map_err(|error| format!("the live graph has no root: {error}"))?;
    if !live.in_world_missing.is_empty() {
        return Err(
            "NIR requires complete in-world linkage; A5-IN-WORLD-MISSING is nonzero".into(),
        );
    }
    let audit = crate::verify::verify(&selected, &live);
    if audit.total_disagreements != 0 {
        return Err(format!(
            "reachability verification failed: {} disagreements",
            audit.total_disagreements
        ));
    }
    let mut attempt = ProgramAttempt {
        live: 0,
        dead: live.dead.len(),
        library: 0,
        lowered: Vec::new(),
        refused: Vec::new(),
    };
    // Source order, independent of reachability traversal order. The same node
    // IDs are used by the single-function CLI, including gaps for dead owners.
    for (node, binding) in live.nodes.iter().enumerate() {
        if !live.is_live(node as u32) {
            continue;
        }
        let index = binding.key.module as usize;
        if !owns(index) {
            attempt.library += 1;
            continue;
        }
        attempt.live += 1;
        match lower_leaf_in_world(modules, index, binding.key.binder, FnId(node as u32)) {
            Ok(leaf) => attempt.lowered.push(leaf),
            Err(error) => attempt.refused.push(error),
        }
    }
    if attempt.lowered.len() + attempt.refused.len() != attempt.live
        || attempt.live + attempt.library != live.live.len()
    {
        return Err("NIR live-owner accounting mismatch".into());
    }
    Ok(attempt)
}
