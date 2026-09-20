//! M3a on small hand-built worlds.
//!
//! The fixtures mirror `h2r-analysis`'s `class_module` builder rather than
//! reusing it: that builder is `#[cfg(test)]` inside its own crate, and
//! making it public would widen h2r-analysis for a convenience. What the
//! two share is the *shape* of a format-5 module, which is the dump's, not
//! either crate's.

use h2r_core_ir::{Module, raw};
use serde_json::{Value, json};

use crate::reachability::{
    A2_EDGE_LOCAL, A3_EDGE_GLOBAL, A12_EXTERNAL_UNIQUE, A13_GLOBAL_EXTERNAL, DeadReason, LinkError,
    LiveSet, NodeId, RootError,
};
use crate::verify::{
    V2_POPULATION, V3_LIVE_CLOSED, V4_DEAD_UNREFERENCED, V5_WITNESS, V6_EDGES, verify,
};

//------------------------------------------------------------------------------
// Fixtures
//------------------------------------------------------------------------------

const UNIT: &str = "u";

#[test]
fn nir_lowers_literal_with_source_origin() {
    use crate::nir::{FnId, Operation, Rule, Source, lower::lower_leaf};
    let m = module(
        "Main",
        vec![(binder(&sn("Main", "constant"), "constant", "c"), lit())],
        json!({}),
    );
    let pair = &m.top[0].pairs[0];
    let result = lower_leaf(&m, 3, pair.binder, FnId(7)).unwrap();
    assert_eq!(result.function.id, FnId(7));
    assert_eq!(result.function.owner, pair.binder);
    let instruction = &result.function.blocks[0].instructions[0];
    assert_eq!(instruction.origin.module, 3);
    assert_eq!(instruction.origin.source, Source::Expr(pair.rhs));
    assert_eq!(instruction.origin.rule, Rule::Literal);
    assert!(matches!(&instruction.operation, Operation::Literal(lit) if lit.pretty == "0"));
    assert!(result.parameters.is_empty());
    assert!(result.erased_ticks.is_empty());
}

#[test]
fn nir_lowers_identity_by_lexical_binder_not_name() {
    use crate::nir::{Exit, FnId, ValueId, lower::lower_leaf};
    use h2r_core_ir::Ty;
    // The lambda deliberately shadows the top-level binder's unique.
    let mut m = module(
        "Main",
        vec![(binder(&sn("Main", "id"), "id", "x"), lam("x", lvar("x")))],
        json!({}),
    );
    let owner = m.top[0].pairs[0].binder;
    let rhs = m.top[0].pairs[0].rhs;
    let ty = m.types[0].clone();
    m.types.push(Ty::Fun {
        mult: Box::new(ty.clone()),
        arg: Box::new(ty.clone()),
        res: Box::new(ty),
    });
    m.binders[owner as usize].ty = 1;
    let result = lower_leaf(&m, 0, owner, FnId(0)).unwrap();
    assert_eq!(result.parameters, vec![(rhs, ValueId(0))]);
    assert_eq!(result.function.blocks[0].params.len(), 1);
    assert!(result.function.blocks[0].instructions.is_empty());
    assert!(matches!(
        result.function.blocks[0].terminator.exit,
        Exit::Return(ValueId(0))
    ));
}

#[test]
fn nir_refuses_unsupported_core_with_source_address() {
    use crate::nir::{FnId, lower::lower_leaf};
    for rhs in [app(lit(), lit()), json!({"node": "Cast", "expr": lit()})] {
        let m = module(
            "Main",
            vec![(binder(&sn("Main", "f"), "f", "f"), rhs)],
            json!({}),
        );
        let pair = &m.top[0].pairs[0];
        let error = lower_leaf(&m, 2, pair.binder, FnId(0)).unwrap_err();
        assert_eq!(error.source, Some(pair.rhs));
        assert_eq!(error.module, 2);
        assert_eq!(error.owner, pair.binder);
    }
}

#[test]
fn nir_rejects_inconsistent_lambda_signatures() {
    use crate::nir::{FnId, lower::lower_leaf};
    use h2r_core_ir::Ty;
    let mut m = module(
        "Main",
        vec![(binder(&sn("Main", "id"), "id", "f"), lam("x", lvar("x")))],
        json!({}),
    );
    let owner = m.top[0].pairs[0].binder;
    assert!(
        lower_leaf(&m, 0, owner, FnId(0))
            .unwrap_err()
            .reason
            .contains("function type")
    );
    let original = m.types[0].clone();
    let other = Ty::Lit {
        kind: "Nat".into(),
        text: "2".into(),
    };
    m.types.push(Ty::Fun {
        mult: Box::new(original.clone()),
        arg: Box::new(other.clone()),
        res: Box::new(original.clone()),
    });
    m.binders[owner as usize].ty = 1;
    assert!(
        lower_leaf(&m, 0, owner, FnId(0))
            .unwrap_err()
            .reason
            .contains("parameter type mismatch")
    );
    m.types[1] = Ty::Fun {
        mult: Box::new(original.clone()),
        arg: Box::new(original),
        res: Box::new(other),
    };
    assert!(
        lower_leaf(&m, 0, owner, FnId(0))
            .unwrap_err()
            .reason
            .contains("returned parameter type mismatch")
    );
}

#[test]
fn nir_records_erased_ticks_and_rejects_nonlocal_returns() {
    use crate::nir::{FnId, lower::lower_leaf};
    let m = module(
        "Main",
        vec![(
            binder(&sn("Main", "f"), "f", "f"),
            json!({"node": "Tick", "expr": lit()}),
        )],
        json!({}),
    );
    let pair = &m.top[0].pairs[0];
    let result = lower_leaf(&m, 0, pair.binder, FnId(0)).unwrap();
    assert_eq!(result.erased_ticks, vec![pair.rhs]);
    let m = module(
        "Main",
        vec![(binder(&sn("Main", "f"), "f", "f"), lvar("f"))],
        json!({}),
    );
    assert!(
        lower_leaf(&m, 0, m.top[0].pairs[0].binder, FnId(0))
            .unwrap_err()
            .reason
            .contains("non-parameter")
    );
    assert!(
        lower_leaf(&m, 0, u32::MAX, FnId(0))
            .unwrap_err()
            .source
            .is_none()
    );
}

#[test]
fn nir_source_verifier_checks_literal_payload_and_origins() {
    use crate::nir::{
        FnId, Operation, Rule, Source,
        lower::lower_leaf,
        verify::{verify, verify_leaf},
    };
    let m = module(
        "Main",
        vec![(binder(&sn("Main", "f"), "f", "f"), lit())],
        json!({}),
    );
    let owner = m.top[0].pairs[0].binder;
    let original = lower_leaf(&m, 0, owner, FnId(0)).unwrap();
    let accounting = verify_leaf(&m, 0, owner, FnId(0), &original).unwrap();
    assert_eq!(accounting.source_nodes, 1);
    assert_eq!(accounting.value_nodes, 1);
    for corruption in 0..6 {
        let mut candidate = original.clone();
        let block = &mut candidate.function.blocks[0];
        match corruption {
            0 | 1 => {
                let Operation::Literal(literal) = &mut block.instructions[0].operation else {
                    unreachable!()
                };
                if corruption == 0 {
                    literal.pretty = "42".into();
                } else {
                    literal.kind = "string".into();
                }
            }
            2 => block.instructions[0].origin.source = Source::Expr(u32::MAX),
            3 => block.instructions[0].origin.rule = Rule::EraseCast,
            4 => block.terminator.origin.source = Source::Binder(owner),
            _ => block.terminator.origin.rule = Rule::Jump,
        }
        // All these corruptions pass structural verification.
        verify(&candidate.function).unwrap();
        assert!(
            verify_leaf(&m, 0, owner, FnId(0), &candidate).is_err(),
            "corruption {corruption}"
        );
    }
}

fn nir_two_parameter_module() -> Module {
    use h2r_core_ir::Ty;
    let mut m = module(
        "Main",
        vec![(
            binder(&sn("Main", "first"), "first", "f"),
            lam("x", lam("y", lvar("x"))),
        )],
        json!({}),
    );
    let ty = m.types[0].clone();
    let inner = Ty::Fun {
        mult: Box::new(ty.clone()),
        arg: Box::new(ty.clone()),
        res: Box::new(ty.clone()),
    };
    m.types.push(Ty::Fun {
        mult: Box::new(ty.clone()),
        arg: Box::new(ty),
        res: Box::new(inner),
    });
    let owner = m.top[0].pairs[0].binder;
    m.binders[owner as usize].ty = 1;
    m
}

#[test]
fn nir_source_verifier_rejects_wrong_parameter_and_added_force() {
    use crate::nir::{
        Exit, FnId, Instruction, Operation, Rule, Value, ValueId,
        lower::lower_leaf,
        verify::{verify, verify_leaf},
    };
    let m = nir_two_parameter_module();
    let owner = m.top[0].pairs[0].binder;
    let original = lower_leaf(&m, 0, owner, FnId(0)).unwrap();
    let accounting = verify_leaf(&m, 0, owner, FnId(0), &original).unwrap();
    assert_eq!(accounting.source_nodes, 3);
    assert_eq!(accounting.parameter_nodes, 2);
    for corruption in 0..4 {
        let mut candidate = original.clone();
        let block = &mut candidate.function.blocks[0];
        match corruption {
            0 => block.terminator.exit = Exit::Return(block.params[1].id),
            1 => candidate.parameters.swap(0, 1),
            2 => candidate.parameters[0].0 = u32::MAX,
            _ => {
                let mut origin = block.terminator.origin.clone();
                origin.rule = Rule::StrictPosition;
                block.instructions.push(Instruction {
                    result: Value {
                        id: ValueId(2),
                        ty: block.params[0].ty.clone(),
                    },
                    operation: Operation::Force(block.params[0].id),
                    origin,
                });
                block.terminator.exit = Exit::Return(ValueId(2));
            }
        }
        verify(&candidate.function).unwrap();
        assert!(
            verify_leaf(&m, 0, owner, FnId(0), &candidate).is_err(),
            "corruption {corruption}"
        );
    }
    // Numeric IDs are not semantic identities: consistent renumbering is valid.
    let mut renamed = original;
    renamed.function.blocks[0].params[0].id = ValueId(99);
    renamed.function.blocks[0].terminator.exit = Exit::Return(ValueId(99));
    renamed.parameters[0].1 = ValueId(99);
    verify_leaf(&m, 0, owner, FnId(0), &renamed).unwrap();
}

#[test]
fn nir_source_verifier_accounts_for_ticks_and_checks_identity() {
    use crate::nir::{FnId, lower::lower_leaf, verify::verify_leaf};
    let m = module(
        "Main",
        vec![(
            binder(&sn("Main", "f"), "f", "f"),
            json!({"node": "Tick", "expr": {"node": "Tick", "expr": lit()}}),
        )],
        json!({}),
    );
    let owner = m.top[0].pairs[0].binder;
    let original = lower_leaf(&m, 4, owner, FnId(7)).unwrap();
    let accounting = verify_leaf(&m, 4, owner, FnId(7), &original).unwrap();
    assert_eq!(accounting.source_nodes, 3);
    assert_eq!(accounting.erased_ticks, 2);
    for corruption in 0..5 {
        let mut candidate = original.clone();
        match corruption {
            0 => {
                candidate.erased_ticks.pop();
            }
            1 => candidate.erased_ticks.push(candidate.erased_ticks[0]),
            2 => candidate.erased_ticks.reverse(),
            3 => candidate.function.owner = u32::MAX,
            _ => candidate.function.id = FnId(99),
        }
        assert!(
            verify_leaf(&m, 4, owner, FnId(7), &candidate).is_err(),
            "corruption {corruption}"
        );
    }
    assert!(verify_leaf(&m, 5, owner, FnId(7), &original).is_err());
}

#[test]
fn nir_source_verifier_rejects_forged_types_and_unsupported_source() {
    use crate::nir::{
        FnId,
        lower::lower_leaf,
        verify::{verify, verify_leaf},
    };
    let mut m = nir_two_parameter_module();
    let owner = m.top[0].pairs[0].binder;
    let mut candidate = lower_leaf(&m, 0, owner, FnId(0)).unwrap();
    let forged = h2r_core_ir::Ty::Lit {
        kind: "Nat".into(),
        text: "42".into(),
    };
    candidate.function.result_ty = forged.clone();
    candidate.function.blocks[0].params[0].ty = forged;
    verify(&candidate.function).unwrap();
    assert!(verify_leaf(&m, 0, owner, FnId(0), &candidate).is_err());
    let original = lower_leaf(&m, 0, owner, FnId(0)).unwrap();
    let rhs = m.top[0].pairs[0].rhs;
    m.exprs[rhs as usize] = h2r_core_ir::Expr::Coercion;
    assert!(
        verify_leaf(&m, 0, owner, FnId(0), &original)
            .unwrap_err()
            .contains("unsupported leaf source")
    );
}

/// The one-entry type table every fixture carries. Nothing in M3a reads a
/// type; the table exists because format 5 has one.
fn ty_table() -> Value {
    json!([{
        "kind": "TyConApp",
        "tycon": {"name": "$u$M$T", "occ": "T", "unique": "T"},
        "args": []
    }])
}

fn demand() -> Value {
    json!({"strict": false, "absent": false, "usedOnce": false, "pretty": "L"})
}

/// A top-level binder with an explicit stable name and unique.
fn binder(name: &str, occ: &str, unique: &str) -> Value {
    json!({
        "kind": "id", "name": name, "occ": occ, "unique": unique,
        "type": "T", "ty": 0,
        "arity": 0, "callArity": 0, "exported": true,
        "dmdSig": {"args": [], "diverges": false, "pretty": ""},
        "cprSig": "", "demand": demand(),
        "occInfo": {"kind": "many", "tailCalled": false}, "oneShot": false,
        "details": "", "hasUnfolding": false, "isJoinPoint": false, "isDataCon": false
    })
}

/// A local occurrence: resolved by unique, never by name.
fn lvar(unique: &str) -> Value {
    json!({"node": "Var", "name": "?", "occ": unique, "unique": unique, "isGlobal": false})
}

/// A global occurrence, with the stable name that is its only linkage.
fn gvar(name: &str, occ: &str) -> Value {
    json!({"node": "Var", "name": name, "occ": occ, "unique": occ, "isGlobal": true})
}

fn app(f: Value, a: Value) -> Value {
    json!({"node": "App", "fun": f, "arg": a})
}

fn lam(unique: &str, body: Value) -> Value {
    json!({"node": "Lam", "binder": binder("$_sys$p", unique, unique), "body": body})
}

fn lit() -> Value {
    json!({"node": "Lit", "lit": {"kind": "int", "pretty": "0"}})
}

/// The stable name of a top-level binding of `module`.
fn sn(module: &str, occ: &str) -> String {
    format!("${UNIT}${module}${occ}")
}

/// A module of independent top-level pairs.
fn module(name: &str, pairs: Vec<(Value, Value)>, ids: Value) -> Module {
    let binds: Vec<Value> = pairs
        .into_iter()
        .map(|(b, rhs)| {
            json!({"rec": false, "pairs": [{
                "binder": b, "rhs": rhs,
                "whnf": false, "trivial": false, "cheap": false, "okForSpec": false
            }]})
        })
        .collect();
    let m = json!({
        "format": raw::FORMAT, "module": name, "unit": UNIT,
        "types": ty_table(), "ids": ids, "binds": binds
    });
    Module::from_raw(serde_json::from_value(m).unwrap()).unwrap()
}

/// The world every reachability test uses.
///
/// ```text
/// Main.main   -> Main.helper (A2, local)  -> L.leaf (A3, global)
///             -> L.exported (A3, global)  -> L.$_sys$w#1 (A2, local, internal name)
/// Main.shadow -- a lambda parameter shadowing helper's unique: not an edge
/// Main.orphan -- no occurrence anywhere
/// Main.deadA  -> Main.deadB               -- both dead, deadB only from dead
/// L.unused    -- no occurrence anywhere
/// L.$_sys$w#2 -- the second binding of the same internal name: dead
/// ```
fn world() -> (Module, Module) {
    let main = module(
        "Main",
        vec![
            (
                binder(&sn("Main", "main"), "main", "main"),
                app(
                    app(lvar("helper"), gvar(&sn("L", "exported"), "exported")),
                    lvar("shadow"),
                ),
            ),
            (
                binder(&sn("Main", "helper"), "helper", "helper"),
                gvar(&sn("L", "leaf"), "leaf"),
            ),
            // A lambda binder whose unique is `helper`'s: the occurrence in
            // the body resolves to the parameter, so it is not an edge.
            (
                binder(&sn("Main", "shadow"), "shadow", "shadow"),
                lam("helper", lvar("helper")),
            ),
            (binder(&sn("Main", "orphan"), "orphan", "orphan"), lit()),
            (
                binder(&sn("Main", "deadA"), "deadA", "deadA"),
                lvar("deadB"),
            ),
            (binder(&sn("Main", "deadB"), "deadB", "deadB"), lit()),
        ],
        json!({}),
    );
    let l = module(
        "L",
        vec![
            (
                binder(&sn("L", "exported"), "exported", "exported"),
                lvar("w1"),
            ),
            (binder(&sn("L", "leaf"), "leaf", "leaf"), lit()),
            (binder("$_sys$w", "w", "w1"), lit()),
            (binder("$_sys$w", "w", "w2"), lit()),
            (binder(&sn("L", "unused"), "unused", "unused"), lit()),
        ],
        json!({}),
    );
    (main, l)
}

fn live_of(ms: &[&Module]) -> LiveSet {
    LiveSet::of_modules(ms.iter().copied()).expect("a world with a root")
}

fn node_named(l: &LiveSet, module: &str, occ: &str) -> NodeId {
    let hits: Vec<NodeId> = (0..l.nodes.len() as NodeId)
        .filter(|&n| l.nodes[n as usize].module_name == module && l.nodes[n as usize].occ == occ)
        .collect();
    assert_eq!(hits.len(), 1, "{module}.{occ} is not unique in the fixture");
    hits[0]
}

//------------------------------------------------------------------------------
// The live set
//------------------------------------------------------------------------------

#[test]
fn the_closure_is_rooted_and_crosses_modules() {
    let (main, l) = world();
    let ms: Vec<&Module> = vec![&main, &l];
    let live = live_of(&ms);

    assert_eq!(live.roots.len(), 1);
    assert_eq!(live.node(live.roots[0].node).occ, "main");

    let want_live = [
        "Main.main",
        "Main.helper",
        "Main.shadow",
        "L.exported",
        "L.leaf",
    ];
    for n in 0..live.nodes.len() as NodeId {
        let t = live.node(n);
        let key = format!("{}.{}", t.module_name, t.occ);
        let expected = want_live.contains(&key.as_str())
            // the first $_sys$w, reached from L.exported by BinderId
            || (t.module_name == "L" && t.occ == "w" && live.is_live(n));
        assert_eq!(
            live.is_live(n),
            expected,
            "{key} (binder {}) liveness",
            t.key.binder
        );
    }
    // Exactly one of the two same-named internal bindings is live.
    let w: Vec<NodeId> = (0..live.nodes.len() as NodeId)
        .filter(|&n| live.node(n).name == "$_sys$w")
        .collect();
    assert_eq!(w.len(), 2);
    assert_eq!(w.iter().filter(|&&n| live.is_live(n)).count(), 1);
}

#[test]
fn a_shadowing_lambda_parameter_is_not_an_edge() {
    let (main, l) = world();
    let ms: Vec<&Module> = vec![&main, &l];
    let live = live_of(&ms);
    let shadow = node_named(&live, "Main", "shadow");
    let helper = node_named(&live, "Main", "helper");
    assert!(
        !live
            .edges
            .iter()
            .any(|e| e.from == shadow && e.to == helper),
        "the occurrence in shadow's body resolves to its own lambda binder"
    );
}

#[test]
fn both_dead_reasons_and_their_referrers() {
    let (main, l) = world();
    let ms: Vec<&Module> = vec![&main, &l];
    let live = live_of(&ms);

    for (module, occ, reason) in [
        ("Main", "orphan", DeadReason::DeadNoReferences),
        ("Main", "deadA", DeadReason::DeadNoReferences),
        ("Main", "deadB", DeadReason::DeadReferencedOnlyFromDead),
        ("L", "unused", DeadReason::DeadNoReferences),
    ] {
        let n = node_named(&live, module, occ);
        let d = live
            .dead_of(n)
            .unwrap_or_else(|| panic!("{module}.{occ} dead"));
        assert_eq!(d.reason, reason, "{module}.{occ}");
    }
    let dead_b = node_named(&live, "Main", "deadB");
    let dead_a = node_named(&live, "Main", "deadA");
    assert_eq!(live.dead_of(dead_b).unwrap().referrers, vec![dead_a]);
    assert!(live.dead_of(dead_a).unwrap().referrers.is_empty());
}

#[test]
fn every_witness_starts_at_the_root_and_names_its_rule() {
    let (main, l) = world();
    let ms: Vec<&Module> = vec![&main, &l];
    let live = live_of(&ms);
    let root = live.roots[0].node;
    for b in &live.live {
        assert_eq!(b.witness.first(), Some(&root));
        assert_eq!(b.witness.last(), Some(&b.node));
    }
    // L.leaf is reached in two hops: main -> helper -> leaf, the second of
    // them by stable name.
    let leaf = node_named(&live, "L", "leaf");
    let helper = node_named(&live, "Main", "helper");
    assert_eq!(
        live.live_of(leaf).unwrap().witness,
        vec![root, helper, leaf]
    );
    let e = live
        .edges
        .iter()
        .find(|e| e.from == helper && e.to == leaf)
        .expect("the inter-module edge");
    assert_eq!(e.rule, A3_EDGE_GLOBAL);
    let e = live
        .edges
        .iter()
        .find(|e| e.from == root && e.to == helper)
        .expect("the intra-module edge");
    assert_eq!(e.rule, A2_EDGE_LOCAL);
}

#[test]
fn the_accounting_closes() {
    let (main, l) = world();
    let ms: Vec<&Module> = vec![&main, &l];
    let live = live_of(&ms);
    let a = &live.accounting;
    assert!(a.check().is_empty(), "{:?}", a.check());
    assert_eq!(a.top, 11);
    assert_eq!(a.top, a.live + a.dead);
    assert_eq!(a.dead, a.dead_no_refs + a.dead_only_from_dead);
    // The zero-reference subset is strictly smaller than the rooted dead
    // set: deadB is referenced and still dead. The root is zero-reference
    // by construction and is the one live member.
    assert_eq!(a.zero_reference_roots, 1);
    assert_eq!(a.zero_reference_live, 0);
    assert!(a.additional_dead >= 1);
}

#[test]
fn imports_and_the_in_world_hole_are_different_categories() {
    let main = module(
        "Main",
        vec![(
            binder(&sn("Main", "main"), "main", "main"),
            app(
                gvar("$base$GHC.Base$map", "map"),
                gvar(&sn("L", "ghost"), "ghost"),
            ),
        )],
        json!({}),
    );
    let l = module(
        "L",
        vec![(binder(&sn("L", "real"), "real", "real"), lit())],
        json!({}),
    );
    let ms: Vec<&Module> = vec![&main, &l];
    let live = live_of(&ms);

    assert_eq!(live.imports.len(), 1);
    assert_eq!(live.imports["$base$GHC.Base$map"].from_live, 1);
    assert_eq!(live.in_world_missing.len(), 1);
    let m = &live.in_world_missing[0];
    assert_eq!(m.name, sn("L", "ghost"));
    assert_eq!(m.in_module, "L");
    assert!(m.referenced_from_live);
    assert!(m.candidates.is_empty());
    assert_eq!(live.accounting.missing_impact.would_become_live, 0);
}

#[test]
fn a_name_matched_candidate_bounds_the_hole_without_making_an_edge() {
    // L's binding carries the *internal* name CoreTidy has not yet
    // replaced; Main refers to it by the external one. No edge is made —
    // and A11 says what that costs.
    let main = module(
        "Main",
        vec![(
            binder(&sn("Main", "main"), "main", "main"),
            gvar(&sn("L", "$wgo"), "$wgo"),
        )],
        json!({}),
    );
    let l = module(
        "L",
        vec![
            (binder("$_in$$wgo", "$wgo", "wgo"), lvar("tail")),
            (binder(&sn("L", "tail"), "tail", "tail"), lit()),
        ],
        json!({}),
    );
    let ms: Vec<&Module> = vec![&main, &l];
    let live = live_of(&ms);

    assert_eq!(live.in_world_missing.len(), 1);
    let m = &live.in_world_missing[0];
    assert_eq!(m.candidates.len(), 1);
    assert_eq!(m.candidates_dead, 1);
    assert_eq!(m.live_referrer_modules, vec!["Main".to_string()]);
    // Both L bindings are dead, and both would be live if the name were
    // an edge. The bound is reported; the verdict is not moved.
    assert_eq!(live.accounting.live, 1);
    assert_eq!(live.accounting.missing_impact.would_become_live, 2);
    assert!(!live.is_live(node_named(&live, "L", "$wgo")));
}

#[test]
fn a_world_without_a_root_fails_with_a_named_reason() {
    let l = module(
        "L",
        vec![(binder(&sn("L", "x"), "x", "x"), lit())],
        json!({}),
    );
    let ms: Vec<&Module> = vec![&l];
    assert_eq!(LiveSet::of_modules(ms).err(), Some(RootError::NoMainModule));

    let main = module(
        "Main",
        vec![(binder(&sn("Main", "notMain"), "notMain", "n"), lit())],
        json!({}),
    );
    let ms: Vec<&Module> = vec![&main];
    assert_eq!(
        LiveSet::of_modules(ms).err(),
        Some(RootError::NoRootBinding(sn("Main", "main")))
    );
}

#[test]
fn two_runs_are_byte_identical() {
    let (main, l) = world();
    let ms: Vec<&Module> = vec![&main, &l];
    let a = serde_json::to_string(&live_of(&ms)).unwrap();
    let b = serde_json::to_string(&live_of(&ms)).unwrap();
    assert_eq!(a, b);
}

//------------------------------------------------------------------------------
// The verifier, and what makes it bite
//------------------------------------------------------------------------------

fn audit_fails_on(check: &str, corrupt: impl Fn(&mut LiveSet)) {
    let (main, l) = world();
    let ms: Vec<&Module> = vec![&main, &l];
    let mut live = live_of(&ms);
    assert!(
        verify(&ms, &live).ok(),
        "the fixture must verify clean first"
    );
    corrupt(&mut live);
    let audit = verify(&ms, &live);
    assert!(!audit.ok(), "the verifier accepted a corrupted live set");
    assert!(
        audit
            .checks
            .iter()
            .any(|c| c.check == check && c.disagreements > 0),
        "{check} did not fire; disagreements: {:?}",
        audit.disagreements
    );
}

#[test]
fn the_verifier_confirms_the_real_world() {
    let (main, l) = world();
    let ms: Vec<&Module> = vec![&main, &l];
    let live = live_of(&ms);
    let audit = verify(&ms, &live);
    assert_eq!(audit.total_disagreements, 0, "{:?}", audit.disagreements);
    assert!(audit.total_population > 0);
}

#[test]
fn moving_a_binding_from_dead_to_live_is_caught() {
    // L.unused has no occurrence anywhere; claiming it live leaves a
    // witness hop that is not an edge.
    audit_fails_on(V5_WITNESS, |live| {
        let n = node_named(live, "L", "unused");
        let root = live.roots[0].node;
        live.dead.retain(|d| d.node != n);
        live.live.push(crate::reachability::LiveBinding {
            node: n,
            witness: vec![root, n],
            rule: crate::reachability::A9_WITNESS,
        });
        live.live.sort_by_key(|x| x.node);
        live.accounting.live += 1;
        live.accounting.dead -= 1;
        live.accounting.dead_no_refs -= 1;
    });
}

#[test]
fn moving_a_referenced_binding_from_live_to_dead_is_caught() {
    // L.leaf is named by the live Main.helper; calling it dead breaks
    // both directions of the closure check.
    for check in [V3_LIVE_CLOSED, V4_DEAD_UNREFERENCED] {
        audit_fails_on(check, |live| {
            let n = node_named(live, "L", "leaf");
            live.live.retain(|x| x.node != n);
            live.dead.push(crate::reachability::DeadBinding {
                node: n,
                reason: DeadReason::DeadReferencedOnlyFromDead,
                referrers: vec![node_named(live, "Main", "helper")],
                rule: DeadReason::DeadReferencedOnlyFromDead.rule(),
            });
            live.dead.sort_by_key(|x| x.node);
            live.accounting.live -= 1;
            live.accounting.dead += 1;
            live.accounting.dead_only_from_dead += 1;
        });
    }
}

#[test]
fn a_broken_witness_is_caught() {
    audit_fails_on(V5_WITNESS, |live| {
        let n = node_named(live, "L", "leaf");
        let i = live.live.iter().position(|x| x.node == n).unwrap();
        // Drop the root: the path no longer starts at one.
        live.live[i].witness.remove(0);
    });
}

#[test]
fn a_dropped_edge_is_caught() {
    audit_fails_on(V6_EDGES, |live| {
        let helper = node_named(live, "Main", "helper");
        let leaf = node_named(live, "L", "leaf");
        live.edges.retain(|e| !(e.from == helper && e.to == leaf));
        live.accounting.edges -= 1;
        live.accounting.edges_global -= 1;
    });
}

#[test]
fn an_invented_edge_is_caught() {
    audit_fails_on(V6_EDGES, |live| {
        let orphan = node_named(live, "Main", "orphan");
        let leaf = node_named(live, "L", "leaf");
        live.edges.push(crate::reachability::EdgeRef {
            from: orphan,
            to: leaf,
            occurrences: 1,
            rule: A3_EDGE_GLOBAL,
        });
        live.accounting.edges += 1;
        live.accounting.edges_global += 1;
    });
}

#[test]
fn a_binding_with_two_verdicts_is_caught() {
    audit_fails_on(V2_POPULATION, |live| {
        let n = node_named(live, "Main", "orphan");
        let root = live.roots[0].node;
        live.live.push(crate::reachability::LiveBinding {
            node: n,
            witness: vec![root, n],
            rule: crate::reachability::A9_WITNESS,
        });
        live.live.sort_by_key(|x| x.node);
    });
}

//------------------------------------------------------------------------------
// The link view (A12-EXTERNAL-UNIQUE)
//------------------------------------------------------------------------------

#[test]
fn link_names_the_one_defining_binding_and_its_referrers() {
    let (main, l) = world();
    let ms: Vec<&Module> = vec![&main, &l];
    let live = live_of(&ms);

    // `L.exported` is defined once, in L, and named from Main (globally, by
    // stable name) and from nowhere else.
    let link = live.link(&sn("L", "exported")).expect("a linkable name");
    assert_eq!(link.node, node_named(&live, "L", "exported"));
    assert_eq!(link.rule, A12_EXTERNAL_UNIQUE);
    assert_eq!(link.referrers.len(), 1);
    assert_eq!(link.referrers[0].module, "Main");
    assert_eq!(link.referrers[0].rule, A3_EDGE_GLOBAL);
    assert_eq!(link.referrers[0].bindings, 1);
    assert_eq!(link.referrers[0].occurrences, 1);

    // It is live, and the witness is the real chain Main.main -> L.exported.
    let w = link.witness.expect("L.exported is live");
    assert_eq!(w.len(), 2);
    assert_eq!(live.named(w[0]).1, sn("Main", "main"));
    assert_eq!(w[1], link.node);
}

#[test]
fn link_crosses_a_module_through_a_local_hop() {
    let (main, l) = world();
    let ms: Vec<&Module> = vec![&main, &l];
    let live = live_of(&ms);

    // `L.leaf` is named only by `Main.helper`, which `Main.main` reaches
    // locally: the witness is three nodes long and mixes both edge rules.
    let link = live.link(&sn("L", "leaf")).expect("a linkable name");
    assert_eq!(link.referrers.len(), 1);
    assert_eq!(link.referrers[0].module, "Main");
    assert_eq!(link.referrers[0].rule, A3_EDGE_GLOBAL);
    let w = link.witness.expect("L.leaf is live");
    assert_eq!(
        w.iter().map(|&n| live.named(n).1).collect::<Vec<_>>(),
        vec![sn("Main", "main"), sn("Main", "helper"), sn("L", "leaf")]
    );
}

#[test]
fn link_refuses_an_internal_name_because_it_is_not_an_identity() {
    let (main, l) = world();
    let ms: Vec<&Module> = vec![&main, &l];
    let live = live_of(&ms);

    // Two top-level bindings of L render as `$_sys$w`. The name is internal,
    // so the link view refuses it rather than picking one.
    assert_eq!(
        (0..live.nodes.len() as NodeId)
            .filter(|&n| live.node(n).name == "$_sys$w")
            .count(),
        2
    );
    assert_eq!(live.link("$_sys$w").err(), Some(LinkError::InternalName));
}

#[test]
fn link_says_not_found_rather_than_guessing() {
    let (main, l) = world();
    let ms: Vec<&Module> = vec![&main, &l];
    let live = live_of(&ms);
    assert_eq!(
        live.link(&sn("L", "nosuch")).err(),
        Some(LinkError::NotFound)
    );
    // An occurrence name is not a stable name, and is not accepted as one.
    assert_eq!(live.link("exported").err(), Some(LinkError::InternalName));
}

#[test]
fn link_reports_a_dead_binding_as_dead_with_no_witness() {
    let (main, l) = world();
    let ms: Vec<&Module> = vec![&main, &l];
    let live = live_of(&ms);
    let link = live.link(&sn("L", "unused")).expect("a linkable name");
    assert!(link.witness.is_none());
    assert!(link.referrers.is_empty());
    assert_eq!(
        live.dead_of(link.node).map(|d| d.reason),
        Some(DeadReason::DeadNoReferences)
    );
}

//------------------------------------------------------------------------------
// The identity rules (A12, A13)
//------------------------------------------------------------------------------

#[test]
fn the_identity_rule_counts_hold_on_the_fixture() {
    let (main, l) = world();
    let ms: Vec<&Module> = vec![&main, &l];
    let live = live_of(&ms);
    let a = &live.accounting;

    // Every external name of the fixture, and no collision.
    // Nine of the fixture's eleven top-level bindings have external names; the
    // two `$_sys$w` ones do not, which is why they are not in the index.
    assert_eq!(a.external_names_defined, 9);
    assert_eq!(a.external_name_collisions, 0);
    // No global occurrence carries an internal name, and no unique collides.
    assert_eq!(a.global_internal_names, 0);
    assert_eq!(a.global_internal_occurrences, 0);
    assert_eq!(a.unique_collisions, 0);
    assert!(a.check().is_empty(), "{:?}", a.check());
}

#[test]
fn a_global_occurrence_with_an_internal_name_is_counted_not_ignored() {
    // A world whose Main names an *internal* stable string globally. It
    // links to nothing — an internal name is not an identity — and A13
    // counts it rather than letting it pass as an import.
    let main = module(
        "Main",
        vec![(
            binder(&sn("Main", "main"), "main", "main"),
            gvar("$_in$hidden", "hidden"),
        )],
        json!({}),
    );
    let ms: Vec<&Module> = vec![&main];
    let live = live_of(&ms);
    let a = &live.accounting;
    assert_eq!(a.global_internal_names, 1);
    assert_eq!(a.global_internal_occurrences, 1);
    assert!(
        a.check().iter().any(|b| b.contains(A13_GLOBAL_EXTERNAL)),
        "A13 must fail loudly: {:?}",
        a.check()
    );
}
