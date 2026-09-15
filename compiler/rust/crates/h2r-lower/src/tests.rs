//! M3a on small hand-built worlds.
//!
//! The fixtures mirror `h2r-analysis`'s `class_module` builder rather than
//! reusing it: that builder is `#[cfg(test)]` inside its own crate, and
//! making it public would widen h2r-analysis for a convenience. What the
//! two share is the *shape* of a format-5 module, which is the dump's, not
//! either crate's.

use h2r_core_ir::{Module, raw};
use serde_json::{Value, json};

use crate::reachability::{A2_EDGE_LOCAL, A3_EDGE_GLOBAL, DeadReason, LiveSet, NodeId, RootError};
use crate::verify::{
    V2_POPULATION, V3_LIVE_CLOSED, V4_DEAD_UNREFERENCED, V5_WITNESS, V6_EDGES, verify,
};

//------------------------------------------------------------------------------
// Fixtures
//------------------------------------------------------------------------------

const UNIT: &str = "u";

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
