//! Census behaviour on small hand-built modules.

use h2r_core_ir::{Module, raw};
use serde_json::{Value, json};

use crate::laziness::{Census, Class, Fate, Multiplicity, Sink};

fn demand(strict: bool, once: bool) -> Value {
    json!({"strict": strict, "absent": false, "usedOnce": once, "pretty": if strict {"S"} else {"L"}})
}

fn binder(occ: &str, dmd: Value) -> Value {
    json!({
        "kind": "id", "name": occ, "occ": occ, "unique": occ, "type": "T",
        "arity": 0, "callArity": 0, "exported": false,
        "dmdSig": {"args": [], "diverges": false, "pretty": ""},
        "cprSig": "", "demand": dmd,
        "occInfo": {"kind": "many", "tailCalled": false}, "oneShot": false,
        "details": "", "hasUnfolding": false, "isJoinPoint": false, "isDataCon": false
    })
}

fn lam_binder(occ: &str, one_shot: bool) -> Value {
    let mut b = binder(occ, demand(false, false));
    b["oneShot"] = json!(one_shot);
    b
}

fn var(occ: &str) -> Value {
    json!({"node": "Var", "name": occ, "occ": occ, "unique": occ, "isGlobal": false})
}

fn app(f: Value, a: Value) -> Value {
    json!({"node": "App", "fun": f, "arg": a})
}

fn case2(scrut: Value, a: Value, b: Value) -> Value {
    json!({
        "node": "Case", "scrut": scrut, "binder": binder("wild", demand(false, false)), "type": "R",
        "alts": [
            {"con": {"kind": "DataAlt", "name": "A", "occ": "A", "tag": 1}, "binders": [], "rhs": a},
            {"con": {"kind": "DataAlt", "name": "B", "occ": "B", "tag": 2}, "binders": [], "rhs": b}
        ]
    })
}

/// `let x = f a in <body>` with the given demand on x, wrapped in a
/// top-level binding, plus an id table for the callees.
fn module(x_demand: Value, body: Value, ids: Value) -> Module {
    let m = json!({
        "format": raw::FORMAT, "module": "M", "unit": "main", "ids": ids,
        "binds": [{"rec": false, "pairs": [{
            "binder": binder("top", demand(false, false)),
            "rhs": {"node": "Let", "bind": {"rec": false, "pairs": [{
                "binder": binder("x", x_demand), "rhs": app(var("f"), var("a")),
                "whnf": false, "trivial": false, "cheap": false, "okForSpec": false
            }]}, "body": body},
            "whnf": false, "trivial": false, "cheap": false, "okForSpec": false
        }]}]
    });
    Module::from_raw(serde_json::from_value(m).unwrap()).unwrap()
}

fn callee(strict: bool) -> Value {
    json!({
        "name": "g", "occ": "g", "arity": 1,
        "dmdSig": {"args": [demand(strict, false)], "diverges": false, "pretty": ""},
        "isJoinPoint": false, "dataCon": null
    })
}

fn only(c: &Census) -> &crate::laziness::BindingReport {
    assert_eq!(c.bindings.len(), 1);
    &c.bindings[0]
}

#[test]
fn exclusive_branches_sink() {
    // case p of A -> x; B -> g x     (g strict)
    let m = module(
        demand(false, false),
        case2(var("p"), var("x"), app(var("g"), var("x"))),
        json!({"g": callee(true)}),
    );
    let c = Census::of_modules([&m]);
    let b = only(&c);
    assert_eq!(b.class, Class::LazyOnce);
    assert_eq!(b.multiplicity, Multiplicity::Once);
    assert_eq!(b.syntactic_once, Some(true));
    assert_eq!(b.fate, Fate::SinkEager);
    assert!(matches!(
        b.sink,
        Sink::Branches {
            leaves: 2,
            all_eager: true,
            ..
        }
    ));
}

#[test]
fn shared_on_a_path_needs_memo() {
    // case p of A -> g x; B -> h x x   (two uses in B)
    let m = module(
        demand(false, false),
        case2(
            var("p"),
            app(var("g"), var("x")),
            app(app(var("h"), var("x")), var("x")),
        ),
        json!({"g": callee(true)}),
    );
    let b_ = Census::of_modules([&m]);
    let b = only(&b_);
    assert_eq!(b.class, Class::LazyShared);
    assert_eq!(b.fate, Fate::Memo);
    assert_eq!(b.sink, Sink::Shared);
}

#[test]
fn escaping_use_is_not_syntactically_once() {
    // g x with g lazy in its argument: the thunk is handed over.
    let m = module(
        demand(false, false),
        app(var("g"), var("x")),
        json!({"g": callee(false)}),
    );
    let c = Census::of_modules([&m]);
    let b = only(&c);
    assert_eq!(b.syntactic_once, Some(false));
    assert_eq!(b.fate, Fate::SinkLazyPosition);
    assert!(matches!(b.sink, Sink::Inline { .. }));
}

#[test]
fn strict_single_use_is_a_plain_value() {
    let m = module(
        demand(true, true),
        app(var("g"), var("x")),
        json!({"g": callee(true)}),
    );
    let c = Census::of_modules([&m]);
    let b = only(&c);
    assert_eq!(b.class, Class::StrictValue);
    assert_eq!(b.fate, Fate::NotAThunk);
}

#[test]
fn capture_by_many_entry_lambda_needs_memo() {
    let lam = |one_shot: bool| json!({"node": "Lam", "binder": lam_binder("y", one_shot), "body": app(var("g"), var("x"))});
    let ids = json!({"g": callee(true)});

    let m = module(demand(false, false), lam(false), ids.clone());
    let c = Census::of_modules([&m]);
    assert_eq!(only(&c).fate, Fate::Memo);
    assert!(matches!(only(&c).sink, Sink::UnderLambda { .. }));

    // A one-shot lambda is transparent: the use sinks into it.
    let m = module(demand(false, false), lam(true), ids);
    let c = Census::of_modules([&m]);
    assert_eq!(only(&c).fate, Fate::SinkEager);
}

#[test]
fn ghc_cardinality_overrides_syntax() {
    // Two non-exclusive uses, but GHC says used at most once.
    let m = module(
        demand(false, true),
        app(app(var("h"), var("x")), var("x")),
        json!({}),
    );
    let c = Census::of_modules([&m]);
    let b = only(&c);
    assert_eq!(b.syntactic_once, Some(false));
    assert_eq!(b.multiplicity, Multiplicity::Once);
    assert_eq!(b.class, Class::LazyOnce);
}

#[test]
fn returned_closure_from_known_call_is_producer_known_only() {
    use crate::callee::Resolution;
    // let f = g a in f (h b)   -- f has no signature; its RHS is a call to
    // the known function g. The producer is known; what g returns is not
    // followed, so the target stays unresolved.
    let m = json!({
        "format": raw::FORMAT, "module": "M", "unit": "main",
        "ids": {"g": callee(true), "h": callee(true)},
        "binds": [{"rec": false, "pairs": [{
            "binder": binder("top", demand(false, false)),
            "rhs": {"node": "Let", "bind": {"rec": false, "pairs": [{
                "binder": binder("f", demand(false, false)), "rhs": app(var("g"), var("a")),
                "whnf": false, "trivial": false, "cheap": false, "okForSpec": false
            }]}, "body": app(var("f"), app(var("h"), var("b")))},
            "whnf": false, "trivial": false, "cheap": false, "okForSpec": false
        }]}]
    });
    let m = Module::from_raw(serde_json::from_value(m).unwrap()).unwrap();
    let c = Census::of_modules([&m]);
    let site = c
        .args
        .iter()
        .find(|a| a.callee.occ == "f")
        .expect("argument site headed by f");
    assert_eq!(site.callee.resolution, Resolution::ClosureFromKnownCall);
    assert_eq!(
        site.callee.resolution.tier(),
        crate::callee::Tier::ProducerKnown
    );
}

#[test]
fn local_signature_comes_from_the_binding_site() {
    use crate::callee::Resolution;
    // let k = \y -> ... with a one-argument signature on the *binder*, and
    // no entry in the id table: k (h b) must resolve as an exact local call.
    let mut k = binder("k", demand(false, false));
    k["dmdSig"] = json!({"args": [demand(true, false)], "diverges": false, "pretty": "<S>"});
    let m = json!({
        "format": raw::FORMAT, "module": "M", "unit": "main",
        "ids": {"h": callee(true)},
        "binds": [{"rec": false, "pairs": [{
            "binder": binder("top", demand(false, false)),
            "rhs": {"node": "Let", "bind": {"rec": false, "pairs": [{
                "binder": k,
                "rhs": {"node": "Lam", "binder": lam_binder("y", false), "body": var("y")},
                "whnf": true, "trivial": false, "cheap": true, "okForSpec": false
            }]}, "body": app(var("k"), app(var("h"), var("b")))},
            "whnf": false, "trivial": false, "cheap": false, "okForSpec": false
        }]}]
    });
    let m = Module::from_raw(serde_json::from_value(m).unwrap()).unwrap();
    let c = Census::of_modules([&m]);
    let site = c.args.iter().find(|a| a.callee.occ == "k").unwrap();
    assert_eq!(site.callee.resolution, Resolution::ExactLocal);
}

/// A module with one top-level binding whose RHS is `body`, an id table
/// `ids`, and no local lets: for testing argument sites directly.
fn top_module(body: Value, ids: Value) -> Module {
    let m = json!({
        "format": raw::FORMAT, "module": "M", "unit": "main", "ids": ids,
        "binds": [{"rec": false, "pairs": [{
            "binder": binder("top", demand(false, false)), "rhs": body,
            "whnf": false, "trivial": false, "cheap": false, "okForSpec": false
        }]}]
    });
    Module::from_raw(serde_json::from_value(m).unwrap()).unwrap()
}

#[test]
fn stale_occurrence_metadata_never_wins_over_the_binder() {
    use crate::callee::Resolution;
    use crate::shape::{ArgShape, Position};
    // let k = \y -> y in g (k (h b))
    //
    // The id table (populated from occurrences) claims k has arity 2 and a
    // two-argument strict signature. The binder says arity 1, one lazy
    // argument. Every consumer must read the binder: the callee resolution
    // of `k (h b)`, the position of `h b` inside it, and the shape of
    // `k (h b)` as an argument to g (a computation, not a PAP).
    let mut k = binder("k", demand(false, false));
    k["arity"] = json!(1);
    k["dmdSig"] = json!({"args": [demand(false, false)], "diverges": false, "pretty": "<L>"});
    let stale_k = json!({
        "name": "k", "occ": "k", "arity": 2,
        "dmdSig": {"args": [demand(true, false), demand(true, false)], "diverges": false, "pretty": "<S><S>"},
        "isJoinPoint": false, "dataCon": null
    });
    let m = json!({
        "format": raw::FORMAT, "module": "M", "unit": "main",
        "ids": {"h": callee(true), "g": callee(false), "k": stale_k},
        "binds": [{"rec": false, "pairs": [{
            "binder": binder("top", demand(false, false)),
            "rhs": {"node": "Let", "bind": {"rec": false, "pairs": [{
                "binder": k,
                "rhs": {"node": "Lam", "binder": lam_binder("y", false), "body": var("y")},
                "whnf": true, "trivial": false, "cheap": true, "okForSpec": false
            }]}, "body": app(var("g"), app(var("k"), app(var("h"), var("b"))))},
            "whnf": false, "trivial": false, "cheap": false, "okForSpec": false
        }]}]
    });
    let m = Module::from_raw(serde_json::from_value(m).unwrap()).unwrap();
    let c = Census::of_modules([&m]);

    let inner = c.args.iter().find(|a| a.callee.occ == "k").unwrap();
    assert_eq!(inner.callee.resolution, Resolution::ExactLocal);
    assert_eq!(
        inner.position,
        Position::LazyParam,
        "binder says lazy; occurrence said strict"
    );

    let outer = c.args.iter().find(|a| a.callee.occ == "g").unwrap();
    assert_eq!(
        outer.shape,
        ArgShape::Computation,
        "binder arity 1: k (h b) is saturated"
    );
}

#[test]
fn undersaturated_call_does_not_unleash_the_signature() {
    use crate::callee::Resolution;
    use crate::shape::{ArgShape, Position};
    // g2 :: strict in both arguments, signature arity 2.
    let g2 = json!({
        "name": "g2", "occ": "g2", "arity": 2,
        "dmdSig": {"args": [demand(true, false), demand(true, false)], "diverges": false, "pretty": "<S><S>"},
        "isJoinPoint": false, "dataCon": null
    });
    let ids = json!({"g2": g2, "h": callee(true), "k": callee(false)});

    // k (g2 (h b)): g2 gets one of two arguments. The PAP holds `h b`
    // unevaluated; g2's strictness in it is not unleashed.
    let m = top_module(
        app(var("k"), app(var("g2"), app(var("h"), var("b")))),
        ids.clone(),
    );
    let c = Census::of_modules([&m]);
    let inner = c.args.iter().find(|a| a.callee.occ == "g2").unwrap();
    assert_eq!(inner.position, Position::UnsaturatedArg);
    assert!(inner.position.escapes());
    assert_eq!(
        inner.callee.resolution,
        Resolution::ExactGlobal,
        "the target is still exact"
    );
    let outer = c.args.iter().find(|a| a.callee.occ == "k").unwrap();
    assert_eq!(outer.shape, ArgShape::PartialApp);

    // The consequence for the let census: `let x = f a in k (g2 x)` must not
    // be a sink-eager site just because g2 is strict.
    let m = module(
        demand(false, false),
        app(var("k"), app(var("g2"), var("x"))),
        ids.clone(),
    );
    let c = Census::of_modules([&m]);
    assert_eq!(only(&c).fate, Fate::SinkLazyPosition);

    // Saturated, the same signature does apply.
    let m = module(
        demand(false, false),
        app(app(var("g2"), var("x")), var("b")),
        ids,
    );
    let c = Census::of_modules([&m]);
    assert_eq!(only(&c).fate, Fate::SinkEager);
}

#[test]
fn past_signature_argument_is_producer_known_not_exact() {
    use crate::callee::{Resolution, Tier};
    use crate::shape::Position;
    // g (h b) (h c) with g's signature covering one argument: the second
    // goes to whatever `g (h b)` returns.
    let m = top_module(
        app(
            app(var("g"), app(var("h"), var("b"))),
            app(var("h"), var("c")),
        ),
        json!({"g": callee(true), "h": callee(true)}),
    );
    let c = Census::of_modules([&m]);
    let sites: Vec<_> = c.args.iter().filter(|a| a.callee.occ == "g").collect();
    assert_eq!(sites.len(), 2);
    assert_eq!(sites[0].position, Position::StrictArg);
    assert_eq!(sites[0].callee.resolution.tier(), Tier::Exact);
    assert_eq!(sites[1].position, Position::PastSigArg);
    assert_eq!(sites[1].callee.resolution, Resolution::PastArity);
    assert_eq!(sites[1].callee.resolution.tier(), Tier::ProducerKnown);
}
