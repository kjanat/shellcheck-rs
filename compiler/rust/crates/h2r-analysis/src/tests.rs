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

//------------------------------------------------------------------------------
// Scoping: uniques are not unique in optimised Core
//------------------------------------------------------------------------------

/// Two sibling `let`s that share a unique (GHC's simplifier renames a binder
/// only when it would clash with the *in-scope* set, so inlined copies of a
/// term keep their original uniques). Each is used exactly once; keying the
/// occurrence census by unique merges them into one two-use binding and
/// reports sharing that is not there.
#[test]
fn sibling_lets_sharing_a_unique_are_not_merged() {
    // case p of
    //   A -> let x = f a in g x
    //   B -> let x = f a in g x        -- a *different* x, same unique
    let one_let = |body: Value| {
        json!({"node": "Let", "bind": {"rec": false, "pairs": [{
            "binder": binder("x", demand(false, false)), "rhs": app(var("f"), var("a")),
            "whnf": false, "trivial": false, "cheap": false, "okForSpec": false
        }]}, "body": body})
    };
    let m = top_module(
        case2(
            var("p"),
            one_let(app(var("g"), var("x"))),
            one_let(app(var("g"), var("x"))),
        ),
        json!({"g": callee(true)}),
    );
    let c = Census::of_modules([&m]);
    assert_eq!(c.bindings.len(), 2);
    for b in &c.bindings {
        assert_eq!(b.occurrences, 1, "each x has exactly one use of its own");
        assert_eq!(b.class, Class::LazyOnce);
        assert_eq!(b.multiplicity, Multiplicity::Once);
        assert_eq!(b.syntactic_once, Some(true));
        assert_eq!(b.fate, Fate::SinkEager);
        assert!(matches!(b.sink, Sink::Inline { .. }));
    }
    // The two bindings really do share a unique, and are different binders.
    assert_eq!(c.bindings[0].unique, c.bindings[1].unique);
    assert_ne!(c.bindings[0].let_node, c.bindings[1].let_node);
}

/// A local binder shadowed by an inner one of the same unique: uses inside
/// the shadow belong to the inner binder only.
#[test]
fn an_inner_binder_shadows_an_outer_one_with_the_same_unique() {
    // let x = f a in (let x = f a in g x)
    let inner = json!({"node": "Let", "bind": {"rec": false, "pairs": [{
        "binder": binder("x", demand(false, false)), "rhs": app(var("f"), var("a")),
        "whnf": false, "trivial": false, "cheap": false, "okForSpec": false
    }]}, "body": app(var("g"), var("x"))});
    let m = module(demand(false, false), inner, json!({"g": callee(true)}));
    let c = Census::of_modules([&m]);
    assert_eq!(c.bindings.len(), 2);
    let outer = c.bindings.iter().find(|b| b.occurrences == 0).unwrap();
    assert_eq!(
        outer.class,
        Class::Dead,
        "the outer x is shadowed, not used"
    );
    let inner = c.bindings.iter().find(|b| b.occurrences == 1).unwrap();
    assert_eq!(inner.class, Class::LazyOnce);
}

/// `Module::spine` looks through the casts the simplifier leaves inside an
/// application spine, so the spine-root test has to as well: otherwise the
/// inner `App` is walked as a spine of its own and its arguments are counted
/// twice.
#[test]
fn a_cast_inside_a_spine_does_not_split_it() {
    use crate::shape::Position;
    // g2 (h b) `cast` (h c) -- one spine, two arguments.
    let cast = |e: Value| json!({"node": "Cast", "expr": e});
    let g2 = json!({
        "name": "g2", "occ": "g2", "arity": 2,
        "dmdSig": {"args": [demand(true, false), demand(false, false)], "diverges": false, "pretty": "<S><L>"},
        "isJoinPoint": false, "dataCon": null
    });
    let m = top_module(
        app(
            cast(app(var("g2"), app(var("h"), var("b")))),
            app(var("h"), var("c")),
        ),
        json!({"g2": g2, "h": callee(true)}),
    );
    let c = Census::of_modules([&m]);
    let mut args: Vec<u32> = c.args.iter().map(|a| a.arg).collect();
    let n = args.len();
    args.sort_unstable();
    args.dedup();
    assert_eq!(args.len(), n, "no argument node may be counted twice");
    assert_eq!(n, 2);
    // Both arguments belong to g2's spine, so the signature is unleashed and
    // each gets the demand of its own slot.
    assert!(c.args.iter().all(|a| a.callee.occ == "g2"));
    let mut pos: Vec<Position> = c.args.iter().map(|a| a.position).collect();
    pos.sort();
    assert_eq!(pos, vec![Position::StrictArg, Position::LazyParam]);
}

//------------------------------------------------------------------------------
// Tuple flows: which allocations are plumbing (tuples.rs)
//------------------------------------------------------------------------------

use crate::tuples::{TupleCensus, TupleFate, TupleUse, Tuples};

/// An imported data constructor, for the id table.
fn data_con(occ: &str, name: &str, arity: u32) -> Value {
    let args: Vec<Value> = (0..arity).map(|_| demand(false, false)).collect();
    json!({
        "name": name, "occ": occ, "arity": arity,
        "dmdSig": {"args": args, "diverges": false, "pretty": ""},
        "isJoinPoint": false,
        "dataCon": {
            "name": name, "repArity": arity, "tag": 1,
            "strictFields": vec![false; arity as usize]
        }
    })
}

fn boxed_tuple_id(arity: u32) -> (String, Value) {
    let occ = format!("({})", ",".repeat(arity as usize - 1));
    let name = format!("$ghc-prim$GHC.Tuple.Prim${occ}");
    (occ.clone(), data_con(&occ, &name, arity))
}

fn unboxed_tuple_id(arity: u32) -> (String, Value) {
    let occ = format!("(#{}#)", ",".repeat(arity as usize - 1));
    let name = format!("$ghc-prim$GHC.Prim${occ}");
    (occ.clone(), data_con(&occ, &name, arity))
}

/// A global `Var` (an import): nothing in the module binds it.
fn gvar(occ: &str) -> Value {
    json!({"node": "Var", "name": occ, "occ": occ, "unique": occ, "isGlobal": true})
}

/// A saturated constructor application.
fn con_app(occ: &str, args: &[Value]) -> Value {
    let mut e = gvar(occ);
    for a in args {
        e = app(e, a.clone());
    }
    e
}

/// `case <scrut> of wild { <con> b0 b1 … -> <rhs> }`, with a distinct
/// unique per binder so that occurrences resolve to the right one.
fn case_con(scrut: Value, con: &str, binders: &[&str], rhs: Value) -> Value {
    json!({
        "node": "Case", "scrut": scrut,
        "binder": binder("wild", demand(false, false)), "type": "R",
        "alts": [{
            "con": {"kind": "DataAlt", "name": con, "occ": con, "tag": 1},
            "binders": binders.iter().map(|b| binder(b, demand(false, false))).collect::<Vec<_>>(),
            "rhs": rhs
        }]
    })
}

fn let1(occ: &str, rhs: Value, body: Value) -> Value {
    json!({"node": "Let", "bind": {"rec": false, "pairs": [{
        "binder": binder(occ, demand(false, false)), "rhs": rhs,
        "whnf": false, "trivial": false, "cheap": false, "okForSpec": false
    }]}, "body": body})
}

/// A module whose top-level binds are the given (binder, rhs) pairs.
fn tops(pairs: Vec<(Value, Value)>, ids: Value) -> Module {
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
        "format": raw::FORMAT, "module": "M", "unit": "main", "ids": ids, "binds": binds
    });
    Module::from_raw(serde_json::from_value(m).unwrap()).unwrap()
}

fn lam(params: &[&str], body: Value) -> Value {
    let mut e = body;
    for p in params.iter().rev() {
        e = json!({"node": "Lam", "binder": lam_binder(p, false), "body": e});
    }
    e
}

fn one_flow<'a>(t: &'a Tuples<'a>) -> &'a crate::tuples::TupleFlow {
    assert_eq!(t.flows.len(), 1, "expected exactly one construction");
    &t.flows[0]
}

/// `let r = (a, b) in case r of (x, y) -> g x`: the box never outlives the
/// match, so it can be replaced by its fields.
#[test]
fn a_let_bound_tuple_that_is_only_scrutinised_vanishes() {
    let (tup, id) = boxed_tuple_id(2);
    let m = top_module(
        let1(
            "r",
            con_app(&tup, &[var("a"), var("b")]),
            case_con(var("r"), &tup, &["x", "y"], app(var("g"), var("x"))),
        ),
        json!({&tup: id, "g": callee(true)}),
    );
    let t = Tuples::of_module(&m);
    let f = one_flow(&t);
    assert!(f.boxed);
    assert_eq!(f.arity, 2);
    assert!(f.bound.is_some(), "the construction is let-bound");
    assert_eq!(f.fate, TupleFate::ScalarReplace);
    assert!(matches!(
        f.consumers.as_slice(),
        [TupleUse::Scrutinised {
            all_fields_bound: true,
            ..
        }]
    ));
}

/// `case (# a, b #) of (# x, y #) -> g x`: no tuple survives at all.
#[test]
fn an_unboxed_construct_then_case_is_trivial() {
    let (tup, id) = unboxed_tuple_id(2);
    let m = top_module(
        case_con(
            con_app(&tup, &[var("a"), var("b")]),
            &tup,
            &["x", "y"],
            app(var("g"), var("x")),
        ),
        json!({&tup: id, "g": callee(true)}),
    );
    let t = Tuples::of_module(&m);
    let f = one_flow(&t);
    assert!(!f.boxed);
    assert_eq!(f.bound, None);
    assert_eq!(f.fate, TupleFate::ScalarReplace);
}

/// A tuple returned from a local function that two call sites both
/// scrutinise immediately: a worker return, which becomes a multi-value
/// return rather than an allocation.
#[test]
fn a_returned_tuple_scrutinised_at_every_call_site_is_a_worker_return() {
    let (tup, id) = unboxed_tuple_id(2);
    let m = tops(
        vec![
            (
                binder("f", demand(false, false)),
                lam(&["p"], con_app(&tup, &[var("p"), var("p")])),
            ),
            (
                binder("user", demand(false, false)),
                app(
                    app(
                        var("h"),
                        case_con(
                            app(var("f"), var("a")),
                            &tup,
                            &["x", "y"],
                            app(var("g"), var("x")),
                        ),
                    ),
                    case_con(
                        app(var("f"), var("b")),
                        &tup,
                        &["x1", "y1"],
                        app(var("g"), var("y1")),
                    ),
                ),
            ),
        ],
        json!({&tup: id, "g": callee(true), "h": callee(true)}),
    );
    let t = Tuples::of_module(&m);
    let f = one_flow(&t);
    assert_eq!(f.fate, TupleFate::WorkerReturn);
    assert_eq!(
        f.consumers
            .iter()
            .filter(|u| matches!(u, TupleUse::Scrutinised { .. }))
            .count(),
        2,
        "one scrutiny per call site"
    );
    assert!(
        f.consumers
            .iter()
            .any(|u| matches!(u, TupleUse::Returned { .. }))
    );
}

/// …and if one call site stores the result instead, the tuple is a real
/// value and has to stay.
#[test]
fn a_call_site_that_stores_the_result_preserves_it() {
    let (tup, id) = unboxed_tuple_id(2);
    let m = tops(
        vec![
            (
                binder("f", demand(false, false)),
                lam(&["p"], con_app(&tup, &[var("p"), var("p")])),
            ),
            (
                binder("user", demand(false, false)),
                app(
                    app(
                        var("h"),
                        case_con(
                            app(var("f"), var("a")),
                            &tup,
                            &["x", "y"],
                            app(var("g"), var("x")),
                        ),
                    ),
                    con_app("Just", &[app(var("f"), var("b"))]),
                ),
            ),
        ],
        json!({
            &tup: id, "g": callee(true), "h": callee(true),
            "Just": data_con("Just", "$base$GHC.Maybe$Just", 1)
        }),
    );
    let t = Tuples::of_module(&m);
    let f = one_flow(&t);
    assert_eq!(f.fate, TupleFate::Preserve);
    assert_eq!(f.reason, Some(crate::tuples::R_STORED_CON));
    assert!(
        f.consumers
            .iter()
            .any(|u| matches!(u, TupleUse::StoredIn { .. }))
    );
}

/// The desugaring of a lazy pattern `~(a, b)` followed by re-tupling:
/// every field of the new tuple is the matching projection of one and the
/// same binder, so the construction is a field-wise copy of it.
#[test]
fn re_tupling_lazy_selectors_over_one_tuple_is_a_copy() {
    let (tup, id) = boxed_tuple_id(2);
    let m = top_module(
        let1(
            "ds",
            app(var("f"), var("a")),
            con_app(
                &tup,
                &[
                    case_con(var("ds"), &tup, &["p", "q"], var("p")),
                    case_con(var("ds"), &tup, &["p1", "q1"], var("q1")),
                ],
            ),
        ),
        json!({&tup: id}),
    );
    let t = Tuples::of_module(&m);
    let f = one_flow(&t);
    let ds = f.copy_of.expect("a field-wise copy of one binder");
    assert_eq!(t.binder(ds).occ, "ds");
    assert!(
        f.evidence
            .iter()
            .any(|e| e.rule == crate::tuples::T4_RETUPLE)
    );

    // Two projections of *different* binders are not a copy: only lexical
    // identity proves the fields come from one tuple.
    let m = top_module(
        let1(
            "ds",
            app(var("f"), var("a")),
            let1(
                "ds2",
                app(var("f"), var("b")),
                con_app(
                    &tup,
                    &[
                        case_con(var("ds"), &tup, &["p", "q"], var("p")),
                        case_con(var("ds2"), &tup, &["p1", "q1"], var("q1")),
                    ],
                ),
            ),
        ),
        json!({&tup: id}),
    );
    let t = Tuples::of_module(&m);
    assert_eq!(one_flow(&t).copy_of, None);
}

/// A tuple handed to a local function whose parameter is only scrutinised:
/// the parameter becomes the fields, so the box is still unnecessary.
#[test]
fn a_tuple_passed_to_a_known_local_that_scrutinises_it_is_scalar_replaced() {
    let (tup, id) = boxed_tuple_id(2);
    let m = top_module(
        let1(
            "k",
            lam(
                &["t"],
                case_con(var("t"), &tup, &["x", "y"], app(var("g"), var("x"))),
            ),
            app(var("k"), con_app(&tup, &[var("a"), var("b")])),
        ),
        json!({&tup: id, "g": callee(true)}),
    );
    let t = Tuples::of_module(&m);
    let f = one_flow(&t);
    assert_eq!(f.fate, TupleFate::ScalarReplace);
    assert!(
        f.consumers
            .iter()
            .any(|u| matches!(u, TupleUse::PassedTo { param: 0, .. }))
    );
    assert!(
        f.consumers
            .iter()
            .any(|u| matches!(u, TupleUse::Scrutinised { .. }))
    );
}

/// A tuple stored in a constructor field is a real value.
#[test]
fn a_tuple_in_a_constructor_field_is_preserved() {
    let (tup, id) = boxed_tuple_id(2);
    let m = top_module(
        con_app("Just", &[con_app(&tup, &[var("a"), var("b")])]),
        json!({&tup: id, "Just": data_con("Just", "$base$GHC.Maybe$Just", 1)}),
    );
    let t = Tuples::of_module(&m);
    let f = one_flow(&t);
    assert_eq!(f.fate, TupleFate::Preserve);
    assert_eq!(f.reason, Some(crate::tuples::R_STORED_CON));
}

/// A tuple returned from an *exported* function: the callers this module
/// can see all scrutinise it, but there are others it cannot see. Recorded
/// as unresolved with the reason, never guessed either way.
#[test]
fn a_tuple_returned_from_an_exported_function_is_unresolved() {
    let (tup, id) = boxed_tuple_id(2);
    let mut f_binder = binder("f", demand(false, false));
    f_binder["exported"] = json!(true);
    let m = tops(
        vec![
            (f_binder, lam(&["p"], con_app(&tup, &[var("p"), var("p")]))),
            (
                binder("user", demand(false, false)),
                case_con(
                    app(var("f"), var("a")),
                    &tup,
                    &["x", "y"],
                    app(var("g"), var("x")),
                ),
            ),
        ],
        json!({&tup: id, "g": callee(true)}),
    );
    let t = Tuples::of_module(&m);
    let f = one_flow(&t);
    assert_eq!(f.fate, TupleFate::Unresolved);
    assert_eq!(f.reason, Some(crate::tuples::R_EXPORTED_RETURN));
}

/// `let r = (a, b) in h (case r of (x, y) -> x) (imported r)`: the tuple is
/// scrutinised *and* aliased into a callee outside the module, so the box
/// outlives the match.
#[test]
fn a_second_use_after_the_scrutiny_is_not_scalar_replaceable() {
    let (tup, id) = boxed_tuple_id(2);
    let m = top_module(
        let1(
            "r",
            con_app(&tup, &[var("a"), var("b")]),
            app(
                app(var("h"), case_con(var("r"), &tup, &["x", "y"], var("x"))),
                app(var("imported"), var("r")),
            ),
        ),
        json!({&tup: id, "h": callee(true), "imported": callee(false)}),
    );
    let t = Tuples::of_module(&m);
    let f = one_flow(&t);
    assert_ne!(f.fate, TupleFate::ScalarReplace);
    assert_eq!(f.fate, TupleFate::Preserve);
    assert_eq!(f.reason, Some(crate::tuples::R_IMPORTED_LAZY));
    assert!(
        f.consumers.iter().any(|u| u.reads_fields()),
        "the field read is still recorded"
    );
}

/// The census' tuple-attributed argument sites map onto the construction
/// they are a field of, one to one; the accounting asserts it.
#[test]
fn census_tuple_argument_sites_map_onto_constructions() {
    let (tup, id) = boxed_tuple_id(2);
    let m = top_module(
        con_app(&tup, &[app(var("f"), var("a")), var("b")]),
        json!({&tup: id, "f": callee(true)}),
    );
    let mods = vec![&m];
    let census = Census::raw(mods.iter().copied());
    let tc = TupleCensus::of_modules(&mods, &census);
    assert_eq!(tc.accounting.constructions_boxed, 1);
    assert_eq!(tc.accounting.sites.len(), 1, "one lazy field computation");
    assert_eq!(tc.accounting.sites_mapped, 1);
    assert_eq!(tc.accounting.sites_unmapped, 0);
    assert_eq!(tc.accounting.sites[0].flow, Some(0));
}

//------------------------------------------------------------------------------
// Adversarial cases: the shapes a removable verdict could be wrong on
//------------------------------------------------------------------------------
//
// One test per case the stage-2 audit went looking for, each built to make
// the wrong answer the tempting one. Every case was also searched for in
// the `-O1` dump; the counts are in the README.

/// An exported top-level binder.
fn exported(occ: &str) -> Value {
    let mut b = binder(occ, demand(false, false));
    b["exported"] = json!(true);
    b
}

/// `case <scrut> of <cb> { <con> b0 … -> <rhs> }` with a named case binder,
/// so the alias the match keeps can be referred to.
fn case_named(scrut: Value, cb: &str, con: &str, binders: &[&str], rhs: Value) -> Value {
    json!({
        "node": "Case", "scrut": scrut,
        "binder": binder(cb, demand(false, false)), "type": "R",
        "alts": [{
            "con": {"kind": "DataAlt", "name": con, "occ": con, "tag": 1},
            "binders": binders.iter().map(|b| binder(b, demand(false, false))).collect::<Vec<_>>(),
            "rhs": rhs
        }]
    })
}

/// `case <scrut> of _ { DEFAULT -> <rhs> }`: forcing, no field read.
fn case_force(scrut: Value, cb: &str, rhs: Value) -> Value {
    json!({
        "node": "Case", "scrut": scrut,
        "binder": binder(cb, demand(false, false)), "type": "R",
        "alts": [{"con": {"kind": "DEFAULT"}, "binders": [], "rhs": rhs}]
    })
}

/// An imported data constructor with strict fields.
fn strict_data_con(occ: &str, name: &str, arity: u32) -> Value {
    let mut d = data_con(occ, name, arity);
    d["dataCon"]["strictFields"] = json!(vec![true; arity as usize]);
    d
}

// --- 1. aliasing ------------------------------------------------------------

/// The case binder is the same tuple under a second name. Reading a field
/// through one alias and handing the other to an import means the box
/// outlives the match, and the analysis must see both.
#[test]
fn an_escaping_case_binder_alias_defeats_the_scrutiny() {
    let (tup, id) = boxed_tuple_id(2);
    let m = top_module(
        let1(
            "r",
            con_app(&tup, &[var("a"), var("b")]),
            case_named(
                var("r"),
                "w",
                &tup,
                &["x", "y"],
                app(app(var("h"), var("x")), app(var("imported"), var("w"))),
            ),
        ),
        json!({&tup: id, "h": callee(true), "imported": callee(false)}),
    );
    let t = Tuples::of_module(&m);
    let f = one_flow(&t);
    assert_eq!(f.fate, TupleFate::Preserve);
    assert_eq!(f.reason, Some(crate::tuples::R_IMPORTED_LAZY));
    assert!(
        f.evidence
            .iter()
            .any(|e| e.rule == crate::tuples::T8_CASE_BINDER_ALIAS)
    );
}

/// `let a = (p, q); let b = a`: a re-binding is another name for the same
/// value, and every occurrence of either has to be classified.
#[test]
fn a_re_bound_alias_is_followed_through() {
    let (tup, id) = boxed_tuple_id(2);
    let body = |second: Value| {
        let1(
            "a",
            con_app(&tup, &[var("p"), var("q")]),
            let1("b", var("a"), second),
        )
    };
    // Both aliases only read fields.
    let m = top_module(
        body(case_con(
            var("b"),
            &tup,
            &["x", "y"],
            app(var("g"), var("x")),
        )),
        json!({&tup: id, "g": callee(true)}),
    );
    let t = Tuples::of_module(&m);
    let f = one_flow(&t);
    assert_eq!(f.fate, TupleFate::ScalarReplace);

    // …and if the second name escapes, the first one's scrutiny does not
    // make the box go away.
    let m = top_module(
        body(app(
            app(var("h"), case_con(var("a"), &tup, &["x", "y"], var("x"))),
            app(var("imported"), var("b")),
        )),
        json!({&tup: id, "h": callee(true), "imported": callee(false)}),
    );
    let t = Tuples::of_module(&m);
    let f = one_flow(&t);
    assert_eq!(f.fate, TupleFate::Preserve);
    assert_eq!(f.reason, Some(crate::tuples::R_IMPORTED_LAZY));
}

// --- 2. several consumers on one path ---------------------------------------

/// Two scrutinies of the same binder are two consumers, and both are
/// recorded; the tuple is still only read.
#[test]
fn two_scrutinies_are_both_seen() {
    let (tup, id) = boxed_tuple_id(2);
    let m = top_module(
        let1(
            "r",
            con_app(&tup, &[var("a"), var("b")]),
            app(
                app(var("h"), case_con(var("r"), &tup, &["x", "y"], var("x"))),
                case_con(var("r"), &tup, &["x1", "y1"], var("y1")),
            ),
        ),
        json!({&tup: id, "h": callee(true)}),
    );
    let t = Tuples::of_module(&m);
    let f = one_flow(&t);
    assert_eq!(f.fate, TupleFate::ScalarReplace);
    assert_eq!(
        f.consumers
            .iter()
            .filter(|u| matches!(u, TupleUse::Selected { .. }))
            .count(),
        2
    );
}

/// Scrutinised *and then* stored: the store wins, because the allocation
/// exists however many fields were read first.
#[test]
fn scrutinised_then_stored_is_preserved() {
    let (tup, id) = boxed_tuple_id(2);
    let m = top_module(
        let1(
            "r",
            con_app(&tup, &[var("a"), var("b")]),
            app(
                app(var("h"), case_con(var("r"), &tup, &["x", "y"], var("x"))),
                con_app("Just", &[var("r")]),
            ),
        ),
        json!({
            &tup: id, "h": callee(true),
            "Just": data_con("Just", "$base$GHC.Maybe$Just", 1)
        }),
    );
    let t = Tuples::of_module(&m);
    let f = one_flow(&t);
    assert_eq!(f.fate, TupleFate::Preserve);
    assert_eq!(f.reason, Some(crate::tuples::R_STORED_CON));
    assert!(f.consumers.iter().any(|u| u.reads_fields()));
}

// --- 3. recursive flows ------------------------------------------------------

/// A tuple returned from a recursive function, scrutinised both by the
/// function's own recursive call site and by an outside caller. The
/// worklist has to terminate and both consumers have to be seen.
#[test]
fn a_tuple_returned_from_a_recursive_function_sees_every_call_site() {
    let (tup, id) = unboxed_tuple_id(2);
    let m = tops(
        vec![
            (
                binder("go", demand(false, false)),
                lam(
                    &["n"],
                    case2(
                        var("p"),
                        con_app(&tup, &[var("a"), var("b")]),
                        case_con(
                            app(var("go"), var("n")),
                            &tup,
                            &["x", "y"],
                            app(var("g"), var("x")),
                        ),
                    ),
                ),
            ),
            (
                binder("user", demand(false, false)),
                case_con(
                    app(var("go"), var("m")),
                    &tup,
                    &["x1", "y1"],
                    app(var("g"), var("y1")),
                ),
            ),
        ],
        json!({&tup: id, "g": callee(true)}),
    );
    let t = Tuples::of_module(&m);
    let f = one_flow(&t);
    assert_eq!(f.fate, TupleFate::WorkerReturn);
    assert_eq!(
        f.consumers
            .iter()
            .filter(|u| matches!(u, TupleUse::Scrutinised { .. }))
            .count(),
        2,
        "the recursive call site and the outside one"
    );
}

/// …and a self-loop is not a consumer: if the only *other* call site hands
/// the result to an import, the tuple is a real value however many times
/// the recursion went round.
#[test]
fn a_self_loop_does_not_make_a_tuple_removable() {
    let (tup, id) = boxed_tuple_id(2);
    let m = tops(
        vec![
            (
                binder("f", demand(false, false)),
                lam(
                    &["n"],
                    case2(
                        var("p"),
                        con_app(&tup, &[var("a"), var("b")]),
                        app(var("f"), var("n")),
                    ),
                ),
            ),
            (
                binder("user", demand(false, false)),
                app(var("imported"), app(var("f"), var("m"))),
            ),
        ],
        json!({&tup: id, "imported": callee(false)}),
    );
    let t = Tuples::of_module(&m);
    let f = one_flow(&t);
    assert_eq!(f.fate, TupleFate::Preserve);
    assert_eq!(f.reason, Some(crate::tuples::R_IMPORTED_LAZY));
}

/// A tuple threaded through a loop as an accumulator parameter and
/// returned: the parameter is another alias, the return is followed to the
/// loop's own call site, and the walk terminates.
#[test]
fn an_accumulator_threaded_through_a_loop_is_a_multi_value_return() {
    let (tup, id) = boxed_tuple_id(2);
    let m = tops(
        vec![
            (
                binder("go", demand(false, false)),
                lam(
                    &["acc"],
                    case2(var("p"), var("acc"), app(var("go"), var("acc"))),
                ),
            ),
            (
                binder("user", demand(false, false)),
                case_con(
                    app(var("go"), con_app(&tup, &[var("a"), var("b")])),
                    &tup,
                    &["x", "y"],
                    app(var("g"), var("x")),
                ),
            ),
        ],
        json!({&tup: id, "g": callee(true)}),
    );
    let t = Tuples::of_module(&m);
    let f = one_flow(&t);
    assert_eq!(f.fate, TupleFate::WorkerReturn);
    assert!(
        f.consumers
            .iter()
            .any(|u| matches!(u, TupleUse::PassedTo { .. }))
    );
}

// --- 4. a tuple in a tuple ---------------------------------------------------

/// An inner tuple in a field of an outer tuple that is itself removable:
/// the box holding it will not exist, so the inner one's consumers are the
/// uses of the outer's field binder, and both go away.
#[test]
fn a_tuple_in_a_removable_tuple_is_removable_too() {
    let (tup, id) = boxed_tuple_id(2);
    let m = top_module(
        let1(
            "o",
            con_app(&tup, &[con_app(&tup, &[var("a"), var("b")]), var("c")]),
            case_con(
                var("o"),
                &tup,
                &["p", "q"],
                case_con(var("p"), &tup, &["x", "y"], app(var("g"), var("x"))),
            ),
        ),
        json!({&tup: id, "g": callee(true)}),
    );
    let t = Tuples::of_module(&m);
    assert_eq!(t.flows.len(), 2);
    let outer = t.flows.iter().find(|f| f.bound.is_some()).unwrap();
    let inner = t.flows.iter().find(|f| f.bound.is_none()).unwrap();
    assert_eq!(outer.fate, TupleFate::ScalarReplace);
    assert_eq!(inner.fate, TupleFate::ScalarReplace);
    assert_eq!(inner.nested_in.len(), 1);
    assert!(
        inner
            .evidence
            .iter()
            .any(|e| e.rule == crate::tuples::T12_NESTED)
    );
    assert!(
        inner
            .consumers
            .iter()
            .any(|u| matches!(u, TupleUse::Scrutinised { .. })),
        "the inner tuple's consumer is the outer's field binder's use"
    );
}

/// …and when the outer tuple is a real value, the inner one is too.
#[test]
fn a_tuple_in_a_preserved_tuple_stays_preserved() {
    let (tup, id) = boxed_tuple_id(2);
    let m = top_module(
        con_app(
            "Just",
            &[con_app(
                &tup,
                &[con_app(&tup, &[var("a"), var("b")]), var("c")],
            )],
        ),
        json!({
            &tup: id,
            "Just": data_con("Just", "$base$GHC.Maybe$Just", 1)
        }),
    );
    let t = Tuples::of_module(&m);
    assert_eq!(t.flows.len(), 2);
    for f in &t.flows {
        assert_eq!(f.fate, TupleFate::Preserve);
    }
    let inner = t
        .flows
        .iter()
        .find(|f| f.reason == Some(crate::tuples::R_STORED_TUPLE))
        .expect("the inner tuple is stored in a tuple field");
    assert_eq!(inner.nested_in.len(), 1);
}

// --- 5. worker/wrapper boundaries -------------------------------------------

/// A worker returning an unboxed tuple whose only caller is the wrapper,
/// which takes it apart and re-boxes the fields into a boxed tuple it
/// returns from an exported function. The unboxed one is a multi-value
/// return; the boxed one has callers this module cannot see.
#[test]
fn a_worker_return_re_boxed_by_an_exported_wrapper() {
    let (ub, ubid) = unboxed_tuple_id(2);
    let (bx, bxid) = boxed_tuple_id(2);
    let m = tops(
        vec![
            (
                binder("w", demand(false, false)),
                lam(&["n"], con_app(&ub, &[var("a"), var("b")])),
            ),
            (
                exported("wrap"),
                lam(
                    &["n1"],
                    case_con(
                        app(var("w"), var("n1")),
                        &ub,
                        &["x", "y"],
                        con_app(&bx, &[var("x"), var("y")]),
                    ),
                ),
            ),
        ],
        json!({&ub: ubid, &bx: bxid}),
    );
    let t = Tuples::of_module(&m);
    assert_eq!(t.flows.len(), 2);
    let unboxed = t.flows.iter().find(|f| !f.boxed).unwrap();
    let boxed = t.flows.iter().find(|f| f.boxed).unwrap();
    assert_eq!(unboxed.fate, TupleFate::WorkerReturn);
    assert_eq!(boxed.fate, TupleFate::Unresolved);
    assert_eq!(boxed.reason, Some(crate::tuples::R_EXPORTED_RETURN));
    // The chain is in the evidence: returned from w, its call site pays
    // the debt, and that call is scrutinised.
    let rules: Vec<&str> = unboxed.evidence.iter().map(|e| e.rule).collect();
    assert!(rules.contains(&crate::tuples::T6_RETURNED));
    assert!(rules.contains(&crate::tuples::T7_CALL_RESULT));
    assert!(rules.contains(&crate::tuples::T2_SCRUTINISED));
}

/// A boxed tuple that crosses a local worker's return first and an
/// exported wrapper's second: the residual says which, so the next pass
/// knows to look for the worker's callers and not the wrapper's.
#[test]
fn an_exported_wrapper_of_a_worker_says_so() {
    let (tup, id) = boxed_tuple_id(2);
    let m = tops(
        vec![
            (
                binder("w", demand(false, false)),
                lam(&["n"], con_app(&tup, &[var("a"), var("b")])),
            ),
            (exported("wrap"), lam(&["n1"], app(var("w"), var("n1")))),
        ],
        json!({&tup: id}),
    );
    let t = Tuples::of_module(&m);
    let f = one_flow(&t);
    assert_eq!(f.fate, TupleFate::Unresolved);
    assert_eq!(f.reason, Some(crate::tuples::R_EXPORTED_WRAPPER_RETURN));
    assert_eq!(f.detail, "wrap of w");
}

/// The other direction: the wrapper takes a boxed tuple apart and hands
/// the fields to the worker. The box never outlives the match.
#[test]
fn a_wrapper_that_unboxes_an_incoming_tuple_scalar_replaces_it() {
    let (tup, id) = boxed_tuple_id(2);
    let m = tops(
        vec![
            (
                binder("wrap", demand(false, false)),
                lam(
                    &["t"],
                    case_con(
                        var("t"),
                        &tup,
                        &["x", "y"],
                        app(app(var("w"), var("x")), var("y")),
                    ),
                ),
            ),
            (
                binder("w", demand(false, false)),
                lam(&["p", "q"], app(var("g"), var("p"))),
            ),
            (
                binder("user", demand(false, false)),
                app(var("wrap"), con_app(&tup, &[var("a"), var("b")])),
            ),
        ],
        json!({&tup: id, "g": callee(true)}),
    );
    let t = Tuples::of_module(&m);
    let f = one_flow(&t);
    assert_eq!(f.fate, TupleFate::ScalarReplace);
    assert!(
        f.consumers
            .iter()
            .any(|u| matches!(u, TupleUse::PassedTo { param: 0, .. }))
    );
}

// --- 6. closure results -----------------------------------------------------

/// A tuple built inside a let-bound lambda whose every occurrence is a
/// call: the returns can be rewritten, so it is followable.
#[test]
fn a_tuple_returned_from_a_let_bound_closure_is_followable() {
    let (tup, id) = boxed_tuple_id(2);
    let m = top_module(
        let1(
            "k",
            lam(&["n"], con_app(&tup, &[var("a"), var("b")])),
            case_con(
                app(var("k"), var("m")),
                &tup,
                &["x", "y"],
                app(var("g"), var("x")),
            ),
        ),
        json!({&tup: id, "g": callee(true)}),
    );
    let t = Tuples::of_module(&m);
    let f = one_flow(&t);
    assert_eq!(f.fate, TupleFate::WorkerReturn);
}

/// …and the same closure stored in a constructor is not: whoever pulls it
/// back out and calls it is outside this module.
#[test]
fn a_tuple_returning_closure_in_a_constructor_is_unresolved() {
    let (tup, id) = boxed_tuple_id(2);
    let m = top_module(
        let1(
            "k",
            lam(&["n"], con_app(&tup, &[var("a"), var("b")])),
            con_app("Just", &[var("k")]),
        ),
        json!({
            &tup: id,
            "Just": data_con("Just", "$base$GHC.Maybe$Just", 1)
        }),
    );
    let t = Tuples::of_module(&m);
    let f = one_flow(&t);
    assert_eq!(f.fate, TupleFate::Unresolved);
    assert_eq!(f.reason, Some(crate::tuples::R_CLOSURE_STORED));
}

/// The residual says *where* the closure went: consed onto a list is a
/// different whole-program fact from stored in a program constructor.
#[test]
fn a_tuple_returning_closure_consed_onto_a_list_says_so() {
    let (tup, id) = boxed_tuple_id(2);
    let m = top_module(
        let1(
            "k",
            lam(&["n"], con_app(&tup, &[var("a"), var("b")])),
            con_app(":", &[var("k"), var("rest")]),
        ),
        json!({&tup: id, ":": data_con(":", "$ghc-prim$GHC.Types$:", 2)}),
    );
    let t = Tuples::of_module(&m);
    let f = one_flow(&t);
    assert_eq!(f.fate, TupleFate::Unresolved);
    assert_eq!(f.reason, Some(crate::tuples::R_CLOSURE_CONSED));
}

// --- 7. may-analysis ---------------------------------------------------------

/// A callee computed by a `case` is not one of its alternatives: picking
/// either would be a guess, so the site is refused.
#[test]
fn a_case_selected_callee_is_refused_not_guessed() {
    let (tup, id) = boxed_tuple_id(2);
    let m = top_module(
        let1(
            "f1",
            lam(
                &["t"],
                case_con(var("t"), &tup, &["x", "y"], app(var("g"), var("x"))),
            ),
            let1(
                "f2",
                lam(&["t2"], app(var("imported"), var("t2"))),
                let1(
                    "sel",
                    case2(var("p"), var("f1"), var("f2")),
                    app(var("sel"), con_app(&tup, &[var("a"), var("b")])),
                ),
            ),
        ),
        json!({&tup: id, "g": callee(true), "imported": callee(false)}),
    );
    let t = Tuples::of_module(&m);
    let f = one_flow(&t);
    assert_ne!(f.fate, TupleFate::ScalarReplace);
    assert_eq!(f.fate, TupleFate::Unresolved);
    assert_eq!(f.reason, Some(crate::tuples::R_HIGHER_ORDER));
}

/// Where a parameter *is* followed, its uses are the union over every call
/// site — so a second producer's store defeats the first producer's
/// scrutiny. The union can only lose removability, never gain it.
#[test]
fn a_parameters_uses_are_the_union_over_its_call_sites() {
    let (tup, id) = boxed_tuple_id(2);
    // `k`'s parameter is scrutinised on one path and stored on another.
    let body = |store: Value| {
        let1(
            "k",
            lam(
                &["t"],
                case2(
                    var("p"),
                    case_con(var("t"), &tup, &["x", "y"], app(var("g"), var("x"))),
                    store,
                ),
            ),
            app(var("k"), con_app(&tup, &[var("a"), var("b")])),
        )
    };
    let m = top_module(
        body(con_app("Just", &[var("t")])),
        json!({
            &tup: id, "g": callee(true),
            "Just": data_con("Just", "$base$GHC.Maybe$Just", 1)
        }),
    );
    let t = Tuples::of_module(&m);
    let f = one_flow(&t);
    assert_eq!(f.fate, TupleFate::Preserve);
    assert_eq!(f.reason, Some(crate::tuples::R_STORED_CON));

    // Take the store away and the same parameter is only read.
    let m = top_module(
        body(app(var("g"), var("z"))),
        json!({&tup: id, "g": callee(true)}),
    );
    let t = Tuples::of_module(&m);
    let f = one_flow(&t);
    assert_eq!(f.fate, TupleFate::ScalarReplace);
}

// --- 8. strict fields and forcing -------------------------------------------

/// Scrutinising a *field* of the tuple is still one scrutiny of the tuple:
/// the nested match is about the field, not the box.
#[test]
fn scrutinising_a_field_is_one_scrutiny_of_the_tuple() {
    let (tup, id) = boxed_tuple_id(2);
    let m = top_module(
        let1(
            "r",
            con_app(&tup, &[var("a"), var("b")]),
            case_con(
                var("r"),
                &tup,
                &["x", "y"],
                case_con(var("x"), &tup, &["u", "v"], app(var("g"), var("u"))),
            ),
        ),
        json!({&tup: id, "g": callee(true)}),
    );
    let t = Tuples::of_module(&m);
    let f = one_flow(&t);
    assert_eq!(f.fate, TupleFate::ScalarReplace);
    assert_eq!(
        f.consumers
            .iter()
            .filter(|u| matches!(u, TupleUse::Scrutinised { .. }))
            .count(),
        1
    );
}

/// Forcing the whole tuple reads no field. It is a no-op on a constructor
/// application, so it neither keeps the box alive nor counts as a read.
#[test]
fn forcing_the_whole_tuple_reads_no_field() {
    let (tup, id) = boxed_tuple_id(2);
    let m = top_module(
        let1(
            "r",
            con_app(&tup, &[var("a"), var("b")]),
            case_force(var("r"), "w", app(var("g"), var("c"))),
        ),
        json!({&tup: id, "g": callee(true)}),
    );
    let t = Tuples::of_module(&m);
    let f = one_flow(&t);
    assert_eq!(f.fate, TupleFate::ScalarReplace);
    assert!(
        f.consumers
            .iter()
            .any(|u| matches!(u, TupleUse::Forced { .. }))
    );
    assert!(!f.consumers.iter().any(|u| u.reads_fields()));

    // …and forcing does not stop a later store from preserving it.
    let m = top_module(
        let1(
            "r",
            con_app(&tup, &[var("a"), var("b")]),
            case_force(var("r"), "w", con_app("Just", &[var("r")])),
        ),
        json!({
            &tup: id, "Just": data_con("Just", "$base$GHC.Maybe$Just", 1)
        }),
    );
    let t = Tuples::of_module(&m);
    let f = one_flow(&t);
    assert_eq!(f.fate, TupleFate::Preserve);
}

/// A tuple in a *strict* constructor field is stored, exactly as in a lazy
/// one: the field's strictness says when it is evaluated, not whether the
/// allocation exists.
#[test]
fn a_tuple_in_a_strict_constructor_field_is_stored() {
    let (tup, id) = boxed_tuple_id(2);
    let m = top_module(
        con_app("Strict", &[con_app(&tup, &[var("a"), var("b")])]),
        json!({&tup: id, "Strict": strict_data_con("Strict", "$main$M$Strict", 1)}),
    );
    let t = Tuples::of_module(&m);
    let f = one_flow(&t);
    assert_eq!(f.fate, TupleFate::Preserve);
    assert_eq!(f.reason, Some(crate::tuples::R_STORED_CON));
    assert!(
        f.consumers
            .iter()
            .any(|u| matches!(u, TupleUse::StoredIn { .. })),
        "stored, not scrutinised"
    );
}

/// A *tuple* constructor with a strict field is not ghc-prim's tuple and
/// is not in the population at all.
#[test]
fn a_strict_field_tuple_constructor_is_not_the_population() {
    let (tup, _) = boxed_tuple_id(2);
    let m = top_module(
        con_app(&tup, &[var("a"), var("b")]),
        json!({&tup: strict_data_con(&tup, &format!("$ghc-prim$GHC.Tuple.Prim${tup}"), 2)}),
    );
    let t = Tuples::of_module(&m);
    assert!(t.flows.is_empty());
    assert!(t.skipped.is_empty());
}

// --- the census' own invariants ---------------------------------------------

/// Every removable verdict the census reaches is re-derived from scratch
/// by the independent verifier, on every module the tests build.
#[test]
fn the_verifier_agrees_on_every_hand_built_module() {
    use std::collections::{HashMap, HashSet};

    use crate::verify::{CrossCheck, cross_check};

    let (tup, id) = boxed_tuple_id(2);
    let modules = [
        top_module(
            let1(
                "r",
                con_app(&tup, &[var("a"), var("b")]),
                case_con(var("r"), &tup, &["x", "y"], app(var("g"), var("x"))),
            ),
            json!({&tup: id, "g": callee(true)}),
        ),
        top_module(
            let1(
                "o",
                con_app(&tup, &[con_app(&tup, &[var("a"), var("b")]), var("c")]),
                case_con(
                    var("o"),
                    &tup,
                    &["p", "q"],
                    case_con(var("p"), &tup, &["x", "y"], app(var("g"), var("x"))),
                ),
            ),
            json!({&tup: id, "g": callee(true)}),
        ),
    ];
    let mut out = CrossCheck::default();
    for m in &modules {
        let t = Tuples::of_module(m);
        let population: HashSet<u32> = t.flows.iter().map(|f| f.construction).collect();
        let removable: HashSet<u32> = t
            .flows
            .iter()
            .filter(|f| matches!(f.fate, TupleFate::ScalarReplace | TupleFate::WorkerReturn))
            .map(|f| f.construction)
            .collect();
        cross_check(m, &population, &removable, HashMap::new(), &mut out);
    }
    assert_eq!(out.checked, 3);
    assert!(out.disagreements.is_empty(), "{:?}", out.disagreements);
    assert_eq!(out.census_stricter, 0);
    assert!(out.only_here.is_empty() && out.only_there.is_empty());
}
