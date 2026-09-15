//! Census behaviour on small hand-built modules.

use h2r_core_ir::{Module, raw};
use serde_json::{Value, json};

use crate::laziness::{Census, Class, Fate, Multiplicity, Sink};

fn demand(strict: bool, once: bool) -> Value {
    json!({"strict": strict, "absent": false, "usedOnce": once, "pretty": if strict {"S"} else {"L"}})
}

//------------------------------------------------------------------------------
// Structured types
//------------------------------------------------------------------------------
//
// Format 5 dumps every type structurally, into one hash-consed table per
// module that binders and `Type` nodes index into. The fixtures carry a
// fixed table with the handful of types they need; the constants below name
// its entries, and `ty_of` maps the rendering a fixture writes to the entry
// it means. That mapping lives *here only* — nothing in `crate::text` reads
// a rendering.

/// `TyConApp <occ> []`, with a stable name in the fixtures' own unit.
fn ty_con(occ: &str) -> Value {
    json!({"kind": "TyConApp",
           "tycon": {"name": format!("$main$M${occ}"), "occ": occ, "unique": occ},
           "args": []})
}

/// `TyConApp Char []`, with the `TyCon` GHC really uses.
fn ty_char() -> Value {
    json!({"kind": "TyConApp",
           "tycon": {"name": h2r_core_ir::CHAR_TYCON, "occ": "Char", "unique": "3g"},
           "args": []})
}

/// `TyConApp List [elem]`, with the `TyCon` GHC really uses.
fn ty_list(elem: u32) -> Value {
    json!({"kind": "TyConApp",
           "tycon": {"name": h2r_core_ir::LIST_TYCON, "occ": "List", "unique": "3Q"},
           "args": [elem]})
}

/// `TyConApp <Class> [T]`: a class constraint on the fixtures' type `T`.
fn class_ty_json(name: &str, occ: &str) -> Value {
    json!({"kind": "TyConApp",
           "tycon": {"name": name, "occ": occ, "unique": occ},
           "args": [TY_T]})
}

fn ty_var(occ: &str) -> Value {
    json!({"kind": "TyVar", "name": format!("$_in${occ}"), "occ": occ, "unique": occ})
}

const TY_T: u32 = 0;
const TY_R: u32 = 1;
const TY_CHAR: u32 = 2;
const TY_STRING: u32 = 3;
const TY_A: u32 = 4;
const TY_LIST_A: u32 = 5;
/// `Show T`, `Eq T`, `Ord T`: the class constraints the class-op fixtures
/// give their dictionaries. A dictionary's *type* is what says which class
/// it belongs to (`classops::K2_DICT_TYPE`), so the fixtures carry the real
/// class `TyCon`s.
const TY_SHOW_T: u32 = 6;
const TY_EQ_T: u32 = 7;
const TY_ORD_T: u32 = 8;
/// `T -> T` and `T -> T -> T`: the function types the higher-order
/// fixtures give their closure-valued slots. What makes a slot a boundary
/// is the *structured* type (`higher::H1_FUNCTION_TYPED`), so the fixtures
/// carry real `FunTy`s rather than a rendering that looks like one.
const TY_FUN1: u32 = 9;
const TY_FUN2: u32 = 10;

/// The type table every hand-built module carries.
fn ty_table() -> Value {
    json!([
        ty_con("T"),
        ty_con("R"),
        ty_char(),
        ty_list(TY_CHAR),
        ty_var("a"),
        ty_list(TY_A),
        class_ty_json("$base$GHC.Show$Show", "Show"),
        class_ty_json("$ghc-prim$GHC.Classes$Eq", "Eq"),
        class_ty_json("$ghc-prim$GHC.Classes$Ord", "Ord"),
        json!({"kind": "FunTy", "mult": TY_T, "arg": TY_T, "res": TY_T}),
        json!({"kind": "FunTy", "mult": TY_T, "arg": TY_T, "res": TY_FUN1}),
    ])
}

/// The table entry a fixture means by this rendering. Unknown renderings
/// are a fixture bug, not a type to guess at.
fn ty_of(rendered: &str) -> u32 {
    match rendered {
        "T" => TY_T,
        "R" => TY_R,
        "Char" => TY_CHAR,
        "[Char]" | "String" | "FilePath" => TY_STRING,
        "a" => TY_A,
        "[a]" => TY_LIST_A,
        other => panic!("fixture type {other:?} has no entry in ty_table()"),
    }
}

/// Fixtures key the id table by occurrence name, because that is how they
/// read; a real dump keys it by stable name. Rekey by the name the global
/// `Var`s of this module actually carry, which is what the loader looks up.
fn key_ids_by_stable_name(m: &mut Value) {
    let mut occ_to_name: std::collections::HashMap<String, String> =
        std::collections::HashMap::new();
    let mut stack = vec![m["binds"].clone()];
    while let Some(x) = stack.pop() {
        match x {
            Value::Object(o) => {
                if o.get("node") == Some(&json!("Var"))
                    && o.get("isGlobal") == Some(&json!(true))
                    && let (Some(Value::String(occ)), Some(Value::String(name))) =
                        (o.get("occ"), o.get("name"))
                {
                    occ_to_name.insert(occ.clone(), name.clone());
                }
                stack.extend(o.into_iter().map(|(_, v)| v));
            }
            Value::Array(a) => stack.extend(a),
            _ => {}
        }
    }
    let Value::Object(ids) = m["ids"].take() else {
        return;
    };
    let mut out = serde_json::Map::new();
    for (k, v) in ids {
        let key = occ_to_name.get(&k).cloned().unwrap_or(k);
        out.insert(key, v);
    }
    m["ids"] = Value::Object(out);
}

fn binder(occ: &str, dmd: Value) -> Value {
    json!({
        "kind": "id", "name": occ, "occ": occ, "unique": occ,
        "type": "T", "ty": TY_T,
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
        "node": "Case", "scrut": scrut, "binder": binder("wild", demand(false, false)), "type": "R", "ty": TY_R,
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
        "format": raw::FORMAT, "module": "M", "unit": "main", "types": ty_table(), "ids": ids,
        "binds": [{"rec": false, "pairs": [{
            "binder": binder("top", demand(false, false)),
            "rhs": {"node": "Let", "bind": {"rec": false, "pairs": [{
                "binder": binder("x", x_demand), "rhs": app(var("f"), var("a")),
                "whnf": false, "trivial": false, "cheap": false, "okForSpec": false
            }]}, "body": body},
            "whnf": false, "trivial": false, "cheap": false, "okForSpec": false
        }]}]
    });
    let mut m = m;
    key_ids_by_stable_name(&mut m);
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
        "format": raw::FORMAT, "module": "M", "unit": "main", "types": ty_table(),
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
    let mut m = m;
    key_ids_by_stable_name(&mut m);
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
        "format": raw::FORMAT, "module": "M", "unit": "main", "types": ty_table(),
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
    let mut m = m;
    key_ids_by_stable_name(&mut m);
    let m = Module::from_raw(serde_json::from_value(m).unwrap()).unwrap();
    let c = Census::of_modules([&m]);
    let site = c.args.iter().find(|a| a.callee.occ == "k").unwrap();
    assert_eq!(site.callee.resolution, Resolution::ExactLocal);
}

/// A module with one top-level binding whose RHS is `body`, an id table
/// `ids`, and no local lets: for testing argument sites directly.
fn top_module(body: Value, ids: Value) -> Module {
    let m = json!({
        "format": raw::FORMAT, "module": "M", "unit": "main", "types": ty_table(), "ids": ids,
        "binds": [{"rec": false, "pairs": [{
            "binder": binder("top", demand(false, false)), "rhs": body,
            "whnf": false, "trivial": false, "cheap": false, "okForSpec": false
        }]}]
    });
    let mut m = m;
    key_ids_by_stable_name(&mut m);
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
        "format": raw::FORMAT, "module": "M", "unit": "main", "types": ty_table(),
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
    let mut m = m;
    key_ids_by_stable_name(&mut m);
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
        "binder": binder("wild", demand(false, false)), "type": "R", "ty": TY_R,
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
        "format": raw::FORMAT, "module": "M", "unit": "main", "types": ty_table(), "ids": ids, "binds": binds
    });
    let mut m = m;
    key_ids_by_stable_name(&mut m);
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
        "binder": binder(cb, demand(false, false)), "type": "R", "ty": TY_R,
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
        "binder": binder(cb, demand(false, false)), "type": "R", "ty": TY_R,
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

//------------------------------------------------------------------------------
// The normalised scalar view (scalar.rs)
//------------------------------------------------------------------------------

// The view is the milestone's deliverable: what the program looks like with
// one proven tuple gone. Every test below asserts *completeness* — every
// consumer of the flow, and every call site it proved, placed exactly once —
// because a view that quietly drops a use would be a wrong rewrite, not a
// missing line.

use crate::scalar::{LineKind, view};

/// The whole census over one hand-built module, so that a view carries the
/// independent verifier's verdict as well as the census'.
fn census_of(m: &Module) -> Census {
    Census::raw([m])
}

/// `let r = (a, b) in case r of (x, y) -> g x`: two scalars, one binding.
#[test]
fn a_scalar_replace_view_places_every_field_and_consumer() {
    let (tup, id) = boxed_tuple_id(2);
    let m = top_module(
        let1(
            "r",
            con_app(&tup, &[var("a"), var("b")]),
            case_con(var("r"), &tup, &["x", "y"], app(var("g"), var("x"))),
        ),
        json!({&tup: id, "g": callee(true)}),
    );
    let census = census_of(&m);
    let mods = [&m];
    let tc = TupleCensus::of_modules(&mods, &census);
    let t = &tc.per_module[0];
    let f = one_flow(t);
    assert_eq!(f.fate, TupleFate::ScalarReplace);
    let v = view(t, f, tc.is_verified(f));
    v.check();
    assert!(v.verified, "the independent verifier re-derived it");
    assert_eq!(v.scalars.len(), 2, "one scalar per field");
    assert_eq!(v.scalars[0].node, f.fields[0]);
    assert_eq!(v.scalars[1].node, f.fields[1]);
    assert_eq!(
        v.consumers,
        f.consumers.len(),
        "every consumer placed exactly once"
    );
    assert!(v.unplaced.is_empty());
    let binding = v
        .lines
        .iter()
        .find(|l| l.kind == LineKind::Binding)
        .expect("the scrutiny becomes bindings");
    assert!(binding.rules.contains(&crate::tuples::T2_SCRUTINISED));
    // `case r of (x, y) -> …` ⇒ `x := f0; y := f1`.
    assert!(binding.text.contains(":= f0"), "{}", binding.text);
    assert!(binding.text.contains(":= f1"), "{}", binding.text);
}

/// A worker returning `(# p, p #)` that two call sites take apart: the
/// result becomes two scalar results and *both* call sites are in the view.
#[test]
fn a_worker_return_view_places_every_call_site() {
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
    let census = census_of(&m);
    let mods = [&m];
    let tc = TupleCensus::of_modules(&mods, &census);
    let t = &tc.per_module[0];
    let f = one_flow(t);
    assert_eq!(f.fate, TupleFate::WorkerReturn);
    let v = view(t, f, tc.is_verified(f));
    v.check();
    assert_eq!(v.call_sites, 2, "both call sites are in the view");
    assert_eq!(v.consumers, f.consumers.len());
    // Each call site's scrutiny folds the call into itself, which is the
    // `(x, y) := f a` multiple-return shape.
    let bindings: Vec<_> = v
        .lines
        .iter()
        .filter(|l| l.kind == LineKind::Binding)
        .collect();
    assert_eq!(bindings.len(), 2);
    for b in &bindings {
        assert!(b.rules.contains(&crate::tuples::T7_CALL_RESULT), "{:?}", b);
        assert!(b.call_site.is_some());
        assert!(b.text.contains(":="), "{}", b.text);
    }
    assert!(
        v.lines
            .iter()
            .any(|l| l.kind == LineKind::Hop && l.rules.contains(&crate::tuples::T6_RETURNED))
    );
}

/// A tuple in a removable tuple's field: the inner view reaches its readers
/// *through* the outer's field binder, and says so.
#[test]
fn a_nested_view_shows_the_inner_scalars_through_the_outer() {
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
    let census = census_of(&m);
    let mods = [&m];
    let tc = TupleCensus::of_modules(&mods, &census);
    let t = &tc.per_module[0];
    let outer = t.flows.iter().find(|f| f.bound.is_some()).unwrap();
    let inner = t.flows.iter().find(|f| f.bound.is_none()).unwrap();

    let ov = view(t, outer, tc.is_verified(outer));
    ov.check();
    assert_eq!(ov.consumers, outer.consumers.len());

    let iv = view(t, inner, tc.is_verified(inner));
    iv.check();
    assert_eq!(iv.consumers, inner.consumers.len());
    // The inner tuple's own fields are still its scalars…
    assert_eq!(iv.scalars.len(), 2);
    // …and one line says the outer box is gone too, naming the outer
    // construction and the field binder the scalars reach the readers
    // through.
    let nested = iv
        .lines
        .iter()
        .find(|l| l.rules.contains(&crate::tuples::T12_NESTED))
        .expect("the nesting is in the view");
    assert!(nested.nodes.contains(&outer.construction));
    assert!(nested.text.contains("ScalarReplace"), "{}", nested.text);
    assert!(nested.text.contains("through p#"), "{}", nested.text);
    // The scrutiny of the outer's field binder is the inner's own consumer,
    // and it is placed as a binding over the inner's scalars.
    assert!(
        iv.lines
            .iter()
            .any(|l| l.rules.contains(&crate::tuples::T2_SCRUTINISED) && l.text.contains(":= f0"))
    );
}

/// The `h2r show` footer finds the flow from the construction, from the
/// binder the tuple is bound to, and from an occurrence of it.
#[test]
fn the_show_footer_finds_the_flow_from_any_of_its_nodes() {
    use std::collections::HashSet;

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
    let verified: HashSet<u32> = HashSet::from([f.construction]);
    let p = crate::scalar::Provenance::of(&t, verified);
    assert_eq!(p.flows_at(f.construction), vec![0]);
    let proof = p.proof_at(f.construction, 0);
    assert!(proof.tuple.as_ref().unwrap().contains("arity 2"));
    assert_eq!(
        proof.fate.as_deref(),
        Some("ScalarReplace  [verified: yes]")
    );
    assert_eq!(proof.consumers.len(), f.consumers.len());
    assert!(
        proof
            .evidence
            .iter()
            .any(|(r, _)| *r == crate::tuples::T0_TUPLE_CON)
    );
    // The alias binder, and the scrutiny, both lead to the same flow.
    let b = f.bound.expect("let-bound");
    assert!(p.binder_note(b).unwrap().contains("alias of tuple flow #0"));
    let case = f
        .consumers
        .iter()
        .find_map(|u| match u {
            TupleUse::Scrutinised { case, .. } => Some(*case),
            _ => None,
        })
        .unwrap();
    assert_eq!(p.flows_at(case), vec![0]);
    assert!(p.node_note(case).unwrap().contains("Scrutinised"));
}

//------------------------------------------------------------------------------
// The cross-milestone link (link.rs)
//------------------------------------------------------------------------------

/// A lazy pattern `~(u, v)` as the desugarer leaves it: the scrutinee bound
/// once and one selector thunk per field. Both selector thunks disappear
/// with the tuple; the binding that holds the tuple itself does not, because
/// its right-hand side is the call, not a selection.
#[test]
fn a_lazy_pattern_desugaring_explains_two_thunk_sites() {
    let (tup, id) = boxed_tuple_id(2);
    // g, lazy in all four arguments, so each selector is used twice on one
    // path: memoisation required, which is the population that matters.
    let lazy4 = json!({
        "name": "g", "occ": "g", "arity": 4,
        "dmdSig": {"args": [demand(false, false), demand(false, false),
                            demand(false, false), demand(false, false)],
                   "diverges": false, "pretty": ""},
        "isJoinPoint": false, "dataCon": null
    });
    let body = app(
        app(app(app(var("g"), var("a")), var("a")), var("b")),
        var("b"),
    );
    let m = tops(
        vec![
            (
                binder("w", demand(false, false)),
                lam(&["z"], con_app(&tup, &[var("p"), var("q")])),
            ),
            (
                binder("top", demand(false, false)),
                lam(
                    &["y"],
                    let1(
                        "t",
                        app(var("w"), var("y")),
                        let1(
                            "a",
                            case_con(var("t"), &tup, &["u", "u2"], var("u")),
                            let1("b", case_con(var("t"), &tup, &["v1", "v"], var("v")), body),
                        ),
                    ),
                ),
            ),
        ],
        json!({&tup: id, "g": lazy4}),
    );
    let census = Census::raw([&m]);
    let mods = [&m];
    let tc = TupleCensus::of_modules(&mods, &census);
    let f = one_flow(&tc.per_module[0]);
    assert_eq!(f.fate, TupleFate::WorkerReturn);
    assert!(tc.is_verified(f), "the verifier re-derives it");
    assert_eq!(
        f.consumers
            .iter()
            .filter(|u| matches!(u, TupleUse::Selected { .. }))
            .count(),
        2,
        "one lazy selector per field"
    );

    let l = crate::link::link(&census, &tc, &mods);
    l.check();
    // t, a and b are all potential thunk sites; only the two selectors are
    // explained by the tuple going away.
    assert_eq!(l.thunk_sites, 3);
    assert_eq!(l.explained.len(), 2);
    assert_eq!(l.remaining(), 1);
    let mut names: Vec<&str> = l.explained.iter().map(|e| e.occ.as_str()).collect();
    names.sort_unstable();
    assert_eq!(names, ["a", "b"]);
    for e in &l.explained {
        assert_eq!(e.rule, crate::tuples::T3_SELECTED);
        assert_eq!(e.over, f.construction);
        assert_eq!(e.fate, Fate::Memo);
        assert!(e.memo && e.shared);
    }
    assert_eq!(l.by_rule.get(crate::tuples::T3_SELECTED), Some(&2));
    let memo = l
        .fates
        .iter()
        .find(|r| r.label == "memoisation required")
        .unwrap();
    assert_eq!((memo.before, memo.explained, memo.after()), (3, 2, 1));
}

/// `before = normalised + preserved + unsupported`, on a module with one of
/// each: a removable tuple, a stored one, and one the rules refuse.
#[test]
fn the_milestone_accounting_closes() {
    let (tup, id) = boxed_tuple_id(2);
    let m = tops(
        vec![
            (
                binder("removable", demand(false, false)),
                let1(
                    "r",
                    con_app(&tup, &[var("a"), var("b")]),
                    case_con(var("r"), &tup, &["x", "y"], app(var("g"), var("x"))),
                ),
            ),
            (
                binder("stored", demand(false, false)),
                con_app("Just", &[con_app(&tup, &[var("c"), var("d")])]),
            ),
            // Returned from an exported function: the callers are outside
            // the module, so the rules refuse it rather than guess.
            (
                exported("escaping"),
                lam(&["k"], con_app(&tup, &[var("e"), var("f2")])),
            ),
        ],
        json!({
            &tup: id, "g": callee(true),
            "Just": data_con("Just", "$base$GHC.Maybe$Just", 1)
        }),
    );
    let census = Census::raw([&m]);
    let mods = [&m];
    let tc = TupleCensus::of_modules(&mods, &census);
    let acct = &tc.accounting;
    acct.check();
    let b = acct.bucket(true);
    assert_eq!(b.before, 3);
    assert_eq!(b.normalised, 1);
    assert_eq!(b.preserved, 1);
    assert_eq!(b.unsupported, 1);
    assert_eq!(b.before, b.normalised + b.preserved + b.unsupported);
    assert_eq!(acct.removable_unverified, 0);
    assert_eq!(
        acct.residual.iter().map(|(_, n)| n).sum::<usize>(),
        b.unsupported
    );
}

//------------------------------------------------------------------------------
// Representation boundaries (boundary.rs)
//------------------------------------------------------------------------------

// A flow's own def-use proof says the tuple is transport. These say whether
// every *other* value that arrives at the same parameter or return agrees
// on one representation — which is what applying all the scalar views at
// once needs, and which neither the census nor the verifier ever asks.

use crate::boundary::{Boundary, BoundaryVerdict, Representation, settle};

/// Every boundary of a module, with its verdict, keyed by its rendering.
fn boundaries_of(m: &Module) -> (Tuples<'_>, Vec<(String, BoundaryVerdict)>, Vec<String>) {
    let t = Tuples::of_module(m);
    let s = settle(&t);
    let reports = s
        .boundaries
        .reports
        .iter()
        .map(|r| (r.name.clone(), r.verdict))
        .collect();
    let downgraded = s
        .downgrades
        .iter()
        .map(|d| format!("{} -> {:?} ({})", d.construction, d.to, d.reason))
        .collect();
    (t, reports, downgraded)
}

/// Two removable tuples and one opaque value reach the same parameter. Each
/// tuple has a perfect def-use proof; the parameter still cannot become two
/// scalars, because the third call site has a real box to pass. Only a
/// clone of the callee could take the split, so both flows lose their fate.
#[test]
fn two_removable_producers_and_an_opaque_one_need_a_clone() {
    let (tup, id) = boxed_tuple_id(2);
    let body = app(
        app(
            app(
                gvar("h"),
                app(var("k"), con_app(&tup, &[var("a"), var("b")])),
            ),
            app(var("k"), con_app(&tup, &[var("c"), var("d")])),
        ),
        app(var("k"), gvar("opaque")),
    );
    let m = top_module(
        let1(
            "k",
            lam(
                &["t"],
                case_con(var("t"), &tup, &["x", "y"], app(var("g"), var("x"))),
            ),
            body,
        ),
        json!({&tup: id, "g": callee(true)}),
    );
    let (t, reports, downgraded) = boundaries_of(&m);
    assert_eq!(t.flows.len(), 2);
    // The census itself proves both removable: each one's own uses are a
    // parameter it is scrutinised at.
    for f in &t.flows {
        assert_eq!(f.fate, TupleFate::ScalarReplace, "{f:?}");
    }
    assert_eq!(reports.len(), 1);
    assert_eq!(reports[0].1, BoundaryVerdict::CloneRequired);
    assert!(reports[0].0.starts_with("parameter 0 of k"));
    assert_eq!(downgraded.len(), 2, "{downgraded:?}");
    assert!(downgraded.iter().all(|d| d.contains("RemovableWithClone")));
}

/// The same shape without the opaque call: every producer of the parameter
/// is a removable tuple of the same arity, so the parameter becomes two
/// scalars and both flows keep their fate.
#[test]
fn two_removable_producers_of_one_arity_split_uniformly() {
    let (tup, id) = boxed_tuple_id(2);
    let body = app(
        app(
            gvar("h"),
            app(var("k"), con_app(&tup, &[var("a"), var("b")])),
        ),
        app(var("k"), con_app(&tup, &[var("c"), var("d")])),
    );
    let m = top_module(
        let1(
            "k",
            lam(
                &["t"],
                case_con(var("t"), &tup, &["x", "y"], app(var("g"), var("x"))),
            ),
            body,
        ),
        json!({&tup: id, "g": callee(true)}),
    );
    let (t, reports, downgraded) = boundaries_of(&m);
    assert_eq!(t.flows.len(), 2);
    assert_eq!(reports.len(), 1);
    assert_eq!(
        reports[0].1,
        BoundaryVerdict::UniformSplit { arity: 2 },
        "{reports:?}"
    );
    assert!(downgraded.is_empty(), "{downgraded:?}");
}

/// A function that returns a removable tuple on one branch and the result
/// of an imported call on the other. A return cannot be specialised the way
/// a parameter can — every return point is in the same body — so the
/// boundary is unresolved and the flow goes with it.
#[test]
fn a_return_that_mixes_a_tuple_with_an_imported_result_is_unresolved() {
    let (tup, id) = boxed_tuple_id(2);
    let m = tops(
        vec![
            (
                binder("f", demand(false, false)),
                lam(
                    &["p"],
                    case2(
                        var("p"),
                        con_app(&tup, &[var("a"), var("b")]),
                        app(gvar("imported"), var("p")),
                    ),
                ),
            ),
            (
                binder("user", demand(false, false)),
                case_con(
                    app(var("f"), var("x")),
                    &tup,
                    &["u", "v"],
                    app(var("g"), var("u")),
                ),
            ),
        ],
        json!({&tup: id, "g": callee(true)}),
    );
    let t = Tuples::of_module(&m);
    assert_eq!(one_flow(&t).fate, TupleFate::WorkerReturn);
    let (_, reports, downgraded) = boundaries_of(&m);
    assert_eq!(reports.len(), 1);
    assert!(reports[0].0.starts_with("return of f"));
    assert_eq!(reports[0].1, BoundaryVerdict::Unresolved);
    assert_eq!(downgraded.len(), 1, "{downgraded:?}");
    assert!(downgraded[0].contains("Unresolved"));
    assert!(downgraded[0].contains(crate::boundary::B_PRODUCERS_DISAGREE));
    // …and the census that owns the flows applies it: the fate is gone and
    // the reason names the boundary that took it.
    let census = census_of(&m);
    let mods = [&m];
    let tc = crate::tuples::TupleCensus::of_modules(&mods, &census);
    assert_eq!(tc.flows[0].fate, TupleFate::Unresolved);
    assert_eq!(
        tc.flows[0].reason,
        Some(crate::tuples::R_BOUNDARY_NOT_UNIFORM)
    );
    assert!(tc.flows[0].detail.starts_with("return of f"));
    assert_eq!(tc.accounting.bucket(true).normalised, 0);
}

/// A callee whose every call site passes the same removable tuple, but
/// which is *also* handed to something as a value: the PAP holds the
/// original representation, so the parameter cannot be split whatever the
/// producers say. The census refuses this shape too — its own
/// `callee-parameter-cannot-be-split` rule fires — and the point of the
/// assertion is that the two independent walks agree about it.
#[test]
fn a_function_used_as_a_value_has_no_splittable_parameter() {
    use std::collections::HashSet;

    let (tup, id) = boxed_tuple_id(2);
    let m = top_module(
        let1(
            "k",
            lam(
                &["t"],
                case_con(var("t"), &tup, &["x", "y"], app(var("g"), var("x"))),
            ),
            app(
                app(gvar("h"), var("k")),
                app(var("k"), con_app(&tup, &[var("a"), var("b")])),
            ),
        ),
        json!({&tup: id, "g": callee(true)}),
    );
    let t = Tuples::of_module(&m);
    let f = one_flow(&t);
    assert_eq!(f.fate, TupleFate::Unresolved);
    assert_eq!(f.reason, Some(crate::tuples::R_CALLEE_NOT_SPLITTABLE));
    // …and the boundary, asked directly, says the same thing for its own
    // reason: one occurrence of `k` is not a call site at all.
    let k = m
        .binders
        .iter()
        .position(|b| b.occ == "k")
        .expect("the callee is bound") as u32;
    let all: HashSet<u32> = t.flows.iter().map(|f| f.construction).collect();
    let r = crate::boundary::examine(
        &t,
        Boundary::Parameter {
            function: k,
            index: 0,
        },
        &all,
    );
    assert_eq!(r.verdict, BoundaryVerdict::Unresolved);
    assert_eq!(r.reason, Some(crate::boundary::B_FUNCTION_IS_A_VALUE));
    // The producer that *is* there is uniform: the refusal is about the
    // other use, not about disagreement.
    assert_eq!(r.requested, vec![Representation::Scalars(2)]);
}

/// The tuple is passed into `f`'s parameter, `f` returns it, and the call
/// site scrutinises the result: two boundaries on one flow, and both have
/// to be checked. `f` is the identity, so its return is whatever its
/// parameter is — which only holds once the parameter boundary itself is a
/// uniform split.
#[test]
fn a_flow_that_crosses_two_boundaries_has_both_checked() {
    let (tup, id) = boxed_tuple_id(2);
    let m = tops(
        vec![
            (binder("f", demand(false, false)), lam(&["t"], var("t"))),
            (
                binder("user", demand(false, false)),
                case_con(
                    app(var("f"), con_app(&tup, &[var("a"), var("b")])),
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
    assert!(
        f.consumers
            .iter()
            .any(|u| matches!(u, TupleUse::PassedTo { param: 0, .. }))
    );
    assert!(
        f.consumers
            .iter()
            .any(|u| matches!(u, TupleUse::Returned { .. }))
    );
    let (_, mut reports, downgraded) = boundaries_of(&m);
    reports.sort_by(|a, b| a.0.cmp(&b.0));
    assert_eq!(reports.len(), 2, "{reports:?}");
    assert!(reports[0].0.starts_with("parameter 0 of f"));
    assert!(reports[1].0.starts_with("return of f"));
    for (name, v) in &reports {
        assert_eq!(*v, BoundaryVerdict::UniformSplit { arity: 2 }, "{name}");
    }
    assert!(downgraded.is_empty(), "{downgraded:?}");
}

//------------------------------------------------------------------------------
// The generic aggregate walk, on a non-tuple constructor (flow.rs)
//------------------------------------------------------------------------------

use crate::flow::{self, Client, Ctx, FlowUse, saturated_con};
use crate::scope::Scope;
use h2r_core_ir::ExprId;

/// A client with no rules of its own: everything it sees is what the
/// generic walk produced. This is the whole contract a non-tuple client
/// (M2.3b's program ADTs and lists) has to implement.
struct Probe;

impl Client for Probe {
    type Use = FlowUse;
}

/// `let j = Just (f a) in h (case j of Just y -> g y) (Wrap j)`.
///
/// Nothing here is a tuple, and nothing in [`crate::flow`] looks at the
/// constructor's name: `Just` is found through its `DataConInfo`. The walk
/// should bind the construction to `j`, report the scrutiny with the
/// alternative's field binder exposed, and report the `Wrap` field as a
/// store that keeps the value alive.
#[test]
fn the_generic_walk_follows_a_non_tuple_constructor() {
    let m = top_module(
        let1(
            "j",
            con_app("Just", &[app(var("f"), var("a"))]),
            app(
                app(
                    var("h"),
                    case_con(var("j"), "Just", &["y"], app(var("g"), var("y"))),
                ),
                con_app("Wrap", &[var("j")]),
            ),
        ),
        json!({
            "Just": data_con("Just", "$main$M$Just", 1),
            "Wrap": data_con("Wrap", "$main$M$Wrap", 1),
            "f": callee(true), "g": callee(true), "h": callee(true)
        }),
    );
    let scope = Scope::new(&m);
    // The population: saturated constructor applications of `Just`,
    // selected through the head's `DataConInfo` and not by name.
    let starts: Vec<ExprId> = (0..m.exprs.len() as ExprId)
        .filter(|id| {
            saturated_con(&scope, *id).is_some_and(|(dc, _, _)| dc.name.ends_with("$Just"))
        })
        .collect();
    assert_eq!(starts.len(), 1, "one `Just` construction");
    let (dc, _head, fields) = saturated_con(&scope, starts[0]).unwrap();
    assert_eq!(fields.len(), 1, "one field, in field order");

    let top_pairs: Vec<h2r_core_ir::BinderId> = m
        .top
        .iter()
        .flat_map(|b| b.pairs.iter())
        .map(|p| p.binder)
        .collect();
    let cx = Ctx {
        m: &m,
        scope: &scope,
        top_pairs: &top_pairs,
        start: starts[0],
        arity: dc.rep_arity,
        con: Some(dc),
    };
    let w = flow::walk(&cx, &mut Probe);

    // T1: the construction is let-bound, and the flow is the occurrences of
    // that binder.
    assert_eq!(w.bound.map(|b| m.binder(b).occ.as_str()), Some("j"));
    // T2: the scrutiny, with the alternative's field binders exposed — this
    // is what lets a client follow one field rather than the whole value.
    assert_eq!(w.scrutinies.len(), 1);
    let s = &w.scrutinies[0];
    assert_eq!(
        s.field_binders
            .iter()
            .map(|b| m.binder(*b).occ.as_str())
            .collect::<Vec<_>>(),
        vec!["y"],
        "field 0 of `Just` is bound to y"
    );
    assert!(matches!(m.expr(s.case), h2r_core_ir::Expr::Case { .. }));
    // The two uses, and nothing else.
    assert!(
        w.consumers.iter().any(|u| matches!(
            u,
            FlowUse::Scrutinised {
                all_fields_bound: true,
                ..
            }
        )),
        "{:?}",
        w.consumers
    );
    assert!(
        w.consumers
            .iter()
            .any(|u| matches!(u, FlowUse::StoredIn { .. })),
        "{:?}",
        w.consumers
    );
    assert_eq!(w.consumers.len(), 2);
    // T9 is what keeps it alive: one escape, and it is a *proven* real
    // value rather than something the rules could not follow.
    assert_eq!(w.escapes.len(), 1);
    assert!(
        w.escapes[0].0,
        "stored in a constructor field: a real value"
    );
    assert_eq!(w.escapes[0].1, flow::R_STORED_CON);
    assert!(!w.returned, "the value never crosses a return");
    assert!(!w.over_budget);
    let rules: Vec<&str> = w.evidence.iter().map(|e| e.rule).collect();
    for want in [flow::T1_LET_BOUND, flow::T2_SCRUTINISED, flow::T9_STORED] {
        assert!(rules.contains(&want), "{want} in {rules:?}");
    }
}

//------------------------------------------------------------------------------
// Constructor fields: what is evaluated, and when (fields.rs)
//------------------------------------------------------------------------------

use crate::fields::{ConStrictness, FieldDemand, FieldRep, Fields, ObsKind, ValueRecursion};

/// `case <scrut> of wild { alts… }`, each alternative `(con, binders, rhs)`;
/// a `con` of `"DEFAULT"` is the default alternative.
fn case_alts(scrut: Value, alts: &[(&str, Vec<&str>, Value)]) -> Value {
    let alts: Vec<Value> = alts
        .iter()
        .map(|(con, binders, rhs)| {
            let c = if *con == "DEFAULT" {
                json!({"kind": "DEFAULT"})
            } else {
                json!({"kind": "DataAlt", "name": format!("$main$M${con}"), "occ": con, "tag": 1})
            };
            json!({
                "con": c,
                "binders": binders.iter().map(|b| binder(b, demand(false, false)))
                    .collect::<Vec<_>>(),
                "rhs": rhs
            })
        })
        .collect();
    json!({
        "node": "Case", "scrut": scrut,
        "binder": binder("wild", demand(false, false)), "type": "R", "ty": TY_R,
        "alts": alts
    })
}

/// A program data constructor, for the id table: its stable name puts it in
/// this module, which is what the report's program/library split reads.
fn prog_con(occ: &str, arity: u32) -> Value {
    data_con(occ, &format!("$main$M${occ}"), arity)
}

fn prog_con_strict(occ: &str, arity: u32) -> Value {
    let mut d = prog_con(occ, arity);
    d["dataCon"]["strictFields"] = json!(vec![true; arity as usize]);
    d
}

/// `let rec r = <rhs> in <body>`.
fn letrec1(occ: &str, rhs: Value, body: Value) -> Value {
    json!({"node": "Let", "bind": {"rec": true, "pairs": [{
        "binder": binder(occ, demand(false, false)), "rhs": rhs,
        "whnf": false, "trivial": false, "cheap": false, "okForSpec": false
    }]}, "body": body})
}

fn field_census(m: &Module) -> Fields<'_> {
    let census = Census::raw([m]);
    Fields::of_module(m, &census)
}

fn one_con_flow<'a>(f: &'a Fields<'a>, occ: &str) -> &'a crate::fields::FieldFlow {
    let mut it = f.flows.iter().filter(|x| x.occ == occ);
    let first = it.next().unwrap_or_else(|| panic!("no {occ} construction"));
    assert!(it.next().is_none(), "expected one {occ} construction");
    first
}

/// `let r = Foo (g a) in seq r ()`: the constructor reaches WHNF and no
/// field is read, so nothing demands the field. It is not `Direct` — that
/// is the bottom-preservation case, `Foo (error …) `seq` 42` — and with a
/// lazy field and no other obligation it is `Dead`.
#[test]
fn a_construction_observed_only_at_whnf_does_not_demand_its_field() {
    let m = top_module(
        let1(
            "r",
            con_app("Foo", &[app(var("g"), var("a"))]),
            case_force(var("r"), "seqw", var("u")),
        ),
        json!({"Foo": prog_con("Foo", 1), "g": callee(true)}),
    );
    let f = field_census(&m);
    let flow = one_con_flow(&f, "Foo");
    assert!(flow.observed());
    assert_eq!(
        flow.observations
            .iter()
            .filter(|o| o.kind == ObsKind::WhnfOnly)
            .count(),
        1
    );
    let v = &flow.verdicts[0];
    assert_eq!(v.demand, FieldDemand::Never);
    assert_eq!(v.strictness, ConStrictness::LazyField);
    assert_ne!(v.rep, FieldRep::Direct);
    assert_eq!(v.rep, FieldRep::Dead);
}

/// A field bound by the pattern and never used: nothing demands it.
#[test]
fn a_field_bound_and_never_used_is_dead() {
    let m = top_module(
        let1(
            "r",
            con_app("Foo", &[app(var("g"), var("a"))]),
            case_alts(var("r"), &[("Foo", vec!["x"], var("u"))]),
        ),
        json!({"Foo": prog_con("Foo", 1), "g": callee(true)}),
    );
    let f = field_census(&m);
    let flow = one_con_flow(&f, "Foo");
    assert!(
        flow.observations
            .iter()
            .any(|o| o.kind == ObsKind::FieldBoundUnused)
    );
    assert_eq!(flow.verdicts[0].demand, FieldDemand::Never);
    assert_eq!(flow.verdicts[0].rep, FieldRep::Dead);
}

/// Forced on one path and taken apart on another: the field is demanded,
/// but not on every observation, so moving its evaluation to the
/// construction would evaluate it on the path that only forces the box.
#[test]
fn a_field_demanded_on_one_observation_only_is_deferred() {
    // let r = Foo (g a) in h (seq r ()) (case r of Foo x -> k x)
    let m = top_module(
        let1(
            "r",
            con_app("Foo", &[app(var("g"), var("a"))]),
            app(
                app(var("h"), case_force(var("r"), "seqw", var("u"))),
                case_alts(var("r"), &[("Foo", vec!["x"], app(var("k"), var("x")))]),
            ),
        ),
        json!({"Foo": prog_con("Foo", 1), "g": callee(true), "k": callee(true)}),
    );
    let f = field_census(&m);
    let flow = one_con_flow(&f, "Foo");
    let v = &flow.verdicts[0];
    assert_eq!(v.demand, FieldDemand::Conditional);
    assert_eq!(v.rep, FieldRep::Deferred);
    assert_eq!(v.reason, Some(crate::fields::R_WHNF_WITHOUT_FIELD));
}

/// `case Foo (g a) of Foo x -> k x` with `k` strict: the field is demanded
/// on every observation *and* the force stands at the construction's own
/// evaluation frontier — no return, no lambda, no conditional in between —
/// so evaluating it eagerly changes no timing.
#[test]
fn a_field_demanded_at_the_construction_s_own_frontier_is_direct() {
    let m = top_module(
        case_alts(
            con_app("Foo", &[app(var("g"), var("a"))]),
            &[("Foo", vec!["x"], app(var("k"), var("x")))],
        ),
        json!({"Foo": prog_con("Foo", 1), "g": callee(true), "k": callee(true)}),
    );
    let f = field_census(&m);
    let flow = one_con_flow(&f, "Foo");
    let v = &flow.verdicts[0];
    assert_eq!(v.demand, FieldDemand::Always);
    assert_eq!(v.rep, FieldRep::Direct);
    assert_eq!(v.rule, crate::fields::R3_SAME_FRONTIER);
}

/// …and the same demand behind a lambda is not, because the field would be
/// evaluated when the closure is built rather than when it is entered.
#[test]
fn the_same_demand_behind_a_lambda_is_not_direct() {
    let m = top_module(
        let1(
            "r",
            con_app("Foo", &[app(var("g"), var("a"))]),
            lam(
                &["y"],
                case_alts(var("r"), &[("Foo", vec!["x"], app(var("k"), var("x")))]),
            ),
        ),
        json!({"Foo": prog_con("Foo", 1), "g": callee(true), "k": callee(true)}),
    );
    let f = field_census(&m);
    let v = &one_con_flow(&f, "Foo").verdicts[0];
    assert_eq!(v.demand, FieldDemand::Always);
    assert_eq!(v.rep, FieldRep::Deferred);
    assert_eq!(v.reason, Some(crate::fields::R_TIMING_NOT_PRESERVED));
}

/// A GHC-strict field is forced when the constructor is built, whatever
/// anyone does with it later: Direct on GHC's own evidence.
#[test]
fn a_ghc_strict_field_is_direct_by_ghc_s_evidence() {
    let m = top_module(
        let1(
            "r",
            con_app("Bang", &[app(var("g"), var("a"))]),
            app(var("imported"), var("r")),
        ),
        json!({"Bang": prog_con_strict("Bang", 1), "g": callee(true), "imported": callee(false)}),
    );
    let f = field_census(&m);
    let v = &one_con_flow(&f, "Bang").verdicts[0];
    assert_eq!(v.strictness, ConStrictness::StrictField);
    assert_eq!(v.rep, FieldRep::Direct);
    assert_eq!(v.rule, crate::fields::R1_STRICT_FIELD);
    // Nothing reads it, but it is not Dead: reaching WHNF forces it.
    assert_eq!(v.demand, FieldDemand::Unknown);
    let m2 = top_module(
        let1(
            "r",
            con_app("Bang", &[app(var("g"), var("a"))]),
            case_force(var("r"), "seqw", var("u")),
        ),
        json!({"Bang": prog_con_strict("Bang", 1), "g": callee(true)}),
    );
    let f2 = field_census(&m2);
    let v2 = &one_con_flow(&f2, "Bang").verdicts[0];
    assert_eq!(v2.demand, FieldDemand::Never);
    assert!(v2.force_on_whnf, "a strict field nobody reads is not Dead");
    assert_eq!(v2.rep, FieldRep::Direct);
}

/// A construction stored in a field of *another* construction, which is
/// then taken apart: the flow continues through the outer's field binder.
#[test]
fn a_construction_stored_in_another_one_is_followed_through_it() {
    // let i = Foo (g a) in
    // let o = Box i in case o of Box b -> case b of Foo x -> k x
    let m = top_module(
        let1(
            "i",
            con_app("Foo", &[app(var("g"), var("a"))]),
            let1(
                "o",
                con_app("Box", &[var("i")]),
                case_alts(
                    var("o"),
                    &[(
                        "Box",
                        vec!["b"],
                        case_alts(var("b"), &[("Foo", vec!["x"], app(var("k"), var("x")))]),
                    )],
                ),
            ),
        ),
        json!({
            "Foo": prog_con("Foo", 1), "Box": prog_con("Box", 1),
            "g": callee(true), "k": callee(true)
        }),
    );
    let f = field_census(&m);
    let inner = one_con_flow(&f, "Foo");
    assert!(
        inner
            .evidence
            .iter()
            .any(|e| e.rule == crate::fields::D8_NESTED),
        "{:?}",
        inner.evidence.iter().map(|e| e.rule).collect::<Vec<_>>()
    );
    assert!(!inner.escaped(), "{:?}", inner.escapes);
    assert_eq!(inner.verdicts[0].demand, FieldDemand::Always);
}

/// A knot: `let rec r = Foo r in …`. The recursion verdict is M1's — the
/// binding is a non-function member of a recursive group that refers to
/// itself — and this only says which field carries the reference.
#[test]
fn a_field_that_refers_back_to_its_own_binding_is_recursive() {
    let m = top_module(
        letrec1(
            "r",
            con_app("Foo", &[var("r")]),
            case_alts(var("r"), &[("Foo", vec!["x"], app(var("k"), var("x")))]),
        ),
        json!({"Foo": prog_con("Foo", 1), "k": callee(true)}),
    );
    let census = Census::raw([&m]);
    assert!(
        census
            .bindings
            .iter()
            .any(|b| b.occ == "r" && b.class == Class::RecursiveValue),
        "M1 must call this binding a recursive value"
    );
    let f = Fields::of_module(&m, &census);
    let v = &one_con_flow(&f, "Foo").verdicts[0];
    assert_eq!(v.recursion, ValueRecursion::RecursiveKnot);
    assert_eq!(v.rep, FieldRep::Recursive);
    assert_eq!(v.rule, crate::fields::R6_RECURSIVE);
}

/// Handed to an imported function: what is demanded of the field is not in
/// this module, and the verdict says so rather than guessing.
#[test]
fn a_construction_passed_to_an_import_is_unknown_with_a_reason() {
    let m = top_module(
        let1(
            "r",
            con_app("Foo", &[app(var("g"), var("a"))]),
            app(var("imported"), var("r")),
        ),
        json!({"Foo": prog_con("Foo", 1), "g": callee(true), "imported": callee(false)}),
    );
    let f = field_census(&m);
    let flow = one_con_flow(&f, "Foo");
    let v = &flow.verdicts[0];
    assert_eq!(v.demand, FieldDemand::Unknown);
    assert_eq!(v.rep, FieldRep::Unknown);
    assert_eq!(v.reason, Some(crate::flow::R_IMPORTED_LAZY));
}

/// A sum type scrutinised by a case with one alternative per constructor:
/// for each construction the alternative that names *its* constructor is
/// the scrutiny, and the other two are unreachable for that value.
#[test]
fn a_sum_type_case_selects_the_alternative_for_each_construction() {
    // let a = A (g p) in let b = B (g q) in
    // h (case a of {A x -> k x; B y -> u; C z -> u})
    //   (case b of {A x -> u; B y -> k y; C z -> u})
    let scrut = |v: &str, which: usize| {
        let mk = |i: usize, b: &str| {
            if i == which {
                app(var("k"), var(b))
            } else {
                var("u")
            }
        };
        case_alts(
            var(v),
            &[
                ("A", vec!["x"], mk(0, "x")),
                ("B", vec!["y"], mk(1, "y")),
                ("C", vec!["z"], mk(2, "z")),
            ],
        )
    };
    let m = top_module(
        let1(
            "a",
            con_app("A", &[app(var("g"), var("p"))]),
            let1(
                "b",
                con_app("B", &[app(var("g"), var("q"))]),
                app(app(var("h"), scrut("a", 0)), scrut("b", 1)),
            ),
        ),
        json!({
            "A": prog_con("A", 1), "B": prog_con("B", 1), "C": prog_con("C", 1),
            "g": callee(true), "k": callee(true)
        }),
    );
    let f = field_census(&m);
    for (occ, want) in [("A", FieldDemand::Always), ("B", FieldDemand::Always)] {
        let flow = one_con_flow(&f, occ);
        // Two cases are reached; only one of them names this constructor
        // with a used binder, the other selects this constructor's own
        // alternative and drops the field.
        assert!(!flow.escaped(), "{occ}: {:?}", flow.escapes);
        assert_eq!(
            flow.unreachable_alts, 2,
            "{occ}: one case reached, 2 dead alts"
        );
        assert!(
            flow.verdicts[0].demand == want || flow.verdicts[0].demand == FieldDemand::Conditional
        );
    }
}

/// A `DEFAULT` alternative is an observation of the constructor to WHNF
/// that binds no field of it — not an escape and not a read.
#[test]
fn a_default_alternative_is_a_whnf_observation() {
    let m = top_module(
        let1(
            "r",
            con_app("C", &[app(var("g"), var("a"))]),
            case_alts(
                var("r"),
                &[
                    ("A", vec!["x"], app(var("k"), var("x"))),
                    ("DEFAULT", vec![], var("u")),
                ],
            ),
        ),
        json!({"C": prog_con("C", 1), "A": prog_con("A", 1), "g": callee(true), "k": callee(true)}),
    );
    let f = field_census(&m);
    let flow = one_con_flow(&f, "C");
    assert!(!flow.escaped(), "{:?}", flow.escapes);
    let whnf: Vec<_> = flow
        .observations
        .iter()
        .filter(|o| o.kind == ObsKind::WhnfOnly)
        .collect();
    assert_eq!(whnf.len(), 1);
    assert_eq!(whnf[0].whnf, Some(crate::flow::WhnfHow::DefaultAlt));
    assert_eq!(flow.verdicts[0].demand, FieldDemand::Never);
}

/// The case *binder* is in scope in every alternative but only the selected
/// one runs. `case v of { C x -> k x; D y -> store v }` for a known `C`:
/// the store under `D` is unreachable for this value and must not make the
/// flow escape.
#[test]
fn an_alias_under_an_unreachable_alternative_is_not_an_escape() {
    let m = top_module(
        let1(
            "r",
            con_app("C", &[app(var("g"), var("a"))]),
            case_alts(
                var("r"),
                &[
                    ("C", vec!["x"], app(var("k"), var("x"))),
                    ("D", vec!["y"], con_app("Box", &[var("wild")])),
                ],
            ),
        ),
        json!({
            "C": prog_con("C", 1), "D": prog_con("D", 1), "Box": prog_con("Box", 1),
            "g": callee(true), "k": callee(true)
        }),
    );
    let f = field_census(&m);
    let flow = one_con_flow(&f, "C");
    assert!(
        !flow.escaped(),
        "the store under D is unreachable: {:?}",
        flow.escapes
    );
    assert_eq!(flow.alias_occurrences_unreachable, 1);
    assert_eq!(flow.unreachable_alts, 1);
    assert_eq!(
        flow.observations
            .iter()
            .filter(|o| o.kind != ObsKind::Escape)
            .count(),
        1
    );
    let v = &flow.verdicts[0];
    assert_eq!(v.demand, FieldDemand::Always);
    assert_eq!(v.recursion, ValueRecursion::Acyclic);
}

/// The whole census closes: every field in exactly one rep, every
/// construction in exactly one observation bucket, every census site mapped
/// or explained.
#[test]
fn the_field_accounting_closes() {
    let m = top_module(
        let1(
            "r",
            con_app("Foo", &[app(var("g"), var("a"))]),
            case_alts(var("r"), &[("Foo", vec!["x"], app(var("k"), var("x")))]),
        ),
        json!({"Foo": prog_con("Foo", 1), "g": callee(true), "k": callee(true)}),
    );
    let modules = [&m];
    let census = Census::raw(modules.iter().copied());
    let fc = crate::fields::FieldCensus::of_modules(&modules, &census);
    fc.accounting.check();
    assert_eq!(fc.accounting.constructions, 1);
    assert_eq!(fc.accounting.fields_total, 1);
    assert_eq!(fc.con_fields.len(), 1);
    assert_eq!(fc.con_fields[0].rep, FieldRep::Direct);
}

//------------------------------------------------------------------------------
// Lists: when, and how much, of a spine is demanded (lists.rs)
//------------------------------------------------------------------------------

use crate::lists::axioms::{CallbackKind, HeadExposure, ListKind, Produces};
use crate::lists::{
    ConsumerKind, Lists, PrefixBound, Recommendation, Recursion, Reuse, SpineDemand, Storage,
    TailFate,
};

/// A global `Var` whose GHC stable name differs from its occurrence name:
/// the axiom table is keyed on the stable name, and nothing else.
fn gvar_named(occ: &str, name: &str) -> Value {
    json!({"node": "Var", "name": name, "occ": occ, "unique": occ, "isGlobal": true})
}

fn cons_cell(h: Value, t: Value) -> Value {
    app(app(gvar(":"), h), t)
}

fn nil() -> Value {
    gvar("[]")
}

/// An imported non-constructor id, keyed in the table by its unique (which
/// these fixtures make equal to the occurrence name).
fn import_fn(occ: &str, arity: u32) -> Value {
    let args: Vec<Value> = (0..arity).map(|_| demand(false, false)).collect();
    json!({
        "name": occ, "occ": occ, "arity": arity,
        "dmdSig": {"args": args, "diverges": false, "pretty": ""},
        "isJoinPoint": false, "dataCon": null
    })
}

fn int_lit(n: u64) -> Value {
    json!({"node": "Lit", "lit": {"kind": "Int", "pretty": n.to_string()}})
}

/// The list constructors, plus whatever else the fixture needs.
fn list_ids(extra: Value) -> Value {
    let mut ids = json!({
        ":": data_con(":", "$ghc-prim$GHC.Types$:", 2),
        "[]": data_con("[]", "$ghc-prim$GHC.Types$[]", 0),
    });
    if let Value::Object(o) = extra {
        for (k, v) in o {
            ids[k] = v;
        }
    }
    ids
}

/// `case <scrut> of { [] -> nil_rhs; (y:ys) -> cons_rhs }`, with the list
/// constructors named exactly as GHC names them — which is what makes the
/// walk's constructor-relative alternative selection pick the right one.
fn list_case(scrut: Value, nil_rhs: Value, binders: &[&str], cons_rhs: Value) -> Value {
    json!({
        "node": "Case", "scrut": scrut,
        "binder": binder("wild", demand(false, false)), "type": "R", "ty": TY_R,
        "alts": [
            {"con": {"kind": "DataAlt", "name": "$ghc-prim$GHC.Types$[]", "occ": "[]", "tag": 1},
             "binders": [], "rhs": nil_rhs},
            {"con": {"kind": "DataAlt", "name": "$ghc-prim$GHC.Types$:", "occ": ":", "tag": 1},
             "binders": binders.iter().map(|b| binder(b, demand(false, false)))
                 .collect::<Vec<_>>(),
             "rhs": cons_rhs}
        ]
    })
}

fn list_census(m: &Module) -> Lists<'_> {
    let census = Census::raw([m]);
    let reads = crate::fields::Fields::of_module(m, &census).field_reads();
    Lists::of_module(m, &census, &reads)
}

fn cons_flow<'a>(l: &'a Lists<'a>, n: usize) -> &'a crate::lists::ListFlow {
    let all: Vec<&crate::lists::ListFlow> = l
        .flows
        .iter()
        .filter(|f| f.kind == crate::lists::ProducerKind::ConsChain)
        .collect();
    assert!(
        all.len() > n,
        "expected more than {n} cons flow(s), got {}",
        all.len()
    );
    all[n]
}

/// `let rec go = \ds -> case ds of { [] -> u; (y:ys) -> k (go ys) }` with
/// `k` strict: every cell is reached before the consumer returns, and the
/// spine is entered once.
#[test]
fn a_cons_chain_walked_by_a_recursive_consumer_demands_the_whole_spine() {
    let loop_body = list_case(
        var("ds"),
        var("u"),
        &["y", "ys"],
        app(var("k"), app(var("go"), var("ys"))),
    );
    let m = top_module(
        letrec1(
            "go",
            lam(&["ds"], loop_body),
            let1("xs", cons_cell(var("a"), nil()), app(var("go"), var("xs"))),
        ),
        list_ids(json!({"k": callee(true)})),
    );
    let l = list_census(&m);
    let f = cons_flow(&l, 0);
    assert_eq!(f.spine, SpineDemand::Whole, "{:?}", f.consumers);
    assert_eq!(
        f.head,
        crate::lists::HeadDemand::None,
        "the element is never forced"
    );
    assert_eq!(f.reuse, Reuse::SinglePass);
    assert_eq!(f.storage, Storage::NotStored);
    assert_eq!(f.recursion, Recursion::FiniteProducer);
    assert!(f.short_circuit.no());
    assert!(
        f.consumers.iter().any(|c| matches!(
            c.kind,
            ConsumerKind::ConsAlt {
                tail: TailFate::Loop { .. },
                ..
            }
        )),
        "the tail alias must close the loop back onto the same case: {:?}",
        f.consumers
    );
}

/// The same loop with the recursive call inside a constructor field is a
/// `map`, not a `length`: one cell is reached per cell the *consumer* asks
/// for, so the spine is `Incremental` and calling it `Whole` would be a
/// lie.
#[test]
fn a_recursive_consumer_that_conses_its_result_is_incremental_not_whole() {
    let loop_body = list_case(
        var("ds"),
        nil(),
        &["y", "ys"],
        cons_cell(var("y"), app(var("go"), var("ys"))),
    );
    let m = top_module(
        letrec1(
            "go",
            lam(&["ds"], loop_body),
            let1("xs", cons_cell(var("a"), nil()), app(var("go"), var("xs"))),
        ),
        list_ids(json!({})),
    );
    let l = list_census(&m);
    let f = cons_flow(&l, 0);
    assert_eq!(f.spine, SpineDemand::Incremental, "{:?}", f.consumers);
    assert!(f.consumers.iter().any(|c| matches!(
        c.kind,
        ConsumerKind::ConsAlt {
            tail: TailFate::LoopIncremental { .. },
            ..
        }
    )));
}

/// `take 1 (x : expensive)`: a bounded prefix, read off the literal, and
/// nothing demands what comes after the first cell.
#[test]
fn take_with_a_literal_count_bounds_the_prefix() {
    let m = top_module(
        let1(
            "xs",
            cons_cell(var("x"), app(var("expensive"), var("a"))),
            app(
                app(gvar_named("take", "$base$GHC.List$take"), int_lit(1)),
                var("xs"),
            ),
        ),
        list_ids(json!({"take": import_fn("take", 2), "expensive": callee(false)})),
    );
    let l = list_census(&m);
    let f = cons_flow(&l, 0);
    assert_eq!(
        f.spine,
        SpineDemand::Prefix(PrefixBound::Known(1)),
        "{:?}",
        f.consumers
    );
    assert_eq!(f.head, crate::lists::HeadDemand::None);
    assert!(
        f.consumers
            .iter()
            .any(|c| matches!(&c.kind, ConsumerKind::Axiom { rule, .. } if *rule == "L-AX-TAKE"))
    );
}

/// `find p xs`: a data-dependent prefix, and a consumer that may stop
/// before the end.
#[test]
fn find_demands_a_data_dependent_prefix_and_short_circuits() {
    let m = top_module(
        let1(
            "xs",
            cons_cell(var("x"), nil()),
            app(
                app(gvar_named("find", "$base$Data.Foldable$find"), var("p")),
                var("xs"),
            ),
        ),
        list_ids(json!({"find": import_fn("find", 2)})),
    );
    let l = list_census(&m);
    let f = cons_flow(&l, 0);
    assert_eq!(f.spine, SpineDemand::Prefix(PrefixBound::DataDependent));
    assert!(!f.short_circuit.no(), "find may stop at the first match");
    // **M2.3g.** `find` hands each element it reaches to an arbitrary
    // predicate, and `find (const True)` forces nothing: the elements are
    // exposed, not forced.
    assert_eq!(f.head, crate::lists::HeadDemand::None);
    assert_eq!(
        f.head_exposure,
        HeadExposure::PassedToCallback(CallbackKind::Predicate)
    );
}

/// Two consumers of one binder are two traversals of one spine.
#[test]
fn two_consumers_of_one_binder_are_two_passes() {
    let len = |v: &str| app(gvar_named("length", "$base$GHC.List$length"), var(v));
    let m = top_module(
        let1(
            "xs",
            cons_cell(var("x"), nil()),
            app(app(var("h"), len("xs")), len("xs")),
        ),
        list_ids(json!({"length": import_fn("length", 1), "h": callee(true)})),
    );
    let l = list_census(&m);
    let f = cons_flow(&l, 0);
    assert_eq!(f.spine, SpineDemand::Whole);
    assert_eq!(f.traversals, 2, "{:?}", f.consumers);
    assert_eq!(f.reuse, Reuse::MultiPass(2));
}

/// A `(y:ys)` alternative that stores the tail while the spine is also
/// consumed elsewhere: the tail survives in two places.
#[test]
fn a_stored_tail_alias_is_a_shared_tail() {
    let m = top_module(
        let1(
            "xs",
            cons_cell(var("x"), nil()),
            app(
                app(
                    var("h"),
                    app(gvar_named("length", "$base$GHC.List$length"), var("xs")),
                ),
                list_case(
                    var("xs"),
                    var("u"),
                    &["y", "ys"],
                    con_app("Box", &[var("ys")]),
                ),
            ),
        ),
        list_ids(json!({
            "length": import_fn("length", 1), "h": callee(true),
            "Box": prog_con("Box", 1)
        })),
    );
    let l = list_census(&m);
    let f = cons_flow(&l, 0);
    assert!(
        matches!(f.reuse, Reuse::SharedTail { .. }),
        "reuse was {:?} with consumers {:?}",
        f.reuse,
        f.consumers
    );
    // **M2.3g.** The shared tail is a *constraint* whatever else is true.
    // Whether it is also the recommendation depends on every other fact
    // being known.
    assert!(f.constraints.tail_sharing);
    assert_eq!(
        f.rec,
        if f.spine == SpineDemand::Unknown
            || f.head == crate::lists::HeadDemand::Unknown
            || matches!(f.reuse, Reuse::Escapes(_))
        {
            Recommendation::Unknown
        } else {
            Recommendation::PersistentCandidate
        },
        "facts: spine {:?} head {:?} reuse {:?}",
        f.spine,
        f.head,
        f.reuse
    );
}

/// `let rec r = a : r`: a value knot, and the verdict is M1's — asserted
/// here first, so that a change in M1 breaks this test rather than
/// silently changing the answer.
#[test]
fn a_self_referential_cons_is_a_recursive_knot() {
    let m = top_module(
        letrec1(
            "r",
            cons_cell(var("a"), var("r")),
            list_case(var("r"), var("u"), &["y", "ys"], app(var("k"), var("y"))),
        ),
        list_ids(json!({"k": callee(true)})),
    );
    let census = Census::raw([&m]);
    assert!(
        census
            .bindings
            .iter()
            .any(|b| b.occ == "r" && b.class == Class::RecursiveValue),
        "M1 must call this binding a recursive value first"
    );
    let reads = crate::fields::Fields::of_module(&m, &census).field_reads();
    let l = Lists::of_module(&m, &census, &reads);
    let f = cons_flow(&l, 0);
    assert_eq!(f.recursion, Recursion::RecursiveKnot);
    assert_eq!(f.rec, Recommendation::LazyCandidate);
}

/// A recursive *function* that builds a finite list is not a knot: M1 does
/// not call it a recursive value, and neither does this.
#[test]
fn a_recursive_function_building_a_list_is_a_finite_producer() {
    let m = top_module(
        letrec1(
            "f",
            lam(
                &["n"],
                case_alts(
                    var("n"),
                    &[
                        ("Z", vec![], nil()),
                        ("S", vec!["p"], cons_cell(var("p"), app(var("f"), var("p")))),
                    ],
                ),
            ),
            app(var("f"), var("n0")),
        ),
        list_ids(json!({"Z": prog_con("Z", 0), "S": prog_con("S", 1)})),
    );
    let census = Census::raw([&m]);
    assert!(
        !census
            .bindings
            .iter()
            .any(|b| b.occ == "f" && b.class == Class::RecursiveValue),
        "M1 must not call a recursive function a recursive value"
    );
    let reads = crate::fields::Fields::of_module(&m, &census).field_reads();
    let l = Lists::of_module(&m, &census, &reads);
    for f in &l.flows {
        assert_eq!(f.recursion, Recursion::FiniteProducer);
    }
}

/// A list stored in a program ADT that nothing takes apart: the spine
/// outlives every consumer this module can see.
#[test]
fn a_list_stored_in_an_adt_is_stored() {
    let m = top_module(
        let1(
            "xs",
            cons_cell(var("x"), nil()),
            con_app("Box", &[var("xs")]),
        ),
        list_ids(json!({"Box": prog_con("Box", 1)})),
    );
    let l = list_census(&m);
    let f = cons_flow(&l, 0);
    assert_eq!(f.storage, Storage::StoredIn("Box".into()));
    assert!(
        f.consumers
            .iter()
            .any(|c| matches!(c.kind, ConsumerKind::StoredIn { .. }))
    );
}

/// Handed to a higher-order parameter: nothing is claimed, and the reason
/// says which rule refused.
#[test]
fn a_list_through_a_higher_order_parameter_is_unknown_with_a_reason() {
    let m = top_module(
        lam(
            &["f"],
            let1("xs", cons_cell(var("x"), nil()), app(var("f"), var("xs"))),
        ),
        list_ids(json!({})),
    );
    let l = list_census(&m);
    let f = cons_flow(&l, 0);
    assert_eq!(f.spine, SpineDemand::Unknown);
    assert_eq!(f.rec, Recommendation::Unknown);
    assert_eq!(
        f.rec_reason.as_deref(),
        Some(crate::flow::R_HIGHER_ORDER),
        "{:?}",
        f.consumers
    );
}

/// `foldl'` reaches every cell and is still a streaming consumer: the
/// advisory verdict is an iterator, **not** a `Vec`. "The whole spine is
/// eventually consumed" does not mean the whole spine has to exist.
#[test]
fn foldl_strict_over_a_whole_list_is_an_iterator_not_a_vec() {
    let m = top_module(
        let1(
            "xs",
            cons_cell(var("x"), nil()),
            app(
                app(
                    app(gvar_named("foldl'", "$base$GHC.List$foldl'"), var("k")),
                    var("z"),
                ),
                var("xs"),
            ),
        ),
        list_ids(json!({"foldl'": import_fn("foldl'", 3)})),
    );
    let l = list_census(&m);
    let f = cons_flow(&l, 0);
    assert_eq!(f.spine, SpineDemand::Whole);
    assert!(f.streaming, "foldl' retains nothing");
    assert_eq!(f.reuse, Reuse::SinglePass);
    assert_eq!(f.rec, Recommendation::IteratorCandidate);
    assert_ne!(f.rec, Recommendation::VecCandidate);
}

/// `xs ++ ys`: the left spine is copied one cell at a time, and the right
/// one is not walked at all — it *becomes* the result's tail, which is a
/// shared tail.
#[test]
fn append_is_incremental_on_the_left_and_aliases_on_the_right() {
    let m = top_module(
        let1(
            "xs",
            cons_cell(var("x"), nil()),
            let1(
                "ys",
                cons_cell(var("y"), nil()),
                app(
                    app(gvar_named("++", "$base$GHC.Base$++"), var("xs")),
                    var("ys"),
                ),
            ),
        ),
        list_ids(json!({"++": import_fn("++", 2)})),
    );
    let l = list_census(&m);
    let left = cons_flow(&l, 0);
    let right = cons_flow(&l, 1);
    assert_eq!(left.spine, SpineDemand::Incremental, "{:?}", left.consumers);
    assert_eq!(right.spine, SpineDemand::None, "{:?}", right.consumers);
    assert!(
        matches!(right.reuse, Reuse::SharedTail { .. }),
        "the right argument is the result's own tail: {:?}",
        right.reuse
    );
    assert!(left.consumers.iter().all(|c| !c.aliases));
}

/// An imported head with no table entry: the flow is `Unknown` and names
/// the head, so the residual says exactly which axiom is missing.
#[test]
fn an_imported_head_without_an_axiom_is_unknown_and_names_it() {
    let m = top_module(
        let1(
            "xs",
            cons_cell(var("x"), nil()),
            app(
                gvar_named("mysteryFn", "$somelib$Some.Module$mysteryFn"),
                var("xs"),
            ),
        ),
        list_ids(json!({"mysteryFn": import_fn("mysteryFn", 1)})),
    );
    let l = list_census(&m);
    let f = cons_flow(&l, 0);
    assert_eq!(f.spine, SpineDemand::Unknown);
    assert_eq!(
        f.rec_reason.as_deref(),
        Some("no-axiom-for($somelib$Some.Module$mysteryFn)")
    );
    assert!(f.consumers.iter().any(
        |c| matches!(&c.kind, ConsumerKind::NoAxiom { name, in_table }
                     if name == "$somelib$Some.Module$mysteryFn" && !*in_table)
    ));
}

/// **A program function is never looked up in the axiom table.** A local
/// `map` with the same occurrence name is followed by def-use, and an
/// imported one from the program's own package gets no axiom at all.
#[test]
fn the_axiom_table_is_never_applied_to_a_program_function() {
    let m = top_module(
        let1(
            "xs",
            cons_cell(var("x"), nil()),
            app(gvar_named("map", "$main$ShellCheck.Mine$map"), var("xs")),
        ),
        list_ids(json!({"map": import_fn("map", 1)})),
    );
    let l = list_census(&m);
    let f = cons_flow(&l, 0);
    assert_eq!(f.spine, SpineDemand::Unknown);
    assert_eq!(
        f.rec_reason.as_deref(),
        Some("no-axiom-for($main$ShellCheck.Mine$map)"),
        "an occurrence name of `map` must not reach GHC.Base's axiom"
    );
}

/// A chain of conses built by one producer is **one** flow of many cells,
/// and the `[]` that terminates it is a cell of it rather than a flow of
/// its own.
#[test]
fn a_cons_chain_is_one_flow() {
    let m = top_module(
        let1(
            "xs",
            cons_cell(var("a"), cons_cell(var("b"), cons_cell(var("c"), nil()))),
            app(gvar_named("length", "$base$GHC.List$length"), var("xs")),
        ),
        list_ids(json!({"length": import_fn("length", 1)})),
    );
    let l = list_census(&m);
    assert_eq!(l.flows.len(), 1, "one producer, one flow");
    let f = &l.flows[0];
    assert_eq!(f.cells.len(), 3);
    assert!(f.nil_terminated);
    assert_eq!(f.spine, SpineDemand::Whole);
}

/// A spine consed onto as the tail of another cell is not stored: it
/// continues into that cell's flow, and the successor's demand comes back.
#[test]
fn a_spine_consed_onto_another_cell_inherits_that_flow_s_demand() {
    // let inner = a : [] in let outer = b : inner in length outer
    let m = top_module(
        let1(
            "inner",
            cons_cell(var("a"), nil()),
            let1(
                "outer",
                cons_cell(var("b"), var("inner")),
                app(gvar_named("length", "$base$GHC.List$length"), var("outer")),
            ),
        ),
        list_ids(json!({"length": import_fn("length", 1)})),
    );
    let l = list_census(&m);
    assert_eq!(l.flows.len(), 2);
    let inner = l
        .flows
        .iter()
        .find(|f| f.bound.is_some_and(|b| m.binder(b).occ == "inner"))
        .unwrap();
    assert!(
        inner
            .consumers
            .iter()
            .any(|c| matches!(c.kind, ConsumerKind::ConsedAsTail { .. })),
        "{:?}",
        inner.consumers
    );
    assert_eq!(
        inner.storage,
        Storage::NotStored,
        "a tail slot is not storage"
    );
    assert_eq!(
        inner.spine,
        SpineDemand::Whole,
        "the successor's whole-spine demand reaches this flow"
    );
}

//------------------------------------------------------------------------------
// M2.3g — the corrected axiom layer
//------------------------------------------------------------------------------

/// Build `let xs = x : [] in <call>` around a single cons flow.
fn one_list_into(call: Value, ids: Value) -> Module {
    top_module(let1("xs", cons_cell(var("x"), nil()), call), list_ids(ids))
}

/// **A call that returns a PAIR of lists is not a list.** `span` returns
/// `([a],[a])`: the call node's type is a tuple, so it starts no flow —
/// the pair does. The demand and aliasing facts it puts on its *argument*
/// are unaffected, and the second component being a suffix of the input
/// still makes the input's tail shared.
#[test]
fn a_pair_returning_head_is_not_a_list_producer() {
    let m = one_list_into(
        app(
            app(gvar_named("span", "$base$GHC.List$span"), var("p")),
            var("xs"),
        ),
        json!({"span": import_fn("span", 2)}),
    );
    let l = list_census(&m);
    assert!(
        l.flows
            .iter()
            .all(|f| f.kind != crate::lists::ProducerKind::ImportedCall),
        "span returns a pair: {:?}",
        l.flows.iter().map(|f| f.kind).collect::<Vec<_>>()
    );
    let f = cons_flow(&l, 0);
    assert_eq!(f.spine, SpineDemand::Prefix(PrefixBound::DataDependent));
    assert!(
        matches!(f.reuse, Reuse::SharedTail { .. }),
        "the second component is a suffix of the argument: {:?}",
        f.reuse
    );
    assert!(f.constraints.tail_sharing);
}

/// The same for `unzip :: [(a,b)] -> ([a],[b])` and for `traverse`, whose
/// result is `f [b]` — an action, not a list.
#[test]
fn a_product_or_effect_returning_head_is_not_a_list_producer() {
    for (occ, name, args) in [
        ("unzip", "$base$GHC.List$unzip", 1u32),
        ("traverse", "$base$Data.Traversable$traverse", 2),
    ] {
        let call = if args == 1 {
            app(gvar_named(occ, name), var("xs"))
        } else {
            app(app(gvar_named(occ, name), var("k")), var("xs"))
        };
        let m = one_list_into(call, json!({occ: import_fn(occ, args)}));
        let l = list_census(&m);
        assert!(
            l.flows
                .iter()
                .all(|f| f.kind != crate::lists::ProducerKind::ImportedCall),
            "{occ} does not return a list"
        );
        let ax = crate::lists::axioms::axiom(name).unwrap();
        assert!(!ax.produces.is_direct_list(), "{occ}");
    }
}

/// Every entry that says it returns a list says so of its **outer** return
/// type, and every entry whose result merely contains one produces no
/// flow. Read off the table so that a future entry cannot quietly
/// reintroduce the M2.3g population bug.
#[test]
fn only_a_direct_list_result_can_be_a_producer() {
    for a in crate::lists::axioms::all() {
        match a.produces {
            Produces::DirectList(_) => {}
            p => assert!(
                !p.is_direct_list(),
                "{}: {} must not start a flow",
                a.name,
                p.name()
            ),
        }
    }
    // The four heads the audit moved off `DirectList`, named explicitly.
    for name in [
        "$base$GHC.List$span",
        "$base$GHC.List$$wspan",
        "$base$GHC.List$splitAt",
        "$ghc-prim$GHC.Magic$lazy",
    ] {
        let a = crate::lists::axioms::axiom(name).unwrap();
        assert!(!a.produces.is_direct_list(), "{name}");
    }
}

/// **`cycle` consumes its argument incrementally and replays it.** Calling
/// the demand `Whole` said that the call walks to the end of the spine
/// before returning, which on an infinite argument never happens.
#[test]
fn cycle_is_incremental_and_replayed_never_whole() {
    let m = one_list_into(
        app(gvar_named("cycle", "$base$GHC.List$cycle"), var("xs")),
        json!({"cycle": import_fn("cycle", 1)}),
    );
    let l = list_census(&m);
    let f = cons_flow(&l, 0);
    assert_eq!(f.spine, SpineDemand::Incremental, "{:?}", f.consumers);
    assert_ne!(f.spine, SpineDemand::Whole);
    assert!(
        matches!(f.reuse, Reuse::Replayed { .. }),
        "reuse was {:?}",
        f.reuse
    );
    assert!(f.constraints.replay);
    assert_eq!(f.rec, Recommendation::PersistentCandidate);
    let ax = crate::lists::axioms::axiom("$base$GHC.List$cycle").unwrap();
    assert_eq!(ax.produces, Produces::DirectList(ListKind::Unbounded));
    assert!(!ax.streaming, "it retains the argument");
}

/// **`isInfixOf`'s needle is replayed**, not walked whole: it is retried as
/// a prefix at successive positions of the haystack.
#[test]
fn the_needle_of_is_infix_of_is_replayed() {
    let m = top_module(
        let1(
            "needle",
            cons_cell(var("a"), nil()),
            let1(
                "hay",
                cons_cell(var("b"), nil()),
                app(
                    app(
                        gvar_named("isInfixOf", "$base$Data.OldList$isInfixOf"),
                        var("needle"),
                    ),
                    var("hay"),
                ),
            ),
        ),
        list_ids(json!({"isInfixOf": import_fn("isInfixOf", 2)})),
    );
    let l = list_census(&m);
    let needle = cons_flow(&l, 0);
    assert_eq!(
        needle.spine,
        SpineDemand::Prefix(PrefixBound::DataDependent),
        "{:?}",
        needle.consumers
    );
    assert_ne!(needle.spine, SpineDemand::Whole);
    assert!(
        matches!(needle.reuse, Reuse::Replayed { .. }),
        "{:?}",
        needle.reuse
    );
    assert!(needle.consumers.iter().any(|c| c.replays));
}

/// **`concat` shares nothing.** `concat = foldr (++) []` makes every inner
/// list the LEFT operand of `(++)`, which copies it — even the last one,
/// `xs ++ []`. So neither the `[[a]]` spine nor any inner `[a]` survives
/// in the result, and the table must claim neither.
#[test]
fn concat_shares_neither_the_outer_spine_nor_an_element() {
    let ax = crate::lists::axioms::axiom("$base$GHC.List$concat").unwrap();
    assert_eq!(ax.alias, crate::lists::axioms::Alias::NoAlias);
    assert!(!ax.aliases_spine(0, 1));
    assert!(!ax.aliases_element(0, 1));
    let m = one_list_into(
        app(gvar_named("concat", "$base$GHC.List$concat"), var("xs")),
        json!({"concat": import_fn("concat", 1)}),
    );
    let l = list_census(&m);
    let f = cons_flow(&l, 0);
    assert!(
        !matches!(f.reuse, Reuse::SharedTail { .. }),
        "concat copies: {:?}",
        f.reuse
    );
    assert!(!f.constraints.tail_sharing);
}

/// `head :: [[a]] -> [a]` is where element sharing is real: the result
/// **is** one of the elements. That puts nothing on the argument's own
/// spine, which is the whole point of the separate variant.
#[test]
fn an_element_alias_is_not_a_shared_tail() {
    let ax = crate::lists::axioms::axiom("$base$GHC.List$head").unwrap();
    assert!(ax.aliases_element(0, 1));
    assert!(!ax.aliases_spine(0, 1));
    let m = one_list_into(
        app(gvar_named("head", "$base$GHC.List$head"), var("xs")),
        json!({"head": import_fn("head", 1)}),
    );
    let l = list_census(&m);
    let f = cons_flow(&l, 0);
    assert!(
        !matches!(f.reuse, Reuse::SharedTail { .. }),
        "an element is not a tail: {:?}",
        f.reuse
    );
    assert!(f.consumers.iter().any(|c| c.aliases_element && !c.aliases));
}

/// **`any p xs` forces no element.** `p` may be `const True`. The elements
/// are *exposed* to the predicate, which is a fact of its own and is what
/// the text census must cite.
#[test]
fn a_predicate_exposes_elements_without_forcing_them() {
    let m = one_list_into(
        app(
            app(gvar_named("any", "$base$GHC.List$any"), var("p")),
            var("xs"),
        ),
        json!({"any": import_fn("any", 2)}),
    );
    let l = list_census(&m);
    let f = cons_flow(&l, 0);
    assert_eq!(
        f.head,
        crate::lists::HeadDemand::None,
        "an arbitrary predicate proves nothing about the elements"
    );
    assert_eq!(
        f.head_exposure,
        HeadExposure::PassedToCallback(CallbackKind::Predicate)
    );
}

/// …while `eqString` really does force, because at `Char` the comparison
/// is a primop and not a dictionary method.
#[test]
fn a_primitive_comparison_does_force_the_elements() {
    let m = one_list_into(
        app(
            app(
                gvar_named("eqString", "$base$GHC.Base$eqString"),
                var("other"),
            ),
            var("xs"),
        ),
        json!({"eqString": import_fn("eqString", 2)}),
    );
    let l = list_census(&m);
    let f = cons_flow(&l, 0);
    assert_eq!(f.head, crate::lists::HeadDemand::Prefix);
    assert_eq!(f.head_exposure, HeadExposure::NotExposed);
}

/// **A proven `SharedTail` beside one unknown consumer is not an
/// advisory.** `ys` is the right operand of `(++)` — its tail survives in
/// the result — and it is also handed to an import with no axiom. Before
/// M2.3g the shared tail won and the flow was advised
/// `PersistentCandidate`; it must be `Unknown`, with the sharing recorded
/// as a constraint that the unknown does not erase.
#[test]
fn a_shared_tail_beside_an_unknown_consumer_is_unknown_with_a_constraint() {
    let m = top_module(
        let1(
            "xs",
            cons_cell(var("x"), nil()),
            let1(
                "ys",
                cons_cell(var("y"), nil()),
                app(
                    app(
                        var("h"),
                        app(
                            app(gvar_named("++", "$base$GHC.Base$++"), var("xs")),
                            var("ys"),
                        ),
                    ),
                    app(
                        gvar_named("mystery", "$somelib$Some.Module$mystery"),
                        var("ys"),
                    ),
                ),
            ),
        ),
        list_ids(json!({
            "++": import_fn("++", 2),
            "mystery": import_fn("mystery", 1),
            "h": callee(true)
        })),
    );
    let l = list_census(&m);
    let ys = cons_flow(&l, 1);
    assert!(
        matches!(ys.reuse, Reuse::SharedTail { .. }),
        "{:?}",
        ys.reuse
    );
    assert_eq!(ys.spine, SpineDemand::Unknown);
    assert_eq!(ys.rec, Recommendation::Unknown);
    assert_eq!(
        ys.rec_reason.as_deref(),
        Some("no-axiom-for($somelib$Some.Module$mystery)")
    );
    assert!(
        ys.constraints.tail_sharing,
        "the sharing survives the unknown"
    );
    assert_eq!(ys.constraints.names(), vec![crate::lists::C_TAIL_SHARING]);
}

/// The whole census closes: every flow in exactly one bucket of every
/// table, and every one of the M2 census' list-cons sites mapped.
#[test]
fn the_list_accounting_closes() {
    let m = top_module(
        let1(
            "xs",
            cons_cell(app(var("g"), var("a")), nil()),
            app(gvar_named("length", "$base$GHC.List$length"), var("xs")),
        ),
        list_ids(json!({"length": import_fn("length", 1), "g": callee(true)})),
    );
    let modules = [&m];
    let census = Census::raw(modules.iter().copied());
    let lc = crate::lists::ListCensus::of_modules(&modules, &census);
    lc.accounting.check();
    assert_eq!(lc.accounting.flows, 1);
    assert_eq!(lc.accounting.sites_unmapped, 0);
    assert_eq!(
        lc.accounting.sites.len(),
        lc.accounting.sites_mapped,
        "the census' list-cons sites all land on a cell"
    );
}

//------------------------------------------------------------------------------
// text: which list flows are [Char], and what is done with them (M2.3d)
//------------------------------------------------------------------------------

use crate::text::{
    Advisory, ConsumerClass, ConsumerShape, ElementTypeEvidence, TextCensus, TextFlow, TextShape,
};

/// A binder carrying a type: the structured entry the rule reads, and the
/// rendering the report prints. The rendering is written here because it is
/// readable; [`ty_of`] is what turns it into the entry.
fn binder_ty(occ: &str, ty: &str) -> Value {
    let mut b = binder(occ, demand(false, false));
    b["type"] = json!(ty);
    b["ty"] = json!(ty_of(ty));
    b
}

/// A binder whose *rendering* and whose *structure* deliberately disagree,
/// so a test can show which of the two a rule reads.
fn binder_ty_ix(occ: &str, rendered: &str, ty: u32) -> Value {
    let mut b = binder(occ, demand(false, false));
    b["type"] = json!(rendered);
    b["ty"] = json!(ty);
    b
}

/// `let x :: ty = rhs in body`, with the binder's structured type given
/// explicitly and its rendering alongside.
fn let_ty_ix(occ: &str, rendered: &str, ty: u32, rhs: Value, body: Value) -> Value {
    json!({"node": "Let", "bind": {"rec": false, "pairs": [{
        "binder": binder_ty_ix(occ, rendered, ty), "rhs": rhs,
        "whnf": false, "trivial": false, "cheap": false, "okForSpec": false
    }]}, "body": body})
}

/// `let x :: ty = rhs in body`.
fn let_ty(occ: &str, ty: &str, rhs: Value, body: Value) -> Value {
    json!({"node": "Let", "bind": {"rec": false, "pairs": [{
        "binder": binder_ty(occ, ty), "rhs": rhs,
        "whnf": false, "trivial": false, "cheap": false, "okForSpec": false
    }]}, "body": body})
}

/// `case <scrut> of { [] -> nil_rhs; (y:ys) -> cons_rhs }` with the head
/// binder carrying a rendered type.
fn list_case_ty(scrut: Value, nil_rhs: Value, head_ty: &str, cons_rhs: Value) -> Value {
    json!({
        "node": "Case", "scrut": scrut,
        "binder": binder("wild", demand(false, false)), "type": "R", "ty": TY_R,
        "alts": [
            {"con": {"kind": "DataAlt", "name": "$ghc-prim$GHC.Types$[]", "occ": "[]", "tag": 1},
             "binders": [], "rhs": nil_rhs},
            {"con": {"kind": "DataAlt", "name": "$ghc-prim$GHC.Types$:", "occ": ":", "tag": 1},
             "binders": [binder_ty("y", head_ty), binder("ys", demand(false, false))],
             "rhs": cons_rhs}
        ]
    })
}

/// An `Addr#` string literal, as GHC dumps one.
fn str_lit(s: &str) -> Value {
    json!({"node": "Lit", "lit": {"kind": "string", "pretty": format!("{s:?}#")}})
}

fn char_lit(c: char) -> Value {
    json!({"node": "Lit", "lit": {"kind": "char", "pretty": format!("'{c}'#")}})
}

fn unpack(s: &str) -> Value {
    app(
        gvar_named("unpackCString#", "$ghc-prim$GHC.CString$unpackCString#"),
        str_lit(s),
    )
}

fn unpack_append(s: &str, rest: Value) -> Value {
    app(
        app(
            gvar_named(
                "unpackAppendCString#",
                "$ghc-prim$GHC.CString$unpackAppendCString#",
            ),
            str_lit(s),
        ),
        rest,
    )
}

/// The ids every text fixture needs, plus whatever else it asks for.
fn text_ids(extra: Value) -> Value {
    let mut ids = json!({
        "unpackCString#": import_fn("unpackCString#", 1),
        "unpackAppendCString#": import_fn("unpackAppendCString#", 2),
        "putStr": import_fn("putStr", 1),
    });
    if let Value::Object(o) = extra {
        for (k, v) in o {
            ids[k] = v;
        }
    }
    list_ids(ids)
}

fn put_str(x: Value) -> Value {
    app(gvar_named("putStr", "$base$System.IO$putStr"), x)
}

fn text_census(m: &Module) -> (crate::lists::ListAccounting, TextCensus) {
    let census = Census::raw([m]);
    let modules = [m];
    let lc = crate::lists::ListCensus::of_modules(&modules, &census);
    let tc = TextCensus::of_modules(&modules, &lc, &census);
    tc.accounting.check();
    (lc.accounting.clone(), tc)
}

fn only_text(tc: &TextCensus) -> &TextFlow {
    assert_eq!(
        tc.flows.len(),
        1,
        "expected exactly one text flow, got {:?}",
        tc.flows
            .iter()
            .map(|f| (f.producer, f.producer_name.clone()))
            .collect::<Vec<_>>()
    );
    &tc.flows[0]
}

/// `putStr (unpackAppendCString# "a"# (unpackCString# "b"#))`: static text
/// appended to static text and written out. Two operand segments, both
/// literal, one complete-output consumer, nothing observes a character.
#[test]
fn a_literal_appended_to_a_literal_and_printed_is_a_strong_string_candidate() {
    let m = top_module(
        put_str(unpack_append("a", unpack("b"))),
        text_ids(json!({})),
    );
    let (_la, tc) = text_census(&m);
    let f = tc
        .flows
        .iter()
        .find(|f| f.append_chain.is_some())
        .expect("the append is a flow of its own");
    let chain = f.append_chain.unwrap();
    assert_eq!(chain.length, 2, "two operand segments");
    assert!(chain.all_literal, "both segments are static data");
    assert_eq!(chain.opaque, 0);
    assert_eq!(f.shape, TextShape::TextOnly, "{:?}", f.consumers);
    assert_eq!(f.complete, 1, "putStr needs the whole text");
    assert!(!f.char_semantics_required, "{:?}", f.char_reasons);
    assert_eq!(
        f.advisory,
        Advisory::StrongStringCandidate,
        "{:?}",
        f.advisory_reason
    );
}

/// A `[Char]` taken apart by `(:)` whose head is compared against a `Char`
/// literal: an individual character is observed, so a representation must
/// keep character semantics, and the advisory is undecided.
#[test]
fn a_head_compared_against_a_char_literal_requires_char_semantics() {
    let scrutiny = case_alts(
        var("y"),
        &[("DEFAULT", vec![], var("u")), ("Q", vec![], var("u"))],
    );
    let mut scrutiny = scrutiny;
    // The inner case decides on a Char literal, which is what makes the
    // element an observed character rather than an opaque field.
    scrutiny["alts"][1]["con"] =
        json!({"kind": "LitAlt", "lit": {"kind": "char", "pretty": "'x'#"}});
    scrutiny["alts"][1]["binders"] = json!([]);
    let m = top_module(
        let_ty(
            "xs",
            "[Char]",
            cons_cell(var("a"), nil()),
            list_case_ty(var("xs"), var("u"), "Char", scrutiny),
        ),
        text_ids(json!({})),
    );
    let (_la, tc) = text_census(&m);
    let f = only_text(&tc);
    assert!(
        f.char_semantics_required,
        "an element is scrutinised as a character"
    );
    assert!(
        f.char_reasons
            .iter()
            .any(|(rule, _, _)| *rule == crate::text::X4_CHAR_SCRUTINY),
        "{:?}",
        f.char_reasons
    );
    assert_eq!(f.element_type_evidence, ElementTypeEvidence::Both);
    assert_eq!(
        f.advisory,
        Advisory::TextValueUndecided,
        "{:?}",
        f.advisory_reason
    );
}

/// A flow whose element type is a type *variable* is never assumed to be
/// text: it is element-type-unknown, and out of the population.
#[test]
fn a_type_variable_element_is_element_type_unknown_not_text() {
    let m = top_module(
        let_ty(
            "xs",
            "[a]",
            cons_cell(var("q"), nil()),
            list_case_ty(var("xs"), var("u"), "a", var("u")),
        ),
        text_ids(json!({})),
    );
    let (la, tc) = text_census(&m);
    assert_eq!(la.flows, 1);
    assert_eq!(tc.flows.len(), 0, "not text");
    assert_eq!(tc.accounting.elem_unknown, 1);
    assert_eq!(tc.accounting.non_text, 0);
    assert_eq!(tc.accounting.text_flows, 0);
}

/// `isPrefixOf needle xs` on text: only a prefix of the spine is needed,
/// which is a prefix consumer and not a complete-output one.
#[test]
fn is_prefix_of_on_text_is_a_prefix_consumer() {
    let m = top_module(
        let_ty(
            "xs",
            "[Char]",
            cons_cell(var("a"), nil()),
            app(
                app(
                    gvar_named("isPrefixOf", "$base$Data.OldList$isPrefixOf"),
                    var("needle"),
                ),
                var("xs"),
            ),
        ),
        text_ids(json!({"isPrefixOf": import_fn("isPrefixOf", 2)})),
    );
    let (_la, tc) = text_census(&m);
    let f = only_text(&tc);
    assert_eq!(f.prefix, 1, "{:?}", f.consumers);
    assert_eq!(f.complete, 0);
    assert_eq!(f.prefix_consumers.len(), 1);
    assert_eq!(f.shape, TextShape::TextOnly);
    assert_ne!(f.advisory, Advisory::StrongStringCandidate);
}

/// A `[Char]` handed to the generic `map`, whose result is not text: the
/// consumer set is mixed, because `map` is a list combinator and not a
/// text operation.
#[test]
fn a_char_list_passed_to_a_generic_map_is_mixed() {
    let m = top_module(
        let_ty(
            "xs",
            "[Char]",
            cons_cell(var("a"), nil()),
            app(
                app(gvar_named("map", "$base$GHC.Base$map"), var("f")),
                var("xs"),
            ),
        ),
        text_ids(json!({"map": import_fn("map", 2)})),
    );
    let (_la, tc) = text_census(&m);
    let f = only_text(&tc);
    assert_eq!(f.shape, TextShape::Mixed, "{:?}", f.consumers);
    assert!(
        f.consumers
            .iter()
            .any(|c| c.shape == ConsumerShape::Generic)
    );
    assert!(
        f.char_semantics_required,
        "map hands each character to a function"
    );
}

/// `unpackCString#` produces `[Char]` whatever any rendered type says: the
/// flow here has no binder at all, so nothing textual could have selected
/// it, and the structural fact does it alone.
#[test]
fn an_unpack_producer_with_no_readable_type_is_selected_structurally() {
    let m = top_module(put_str(unpack("b")), text_ids(json!({})));
    let (_la, tc) = text_census(&m);
    let f = only_text(&tc);
    assert_eq!(f.list_ty, None, "no binder carries a type");
    assert_eq!(f.elem_ty, None);
    assert_eq!(
        f.element_type_evidence,
        ElementTypeEvidence::StructuralOnly,
        "{:?}",
        f.selection
    );
    assert!(
        f.selection
            .iter()
            .any(|e| e.rule == crate::text::X2_UNPACK_PRODUCER)
    );
    assert!(f.literal, "static data");
}

/// `eqString xs ys`: the axiom's signature fixes the argument to `[Char]`,
/// which corroborates the type rather than replacing it. The binder's type
/// renders as `String`; the plugin expands the synonym, so what the rule
/// sees is `TyConApp List [TyConApp Char []]` and no spelling is involved.
#[test]
fn an_eq_string_consumer_corroborates_the_rendered_type() {
    let m = top_module(
        let_ty(
            "xs",
            "String",
            cons_cell(var("a"), nil()),
            app(
                app(gvar_named("eqString", "$base$GHC.Base$eqString"), var("xs")),
                var("ys"),
            ),
        ),
        text_ids(json!({"eqString": import_fn("eqString", 2)})),
    );
    let (_la, tc) = text_census(&m);
    let f = only_text(&tc);
    assert_eq!(
        f.element_type_evidence,
        ElementTypeEvidence::Both,
        "{:?}",
        f.selection
    );
    assert!(
        f.selection
            .iter()
            .any(|e| e.rule == crate::text::X1_LIST_TYPE),
        "`String` expands to TyConApp List [Char]: level-4 evidence"
    );
    assert!(
        f.selection
            .iter()
            .any(|e| e.rule == crate::text::X5_AXIOM_FIXES_CHAR),
        "and the signature corroborates it"
    );
    assert_eq!(
        f.consumers
            .iter()
            .find(|c| c.name.contains("eqString"))
            .map(|c| c.class),
        Some(ConsumerClass::Complete),
        "the whole text is the subject of the comparison"
    );
}

/// A `Char` literal consed onto a list says the list is text without any
/// type being read at all.
#[test]
fn a_char_literal_element_selects_the_flow_structurally() {
    let m = top_module(
        let1("xs", cons_cell(char_lit('x'), nil()), put_str(var("xs"))),
        text_ids(json!({})),
    );
    let (_la, tc) = text_census(&m);
    let f = only_text(&tc);
    assert_eq!(f.element_type_evidence, ElementTypeEvidence::StructuralOnly);
    assert!(
        f.selection
            .iter()
            .any(|e| e.rule == crate::text::X3_CHAR_LITERAL_HEAD),
        "{:?}",
        f.selection
    );
    assert!(f.char_semantics_required);
}

/// The milestone's accounting closes on a hand-built module: the three
/// selection buckets partition M2.3c's flows, and every append argument
/// site is mapped or carries a reason.
#[test]
fn the_text_accounting_closes() {
    let m = top_module(
        put_str(unpack_append("a", unpack("b"))),
        text_ids(json!({})),
    );
    let (la, tc) = text_census(&m);
    let a = &tc.accounting;
    a.check();
    assert_eq!(a.list_flows, la.flows);
    assert_eq!(a.text_flows + a.non_text + a.elem_unknown, a.list_flows);
    assert_eq!(a.type_only + a.structural_only + a.both, a.text_flows);
}

//------------------------------------------------------------------------------
// M2.3e: the independent re-derivation of the representation verdicts
//------------------------------------------------------------------------------

/// Collect every claim the three censuses publish for one module and hand
/// it to [`crate::verify_rep`], which re-derives it with a walk that shares
/// nothing with them but the IR.
fn rep_cross_check(m: &Module) -> crate::verify_rep::RepCrossCheck {
    use crate::verify_rep::{Claim, ClaimKind, RepCrossCheck, cross_check};

    let census = Census::raw([m]);
    let modules = [m];
    let fc = crate::fields::FieldCensus::of_modules(&modules, &census);
    let lc = crate::lists::ListCensus::of_modules(&modules, &census);
    let tc = TextCensus::of_modules(&modules, &lc, &census);

    let mut claims = Vec::new();
    for f in &fc.flows {
        for v in &f.verdicts {
            let kind = match v.rep {
                FieldRep::Direct => ClaimKind::FieldDirect,
                FieldRep::Dead => ClaimKind::FieldDead,
                FieldRep::Recursive => ClaimKind::FieldRecursive,
                _ => continue,
            };
            claims.push(Claim {
                module: f.module.clone(),
                kind,
                at: f.construction,
                field: v.index,
                rule: v.rule,
            });
        }
    }
    for f in &lc.flows {
        let kind = match f.rec {
            crate::lists::Recommendation::VecCandidate => Some(ClaimKind::ListVec),
            crate::lists::Recommendation::IteratorCandidate => Some(ClaimKind::ListIterator),
            _ => None,
        };
        if f.recursion == crate::lists::Recursion::RecursiveKnot {
            claims.push(Claim {
                module: f.module.clone(),
                kind: ClaimKind::ListKnot,
                at: f.producer,
                field: 0,
                rule: f.rec_rule,
            });
        }
        if let Some(kind) = kind {
            claims.push(Claim {
                module: f.module.clone(),
                kind,
                at: f.producer,
                field: 0,
                rule: f.rec_rule,
            });
        }
    }
    for f in &tc.flows {
        if f.advisory == crate::text::Advisory::StrongStringCandidate {
            claims.push(Claim {
                module: f.module.clone(),
                kind: ClaimKind::TextStrong,
                at: f.producer,
                field: 0,
                rule: f.advisory_rule,
            });
        }
    }
    let mut out = RepCrossCheck::default();
    cross_check(m, &census, &claims, &mut out);
    out
}

/// The modules the adversarial cases are built on, in one place: every one
/// of them goes through the independent re-derivation below.
fn adversarial_modules() -> Vec<Module> {
    vec![
        // 1 — `Foo (error …)` observed only at WHNF.
        top_module(
            let1(
                "r",
                con_app("Foo", &[app(var("g"), var("a"))]),
                case_force(var("r"), "seqw", var("u")),
            ),
            json!({"Foo": prog_con("Foo", 1), "g": callee(true)}),
        ),
        // 2a — an unused lazy field.
        top_module(
            let1(
                "r",
                con_app("Foo", &[app(var("g"), var("a"))]),
                case_alts(var("r"), &[("Foo", vec!["x"], var("u"))]),
            ),
            json!({"Foo": prog_con("Foo", 1), "g": callee(true)}),
        ),
        // 2b — an unused *strict* field.
        top_module(
            let1(
                "r",
                con_app("Bar", &[app(var("g"), var("a"))]),
                case_alts(var("r"), &[("Bar", vec!["x"], var("u"))]),
            ),
            json!({"Bar": prog_con_strict("Bar", 1), "g": callee(true)}),
        ),
        // 3 — forced on one observation only.
        top_module(
            let1(
                "r",
                con_app("Foo", &[app(var("g"), var("a"))]),
                app(
                    app(var("h"), case_force(var("r"), "seqw", var("u"))),
                    case_alts(var("r"), &[("Foo", vec!["x"], app(var("k"), var("x")))]),
                ),
            ),
            json!({"Foo": prog_con("Foo", 1), "g": callee(true), "k": callee(true)}),
        ),
        // 9 — a list stored in a program ADT.
        top_module(
            let1(
                "xs",
                cons_cell(var("x"), nil()),
                con_app("Box", &[var("xs")]),
            ),
            list_ids(json!({"Box": prog_con("Box", 1)})),
        ),
        // 10 — a list through a higher-order parameter.
        top_module(
            lam(
                &["f"],
                let1("xs", cons_cell(var("x"), nil()), app(var("f"), var("xs"))),
            ),
            list_ids(json!({})),
        ),
        // 14 — a case-binder alias under an alternative this value cannot
        // take: `case v of C x -> use x; D y -> store v` on a known `C`.
        top_module(
            let1(
                "r",
                con_app("C", &[app(var("g"), var("a"))]),
                case_alts(
                    var("r"),
                    &[
                        ("C", vec!["x"], app(var("k"), var("x"))),
                        ("D", vec!["y"], con_app("Box", &[var("wild")])),
                    ],
                ),
            ),
            json!({
                "C": prog_con("C", 1), "D": prog_con("D", 1),
                "Box": prog_con("Box", 1), "g": callee(true), "k": callee(true)
            }),
        ),
    ]
}

/// Every `Direct`, `Dead`, `Recursive`, `VecCandidate`,
/// `IteratorCandidate` and `StrongStringCandidate` verdict the censuses
/// reach on a hand-built module is re-derived from scratch by the
/// independent walk — with **no** disagreement, and no coverage refusal
/// either on shapes this small.
#[test]
fn the_rep_verifier_agrees_on_every_hand_built_module() {
    let mut checked = 0usize;
    for m in adversarial_modules() {
        let out = rep_cross_check(&m);
        checked += out.checked;
        assert_eq!(
            out.real_disagreements(),
            0,
            "{:?}",
            out.disagreements
                .iter()
                .map(|d| (d.claim.kind, d.refusal.why))
                .collect::<Vec<_>>()
        );
        // The only fact this walk declines to re-derive is `R3`, which is
        // the census' own frontier walk; nothing else may be refused on
        // shapes this small.
        for d in &out.disagreements {
            assert_eq!(d.refusal.why, crate::verify_rep::W_NO_R3_RULE);
        }
    }
    assert!(checked > 0, "the cross-check examined nothing");
}

/// Case 2b. `data X = X !T` with the field never read is **not** `Dead`:
/// the strictness is a forcing obligation that holds whenever `X` reaches
/// WHNF, and nobody reading the field does not remove it. The verifier
/// refuses a `Dead` claim on a strict field outright.
#[test]
fn an_unused_strict_field_is_not_dead() {
    let m = top_module(
        let1(
            "r",
            con_app("Bar", &[app(var("g"), var("a"))]),
            case_alts(var("r"), &[("Bar", vec!["x"], var("u"))]),
        ),
        json!({"Bar": prog_con_strict("Bar", 1), "g": callee(true)}),
    );
    let f = field_census(&m);
    let flow = one_con_flow(&f, "Bar");
    let v = &flow.verdicts[0];
    assert_eq!(v.demand, FieldDemand::Never);
    assert_eq!(v.strictness, ConStrictness::StrictField);
    assert_ne!(v.rep, FieldRep::Dead);
    assert!(v.force_on_whnf, "the forcing obligation survives");

    // And the independent walk refuses the claim the census does not make.
    use crate::verify_rep::{Claim, ClaimKind, RepVerifier};
    let census = Census::raw([&m]);
    let mut v2 = RepVerifier::new(&m, &census);
    let err = v2
        .check(&Claim {
            module: "M".into(),
            kind: ClaimKind::FieldDead,
            at: flow.construction,
            field: 0,
            rule: crate::fields::R5_DEAD,
        })
        .unwrap_err();
    assert_eq!(err.why, crate::verify_rep::X_DEAD_FIELD_STRICT);
}

/// Case 14, from the verifier's side. `case v of { C x -> k x; D y ->
/// Box wild }` on a value known to be `C`: the `D` alternative cannot run,
/// so the store of the case binder under it is not an escape and the field
/// verdict is not forced to `Unknown` by it. The independent walk selects
/// alternatives constructor-relative for exactly this reason, and skips
/// the case binder's occurrences that stand inside the other alternative.
#[test]
fn the_rep_verifier_skips_a_case_binder_under_an_unreachable_alternative() {
    let m = top_module(
        let1(
            "r",
            con_app("C", &[app(var("g"), var("a"))]),
            case_alts(
                var("r"),
                &[
                    ("C", vec!["x"], app(var("k"), var("x"))),
                    ("D", vec!["y"], con_app("Box", &[var("wild")])),
                ],
            ),
        ),
        json!({
            "C": prog_con("C", 1), "D": prog_con("D", 1), "Box": prog_con("Box", 1),
            "g": callee(true), "k": callee(true)
        }),
    );
    let f = field_census(&m);
    let flow = one_con_flow(&f, "C");
    assert!(
        flow.alias_occurrences_unreachable > 0,
        "the census skipped the unreachable case-binder occurrence"
    );
    assert_ne!(flow.verdicts[0].demand, FieldDemand::Unknown);

    // The verifier reaches the same conclusion on its own: it never sees
    // the store, so the value does not escape and the field is readable.
    let out = rep_cross_check(&m);
    assert_eq!(out.real_disagreements(), 0);
    for d in &out.disagreements {
        assert_eq!(d.refusal.why, crate::verify_rep::W_NO_R3_RULE);
    }
}

//------------------------------------------------------------------------------
// M2.3f: the representation views
//------------------------------------------------------------------------------

/// The three censuses over one hand-built module, plus the verification
/// index every view reads its `[verified: …]` from.
fn view_fixture<'a>(
    modules: &'a [&'a Module],
) -> (
    crate::fields::FieldCensus<'a>,
    crate::lists::ListCensus<'a>,
    TextCensus,
    crate::views::Verdicts,
) {
    let census = Census::raw(modules.iter().copied());
    let fc = crate::fields::FieldCensus::of_modules(modules, &census);
    let lc = crate::lists::ListCensus::of_modules(modules, &census);
    let tc = TextCensus::of_modules(modules, &lc, &census);
    let (_, v) = crate::views::verify_all(modules, &census, &fc, &lc, &tc);
    (fc, lc, tc, v)
}

/// The field view lists every field of the construction exactly once, with
/// the three facts, the derived rep and the route that proved it — and the
/// `check` that asserts the "exactly once" is the view's own.
#[test]
fn the_field_view_lists_every_field_once() {
    // `data C = C !Int Int`, built with one strict field already forced and
    // one lazy field that only one of two observations reads.
    let m = tops(
        vec![(
            binder("top", demand(false, false)),
            let1(
                "r",
                con_app("C", &[int_lit(1), app(var("g"), var("a"))]),
                case_alts(var("r"), &[("C", vec!["x", "y"], app(var("k"), var("y")))]),
            ),
        )],
        json!({
            "C": {
                "name": "$main$M$C", "occ": "C", "arity": 2,
                "dmdSig": {"args": [demand(false, false), demand(false, false)],
                           "diverges": false, "pretty": ""},
                "isJoinPoint": false,
                "dataCon": {"name": "$main$M$C", "repArity": 2, "tag": 1,
                            "strictFields": [true, false]}
            },
            "g": callee(true), "k": callee(true)
        }),
    );
    let ms = [&m];
    let (fc, _, _, v) = view_fixture(&ms);
    let flow = fc.flows.iter().find(|f| f.occ == "C").expect("a C flow");
    let view = crate::views::FieldView::of(&m, flow, &v);
    view.check();
    assert_eq!(view.arity, 2);
    assert_eq!(
        view.lines.len(),
        2,
        "one line per field, no more and no less"
    );
    assert_eq!(view.lines[0].index, 0);
    assert_eq!(view.lines[1].index, 1);
    // Field 0 is GHC-strict, so R1 proves the timing and the verifier
    // re-derives it; the headline carries the three facts and the route.
    assert_eq!(view.lines[0].rep, FieldRep::Direct);
    assert!(
        view.lines[0]
            .routes
            .contains(&crate::fields::R1_STRICT_FIELD)
    );
    assert_eq!(view.lines[0].verified, crate::views::Verified::Yes);
    assert!(
        view.lines[0].headline.contains("demand=")
            && view.lines[0].headline.contains("strict=")
            && view.lines[0].headline.contains("rec=")
            && view.lines[0].headline.contains("⇒ Direct"),
        "the headline must carry the three facts and the rep: {}",
        view.lines[0].headline
    );
    // Every line names at least one observation or an escape, so no field
    // is asserted without something under it.
    for l in &view.lines {
        assert!(
            !l.observations.is_empty() || l.escape.is_some() || !l.evidence.is_empty(),
            "field {} has no justification under it",
            l.index
        );
    }
}

/// The list view lists every consumer of the flow exactly once, each with
/// the rule that classified it and the demand that one consumer puts on the
/// spine.
#[test]
fn the_list_view_lists_every_consumer_once() {
    let m = tops(
        vec![(
            binder("top", demand(false, false)),
            let1(
                "xs",
                con_app(":", &[int_lit(1), con_app(":", &[int_lit(2), gvar("[]")])]),
                app(
                    app(
                        var("k"),
                        list_case(var("xs"), int_lit(0), &["y", "ys"], var("y")),
                    ),
                    app(gvar("length"), var("xs")),
                ),
            ),
        )],
        list_ids(json!({"length": import_fn("length", 1), "k": callee(true)})),
    );
    let ms = [&m];
    let (_, lc, _, v) = view_fixture(&ms);
    let flow = lc
        .flows
        .iter()
        .find(|f| f.kind == crate::lists::ProducerKind::ConsChain)
        .expect("a cons chain");
    let view = crate::views::ListView::of(&m, flow, &v);
    view.check(flow);
    assert_eq!(
        view.consumers.len(),
        flow.consumers.len(),
        "every consumer exactly once"
    );
    assert!(view.consumers.len() >= 2, "the fixture has two consumers");
    assert_eq!(view.cells.len(), 2, "one flow of two cells, not two flows");
    // Every consumer line carries its rule and the demand it contributes.
    for c in &view.consumers {
        assert!(!c.rule.is_empty());
        assert!(c.headline.contains("spine ") && c.headline.contains("head "));
    }
    // Every fact is present, each with the rule that decided it — including
    // M2.3g's `HeadExposure`, which is recorded beside `HeadDemand` and
    // never folded into it.
    let names: Vec<&str> = view.facts.iter().map(|(n, _, _)| *n).collect();
    assert_eq!(
        names,
        vec![
            "SpineDemand",
            "HeadDemand",
            "HeadExposure",
            "Reuse",
            "Storage",
            "Recursion",
            "ShortCircuit"
        ]
    );
    assert!(
        view.advisory_from.contains(view.facts[0].1.as_str()),
        "the advisory must name the fact combination it came from"
    );
}

/// The text view shows how `Char` was established — the selection evidence
/// — on top of the list view it refines.
#[test]
fn the_text_view_shows_the_selection_evidence() {
    // `eqString s "…"`: the axiom table fixes the argument to `[Char]`,
    // which is `X5-AXIOM-FIXES-CHAR`, a structural selection that reads no
    // rendered type at all.
    let m = tops(
        vec![(
            binder("top", demand(false, false)),
            let1(
                "s",
                con_app(":", &[gvar("c"), gvar("[]")]),
                app(
                    app(gvar_named("eqString", "$base$GHC.Base$eqString"), var("s")),
                    gvar("other"),
                ),
            ),
        )],
        list_ids(json!({"eqString": import_fn("eqString", 2)})),
    );
    let ms = [&m];
    let (_, lc, tc, v) = view_fixture(&ms);
    let flow = tc.flows.first().expect("a text flow");
    let view = crate::views::TextView::of(&m, flow, &lc.flows[flow.list_flow], &v);
    assert!(
        !view.selection.is_empty(),
        "the view must show how Char was established"
    );
    assert!(
        view.selection
            .iter()
            .any(|(rule, _)| *rule == crate::text::X5_AXIOM_FIXES_CHAR),
        "this flow is selected by a consumer's signature: {:?}",
        view.selection
    );
    // …and it sits on the list view, whose own consumer check still holds.
    view.list.check(&lc.flows[flow.list_flow]);
    assert_eq!(view.producer, flow.producer);
}

/// The route-set histogram asks all three `Direct` rules rather than
/// stopping at the first: a field that is both GHC-strict *and* already a
/// value lands in the `R1+R2` bucket, not in `R1`.
#[test]
fn the_route_set_shows_the_overlap_between_the_direct_rules() {
    let m = tops(
        vec![(
            binder("top", demand(false, false)),
            let1(
                "r",
                con_app("C", &[int_lit(1)]),
                case_alts(var("r"), &[("C", vec!["x"], app(var("k"), var("x")))]),
            ),
        )],
        json!({
            "C": {
                "name": "$main$M$C", "occ": "C", "arity": 1,
                "dmdSig": {"args": [demand(false, false)], "diverges": false, "pretty": ""},
                "isJoinPoint": false,
                "dataCon": {"name": "$main$M$C", "repArity": 1, "tag": 1,
                            "strictFields": [true]}
            },
            "k": callee(true)
        }),
    );
    let f = field_census(&m);
    let flow = one_con_flow(&f, "C");
    let v = &flow.verdicts[0];
    assert_eq!(v.rep, FieldRep::Direct);
    assert_eq!(v.rule, crate::fields::R1_STRICT_FIELD, "R1 is tried first");
    assert_eq!(
        v.route_key(),
        "R1+R2+R3",
        "the field is strict, already a value, AND scrutinised at the construction's own \
         frontier — all three prove it, and the histogram must show all three"
    );
}

/// The selection reads the **structured** type, not GHC's rendering of it.
/// Here the binder renders as `Path` — a name no rule knows and no
/// spelling-based reading could accept — while its type *is*
/// `TyConApp List [TyConApp Char []]`. The flow is text, on `X1-LIST-TYPE`.
#[test]
fn a_list_of_char_is_text_whatever_its_rendering_says() {
    let m = top_module(
        let_ty_ix(
            "xs",
            "Path",
            TY_STRING,
            cons_cell(var("a"), nil()),
            put_str(var("xs")),
        ),
        text_ids(json!({})),
    );
    let (_la, tc) = text_census(&m);
    let f = only_text(&tc);
    assert_eq!(f.list_ty.as_deref(), Some("Path"), "the rendering is kept");
    assert!(
        f.selection
            .iter()
            .any(|e| e.rule == crate::text::X1_LIST_TYPE),
        "{:?}",
        f.selection
    );
    // `putStr` fixes `[Char]` too, so both kinds of evidence are present;
    // the point here is that the type half fired on a rendering nothing
    // could have parsed.
    assert_eq!(f.element_type_evidence, ElementTypeEvidence::Both);
}

/// …and the converse: a binder that *renders* as `[Char]` but whose type is
/// `[a]` is element-type-unknown. A rule that read the string would call
/// this text; nothing does.
#[test]
fn a_rendering_that_says_char_over_a_type_variable_is_not_text() {
    let m = top_module(
        let_ty_ix(
            "xs",
            "[Char]",
            TY_LIST_A,
            cons_cell(var("q"), nil()),
            var("u"),
        ),
        text_ids(json!({})),
    );
    let (la, tc) = text_census(&m);
    assert_eq!(la.flows, 1);
    assert_eq!(tc.flows.len(), 0, "a type variable proves nothing");
    assert_eq!(tc.accounting.elem_unknown, 1);
    assert_eq!(tc.accounting.non_text, 0);
}

/// The two readings of a flow's element type — the structured one the rules
/// use and the rendered one M2.3d used to use — are checked against each
/// other, so the move from level 6 to level 4 cannot silently reclassify a
/// flow. They agree when the fixture does not force them apart.
#[test]
fn the_structured_and_rendered_element_readings_agree() {
    let m = top_module(
        let_ty(
            "xs",
            "String",
            cons_cell(var("a"), nil()),
            list_case_ty(var("xs"), var("u"), "Char", var("u")),
        ),
        text_ids(json!({})),
    );
    let census = Census::raw([&m]);
    let modules = [&m];
    let lc = crate::lists::ListCensus::of_modules(&modules, &census);
    assert!(!lc.flows.is_empty());
    for f in &lc.flows {
        assert_eq!(crate::text::elem_readings_disagree(f), None, "{f:?}");
    }
}

//------------------------------------------------------------------------------
// Class-op dispatch: which instance and which method can run (classops.rs)
//------------------------------------------------------------------------------

use crate::classops::{self, Outcome, SourceKind, TargetKind};

/// A binder with a class-constraint type: a dictionary.
fn dict_binder(occ: &str, ty: u32) -> Value {
    let mut b = binder(occ, demand(false, false));
    b["ty"] = json!(ty);
    b["type"] = json!("dict");
    b
}

fn dict_lam_binder(occ: &str, ty: u32) -> Value {
    let mut b = lam_binder(occ, false);
    b["ty"] = json!(ty);
    b["type"] = json!("dict");
    b
}

/// A class-op selector, for the id table: GHC's own `isClassOpId`.
fn class_op(occ: &str, module: &str) -> (String, Value) {
    let name = format!("${module}${occ}");
    (
        name.clone(),
        json!({
            "name": name, "occ": occ, "arity": 1,
            "dmdSig": {"args": [demand(true, false)], "diverges": false, "pretty": ""},
            "isJoinPoint": false, "isClassOp": true, "details": "[gid[ClassOp]]",
            "hasUnfolding": false
        }),
    )
}

/// A class's dictionary constructor, for the id table.
fn dict_con(occ: &str, module: &str, arity: u32) -> (String, Value) {
    let name = format!("${module}${occ}");
    (name.clone(), data_con(occ, &name, arity))
}

/// `case <scrut> of wild { <con> d… -> <rhs> }` with dictionary-typed
/// alternative binders.
fn case_con_dict(scrut: Value, con: &str, binders: &[(&str, u32)], rhs: Value) -> Value {
    json!({
        "node": "Case", "scrut": scrut,
        "binder": binder("wild", demand(false, false)), "type": "R", "ty": TY_R,
        "alts": [{
            "con": {"kind": "DataAlt", "name": con, "occ": con, "tag": 1},
            "binders": binders.iter().map(|(b, t)| dict_binder(b, *t)).collect::<Vec<_>>(),
            "rhs": rhs
        }]
    })
}

/// A global `Var` with an explicit stable name.
fn named_gvar(occ: &str, name: &str) -> Value {
    json!({"node": "Var", "name": name, "occ": occ, "unique": occ, "isGlobal": true})
}

/// A saturated application of a dictionary constructor named by stable name.
fn dict_con_app(occ: &str, name: &str, args: &[Value]) -> Value {
    let mut e = named_gvar(occ, name);
    for a in args {
        e = app(e, a.clone());
    }
    e
}

/// A lambda chain over dictionary parameters.
fn dict_lam(params: &[(&str, u32)], body: Value) -> Value {
    let mut e = body;
    for (p, ty) in params.iter().rev() {
        e = json!({"node": "Lam", "binder": dict_lam_binder(p, *ty), "body": e});
    }
    e
}

/// A top-level binding whose binder carries a class-constraint type.
fn dict_top(occ: &str, ty: u32, exported: bool) -> Value {
    let mut b = dict_binder(occ, ty);
    b["exported"] = json!(exported);
    b
}

/// The id table every class-op fixture shares: the `Show`, `Eq` and `Ord`
/// selectors and dictionary constructors GHC really uses.
fn class_ids(extra: Vec<(String, Value)>) -> Value {
    let mut ids = serde_json::Map::new();
    for (k, v) in [
        class_op("showsPrec", "base$GHC.Show"),
        class_op("show", "base$GHC.Show"),
        class_op("==", "ghc-prim$GHC.Classes"),
        class_op("$p1Ord", "ghc-prim$GHC.Classes"),
        dict_con("C:Show", "base$GHC.Show", 3),
        dict_con("C:Eq", "ghc-prim$GHC.Classes", 2),
        dict_con("C:Ord", "ghc-prim$GHC.Classes", 8),
        ("g".to_string(), callee(false)),
    ] {
        ids.insert(k, v);
    }
    for (k, v) in extra {
        ids.insert(k, v);
    }
    Value::Object(ids)
}

/// A module of top-level bindings whose id table is *not* rekeyed: these
/// fixtures give every global its real stable name already.
fn class_module(name: &str, pairs: Vec<(Value, Value)>, ids: Value) -> Module {
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
        "format": raw::FORMAT, "module": name, "unit": "main",
        "types": ty_table(), "ids": ids, "binds": binds
    });
    Module::from_raw(serde_json::from_value(m).unwrap()).unwrap()
}

const SHOWS_PREC: &str = "$base$GHC.Show$showsPrec";
const EQ_EQ: &str = "$ghc-prim$GHC.Classes$==";
const P1_ORD: &str = "$ghc-prim$GHC.Classes$$p1Ord";
const C_SHOW: &str = "$base$GHC.Show$C:Show";
const C_EQ: &str = "$ghc-prim$GHC.Classes$C:Eq";
const C_ORD: &str = "$ghc-prim$GHC.Classes$C:Ord";

/// `C:Show $cshowsPrec $cshow $cshowList`.
fn show_dict() -> Value {
    dict_con_app(
        "C:Show",
        C_SHOW,
        &[var("$cshowsPrec"), var("$cshow"), var("$cshowList")],
    )
}

fn class_census(ms: &[Module]) -> classops::Census {
    let world = classops::World::new(ms);
    let c = classops::Census::of_world(&world);
    assert!(
        classops::check_table(&world).is_empty(),
        "class table disagrees with the dump"
    );
    c
}

fn one_class_site(c: &classops::Census) -> &classops::Site {
    assert_eq!(c.sites.len(), 1, "expected exactly one class-op site");
    &c.sites[0]
}

/// A selector applied to a dictionary this module builds: one origin, one
/// method field, one target.
#[test]
fn a_selector_on_a_known_dfun_is_exact() {
    let m = class_module(
        "M",
        vec![
            (dict_top("$fShowT", TY_SHOW_T, false), show_dict()),
            (
                binder("use", demand(false, false)),
                app(
                    app(named_gvar("showsPrec", SHOWS_PREC), var("$fShowT")),
                    var("x"),
                ),
            ),
        ],
        class_ids(vec![]),
    );
    let c = class_census(&[m]);
    let site = one_class_site(&c);
    assert_eq!(site.class.as_deref(), Some("$base$GHC.Show$Show"));
    assert_eq!(site.field, Some(0));
    match &site.outcome {
        Outcome::Exact(t) => {
            assert_eq!(t.occ, "$cshowsPrec");
            assert_eq!(t.kind, TargetKind::GlobalBinding);
        }
        other => panic!("expected Exact, got {other:?}"),
    }
    assert!(site.facts.forces_dictionary);
}

/// A dfun applied to an argument dictionary: the instance's own method is
/// the target.
#[test]
fn a_dfun_applied_to_an_argument_dictionary_resolves_through_the_instance() {
    let inner = dict_con_app(
        "C:Show",
        C_SHOW,
        &[var("$cshowsPrecL"), var("$cshowL"), var("$cshowListL")],
    );
    let m = class_module(
        "M",
        vec![
            (dict_top("$fShowT", TY_SHOW_T, false), show_dict()),
            (
                dict_top("$fShowList", TY_SHOW_T, false),
                dict_lam(&[("dShow", TY_SHOW_T)], inner),
            ),
            (
                binder("use", demand(false, false)),
                app(
                    app(
                        named_gvar("showsPrec", SHOWS_PREC),
                        app(var("$fShowList"), var("$fShowT")),
                    ),
                    var("x"),
                ),
            ),
        ],
        class_ids(vec![]),
    );
    let c = class_census(&[m]);
    match &one_class_site(&c).outcome {
        Outcome::Exact(t) => assert_eq!(t.occ, "$cshowsPrecL"),
        other => panic!("expected Exact, got {other:?}"),
    }
}

/// A dictionary field that is one of the dfun's own parameters is the
/// actual argument at the application that built the dictionary.
#[test]
fn a_dfun_parameter_in_a_field_is_the_actual_argument() {
    let ord_dict = dict_con_app(
        "C:Ord",
        C_ORD,
        &[
            var("dEq"),
            var("$ccompare"),
            var("$c<"),
            var("$c<="),
            var("$c>"),
            var("$c>="),
            var("$cmax"),
            var("$cmin"),
        ],
    );
    let m = class_module(
        "M",
        vec![
            (
                dict_top("$fEqT", TY_EQ_T, false),
                dict_con_app("C:Eq", C_EQ, &[var("$c=="), var("$c/=")]),
            ),
            (
                dict_top("$fOrdT", TY_ORD_T, false),
                dict_lam(&[("dEq", TY_EQ_T)], ord_dict),
            ),
            (
                binder("use", demand(false, false)),
                app(
                    named_gvar("$p1Ord", P1_ORD),
                    app(var("$fOrdT"), var("$fEqT")),
                ),
            ),
        ],
        class_ids(vec![]),
    );
    let c = class_census(&[m]);
    match &one_class_site(&c).outcome {
        Outcome::Exact(t) => assert_eq!(t.occ, "$fEqT"),
        other => panic!("expected the argument dictionary, got {other:?}"),
    }
}

/// The class the table names and the class the dictionary's type says must
/// agree, or nothing is read.
#[test]
fn a_selector_over_the_wrong_class_dictionary_is_refused() {
    let m = class_module(
        "M",
        vec![
            (
                dict_top("$fOrdT", TY_ORD_T, false),
                dict_con_app(
                    "C:Ord",
                    C_ORD,
                    &[
                        var("$fEqT"),
                        var("$ccompare"),
                        var("$c<"),
                        var("$c<="),
                        var("$c>"),
                        var("$c>="),
                        var("$cmax"),
                        var("$cmin"),
                    ],
                ),
            ),
            (
                binder("use", demand(false, false)),
                app(
                    app(named_gvar("showsPrec", SHOWS_PREC), var("$fOrdT")),
                    var("x"),
                ),
            ),
        ],
        class_ids(vec![]),
    );
    let c = class_census(&[m]);
    assert!(
        matches!(&one_class_site(&c).outcome,
                 Outcome::Unresolved(r) if r.starts_with(classops::U_CLASS_MISMATCH)),
        "{:?}",
        one_class_site(&c).outcome
    );
}

/// `$p1Ord d` selects the `Eq` superclass field, and the walk continues
/// into the dictionary it finds there.
#[test]
fn a_superclass_selection_is_followed_to_the_superclass() {
    let ord_dict = dict_con_app(
        "C:Ord",
        C_ORD,
        &[
            var("$fEqT"),
            var("$ccompare"),
            var("$c<"),
            var("$c<="),
            var("$c>"),
            var("$c>="),
            var("$cmax"),
            var("$cmin"),
        ],
    );
    let m = class_module(
        "M",
        vec![
            (
                dict_top("$fEqT", TY_EQ_T, false),
                dict_con_app("C:Eq", C_EQ, &[var("$c=="), var("$c/=")]),
            ),
            (dict_top("$fOrdT", TY_ORD_T, false), ord_dict),
            (
                binder("use", demand(false, false)),
                app(
                    app(
                        named_gvar("==", EQ_EQ),
                        app(named_gvar("$p1Ord", P1_ORD), var("$fOrdT")),
                    ),
                    var("x"),
                ),
            ),
        ],
        class_ids(vec![]),
    );
    let c = class_census(&[m]);
    // Two sites: the `==` and the `$p1Ord` that feeds it.
    assert_eq!(c.sites.len(), 2);
    let eq = c.sites.iter().find(|s| s.method == "==").unwrap();
    match &eq.outcome {
        Outcome::Exact(t) => assert_eq!(t.occ, "$c=="),
        other => panic!("expected Exact, got {other:?}"),
    }
    let sup = c.sites.iter().find(|s| s.method == "$p1Ord").unwrap();
    assert!(sup.is_superclass_sel);
    match &sup.outcome {
        Outcome::Exact(t) => assert_eq!(t.occ, "$fEqT"),
        other => panic!("expected the superclass field, got {other:?}"),
    }
}

/// A local function's dictionary parameter: the union over its call sites.
#[test]
fn two_call_sites_passing_different_dictionaries_give_a_finite_set() {
    let other_dict = dict_con_app(
        "C:Show",
        C_SHOW,
        &[var("$cshowsPrec2"), var("$cshow2"), var("$cshowList2")],
    );
    let m = class_module(
        "M",
        vec![
            (dict_top("$fShowT", TY_SHOW_T, false), show_dict()),
            (dict_top("$fShowT2", TY_SHOW_T, false), other_dict),
            (
                binder("f", demand(false, false)),
                dict_lam(
                    &[("d", TY_SHOW_T)],
                    lam(
                        &["x"],
                        app(app(named_gvar("showsPrec", SHOWS_PREC), var("d")), var("x")),
                    ),
                ),
            ),
            (
                binder("use", demand(false, false)),
                app(
                    app(app(var("f"), var("$fShowT")), var("a")),
                    app(app(var("f"), var("$fShowT2")), var("b")),
                ),
            ),
        ],
        class_ids(vec![]),
    );
    let c = class_census(&[m]);
    let site = one_class_site(&c);
    match &site.outcome {
        Outcome::FiniteSet(ts) => {
            let mut occs: Vec<&str> = ts.iter().map(|t| t.occ.as_str()).collect();
            occs.sort();
            assert_eq!(occs, vec!["$cshowsPrec", "$cshowsPrec2"]);
        }
        other => panic!("expected FiniteSet(2), got {other:?}"),
    }
    assert!(site.rules.contains(&classops::K8_PARAM_UNION));
}

/// An exported function can be called from outside this module, so its
/// dictionary parameter is not enumerable.
#[test]
fn an_exported_functions_dictionary_parameter_is_unresolved() {
    let m = class_module(
        "M",
        vec![(
            dict_top("f", TY_T, true),
            dict_lam(
                &[("d", TY_SHOW_T)],
                lam(
                    &["x"],
                    app(app(named_gvar("showsPrec", SHOWS_PREC), var("d")), var("x")),
                ),
            ),
        )],
        class_ids(vec![]),
    );
    let c = class_census(&[m]);
    assert!(
        matches!(&one_class_site(&c).outcome, Outcome::Unresolved(r) if r == classops::U_EXPORTED_PARAM),
        "{:?}",
        one_class_site(&c).outcome
    );
}

/// A dictionary stored in a program constructor and read back is not
/// followable: the constructor's field is whatever anyone put there.
#[test]
fn a_dictionary_read_from_a_constructor_field_is_unresolved() {
    let m = class_module(
        "M",
        vec![(
            binder("use", demand(false, false)),
            case_con_dict(
                var("box"),
                "MkBox",
                &[("d", TY_SHOW_T)],
                app(app(named_gvar("showsPrec", SHOWS_PREC), var("d")), var("x")),
            ),
        )],
        class_ids(vec![(
            "MkBox".to_string(),
            data_con("MkBox", "$main$M$MkBox", 1),
        )]),
    );
    let c = class_census(&[m]);
    assert!(
        matches!(&one_class_site(&c).outcome, Outcome::Unresolved(r) if r == classops::U_FROM_FIELD),
        "{:?}",
        one_class_site(&c).outcome
    );
}

/// A selector that is not applied to anything is a value, not a dispatch.
#[test]
fn a_partially_applied_selector_is_recorded_as_one() {
    let m = class_module(
        "M",
        vec![(
            binder("use", demand(false, false)),
            app(var("g"), named_gvar("showsPrec", SHOWS_PREC)),
        )],
        class_ids(vec![]),
    );
    let c = class_census(&[m]);
    let site = one_class_site(&c);
    assert_eq!(site.n_value_args, 0);
    assert!(site.rules.contains(&classops::K12_PARTIAL));
    assert!(
        matches!(&site.outcome, Outcome::Unresolved(r) if r == classops::U_PARTIAL),
        "{:?}",
        site.outcome
    );
}

/// A dictionary that is also handed to an unknown callee: the observation
/// is recorded, and the method target is unaffected by it.
#[test]
fn a_dictionary_used_as_an_ordinary_value_is_recorded_but_still_resolves() {
    let m = class_module(
        "M",
        vec![
            (dict_top("$fShowT", TY_SHOW_T, false), show_dict()),
            (
                binder("f", demand(false, false)),
                dict_lam(
                    &[("d", TY_SHOW_T)],
                    app(
                        app(app(named_gvar("showsPrec", SHOWS_PREC), var("d")), var("x")),
                        app(gvar("g"), var("d")),
                    ),
                ),
            ),
            (
                binder("use", demand(false, false)),
                app(var("f"), var("$fShowT")),
            ),
        ],
        class_ids(vec![]),
    );
    let c = class_census(&[m]);
    let site = one_class_site(&c);
    assert!(site.facts.dict_used_as_value);
    assert!(site.rules.contains(&classops::K11_DICT_ESCAPES));
    match &site.outcome {
        Outcome::Exact(t) => assert_eq!(t.occ, "$cshowsPrec"),
        other => panic!("expected Exact, got {other:?}"),
    }
}

/// The dictionary sources of a module are enumerated by kind.
#[test]
fn dictionary_sources_are_enumerated_by_kind() {
    let m = class_module(
        "M",
        vec![
            (dict_top("$fShowT", TY_SHOW_T, false), show_dict()),
            (
                binder("f", demand(false, false)),
                dict_lam(
                    &[("d", TY_SHOW_T)],
                    app(app(named_gvar("showsPrec", SHOWS_PREC), var("d")), var("x")),
                ),
            ),
        ],
        class_ids(vec![]),
    );
    let c = class_census(&[m]);
    let a = c.accounting();
    assert_eq!(a.sources.get(&SourceKind::Dfun), Some(&1));
    assert_eq!(a.sources.get(&SourceKind::DictParam), Some(&1));
    assert_eq!(a.population, 1);
    a.check().unwrap();
}

/// A dfun defined in another module of the closed world: an import here, a
/// top-level binding there, and the same stable name in both.
#[test]
fn a_dfun_in_another_module_is_followed_across_the_closed_world() {
    let mut b = dict_binder("$fShowT", TY_SHOW_T);
    b["name"] = json!("$main$A$$fShowT");
    let a = class_module(
        "A",
        vec![
            (b, show_dict()),
            (
                binder("$cshowsPrec", demand(false, false)),
                lam(&["p", "v"], var("v")),
            ),
        ],
        class_ids(vec![]),
    );
    let m = class_module(
        "B",
        vec![(
            binder("use", demand(false, false)),
            app(
                app(
                    named_gvar("showsPrec", SHOWS_PREC),
                    named_gvar("$fShowT", "$main$A$$fShowT"),
                ),
                var("x"),
            ),
        )],
        class_ids(vec![]),
    );
    let c = class_census(&[a, m]);
    let site = c.sites.iter().find(|s| s.module == "B").unwrap();
    match &site.outcome {
        Outcome::Exact(t) => {
            assert_eq!(t.occ, "$cshowsPrec");
            assert_eq!(t.module, "A");
        }
        other => panic!("expected Exact across modules, got {other:?}"),
    }
}

/// A dfun that is not in the dump at all: the instance is known exactly,
/// the method body is not, and the site says so instead of guessing.
#[test]
fn an_imported_dfun_names_the_instance_and_refuses_the_method() {
    let m = class_module(
        "M",
        vec![(
            binder("use", demand(false, false)),
            app(
                app(
                    named_gvar("showsPrec", SHOWS_PREC),
                    named_gvar("$fShowInt", "$base$GHC.Show$$fShowInt"),
                ),
                var("x"),
            ),
        )],
        class_ids(vec![]),
    );
    let c = class_census(&[m]);
    let site = one_class_site(&c);
    assert_eq!(site.origins.len(), 1);
    assert_eq!(site.origins[0].kind, classops::OriginKind::ImportedDfun);
    assert_eq!(site.origins[0].name, "$base$GHC.Show$$fShowInt");
    assert!(
        matches!(&site.outcome, Outcome::Unresolved(r) if r.contains(classops::U_IMPORTED_DFUN)),
        "{:?}",
        site.outcome
    );
}

//------------------------------------------------------------------------------
// Whole-program dictionary propagation and erasure (dictflow.rs)
//------------------------------------------------------------------------------

use crate::dictflow::{self, DictFlow, DictSet, Verdict};

/// A top-level binder with an explicit stable name.
fn named_top(occ: &str, name: &str, exported: bool) -> Value {
    let mut b = binder(occ, demand(false, false));
    b["name"] = json!(name);
    b["exported"] = json!(exported);
    b
}

/// A dictionary binding with an explicit stable name.
fn named_dict_top(occ: &str, name: &str, ty: u32) -> Value {
    let mut b = dict_top(occ, ty, false);
    b["name"] = json!(name);
    b
}

/// `C:Show <method> $cshow $cshowList`.
fn show_dict_with(method: &str) -> Value {
    dict_con_app(
        "C:Show",
        C_SHOW,
        &[var(method), var("$cshow"), var("$cshowList")],
    )
}

/// `f = \$dShow x -> showsPrec $dShow x`, exported, in module `A`.
fn show_user(name: &str) -> (Value, Value) {
    (
        named_top("f", name, true),
        dict_lam(
            &[("$dShow", TY_SHOW_T)],
            lam(
                &["x"],
                app(
                    app(named_gvar("showsPrec", SHOWS_PREC), var("$dShow")),
                    var("x"),
                ),
            ),
        ),
    )
}

/// `use = f <dict> y`, calling `A.f` from another module.
fn call_f(occ: &str, dict: Value) -> (Value, Value) {
    (
        binder(occ, demand(false, false)),
        app(app(named_gvar("f", "$main$A$f"), dict), var("y")),
    )
}

fn flow_site<'a>(f: &'a DictFlow, module: &str) -> &'a dictflow::Site {
    f.sites
        .iter()
        .find(|s| s.module == module)
        .expect("no class-op site in that module")
}

fn flow_param<'a>(f: &'a DictFlow, owner: &str) -> &'a dictflow::Param {
    f.params
        .iter()
        .find(|p| p.owner == owner)
        .expect("no such dictionary parameter")
}

/// Module `A`: the dictionaries, the instance methods and the exported
/// function whose dictionary parameter the closed world has to enumerate.
fn wp_module_a(extra: Vec<(Value, Value)>) -> Module {
    let mut pairs = vec![
        (
            named_dict_top("$fShowT", "$main$A$$fShowT", TY_SHOW_T),
            show_dict_with("$cshowsPrec"),
        ),
        (
            named_dict_top("$fShowU", "$main$A$$fShowU", TY_SHOW_T),
            show_dict_with("$cshowsPrecU"),
        ),
        (
            binder("$cshowsPrec", demand(false, false)),
            lam(&["p", "v"], var("v")),
        ),
        (
            binder("$cshowsPrecU", demand(false, false)),
            lam(&["p", "v"], var("v")),
        ),
    ];
    let (b, rhs) = show_user("$main$A$f");
    pairs.push((b, rhs));
    pairs.extend(extra);
    class_module("A", pairs, class_ids(vec![]))
}

/// The one call site in the closed world fixes the instance: the exported
/// function's dictionary parameter is a singleton and the method is exact.
#[test]
fn one_caller_in_the_closed_world_makes_the_method_exact() {
    let a = wp_module_a(vec![]);
    let b = class_module(
        "B",
        vec![call_f("use", named_gvar("$fShowT", "$main$A$$fShowT"))],
        class_ids(vec![]),
    );
    let f = DictFlow::of_modules([&a, &b]);
    let p = flow_param(&f, "f");
    assert_eq!(p.set.keys().len(), 1, "{:?}", p.set);
    match &flow_site(&f, "A").outcome {
        dictflow::Outcome::Exact(t) => assert_eq!(t.occ, "$cshowsPrec"),
        other => panic!("expected Exact, got {other:?}"),
    }
    f.accounting().check().unwrap();
}

/// Two modules, two dfuns: the union is a finite set of two, and so is the
/// method target. Neither module could say this on its own.
#[test]
fn two_callers_in_two_modules_give_a_finite_set_of_two() {
    let a = wp_module_a(vec![]);
    let b = class_module(
        "B",
        vec![call_f("useB", named_gvar("$fShowT", "$main$A$$fShowT"))],
        class_ids(vec![]),
    );
    let c = class_module(
        "C",
        vec![call_f("useC", named_gvar("$fShowU", "$main$A$$fShowU"))],
        class_ids(vec![]),
    );
    let f = DictFlow::of_modules([&a, &b, &c]);
    assert_eq!(flow_param(&f, "f").set.keys().len(), 2);
    match &flow_site(&f, "A").outcome {
        dictflow::Outcome::FiniteSet(ts) => assert_eq!(ts.len(), 2),
        other => panic!("expected FiniteSet(2), got {other:?}"),
    }
    f.accounting().check().unwrap();
}

/// The same two callers, but a third module also uses the function as a
/// value: the producer set is no longer enumerable and every site
/// downstream of the parameter is Unresolved.
#[test]
fn using_the_function_as_a_value_makes_the_parameter_unenumerable() {
    let a = wp_module_a(vec![]);
    let b = class_module(
        "B",
        vec![call_f("useB", named_gvar("$fShowT", "$main$A$$fShowT"))],
        class_ids(vec![]),
    );
    let c = class_module(
        "C",
        vec![(
            binder("stash", demand(false, false)),
            app(gvar("g"), named_gvar("f", "$main$A$f")),
        )],
        class_ids(vec![]),
    );
    let f = DictFlow::of_modules([&a, &b, &c]);
    assert_eq!(
        flow_param(&f, "f").set,
        DictSet::Top(dictflow::T_USED_AS_A_VALUE.into())
    );
    assert!(
        matches!(&flow_site(&f, "A").outcome,
            dictflow::Outcome::Unresolved(r) if r == dictflow::T_USED_AS_A_VALUE),
        "{:?}",
        flow_site(&f, "A").outcome
    );
    f.accounting().check().unwrap();
}

/// Dispatch carries dictionaries forward: the instance method `$cshowsPrec`
/// is reached only by selecting field 0 of `$fShowT`, and the dictionary
/// the dispatch site passes becomes its own parameter's producer.
#[test]
fn dispatch_feeds_the_instance_methods_own_dictionary_parameter() {
    // $cshowsPrec = \$dShow2 v -> showsPrec $dShow2 v
    let method = (
        binder("$cshowsPrec", demand(false, false)),
        dict_lam(
            &[("$dShow2", TY_SHOW_T)],
            lam(
                &["v"],
                app(
                    app(named_gvar("showsPrec", SHOWS_PREC), var("$dShow2")),
                    var("v"),
                ),
            ),
        ),
    );
    let mut pairs = vec![
        (
            named_dict_top("$fShowT", "$main$A$$fShowT", TY_SHOW_T),
            show_dict_with("$cshowsPrec"),
        ),
        (
            named_dict_top("$fShowU", "$main$A$$fShowU", TY_SHOW_T),
            show_dict_with("$cshowsPrecU"),
        ),
        method,
        (
            binder("$cshowsPrecU", demand(false, false)),
            lam(&["p", "v"], var("v")),
        ),
    ];
    // The dispatch: showsPrec $fShowT $fShowU  — the method's own
    // dictionary parameter receives $fShowU.
    pairs.push((
        binder("dispatch", demand(false, false)),
        app(
            app(
                named_gvar("showsPrec", SHOWS_PREC),
                named_gvar("$fShowT", "$main$A$$fShowT"),
            ),
            named_gvar("$fShowU", "$main$A$$fShowU"),
        ),
    ));
    let a = class_module("A", pairs, class_ids(vec![]));
    let f = DictFlow::of_modules([&a]);
    let p = flow_param(&f, "$cshowsPrec");
    assert_eq!(p.set.keys().len(), 1, "{:?}", p.set);
    let key = p.set.keys().iter().next().unwrap();
    assert!(
        f.values
            .iter()
            .any(|v| v.what.contains(key) && v.what.contains("$fShowU")),
        "the dispatch should have carried $fShowU into the method: {key}"
    );
    let inner = f
        .sites
        .iter()
        .find(|s| s.node != flow_site(&f, "A").node && s.module == "A")
        .unwrap();
    let exact = f
        .sites
        .iter()
        .any(|s| matches!(&s.outcome, dictflow::Outcome::Exact(t) if t.occ == "$cshowsPrecU"));
    assert!(
        exact,
        "no site dispatched into $fShowU: {:?}",
        inner.outcome
    );
    f.accounting().check().unwrap();
}

/// One producer from a source the dump cannot see taints the parameter,
/// and the taint reaches every site downstream of it.
#[test]
fn a_tainted_producer_is_unresolved_downstream() {
    let a = wp_module_a(vec![]);
    let b = class_module(
        "B",
        vec![call_f("useB", app(gvar("g"), var("z")))],
        class_ids(vec![]),
    );
    let f = DictFlow::of_modules([&a, &b]);
    assert_eq!(
        flow_param(&f, "f").set,
        DictSet::Top(dictflow::T_UNKNOWN_CALL.into())
    );
    assert!(matches!(
        &flow_site(&f, "A").outcome,
        dictflow::Outcome::Unresolved(r) if r == dictflow::T_UNKNOWN_CALL
    ));
    f.accounting().check().unwrap();
}

/// More instances than the set budget allows: the set collapses to `Top`
/// with the budget named, and the site is Unresolved rather than a guess.
#[test]
fn exceeding_the_set_budget_is_unresolved() {
    let n = dictflow::SET_CAP + 1;
    let mut pairs = vec![(
        binder("$cshowsPrec", demand(false, false)),
        lam(&["p", "v"], var("v")),
    )];
    for i in 0..n {
        pairs.push((
            named_dict_top(
                &format!("$fShow{i}"),
                &format!("$main$A$$fShow{i}"),
                TY_SHOW_T,
            ),
            show_dict_with("$cshowsPrec"),
        ));
    }
    let (b, rhs) = show_user("$main$A$f");
    pairs.push((b, rhs));
    let a = class_module("A", pairs, class_ids(vec![]));
    let calls: Vec<(Value, Value)> = (0..n)
        .map(|i| {
            call_f(
                &format!("use{i}"),
                named_gvar(&format!("$fShow{i}"), &format!("$main$A$$fShow{i}")),
            )
        })
        .collect();
    let bm = class_module("B", calls, class_ids(vec![]));
    let f = DictFlow::of_modules([&a, &bm]);
    assert_eq!(
        flow_param(&f, "f").set,
        DictSet::Top(dictflow::B_SET.into()),
        "the {}-dictionary budget should have been exceeded",
        dictflow::SET_CAP
    );
    assert!(matches!(
        &flow_site(&f, "A").outcome,
        dictflow::Outcome::Unresolved(r) if r == dictflow::B_SET
    ));
    f.accounting().check().unwrap();
}

/// A known method target is not a removable dictionary. The target is
/// exact and the very same dictionary parameter is also handed to a callee
/// the dump cannot see, so the dictionary is preserved and the site keeps
/// dispatching on it.
#[test]
fn an_exact_target_on_an_escaping_dictionary_is_preserved() {
    // f = \$dShow x -> showsPrec $dShow (g $dShow)
    let leaky = (
        named_top("f", "$main$A$f", true),
        dict_lam(
            &[("$dShow", TY_SHOW_T)],
            lam(
                &["x"],
                app(
                    app(named_gvar("showsPrec", SHOWS_PREC), var("$dShow")),
                    app(gvar("g"), var("$dShow")),
                ),
            ),
        ),
    );
    let a = class_module(
        "A",
        vec![
            (
                named_dict_top("$fShowT", "$main$A$$fShowT", TY_SHOW_T),
                show_dict_with("$cshowsPrec"),
            ),
            (
                binder("$cshowsPrec", demand(false, false)),
                lam(&["p", "v"], var("v")),
            ),
            leaky,
        ],
        class_ids(vec![]),
    );
    let b = class_module(
        "B",
        vec![call_f("use", named_gvar("$fShowT", "$main$A$$fShowT"))],
        class_ids(vec![]),
    );
    let f = DictFlow::of_modules([&a, &b]);
    // Part 1 still resolves the method.
    assert!(
        matches!(&flow_site(&f, "A").outcome,
            dictflow::Outcome::Exact(t) if t.occ == "$cshowsPrec"),
        "{:?}",
        flow_site(&f, "A").outcome
    );
    // Part 2 refuses to erase it, and names the holder.
    let e = f
        .param_erasure
        .iter()
        .zip(&f.params)
        .find(|(_, p)| p.owner == "f")
        .map(|(e, _)| e)
        .unwrap();
    assert!(
        matches!(&e.verdict, Verdict::Preserve(h) if h.contains("outside the dump")),
        "{:?}",
        e.verdict
    );
    let acct = f.accounting();
    acct.check().unwrap();
    assert_eq!(acct.preserved_dispatch(), 1, "{:?}", acct.matrix);
}

/// Two instances at a function that is never used as a value: the
/// representation does not agree, but a clone per instance would carry it.
#[test]
fn two_instances_at_a_never_a_value_function_cost_one_clone_each() {
    let a = wp_module_a(vec![]);
    let b = class_module(
        "B",
        vec![
            call_f("useB", named_gvar("$fShowT", "$main$A$$fShowT")),
            call_f("useC", named_gvar("$fShowU", "$main$A$$fShowU")),
        ],
        class_ids(vec![]),
    );
    let f = DictFlow::of_modules([&a, &b]);
    let e = f
        .param_erasure
        .iter()
        .zip(&f.params)
        .find(|(_, p)| p.owner == "f")
        .map(|(e, _)| e)
        .unwrap();
    assert_eq!(e.verdict, Verdict::ErasableWithClone(2), "{:?}", e);
    assert_eq!(f.accounting().param_clones, 2);
    f.accounting().check().unwrap();
}

/// A top-level binder GHC has not externalised has an *internal* name, and
/// those are not unique — `ShellCheck.AST` has three top-level bindings
/// called `$_sys$$fTraversableInnerToken`. Two dictionaries that share one
/// must stay two dictionaries.
#[test]
fn two_dictionaries_sharing_an_internal_name_stay_distinct() {
    let mut p1 = dict_top("$fShowP", TY_SHOW_T, false);
    p1["name"] = json!("$_sys$$fShowX");
    let mut p2 = dict_top("$fShowQ", TY_SHOW_T, false);
    p2["name"] = json!("$_sys$$fShowX");
    let a = class_module(
        "A",
        vec![
            (p1, show_dict_with("$cA")),
            (p2, show_dict_with("$cB")),
            (
                binder("$cA", demand(false, false)),
                lam(&["p", "v"], var("v")),
            ),
            (
                binder("$cB", demand(false, false)),
                lam(&["p", "v"], var("v")),
            ),
            (
                binder("use1", demand(false, false)),
                app(
                    app(named_gvar("showsPrec", SHOWS_PREC), var("$fShowP")),
                    var("x"),
                ),
            ),
            (
                binder("use2", demand(false, false)),
                app(
                    app(named_gvar("showsPrec", SHOWS_PREC), var("$fShowQ")),
                    var("x"),
                ),
            ),
        ],
        class_ids(vec![]),
    );
    let f = DictFlow::of_modules([&a]);
    let mut targets: Vec<String> = f
        .sites
        .iter()
        .map(|s| match &s.outcome {
            dictflow::Outcome::Exact(t) => t.occ.clone(),
            other => panic!("expected Exact, got {other:?}"),
        })
        .collect();
    targets.sort();
    assert_eq!(targets, vec!["$cA".to_string(), "$cB".to_string()]);
    f.accounting().check().unwrap();
}

//------------------------------------------------------------------------------
// M2.4c' — totality is its own domain
//------------------------------------------------------------------------------

use crate::dictflow::Totality;

/// A dictionary lambda binder GHC records as strict at its binding site.
fn strict_dict_lam(params: &[(&str, u32)], body: Value) -> Value {
    let mut e = body;
    for (p, ty) in params.iter().rev() {
        let mut b = dict_lam_binder(p, *ty);
        b["demand"] = demand(true, false);
        e = json!({"node": "Lam", "binder": b, "body": e});
    }
    e
}

/// `f = \$dShow x -> showsPrec $dShow x` with a *strict* dictionary binder.
fn strict_show_user(name: &str) -> (Value, Value) {
    (
        named_top("f", name, true),
        strict_dict_lam(
            &[("$dShow", TY_SHOW_T)],
            lam(
                &["x"],
                app(
                    app(named_gvar("showsPrec", SHOWS_PREC), var("$dShow")),
                    var("x"),
                ),
            ),
        ),
    )
}

/// Module `A`, with the dictionary parameter of `f` marked strict.
fn wp_module_a_strict(extra: Vec<(Value, Value)>) -> Module {
    let mut pairs = vec![
        (
            named_dict_top("$fShowT", "$main$A$$fShowT", TY_SHOW_T),
            show_dict_with("$cshowsPrec"),
        ),
        (
            named_dict_top("$fShowU", "$main$A$$fShowU", TY_SHOW_T),
            show_dict_with("$cshowsPrecU"),
        ),
        (
            binder("$cshowsPrec", demand(false, false)),
            lam(&["p", "v"], var("v")),
        ),
        (
            binder("$cshowsPrecU", demand(false, false)),
            lam(&["p", "v"], var("v")),
        ),
    ];
    let (b, rhs) = strict_show_user("$main$A$f");
    pairs.push((b, rhs));
    pairs.extend(extra);
    class_module("A", pairs, class_ids(vec![]))
}

/// `case <scrut> of { A -> <d>; B -> <d> }` — both alternatives yield the
/// same dictionary, so the MAY-set is a singleton and says nothing.
fn case_both_alts(scrut: Value, d: Value) -> Value {
    case_alts(scrut, &[("A", vec![], d.clone()), ("B", vec![], d)])
}

/// **The counterexample the correction is for.** `f (case bottom of A -> d;
/// B -> d)`: the dictionary set is exactly `{$fShowT}`, and erasing the
/// dictionary computation would delete the divergence the selector forces.
/// Bounded identity is not totality.
#[test]
fn a_case_on_an_unevaluated_scrutinee_is_not_erasable() {
    let a = wp_module_a(vec![]);
    let b = class_module(
        "B",
        vec![call_f(
            "use",
            case_both_alts(
                app(gvar("g"), var("y")),
                named_gvar("$fShowT", "$main$A$$fShowT"),
            ),
        )],
        class_ids(vec![]),
    );
    let f = DictFlow::of_modules([&a, &b]);
    let p = flow_param(&f, "f");
    // Part 1 is unchanged: the set really is the single instance.
    assert_eq!(p.set.keys().len(), 1, "{:?}", p.set);
    // Part 2 no longer reads that as totality.
    assert_eq!(p.totality, Totality::MustPreserveForce);
    let e = &f.param_erasure[f.params.iter().position(|x| x.owner == "f").unwrap()];
    assert!(
        !matches!(e.verdict, Verdict::Erasable),
        "a forced dictionary must never be silently Erasable: {:?}",
        e.verdict
    );
    match &e.verdict {
        Verdict::ErasableWithObligation(o) => assert_eq!(o.module, "B"),
        Verdict::Preserve(r) => assert_eq!(r, dictflow::R_FORCE),
        other => panic!("expected an obligation or Preserve(force), got {other:?}"),
    }
    f.accounting().check().unwrap();
}

/// A producer through a call the dump cannot see has unknown totality —
/// not `ProvenTotal`, and not a permission to erase.
#[test]
fn a_producer_through_an_unknown_call_has_unknown_totality() {
    let a = wp_module_a(vec![]);
    let b = class_module(
        "B",
        vec![(
            binder("use", demand(false, false)),
            let_ty_ix(
                "d",
                "Show T",
                TY_SHOW_T,
                app(gvar("g"), var("y")),
                app(app(named_gvar("f", "$main$A$f"), var("d")), var("y")),
            ),
        )],
        class_ids(vec![]),
    );
    let f = DictFlow::of_modules([&a, &b]);
    let p = flow_param(&f, "f");
    assert_eq!(p.totality, Totality::Unknown);
    let e = &f.param_erasure[f.params.iter().position(|x| x.owner == "f").unwrap()];
    assert!(
        !matches!(e.verdict, Verdict::Erasable | Verdict::ErasableWithClone(_)),
        "{:?}",
        e.verdict
    );
    f.accounting().check().unwrap();
}

/// A dfun application is a value: `ProvenTotal`, and the dictionary is
/// erasable exactly as before.
#[test]
fn a_dfun_application_is_proven_total() {
    // $fShowL = \$dShow -> C:Show $cshowsPrec $cshow $cshowList
    let dfun = (
        named_dict_top("$fShowL", "$main$A$$fShowL", TY_SHOW_T),
        dict_lam(&[("$dShow", TY_SHOW_T)], show_dict_with("$cshowsPrec")),
    );
    let a = wp_module_a(vec![dfun]);
    let b = class_module(
        "B",
        vec![call_f(
            "use",
            app(
                named_gvar("$fShowL", "$main$A$$fShowL"),
                named_gvar("$fShowT", "$main$A$$fShowT"),
            ),
        )],
        class_ids(vec![]),
    );
    let f = DictFlow::of_modules([&a, &b]);
    let p = flow_param(&f, "f");
    assert_eq!(p.totality, Totality::ProvenTotal);
    let e = &f.param_erasure[f.params.iter().position(|x| x.owner == "f").unwrap()];
    assert_eq!(e.verdict, Verdict::Erasable);
    f.accounting().check().unwrap();
}

/// A strict parameter all of whose producers are proven total is Erasable —
/// on the totality, not on the strictness.
#[test]
fn a_strict_parameter_with_total_producers_is_erasable() {
    let a = wp_module_a_strict(vec![]);
    let b = class_module(
        "B",
        vec![call_f("use", named_gvar("$fShowT", "$main$A$$fShowT"))],
        class_ids(vec![]),
    );
    let f = DictFlow::of_modules([&a, &b]);
    let p = flow_param(&f, "f");
    assert!(p.known_strict);
    assert_eq!(p.totality, Totality::ProvenTotal);
    let e = &f.param_erasure[f.params.iter().position(|x| x.owner == "f").unwrap()];
    assert_eq!(e.verdict, Verdict::Erasable);
    assert!(e.known_strict, "strictness is reported as evidence");
    f.accounting().check().unwrap();
}

/// …and the same strict parameter with **one** forced producer is not.
/// Strictness at entry is not permission to drop the force: if the
/// parameter disappears the entry force must still happen somewhere.
#[test]
fn a_strict_parameter_with_one_forced_producer_keeps_the_force() {
    let a = wp_module_a_strict(vec![]);
    let b = class_module(
        "B",
        vec![call_f("useB", named_gvar("$fShowT", "$main$A$$fShowT"))],
        class_ids(vec![]),
    );
    let c = class_module(
        "C",
        vec![call_f(
            "useC",
            case_both_alts(
                app(gvar("g"), var("y")),
                named_gvar("$fShowT", "$main$A$$fShowT"),
            ),
        )],
        class_ids(vec![]),
    );
    let f = DictFlow::of_modules([&a, &b, &c]);
    let p = flow_param(&f, "f");
    assert!(p.known_strict);
    assert_eq!(p.set.keys().len(), 1, "{:?}", p.set);
    assert_eq!(p.totality, Totality::MustPreserveForce);
    let e = &f.param_erasure[f.params.iter().position(|x| x.owner == "f").unwrap()];
    match &e.verdict {
        Verdict::ErasableWithObligation(o) => assert_eq!(o.module, "C"),
        Verdict::Preserve(r) => assert_eq!(r, dictflow::R_FORCE),
        other => panic!("expected an obligation or Preserve(force), got {other:?}"),
    }
    f.accounting().check().unwrap();
}

/// Owner-level clone planning: one function, two dictionary parameters,
/// three call sites that use only **two** distinct assignment tuples. The
/// per-parameter cardinalities are 2 and 2; the clone count is 2 — neither
/// their sum (4) nor their product (4).
#[test]
fn clones_are_the_distinct_call_site_tuples_not_a_sum_or_a_product() {
    // f2 = \$dShow1 $dShow2 x -> showsPrec $dShow1 x
    let f2 = (
        named_top("f2", "$main$A$f2", true),
        dict_lam(
            &[("$dShow1", TY_SHOW_T), ("$dShow2", TY_SHOW_T)],
            lam(
                &["x"],
                app(
                    app(named_gvar("showsPrec", SHOWS_PREC), var("$dShow1")),
                    var("x"),
                ),
            ),
        ),
    );
    let a = wp_module_a(vec![f2]);
    let call = |occ: &str, d1: &str, d2: &str| {
        (
            binder(occ, demand(false, false)),
            app(
                app(
                    app(
                        named_gvar("f2", "$main$A$f2"),
                        named_gvar(d1, &format!("$main$A$${d1}")),
                    ),
                    named_gvar(d2, &format!("$main$A$${d2}")),
                ),
                var("y"),
            ),
        )
    };
    let b = class_module(
        "B",
        vec![
            call("useTT", "fShowT", "fShowT"),
            call("useUU", "fShowU", "fShowU"),
            // A third call site that repeats the first tuple.
            call("useTT2", "fShowT", "fShowT"),
        ],
        class_ids(vec![]),
    );
    let f = DictFlow::of_modules([&a, &b]);
    let plan = f
        .owners
        .iter()
        .find(|o| o.owner == "f2")
        .expect("no clone plan for f2");
    assert_eq!(plan.params.len(), 2);
    assert_eq!(plan.cardinalities, vec![2, 2]);
    assert_eq!(plan.clones, Some(2), "{:?}", plan.tuples);
    assert_eq!(f.accounting().owner_clones, 2);
    f.accounting().check().unwrap();
}

//------------------------------------------------------------------------------
// Higher-order representation agreement (higher.rs)
//------------------------------------------------------------------------------

use crate::higher::Verdict as HVerdict;
use crate::higher::{self, Higher, ProducerKind, Program, Shape, Slot};

/// A binder of the given function type.
fn fn_binder(occ: &str, ty: u32) -> Value {
    let mut b = binder(occ, demand(false, false));
    b["ty"] = json!(ty);
    b["type"] = json!("fn");
    b
}

/// A lambda binder of the given function type: a function-valued parameter.
fn fn_lam_binder(occ: &str, ty: u32) -> Value {
    let mut b = lam_binder(occ, false);
    b["ty"] = json!(ty);
    b["type"] = json!("fn");
    b
}

/// A lambda chain whose parameters carry the given types (`None` for the
/// fixtures' plain `T`).
fn typed_lam(params: &[(&str, Option<u32>)], body: Value) -> Value {
    let mut e = body;
    for (p, ty) in params.iter().rev() {
        let b = match ty {
            Some(t) => fn_lam_binder(p, *t),
            None => lam_binder(p, false),
        };
        e = json!({"node": "Lam", "binder": b, "body": e});
    }
    e
}

/// A top-level binder with a stable name and a function type.
fn named_fn_top(occ: &str, name: &str, ty: u32, exported: bool) -> Value {
    let mut b = fn_binder(occ, ty);
    b["name"] = json!(name);
    b["exported"] = json!(exported);
    b
}

/// `f = \k x -> k x`, whose parameter 0 is the function-valued slot every
/// fixture below asks about. `name` is its stable name so other modules can
/// call it.
fn f_takes_a_closure(name: &str, exported: bool) -> (Value, Value) {
    (
        named_fn_top("f", name, TY_FUN2, exported),
        typed_lam(
            &[("k", Some(TY_FUN1)), ("x", None)],
            app(var("k"), var("x")),
        ),
    )
}

const F_NAME: &str = "$main$A$f";

/// `use<n> = f <closure> a`, calling `A.f` from wherever it is put.
fn call_hf(occ: &str, closure: Value) -> (Value, Value) {
    (
        binder(occ, demand(false, false)),
        app(app(named_gvar("f", F_NAME), closure), var("a")),
    )
}

fn higher_of(mods: &[&Module]) -> Higher {
    let p = Program::new(mods.iter().copied());
    Higher::of_program(&p)
}

/// The boundary of parameter `index` of the named function.
fn param_boundary<'a>(h: &'a Higher, owner: &str, index: usize) -> &'a higher::Boundary {
    h.boundaries
        .iter()
        .find(|b| {
            b.owner == owner
                && matches!(b.slot, Slot::Param { .. })
                && b.name.starts_with(&format!("parameter {index} "))
        })
        .unwrap_or_else(|| panic!("no parameter {index} boundary on {owner}"))
}

/// Two lambdas of the same arity, from two different modules, into one
/// parameter: neither module could say this on its own, and one
/// representation serves the slot.
#[test]
fn two_lambdas_of_one_arity_share_one_representation() {
    let a = class_module(
        "A",
        vec![f_takes_a_closure(F_NAME, false)],
        class_ids(vec![]),
    );
    let b = class_module(
        "B",
        vec![call_hf("useB", lam(&["y"], var("y")))],
        class_ids(vec![]),
    );
    let c = class_module(
        "C",
        vec![call_hf("useC", lam(&["z"], var("z")))],
        class_ids(vec![]),
    );
    let h = higher_of(&[&a, &b, &c]);
    let k = param_boundary(&h, "f", 0);
    assert_eq!(k.producers.len(), 2, "{:?}", k.set);
    assert!(k.enumerated);
    assert_eq!(k.classes, 1);
    assert_eq!(k.verdict, HVerdict::TypeShapeUniform);
    h.accounting().check().unwrap();
}

/// The same parameter, but the two lambdas take different numbers of
/// arguments. At a local function that is never used as a value, one clone
/// per shape class carries them; the clones are counted, never made.
#[test]
fn lambdas_of_different_arities_need_a_clone() {
    let a = class_module(
        "A",
        vec![f_takes_a_closure(F_NAME, false)],
        class_ids(vec![]),
    );
    let b = class_module(
        "B",
        vec![
            call_hf("useB", lam(&["y"], var("y"))),
            call_hf("useC", lam(&["y", "z"], var("y"))),
        ],
        class_ids(vec![]),
    );
    let h = higher_of(&[&a, &b]);
    let k = param_boundary(&h, "f", 0);
    assert!(k.enumerated, "the set is still enumerated: {:?}", k.set);
    assert_eq!(k.classes, 2);
    assert_eq!(k.verdict, HVerdict::CloneRequired(2));
    // The per-parameter class count is evidence; the clone count is the
    // owning function's distinct call-site tuples (H15-OWNER-CLONES).
    assert_eq!(h.accounting().clone_classes, 2);
    assert_eq!(h.accounting().owner_clones, 2);
}

/// The same disagreement at an *exported* function: its representation is
/// shared with callers the rewrite does not own, so there is no clone —
/// the closure is preserved, and the holder is named.
#[test]
fn a_disagreement_at_an_exported_boundary_is_preserved() {
    let a = class_module(
        "A",
        vec![f_takes_a_closure(F_NAME, true)],
        class_ids(vec![]),
    );
    let b = class_module(
        "B",
        vec![
            call_hf("useB", lam(&["y"], var("y"))),
            call_hf("useC", lam(&["y", "z"], var("y"))),
        ],
        class_ids(vec![]),
    );
    let h = higher_of(&[&a, &b]);
    let k = param_boundary(&h, "f", 0);
    assert_eq!(k.classes, 2);
    match &k.verdict {
        HVerdict::Preserve(why) => assert!(why.contains(higher::P_EXPORTED), "{why}"),
        other => panic!("expected Preserve, got {other:?}"),
    }
}

/// A closure read back out of a constructor field has been through a data
/// representation: its environment is not visible, so the slot it reaches
/// keeps a run-time closure.
#[test]
fn a_closure_read_from_a_field_is_preserved() {
    let a = class_module(
        "A",
        vec![f_takes_a_closure(F_NAME, false)],
        class_ids(vec![]),
    );
    // useB = case d of MkC h -> f h a
    let read = (
        binder("useB", demand(false, false)),
        json!({
            "node": "Case", "scrut": var("d"),
            "binder": binder("wild", demand(false, false)), "type": "R", "ty": TY_R,
            "alts": [{
                "con": {"kind": "DataAlt", "name": "$main$B$MkC", "occ": "MkC", "tag": 1},
                "binders": [fn_binder("h", TY_FUN1)],
                "rhs": app(app(named_gvar("f", F_NAME), var("h")), var("a"))
            }]
        }),
    );
    let mut ids = class_ids(vec![(
        "$main$B$MkC".to_string(),
        data_con("MkC", "$main$B$MkC", 1),
    )]);
    ids["MkC"] = json!(data_con("MkC", "$main$B$MkC", 1));
    let b = class_module("B", vec![read], ids);
    let h = higher_of(&[&a, &b]);
    let k = param_boundary(&h, "f", 0);
    assert_eq!(k.producers.len(), 1);
    assert_eq!(k.producers[0].kind, ProducerKind::FieldRead);
    assert!(k.producers[0].shape.is_opaque());
    match &k.verdict {
        HVerdict::Preserve(why) => assert!(why.contains(higher::P_FIELD_READ), "{why}"),
        other => panic!("expected Preserve, got {other:?}"),
    }
}

/// A partial application and a lambda that take the same number of further
/// arguments and capture the same type are one shape class.
#[test]
fn a_pap_and_a_lambda_of_equal_arity_and_capture_agree() {
    let a = class_module(
        "A",
        vec![f_takes_a_closure(F_NAME, false)],
        class_ids(vec![]),
    );
    // p = \u v -> v; useB = \x -> f (p x) a; useC = \x -> f (\y -> x) a
    let b = class_module(
        "B",
        vec![
            (
                binder("p", demand(false, false)),
                lam(&["u", "v"], var("v")),
            ),
            (
                binder("useB", demand(false, false)),
                lam(
                    &["x"],
                    app(
                        app(named_gvar("f", F_NAME), app(var("p"), var("x"))),
                        var("a"),
                    ),
                ),
            ),
            (
                binder("useC", demand(false, false)),
                lam(
                    &["x"],
                    app(
                        app(named_gvar("f", F_NAME), lam(&["y"], var("x"))),
                        var("a"),
                    ),
                ),
            ),
        ],
        class_ids(vec![]),
    );
    let h = higher_of(&[&a, &b]);
    let k = param_boundary(&h, "f", 0);
    assert_eq!(k.producers.len(), 2, "{:?}", k.producers);
    let kinds: Vec<ProducerKind> = k.producers.iter().map(|x| x.kind).collect();
    assert!(
        kinds.contains(&ProducerKind::PartialApplication),
        "{kinds:?}"
    );
    assert!(kinds.contains(&ProducerKind::Lambda), "{kinds:?}");
    assert_eq!(k.arity, Some(1));
    assert_eq!(k.classes, 1);
    assert_eq!(k.verdict, HVerdict::TypeShapeUniform);
}

/// A parameter handed straight on to another function's parameter: the
/// second slot's producer set is the first's, not an unknown.
#[test]
fn a_parameter_passed_on_propagates_to_the_next_slot() {
    // f = \k x -> g k x; g = \k2 y -> k2 y; useB = f (\y -> y) a
    let a = class_module(
        "A",
        vec![
            (
                named_fn_top("f", F_NAME, TY_FUN2, false),
                typed_lam(
                    &[("k", Some(TY_FUN1)), ("x", None)],
                    app(app(var("g"), var("k")), var("x")),
                ),
            ),
            (
                named_fn_top("g", "$main$A$g", TY_FUN2, false),
                typed_lam(
                    &[("k2", Some(TY_FUN1)), ("y", None)],
                    app(var("k2"), var("y")),
                ),
            ),
        ],
        class_ids(vec![]),
    );
    let b = class_module(
        "B",
        vec![call_hf("useB", lam(&["y"], var("y")))],
        class_ids(vec![]),
    );
    let h = higher_of(&[&a, &b]);
    let k2 = param_boundary(&h, "g", 0);
    assert_eq!(k2.producers.len(), 1, "{:?}", k2.set);
    assert_eq!(k2.producers[0].kind, ProducerKind::Lambda);
    assert_eq!(k2.verdict, HVerdict::ExactClosure);
    // …and the slot it came through says the same.
    assert_eq!(param_boundary(&h, "f", 0).verdict, HVerdict::ExactClosure);
}

/// A function used as a value has no enumerable set of call sites, so no
/// slot of it can be resolved — the same refusal `boundary.rs` and
/// `dictflow.rs` make.
#[test]
fn a_function_used_as_a_value_makes_its_slots_unresolved() {
    let a = class_module(
        "A",
        vec![f_takes_a_closure(F_NAME, false)],
        class_ids(vec![]),
    );
    let b = class_module(
        "B",
        vec![
            call_hf("useB", lam(&["y"], var("y"))),
            // `h f`: the function itself is handed somewhere.
            (
                binder("useC", demand(false, false)),
                app(gvar("h"), named_gvar("f", F_NAME)),
            ),
        ],
        class_ids(vec![]),
    );
    let h = higher_of(&[&a, &b]);
    let k = param_boundary(&h, "f", 0);
    assert!(!k.enumerated);
    match &k.verdict {
        HVerdict::Unresolved(r) => assert_eq!(r, higher::T_USED_AS_A_VALUE),
        other => panic!("expected Unresolved, got {other:?}"),
    }
}

/// More distinct closures than the set budget allows: the set collapses to
/// `Top` with the budget as the reason, and the boundary is `Unresolved`
/// rather than a guess.
#[test]
fn exhausting_the_set_budget_is_unresolved() {
    let a = class_module(
        "A",
        vec![f_takes_a_closure(F_NAME, false)],
        class_ids(vec![]),
    );
    let calls: Vec<(Value, Value)> = (0..higher::SET_CAP + 4)
        .map(|i| {
            call_hf(
                &format!("use{i}"),
                lam(&[&format!("y{i}")], var(&format!("y{i}"))),
            )
        })
        .collect();
    let b = class_module("B", calls, class_ids(vec![]));
    let h = higher_of(&[&a, &b]);
    let k = param_boundary(&h, "f", 0);
    assert!(!k.enumerated);
    match &k.verdict {
        HVerdict::Unresolved(r) => assert_eq!(r, higher::B_SET),
        other => panic!("expected Unresolved(budget), got {other:?}"),
    }
    assert_eq!(
        k.classes, 0,
        "an unenumerated set has no representation count"
    );
}

/// The two facts stay apart: a boundary can be perfectly enumerated and
/// still need more than one representation.
#[test]
fn enumeration_and_one_representation_are_separate_facts() {
    let a = class_module(
        "A",
        vec![f_takes_a_closure(F_NAME, false)],
        class_ids(vec![]),
    );
    let b = class_module(
        "B",
        vec![
            call_hf("useB", lam(&["y"], var("y"))),
            call_hf("useC", lam(&["y", "z"], var("y"))),
        ],
        class_ids(vec![]),
    );
    let h = higher_of(&[&a, &b]);
    let k = param_boundary(&h, "f", 0);
    assert!(k.enumerated && k.classes > 1);
    assert!(!k.verdict.rewritable_as_one());
    assert!(!k.one_representation());
    assert_eq!(
        h.accounting().one_representation,
        h.boundaries
            .iter()
            .filter(|b| b.one_representation())
            .count(),
        "the accounting and the method must state ONE theorem"
    );
    let acct = h.accounting();
    assert!(acct.enumerated >= 1);
    acct.check().unwrap();
}

/// `verdict_for` is the API M2.4e calls: a module and a binder, and the
/// boundary that binder names.
#[test]
fn verdict_for_finds_a_slot_by_its_binder() {
    let a = class_module(
        "A",
        vec![f_takes_a_closure(F_NAME, false)],
        class_ids(vec![]),
    );
    let b = class_module(
        "B",
        vec![call_hf("useB", lam(&["y"], var("y")))],
        class_ids(vec![]),
    );
    let h = higher_of(&[&a, &b]);
    let k = param_boundary(&h, "f", 0);
    let Slot::Param { binder, .. } = k.slot else {
        panic!("not a parameter")
    };
    let found = h
        .verdict_for("A", binder)
        .expect("no verdict for the binder");
    assert_eq!(found.verdict, HVerdict::ExactClosure);
    assert!(h.verdict_for("B", binder).is_none());
}

/// The shape-class key is alpha-equivalence, and nothing else: two types
/// agree on a key exactly when `Ty::alpha_eq` accepts them.
#[test]
fn the_shape_class_key_is_alpha_equivalence() {
    let m = class_module(
        "A",
        vec![f_takes_a_closure(F_NAME, false)],
        class_ids(vec![]),
    );
    for i in 0..m.types.len() {
        for j in 0..m.types.len() {
            assert_eq!(
                higher::ty_key(&m.types[i]) == higher::ty_key(&m.types[j]),
                m.types[i].alpha_eq(&m.types[j]),
                "types {i} and {j} disagree"
            );
        }
    }
}

/// A slot whose type is not a `FunTy` is not a boundary at all: the
/// population is decided by the structured type (`H1-FUNCTION-TYPED`) and
/// never by what a name or a use suggests.
#[test]
fn only_function_typed_slots_are_boundaries() {
    let a = class_module(
        "A",
        vec![f_takes_a_closure(F_NAME, false)],
        class_ids(vec![]),
    );
    let h = higher_of(&[&a]);
    // `f`'s second parameter `x` is plain `T`.
    assert!(
        !h.boundaries
            .iter()
            .any(|b| b.owner == "f" && b.name.starts_with("parameter 1 ")),
        "a non-function-typed parameter was registered as a boundary"
    );
    assert!(matches!(
        param_boundary(&h, "f", 0).slot,
        Slot::Param { .. }
    ));
}

/// A producer's shape records its captures: a lambda that reads an
/// enclosing parameter is not the same representation as one that reads
/// nothing.
#[test]
fn a_capture_changes_the_shape_class() {
    let a = class_module(
        "A",
        vec![f_takes_a_closure(F_NAME, false)],
        class_ids(vec![]),
    );
    let b = class_module(
        "B",
        vec![
            call_hf("useB", lam(&["y"], var("y"))),
            (
                binder("useC", demand(false, false)),
                lam(
                    &["x"],
                    app(
                        app(named_gvar("f", F_NAME), lam(&["y"], var("x"))),
                        var("a"),
                    ),
                ),
            ),
        ],
        class_ids(vec![]),
    );
    let h = higher_of(&[&a, &b]);
    let k = param_boundary(&h, "f", 0);
    assert_eq!(k.producers.len(), 2);
    assert_eq!(k.classes, 2, "{:?}", k.class_keys());
    let caps: Vec<usize> = k
        .producers
        .iter()
        .map(|x| match &x.shape {
            Shape::Known { captures, .. } => captures.len(),
            Shape::Opaque { .. } => usize::MAX,
        })
        .collect();
    assert!(caps.contains(&0) && caps.contains(&1), "{caps:?}");
}

/// **H8 before H5.** An exported boundary with exactly ONE producer is
/// still shared with callers the rewrite does not own: sharing is decided
/// before agreement, so this is `Preserve`, not `ExactClosure`.
#[test]
fn an_exported_boundary_with_one_producer_is_preserved() {
    let a = class_module(
        "A",
        vec![f_takes_a_closure(F_NAME, true)],
        class_ids(vec![]),
    );
    let b = class_module(
        "B",
        vec![call_hf("useB", lam(&["y"], var("y")))],
        class_ids(vec![]),
    );
    let h = higher_of(&[&a, &b]);
    let k = param_boundary(&h, "f", 0);
    assert_eq!(k.producers.len(), 1);
    assert_eq!(k.classes, 1);
    // The representation FACT still holds; the rewrite just does not own
    // the slot.
    assert!(k.one_representation());
    assert!(!k.verdict.rewritable_as_one());
    match &k.verdict {
        HVerdict::Preserve(why) => assert!(why.contains(higher::P_EXPORTED), "{why}"),
        other => panic!("expected Preserve, got {other:?}"),
    }
}

/// **H8 before H6.** The same at an exported boundary whose two producers
/// fall in ONE shape class.
#[test]
fn an_exported_boundary_with_one_shape_class_is_preserved() {
    let a = class_module(
        "A",
        vec![f_takes_a_closure(F_NAME, true)],
        class_ids(vec![]),
    );
    let b = class_module(
        "B",
        vec![
            call_hf("useB", lam(&["y"], var("y"))),
            call_hf("useC", lam(&["z"], var("z"))),
        ],
        class_ids(vec![]),
    );
    let h = higher_of(&[&a, &b]);
    let k = param_boundary(&h, "f", 0);
    assert_eq!(k.producers.len(), 2);
    assert_eq!(k.classes, 1);
    assert!(k.one_representation());
    match &k.verdict {
        HVerdict::Preserve(why) => assert!(why.contains(higher::P_EXPORTED), "{why}"),
        other => panic!("expected Preserve, got {other:?}"),
    }
}

/// **H8 before H5/H6, the `valued` half.** A function that is also used as
/// a value has holders the rewrite cannot rewrite, so the closure it
/// returns is preserved even though both its producers fall in one shape
/// class.
#[test]
fn a_valued_boundary_is_preserved_whatever_its_producers_agree_on() {
    const R_NAME: &str = "$main$A$r";
    // p and q are one-argument functions; r = \x -> case x of A -> p ; B -> q
    // returns one of them, so both producers are known functions of one
    // shape class.
    let a = class_module(
        "A",
        vec![
            (
                named_fn_top("p", "$main$A$p", TY_FUN1, false),
                lam(&["u"], var("u")),
            ),
            (
                named_fn_top("q", "$main$A$q", TY_FUN1, false),
                lam(&["v"], var("v")),
            ),
            (
                named_fn_top("r", R_NAME, TY_FUN2, false),
                typed_lam(
                    &[("x", None)],
                    case2(
                        var("x"),
                        named_gvar("p", "$main$A$p"),
                        named_gvar("q", "$main$A$q"),
                    ),
                ),
            ),
        ],
        class_ids(vec![]),
    );
    // B calls it, and also hands it to `g` as a value.
    let b = class_module(
        "B",
        vec![
            (
                binder("useB", demand(false, false)),
                app(named_gvar("r", R_NAME), var("a")),
            ),
            (
                binder("useV", demand(false, false)),
                app(var("g"), named_gvar("r", R_NAME)),
            ),
        ],
        class_ids(vec![]),
    );
    let h = higher_of(&[&a, &b]);
    let k = h
        .boundaries
        .iter()
        .find(|x| matches!(x.slot, Slot::Return { .. }) && x.owner == "r")
        .expect("no return boundary for r");
    assert_eq!(k.producers.len(), 2, "{:?}", k.producers);
    assert_eq!(k.classes, 1, "{:?}", k.class_keys());
    // One representation is a fact about the producers; it does not make
    // the slot the rewrite's to change.
    assert!(k.one_representation());
    assert!(!k.verdict.rewritable_as_one());
    match &k.verdict {
        HVerdict::Preserve(why) => assert!(why.contains(higher::P_VALUED), "{why}"),
        other => panic!("expected Preserve, got {other:?}"),
    }
}

/// **H14.** Two closures in two different modules whose captured type is a
/// FREE type variable that happens to carry the same GHC unique are NOT
/// one shape class: a free variable's unique is neither module- nor
/// scope-qualified, so it identifies nothing across producers.
#[test]
fn free_type_variables_with_one_unique_do_not_merge_two_closures() {
    // \x::a -> f (\y -> x) a, with `x` of the free type variable `a`.
    let capture_call = |occ: &str| {
        let mut xb = lam_binder("x", false);
        xb["ty"] = json!(TY_A);
        xb["type"] = json!("a");
        (
            binder(occ, demand(false, false)),
            json!({
                "node": "Lam", "binder": xb,
                "body": app(
                    app(named_gvar("f", F_NAME), lam(&["y"], var("x"))),
                    var("a"),
                )
            }),
        )
    };
    let a = class_module(
        "A",
        vec![f_takes_a_closure(F_NAME, false)],
        class_ids(vec![]),
    );
    let b = class_module("B", vec![capture_call("useB")], class_ids(vec![]));
    let c = class_module("C", vec![capture_call("useC")], class_ids(vec![]));
    let h = higher_of(&[&a, &b, &c]);
    let k = param_boundary(&h, "f", 0);
    assert_eq!(k.producers.len(), 2, "{:?}", k.producers);
    // Same arity, one capture each, and the capture types are written
    // identically — `a` in both tables, with the same unique.
    assert_eq!(
        higher::ty_key(&b.types[TY_A as usize]),
        higher::ty_key(&c.types[TY_A as usize])
    );
    assert_eq!(
        k.classes,
        2,
        "two unrelated free type variables merged two closures into one class: {:?}",
        k.class_keys()
    );
    assert!(!k.one_representation());
}

/// **H2, value-field indexing.** An existential constructor binds its type
/// variable first; the runtime fields are still numbered from zero. A
/// function-typed binder after a type binder must be paired with the
/// constructor argument it is really read from.
#[test]
fn an_existential_type_binder_does_not_shift_the_field_index() {
    // A: f as before, plus `MkE` with one runtime field.
    let a = class_module(
        "A",
        vec![f_takes_a_closure(F_NAME, false)],
        class_ids(vec![]),
    );
    // B builds `MkE (\y -> y)` and matches it as `MkE @a h`, handing `h`
    // to `f`. The binder `h` is raw position 1 and value field 0.
    let mut tyb = binder("tv", demand(false, false));
    tyb["kind"] = json!("tyvar");
    let read = (
        binder("useB", demand(false, false)),
        json!({
            "node": "Case", "scrut": app(named_gvar("MkE", "$main$B$MkE"), lam(&["w"], var("w"))),
            "binder": binder("wild", demand(false, false)), "type": "R", "ty": TY_R,
            "alts": [{
                "con": {"kind": "DataAlt", "name": "$main$B$MkE", "occ": "MkE", "tag": 1},
                "binders": [tyb, fn_binder("h", TY_FUN1)],
                "rhs": app(app(named_gvar("f", F_NAME), var("h")), var("a"))
            }]
        }),
    );
    let mut ids = class_ids(vec![(
        "$main$B$MkE".to_string(),
        data_con("MkE", "$main$B$MkE", 1),
    )]);
    ids["MkE"] = json!(data_con("MkE", "$main$B$MkE", 1));
    let b = class_module("B", vec![read], ids);
    let h = higher_of(&[&a, &b]);
    let field = h
        .boundaries
        .iter()
        .find(|x| matches!(&x.slot, Slot::Field { con, .. } if con == "$main$B$MkE"))
        .expect("no field boundary for MkE");
    let Slot::Field { index, .. } = &field.slot else {
        unreachable!()
    };
    assert_eq!(*index, 0, "the type binder shifted the value-field index");
    // And the field really resolves to the closure that was stored there.
    assert_eq!(field.producers.len(), 1, "{:?}", field.producers);
    assert_eq!(field.producers[0].kind, ProducerKind::Lambda);
}

/// **H15.** A function with TWO function-valued parameters, called from
/// three sites, is cloned once per distinct call-site tuple — three sites,
/// two distinct tuples — and never once per parameter class, which would
/// say four.
#[test]
fn clones_are_the_owner_s_distinct_call_site_tuples() {
    const G2: &str = "$main$A$g2";
    // g2 = \k1 k2 x -> k1 x
    let a = class_module(
        "A",
        vec![(
            named_fn_top("g2", G2, TY_FUN2, false),
            typed_lam(
                &[("k1", Some(TY_FUN1)), ("k2", Some(TY_FUN1)), ("x", None)],
                app(var("k1"), var("x")),
            ),
        )],
        class_ids(vec![]),
    );
    let call = |occ: &str, k1: Value, k2: Value| {
        (
            binder(occ, demand(false, false)),
            app(app(app(named_gvar("g2", G2), k1), k2), var("a")),
        )
    };
    // Two of the three call sites assign the SAME pair of shapes.
    let b = class_module(
        "B",
        vec![
            call("u1", lam(&["y"], var("y")), lam(&["y", "z"], var("y"))),
            call("u2", lam(&["p"], var("p")), lam(&["p", "q"], var("p"))),
            call("u3", lam(&["r", "s"], var("r")), lam(&["t"], var("t"))),
        ],
        class_ids(vec![]),
    );
    let h = higher_of(&[&a, &b]);
    let k1 = param_boundary(&h, "g2", 0);
    let k2 = param_boundary(&h, "g2", 1);
    assert_eq!(k1.classes, 2, "{:?}", k1.class_keys());
    assert_eq!(k2.classes, 2, "{:?}", k2.class_keys());
    let plan = h
        .owners
        .iter()
        .find(|o| o.owner == "g2")
        .expect("no clone plan for g2");
    assert_eq!(plan.params.len(), 2);
    assert_eq!(plan.classes, vec![2, 2]);
    assert_eq!(plan.sites, 3);
    assert_eq!(plan.clones, Some(2), "{:?}", plan.tuples);
    let a2 = h.accounting();
    // NOT the sum of the per-parameter counts, which is 4.
    assert_eq!(a2.clone_classes, 4);
    assert_eq!(a2.owner_clones, 2);
    a2.check().unwrap();
}

/// **The one-representation theorem is stated once.** A lone opaque
/// producer is a class of one and still not a representation anything can
/// share, so the fact and the accounting agree on excluding it.
#[test]
fn a_lone_opaque_producer_is_not_one_representation() {
    let a = class_module(
        "A",
        vec![f_takes_a_closure(F_NAME, false)],
        class_ids(vec![]),
    );
    // useB = case d of MkC h -> f h a: the one producer is a field read.
    let read = (
        binder("useB", demand(false, false)),
        json!({
            "node": "Case", "scrut": var("d"),
            "binder": binder("wild", demand(false, false)), "type": "R", "ty": TY_R,
            "alts": [{
                "con": {"kind": "DataAlt", "name": "$main$B$MkC", "occ": "MkC", "tag": 1},
                "binders": [fn_binder("h", TY_FUN1)],
                "rhs": app(app(named_gvar("f", F_NAME), var("h")), var("a"))
            }]
        }),
    );
    let mut ids = class_ids(vec![(
        "$main$B$MkC".to_string(),
        data_con("MkC", "$main$B$MkC", 1),
    )]);
    ids["MkC"] = json!(data_con("MkC", "$main$B$MkC", 1));
    let b = class_module("B", vec![read], ids);
    let h = higher_of(&[&a, &b]);
    let k = param_boundary(&h, "f", 0);
    assert_eq!(k.producers.len(), 1);
    assert!(k.producers[0].shape.is_opaque());
    assert!(!k.one_representation(), "an opaque shape shares nothing");
    let acct = h.accounting();
    assert_eq!(
        acct.one_representation,
        h.boundaries
            .iter()
            .filter(|b| b.one_representation())
            .count()
    );
    acct.check().unwrap();
}
