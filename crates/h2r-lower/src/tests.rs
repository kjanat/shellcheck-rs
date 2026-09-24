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
    assert!(
        matches!(&instruction.operation, Operation::Literal(lit) if lit.number("Int") == Ok(0))
    );
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
        let expected_source = match m.expr(pair.rhs) {
            h2r_core_ir::Expr::App { fun, .. } => *fun,
            _ => pair.rhs,
        };
        assert_eq!(error.source, Some(expected_source));
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
            .contains("returned reference type mismatch")
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
        vec![(
            binder(&sn("Main", "f"), "f", "f"),
            gvar("$base$M$external", "external"),
        )],
        json!({}),
    );
    assert!(
        lower_leaf(&m, 0, m.top[0].pairs[0].binder, FnId(0))
            .unwrap_err()
            .reason
            .contains("external references")
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
    candidate.function.blocks[0].params[0].ty = crate::nir::shared(&forged);
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

#[test]
fn nir_preserves_top_reference_identity_without_forcing() {
    use crate::nir::{FnId, Operation, Rule, lower::lower_leaf, verify::verify_leaf};
    let m = module(
        "Main",
        vec![
            (binder(&sn("Main", "f"), "f", "f"), lvar("g")),
            (binder("$_in$same", "same", "g"), lit()),
            (binder("$_in$same", "same", "h"), lit()),
        ],
        json!({}),
    );
    let owner = m.top[0].pairs[0].binder;
    let target = m.top[1].pairs[0].binder;
    let leaf = lower_leaf(&m, 5, owner, FnId(10)).unwrap();
    let block = &leaf.function.blocks[0];
    assert_eq!(block.instructions.len(), 1);
    assert!(
        matches!(block.instructions[0].operation, Operation::TopReference { module: 5, binder, .. } if binder == target)
    );
    assert_eq!(block.instructions[0].origin.rule, Rule::TopReference);
    assert_eq!(
        verify_leaf(&m, 5, owner, FnId(10), &leaf)
            .unwrap()
            .source_nodes,
        1
    );
}

#[test]
fn nir_top_reference_verifier_rejects_wrong_targets_and_operations() {
    use crate::nir::{
        FnId, Operation, Rule, Source,
        lower::lower_leaf,
        verify::{verify, verify_leaf},
    };
    let m = module(
        "Main",
        vec![
            (binder(&sn("Main", "f"), "f", "f"), lvar("g")),
            (binder(&sn("Main", "g"), "g", "g"), lit()),
            (binder(&sn("Main", "h"), "h", "h"), lit()),
        ],
        json!({}),
    );
    let owner = m.top[0].pairs[0].binder;
    let target = m.top[1].pairs[0].binder;
    let other = m.top[2].pairs[0].binder;
    let original = lower_leaf(&m, 0, owner, FnId(0)).unwrap();
    for corruption in 0..5 {
        let mut leaf = original.clone();
        let instruction = &mut leaf.function.blocks[0].instructions[0];
        match corruption {
            0 => {
                instruction.operation = Operation::TopReference {
                    module: 0,
                    binder: other,
                    type_arguments: Vec::new(),
                    dictionaries: Vec::new(),
                }
            }
            1 => {
                instruction.operation = Operation::TopReference {
                    module: 99,
                    binder: target,
                    type_arguments: Vec::new(),
                    dictionaries: Vec::new(),
                }
            }
            2 => instruction.origin.rule = Rule::Literal,
            3 => instruction.origin.source = Source::Expr(u32::MAX),
            _ => {
                instruction.operation = Operation::Literal(h2r_core_ir::Lit {
                    kind: "int".into(),
                    ..h2r_core_ir::Lit::int(0)
                })
            }
        }
        verify(&leaf.function).unwrap();
        assert!(
            verify_leaf(&m, 0, owner, FnId(0), &leaf).is_err(),
            "corruption {corruption}"
        );
    }
}

#[test]
fn nir_retains_recursive_top_reference_and_rejects_mismatched_type() {
    use crate::nir::{FnId, Operation, lower::lower_leaf};
    let m = module(
        "Main",
        vec![(binder(&sn("Main", "f"), "f", "f"), lvar("f"))],
        json!({}),
    );
    let owner = m.top[0].pairs[0].binder;
    let leaf = lower_leaf(&m, 0, owner, FnId(0)).unwrap();
    assert!(
        matches!(leaf.function.blocks[0].instructions[0].operation, Operation::TopReference { binder, .. } if binder == owner)
    );
    let mut m = module(
        "Main",
        vec![
            (binder(&sn("Main", "f"), "f", "f"), lvar("g")),
            (binder(&sn("Main", "g"), "g", "g"), lit()),
        ],
        json!({}),
    );
    m.types.push(h2r_core_ir::Ty::Lit {
        kind: "Nat".into(),
        text: "42".into(),
    });
    let target = m.top[1].pairs[0].binder;
    m.binders[target as usize].ty = 1;
    assert!(
        lower_leaf(&m, 0, m.top[0].pairs[0].binder, FnId(0))
            .unwrap_err()
            .reason
            .contains("reference type mismatch")
    );
}

fn nir_import_world() -> Vec<Module> {
    vec![
        module(
            "Main",
            vec![(
                binder(&sn("Main", "main"), "main", "main"),
                gvar(&sn("Lib", "value"), "value"),
            )],
            json!({}),
        ),
        module(
            "Lib",
            vec![(
                binder(&sn("Lib", "value"), "value", "different-unique"),
                lit(),
            )],
            json!({}),
        ),
    ]
}

#[test]
fn nir_links_imports_by_stable_name_and_keeps_source_origins() {
    use crate::nir::{
        FnId, Operation, lower::lower_leaf_in_world, program::lower_program,
        verify::verify_leaf_in_world,
    };
    let modules = nir_import_world();
    let owner = modules[0].top[0].pairs[0].binder;
    let target = modules[1].top[0].pairs[0].binder;
    let leaf = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
    let instruction = &leaf.function.blocks[0].instructions[0];
    assert!(
        matches!(instruction.operation, Operation::TopReference { module: 1, binder, .. } if binder == target)
    );
    assert_eq!(instruction.origin.module, 0);
    assert_eq!(
        verify_leaf_in_world(&modules, 0, owner, FnId(0), &leaf)
            .unwrap()
            .source_nodes,
        1
    );
    let attempt = lower_program(&modules).unwrap();
    assert_eq!(
        (attempt.live, attempt.lowered.len(), attempt.refused.len()),
        (2, 2, 0)
    );
    let program_only =
        crate::nir::program::lower_program_owners(&modules, |module| module == 0).unwrap();
    assert_eq!(
        (
            program_only.live,
            program_only.library,
            program_only.lowered.len()
        ),
        (1, 1, 1)
    );
    assert_eq!(program_only.lowered[0].function.module, 0);
    assert!(lower_leaf_in_world(&modules, 99, owner, FnId(0)).is_err());
    assert!(verify_leaf_in_world(&modules, 99, owner, FnId(0), &leaf).is_err());
}

#[test]
fn nir_import_verifier_rejects_forged_target_origin_and_operation() {
    use crate::nir::{
        FnId, Operation, Rule,
        lower::lower_leaf_in_world,
        verify::{verify, verify_leaf_in_world},
    };
    let modules = nir_import_world();
    let owner = modules[0].top[0].pairs[0].binder;
    let original = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
    for mutation in 0..5 {
        let mut leaf = original.clone();
        let instruction = &mut leaf.function.blocks[0].instructions[0];
        match mutation {
            0 => {
                instruction.operation = Operation::TopReference {
                    module: 0,
                    binder: owner,
                    type_arguments: Vec::new(),
                    dictionaries: Vec::new(),
                }
            }
            1 => {
                instruction.operation = Operation::TopReference {
                    module: 1,
                    binder: u32::MAX,
                    type_arguments: Vec::new(),
                    dictionaries: Vec::new(),
                }
            }
            2 => instruction.origin.rule = Rule::Literal,
            3 => instruction.origin.source = crate::nir::Source::Expr(u32::MAX),
            _ => {
                instruction.operation = Operation::Literal(h2r_core_ir::Lit {
                    kind: "int".into(),
                    ..h2r_core_ir::Lit::int(0)
                })
            }
        }
        verify(&leaf.function).unwrap();
        assert!(verify_leaf_in_world(&modules, 0, owner, FnId(0), &leaf).is_err());
    }
}

/// A world whose `Main.main` builds an unboxed tuple from its two parameters
/// and immediately takes it apart again.
///
/// The constructor evidence is what GHC's own is for a tuple: unboxed,
/// unlifted, one constructor in the family, and not a newtype.
fn unboxed_tuple_world() -> Vec<Module> {
    use h2r_core_ir::Ty;
    let tuple_name = "$u$M$Pair#";
    let body = json!({
        "node": "Case",
        "scrut": app(app(gvar(tuple_name, "Pair#"), lvar("x")), lvar("y")),
        "binder": binder("$_in$wild", "wild", "wild"),
        "type": "Int#", "ty": 0,
        "alts": [{
            "con": {"kind": "DataAlt", "name": tuple_name, "occ": "Pair#", "tag": 1},
            "binders": [binder("$_in$p", "p", "p"), binder("$_in$q", "q", "q")],
            "rhs": int_op("-#", lvar("p"), lvar("q"))
        }]
    });
    let mut modules = scalar_expression_world(body);
    let m = &mut modules[0];
    let int = m.types[0].clone();
    let tuple = Ty::Con {
        tycon: h2r_core_ir::TyConId {
            name: tuple_name.into(),
            occ: "Pair#".into(),
            unique: "pair-hash".into(),
        },
        args: vec![],
    };
    let tuple_index = m.types.len() as u32;
    m.types.push(tuple.clone());
    let signature = m.types.len() as u32;
    m.types.push(Ty::Fun {
        mult: Box::new(int.clone()),
        arg: Box::new(int.clone()),
        res: Box::new(Ty::Fun {
            mult: Box::new(int.clone()),
            arg: Box::new(int),
            res: Box::new(tuple),
        }),
    });
    for b in &mut m.binders {
        if b.unique == "wild" {
            b.ty = tuple_index;
        }
    }
    m.constructors.push(
        serde_json::from_value(json!({
            "name": tuple_name, "worker": tuple_name, "family": tuple_name,
            "familySize": 1, "tag": 1, "signature": signature, "repArity": 2,
            "strict": [false, false], "vanilla": false,
            "newtype": false, "unlifted": true, "unboxed": true,
            "existential": false, "equalities": false
        }))
        .unwrap(),
    );
    modules
}

/// An unboxed tuple projection that read the wrong component would be a
/// miscompile, so the verifier re-derives every index from the source
/// alternative's binder order rather than from the candidate.
#[test]
fn unboxed_tuple_verifier_rejects_a_swapped_projection() {
    use crate::nir::{
        FnId, Operation, Rule,
        lower::lower_leaf_in_world,
        verify::{verify, verify_leaf_in_world},
    };
    let modules = unboxed_tuple_world();
    let owner = modules[0].top[0].pairs[0].binder;
    let original = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
    let projections = original.function.blocks[0]
        .instructions
        .iter()
        .filter(|i| matches!(i.operation, Operation::UnboxedTupleField { .. }))
        .count();
    assert_eq!(projections, 2, "both components are named");
    for mutation in 0..3 {
        let mut leaf = original.clone();
        let block = &mut leaf.function.blocks[0];
        let at = block
            .instructions
            .iter()
            .position(|i| matches!(i.operation, Operation::UnboxedTupleField { index: 0, .. }))
            .expect("the first component is projected");
        match mutation {
            // Read component 1 where the source named component 0.
            0 => {
                if let Operation::UnboxedTupleField { index, .. } =
                    &mut block.instructions[at].operation
                {
                    *index = 1;
                }
            }
            1 => block.instructions[at].origin.rule = Rule::Construct,
            _ => block.instructions[at].origin.source = crate::nir::Source::Expr(u32::MAX),
        }
        verify(&leaf.function).unwrap();
        assert!(
            verify_leaf_in_world(&modules, 0, owner, FnId(0), &leaf).is_err(),
            "mutation {mutation} survived"
        );
    }
}

fn case_binder_refusal(ty: h2r_core_ir::Ty) -> String {
    use crate::nir::{FnId, lower::lower_leaf_in_world};
    let mut modules = unboxed_tuple_world();
    let m = &mut modules[0];
    let index = m.types.len() as u32;
    m.types.push(ty);
    for b in &mut m.binders {
        if b.unique == "wild" {
            b.ty = index;
        }
    }
    let owner = modules[0].top[0].pairs[0].binder;
    lower_leaf_in_world(&modules, 0, owner, FnId(0))
        .expect_err("the case must be refused")
        .reason
}

#[test]
fn a_case_scrutinee_without_a_carrier_is_not_a_scalar_switch() {
    let reason = case_binder_refusal(h2r_core_ir::Ty::Var(h2r_core_ir::TyVarId {
        name: "a".into(),
        occ: "a".into(),
        unique: "a".into(),
    }));
    assert_eq!(reason, "unsupported case scrutinee carrier");
}

#[test]
fn an_unboxed_tuple_instantiation_failure_keeps_its_reason() {
    let reason = case_binder_refusal(h2r_core_ir::Ty::Con {
        tycon: h2r_core_ir::TyConId {
            name: "$u$M$Pair#".into(),
            occ: "Pair#".into(),
            unique: "pair-hash".into(),
        },
        args: vec![h2r_core_ir::Ty::Con {
            tycon: h2r_core_ir::TyConId {
                name: "$ghc-prim$GHC.Prim$Int#".into(),
                occ: "Int#".into(),
                unique: "int-hash".into(),
            },
            args: vec![],
        }],
    });
    assert_eq!(reason, "type application exceeds forall parameters");
}

/// A world whose `Main.main` calls an import GHC's demand analysis marked as a
/// dead end."" Nothing in the world defines it, so the signature is the only
/// evidence there is, which is exactly the situation the rule is for.
fn nir_dead_end_world(diverges: bool, signature_arity: usize, applied: usize) -> Vec<Module> {
    nir_dead_end_cases_world(diverges, signature_arity, applied, 0)
}

fn nir_dead_end_cases_world(
    diverges: bool,
    signature_arity: usize,
    applied: usize,
    cases: usize,
) -> Vec<Module> {
    let dead_end = "$base$GHC.Err$errorWithoutStackTrace";
    let mut body = gvar(dead_end, "errorWithoutStackTrace");
    for _ in 0..applied {
        body = app(body, lit());
    }
    for n in 0..cases {
        body = json!({
            "node": "Case", "scrut": body,
            "binder": binder("$_sys$dead", "dead", &format!("dead{n}")),
            "ty": 0, "type": "Int#", "alts": []
        });
    }
    let mut modules = vec![module(
        "Main",
        vec![(binder(&sn("Main", "main"), "main", "main"), body)],
        json!({}),
    )];
    modules[0].ids.insert(
        dead_end.into(),
        serde_json::from_value(json!({
            "name": dead_end, "occ": "errorWithoutStackTrace",
            "arity": signature_arity, "details": "", "isJoinPoint": false, "dataCon": null,
            "dmdSig": {
                "args": vec![demand(); signature_arity],
                "diverges": diverges,
                "pretty": if diverges { "<S>b" } else { "<S>" },
            }
        }))
        .unwrap(),
    );
    modules
}

/// A call GHC proved never returns becomes a terminator, and the verifier
/// re-derives that from the demand signature rather than from the candidate.
#[test]
fn nir_lowers_a_proven_dead_end_as_a_terminator() {
    use crate::nir::{Exit, FnId, Rule, lower::lower_leaf_in_world, verify::verify_leaf_in_world};
    let modules = nir_dead_end_world(true, 1, 1);
    let owner = modules[0].top[0].pairs[0].binder;
    let leaf = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
    let block = &leaf.function.blocks[0];
    assert!(
        block.instructions.is_empty(),
        "a dead end evaluates nothing"
    );
    assert!(matches!(
        &block.terminator.exit,
        Exit::Diverge { name, .. } if name == "$base$GHC.Err$errorWithoutStackTrace"
    ));
    assert_eq!(block.terminator.origin.rule, Rule::Diverge);
    verify_leaf_in_world(&modules, 0, owner, FnId(0), &leaf).unwrap();
}

#[test]
fn emission_refuses_dead_ends_without_runtime_semantics() {
    // Even a recognized error function cannot be replaced by exit(1): its
    // argument may diverge, and exception text/handling remain observable.
    let modules = nir_dead_end_world(true, 1, 1);
    let error = crate::emit::emit_entry(&modules, &sn("Main", "main")).unwrap_err();
    assert!(
        error.contains("unimplemented non-returning call"),
        "{error}"
    );
}

#[test]
fn empty_cases_require_proven_nonreturn_and_preserve_source_accounting() {
    use crate::nir::{FnId, lower::lower_leaf_in_world, verify::verify_leaf_in_world};
    for depth in [1, 2, 4] {
        let modules = nir_dead_end_cases_world(true, 1, 1, depth);
        let owner = modules[0].top[0].pairs[0].binder;
        let leaf = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
        verify_leaf_in_world(&modules, 0, owner, FnId(0), &leaf).unwrap();
        assert!(
            crate::emit::emit_entry(&modules, &sn("Main", "main"))
                .unwrap_err()
                .contains("unimplemented non-returning call")
        );
        let mut changed = nir_dead_end_cases_world(true, 1, 1, depth);
        changed[0].ids.values_mut().next().unwrap().dmd_sig.diverges = false;
        assert!(verify_leaf_in_world(&changed, 0, owner, FnId(0), &leaf).is_err());
        assert!(lower_leaf_in_world(&changed, 0, owner, FnId(0)).is_err());
        // A mismatching empty-case result type invalidates the same candidate.
        let mut changed = nir_dead_end_cases_world(true, 1, 1, depth);
        let wrong = changed[0].types.len() as u32;
        changed[0].types.push(h2r_core_ir::Ty::Opaque {
            pretty: "wrong".into(),
        });
        let rhs = changed[0].top[0].pairs[0].rhs;
        if let h2r_core_ir::Expr::Case { ty, .. } = &mut changed[0].exprs[rhs as usize] {
            *ty = wrong;
        }
        assert!(verify_leaf_in_world(&changed, 0, owner, FnId(0), &leaf).is_err());
        let mut changed = nir_dead_end_cases_world(true, 1, 1, depth);
        let rhs = changed[0].top[0].pairs[0].rhs;
        if let h2r_core_ir::Expr::Case { scrut, alts, .. } = &mut changed[0].exprs[rhs as usize] {
            alts.push(h2r_core_ir::Alt {
                con: h2r_core_ir::AltCon::Default,
                binders: vec![],
                rhs: *scrut,
            });
        }
        assert!(verify_leaf_in_world(&changed, 0, owner, FnId(0), &leaf).is_err());
    }
    let modules = nir_dead_end_cases_world(true, 2, 1, 1);
    let owner = modules[0].top[0].pairs[0].binder;
    assert!(lower_leaf_in_world(&modules, 0, owner, FnId(0)).is_err());
}

#[test]
fn empty_case_reads_a_local_cafs_own_demand_evidence() {
    use crate::nir::{FnId, lower::lower_leaf_in_world, verify::verify_leaf_in_world};
    let mut bottom = binder(&sn("Main", "bottom"), "bottom", "bottom");
    bottom["dmdSig"] = json!({"args": [], "diverges": true, "pretty": "b"});
    let mut modules = vec![module(
        "Main",
        vec![
            (
                binder(&sn("Main", "main"), "main", "main"),
                json!({
                    "node": "Case", "scrut": lvar("bottom"),
                    "binder": binder("$_sys$dead", "dead", "dead"),
                    "ty": 0, "type": "Int#", "alts": []
                }),
            ),
            (bottom, lvar("bottom")),
        ],
        json!({}),
    )];
    let owner = modules[0].top[0].pairs[0].binder;
    let bottom = modules[0].top[1].pairs[0].binder;
    let leaf = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
    verify_leaf_in_world(&modules, 0, owner, FnId(0), &leaf).unwrap();
    let error = crate::emit::emit_entry(&modules, &sn("Main", "main")).unwrap_err();
    assert!(
        error.contains("emission requires a carrier for $u$M$T"),
        "{error}"
    );
    modules[0].binders[bottom as usize]
        .dmd_sig
        .as_mut()
        .unwrap()
        .diverges = false;
    assert!(verify_leaf_in_world(&modules, 0, owner, FnId(0), &leaf).is_err());
    assert!(lower_leaf_in_world(&modules, 0, owner, FnId(0)).is_err());
}

/// Without the divergence, and below the signature's own arity, the same
/// spine is an ordinary call: a partial application returns perfectly well.
#[test]
fn a_dead_end_needs_divergence_and_saturation() {
    use crate::nir::{Exit, FnId, lower::lower_leaf_in_world};
    for (diverges, applied) in [(false, 1), (true, 0)] {
        let modules = nir_dead_end_world(diverges, 2, applied);
        let owner = modules[0].top[0].pairs[0].binder;
        let lowered = lower_leaf_in_world(&modules, 0, owner, FnId(0));
        let diverged = lowered.is_ok_and(|leaf| {
            leaf.function
                .blocks
                .iter()
                .any(|b| matches!(b.terminator.exit, Exit::Diverge { .. }))
        });
        assert!(!diverged, "diverges={diverges} applied={applied}");
    }
}

/// A forged dead end is rejected: the source must say the same thing.
#[test]
fn dead_end_verifier_rejects_a_forged_name_type_and_rule() {
    use crate::nir::{
        Exit, FnId, Rule,
        lower::lower_leaf_in_world,
        verify::{verify, verify_leaf_in_world},
    };
    let modules = nir_dead_end_world(true, 1, 1);
    let owner = modules[0].top[0].pairs[0].binder;
    let original = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
    for mutation in 0..3 {
        let mut leaf = original.clone();
        let terminator = &mut leaf.function.blocks[0].terminator;
        match mutation {
            0 => {
                if let Exit::Diverge { name, .. } = &mut terminator.exit {
                    *name = "$base$GHC.Err$undefined".into();
                }
            }
            1 => terminator.origin.rule = Rule::Return,
            _ => terminator.origin.source = crate::nir::Source::Expr(u32::MAX),
        }
        verify(&leaf.function).unwrap();
        assert!(
            verify_leaf_in_world(&modules, 0, owner, FnId(0), &leaf).is_err(),
            "mutation {mutation} survived"
        );
    }
}

#[test]
fn nir_imports_refuse_missing_ambiguous_and_internal_names() {
    use crate::nir::{FnId, lower::lower_leaf_in_world};
    let mut modules = nir_import_world();
    let owner = modules[0].top[0].pairs[0].binder;
    assert!(
        lower_leaf_in_world(&modules[..1], 0, owner, FnId(0))
            .unwrap_err()
            .reason
            .contains("outside the loaded world")
    );
    modules.push(module(
        "Other",
        vec![(binder(&sn("Lib", "value"), "value", "v2"), lit())],
        json!({}),
    ));
    assert!(
        lower_leaf_in_world(&modules, 0, owner, FnId(0))
            .unwrap_err()
            .reason
            .contains("ambiguous")
    );
    let modules = [module(
        "Main",
        vec![(
            binder(&sn("Main", "main"), "main", "main"),
            gvar("$_in$value", "value"),
        )],
        json!({}),
    )];
    assert!(
        lower_leaf_in_world(&modules, 0, owner, FnId(0))
            .unwrap_err()
            .reason
            .contains("external stable name")
    );
}

#[test]
fn nir_imports_require_closed_structured_types_in_both_modules() {
    use crate::nir::{FnId, lower::lower_leaf_in_world, verify::verify_leaf_in_world};
    use h2r_core_ir::{Ty, TyVarId};
    let modules = nir_import_world();
    let owner = modules[0].top[0].pairs[0].binder;
    let leaf = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
    for bad_ty in [
        Ty::Var(TyVarId {
            name: "a".into(),
            occ: "a".into(),
            unique: "same-free-unique".into(),
        }),
        Ty::Opaque {
            pretty: "same printed type".into(),
        },
        Ty::Con {
            tycon: h2r_core_ir::TyConId {
                name: "$_in$T".into(),
                occ: "T".into(),
                unique: "T".into(),
            },
            args: vec![],
        },
    ] {
        let mut modules = nir_import_world();
        // Matching uniques/text must not make unrelated scopes equal.
        modules[0].types[0] = bad_ty.clone();
        modules[1].types[0] = bad_ty;
        assert!(
            lower_leaf_in_world(&modules, 0, owner, FnId(0))
                .unwrap_err()
                .reason
                .contains("closed structured")
        );
        let mut forged = leaf.clone();
        forged.function.result_ty = modules[0].types[0].clone();
        forged.function.blocks[0].instructions[0].result.ty =
            crate::nir::shared(&modules[0].types[0]);
        assert!(verify_leaf_in_world(&modules, 0, owner, FnId(0), &forged).is_err());
    }
    let mut modules = nir_import_world();
    modules[1].types[0] = Ty::Lit {
        kind: "Nat".into(),
        text: "42".into(),
    };
    assert!(
        lower_leaf_in_world(&modules, 0, owner, FnId(0))
            .unwrap_err()
            .reason
            .contains("type mismatch")
    );
}

#[test]
fn nir_imports_accept_closed_alpha_renamed_foralls() {
    use crate::nir::{FnId, lower::lower_leaf_in_world};
    use h2r_core_ir::{Ty, TyVarId};
    let mut modules = nir_import_world();
    for (index, module) in modules.iter_mut().enumerate() {
        let var = TyVarId {
            name: "a".into(),
            occ: "a".into(),
            unique: format!("a{index}").into(),
        };
        module.types[0] = Ty::ForAll {
            binder: var.clone(),
            body: Box::new(Ty::Var(var)),
        };
    }
    let owner = modules[0].top[0].pairs[0].binder;
    lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
}

#[test]
fn nir_world_lookup_does_not_override_lexical_parameters() {
    use crate::nir::{FnId, lower::lower_leaf_in_world};
    use h2r_core_ir::Ty;
    let mut modules = nir_import_world();
    modules[0] = module(
        "Main",
        vec![(
            binder(&sn("Main", "main"), "main", "main"),
            lam("value", lvar("value")),
        )],
        json!({}),
    );
    let ty = modules[0].types[0].clone();
    modules[0].types.push(Ty::Fun {
        mult: Box::new(ty.clone()),
        arg: Box::new(ty.clone()),
        res: Box::new(ty),
    });
    let owner = modules[0].top[0].pairs[0].binder;
    modules[0].binders[owner as usize].ty = 1;
    let leaf = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
    assert!(leaf.function.blocks[0].instructions.is_empty());
    assert_eq!(leaf.function.blocks[0].params.len(), 1);
}

fn nir_type_application_world(imported: bool) -> Vec<Module> {
    use h2r_core_ir::{Expr, Ty, TyConId, TyVarId};
    let target_module = if imported { "Lib" } else { "Main" };
    let head = if imported {
        gvar(&sn("Lib", "f"), "f")
    } else {
        lvar("f")
    };
    let rhs = app(
        app(head, json!({"node": "Type", "ty": 0, "type": "T"})),
        json!({"node": "Type", "ty": 0, "type": "U"}),
    );
    let target = (binder(&sn(target_module, "f"), "f", "f"), lvar("f"));
    let mut pairs = vec![(binder(&sn("Main", "main"), "main", "main"), rhs)];
    if !imported {
        pairs.push(target.clone());
    }
    let mut modules = vec![module("Main", pairs, json!({}))];
    if imported {
        modules.push(module("Lib", vec![target], json!({})));
    }
    let con = |name: &str, args| Ty::Con {
        tycon: TyConId {
            name: sn("Types", name).into(),
            occ: name.into(),
            unique: name.into(),
        },
        args,
    };
    let a = TyVarId {
        name: "a".into(),
        occ: "a".into(),
        unique: "a".into(),
    };
    let b = TyVarId {
        name: "b".into(),
        occ: "b".into(),
        unique: "b".into(),
    };
    let t = con("T", vec![]);
    let u = con("U", vec![]);
    let poly = Ty::ForAll {
        binder: a.clone(),
        body: Box::new(Ty::ForAll {
            binder: b.clone(),
            body: Box::new(con("Pair", vec![Ty::Var(a), Ty::Var(b)])),
        }),
    };
    let result = con("Pair", vec![t.clone(), u.clone()]);
    for m in &mut modules {
        m.types = vec![t.clone(), u.clone(), poly.clone(), result.clone()];
        for pair in m.top.iter().flat_map(|g| &g.pairs) {
            let binder = &mut m.binders[pair.binder as usize];
            binder.ty = if binder.occ == "main" { 3 } else { 2 };
        }
        for expr in &mut m.exprs {
            if let Expr::Type { ty, pretty } = expr {
                *ty = if pretty == "T" { 0 } else { 1 };
            }
        }
    }
    modules
}

#[test]
fn nir_type_applications_preserve_order_and_account_for_source_nodes() {
    use crate::nir::{FnId, Operation, lower::lower_leaf_in_world, verify::verify_leaf_in_world};
    for imported in [false, true] {
        let modules = nir_type_application_world(imported);
        let owner = modules[0].top[0].pairs[0].binder;
        let leaf = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
        let [instruction] = leaf.function.blocks[0].instructions.as_slice() else {
            panic!()
        };
        let Operation::TopReference {
            module,
            type_arguments: arguments,
            ..
        } = &instruction.operation
        else {
            panic!()
        };
        assert_eq!(*module, usize::from(imported));
        assert_eq!(arguments, &modules[0].types[..2]);
        assert_eq!(*instruction.result.ty, modules[0].types[3]);
        let accounting = verify_leaf_in_world(&modules, 0, owner, FnId(0), &leaf).unwrap();
        assert_eq!(
            (
                accounting.source_nodes,
                accounting.type_application_nodes,
                accounting.type_argument_nodes,
                accounting.value_nodes
            ),
            (5, 2, 2, 1)
        );
    }
}

#[test]
fn nir_type_application_verifier_rejects_forged_evidence() {
    use crate::nir::{
        FnId, Operation, Rule, Source,
        lower::lower_leaf_in_world,
        verify::{verify, verify_leaf_in_world},
    };
    let modules = nir_type_application_world(true);
    let owner = modules[0].top[0].pairs[0].binder;
    let original = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
    for mutation in 0..6 {
        let mut leaf = original.clone();
        let instruction = &mut leaf.function.blocks[0].instructions[0];
        let Operation::TopReference {
            module,
            binder,
            type_arguments: arguments,
            ..
        } = &mut instruction.operation
        else {
            panic!()
        };
        match mutation {
            0 => arguments.reverse(),
            1 => {
                arguments.pop();
            }
            2 => *module = 0,
            3 => *binder = u32::MAX,
            4 => instruction.origin.rule = Rule::TopReference,
            _ => instruction.origin.source = Source::Expr(u32::MAX),
        }
        verify(&leaf.function).unwrap();
        assert!(verify_leaf_in_world(&modules, 0, owner, FnId(0), &leaf).is_err());
    }
}

#[test]
fn nir_type_applications_refuse_value_arguments_open_types_and_wrong_results() {
    use crate::nir::{FnId, lower::lower_leaf_in_world};
    use h2r_core_ir::{Expr, Ty, TyVarId};
    for mutation in 0..4 {
        let mut modules = nir_type_application_world(false);
        let owner = modules[0].top[0].pairs[0].binder;
        let rhs = modules[0].top[0].pairs[0].rhs;
        let Expr::App { arg, .. } = modules[0].expr(rhs) else {
            panic!()
        };
        let arg = *arg;
        match mutation {
            0 => modules[0].exprs[arg as usize] = Expr::Coercion,
            1 => {
                modules[0].types[1] = Ty::Var(TyVarId {
                    name: "b".into(),
                    occ: "b".into(),
                    unique: "b".into(),
                })
            }
            2 => modules[0].binders[owner as usize].ty = 0,
            _ => modules[0].types[2] = modules[0].types[0].clone(),
        }
        assert!(
            lower_leaf_in_world(&modules, 0, owner, FnId(0)).is_err(),
            "mutation {mutation}"
        );
    }
}

fn nir_call_world(imported: bool) -> Vec<Module> {
    nir_call_world_to(imported, lam("a", lam("b", lvar("a"))))
}

fn nir_call_world_to(imported: bool, target_rhs: Value) -> Vec<Module> {
    use h2r_core_ir::Ty;
    let head = if imported {
        gvar(&sn("Lib", "target"), "target")
    } else {
        lvar("target")
    };
    let source = (
        binder(&sn("Main", "main"), "main", "main"),
        lam("x", lam("y", app(app(head, lvar("y")), lvar("x")))),
    );
    let target = (
        binder(
            &sn(if imported { "Lib" } else { "Main" }, "target"),
            "target",
            "target",
        ),
        target_rhs,
    );
    let mut modules = if imported {
        vec![
            module("Main", vec![source], json!({})),
            module("Lib", vec![target], json!({})),
        ]
    } else {
        vec![module("Main", vec![source, target], json!({}))]
    };
    for m in &mut modules {
        let t = m.types[0].clone();
        let arrow = |res| Ty::Fun {
            mult: Box::new(t.clone()),
            arg: Box::new(t.clone()),
            res: Box::new(res),
        };
        m.types.push(arrow(arrow(t.clone())));
        for pair in m.top.iter().flat_map(|g| &g.pairs) {
            m.binders[pair.binder as usize].ty = 1;
            m.binders[pair.binder as usize].arity = Some(2);
        }
    }
    modules
}

#[test]
fn nir_direct_calls_pass_parameters_without_forcing() {
    use crate::nir::{
        FnId, Operation, ValueId, lower::lower_leaf_in_world, program::lower_program,
        verify::verify_leaf_in_world,
    };
    for imported in [false, true] {
        let modules = nir_call_world(imported);
        let owner = modules[0].top[0].pairs[0].binder;
        let leaf = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
        let [instruction] = leaf.function.blocks[0].instructions.as_slice() else {
            panic!()
        };
        let Operation::CallTop {
            module, arguments, ..
        } = &instruction.operation
        else {
            panic!()
        };
        assert_eq!(*module, usize::from(imported));
        assert_eq!(arguments, &[ValueId(1), ValueId(0)]);
        let counts = verify_leaf_in_world(&modules, 0, owner, FnId(0), &leaf).unwrap();
        assert_eq!(
            (
                counts.source_nodes,
                counts.parameter_nodes,
                counts.value_application_nodes,
                counts.value_argument_nodes
            ),
            (7, 2, 2, 2)
        );
        let attempt = lower_program(&modules).unwrap();
        assert_eq!(attempt.lowered.len(), 2);
        assert!(attempt.refused.is_empty());
    }
}

#[test]
fn nir_direct_call_verifier_rejects_wrong_target_arguments_and_origin() {
    use crate::nir::{
        FnId, Operation, Rule, Source, ValueId,
        lower::lower_leaf_in_world,
        verify::{verify, verify_leaf_in_world},
    };
    let modules = nir_call_world(true);
    let owner = modules[0].top[0].pairs[0].binder;
    let original = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
    for mutation in 0..6 {
        let mut leaf = original.clone();
        let instruction = &mut leaf.function.blocks[0].instructions[0];
        let Operation::CallTop {
            module,
            binder,
            arguments,
            ..
        } = &mut instruction.operation
        else {
            panic!()
        };
        match mutation {
            0 => arguments.reverse(),
            1 => {
                arguments.pop();
            }
            2 => *module = 0,
            3 => *binder = u32::MAX,
            4 => instruction.origin.rule = Rule::TopReference,
            _ => instruction.origin.source = Source::Expr(u32::MAX),
        }
        verify(&leaf.function).unwrap();
        assert!(verify_leaf_in_world(&modules, 0, owner, FnId(0), &leaf).is_err());
    }
    let mut leaf = original;
    let Operation::CallTop { arguments, .. } =
        &mut leaf.function.blocks[0].instructions[0].operation
    else {
        panic!()
    };
    arguments[0] = ValueId(u32::MAX);
    assert!(
        verify(&leaf.function)
            .unwrap_err()
            .contains("unavailable call argument")
    );
}

#[test]
fn nir_direct_calls_reject_extra_forcing_and_computed_arguments() {
    use crate::nir::{
        FnId, Operation, ValueId,
        lower::lower_leaf_in_world,
        verify::{verify, verify_leaf_in_world},
    };
    let modules = nir_call_world(true);
    let owner = modules[0].top[0].pairs[0].binder;
    let mut leaf = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
    let mut extra = leaf.function.blocks[0].instructions[0].clone();
    extra.result.id = ValueId(99);
    extra.result.ty = leaf.function.blocks[0].params[0].ty.clone();
    extra.operation = Operation::Force(ValueId(0));
    leaf.function.blocks[0].instructions.insert(0, extra);
    verify(&leaf.function).unwrap();
    assert!(verify_leaf_in_world(&modules, 0, owner, FnId(0), &leaf).is_err());

    for argument in [json!({"node": "Coercion"}), app(lvar("x"), lvar("x"))] {
        let mut m = module(
            "Main",
            vec![
                (
                    binder(&sn("Main", "main"), "main", "main"),
                    lam("x", app(app(lvar("f"), argument), lvar("x"))),
                ),
                (
                    binder(&sn("Main", "f"), "f", "f"),
                    lam("a", lam("b", lvar("a"))),
                ),
            ],
            json!({}),
        );
        let t = m.types[0].clone();
        m.types.push(h2r_core_ir::Ty::Fun {
            mult: Box::new(t.clone()),
            arg: Box::new(t.clone()),
            res: Box::new(t.clone()),
        });
        m.types.push(h2r_core_ir::Ty::Fun {
            mult: Box::new(t.clone()),
            arg: Box::new(t),
            res: Box::new(m.types[1].clone()),
        });
        let target = m.top[1].pairs[0].binder;
        m.binders[target as usize].ty = 2;
        m.binders[target as usize].arity = Some(2);
        let owner = m.top[0].pairs[0].binder;
        m.binders[owner as usize].ty = 1;
        assert!(
            lower_leaf_in_world(&[m], 0, owner, FnId(0))
                .unwrap_err()
                .reason
                .contains(
                    "call arguments require supported Int#/Int computations or shared references"
                )
        );
    }
}

#[test]
fn nir_direct_calls_require_exact_known_arity_and_closed_types() {
    use crate::nir::{
        FnId, lower::lower_leaf_in_world, pretty::format_leaf, verify::verify_leaf_in_world,
    };
    use h2r_core_ir::Ty;
    let original_world = nir_call_world(true);
    let owner = original_world[0].top[0].pairs[0].binder;
    let original = lower_leaf_in_world(&original_world, 0, owner, FnId(0)).unwrap();
    for arity in [None, Some(0), Some(1), Some(3)] {
        let mut modules = nir_call_world(true);
        let target = modules[1].top[0].pairs[0].binder;
        modules[1].binders[target as usize].arity = arity;
        let relowered = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
        assert_eq!(
            format_leaf(&relowered),
            format_leaf(&original),
            "arity {arity:?}"
        );
    }
    for target_rhs in [
        lit(),
        lam("a", lvar("a")),
        lam("a", lam("b", lam("c", lvar("a")))),
    ] {
        let modules = nir_call_world_to(true, target_rhs);
        let relowered = lower_leaf_in_world(&modules, 0, owner, FnId(0));
        assert!(match &relowered {
            Err(_) => true,
            Ok(leaf) => format_leaf(leaf) != format_leaf(&original),
        });
        assert!(verify_leaf_in_world(&modules, 0, owner, FnId(0), &original).is_err());
    }
    let mut modules = nir_call_world(true);
    let owner = modules[0].top[0].pairs[0].binder;
    let Ty::Fun { arg, .. } = &mut modules[1].types[1] else {
        panic!()
    };
    **arg = Ty::Opaque { pretty: "T".into() };
    assert!(
        lower_leaf_in_world(&modules, 0, owner, FnId(0))
            .unwrap_err()
            .reason
            .contains("closed structured")
    );
}

#[test]
fn nir_direct_calls_refuse_wrong_argument_and_result_types() {
    use crate::nir::{FnId, lower::lower_leaf_in_world, verify::verify_leaf_in_world};
    use h2r_core_ir::Ty;
    for change_argument in [false, true] {
        let mut modules = nir_call_world(true);
        let owner = modules[0].top[0].pairs[0].binder;
        let original = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
        let Ty::Fun { arg, res, .. } = &mut modules[1].types[1] else {
            panic!()
        };
        let wrong = Ty::Lit {
            kind: "Nat".into(),
            text: "42".into(),
        };
        if change_argument {
            **arg = wrong;
        } else {
            let Ty::Fun { res, .. } = res.as_mut() else {
                panic!()
            };
            **res = wrong;
        }
        assert!(
            lower_leaf_in_world(&modules, 0, owner, FnId(0))
                .unwrap_err()
                .reason
                .contains("type mismatch")
        );
        assert!(verify_leaf_in_world(&modules, 0, owner, FnId(0), &original).is_err());
    }
}

fn nir_mixed_call_world(interleaved: bool) -> Vec<Module> {
    use h2r_core_ir::{Expr, Ty, TyVarId};
    let type_arg = |name: &str| json!({"node": "Type", "ty": 0, "type": name});
    let head = gvar(&sn("Lib", "target"), "target");
    let call = if interleaved {
        app(
            app(app(app(head, type_arg("T")), lvar("y")), type_arg("U")),
            lvar("x"),
        )
    } else {
        app(
            app(app(app(head, type_arg("T")), type_arg("U")), lvar("y")),
            lvar("x"),
        )
    };
    let mut modules = nir_call_world(true);
    let types = modules[0].types.clone();
    modules[0] = module(
        "Main",
        vec![(
            binder(&sn("Main", "main"), "main", "main"),
            lam("x", lam("y", call)),
        )],
        json!({}),
    );
    modules[0].types = types;
    let owner = modules[0].top[0].pairs[0].binder;
    modules[0].binders[owner as usize].ty = 1;
    let mut u = modules[0].types[0].clone();
    let Ty::Con { tycon, .. } = &mut u else {
        panic!()
    };
    tycon.name = sn("M", "U").into();
    modules[0].types.push(u);
    for expr in &mut modules[0].exprs {
        if let Expr::Type { ty, pretty } = expr
            && pretty == "U"
        {
            *ty = 2;
        }
    }
    let type_lambda = |name: &str, body| {
        let mut b = binder(name, name, name);
        b["kind"] = json!("tyvar");
        json!({"node": "Lam", "binder": b, "body": body})
    };
    let mut target = module(
        "Lib",
        vec![(
            binder(&sn("Lib", "target"), "target", "target"),
            type_lambda("q", type_lambda("r", lam("a", lam("b", lvar("a"))))),
        )],
        json!({}),
    );
    target.types = modules[1].types.clone();
    let q = Ty::Var(TyVarId {
        name: "q".into(),
        occ: "q".into(),
        unique: "q".into(),
    });
    let arrow = |result| Ty::Fun {
        mult: Box::new(target.types[0].clone()),
        arg: Box::new(q.clone()),
        res: Box::new(result),
    };
    let mut signature = arrow(arrow(q.clone()));
    for name in ["r", "q"] {
        signature = Ty::ForAll {
            binder: TyVarId {
                name: name.into(),
                occ: name.into(),
                unique: name.into(),
            },
            body: Box::new(signature),
        };
    }
    target.types.push(signature);
    target.types.push(q);
    for parameter in &mut target.binders {
        if parameter.occ == "a" || parameter.occ == "b" {
            parameter.ty = 3;
        }
    }
    let binder = target.top[0].pairs[0].binder;
    target.binders[binder as usize].ty = 2;
    target.binders[binder as usize].arity = Some(2);
    modules[1] = target;
    modules
}

#[test]
fn nir_mixed_calls_preserve_both_argument_lists_and_accounting() {
    use crate::nir::{
        FnId, Operation, ValueId, lower::lower_leaf_in_world, program::lower_program,
        verify::verify_leaf_in_world,
    };
    let modules = nir_mixed_call_world(false);
    let owner = modules[0].top[0].pairs[0].binder;
    let leaf = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
    let Operation::CallTop {
        type_arguments,
        arguments,
        ..
    } = &leaf.function.blocks[0].instructions[0].operation
    else {
        panic!()
    };
    assert_eq!(
        type_arguments,
        &[modules[0].types[0].clone(), modules[0].types[2].clone()]
    );
    assert_eq!(arguments, &[ValueId(1), ValueId(0)]);
    let counts = verify_leaf_in_world(&modules, 0, owner, FnId(0), &leaf).unwrap();
    assert_eq!(
        (
            counts.source_nodes,
            counts.parameter_nodes,
            counts.type_application_nodes,
            counts.type_argument_nodes,
            counts.value_application_nodes,
            counts.value_argument_nodes
        ),
        (11, 2, 2, 2, 2, 2)
    );
    let attempt = lower_program(&modules).unwrap();
    assert_eq!(attempt.lowered.len(), 2);
    assert!(attempt.refused.is_empty());
}

#[test]
fn nir_mixed_call_verifier_checks_even_phantom_type_arguments() {
    use crate::nir::{
        FnId, Operation,
        lower::lower_leaf_in_world,
        verify::{verify, verify_leaf_in_world},
    };
    let modules = nir_mixed_call_world(false);
    let owner = modules[0].top[0].pairs[0].binder;
    let original = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
    for mutation in 0..3 {
        let mut leaf = original.clone();
        let Operation::CallTop { type_arguments, .. } =
            &mut leaf.function.blocks[0].instructions[0].operation
        else {
            panic!()
        };
        match mutation {
            0 => type_arguments.reverse(),
            1 => {
                type_arguments.pop();
            }
            _ => type_arguments.push(modules[0].types[0].clone()),
        }
        verify(&leaf.function).unwrap();
        assert!(verify_leaf_in_world(&modules, 0, owner, FnId(0), &leaf).is_err());
    }
}

#[test]
fn nir_mixed_calls_refuse_interleaved_and_open_type_arguments() {
    use crate::nir::{FnId, lower::lower_leaf_in_world, verify::verify_leaf_in_world};
    let modules = nir_mixed_call_world(false);
    let owner = modules[0].top[0].pairs[0].binder;
    let leaf = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
    let bad = nir_mixed_call_world(true);
    assert!(
        lower_leaf_in_world(&bad, 0, owner, FnId(0))
            .unwrap_err()
            .reason
            .contains("applies a value where its target quantifies a type")
    );
    assert!(verify_leaf_in_world(&bad, 0, owner, FnId(0), &leaf).is_err());
    let mut modules = modules;
    modules[0].types[2] = h2r_core_ir::Ty::Var(h2r_core_ir::TyVarId {
        name: "q".into(),
        occ: "q".into(),
        unique: "q".into(),
    });
    assert!(
        lower_leaf_in_world(&modules, 0, owner, FnId(0))
            .unwrap_err()
            .reason
            .contains("closed structured")
    );
    assert!(verify_leaf_in_world(&modules, 0, owner, FnId(0), &leaf).is_err());
}

fn nir_literal_call_world(two_literals: bool) -> Vec<Module> {
    let literal = |n: i64| json!({"node": "Lit", "lit": int_lit(n)});
    let mut modules = nir_call_world(true);
    let types = modules[0].types.clone();
    let last = if two_literals { literal(20) } else { lvar("x") };
    modules[0] = module(
        "Main",
        vec![(
            binder(&sn("Main", "main"), "main", "main"),
            lam(
                "x",
                lam(
                    "y",
                    app(app(gvar(&sn("Lib", "target"), "target"), literal(10)), last),
                ),
            ),
        )],
        json!({}),
    );
    modules[0].types = types;
    let owner = modules[0].top[0].pairs[0].binder;
    modules[0].binders[owner as usize].ty = 1;
    modules
}

#[test]
fn nir_call_literals_have_typed_values_and_complete_accounting() {
    use crate::nir::{
        FnId, Operation, ValueId, lower::lower_leaf_in_world, verify::verify_leaf_in_world,
    };
    for two in [false, true] {
        let modules = nir_literal_call_world(two);
        let owner = modules[0].top[0].pairs[0].binder;
        let leaf = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
        let instructions = &leaf.function.blocks[0].instructions;
        assert_eq!(instructions.len(), if two { 3 } else { 2 });
        assert!(
            matches!(&instructions[0].operation, Operation::Literal(lit) if lit.number("Int") == Ok(10))
        );
        assert_eq!(*instructions[0].result.ty, modules[0].types[0]);
        let Operation::CallTop { arguments, .. } = &instructions.last().unwrap().operation else {
            panic!()
        };
        assert_eq!(
            arguments,
            &[ValueId(2), if two { ValueId(3) } else { ValueId(0) }]
        );
        assert_eq!(
            verify_leaf_in_world(&modules, 0, owner, FnId(0), &leaf)
                .unwrap()
                .source_nodes,
            7
        );
    }
}

#[test]
fn nir_call_literal_verifier_rejects_payload_origin_order_and_extra_forcing() {
    use crate::nir::{
        FnId, Operation, Rule, Source, ValueId,
        lower::lower_leaf_in_world,
        verify::{verify, verify_leaf_in_world},
    };
    let modules = nir_literal_call_world(true);
    let owner = modules[0].top[0].pairs[0].binder;
    let original = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
    for mutation in 0..8 {
        let mut leaf = original.clone();
        let instructions = &mut leaf.function.blocks[0].instructions;
        match mutation {
            0 | 1 => {
                let Operation::Literal(lit) = &mut instructions[0].operation else {
                    panic!()
                };
                if mutation == 0 {
                    lit.pretty = "999".into();
                } else {
                    lit.kind = "string".into();
                }
            }
            2 => instructions[0].origin.source = Source::Expr(u32::MAX),
            3 => instructions[0].origin.rule = Rule::CallTop,
            4 => instructions.swap(0, 1),
            5 => {
                let Operation::CallTop { arguments, .. } = &mut instructions[2].operation else {
                    panic!()
                };
                arguments.reverse();
            }
            6 => {
                instructions[0].result.ty = crate::nir::shared(&h2r_core_ir::Ty::Lit {
                    kind: "Nat".into(),
                    text: "42".into(),
                })
            }
            _ => {
                let mut extra = instructions[0].clone();
                extra.result.id = ValueId(99);
                extra.operation = Operation::Force(ValueId(0));
                instructions.insert(0, extra);
            }
        }
        verify(&leaf.function).unwrap();
        assert!(
            verify_leaf_in_world(&modules, 0, owner, FnId(0), &leaf).is_err(),
            "mutation {mutation}"
        );
    }
}

fn nir_top_argument_world() -> Vec<Module> {
    let types = nir_call_world(true)[0].types.clone();
    let mut modules = vec![
        module(
            "Main",
            vec![
                (
                    binder(&sn("Main", "main"), "main", "main"),
                    lam(
                        "x",
                        lam(
                            "y",
                            app(
                                app(gvar(&sn("Lib", "target"), "target"), lvar("shared")),
                                gvar(&sn("Lib", "shared"), "remote"),
                            ),
                        ),
                    ),
                ),
                (
                    binder(&sn("Main", "shared"), "shared", "shared"),
                    lvar("shared"),
                ),
            ],
            json!({}),
        ),
        module(
            "Lib",
            vec![
                (
                    binder(&sn("Lib", "target"), "target", "target"),
                    lam("a", lam("b", lvar("a"))),
                ),
                (
                    binder(&sn("Lib", "shared"), "shared", "different-unique"),
                    lit(),
                ),
            ],
            json!({}),
        ),
    ];
    for m in &mut modules {
        m.types = types.clone();
        let owner = m.top[0].pairs[0].binder;
        m.binders[owner as usize].ty = 1;
        m.binders[owner as usize].arity = Some(2);
    }
    modules
}

#[test]
fn nir_top_arguments_preserve_local_recursive_and_imported_identity() {
    use crate::nir::{
        FnId, Operation, ValueId, lower::lower_leaf_in_world, verify::verify_leaf_in_world,
    };
    let modules = nir_top_argument_world();
    let owner = modules[0].top[0].pairs[0].binder;
    let leaf = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
    let instructions = &leaf.function.blocks[0].instructions;
    assert_eq!(instructions.len(), 3);
    for index in 0..2 {
        let Operation::TopReference { module, binder, .. } = instructions[index].operation else {
            panic!()
        };
        assert_eq!(module, index);
        assert_eq!(binder, modules[index].top[1].pairs[0].binder);
    }
    let Operation::CallTop { arguments, .. } = &instructions[2].operation else {
        panic!()
    };
    assert_eq!(arguments, &[ValueId(2), ValueId(3)]);
    assert_eq!(
        verify_leaf_in_world(&modules, 0, owner, FnId(0), &leaf)
            .unwrap()
            .source_nodes,
        7
    );
}

#[test]
fn nir_top_argument_verifier_rejects_target_origin_type_and_forcing_changes() {
    use crate::nir::{
        FnId, Operation, Rule, ValueId,
        lower::lower_leaf_in_world,
        verify::{verify, verify_leaf_in_world},
    };
    let modules = nir_top_argument_world();
    let owner = modules[0].top[0].pairs[0].binder;
    let original = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
    for mutation in 0..5 {
        let mut leaf = original.clone();
        let instruction = &mut leaf.function.blocks[0].instructions[0];
        match mutation {
            0 => {
                instruction.operation = Operation::TopReference {
                    module: 1,
                    binder: modules[1].top[1].pairs[0].binder,
                    type_arguments: Vec::new(),
                    dictionaries: Vec::new(),
                }
            }
            1 => {
                instruction.operation = Operation::TopReference {
                    module: 0,
                    binder: u32::MAX,
                    type_arguments: Vec::new(),
                    dictionaries: Vec::new(),
                }
            }
            2 => instruction.origin.rule = Rule::Literal,
            3 => {
                instruction.result.ty = crate::nir::shared(&h2r_core_ir::Ty::Lit {
                    kind: "Nat".into(),
                    text: "42".into(),
                })
            }
            _ => instruction.operation = Operation::Force(ValueId(0)),
        }
        verify(&leaf.function).unwrap();
        assert!(verify_leaf_in_world(&modules, 0, owner, FnId(0), &leaf).is_err());
    }
    let mut modules = modules;
    let target = modules[1].top[1].pairs[0].binder;
    modules[1]
        .types
        .push(h2r_core_ir::Ty::Opaque { pretty: "T".into() });
    modules[1].binders[target as usize].ty = 2;
    assert!(
        lower_leaf_in_world(&modules, 0, owner, FnId(0))
            .unwrap_err()
            .reason
            .contains("top-level argument type mismatch")
    );
    assert!(verify_leaf_in_world(&modules, 0, owner, FnId(0), &original).is_err());
}

fn scalar_emission_world() -> Vec<Module> {
    use h2r_core_ir::{Expr, Ty, TyConId};
    let mut modules = nir_literal_call_world(false);
    for m in &mut modules {
        let int = Ty::Con {
            tycon: TyConId {
                name: "$ghc-prim$GHC.Prim$Int#".into(),
                occ: "Int#".into(),
                unique: "int".into(),
            },
            args: vec![],
        };
        let arrow = |res| Ty::Fun {
            mult: Box::new(int.clone()),
            arg: Box::new(int.clone()),
            res: Box::new(res),
        };
        m.types = vec![int.clone(), arrow(arrow(int.clone()))];
        for expr in &mut m.exprs {
            if let Expr::Lit(lit) = expr {
                lit.kind = "number".into();
                lit.pretty.push('#');
            }
        }
    }
    modules
}

#[test]
fn scalar_emission_is_deterministic_and_includes_dependencies() {
    let modules = scalar_emission_world();
    let source = crate::emit::emit_entry(&modules, &sn("Main", "main")).unwrap();
    assert_eq!(
        source,
        crate::emit::emit_entry(&modules, &sn("Main", "main")).unwrap()
    );
    let source = generated(&source);
    assert_eq!(source.matches("fn f_").count(), 2);
    assert!(source.contains("10i64"));
    assert!(source.contains("-> i64"));
    assert!(source.contains("target_pointer_width = \"64\""));
    assert!(!source.contains("unsafe"));
}

#[test]
fn scalar_emission_refuses_unsupported_dependency_and_unsafe_literals() {
    use h2r_core_ir::Expr;
    let mut modules = scalar_emission_world();
    let rhs = modules[1].top[0].pairs[0].rhs;
    modules[1].exprs[rhs as usize] = Expr::Coercion;
    assert!(crate::emit::emit_entry(&modules, &sn("Main", "main")).is_err());
    // Conversely, an unsupported owner outside the selected closure is irrelevant.
    let mut modules = scalar_emission_world();
    let rhs = modules[0].top[0].pairs[0].rhs;
    modules[0].exprs[rhs as usize] = Expr::Coercion;
    assert!(crate::emit::emit_entry(&modules, &sn("Lib", "target")).is_ok());
    // A forged value, a width the carrier does not have, and a missing
    // `LitNumType`. GHC's rendering is not read, so corrupting it changes
    // nothing; these corrupt what a decoder actually uses.
    for forgery in 0..4 {
        let mut modules = scalar_emission_world();
        for expr in &mut modules[0].exprs {
            if let Expr::Lit(lit) = expr {
                match forgery {
                    0 => lit.value = Some("9223372036854775808".into()),
                    1 => lit.value = Some("0; panic!()".into()),
                    2 => lit.num_type = Some("Word64".into()),
                    _ => lit.num_type = None,
                }
            }
        }
        assert!(
            crate::emit::emit_entry(&modules, &sn("Main", "main")).is_err(),
            "forgery {forgery}"
        );
    }
    // The rendering is a diagnostic: changing it alone cannot change the code.
    let source = crate::emit::emit_entry(&scalar_emission_world(), &sn("Main", "main")).unwrap();
    let mut modules = scalar_emission_world();
    for expr in &mut modules[0].exprs {
        if let Expr::Lit(lit) = expr {
            lit.pretty = "0; panic!()#".into();
        }
    }
    assert_eq!(
        source,
        crate::emit::emit_entry(&modules, &sn("Main", "main")).unwrap()
    );
    assert!(crate::emit::emit_entry(&nir_call_world(true), &sn("Main", "main")).is_err());
    assert!(crate::emit::emit_entry(&scalar_emission_world(), "main").is_err());
}

#[test]
fn scalar_emission_accepts_recursive_functions() {
    let mut modules = scalar_emission_world();
    // Main's existing source call now resolves back to its own definition.
    let target = modules[1].top[0].pairs[0].binder;
    modules[1].binders[target as usize].name = sn("Lib", "unused");
    let owner = modules[0].top[0].pairs[0].binder;
    modules[0].binders[owner as usize].name = sn("Lib", "target");
    modules[0].binders[owner as usize].arity = Some(2);
    let source = generated(&crate::emit::emit_entry(&modules, &sn("Lib", "target")).unwrap());
    // Instance 0 is the entry, and the self-call transfers back to its entry
    // block rather than growing the native stack.
    assert!(source.contains("h2r_rt::Step::Next(Box::new(move || s_0_0("));
}

fn local_function_world(recursive: bool) -> Vec<Module> {
    let mut b = binder("$_in$go", "go", "go");
    b["ty"] = json!(1);
    b["arity"] = json!(2);
    b["isJoinPoint"] = json!(true);
    let rhs = if recursive {
        int_case(
            lvar("i"),
            "s",
            app(
                app(
                    lvar("go"),
                    int_op("-#", lvar("i"), json!({"node": "Lit", "lit": int_lit(1)})),
                ),
                int_op("+#", lvar("acc"), lvar("y")),
            ),
            vec![(0, lvar("acc"))],
        )
    } else {
        int_op("+#", lvar("acc"), lvar("y"))
    };
    scalar_expression_world(
        json!({"node":"Let", "bind":{"rec":recursive,"pairs":[{"binder":b,"rhs":lam("i",lam("acc",rhs)),"whnf":true,"cheap":true,"trivial":false,"okForSpec":true}]}, "body":app(app(lvar("go"),lvar("x")),lvar("y"))}),
    )
}

fn closure_world() -> Vec<Module> {
    closure_world_applying(app(lvar("p"), lvar("y")))
}

fn polymorphic_local_world(second_type: u32) -> Vec<Module> {
    use h2r_core_ir::{Ty, TyVarId};
    let mut f = binder("$_in$f", "f", "f");
    f["arity"] = json!(2);
    let call = |value: Value, ty: u32, argument: Value| {
        app(app(app(lvar("f"), value), type_arg(ty, "t")), argument)
    };
    let primop = |symbol: &str, argument: Value| {
        app(
            gvar(&format!("$ghc-prim$GHC.Prim${symbol}"), symbol),
            argument,
        )
    };
    let inner = if second_type == 0 {
        call(lvar("y"), 0, lvar("x"))
    } else {
        primop(
            "word2Int#",
            call(lvar("y"), second_type, primop("int2Word#", lvar("x"))),
        )
    };
    let body = json!({"node":"Let","bind":{"rec":false,"pairs":[{"binder":f,
        "rhs":lam("v",tylam("a",lam("k",lvar("k")))),
        "whnf":true,"cheap":true,"trivial":false,"okForSpec":true}]},
        "body":call(lvar("x"), 0, inner)});
    let mut modules = scalar_expression_world(body);
    for symbol in ["int2Word#", "word2Int#"] {
        let name = format!("$ghc-prim$GHC.Prim${symbol}");
        modules[0].ids.insert(
            name.clone(),
            serde_json::from_value(json!({
                "name": name, "occ": symbol, "arity": 1, "details": "[PrimOp]",
                "isJoinPoint": false, "dataCon": null,
                "dmdSig": {"args": [], "diverges": false, "pretty": ""}
            }))
            .unwrap(),
        );
    }
    let int = modules[0].types[0].clone();
    let a = Ty::Var(TyVarId {
        name: "$_in$a".into(),
        occ: "a".into(),
        unique: "a".into(),
    });
    let arrow = |arg: Ty, res: Ty| Ty::Fun {
        mult: Box::new(int.clone()),
        arg: Box::new(arg),
        res: Box::new(res),
    };
    let signature = arrow(
        int.clone(),
        Ty::ForAll {
            binder: TyVarId {
                name: "$_in$a".into(),
                occ: "a".into(),
                unique: "a".into(),
            },
            body: Box::new(arrow(a.clone(), a.clone())),
        },
    );
    let mut word = int.clone();
    if let Ty::Con { tycon, .. } = &mut word {
        tycon.name = "$ghc-prim$GHC.Prim$Word#".into();
    }
    modules[0].types.extend([a, signature, word]);
    for (occ, ty) in [("f", 3), ("v", 0), ("k", 2)] {
        for b in &mut modules[0].binders {
            if b.occ == occ {
                b.ty = ty;
            }
        }
    }
    modules
}

#[test]
fn a_polymorphic_local_function_lowers_once_per_instantiation() {
    use crate::nir::{FnId, Operation, lower::lower_leaf_in_world, verify::verify_leaf_in_world};
    for (second_type, instantiations) in [(0, 1), (4, 2)] {
        let modules = polymorphic_local_world(second_type);
        let owner = modules[0].top[0].pairs[0].binder;
        let leaf = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
        let accounting = verify_leaf_in_world(&modules, 0, owner, FnId(0), &leaf).unwrap();
        assert_eq!(
            accounting.source_nodes,
            modules[0].preorder(modules[0].top[0].pairs[0].rhs).count()
        );
        let instructions: Vec<_> = leaf
            .function
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .collect();
        let definitions: Vec<_> = instructions
            .iter()
            .filter_map(|i| match &i.operation {
                Operation::LocalScope { definitions, .. } => Some(definitions),
                _ => None,
            })
            .flatten()
            .collect();
        assert_eq!(definitions.len(), instantiations);
        let targets: std::collections::BTreeSet<_> = instructions
            .iter()
            .filter_map(|i| match i.operation {
                Operation::CallLocal { target, .. } => Some(target),
                _ => None,
            })
            .collect();
        assert_eq!(targets.len(), instantiations);
        assert!(
            targets
                .iter()
                .all(|target| definitions.iter().any(|d| d.target == *target))
        );
        crate::emit::emit_entry(&modules, &sn("Main", "main")).unwrap();
    }
}

fn partially_applied_local_world() -> Vec<Module> {
    use h2r_core_ir::{Ty, TyVarId};
    let pair = |binder: Value, rhs: Value| json!({"binder":binder,"rhs":rhs,"whnf":true,"cheap":true,"trivial":false,"okForSpec":true});
    let mut f = binder("$_in$f", "f", "f");
    f["arity"] = json!(2);
    let g = binder("$_in$g", "g", "g");
    let body = json!({"node":"Let","bind":{"rec":false,"pairs":[pair(f,
        tylam("a", lam("v", tylam("b", lam("k", lvar("k"))))))]},
        "body":{"node":"Let","bind":{"rec":false,"pairs":[pair(g,
            app(app(lvar("f"), type_arg(0, "Int#")), lvar("x")))]},
            "body":app(app(lvar("g"), type_arg(0, "Int#")), lvar("y"))}});
    let mut modules = scalar_expression_world(body);
    let int = modules[0].types[0].clone();
    let var = |occ: &str| TyVarId {
        name: format!("$_in${occ}").as_str().into(),
        occ: occ.into(),
        unique: occ.into(),
    };
    let arrow = |arg: Ty, res: Ty| Ty::Fun {
        mult: Box::new(int.clone()),
        arg: Box::new(arg),
        res: Box::new(res),
    };
    let identity = Ty::ForAll {
        binder: var("b"),
        body: Box::new(arrow(Ty::Var(var("b")), Ty::Var(var("b")))),
    };
    let signature = Ty::ForAll {
        binder: var("a"),
        body: Box::new(arrow(Ty::Var(var("a")), identity.clone())),
    };
    modules[0]
        .types
        .extend([Ty::Var(var("a")), Ty::Var(var("b")), identity, signature]);
    for (occ, ty) in [("f", 5), ("v", 2), ("k", 3), ("g", 4)] {
        for b in &mut modules[0].binders {
            if b.occ == occ {
                b.ty = ty;
            }
        }
    }
    modules
}

#[test]
fn a_partially_applied_local_function_closes_over_its_instance() {
    use crate::nir::{FnId, Operation, lower::lower_leaf_in_world, verify::verify_leaf_in_world};
    let modules = partially_applied_local_world();
    let owner = modules[0].top[0].pairs[0].binder;
    let leaf = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
    let accounting = verify_leaf_in_world(&modules, 0, owner, FnId(0), &leaf).unwrap();
    assert_eq!(
        accounting.source_nodes,
        modules[0].preorder(modules[0].top[0].pairs[0].rhs).count()
    );
    let closure = leaf
        .function
        .blocks
        .iter()
        .flat_map(|b| &b.instructions)
        .find(|i| matches!(i.operation, Operation::MakeClosure { .. }))
        .expect("the partial application closes over the instance");
    assert_eq!(closure.result.ty.render(), "Int# -> forall b. b -> b");
    crate::emit::emit_entry(&modules, &sn("Main", "main")).unwrap();
}

fn closure_world_applying(use_of_p: Value) -> Vec<Module> {
    let mut f = binder("$_in$f", "f", "f");
    f["ty"] = json!(1);
    f["arity"] = json!(2);
    let p = binder("$_in$p", "p", "p");
    let pair = |binder, rhs| json!({"binder":binder,"rhs":rhs,"whnf":true,"cheap":true,"trivial":false,"okForSpec":true});
    let sum = int_op(
        "+#",
        int_op("+#", lvar("a"), lvar("b")),
        int_op("-#", lvar("x"), lvar("y")),
    );
    let body = json!({"node":"Let","bind":{"rec":false,"pairs":[pair(f,lam("a",lam("b",sum)))]},"body":{
        "node":"Let","bind":{"rec":false,"pairs":[pair(p,app(lvar("f"),lvar("x")))]},"body":use_of_p
    }});
    let mut modules = scalar_expression_world(body);
    let h2r_core_ir::Ty::Fun { res, .. } = modules[0].types[1].clone() else {
        panic!()
    };
    modules[0].types.push(*res);
    for p in modules[0]
        .binders
        .iter_mut()
        .filter(|b| b.unique == "p" || b.unique == "forced")
    {
        p.ty = 2;
    }
    modules
}

#[test]
fn closures_partial_application_and_indirect_calls_are_source_verified() {
    use crate::nir::{FnId, Operation, lower::lower_leaf_in_world, verify::verify_leaf_in_world};
    let modules = closure_world();
    let owner = modules[0].top[0].pairs[0].binder;
    let leaf = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
    let counts = verify_leaf_in_world(&modules, 0, owner, FnId(0), &leaf).unwrap();
    assert_eq!(
        counts.source_nodes,
        modules[0].preorder(modules[0].top[0].pairs[0].rhs).count()
    );
    assert!(
        leaf.function
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .any(|i| matches!(i.operation, Operation::MakeClosure { .. }))
    );
    assert_eq!(
        leaf.function
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .filter(|i| matches!(i.operation, Operation::Apply { .. }))
            .count(),
        2
    );
    assert!(
        crate::emit::emit_entry(&modules, &sn("Main", "main"))
            .unwrap()
            .contains("HClosure::entering(2")
    );
    for mutation in 0..6 {
        let mut bad = leaf.clone();
        if mutation < 3 {
            let i = bad
                .function
                .blocks
                .iter_mut()
                .flat_map(|b| &mut b.instructions)
                .find(|i| matches!(i.operation, Operation::MakeClosure { .. }))
                .unwrap();
            let Operation::MakeClosure { target, arguments } = &mut i.operation else {
                panic!()
            };
            match mutation {
                0 => arguments.swap(0, 1),
                1 => *target = crate::nir::BlockId(0),
                _ => i.origin.rule = crate::nir::Rule::CallLocal,
            }
        } else {
            let i = bad
                .function
                .blocks
                .iter_mut()
                .flat_map(|b| &mut b.instructions)
                .find(|i| matches!(i.operation, Operation::Apply { .. }))
                .unwrap();
            let Operation::Apply { callee, arguments } = &mut i.operation else {
                panic!()
            };
            match mutation {
                3 => *callee = arguments[0],
                4 => arguments.clear(),
                _ => {
                    i.result.ty = crate::nir::shared(&h2r_core_ir::Ty::Opaque {
                        pretty: "bad result".into(),
                    })
                }
            }
        }
        assert!(
            verify_leaf_in_world(&modules, 0, owner, FnId(0), &bad).is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn local_functions_and_join_loops_have_verified_captures() {
    use crate::nir::{FnId, lower::lower_leaf_in_world, verify::verify_leaf_in_world};
    for recursive in [false, true] {
        let modules = local_function_world(recursive);
        let owner = modules[0].top[0].pairs[0].binder;
        let leaf = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
        let accounting = verify_leaf_in_world(&modules, 0, owner, FnId(0), &leaf).unwrap();
        assert_eq!(
            accounting.source_nodes,
            modules[0].preorder(modules[0].top[0].pairs[0].rhs).count()
        );
        let source = generated(&crate::emit::emit_entry(&modules, &sn("Main", "main")).unwrap());
        assert!(source.contains("h2r_rt::Step::Next"));
    }
}

#[test]
fn anonymous_returned_lambda_is_source_verified_and_tamper_checked() {
    use crate::nir::{FnId, Operation, lower::lower_leaf_in_world, verify::verify_leaf_in_world};
    let p = binder("$_in$p", "p", "p");
    let lambda = lam(
        "z",
        int_op("+#", int_op("+#", lvar("x"), lvar("z")), lvar("y")),
    );
    let body = json!({"node":"Let","bind":{"rec":false,"pairs":[{"binder":p,"rhs":int_case(lvar("x"),"s",lambda,vec![]),"whnf":false,"cheap":false,"trivial":false,"okForSpec":false}]},"body":app(lvar("p"),lvar("y"))});
    let mut modules = scalar_expression_world(body);
    let h2r_core_ir::Ty::Fun { res, .. } = modules[0].types[1].clone() else {
        panic!()
    };
    modules[0].types.push(*res);
    modules[0]
        .binders
        .iter_mut()
        .find(|b| b.unique == "p")
        .unwrap()
        .ty = 2;
    for e in &mut modules[0].exprs {
        if let h2r_core_ir::Expr::Case { ty, .. } = e {
            *ty = 2;
        }
    }
    let owner = modules[0].top[0].pairs[0].binder;
    let leaf = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
    verify_leaf_in_world(&modules, 0, owner, FnId(0), &leaf).unwrap();
    crate::emit::emit_entry(&modules, &sn("Main", "main")).unwrap();
    for mutation in 0..3 {
        let mut bad = leaf.clone();
        let i = bad
            .function
            .blocks
            .iter_mut()
            .flat_map(|b| &mut b.instructions)
            .find(|i| matches!(i.operation, Operation::MakeClosure { .. }))
            .unwrap();
        let Operation::MakeClosure { target, arguments } = &mut i.operation else {
            panic!()
        };
        match mutation {
            0 => arguments.swap(0, 1),
            1 => *target = crate::nir::BlockId(0),
            _ => i.origin.source = crate::nir::Source::Expr(u32::MAX),
        }
        assert!(verify_leaf_in_world(&modules, 0, owner, FnId(0), &bad).is_err());
    }
}

#[test]
fn function_scrutinee_cases_refuse_instead_of_reentering_the_same_region() {
    use crate::nir::{FnId, lower::lower_leaf_in_world};
    let mut m = scalar_expression_world(
        json!({"node":"Case","scrut":gvar(&sn("Lib","target"),"target"),"binder":binder("$_in$f","f","f"),"ty":0,"type":"Int#","alts":[]}),
    );
    m[0].binders
        .iter_mut()
        .find(|b| b.unique == "f")
        .unwrap()
        .ty = 1;
    let owner = m[0].top[0].pairs[0].binder;
    assert!(
        lower_leaf_in_world(&m, 0, owner, FnId(0))
            .unwrap_err()
            .reason
            .contains("scrutinee")
    );
}

#[test]
fn function_alias_entry_uses_the_returned_closure() {
    let mut modules = scalar_emission_world();
    // Rebuild lexical references by loading a new source module.
    let types = modules[0].types.clone();
    modules[0] = module(
        "Main",
        vec![(
            binder(&sn("Main", "main"), "main", "main"),
            gvar(&sn("Lib", "target"), "target"),
        )],
        json!({}),
    );
    modules[0].types = types;
    let owner = modules[0].top[0].pairs[0].binder;
    modules[0].binders[owner as usize].ty = 1;
    let source = generated(&crate::emit::emit_entry(&modules, &sn("Main", "main")).unwrap());
    assert!(source.contains("fn h2r_entry(a0: i64, a1: i64)"));
    assert!(source.contains(".apply(vec![HField::Int64(a0), HField::Int64(a1)])"));
}

#[test]
fn local_function_verifier_rejects_capture_target_and_definition_corruption() {
    use crate::nir::{FnId, Operation, lower::lower_leaf_in_world, verify::verify_leaf_in_world};
    let modules = local_function_world(true);
    let owner = modules[0].top[0].pairs[0].binder;
    let leaf = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
    for mutation in 0..7 {
        let mut bad = leaf.clone();
        if mutation < 4 {
            let Operation::LocalScope {
                definitions,
                target,
                arguments,
            } = &mut bad.function.blocks[0].instructions[0].operation
            else {
                panic!()
            };
            match mutation {
                0 => arguments.swap(0, 1),
                1 => definitions[0].binder = owner,
                2 => definitions[0].target = *target,
                _ => definitions.clear(),
            }
        } else {
            let i = bad
                .function
                .blocks
                .iter_mut()
                .flat_map(|b| &mut b.instructions)
                .find(|i| matches!(i.operation, Operation::CallLocal { .. }))
                .unwrap();
            let Operation::CallLocal { target, arguments } = &mut i.operation else {
                panic!()
            };
            match mutation {
                4 => arguments.swap(0, 1),
                5 => *target = crate::nir::BlockId(0),
                _ => {
                    arguments.pop();
                }
            }
        }
        assert!(
            verify_leaf_in_world(&modules, 0, owner, FnId(0), &bad).is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn an_unlifted_value_recurses_as_a_function_and_escaping_local_functions_are_refused() {
    use crate::nir::{FnId, lower::lower_leaf_in_world};
    let mut m = module(
        "Main",
        vec![(
            binder(&sn("Main", "cycle"), "cycle", "cycle"),
            lvar("cycle"),
        )],
        json!({}),
    );
    m.types = scalar_emission_world()[0].types.clone();
    assert!(
        crate::emit::emit_entry(&[m], &sn("Main", "cycle"))
            .unwrap()
            .contains("fn f_0() -> i64")
    );
    for mutation in 0..3 {
        let mut modules = local_function_world(true);
        let owner = modules[0].top[0].pairs[0].binder;
        let let_id = modules[0]
            .exprs
            .iter()
            .position(|e| matches!(e, h2r_core_ir::Expr::Let { .. }))
            .unwrap();
        let h2r_core_ir::Expr::Let { bind, body } = modules[0].exprs[let_id].clone() else {
            panic!()
        };
        match mutation {
            0 => {
                // Recursive RHS is not in scope in a non-recursive binding.
                let h2r_core_ir::Expr::Let { bind, .. } = &mut modules[0].exprs[let_id] else {
                    panic!()
                };
                bind.recursive = false;
            }
            1 => {
                // Returning a function instead of a saturated call is not supported.
                let h2r_core_ir::Expr::App { fun, .. } = modules[0].expr(body) else {
                    panic!()
                };
                let replacement = modules[0].expr(*fun).clone();
                modules[0].exprs[body as usize] = replacement;
            }
            _ => {
                modules[0].binders[bind.pairs[0].binder as usize].ty = 0;
            }
        }
        assert!(
            lower_leaf_in_world(&modules, 0, owner, FnId(0)).is_err(),
            "mutation {mutation}"
        );
    }
}

fn int_op(symbol: &str, left: Value, right: Value) -> Value {
    app(
        app(gvar(&format!("$ghc-prim$GHC.Prim${symbol}"), symbol), left),
        right,
    )
}

fn strict_case(scrut: Value, unique: &str, body: Value) -> Value {
    json!({
        "node": "Case", "scrut": scrut,
        "binder": binder("$_in$intermediate", "intermediate", unique),
        "type": "Int#", "ty": 0,
        "alts": [{"con": {"kind": "DEFAULT"}, "binders": [], "rhs": body}]
    })
}

fn scalar_expression_world(body: Value) -> Vec<Module> {
    let mut world = scalar_emission_world();
    let types = world[0].types.clone();
    world[0] = module(
        "Main",
        vec![(
            binder(&sn("Main", "main"), "main", "main"),
            lam("x", lam("y", body)),
        )],
        json!({}),
    );
    world[0].types = types;
    let owner = world[0].top[0].pairs[0].binder;
    world[0].binders[owner as usize].ty = 1;
    world[0].binders[owner as usize].arity = Some(2);
    for symbol in ["+#", "-#", "*#", "==#", "/=#", "<#", "<=#", ">#", ">=#"] {
        world[0]
            .ids
            .extend(primitive_emission_world(symbol)[0].ids.clone());
    }
    world
}

#[test]
fn scalar_composition_verifies_nested_calls_and_strict_case_chains() {
    use crate::nir::{FnId, Operation, lower::lower_leaf_in_world, verify::verify_leaf_in_world};
    let sum = || int_op("+#", lvar("x"), lvar("y"));
    for body in [
        int_op("*#", sum(), int_op("-#", lvar("x"), lvar("y"))),
        strict_case(
            sum(),
            "s",
            strict_case(
                int_op("-#", lvar("s"), lvar("y")),
                "t",
                int_op("*#", lvar("s"), lvar("t")),
            ),
        ),
        strict_case(
            strict_case(sum(), "inner", lvar("inner")),
            "outer",
            lvar("outer"),
        ),
        // A discarded result must not discard the scrutinee evaluation.
        strict_case(
            app(
                app(gvar(&sn("Lib", "target"), "target"), lvar("x")),
                lvar("y"),
            ),
            "unused",
            lvar("x"),
        ),
    ] {
        let modules = scalar_expression_world(body);
        let owner = modules[0].top[0].pairs[0].binder;
        let leaf = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
        let accounting = verify_leaf_in_world(&modules, 0, owner, FnId(0), &leaf).unwrap();
        assert_eq!(
            accounting.source_nodes,
            modules[0].preorder(modules[0].top[0].pairs[0].rhs).count()
        );
        let emitted = generated(&crate::emit::emit_entry(&modules, &sn("Main", "main")).unwrap());
        assert!(emitted.contains("fn f_"));
        for index in 0..leaf.function.blocks[0].instructions.len() {
            for mutation in 0..4 {
                let mut bad = leaf.clone();
                let instruction = &mut bad.function.blocks[0].instructions[index];
                match mutation {
                    0 => instruction.origin.source = crate::nir::Source::Binder(owner),
                    1 => instruction.operation = Operation::Move(crate::nir::ValueId(0)),
                    2 => instruction.origin.rule = crate::nir::Rule::EraseCast,
                    _ => {
                        bad.function.blocks[0].instructions.remove(index);
                    }
                }
                assert!(
                    verify_leaf_in_world(&modules, 0, owner, FnId(0), &bad).is_err(),
                    "index {index}, mutation {mutation}"
                );
            }
        }
    }
}

#[test]
fn scalar_cases_refuse_duplicate_defaults_wrong_types_and_alternative_binders() {
    use crate::nir::{FnId, lower::lower_leaf_in_world, verify::verify_leaf_in_world};
    let modules = scalar_expression_world(strict_case(
        int_op("+#", lvar("x"), lvar("y")),
        "s",
        lvar("s"),
    ));
    let owner = modules[0].top[0].pairs[0].binder;
    let leaf = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
    for mutation in 0..6 {
        let mut bad = scalar_expression_world(strict_case(
            int_op("+#", lvar("x"), lvar("y")),
            "s",
            lvar("s"),
        ));
        let m = &mut bad[0];
        let h2r_core_ir::Expr::Case {
            binder, ty, alts, ..
        } = m
            .exprs
            .iter_mut()
            .find(|e| matches!(e, h2r_core_ir::Expr::Case { .. }))
            .unwrap()
        else {
            panic!()
        };
        match mutation {
            0 => alts.clear(),
            1 => alts.push(alts[0].clone()),
            2 => alts[0].binders.push(*binder),
            3 => *ty = 1,
            4 => m.binders[*binder as usize].ty = 1,
            _ => {
                alts[0].con = h2r_core_ir::AltCon::LitAlt {
                    lit: h2r_core_ir::Lit::int(0),
                }
            }
        }
        assert!(
            lower_leaf_in_world(&bad, 0, owner, FnId(0)).is_err(),
            "mutation {mutation}"
        );
        assert!(
            verify_leaf_in_world(&bad, 0, owner, FnId(0), &leaf).is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn computed_arguments_do_not_enable_eager_lifted_evaluation() {
    use crate::nir::{FnId, lower::lower_leaf_in_world};
    let mut modules = scalar_expression_world(app(
        app(
            gvar(&sn("Lib", "target"), "target"),
            app(
                app(gvar(&sn("Lib", "target"), "target"), lvar("x")),
                lvar("y"),
            ),
        ),
        lvar("y"),
    ));
    for module in &mut modules {
        for ty in &mut module.types {
            fn lift(ty: &mut h2r_core_ir::Ty) {
                match ty {
                    h2r_core_ir::Ty::Con { tycon, .. } => tycon.name = "$base$GHC.Types$Int".into(),
                    h2r_core_ir::Ty::Fun { arg, res, .. } => {
                        lift(arg);
                        lift(res);
                    }
                    _ => {}
                }
            }
            lift(ty);
        }
    }
    let owner = modules[0].top[0].pairs[0].binder;
    assert!(
        lower_leaf_in_world(&modules, 0, owner, FnId(0))
            .unwrap_err()
            .reason
            .contains("call arguments")
    );
}

fn int_case(scrut: Value, unique: &str, default: Value, arms: Vec<(i64, Value)>) -> Value {
    let mut value = strict_case(scrut, unique, default);
    for (pattern, rhs) in arms {
        value["alts"].as_array_mut().unwrap().push(json!({
            "con": {"kind": "LitAlt", "lit": int_lit(pattern)},
            "binders": [], "rhs": rhs
        }));
    }
    value
}

fn branching_world() -> Vec<Module> {
    scalar_expression_world(int_case(
        int_op("+#", lvar("x"), lvar("y")),
        "s",
        int_case(
            int_op("<#", lvar("s"), lvar("x")),
            "less",
            int_op("*#", lvar("s"), lvar("y")),
            vec![(0, int_op("-#", lvar("s"), lvar("x")))],
        ),
        vec![
            (-1, lvar("s")),
            (
                0,
                app(
                    app(gvar(&sn("Lib", "target"), "target"), lvar("y")),
                    lvar("x"),
                ),
            ),
            (i64::MIN, lvar("x")),
            (i64::MAX, lvar("y")),
        ],
    ))
}

fn region_expression() -> Value {
    int_op(
        "*#",
        int_case(
            lvar("x"),
            "a",
            int_op("+#", lvar("a"), lvar("y")),
            vec![(0, lvar("y"))],
        ),
        int_case(
            int_case(lvar("y"), "b", lvar("b"), vec![(0, lvar("x"))]),
            "c",
            int_op("-#", lvar("c"), lvar("x")),
            vec![(1, int_op("+#", lvar("c"), lvar("y")))],
        ),
    )
}

fn box_int(value: Value) -> Value {
    app(gvar(crate::nir::boxed::CONSTRUCTOR, "I#"), value)
}

fn unbox_int(scrut: Value, body: Value, boxed_result: bool) -> Value {
    let mut value = strict_case(scrut, "boxed_case", body);
    value["binder"]["ty"] = json!(2);
    value["ty"] = json!(if boxed_result { 2 } else { 0 });
    value["alts"][0]["con"] =
        json!({"kind":"DataAlt", "name":crate::nir::boxed::CONSTRUCTOR, "occ":"I#", "tag":1});
    value["alts"][0]["binders"] = json!([binder("$_in$field", "field", "field")]);
    value
}

fn boxed_world(body: Value, boxed_x: bool, boxed_result: bool) -> Vec<Module> {
    use h2r_core_ir::Ty;
    let mut modules = scalar_expression_world(body);
    let m = &mut modules[0];
    let boxed = Box::new(Ty::Con {
        tycon: h2r_core_ir::TyConId {
            name: crate::nir::boxed::INT.into(),
            occ: "Int".into(),
            unique: "boxed-int".into(),
        },
        args: vec![],
    });
    m.types.push(*boxed.clone());
    if let Ty::Fun { arg, res, .. } = &mut m.types[1] {
        if boxed_x {
            *arg = boxed.clone();
        }
        if let Ty::Fun { res, .. } = res.as_mut()
            && boxed_result
        {
            *res = boxed;
        }
    }
    if boxed_x {
        for binder in &mut m.binders {
            if binder.unique == "x" {
                binder.ty = 2;
            }
        }
    }
    let name = crate::nir::boxed::CONSTRUCTOR;
    m.ids.insert(
        name.into(),
        serde_json::from_value(json!({
            "name": name, "occ":"I#", "arity":1, "details":"[DataCon]", "isJoinPoint":false,
            "dataCon":{"name":name, "repArity":1, "tag":1, "strictFields":[false]},
            "dmdSig":{"args":[], "diverges":false, "pretty":""}
        }))
        .unwrap(),
    );
    modules
}

#[test]
fn boxed_int_construction_cases_and_captures_are_source_verified() {
    use crate::nir::{FnId, lower::lower_leaf_in_world, verify::verify_leaf_in_world};
    let mut branch = int_case(
        lvar("y"),
        "s",
        box_int(lvar("s")),
        vec![(0, box_int(lvar("y")))],
    );
    branch["ty"] = json!(2);
    let mut default_case = unbox_int(lvar("x"), lvar("y"), false);
    default_case["alts"][0]["con"] = json!({"kind":"DEFAULT"});
    default_case["alts"][0]["binders"] = json!([]);
    for (body, input, result) in [
        (box_int(int_op("+#", lvar("x"), lvar("y"))), false, true),
        (
            unbox_int(box_int(lvar("x")), lvar("field"), false),
            false,
            false,
        ),
        (
            unbox_int(lvar("x"), int_op("+#", lvar("field"), lvar("y")), false),
            true,
            false,
        ),
        (unbox_int(lvar("x"), lvar("boxed_case"), true), true, true),
        (
            unbox_int(
                lvar("x"),
                int_case(lvar("field"), "s", lvar("s"), vec![(0, lvar("y"))]),
                false,
            ),
            true,
            false,
        ),
        (default_case, true, false),
        (branch.clone(), false, true),
        (unbox_int(branch, lvar("field"), false), false, false),
    ] {
        let modules = boxed_world(body, input, result);
        let owner = modules[0].top[0].pairs[0].binder;
        let leaf = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
        let counts = verify_leaf_in_world(&modules, 0, owner, FnId(0), &leaf).unwrap();
        assert_eq!(
            counts.source_nodes,
            modules[0].preorder(modules[0].top[0].pairs[0].rhs).count()
        );
        let rust = generated(&crate::emit::emit_entry(&modules, &sn("Main", "main")).unwrap());
        assert!(rust.contains("use h2r_rt::Int as HInt"));
        check_scalar_renumbering(modules);
    }
}

#[test]
fn boxed_constructor_requires_exact_identity_metadata_and_carriers() {
    use crate::nir::{FnId, lower::lower_leaf_in_world};
    for mutation in 0..6 {
        let mut modules = boxed_world(box_int(lvar("x")), false, true);
        let info = modules[0]
            .ids
            .get_mut(crate::nir::boxed::CONSTRUCTOR)
            .unwrap();
        match mutation {
            0 => info.arity = 2,
            1 => info.details = "[VanillaId]".into(),
            2 => info.data_con.as_mut().unwrap().name = "$other$Types$I#".into(),
            3 => info.data_con.as_mut().unwrap().tag = 2,
            4 => info.data_con.as_mut().unwrap().rep_arity = 2,
            _ => info.data_con = None,
        }
        let owner = modules[0].top[0].pairs[0].binder;
        assert!(
            lower_leaf_in_world(&modules, 0, owner, FnId(0)).is_err(),
            "mutation {mutation}"
        );
    }
    for mutation in 0..5 {
        let mut body = unbox_int(lvar("x"), lvar("field"), false);
        match mutation {
            0 => body["alts"][0]["con"]["tag"] = json!(2),
            1 => body["alts"][0]["con"]["name"] = json!("$other$Types$I#"),
            2 => body["alts"][0]["binders"][0]["ty"] = json!(2),
            3 => body["alts"][0]["binders"] = json!([]),
            _ => body["ty"] = json!(2),
        }
        let modules = boxed_world(body, true, false);
        assert!(crate::emit::emit_entry(&modules, &sn("Main", "main")).is_err());
    }
}

#[test]
fn boxed_case_verifier_rejects_removed_forcing_and_wrong_fields() {
    use crate::nir::{
        FnId, Operation, Rule, lower::lower_leaf_in_world, verify::verify_leaf_in_world,
    };
    let modules = boxed_world(
        unbox_int(lvar("x"), int_op("+#", lvar("field"), lvar("y")), false),
        true,
        false,
    );
    let owner = modules[0].top[0].pairs[0].binder;
    let leaf = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
    for mutation in 0..5 {
        let mut bad = leaf.clone();
        let instruction = &mut bad.function.blocks[0].instructions[0];
        match mutation {
            0 => instruction.operation = Operation::Move(crate::nir::ValueId(1)),
            1 => instruction.operation = Operation::BoxInt(crate::nir::ValueId(1)),
            2 => instruction.origin.rule = Rule::StrictPosition,
            3 => instruction.result.ty = crate::nir::shared(&modules[0].types[2]),
            _ => {
                bad.function.blocks[0].instructions.remove(0);
            }
        }
        assert!(verify_leaf_in_world(&modules, 0, owner, FnId(0), &bad).is_err());
    }
}

#[test]
fn boxed_constructor_verifier_rejects_changed_field_and_eager_lifted_arguments() {
    use crate::nir::{FnId, Operation, lower::lower_leaf_in_world, verify::verify_leaf_in_world};
    let modules = boxed_world(box_int(lvar("x")), false, true);
    let owner = modules[0].top[0].pairs[0].binder;
    let mut leaf = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
    leaf.function.blocks[0].instructions[0].operation = Operation::BoxInt(crate::nir::ValueId(1));
    assert!(verify_leaf_in_world(&modules, 0, owner, FnId(0), &leaf).is_err());
    // A computed lifted argument is accepted only with explicit delay evidence.
    let modules = boxed_world(
        app(
            app(gvar(&sn("Main", "main"), "main"), box_int(lvar("y"))),
            lvar("y"),
        ),
        true,
        false,
    );
    let owner = modules[0].top[0].pairs[0].binder;
    let mut leaf = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
    let instruction = &mut leaf.function.blocks[0].instructions[0];
    let Operation::DelayBlock { target, arguments } = &instruction.operation else {
        panic!()
    };
    instruction.operation = Operation::EvaluateBlock {
        target: *target,
        arguments: arguments.clone(),
    };
    instruction.origin.rule = crate::nir::Rule::EvaluateBlock;
    assert!(verify_leaf_in_world(&modules, 0, owner, FnId(0), &leaf).is_err());
}

fn lazy_let(unique: &str, rhs: Value, body: Value) -> Value {
    let mut local = binder("$_in$local", "local", unique);
    local["ty"] = json!(2);
    json!({"node":"Let", "bind":{"rec":false, "pairs":[{
        "binder":local, "rhs":rhs, "whnf":false, "trivial":false, "cheap":false, "okForSpec":false
    }]}, "body":body})
}

#[test]
fn lazy_lets_preserve_scope_sharing_and_complete_source_accounting() {
    use crate::nir::{
        FnId, Operation, Rule, lower::lower_leaf_in_world, verify::verify_leaf_in_world,
    };
    let bodies = [
        lazy_let(
            "z",
            box_int(lvar("y")),
            unbox_int(lvar("z"), int_op("+#", lvar("field"), lvar("field")), false),
        ),
        lazy_let("z", box_int(lvar("y")), lvar("y")),
        lazy_let("z", lvar("x"), unbox_int(lvar("z"), lvar("field"), false)),
        lazy_let(
            "z",
            box_int(lvar("y")),
            lazy_let(
                "w",
                unbox_int(
                    lvar("z"),
                    box_int(int_op("+#", lvar("field"), lvar("y"))),
                    true,
                ),
                unbox_int(lvar("w"), lvar("field"), false),
            ),
        ),
        lazy_let(
            "x",
            box_int(lvar("y")),
            unbox_int(lvar("x"), lvar("field"), false),
        ),
        int_op(
            "+#",
            lazy_let(
                "z",
                box_int(lvar("y")),
                unbox_int(lvar("z"), lvar("field"), false),
            ),
            lvar("y"),
        ),
    ];
    for body in bodies {
        let modules = boxed_world(body, true, false);
        let owner = modules[0].top[0].pairs[0].binder;
        let leaf = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
        let counts = verify_leaf_in_world(&modules, 0, owner, FnId(0), &leaf).unwrap();
        assert_eq!(
            counts.source_nodes,
            modules[0].preorder(modules[0].top[0].pairs[0].rhs).count()
        );
        assert!(
            leaf.function
                .blocks
                .iter()
                .flat_map(|b| &b.instructions)
                .any(|i| i.origin.rule == Rule::LazyBinding
                    && matches!(i.operation, Operation::Move(_)))
        );
        crate::emit::emit_entry(&modules, &sn("Main", "main")).unwrap();
        check_scalar_renumbering(modules);
    }
}

#[test]
fn lazy_let_verifier_rejects_eagerness_recapture_cycles_and_wrong_identity() {
    use crate::nir::{
        BlockId, FnId, Operation, Rule, lower::lower_leaf_in_world, verify::verify_leaf_in_world,
    };
    let modules = boxed_world(
        lazy_let(
            "z",
            unbox_int(
                lvar("x"),
                box_int(int_op("+#", lvar("field"), lvar("y"))),
                true,
            ),
            unbox_int(lvar("z"), lvar("field"), false),
        ),
        true,
        false,
    );
    let owner = modules[0].top[0].pairs[0].binder;
    let leaf = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
    verify_leaf_in_world(&modules, 0, owner, FnId(0), &leaf).unwrap();
    for mutation in 0..9 {
        let mut bad = leaf.clone();
        let block = &mut bad.function.blocks[0];
        let Operation::DelayBlock { target, arguments } = &mut block.instructions[0].operation
        else {
            panic!()
        };
        match mutation {
            0 => *target = BlockId(0),
            1 => arguments.swap(0, 1),
            2 => arguments[0] = crate::nir::ValueId(999),
            3 => {
                arguments.pop();
            }
            4 => {
                block.instructions[0].operation = Operation::EvaluateBlock {
                    target: *target,
                    arguments: arguments.clone(),
                };
                block.instructions[0].origin.rule = Rule::EvaluateBlock;
            }
            5 => block.instructions[1].operation = Operation::Move(block.params[0].id),
            6 => block.instructions[1].origin.rule = Rule::StrictPosition,
            7 => {
                block.instructions.remove(1);
            }
            _ => block.instructions[0].result.ty = crate::nir::shared(&modules[0].types[0]),
        }
        assert!(
            verify_leaf_in_world(&modules, 0, owner, FnId(0), &bad).is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn a_recursive_value_group_fills_its_cells_before_the_body() {
    use crate::nir::{
        FnId, Operation, Rule, lower::lower_leaf_in_world, verify::verify_leaf_in_world,
    };
    let mut body = lazy_let(
        "z",
        box_int(lvar("y")),
        unbox_int(lvar("z"), lvar("field"), false),
    );
    body["bind"]["rec"] = json!(true);
    let modules = boxed_world(body, true, false);
    let owner = modules[0].top[0].pairs[0].binder;
    let leaf = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
    verify_leaf_in_world(&modules, 0, owner, FnId(0), &leaf).unwrap();
    let instructions = &leaf.function.blocks[0].instructions;
    assert!(matches!(
        instructions
            .iter()
            .map(|i| &i.operation)
            .collect::<Vec<_>>()
            .as_slice(),
        [
            Operation::PendingCell,
            Operation::DelayBlock { .. },
            Operation::FillCell { .. },
            ..
        ]
    ));
    for mutation in 0..3 {
        let mut bad = leaf.clone();
        let instructions = &mut bad.function.blocks[0].instructions;
        match mutation {
            0 => {
                instructions.remove(2);
            }
            1 => {
                let delayed = instructions[1].result.id;
                instructions[2].operation = Operation::FillCell {
                    cell: delayed,
                    value: delayed,
                };
            }
            _ => instructions[0].origin.rule = Rule::LazyBinding,
        }
        assert!(
            verify_leaf_in_world(&modules, 0, owner, FnId(0), &bad).is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn lazy_lets_refuse_join_unlifted_and_out_of_scope_bindings() {
    use crate::nir::{FnId, lower::lower_leaf_in_world};
    for mutation in 1..6 {
        let mut body = lazy_let(
            "z",
            box_int(lvar("y")),
            unbox_int(lvar("z"), lvar("field"), false),
        );
        match mutation {
            1 => {
                body["bind"]["pairs"][0]["binder"]["isJoinPoint"] = json!(true);
                body["bind"]["pairs"][0]["binder"]["arity"] = json!(1);
            }
            2 => body["bind"]["pairs"][0]["binder"]["ty"] = json!(0),
            3 => body["bind"]["pairs"][0]["rhs"] = lvar("z"),
            4 => body["body"] = lvar("missing"),
            _ => body["bind"]["pairs"][0]["rhs"] = json!({"node":"Coercion"}),
        }
        let modules = boxed_world(body, true, false);
        let owner = modules[0].top[0].pairs[0].binder;
        assert!(
            lower_leaf_in_world(&modules, 0, owner, FnId(0)).is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn lazy_argument_cases_and_lets_cannot_be_replaced_by_eager_regions() {
    use crate::nir::{
        FnId, Operation, Rule,
        lower::lower_leaf_in_world,
        verify::{verify, verify_leaf_in_world},
    };
    let mut branch = int_case(lvar("y"), "s", box_int(lvar("s")), vec![(0, lvar("x"))]);
    branch["ty"] = json!(2);
    for argument in [branch, lazy_let("z", box_int(lvar("y")), lvar("z"))] {
        let modules = boxed_world(
            app(app(gvar(&sn("Main", "main"), "main"), argument), lvar("y")),
            true,
            false,
        );
        let owner = modules[0].top[0].pairs[0].binder;
        let mut leaf = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
        let instruction = &mut leaf.function.blocks[0].instructions[0];
        let Operation::DelayBlock { target, arguments } = &instruction.operation else {
            panic!()
        };
        instruction.operation = Operation::EvaluateBlock {
            target: *target,
            arguments: arguments.clone(),
        };
        instruction.origin.rule = Rule::EvaluateBlock;
        verify(&leaf.function).unwrap(); // Well typed, but semantically too strict.
        assert!(
            verify_leaf_in_world(&modules, 0, owner, FnId(0), &leaf)
                .unwrap_err()
                .contains("must remain delayed")
        );
        check_scalar_renumbering(modules);
    }
}

#[test]
fn lazy_variable_alias_reuses_the_existing_value_without_a_new_thunk() {
    use crate::nir::{FnId, Operation, lower::lower_leaf_in_world};
    let modules = boxed_world(lazy_let("z", lvar("x"), lvar("z")), true, true);
    let owner = modules[0].top[0].pairs[0].binder;
    let leaf = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
    assert_eq!(leaf.function.blocks.len(), 1);
    let block = &leaf.function.blocks[0];
    assert_eq!(block.instructions.len(), 1);
    assert!(
        matches!(block.instructions[0].operation, Operation::Move(value) if value == block.params[0].id)
    );
}

#[test]
fn thunk_source_verification_rejects_well_typed_capture_swaps_and_eager_lets() {
    use crate::nir::{
        FnId, Operation, Rule,
        lower::lower_leaf_in_world,
        verify::{verify, verify_leaf_in_world},
    };
    let mut inner = unbox_int(
        lvar("y"),
        box_int(int_op("+#", lvar("field"), lvar("field_y"))),
        true,
    );
    inner["binder"] = binder("$_in$boxed_y", "boxed_y", "boxed_y");
    inner["binder"]["ty"] = json!(2);
    inner["alts"][0]["binders"] = json!([binder("$_in$field_y", "field_y", "field_y")]);
    let mut modules = boxed_world(
        lazy_let("z", unbox_int(lvar("x"), inner, true), lvar("z")),
        true,
        true,
    );
    let boxed_ty = modules[0].types[2].clone();
    if let h2r_core_ir::Ty::Fun { res, .. } = &mut modules[0].types[1]
        && let h2r_core_ir::Ty::Fun { arg, .. } = res.as_mut()
    {
        **arg = boxed_ty;
    }
    modules[0]
        .binders
        .iter_mut()
        .find(|b| b.unique == "y")
        .unwrap()
        .ty = 2;
    let owner = modules[0].top[0].pairs[0].binder;
    let leaf = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
    for eager in [false, true] {
        let mut bad = leaf.clone();
        let instruction = &mut bad.function.blocks[0].instructions[0];
        let Operation::DelayBlock { target, arguments } = &mut instruction.operation else {
            panic!()
        };
        if eager {
            instruction.operation = Operation::EvaluateBlock {
                target: *target,
                arguments: arguments.clone(),
            };
            instruction.origin.rule = Rule::EvaluateBlock;
        } else {
            arguments.swap(0, 1);
        }
        verify(&bad.function).unwrap();
        assert!(verify_leaf_in_world(&modules, 0, owner, FnId(0), &bad).is_err());
    }
}

#[test]
fn scalar_regions_compose_operands_scrutinees_and_strict_scopes() {
    use crate::nir::{FnId, Operation, lower::lower_leaf_in_world, verify::verify_leaf_in_world};
    for body in [
        region_expression(),
        strict_case(
            region_expression(),
            "shared",
            int_op(
                "+#",
                lvar("shared"),
                int_case(lvar("shared"), "s", lvar("s"), vec![(0, lvar("x"))]),
            ),
        ),
        int_case(region_expression(), "s", lvar("s"), vec![(0, lvar("y"))]),
        int_op(
            "+#",
            strict_case(lvar("x"), "single", lvar("single")),
            lvar("y"),
        ),
        app(
            app(gvar(&sn("Lib", "target"), "target"), region_expression()),
            lvar("x"),
        ),
    ] {
        let modules = scalar_expression_world(body);
        let owner = modules[0].top[0].pairs[0].binder;
        let leaf = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
        let counts = verify_leaf_in_world(&modules, 0, owner, FnId(0), &leaf).unwrap();
        assert_eq!(
            counts.source_nodes,
            modules[0].preorder(modules[0].top[0].pairs[0].rhs).count()
        );
        assert!(
            leaf.function
                .blocks
                .iter()
                .flat_map(|b| &b.instructions)
                .any(|i| matches!(i.operation, Operation::EvaluateBlock { .. }))
        );
        crate::emit::emit_entry(&modules, &sn("Main", "main")).unwrap();
    }
    let modules = scalar_expression_world(region_expression());
    let rust = generated(&crate::emit::emit_entry(&modules, &sn("Main", "main")).unwrap());
    assert_eq!(
        rust.matches("wrapping_mul").count(),
        1,
        "continuation must not be cloned into arms"
    );
    assert_eq!(rust.matches("match v").count(), 3);
}

#[test]
fn scalar_region_verifier_rejects_forged_calls_captures_and_cycles() {
    use crate::nir::{
        BlockId, FnId, Operation, Rule, Source, ValueId, lower::lower_leaf_in_world,
        verify::verify_leaf_in_world,
    };
    let modules = scalar_expression_world(region_expression());
    let owner = modules[0].top[0].pairs[0].binder;
    let leaf = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
    for mutation in 0..10 {
        let mut bad = leaf.clone();
        let instruction = &mut bad.function.blocks[0].instructions[0];
        let Operation::EvaluateBlock { target, arguments } = &mut instruction.operation else {
            panic!()
        };
        match mutation {
            0 => *target = BlockId(0),
            1 => *target = BlockId(999),
            2 => arguments.swap(0, 1),
            3 => arguments[0] = arguments[1],
            4 => {
                arguments.pop();
            }
            5 => arguments[0] = instruction.result.id,
            6 => instruction.origin.rule = Rule::IntSwitch,
            7 => instruction.origin.source = Source::Binder(owner),
            8 => instruction.result.id = ValueId(999),
            _ => {
                *target = leaf.function.blocks[0]
                    .instructions
                    .iter()
                    .find_map(|i| match i.operation {
                        Operation::EvaluateBlock { target: other, .. } if other != *target => {
                            Some(other)
                        }
                        _ => None,
                    })
                    .unwrap()
            }
        }
        assert!(
            verify_leaf_in_world(&modules, 0, owner, FnId(0), &bad).is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn scalar_regions_refuse_unsupported_arms_and_escaped_binders() {
    use crate::nir::{FnId, lower::lower_leaf_in_world};
    for arm in [
        json!({"node": "Coercion"}),
        lvar("not-in-scope"),
        app(gvar("$missing$Module$function", "function"), lvar("x")),
    ] {
        let modules = scalar_expression_world(int_op(
            "+#",
            int_case(lvar("x"), "inner", lvar("inner"), vec![(0, arm)]),
            lvar("y"),
        ));
        assert!(crate::emit::emit_entry(&modules, &sn("Main", "main")).is_err());
    }
    let modules = scalar_expression_world(int_op(
        "+#",
        int_case(lvar("x"), "inner", lvar("inner"), vec![(0, lvar("y"))]),
        lvar("inner"),
    ));
    let owner = modules[0].top[0].pairs[0].binder;
    assert!(lower_leaf_in_world(&modules, 0, owner, FnId(0)).is_err());
}

#[test]
fn scalar_switches_have_explicit_environments_and_complete_source_accounting() {
    use crate::nir::{Exit, FnId, lower::lower_leaf_in_world, verify::verify_leaf_in_world};
    let modules = branching_world();
    let owner = modules[0].top[0].pairs[0].binder;
    let leaf = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
    assert_eq!(leaf.function.blocks.len(), 8);
    let counts = verify_leaf_in_world(&modules, 0, owner, FnId(0), &leaf).unwrap();
    assert_eq!(
        counts.source_nodes,
        modules[0].preorder(modules[0].top[0].pairs[0].rhs).count()
    );
    let Exit::IntSwitch { args, arms, .. } = &leaf.function.blocks[0].terminator.exit else {
        panic!()
    };
    assert_eq!(args.len(), 3);
    assert_eq!(
        arms.iter().map(|(n, _)| *n).collect::<Vec<_>>(),
        [-1, 0, i64::MIN, i64::MAX]
    );
    let rust = generated(&crate::emit::emit_entry(&modules, &sn("Main", "main")).unwrap());
    assert_eq!(rust.matches("match v").count(), 2);
    assert!(rust.contains("-9223372036854775808i64 =>"));
    assert!(rust.contains("9223372036854775807i64 =>"));
    assert_eq!(
        rust.matches("fn f_").count(),
        2,
        "branch-only import must be emitted"
    );
}

#[test]
fn scalar_switch_verifier_rejects_forged_control_flow_and_environments() {
    use crate::nir::{
        BlockId, Exit, FnId, Rule, Source, ValueId, lower::lower_leaf_in_world,
        verify::verify_leaf_in_world,
    };
    let modules = branching_world();
    let owner = modules[0].top[0].pairs[0].binder;
    let leaf = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
    for mutation in 0..13 {
        let mut bad = leaf.clone();
        let block = &mut bad.function.blocks[0];
        let Exit::IntSwitch {
            scrutinee,
            arms,
            default,
            args,
        } = &mut block.terminator.exit
        else {
            panic!()
        };
        match mutation {
            0 => arms[0].0 = 99,
            1 => arms.swap(0, 1),
            2 => std::mem::swap(&mut arms[0].1, default),
            3 => args.swap(0, 1),
            4 => *scrutinee = ValueId(0),
            5 => args[2] = ValueId(0),
            6 => *default = BlockId(0),
            7 => arms[0].1 = BlockId(999),
            8 => block.terminator.origin.rule = Rule::Return,
            9 => block.terminator.origin.source = Source::Binder(owner),
            10 => {
                arms.pop();
            }
            11 => {
                let duplicate = bad.function.blocks.last().unwrap().clone();
                bad.function.blocks.push(duplicate);
            }
            _ => {
                let last = bad.function.blocks.last_mut().unwrap();
                last.terminator.exit = Exit::Return(last.params[0].id);
            }
        }
        assert!(
            verify_leaf_in_world(&modules, 0, owner, FnId(0), &bad).is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn scalar_switch_ids_are_not_source_identities() {
    check_scalar_renumbering(branching_world());
    check_scalar_renumbering(scalar_expression_world(region_expression()));
}

fn data_construct(name: &str, fields: Vec<Value>) -> Value {
    fields.into_iter().fold(gvar(&sn("Main", name), name), app)
}

fn data_case(scrut: Value, default: bool) -> Value {
    let mut case = strict_case(scrut, "case_data", lvar("x"));
    case["binder"]["ty"] = json!(3);
    case["alts"] = json!([
        {"con":{"kind":"DataAlt", "name":sn("Main","Empty"), "occ":"Empty", "tag":1}, "binders":[], "rhs":lvar("y")},
        {"con":{"kind":"DataAlt", "name":sn("Main","Pair"), "occ":"Pair", "tag":2}, "binders":[binder("$_in$a","a","a"), binder("$_in$b","b","b")], "rhs":int_op("-#",lvar("a"),lvar("b"))}
    ]);
    if default {
        case["alts"][0]["con"] = json!({"kind":"DEFAULT"});
    }
    case
}

fn data_world(body: Value) -> Vec<Module> {
    use h2r_core_ir::Ty;
    let mut modules = boxed_world(body, false, false);
    let m = &mut modules[0];
    let ty = Ty::Con {
        tycon: h2r_core_ir::TyConId {
            name: sn("Main", "Choice").into(),
            occ: "Choice".into(),
            unique: "choice".into(),
        },
        args: vec![],
    };
    m.types.push(ty.clone());
    let int = m.types[0].clone();
    m.types.push(Ty::Fun {
        mult: Box::new(int.clone()),
        arg: Box::new(int.clone()),
        res: Box::new(Ty::Fun {
            mult: Box::new(int.clone()),
            arg: Box::new(int),
            res: Box::new(ty),
        }),
    });
    for (name, tag, signature, arity) in [("Empty", 1, 3, 0), ("Pair", 2, 4, 2)] {
        m.constructors.push(serde_json::from_value(json!({"name":sn("Main",name),"worker":sn("Main",name),"family":sn("Main","Choice"),"familySize":2,"tag":tag,"signature":signature,"repArity":arity,"strict":vec![false;arity],"vanilla":true})).unwrap());
    }
    modules
}

#[test]
fn data_constructors_and_cases_close_source_accounting_and_renumber() {
    use crate::nir::{FnId, lower::lower_leaf_in_world, verify::verify_leaf_in_world};
    for body in [
        data_case(data_construct("Pair", vec![lvar("x"), lvar("y")]), false),
        data_case(data_construct("Empty", vec![]), true),
        int_op(
            "+#",
            data_case(data_construct("Pair", vec![lvar("x"), lvar("y")]), true),
            lvar("x"),
        ),
    ] {
        let modules = data_world(body);
        let owner = modules[0].top[0].pairs[0].binder;
        let leaf = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
        let accounting = verify_leaf_in_world(&modules, 0, owner, FnId(0), &leaf).unwrap();
        assert_eq!(
            accounting.source_nodes,
            modules[0].preorder(modules[0].top[0].pairs[0].rhs).count()
        );
        let rust = generated(&crate::emit::emit_entry(&modules, &sn("Main", "main")).unwrap());
        assert!(rust.contains("HData::ready"));
        assert!(rust.contains("let constructor = node.constructor; match constructor"));
        check_scalar_renumbering(modules);
    }
}

#[test]
fn data_layout_evidence_is_mandatory_and_complete() {
    use crate::nir::{FnId, lower::lower_leaf_in_world};
    for mutation in 0..9 {
        let mut modules = data_world(data_case(
            data_construct("Pair", vec![lvar("x"), lvar("y")]),
            false,
        ));
        let m = &mut modules[0];
        match mutation {
            0 => m.constructors.clear(),
            1 => {
                m.constructors.pop();
            }
            2 => m.constructors[1].signature = u32::MAX,
            3 => m.constructors[1].vanilla = false,
            4 => m.constructors[1].rep_arity = 1,
            5 => m.constructors[1].strict.clear(),
            6 => m.constructors[1].tag = 1,
            7 => m.constructors[1].family_size = 3,
            _ => m.constructors.push(m.constructors[1].clone()),
        }
        let owner = m.top[0].pairs[0].binder;
        assert!(
            lower_leaf_in_world(&modules, 0, owner, FnId(0)).is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn data_lets_preserve_shared_aliases_and_delayed_construction() {
    use crate::nir::{FnId, Operation, Rule, lower::lower_leaf_in_world};
    let mut body = lazy_let(
        "z",
        data_construct("Pair", vec![lvar("x"), lvar("y")]),
        data_case(lvar("z"), false),
    );
    body["bind"]["pairs"][0]["binder"]["ty"] = json!(3);
    let modules = data_world(body);
    let owner = modules[0].top[0].pairs[0].binder;
    let leaf = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
    assert!(
        leaf.function
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .any(|i| matches!(i.operation, Operation::DelayBlock { .. }))
    );
    assert_eq!(
        leaf.function
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .filter(|i| i.origin.rule == Rule::LazyBinding)
            .count(),
        1
    );
    check_scalar_renumbering(modules);
}

#[test]
fn data_nullary_workers_in_call_arguments_are_not_linked_as_functions() {
    use crate::nir::{FnId, Operation, lower::lower_leaf_in_world};
    let body = app(
        gvar(&sn("Helper", "consume"), "consume"),
        data_construct("Empty", vec![]),
    );
    let mut modules = data_world(body);
    let data_ty = modules[0].types[3].clone();
    let int_ty = modules[0].types[0].clone();
    let target = modules[1].top[0].pairs[0].binder;
    modules[1].binders[target as usize].name = sn("Helper", "consume");
    modules[1].binders[target as usize].arity = Some(1);
    let index = modules[1].types.len() as u32;
    modules[1].types.push(h2r_core_ir::Ty::Fun {
        mult: Box::new(int_ty.clone()),
        arg: Box::new(data_ty),
        res: Box::new(int_ty),
    });
    modules[1].binders[target as usize].ty = index;
    let leaf =
        lower_leaf_in_world(&modules, 0, modules[0].top[0].pairs[0].binder, FnId(0)).unwrap();
    assert!(matches!(
        leaf.function.blocks[0].instructions[0].operation,
        Operation::Construct { .. }
    ));
}

#[test]
fn data_constructor_names_never_override_lexical_bindings() {
    use h2r_core_ir::Expr;
    // Rebuild with a lambda shadow using the worker's exact stable name/unique.
    let mut shadow = binder(&sn("Main", "Pair"), "Pair", "Pair");
    shadow["ty"] = json!(4);
    let body = json!({"node":"Lam","binder":shadow,"body":data_case(data_construct("Pair",vec![lvar("x"),lvar("y")]),false)});
    let modules = data_world(body);
    let m = &modules[0];
    let source = m
        .exprs
        .iter()
        .position(|e| matches!(e,Expr::Var{name,..} if *name==sn("Main","Pair")))
        .unwrap() as u32;
    assert!(
        m.resolve(source).is_some(),
        "fixture must actually resolve lexically"
    );
    assert!(
        crate::nir::data::resolve(
            &crate::nir::World::of(&modules, 0).unwrap(),
            0,
            source,
            &m.types[3]
        )
        .unwrap()
        .is_none()
    );
}

#[test]
fn data_source_verifier_rejects_corrupted_layout_fields_and_control_flow() {
    use crate::nir::{
        FnId, Operation, Rule, lower::lower_leaf_in_world, verify::verify_leaf_in_world,
    };
    let modules = data_world(data_case(
        data_construct("Pair", vec![lvar("x"), lvar("y")]),
        false,
    ));
    let owner = modules[0].top[0].pairs[0].binder;
    let good = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
    for mutation in 0..12 {
        let mut bad = good.clone();
        if mutation < 6 {
            let instruction = bad
                .function
                .blocks
                .iter_mut()
                .flat_map(|b| &mut b.instructions)
                .find(|i| matches!(i.operation, Operation::Construct { .. }))
                .unwrap();
            let Operation::Construct {
                constructor,
                arguments,
            } = &mut instruction.operation
            else {
                unreachable!()
            };
            match mutation {
                0 => arguments.swap(0, 1),
                1 => constructor.tag = 1,
                2 => constructor.name = sn("Main", "Empty"),
                3 => constructor.strict[0] = true,
                4 => constructor.fields.swap(0, 1), // same types: corrupt result instead
                _ => instruction.origin.rule = Rule::Literal,
            }
            if mutation == 4 {
                constructor.result = modules[0].types[0].clone();
            }
        } else {
            let entry = bad.function.entry;
            let instruction = bad
                .function
                .blocks
                .iter_mut()
                .flat_map(|b| &mut b.instructions)
                .find(|i| matches!(i.operation, Operation::MatchData { .. }))
                .unwrap();
            let Operation::MatchData {
                scrutinee,
                arguments,
                arms,
            } = &mut instruction.operation
            else {
                unreachable!()
            };
            match mutation {
                6 => arguments.swap(0, 1),
                7 => arms.swap(0, 1),
                8 => {
                    arms.pop();
                }
                9 => arms[0].target = entry,
                10 => *scrutinee = arguments[0],
                _ => arms[1].constructor.as_mut().unwrap().strict[0] = true,
            }
        }
        assert!(
            verify_leaf_in_world(&modules, 0, owner, FnId(0), &bad).is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn data_patterns_require_correct_fields_unique_tags_and_exhaustiveness() {
    use crate::nir::{FnId, lower::lower_leaf_in_world};
    for mutation in 0..6 {
        let mut body = data_case(data_construct("Empty", vec![]), false);
        match mutation {
            0 => body["alts"] = json!([]),
            1 => body["alts"][1]["con"]["tag"] = json!(1),
            2 => body["alts"][1]["binders"][0]["ty"] = json!(2),
            3 => body["alts"][1]["binders"] = json!([]),
            4 => body["alts"][1]["con"]["name"] = json!(sn("Other", "Pair")),
            _ => body["alts"][1]["rhs"] = json!({"node":"Coercion"}),
        }
        let modules = data_world(body);
        assert!(
            lower_leaf_in_world(&modules, 0, modules[0].top[0].pairs[0].binder, FnId(0)).is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn a_lifted_strict_case_forces_and_a_partial_match_lowers() {
    use crate::nir::{
        FnId, Operation, Rule, lower::lower_leaf_in_world, verify::verify_leaf_in_world,
    };
    let mut forced = strict_case(lvar("p"), "forced", app(lvar("forced"), lvar("y")));
    forced["binder"]["ty"] = json!(2);
    let mut partial = data_case(data_construct("Pair", vec![lvar("x"), lvar("y")]), false);
    partial["alts"] = json!([partial["alts"][1].clone()]);
    for (modules, rule) in [
        (closure_world_applying(forced), Rule::StrictPosition),
        (data_world(partial), Rule::MatchData),
    ] {
        let owner = modules[0].top[0].pairs[0].binder;
        let leaf = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
        let accounting = verify_leaf_in_world(&modules, 0, owner, FnId(0), &leaf).unwrap();
        assert_eq!(
            accounting.source_nodes,
            modules[0].preorder(modules[0].top[0].pairs[0].rhs).count()
        );
        let instructions = || leaf.function.blocks.iter().flat_map(|b| &b.instructions);
        assert!(instructions().any(|i| i.origin.rule == rule));
        crate::emit::emit_entry(&modules, &sn("Main", "main")).unwrap();
        if rule == Rule::StrictPosition {
            let mut bad = leaf.clone();
            let instruction = bad
                .function
                .blocks
                .iter_mut()
                .flat_map(|b| &mut b.instructions)
                .find(|i| matches!(i.operation, Operation::Force(_)))
                .unwrap();
            let Operation::Force(value) = instruction.operation else {
                unreachable!()
            };
            instruction.operation = Operation::Move(value);
            assert!(verify_leaf_in_world(&modules, 0, owner, FnId(0), &bad).is_err());
        }
    }
}

fn check_scalar_renumbering(modules: Vec<Module>) {
    use crate::nir::{
        Exit, FnId, Operation, lower::lower_leaf_in_world, verify::verify_leaf_in_world,
    };
    let owner = modules[0].top[0].pairs[0].binder;
    let mut leaf = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
    leaf.function.entry.0 += 100;
    for (_, value) in &mut leaf.parameters {
        value.0 += 1000;
    }
    for block in &mut leaf.function.blocks {
        block.id.0 += 100;
        for param in &mut block.params {
            param.id.0 += 1000;
        }
        for instruction in &mut block.instructions {
            instruction.result.id.0 += 1000;
            match &mut instruction.operation {
                Operation::Construct { arguments, .. } => {
                    for value in arguments {
                        value.0 += 1000;
                    }
                }
                Operation::MatchData {
                    scrutinee,
                    arguments,
                    arms,
                } => {
                    scrutinee.0 += 1000;
                    for value in arguments {
                        value.0 += 1000;
                    }
                    for arm in arms {
                        arm.target.0 += 100;
                    }
                }
                Operation::EvaluateBlock { target, arguments }
                | Operation::DelayBlock { target, arguments } => {
                    target.0 += 100;
                    for value in arguments {
                        value.0 += 1000;
                    }
                }
                Operation::IntBinary { arguments, .. } | Operation::CallTop { arguments, .. } => {
                    for value in arguments {
                        value.0 += 1000;
                    }
                }
                Operation::Move(value)
                | Operation::Force(value)
                | Operation::BoxInt(value)
                | Operation::UnboxInt(value) => value.0 += 1000,
                _ => {}
            }
        }
        match &mut block.terminator.exit {
            Exit::Return(value) => value.0 += 1000,
            Exit::IntSwitch {
                scrutinee,
                arms,
                default,
                args,
            } => {
                scrutinee.0 += 1000;
                default.0 += 100;
                for (_, target) in arms {
                    target.0 += 100;
                }
                for arg in args {
                    arg.0 += 1000;
                }
            }
            Exit::Jump { .. } => panic!("fixture has no jumps"),
            Exit::Diverge { .. } => panic!("fixture has no dead ends"),
        }
    }
    leaf.function.blocks.reverse();
    verify_leaf_in_world(&modules, 0, owner, FnId(0), &leaf).unwrap();
}

#[test]
fn scalar_switches_refuse_incomplete_or_unsafe_source_patterns() {
    use crate::nir::{FnId, lower::lower_leaf_in_world};
    for mutation in 0..6 {
        let mut source = int_case(lvar("x"), "s", lvar("s"), vec![(0, lvar("y"))]);
        let alts = source["alts"].as_array_mut().unwrap();
        match mutation {
            0 => {
                alts.remove(0);
            }
            1 => alts.push(alts[1].clone()),
            2 => alts[1]["con"]["lit"]["value"] = json!("9223372036854775808"),
            3 => alts[1]["con"]["lit"]["numType"] = json!("Word64"),
            4 => alts[1]["con"]["lit"]["kind"] = json!("string"),
            _ => {
                alts[1]["con"] = json!({"kind": "DataAlt", "name": "$x$M$C", "occ": "C", "tag": 1})
            }
        }
        let modules = scalar_expression_world(source);
        let owner = modules[0].top[0].pairs[0].binder;
        assert!(
            lower_leaf_in_world(&modules, 0, owner, FnId(0)).is_err(),
            "mutation {mutation}"
        );
    }
    // Even a branch which these particular arguments would not select must
    // have a lowerable, fully validated dependency closure.
    let modules = scalar_expression_world(int_case(
        lvar("x"),
        "s",
        lvar("s"),
        vec![(0, json!({"node": "Coercion"}))],
    ));
    assert!(crate::emit::emit_entry(&modules, &sn("Main", "main")).is_err());
}

#[test]
fn all_int_comparisons_preserve_operator_and_int_result() {
    use crate::nir::{
        FnId, IntBinary, Operation, lower::lower_leaf_in_world, verify::verify_leaf_in_world,
    };
    for (symbol, expected, rust_op) in [
        ("==#", IntBinary::Equal, " == "),
        ("/=#", IntBinary::NotEqual, " != "),
        ("<#", IntBinary::Less, " < "),
        ("<=#", IntBinary::LessEqual, " <= "),
        (">#", IntBinary::Greater, " > "),
        (">=#", IntBinary::GreaterEqual, " >= "),
    ] {
        let modules = scalar_expression_world(int_op(symbol, lvar("x"), lvar("y")));
        let owner = modules[0].top[0].pairs[0].binder;
        let mut leaf = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
        let Operation::IntBinary { op, arguments } =
            &mut leaf.function.blocks[0].instructions[0].operation
        else {
            panic!()
        };
        assert_eq!(*op, expected);
        arguments.swap(0, 1);
        assert!(verify_leaf_in_world(&modules, 0, owner, FnId(0), &leaf).is_err());
        let rust = generated(&crate::emit::emit_entry(&modules, &sn("Main", "main")).unwrap());
        assert!(rust.contains("i64::from(") && rust.contains(rust_op));
    }
}

fn primitive_emission_world(symbol: &str) -> Vec<Module> {
    let mut modules = scalar_emission_world();
    let name = format!("$ghc-prim$GHC.Prim${symbol}");
    for expr in &mut modules[0].exprs {
        if let h2r_core_ir::Expr::Var { name: target, .. } = expr
            && *target == sn("Lib", "target")
        {
            *target = name.clone();
        }
    }
    modules[0].ids.insert(
        name.clone(),
        serde_json::from_value(json!({
            "name": name, "occ": symbol, "arity": 2, "details": "[PrimOp]",
            "isJoinPoint": false, "dataCon": null,
            "dmdSig": {"args": [], "diverges": false, "pretty": ""}
        }))
        .unwrap(),
    );
    modules
}

#[test]
fn int_arithmetic_is_source_verified_and_emits_wrapping_operations() {
    use crate::nir::{
        FnId, IntBinary, Operation, lower::lower_leaf_in_world, verify::verify_leaf_in_world,
    };
    for (symbol, expected, method) in [
        ("+#", IntBinary::Add, "wrapping_add"),
        ("-#", IntBinary::Subtract, "wrapping_sub"),
        ("*#", IntBinary::Multiply, "wrapping_mul"),
        ("quotInt#", IntBinary::Quot, "wrapping_div"),
        ("remInt#", IntBinary::Rem, "wrapping_rem"),
        ("andI#", IntBinary::And, " & "),
        ("orI#", IntBinary::Or, " | "),
    ] {
        let modules = primitive_emission_world(symbol);
        let owner = modules[0].top[0].pairs[0].binder;
        let leaf = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
        assert!(
            matches!(leaf.function.blocks[0].instructions.last().unwrap().operation,
            Operation::IntBinary { op, .. } if op == expected)
        );
        let counts = verify_leaf_in_world(&modules, 0, owner, FnId(0), &leaf).unwrap();
        assert_eq!(counts.value_application_nodes, 2);
        let emitted = generated(&crate::emit::emit_entry(&modules, &sn("Main", "main")).unwrap());
        assert!(emitted.contains(method));
        assert_eq!(emitted.matches("fn f_").count(), 1);
        for mutation in 0..7 {
            let mut bad = leaf.clone();
            let instruction = bad.function.blocks[0].instructions.last_mut().unwrap();
            let Operation::IntBinary { op, arguments } = &mut instruction.operation else {
                panic!()
            };
            match mutation {
                0 => {
                    *op = if expected == IntBinary::Add {
                        IntBinary::Subtract
                    } else {
                        IntBinary::Add
                    }
                }
                1 => arguments.swap(0, 1),
                2 => {
                    arguments.pop();
                }
                3 => arguments[0] = crate::nir::ValueId(999),
                4 => instruction.origin.rule = crate::nir::Rule::CallTop,
                5 => instruction.origin.source = crate::nir::Source::Binder(owner),
                _ => instruction.result.ty = crate::nir::shared(&modules[0].types[1]),
            }
            assert!(
                verify_leaf_in_world(&modules, 0, owner, FnId(0), &bad).is_err(),
                "{symbol} mutation {mutation}"
            );
        }
    }
}

#[test]
fn a_primop_with_two_results_fills_the_unboxed_tuple_it_returns() {
    use crate::nir::{
        FnId, Machine, Operation, lower::lower_leaf_in_world, verify::verify_leaf_in_world,
    };
    let mut modules = unboxed_tuple_world();
    let name = "$ghc-prim$GHC.Prim$quotRemInt#";
    for expr in &mut modules[0].exprs {
        if let h2r_core_ir::Expr::Var { name: target, .. } = expr
            && *target == "$u$M$Pair#"
        {
            *target = name.into();
        }
    }
    modules[0].ids.insert(
        name.into(),
        serde_json::from_value(json!({
            "name": name, "occ": "quotRemInt#", "arity": 2, "details": "[PrimOp]",
            "isJoinPoint": false, "dataCon": null,
            "dmdSig": {"args": [], "diverges": false, "pretty": ""}
        }))
        .unwrap(),
    );
    let owner = modules[0].top[0].pairs[0].binder;
    let leaf = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
    verify_leaf_in_world(&modules, 0, owner, FnId(0), &leaf).unwrap();
    let emitted = generated(&crate::emit::emit_entry(&modules, &sn("Main", "main")).unwrap());
    assert!(emitted.contains(".wrapping_div(") && emitted.contains(".wrapping_rem("));
    for mutation in 0..3 {
        let mut bad = leaf.clone();
        let instruction = bad
            .function
            .blocks
            .iter_mut()
            .flat_map(|b| &mut b.instructions)
            .find(|i| matches!(i.operation, Operation::Machine { .. }))
            .unwrap();
        let Operation::Machine { op, arguments, .. } = &mut instruction.operation else {
            unreachable!()
        };
        match mutation {
            0 => *op = Machine::NotInt,
            1 => arguments.swap(0, 1),
            _ => instruction.origin.rule = crate::nir::Rule::IntBinary,
        }
        assert!(
            verify_leaf_in_world(&modules, 0, owner, FnId(0), &bad).is_err(),
            "mutation {mutation}"
        );
    }
    modules[0].constructors[0].rep_arity = 3;
    assert!(lower_leaf_in_world(&modules, 0, owner, FnId(0)).is_err());
}

#[test]
fn int_arithmetic_refuses_unknown_names_metadata_types_and_arity() {
    use crate::nir::{FnId, lower::lower_leaf_in_world};
    for symbol in ["fetchAddIntArray#", "casIntArray#", "notARealPrimOp#"] {
        assert!(
            crate::emit::emit_entry(&primitive_emission_world(symbol), &sn("Main", "main"))
                .is_err()
        );
    }
    for mutation in 0..5 {
        let mut modules = primitive_emission_world("+#");
        let name = "$ghc-prim$GHC.Prim$+#";
        match mutation {
            0 => modules[0].ids.get_mut(name).unwrap().arity = 1,
            1 => modules[0].ids.get_mut(name).unwrap().details = "[VanillaId]".into(),
            2 => {
                modules[0].ids.remove(name);
            }
            3 => modules[0].ids.get_mut(name).unwrap().name = "$other$GHC.Prim$+#".into(),
            _ => {
                let h2r_core_ir::Ty::Con { tycon, .. } = &mut modules[0].types[0] else {
                    panic!()
                };
                tycon.name = "$ghc-prim$GHC.Prim$Word#".into();
            }
        }
        let owner = modules[0].top[0].pairs[0].binder;
        assert!(
            lower_leaf_in_world(&modules, 0, owner, FnId(0)).is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn primitive_spelling_does_not_override_a_lexical_call_target() {
    use crate::nir::{FnId, Operation, lower::lower_leaf_in_world};
    let name = "$ghc-prim$GHC.Prim$+#";
    let mut head = lvar("target");
    head["name"] = json!(name);
    let mut modules = nir_call_world(false);
    let types = modules[0].types.clone();
    let ids = primitive_emission_world("+#")[0].ids.clone();
    modules[0] = module(
        "Main",
        vec![
            (
                binder(&sn("Main", "main"), "main", "main"),
                lam("x", lam("y", app(app(head, lvar("x")), lvar("y")))),
            ),
            (binder(name, "+#", "target"), lam("a", lam("b", lvar("a")))),
        ],
        json!({}),
    );
    modules[0].types = types;
    modules[0].ids = ids;
    let top_binders: Vec<_> = modules[0]
        .top
        .iter()
        .flat_map(|g| &g.pairs)
        .map(|p| p.binder)
        .collect();
    for binder in top_binders {
        modules[0].binders[binder as usize].ty = 1;
        modules[0].binders[binder as usize].arity = Some(2);
    }
    let owner = modules[0].top[0].pairs[0].binder;
    let leaf = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
    assert!(matches!(
        leaf.function.blocks[0].instructions[0].operation,
        Operation::CallTop { .. }
    ));
}

fn nir_polymorphic_module() -> Module {
    use h2r_core_ir::{Ty, TyVarId};
    let type_lambda = |unique: &str, body: Value| {
        let mut b = binder("$_in$a", "a", unique);
        b["kind"] = json!("tyvar");
        json!({"node": "Lam", "binder": b, "body": body})
    };
    let mut m = module(
        "Main",
        vec![(
            binder(&sn("Main", "first"), "first", "f"),
            type_lambda(
                "localA",
                type_lambda("localB", lam("x", lam("y", lvar("x")))),
            ),
        )],
        json!({}),
    );
    // Same spelling, different uniques in the signature and body: correspondence
    // must come from paired forall/type-lambda positions, not names.
    let tv = |unique: &str| TyVarId {
        name: "$_in$a".into(),
        occ: "a".into(),
        unique: unique.into(),
    };
    let a = tv("sigA");
    let b = tv("sigB");
    let fun = |arg: Ty, res: Ty| Ty::Fun {
        mult: Box::new(m.types[0].clone()),
        arg: Box::new(arg),
        res: Box::new(res),
    };
    let signature = Ty::ForAll {
        binder: a.clone(),
        body: Box::new(Ty::ForAll {
            binder: b.clone(),
            body: Box::new(fun(Ty::Var(a.clone()), fun(Ty::Var(b), Ty::Var(a)))),
        }),
    };
    m.types
        .extend([signature, Ty::Var(tv("localA")), Ty::Var(tv("localB"))]);
    for binder in &mut m.binders {
        binder.ty = match binder.unique.as_str() {
            "f" => 1,
            "x" => 2,
            "y" => 3,
            _ => 0,
        };
    }
    m
}

#[test]
fn nir_lowers_alpha_renamed_type_lambdas_without_runtime_arguments() {
    use crate::nir::{FnId, ValueId, lower::lower_leaf, pretty::format_leaf, verify::verify_leaf};
    let m = nir_polymorphic_module();
    let owner = m.top[0].pairs[0].binder;
    let leaf = lower_leaf(&m, 0, owner, FnId(0)).unwrap();
    assert_eq!(leaf.type_parameters.len(), 2);
    assert_eq!(leaf.function.type_params[0].unique, "sigA");
    assert_eq!(leaf.function.type_params[1].unique, "sigB");
    assert_eq!(leaf.function.blocks[0].params.len(), 2);
    assert_eq!(leaf.function.blocks[0].params[0].id, ValueId(0));
    assert!(leaf.function.blocks[0].instructions.is_empty());
    let accounting = verify_leaf(&m, 0, owner, FnId(0), &leaf).unwrap();
    assert_eq!(accounting.source_nodes, 5);
    assert_eq!(accounting.type_parameter_nodes, 2);
    assert_eq!(accounting.parameter_nodes, 2);
    assert!(format_leaf(&leaf).contains("type param a [sigA]"));
    assert!(format_leaf(&leaf).contains("erased type lambda"));
}

#[test]
fn nir_type_lambda_verifier_rejects_corrupt_provenance() {
    use crate::nir::{
        FnId,
        lower::lower_leaf,
        verify::{verify, verify_leaf},
    };
    let m = nir_polymorphic_module();
    let owner = m.top[0].pairs[0].binder;
    let original = lower_leaf(&m, 0, owner, FnId(0)).unwrap();
    for corruption in 0..5 {
        let mut leaf = original.clone();
        match corruption {
            0 => {
                leaf.type_parameters.pop();
            }
            1 => leaf.type_parameters.swap(0, 1),
            2 => leaf.type_parameters[0].1 = owner,
            3 => leaf.function.type_params.swap(0, 1),
            _ => leaf.function.type_params[0].unique = "forged".into(),
        }
        verify(&leaf.function).unwrap();
        assert!(
            verify_leaf(&m, 0, owner, FnId(0), &leaf).is_err(),
            "corruption {corruption}"
        );
    }
}

#[test]
fn nir_rejects_wrong_or_ambiguous_type_lambda_scope() {
    use crate::nir::{FnId, lower::lower_leaf};
    for corruption in 0..4 {
        let mut m = nir_polymorphic_module();
        let owner = m.top[0].pairs[0].binder;
        match corruption {
            0 => m.binders[owner as usize].ty = 0, // Type lambda without forall.
            1 => {
                // Free variable must not be mistaken for the bound type.
                let h2r_core_ir::Ty::Var(v) = &mut m.types[2] else {
                    unreachable!()
                };
                v.unique = "unbound".into();
            }
            2 => {
                // Returning/accepting the other quantified type is not alpha-renaming.
                let x = m.binders.iter_mut().find(|b| b.unique == "x").unwrap();
                x.ty = 3;
            }
            _ => {
                let b = m.binders.iter_mut().find(|b| b.unique == "localB").unwrap();
                b.unique = "localA".into();
            }
        }
        assert!(
            lower_leaf(&m, 0, owner, FnId(0)).is_err(),
            "corruption {corruption}"
        );
    }
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
    json!({"node": "Lit", "lit": int_lit(0)})
}

/// An `Int#` literal as the dump carries one: GHC's rendering *and* the exact
/// value with its `LitNumType`, which is what every decoder reads.
fn int_lit(value: i64) -> Value {
    json!({
        "kind": "number",
        "pretty": format!("{value}#"),
        "value": value.to_string(),
        "numType": "Int",
    })
}

/// The stable name of a top-level binding of `module`.
fn generated(source: &str) -> String {
    source.replacen(include_str!("../../h2r-rt/src/lib.rs"), "", 1)
}

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

//------------------------------------------------------------------------------
// Specialization: instances, dictionaries, and what corrupting either costs
//------------------------------------------------------------------------------

fn tylam(unique: &str, body: Value) -> Value {
    json!({"node": "Lam", "binder": {
        "kind": "tyvar", "name": format!("$_in${unique}"), "occ": unique,
        "unique": unique, "type": "*", "ty": 0
    }, "body": body})
}

fn type_arg(index: u32, pretty: &str) -> Value {
    json!({"node": "Type", "ty": index, "type": pretty})
}

/// One binder's signature, arity and `IdDetails`, by occurrence. Every
/// occurrence in these fixtures is distinct, so this is unambiguous.
fn set_binder(modules: &mut [Module], occ: &str, ty: u32, arity: u32, details: &str) {
    let mut found = 0;
    for module in modules.iter_mut() {
        for binder in &mut module.binders {
            if binder.occ == occ {
                binder.ty = ty;
                binder.arity = Some(arity);
                binder.details = Some(details.into());
                found += 1;
            }
        }
    }
    assert!(found > 0, "no binder named {occ} in the fixture");
}

fn specialization_types() -> Vec<h2r_core_ir::Ty> {
    use h2r_core_ir::{Ty, TyConId, TyVarId};
    let con = |name: &str, args| Ty::Con {
        tycon: TyConId {
            name: sn("Types", name).into(),
            occ: name.into(),
            unique: name.into(),
        },
        args,
    };
    let arrow = |arg: Ty, res: Ty| Ty::Fun {
        mult: Box::new(con("Many", vec![])),
        arg: Box::new(arg),
        res: Box::new(res),
    };
    let a = TyVarId {
        name: "$_in$a".into(),
        occ: "a".into(),
        unique: "a".into(),
    };
    let t = con("T", vec![]);
    let u = con("U", vec![]);
    let var = Ty::Var(a.clone());
    vec![
        t.clone(),                       // 0: T
        u.clone(),                       // 1: U
        arrow(t.clone(), t.clone()),     // 2: T -> T
        arrow(u.clone(), u.clone()),     // 3: U -> U
        var.clone(),                     // 4: a
        arrow(var.clone(), var.clone()), // 5: a -> a
        Ty::ForAll {
            binder: a.clone(),
            body: Box::new(arrow(var.clone(), var.clone())),
        }, // 6: forall a. a -> a
        con("C", vec![var.clone()]),     // 7: C a
        con("C", vec![t.clone()]),       // 8: C T
        con("C", vec![u.clone()]),       // 9: C U
        Ty::ForAll {
            binder: a.clone(),
            body: Box::new(arrow(
                con("C", vec![var.clone()]),
                arrow(var.clone(), var.clone()),
            )),
        }, // 10: forall a. C a -> a -> a
        Ty::ForAll {
            binder: a.clone(),
            body: Box::new(arrow(
                arrow(var.clone(), var.clone()),
                arrow(arrow(var.clone(), var.clone()), con("C", vec![var.clone()])),
            )),
        }, // 11: the class constructor's worker signature
        con("L", vec![var]),             // 12: L a
    ]
}

/// A nullary constructor, so the fixture's types are supported carriers.
fn nullary_constructor(name: &str, signature: u32) -> raw::ConstructorInfo {
    raw::ConstructorInfo {
        name: sn("Types", &format!("Mk{name}")),
        worker: sn("Types", &format!("Mk{name}")),
        family: sn("Types", name),
        family_size: 1,
        tag: 1,
        signature,
        rep_arity: 0,
        strict: Vec::new(),
        vanilla: true,
        newtype: Some(false),
        unlifted: Some(false),
        unboxed: Some(false),
        existential: Some(false),
        equalities: Some(false),
        class_dictionary: Some(false),
    }
}

fn class_constructor() -> raw::ConstructorInfo {
    raw::ConstructorInfo {
        name: sn("Types", "C:C"),
        worker: sn("Types", "C:C"),
        family: sn("Types", "C"),
        family_size: 1,
        tag: 1,
        signature: 11,
        rep_arity: 2,
        strict: vec![false, false],
        // A class dictionary is not `isVanillaDataCon` once it has a
        // superclass, so the finer evidence is what the lowering reads.
        vanilla: false,
        newtype: Some(false),
        unlifted: Some(false),
        unboxed: Some(false),
        existential: Some(false),
        equalities: Some(false),
        class_dictionary: Some(true),
    }
}

/// A two-module world: one polymorphic identity, one class with two
/// instances, one dictionary-taking function, and one growing recursion.
///
/// ```text
/// Lib.poly     = /\a \px. px                       forall a. a -> a
/// Lib.grow     = /\a \gx. grow @(L a) gx           forall a. a -> a
/// Lib.grow2    = /\a \hx. grow3 @(L a) hx          forall a. T -> T
/// Lib.grow3    = /\a \ix. grow2 @(L a) ix          forall a. T -> T
/// Lib.method   = /\a \mv. case mv of C:C f1 f2 -> f1   (a class-op selector)
/// Lib.dictT    = C:C @T tm1 tm2                    C T
/// Lib.dictU    = C:C @U um1 um2                    C U
/// Lib.tm1/tm2  = \t1/\t2. t1/t2                    T -> T
/// Lib.um1/um2  = \u1/\u2. u1/u2                    U -> U
/// Lib.viaDict  = /\a \dd \dx. method @a dd dx      forall a. C a -> a -> a
/// Main.useT    = \yt. poly @T yt                   T -> T
/// Main.useU    = \yu. poly @U yu                   U -> U
/// Main.useDict = \yd. viaDict @T dictT yd          T -> T
/// Main.useOpen = \od \oy. method @T od oy          C T -> T -> T
/// Main.useGrow = \yg. grow @T yg                   T -> T
/// Main.useGrow2 = \yh. grow2 @T yh                 T -> T
/// ```
fn nir_specialization_world() -> Vec<Module> {
    let selector = class_case(
        lvar("mv"),
        "mw",
        &sn("Types", "C:C"),
        vec!["f1", "f2"],
        lvar("f1"),
        5,
    );
    let lib = vec![
        (
            binder(&sn("Lib", "poly"), "poly", "poly"),
            tylam("a", lam("px", lvar("px"))),
        ),
        (
            binder(&sn("Lib", "grow"), "grow", "grow"),
            tylam(
                "a",
                lam(
                    "gx",
                    app(
                        app(gvar(&sn("Lib", "grow"), "grow"), type_arg(12, "L a")),
                        lvar("gx"),
                    ),
                ),
            ),
        ),
        (
            binder(&sn("Lib", "grow2"), "grow2", "grow2"),
            tylam(
                "a",
                lam(
                    "hx",
                    app(
                        app(gvar(&sn("Lib", "grow3"), "grow3"), type_arg(12, "L a")),
                        lvar("hx"),
                    ),
                ),
            ),
        ),
        (
            binder(&sn("Lib", "grow3"), "grow3", "grow3"),
            tylam(
                "a",
                lam(
                    "ix",
                    app(
                        app(gvar(&sn("Lib", "grow2"), "grow2"), type_arg(12, "L a")),
                        lvar("ix"),
                    ),
                ),
            ),
        ),
        (
            binder(&sn("Lib", "method"), "method", "method"),
            tylam("a", lam("mv", selector)),
        ),
        (
            binder(&sn("Lib", "dictT"), "dictT", "dictT"),
            app(
                app(
                    app(gvar(&sn("Types", "C:C"), "C:C"), type_arg(0, "T")),
                    gvar(&sn("Lib", "tm1"), "tm1"),
                ),
                gvar(&sn("Lib", "tm2"), "tm2"),
            ),
        ),
        (
            binder(&sn("Lib", "dictU"), "dictU", "dictU"),
            app(
                app(
                    app(gvar(&sn("Types", "C:C"), "C:C"), type_arg(1, "U")),
                    gvar(&sn("Lib", "um1"), "um1"),
                ),
                gvar(&sn("Lib", "um2"), "um2"),
            ),
        ),
        (
            binder(&sn("Lib", "tm1"), "tm1", "tm1"),
            lam("t1", lvar("t1")),
        ),
        (
            binder(&sn("Lib", "tm2"), "tm2", "tm2"),
            lam("t2", lvar("t2")),
        ),
        (
            binder(&sn("Lib", "caseDict"), "caseDict", "caseDict"),
            tylam(
                "a",
                lam(
                    "cd",
                    lam(
                        "cx",
                        class_case(
                            lvar("cd"),
                            "kw",
                            &sn("Types", "C:C"),
                            vec!["k1", "k2"],
                            app(lvar("k2"), lvar("cx")),
                            4,
                        ),
                    ),
                ),
            ),
        ),
        (
            binder(&sn("Lib", "um1"), "um1", "um1"),
            lam("u1", lvar("u1")),
        ),
        (
            binder(&sn("Lib", "um2"), "um2", "um2"),
            lam("u2", lvar("u2")),
        ),
        (
            binder(&sn("Lib", "viaDict"), "viaDict", "viaDict"),
            tylam(
                "a",
                lam(
                    "dd",
                    lam(
                        "dx",
                        app(
                            app(
                                app(gvar(&sn("Lib", "method"), "method"), type_arg(4, "a")),
                                lvar("dd"),
                            ),
                            lvar("dx"),
                        ),
                    ),
                ),
            ),
        ),
    ];
    let call_poly = |index: u32, pretty: &str, arg: &str| {
        app(
            app(gvar(&sn("Lib", "poly"), "poly"), type_arg(index, pretty)),
            lvar(arg),
        )
    };
    let main = vec![
        (
            binder(&sn("Main", "useT"), "useT", "useT"),
            lam("yt", call_poly(0, "T", "yt")),
        ),
        (
            binder(&sn("Main", "useU"), "useU", "useU"),
            lam("yu", call_poly(1, "U", "yu")),
        ),
        (
            binder(&sn("Main", "useDict"), "useDict", "useDict"),
            lam(
                "yd",
                app(
                    app(
                        app(gvar(&sn("Lib", "viaDict"), "viaDict"), type_arg(0, "T")),
                        gvar(&sn("Lib", "dictT"), "dictT"),
                    ),
                    lvar("yd"),
                ),
            ),
        ),
        (
            binder(&sn("Main", "useOpen"), "useOpen", "useOpen"),
            lam(
                "od",
                lam(
                    "oy",
                    app(
                        app(
                            app(gvar(&sn("Lib", "method"), "method"), type_arg(0, "T")),
                            lvar("od"),
                        ),
                        lvar("oy"),
                    ),
                ),
            ),
        ),
        (
            binder(&sn("Main", "useCase"), "useCase", "useCase"),
            lam(
                "yc",
                app(
                    app(
                        app(gvar(&sn("Lib", "caseDict"), "caseDict"), type_arg(0, "T")),
                        gvar(&sn("Lib", "dictT"), "dictT"),
                    ),
                    lvar("yc"),
                ),
            ),
        ),
        (
            binder(&sn("Main", "useGrow"), "useGrow", "useGrow"),
            lam(
                "yg",
                app(
                    app(gvar(&sn("Lib", "grow"), "grow"), type_arg(0, "T")),
                    lvar("yg"),
                ),
            ),
        ),
        (
            binder(&sn("Main", "useGrow2"), "useGrow2", "useGrow2"),
            lam(
                "yh",
                app(
                    app(gvar(&sn("Lib", "grow2"), "grow2"), type_arg(0, "T")),
                    lvar("yh"),
                ),
            ),
        ),
    ];
    let mut modules = vec![
        module("Main", main, json!({})),
        module("Lib", lib, json!({})),
    ];
    let types = specialization_types();
    for m in &mut modules {
        m.types = types.clone();
        m.constructors = vec![
            class_constructor(),
            nullary_constructor("T", 0),
            nullary_constructor("U", 1),
        ];
    }
    for (occ, ty, arity) in [
        ("poly", 6, 1),
        ("grow", 14, 1),
        ("grow2", 14, 1),
        ("grow3", 14, 1),
        ("useGrow2", 2, 1),
        ("hx", 0, 0),
        ("ix", 0, 0),
        ("yh", 0, 0),
        ("method", 10, 1),
        ("viaDict", 10, 2),
        ("dictT", 8, 0),
        ("dictU", 9, 0),
        ("tm1", 2, 1),
        ("tm2", 2, 1),
        ("um1", 3, 1),
        ("um2", 3, 1),
        ("useT", 2, 1),
        ("useU", 3, 1),
        ("useDict", 2, 1),
        ("useGrow", 2, 1),
        ("useCase", 2, 1),
        ("caseDict", 10, 2),
        ("cd", 7, 0),
        ("cx", 4, 0),
        ("kw", 7, 0),
        ("k1", 5, 0),
        ("k2", 5, 0),
        ("yc", 0, 0),
        // Lambda binders: the signature decides the parameter type, but the
        // binder's own type must agree with it.
        ("px", 4, 0),
        ("gx", 0, 0),
        ("mv", 7, 0),
        ("mw", 7, 0),
        ("f1", 5, 0),
        ("f2", 5, 0),
        ("dd", 7, 0),
        ("dx", 4, 0),
        ("t1", 0, 0),
        ("t2", 0, 0),
        ("u1", 1, 0),
        ("u2", 1, 0),
        ("yt", 0, 0),
        ("yu", 1, 0),
        ("yd", 0, 0),
        ("yg", 0, 0),
        ("od", 8, 0),
        ("oy", 0, 0),
    ] {
        set_binder(&mut modules, occ, ty, arity, "");
    }
    set_binder(&mut modules, "method", 10, 1, "[ClassOp]");
    set_binder(&mut modules, "dictT", 8, 0, "[DFunId]");
    set_binder(&mut modules, "dictU", 9, 0, "[DFunId]");
    // `useOpen` takes the dictionary at runtime: C T -> T -> T.
    let open = h2r_core_ir::Ty::Fun {
        mult: Box::new(modules[0].types[0].clone()),
        arg: Box::new(modules[0].types[8].clone()),
        res: Box::new(modules[0].types[2].clone()),
    };
    // 14: forall a. T -> T. Only the type argument grows along `grow`'s
    // recursion, so the fixture stays well typed while the instance key does
    // not converge.
    let growing = h2r_core_ir::Ty::ForAll {
        binder: h2r_core_ir::TyVarId {
            name: "$_in$a".into(),
            occ: "a".into(),
            unique: "a".into(),
        },
        body: Box::new(modules[0].types[2].clone()),
    };
    for m in &mut modules {
        m.types.push(open.clone());
        m.types.push(growing.clone());
    }
    set_binder(&mut modules, "useOpen", 13, 2, "");
    modules
}

fn nir_interleaved_world() -> Vec<Module> {
    nir_interleaving_world(false)
}

fn nir_interleaving_world(late: bool) -> Vec<Module> {
    use h2r_core_ir::{Ty, TyVarId};
    let later = if late {
        tylam("a", lam("ld", lam("lz", tylam("b", lam("lx", lvar("lx"))))))
    } else {
        tylam("a", lam("ld", tylam("b", lam("lx", lvar("lx")))))
    };
    let dictionary = app(
        app(gvar(&sn("Lib", "later"), "later"), type_arg(0, "T")),
        gvar(&sn("Lib", "dictT"), "dictT"),
    );
    let before_u = if late {
        app(dictionary, gvar(&sn("Types", "MkT"), "MkT"))
    } else {
        dictionary
    };
    let lib = vec![
        (binder(&sn("Lib", "later"), "later", "later"), later),
        (
            binder(&sn("Lib", "dictT"), "dictT", "dictT"),
            app(
                app(
                    app(gvar(&sn("Types", "C:C"), "C:C"), type_arg(0, "T")),
                    gvar(&sn("Lib", "tm1"), "tm1"),
                ),
                gvar(&sn("Lib", "tm2"), "tm2"),
            ),
        ),
        (
            binder(&sn("Lib", "tm1"), "tm1", "tm1"),
            lam("t1", lvar("t1")),
        ),
        (
            binder(&sn("Lib", "tm2"), "tm2", "tm2"),
            lam("t2", lvar("t2")),
        ),
    ];
    let main = vec![(
        binder(&sn("Main", "useLater"), "useLater", "useLater"),
        lam("yl", app(app(before_u, type_arg(1, "U")), lvar("yl"))),
    )];
    let mut modules = vec![
        module("Main", main, json!({})),
        module("Lib", lib, json!({})),
    ];
    let mut types = specialization_types();
    let variable = |name: &str| TyVarId {
        name: format!("$_in${name}").into(),
        occ: name.into(),
        unique: name.into(),
    };
    let arrow = |arg: Ty, res: Ty| Ty::Fun {
        mult: Box::new(types[0].clone()),
        arg: Box::new(arg),
        res: Box::new(res),
    };
    let b = Ty::Var(variable("b"));
    let polymorphic = Ty::ForAll {
        binder: variable("b"),
        body: Box::new(arrow(b.clone(), b.clone())),
    };
    let later = Ty::ForAll {
        binder: variable("a"),
        body: Box::new(arrow(
            types[7].clone(),
            if late {
                arrow(types[4].clone(), polymorphic)
            } else {
                polymorphic
            },
        )),
    };
    types.push(later);
    types.push(b);
    for m in &mut modules {
        m.types = types.clone();
        m.constructors = vec![
            class_constructor(),
            nullary_constructor("T", 0),
            nullary_constructor("U", 1),
        ];
    }
    for (occ, ty, arity) in [
        ("later", 13, if late { 3 } else { 2 }),
        ("dictT", 8, 0),
        ("tm1", 2, 1),
        ("tm2", 2, 1),
        ("useLater", 3, 1),
        ("ld", 7, 0),
        ("lx", 14, 0),
        ("t1", 0, 0),
        ("t2", 0, 0),
        ("yl", 1, 0),
    ] {
        set_binder(&mut modules, occ, ty, arity, "");
    }
    if late {
        set_binder(&mut modules, "lz", 4, 0, "");
    }
    set_binder(&mut modules, "dictT", 8, 0, "[DFunId]");
    modules
}

#[test]
fn specialization_absorbs_a_dictionary_between_type_arguments() {
    use crate::nir::specialize::{Instance, specialize};
    let modules = nir_interleaved_world();
    let root = Instance::whole(0, owner_of(&modules, 0, "useLater"));
    let program = specialize(&modules, &[root]).unwrap();
    assert!(program.refused.is_empty());
    let later = owner_of(&modules, 1, "later");
    let dict_t = owner_of(&modules, 1, "dictT");
    let (index, instance) = program
        .instances
        .iter()
        .enumerate()
        .find(|(_, instance)| instance.module == 1 && instance.binder == later)
        .expect("later is specialized");
    assert_eq!(
        instance.type_arguments,
        vec![modules[1].types[0].clone(), modules[1].types[1].clone()]
    );
    assert_eq!(instance.dictionaries.len(), 1);
    assert_eq!(instance.dictionaries[0].binder, dict_t);
    let leaf = program.leaf(index).expect("lowered");
    assert_eq!(leaf.type_instantiations.len(), 2);
    assert_eq!(leaf.dictionary_parameters.len(), 1);
    assert_eq!(leaf.function.blocks[0].params.len(), 1);
    assert_eq!(*leaf.function.blocks[0].params[0].ty, modules[1].types[1]);
}

#[test]
fn specialization_takes_a_type_argument_after_a_runtime_argument() {
    use crate::nir::specialize::{Instance, specialize};
    use crate::nir::{Operation, Rule};
    let modules = nir_interleaving_world(true);
    let root = Instance::whole(0, owner_of(&modules, 0, "useLater"));
    let program = specialize(&modules, &[root]).unwrap();
    assert!(program.refused.is_empty());
    let later = owner_of(&modules, 1, "later");
    let (index, instance) = program
        .instances
        .iter()
        .enumerate()
        .find(|(_, instance)| instance.module == 1 && instance.binder == later)
        .expect("later is specialized");
    assert_eq!(
        instance.type_arguments,
        vec![modules[1].types[0].clone(), modules[1].types[1].clone()]
    );
    assert_eq!(instance.dictionaries.len(), 1);
    let leaf = program.leaf(index).expect("lowered");
    let params: Vec<_> = leaf.function.blocks[0]
        .params
        .iter()
        .map(|p| &*p.ty)
        .collect();
    assert_eq!(params, [&modules[1].types[0], &modules[1].types[1]]);
    let caller = program.leaf(0).expect("lowered");
    let call = caller.function.blocks[0]
        .instructions
        .iter()
        .find(|i| matches!(i.operation, Operation::CallTop { .. }))
        .expect("one direct call");
    assert_eq!(call.origin.rule, Rule::CallTop);
    assert!(
        matches!(&call.operation, Operation::CallTop { type_arguments, arguments, .. }
        if type_arguments.len() == 2 && arguments.len() == 2)
    );
}

fn class_case(
    scrut: Value,
    case_binder: &str,
    constructor: &str,
    fields: Vec<&str>,
    rhs: Value,
    ty: u32,
) -> Value {
    json!({
        "node": "Case",
        "scrut": scrut,
        "binder": binder("$_sys$w", case_binder, case_binder),
        "ty": ty, "type": "R",
        "alts": [{
            "con": {"kind": "DataAlt", "name": constructor, "occ": "C:C", "tag": 1},
            "binders": fields.iter().map(|f| binder("$_sys$f", f, f)).collect::<Vec<_>>(),
            "rhs": rhs
        }]
    })
}

fn owner_of(modules: &[Module], module_index: usize, occ: &str) -> u32 {
    modules[module_index]
        .top
        .iter()
        .flat_map(|g| &g.pairs)
        .find(|p| modules[module_index].binder(p.binder).occ == occ)
        .expect("fixture binding")
        .binder
}

/// One source binding, lowered once per type its call sites use it at, with
/// the instances reached from two different roots interned only once.
#[test]
fn specialization_lowers_one_binding_at_each_type_it_is_used_at() {
    use crate::nir::specialize::{Instance, specialize};
    let modules = nir_specialization_world();
    let use_t = Instance::whole(0, owner_of(&modules, 0, "useT"));
    let use_u = Instance::whole(0, owner_of(&modules, 0, "useU"));
    let poly = owner_of(&modules, 1, "poly");
    let program = specialize(&modules, &[use_t.clone(), use_u]).unwrap();
    let instances: Vec<_> = program
        .instances
        .iter()
        .filter(|i| i.module == 1 && i.binder == poly)
        .collect();
    assert_eq!(instances.len(), 2, "one instance per type argument");
    assert!(!instances[0].same(instances[1]));
    assert_ne!(instances[0].key(), instances[1].key());
    assert_eq!(program.instances.len(), 4);
    assert!(program.refused.is_empty());
    // Each instance is monomorphic: the quantifier is gone and the parameter
    // carries the concrete type the call site supplied.
    for (index, instance) in program.instances.iter().enumerate() {
        let leaf = program.leaf(index).expect("lowered");
        assert!(leaf.function.type_params.is_empty());
        if instance.binder == poly && instance.module == 1 {
            assert_eq!(leaf.function.type_arguments.len(), 1);
            assert_eq!(
                *leaf.function.blocks[0].params[0].ty,
                instance.type_arguments[0]
            );
            assert_eq!(leaf.type_instantiations.len(), 1);
        }
    }
    // Reaching the same instance twice interns it once.
    let twice = specialize(&modules, &[use_t.clone(), use_t]).unwrap();
    assert_eq!(twice.instances.len(), 2);
}

/// An instance chain whose type arguments keep growing is refused with the
/// chain that produced it, rather than being allowed to run forever.
#[test]
fn specialization_refuses_an_unbounded_instance_chain() {
    use crate::nir::specialize::{Instance, OWNER_BUDGET, specialize, survey};
    let modules = nir_specialization_world();
    let root = Instance::whole(0, owner_of(&modules, 0, "useGrow2"));
    let error = specialize(&modules, std::slice::from_ref(&root)).unwrap_err();
    assert!(
        error.reason.contains("does not terminate"),
        "{}",
        error.reason
    );
    assert!(!error.path.is_empty(), "a refusal names how it was reached");
    assert_eq!(error.path[0].binder, root.binder);
    // Recording mode stops at the same bound instead of running away.
    let recorded = survey(&modules, &[root]);
    assert!(!recorded.refused.is_empty());
    assert!(recorded.instances.len() <= OWNER_BUDGET + 2);
}

#[test]
fn specialization_erases_a_direct_polymorphic_recursion() {
    use crate::nir::specialize::{Instance, specialize};
    use crate::nir::{DictionaryRef, Operation};
    let modules = nir_specialization_world();
    let root = Instance::whole(0, owner_of(&modules, 0, "useGrow"));
    let program = specialize(&modules, std::slice::from_ref(&root)).unwrap();
    let grow = owner_of(&modules, 1, "grow");
    let instances: Vec<_> = program
        .instances
        .iter()
        .enumerate()
        .filter(|(_, instance)| instance.module == 1 && instance.binder == grow)
        .collect();
    assert_eq!(instances.len(), 2);
    let (erased, instance) = instances[1];
    assert!(crate::nir::data::is_erased(&instance.type_arguments[0]));
    let leaf = program.leaf(erased).expect("lowered");
    let call = leaf
        .function
        .blocks
        .iter()
        .flat_map(|b| &b.instructions)
        .find_map(|i| match &i.operation {
            Operation::CallTop {
                module,
                binder,
                type_arguments,
                dictionaries,
                ..
            } => Some(DictionaryRef {
                module: *module,
                binder: *binder,
                type_arguments: type_arguments.clone(),
                dictionaries: dictionaries.clone(),
            }),
            _ => None,
        })
        .expect("the recursive call");
    assert_eq!(program.resolve(&call), Some(erased));
}

/// A budget refusal is recorded before its instance is interned, so a survey
/// considered its lowered count plus its refusals, not `instances.len()`.
#[test]
fn specialization_counts_a_budget_refusal_outside_the_interned_instances() {
    use crate::nir::specialize::{Instance, survey};
    let modules = nir_specialization_world();
    let root = Instance::whole(0, owner_of(&modules, 0, "useGrow2"));
    let recorded = survey(&modules, &[root]);
    let budget = recorded
        .refused
        .iter()
        .filter(|error| error.reason.contains("budget"))
        .count();
    assert!(budget > 0, "the growing chain is stopped by a budget");
    assert_eq!(
        recorded.lowered_count() + recorded.refused.len(),
        recorded.instances.len() + budget,
    );
}

/// A class method whose dictionary is proven unique becomes a direct call to
/// that instance's method, and the dictionary itself is never built.
#[test]
fn specialization_resolves_a_class_method_to_its_instance() {
    use crate::nir::specialize::{Instance, specialize};
    use crate::nir::{Operation, Rule};
    let modules = nir_specialization_world();
    let root = Instance::whole(0, owner_of(&modules, 0, "useDict"));
    let program = specialize(&modules, &[root]).unwrap();
    let dict_t = owner_of(&modules, 1, "dictT");
    assert!(
        !program
            .instances
            .iter()
            .any(|i| i.module == 1 && i.binder == dict_t),
        "a resolved dictionary is never built"
    );
    let via = owner_of(&modules, 1, "viaDict");
    let index = program
        .instances
        .iter()
        .position(|i| i.module == 1 && i.binder == via)
        .expect("the dictionary-taking function is specialized");
    let instance = &program.instances[index];
    assert_eq!(instance.dictionaries.len(), 1);
    assert_eq!(instance.dictionaries[0].binder, dict_t);
    let leaf = program.leaf(index).expect("lowered");
    // One runtime parameter: the dictionary lambda is gone.
    assert_eq!(leaf.function.blocks[0].params.len(), 1);
    assert_eq!(leaf.dictionary_parameters.len(), 1);
    let tm1 = owner_of(&modules, 1, "tm1");
    let call = leaf.function.blocks[0]
        .instructions
        .iter()
        .find(|i| matches!(i.operation, Operation::CallTop { .. }))
        .expect("the method call");
    assert_eq!(call.origin.rule, Rule::ResolveMethod);
    assert!(
        matches!(&call.operation, Operation::CallTop { binder, dictionaries, .. }
            if *binder == tm1 && dictionaries.is_empty())
    );
}

#[test]
fn specialization_selects_the_fields_of_a_known_dictionary_case() {
    use crate::nir::specialize::{Instance, specialize};
    use crate::nir::{Operation, Rule};
    let modules = nir_specialization_world();
    let root = Instance::whole(0, owner_of(&modules, 0, "useCase"));
    let program = specialize(&modules, &[root]).unwrap();
    assert!(program.refused.is_empty());
    let case_dict = owner_of(&modules, 1, "caseDict");
    let index = program
        .instances
        .iter()
        .position(|i| i.module == 1 && i.binder == case_dict)
        .expect("the dictionary-matching function is specialized");
    let leaf = program.leaf(index).expect("lowered");
    let instructions: Vec<_> = leaf
        .function
        .blocks
        .iter()
        .flat_map(|b| &b.instructions)
        .collect();
    assert!(
        !instructions
            .iter()
            .any(|i| matches!(i.operation, Operation::MatchData { .. })),
        "a known dictionary is never matched at run time"
    );
    let tm2 = owner_of(&modules, 1, "tm2");
    assert!(
        instructions
            .iter()
            .any(|i| i.origin.rule == Rule::ResolveMethod
                && matches!(&i.operation, Operation::CallTop { binder, .. } if *binder == tm2))
    );
    let dict_t = owner_of(&modules, 1, "dictT");
    assert!(
        !program
            .instances
            .iter()
            .any(|i| i.module == 1 && i.binder == dict_t),
        "a known dictionary is never built"
    );
}

/// A dictionary that is not proven unique keeps its runtime dispatch: the
/// selector stays a constructor match and the call stays indirect.
#[test]
fn specialization_preserves_dispatch_for_an_unproven_dictionary() {
    use crate::nir::specialize::{Instance, specialize};
    use crate::nir::{Operation, Rule};
    let modules = nir_specialization_world();
    let root = Instance::whole(0, owner_of(&modules, 0, "useOpen"));
    let program = specialize(&modules, &[root]).unwrap();
    let caller = program.leaf(0).expect("lowered");
    let operations: Vec<_> = caller.function.blocks[0]
        .instructions
        .iter()
        .map(|i| (&i.operation, i.origin.rule))
        .collect();
    assert!(
        operations
            .iter()
            .any(|(op, rule)| matches!(op, Operation::TopReference { .. })
                && *rule == Rule::ResolveInstance),
        "the selector is referenced as an instance, not resolved to a method"
    );
    assert!(
        operations
            .iter()
            .any(|(op, _)| matches!(op, Operation::Apply { .. })),
        "the dispatch stays an indirect application"
    );
    let method = owner_of(&modules, 1, "method");
    let index = program
        .instances
        .iter()
        .position(|i| i.module == 1 && i.binder == method)
        .expect("the selector itself is specialized");
    let selector = program.leaf(index).expect("lowered");
    assert!(
        selector
            .function
            .blocks
            .iter()
            .flat_map(|b| &b.instructions)
            .any(|i| matches!(i.operation, Operation::MatchData { .. })),
        "the selector still matches the dictionary's constructor"
    );
}

/// The verifier re-derives the substitution from the source, so a candidate
/// whose types were substituted differently is rejected.
#[test]
fn verifier_rejects_a_wrong_substitution() {
    use crate::nir::lower::lower_leaf_specialized;
    use crate::nir::verify::verify_leaf_specialized;
    use crate::nir::{FnId, Operation};
    let modules = nir_specialization_world();
    let poly = owner_of(&modules, 1, "poly");
    let t = modules[1].types[0].clone();
    let u = modules[1].types[1].clone();
    let original =
        lower_leaf_specialized(&modules, 1, poly, FnId(0), std::slice::from_ref(&t), &[]).unwrap();
    verify_leaf_specialized(
        &modules,
        1,
        poly,
        FnId(0),
        &original,
        std::slice::from_ref(&t),
        &[],
    )
    .unwrap();
    // The instance the caller asked for is the caller's to state.
    assert!(
        verify_leaf_specialized(
            &modules,
            1,
            poly,
            FnId(0),
            &original,
            std::slice::from_ref(&u),
            &[]
        )
        .is_err()
    );
    for corruption in 0..4 {
        let mut candidate = original.clone();
        match corruption {
            0 => candidate.function.type_arguments = vec![u.clone()],
            1 => candidate.function.blocks[0].params[0].ty = crate::nir::shared(&u),
            2 => candidate.function.result_ty = u.clone(),
            _ => candidate.type_instantiations[0].2 = u.clone(),
        }
        assert!(
            verify_leaf_specialized(
                &modules,
                1,
                poly,
                FnId(0),
                &candidate,
                std::slice::from_ref(&t),
                &[]
            )
            .is_err(),
            "corruption {corruption} survived verification"
        );
    }
    // A call site's own type evidence is checked against the source too.
    let use_t = owner_of(&modules, 0, "useT");
    let caller = lower_leaf_specialized(&modules, 0, use_t, FnId(1), &[], &[]).unwrap();
    let mut candidate = caller.clone();
    let Operation::CallTop { type_arguments, .. } =
        &mut candidate.function.blocks[0].instructions[0].operation
    else {
        panic!("the call site is a direct call")
    };
    *type_arguments = vec![u];
    assert!(verify_leaf_specialized(&modules, 0, use_t, FnId(1), &candidate, &[], &[]).is_err());
}

/// Dictionary evidence is checked the same way: a candidate that names a
/// different dictionary, or a different method, is rejected.
#[test]
fn verifier_rejects_a_wrong_dictionary_target() {
    use crate::nir::lower::lower_leaf_specialized;
    use crate::nir::verify::verify_leaf_specialized;
    use crate::nir::{DictionaryRef, FnId, Operation};
    let modules = nir_specialization_world();
    let via = owner_of(&modules, 1, "viaDict");
    let dict_t = owner_of(&modules, 1, "dictT");
    let dict_u = owner_of(&modules, 1, "dictU");
    let tm2 = owner_of(&modules, 1, "tm2");
    let t = modules[1].types[0].clone();
    let reference = |binder| DictionaryRef {
        module: 1,
        binder,
        type_arguments: Vec::new(),
        dictionaries: Vec::new(),
    };
    let expected = [reference(dict_t)];
    let original = lower_leaf_specialized(
        &modules,
        1,
        via,
        FnId(0),
        std::slice::from_ref(&t),
        &expected,
    )
    .unwrap();
    verify_leaf_specialized(
        &modules,
        1,
        via,
        FnId(0),
        &original,
        std::slice::from_ref(&t),
        &expected,
    )
    .unwrap();
    // A different dictionary is a different instance, and the caller says which.
    assert!(
        verify_leaf_specialized(
            &modules,
            1,
            via,
            FnId(0),
            &original,
            std::slice::from_ref(&t),
            &[reference(dict_u)]
        )
        .is_err()
    );
    for corruption in 0..4 {
        let mut candidate = original.clone();
        match corruption {
            0 => candidate.function.dictionaries = Vec::new(),
            1 => candidate.function.dictionaries = vec![reference(dict_u)],
            2 => candidate.dictionary_parameters[0].2 = reference(dict_u),
            _ => {
                let call = candidate.function.blocks[0]
                    .instructions
                    .iter_mut()
                    .find(|i| matches!(i.operation, Operation::CallTop { .. }))
                    .expect("the method call");
                let Operation::CallTop { binder, .. } = &mut call.operation else {
                    unreachable!()
                };
                // The other method of the same dictionary: same shape, wrong target.
                *binder = tm2;
            }
        }
        assert!(
            verify_leaf_specialized(
                &modules,
                1,
                via,
                FnId(0),
                &candidate,
                std::slice::from_ref(&t),
                &expected
            )
            .is_err(),
            "dictionary corruption {corruption} survived verification"
        );
    }
}

#[test]
fn a_big_nat_literal_is_its_little_endian_limbs() {
    let big_nat = |value: &str| h2r_core_ir::Lit {
        kind: "number".into(),
        pretty: value.into(),
        codepoint: None,
        bytes: None,
        value: Some(value.into()),
        num_type: Some("BigNat".into()),
    };
    assert_eq!(
        crate::emit::big_nat_limbs(&big_nat("1000000000000000000000000000000000000")),
        Ok(vec![0xb34b_9f10_0000_0000, 0x00c0_97ce_7bc9_0715])
    );
    assert_eq!(
        crate::emit::big_nat_limbs(&big_nat("18446744073709551616")),
        Ok(vec![0, 1])
    );
    assert_eq!(crate::emit::big_nat_limbs(&big_nat("0")), Ok(vec![]));
    assert!(crate::emit::big_nat_limbs(&h2r_core_ir::Lit::int(7)).is_err());
}
