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
        matches!(block.instructions[0].operation, Operation::TopReference { module: 5, binder } if binder == target)
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
                }
            }
            1 => {
                instruction.operation = Operation::TopReference {
                    module: 99,
                    binder: target,
                }
            }
            2 => instruction.origin.rule = Rule::Literal,
            3 => instruction.origin.source = Source::Expr(u32::MAX),
            _ => {
                instruction.operation = Operation::Literal(h2r_core_ir::Lit {
                    kind: "int".into(),
                    pretty: "0".into(),
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
        matches!(instruction.operation, Operation::TopReference { module: 1, binder } if binder == target)
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
                }
            }
            1 => {
                instruction.operation = Operation::TopReference {
                    module: 1,
                    binder: u32::MAX,
                }
            }
            2 => instruction.origin.rule = Rule::Literal,
            3 => instruction.origin.source = crate::nir::Source::Expr(u32::MAX),
            _ => {
                instruction.operation = Operation::Literal(h2r_core_ir::Lit {
                    kind: "int".into(),
                    pretty: "0".into(),
                })
            }
        }
        verify(&leaf.function).unwrap();
        assert!(verify_leaf_in_world(&modules, 0, owner, FnId(0), &leaf).is_err());
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
        forged.function.blocks[0].instructions[0].result.ty = modules[0].types[0].clone();
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
            unique: format!("a{index}"),
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
            name: sn("Types", name),
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
        let Operation::InstantiateTop {
            module, arguments, ..
        } = &instruction.operation
        else {
            panic!()
        };
        assert_eq!(*module, usize::from(imported));
        assert_eq!(arguments, &modules[0].types[..2]);
        assert_eq!(instruction.result.ty, modules[0].types[3]);
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
        let Operation::InstantiateTop {
            module,
            binder,
            arguments,
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
        lam("a", lam("b", lvar("a"))),
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
                (binder(&sn("Main", "f"), "f", "f"), lit()),
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
                .contains("parameters, literals, top-level references or Int# applications")
        );
    }
}

#[test]
fn nir_direct_calls_require_exact_known_arity_and_closed_types() {
    use crate::nir::{FnId, lower::lower_leaf_in_world, verify::verify_leaf_in_world};
    use h2r_core_ir::Ty;
    for arity in [None, Some(0), Some(1), Some(3)] {
        let mut modules = nir_call_world(true);
        let owner = modules[0].top[0].pairs[0].binder;
        let target = modules[1].top[0].pairs[0].binder;
        let original = lower_leaf_in_world(&modules, 0, owner, FnId(0)).unwrap();
        modules[1].binders[target as usize].arity = arity;
        assert!(
            lower_leaf_in_world(&modules, 0, owner, FnId(0))
                .unwrap_err()
                .reason
                .contains("arity")
        );
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
    tycon.name = sn("M", "U");
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
            .contains("must precede")
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
    let literal = |n: &str| json!({"node": "Lit", "lit": {"kind": "int", "pretty": n}});
    let mut modules = nir_call_world(true);
    let types = modules[0].types.clone();
    let last = if two_literals {
        literal("20")
    } else {
        lvar("x")
    };
    modules[0] = module(
        "Main",
        vec![(
            binder(&sn("Main", "main"), "main", "main"),
            lam(
                "x",
                lam(
                    "y",
                    app(
                        app(gvar(&sn("Lib", "target"), "target"), literal("10")),
                        last,
                    ),
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
            matches!(&instructions[0].operation, Operation::Literal(lit) if lit.pretty == "10")
        );
        assert_eq!(instructions[0].result.ty, modules[0].types[0]);
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
                instructions[0].result.ty = h2r_core_ir::Ty::Lit {
                    kind: "Nat".into(),
                    text: "42".into(),
                }
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
        let Operation::TopReference { module, binder } = instructions[index].operation else {
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
                }
            }
            1 => {
                instruction.operation = Operation::TopReference {
                    module: 0,
                    binder: u32::MAX,
                }
            }
            2 => instruction.origin.rule = Rule::Literal,
            3 => {
                instruction.result.ty = h2r_core_ir::Ty::Lit {
                    kind: "Nat".into(),
                    text: "42".into(),
                }
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
    for payload in ["9223372036854775808#", "42u64", "0; panic!()#"] {
        let mut modules = scalar_emission_world();
        for expr in &mut modules[0].exprs {
            if let Expr::Lit(lit) = expr {
                lit.pretty = payload.into();
            }
        }
        assert!(crate::emit::emit_entry(&modules, &sn("Main", "main")).is_err());
    }
    assert!(crate::emit::emit_entry(&nir_call_world(true), &sn("Main", "main")).is_err());
    assert!(crate::emit::emit_entry(&scalar_emission_world(), "main").is_err());
}

#[test]
fn scalar_emission_refuses_recursive_closure() {
    let mut modules = scalar_emission_world();
    // Main's existing source call now resolves back to its own definition.
    let target = modules[1].top[0].pairs[0].binder;
    modules[1].binders[target as usize].name = sn("Lib", "unused");
    let owner = modules[0].top[0].pairs[0].binder;
    modules[0].binders[owner as usize].name = sn("Lib", "target");
    modules[0].binders[owner as usize].arity = Some(2);
    assert!(
        crate::emit::emit_entry(&modules, &sn("Lib", "target"))
            .unwrap_err()
            .contains("recursive")
    );
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
        let emitted = crate::emit::emit_entry(&modules, &sn("Main", "main")).unwrap();
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
                    lit: h2r_core_ir::Lit {
                        kind: "number".into(),
                        pretty: "0#".into(),
                    },
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
            "con": {"kind": "LitAlt", "lit": {"kind": "number", "pretty": format!("{pattern}#")}},
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
    let rust = crate::emit::emit_entry(&modules, &sn("Main", "main")).unwrap();
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
    let rust = crate::emit::emit_entry(&modules, &sn("Main", "main")).unwrap();
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
                Operation::EvaluateBlock { target, arguments } => {
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
                Operation::Move(value) | Operation::Force(value) => value.0 += 1000,
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
            2 => alts[1]["con"]["lit"]["pretty"] = json!("9223372036854775808#"),
            3 => alts[1]["con"]["lit"]["pretty"] = json!("0#;panic!()"),
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
        let rust = crate::emit::emit_entry(&modules, &sn("Main", "main")).unwrap();
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
        let emitted = crate::emit::emit_entry(&modules, &sn("Main", "main")).unwrap();
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
                _ => instruction.result.ty = modules[0].types[1].clone(),
            }
            assert!(
                verify_leaf_in_world(&modules, 0, owner, FnId(0), &bad).is_err(),
                "{symbol} mutation {mutation}"
            );
        }
    }
}

#[test]
fn int_arithmetic_refuses_unknown_names_metadata_types_and_arity() {
    use crate::nir::{FnId, lower::lower_leaf_in_world};
    for symbol in ["quotInt#", "plusWord#", "notARealPrimOp#"] {
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
