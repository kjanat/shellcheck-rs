//! Diagnostic text for leaf NIR; not Rust emission or a serialization contract.

use std::fmt::Write;

use super::{Exit, Operation, lower::LoweredLeaf};

pub fn format_leaf(leaf: &LoweredLeaf) -> String {
    let f = &leaf.function;
    let mut out = format!(
        "fn f{} [module {}, binder {}] -> {:?}\n",
        f.id.0, f.module, f.owner, f.result_ty
    );
    for param in &f.type_params {
        writeln!(out, "  type param {} [{}]", param.occ, param.unique).unwrap();
    }
    for block in &f.blocks {
        writeln!(
            out,
            "  b{}{}:",
            block.id.0,
            if block.id == f.entry { " (entry)" } else { "" }
        )
        .unwrap();
        for param in &block.params {
            writeln!(out, "    param v{}: {:?}", param.id.0, param.ty).unwrap();
        }
        for instruction in &block.instructions {
            let operation = match &instruction.operation {
                Operation::LocalScope {
                    definitions,
                    target,
                    arguments,
                } => format!(
                    "local-scope {definitions:?} body b{} {arguments:?}",
                    target.0
                ),
                Operation::CallLocal { target, arguments } => {
                    format!("call-local b{} {arguments:?}", target.0)
                }
                Operation::Construct {
                    constructor,
                    arguments,
                } => format!(
                    "construct {} tag {} {arguments:?}",
                    constructor.name, constructor.tag
                ),
                Operation::MatchData {
                    scrutinee,
                    arguments,
                    arms,
                } => format!(
                    "match-data v{} captures {arguments:?} arms {arms:?}",
                    scrutinee.0
                ),
                Operation::DelayBlock { target, arguments } => {
                    format!("delay b{} {arguments:?}", target.0)
                }
                Operation::BoxInt(value) => format!("box-int v{}", value.0),
                Operation::UnboxInt(value) => format!("unbox-int v{}", value.0),
                Operation::IntBinary { op, arguments } => format!("int-{op:?} {arguments:?}"),
                Operation::EvaluateBlock { target, arguments } => {
                    format!("evaluate b{} {arguments:?}", target.0)
                }
                Operation::Literal(lit) => format!("literal {} {:?}", lit.kind, lit.pretty),
                Operation::Move(value) => format!("move v{}", value.0),
                Operation::Force(value) => format!("force v{}", value.0),
                Operation::TopReference { module, binder } => {
                    format!("top-ref module {module} binder {binder}")
                }
                Operation::InstantiateTop {
                    module,
                    binder,
                    arguments,
                } => {
                    format!("instantiate-top module {module} binder {binder} types {arguments:?}")
                }
                Operation::CallTop {
                    module,
                    binder,
                    type_arguments,
                    arguments,
                } => {
                    format!(
                        "call-top module {module} binder {binder} types {type_arguments:?} args {arguments:?}"
                    )
                }
            };
            writeln!(
                out,
                "    v{} = {} : {:?}  [{:?}, {:?}]",
                instruction.result.id.0,
                operation,
                instruction.result.ty,
                instruction.origin.source,
                instruction.origin.rule
            )
            .unwrap();
        }
        let exit = match &block.terminator.exit {
            Exit::IntSwitch {
                scrutinee,
                arms,
                default,
                args,
            } => format!(
                "int-switch v{} {arms:?} default {default:?} args {args:?}",
                scrutinee.0
            ),
            Exit::Return(value) => format!("return v{}", value.0),
            Exit::Jump { target, args } => format!(
                "jump b{}({})",
                target.0,
                args.iter()
                    .map(|v| format!("v{}", v.0))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        };
        writeln!(
            out,
            "    {exit}  [{:?}, {:?}]",
            block.terminator.origin.source, block.terminator.origin.rule
        )
        .unwrap();
    }
    for (expr, value) in &leaf.parameters {
        writeln!(out, "  lambda Expr({expr}) -> param v{}", value.0).unwrap();
    }
    for (expr, binder) in &leaf.type_parameters {
        writeln!(out, "  erased type lambda Expr({expr}) -> Binder({binder})").unwrap();
    }
    for expr in &leaf.erased_ticks {
        writeln!(out, "  erased tick Expr({expr})").unwrap();
    }
    out
}
