//! Diagnostic text for leaf NIR; not Rust emission or a serialization contract.

use std::fmt::Write;

use super::{DictionaryRef, Exit, Operation, lower::LoweredLeaf};

/// Instance evidence, printed as the compile-time identity it is.
fn dictionary_list(dictionaries: &[DictionaryRef]) -> String {
    let entries: Vec<_> = dictionaries
        .iter()
        .map(|d| {
            format!(
                "module {} binder {} types {:?} dicts {}",
                d.module,
                d.binder,
                d.type_arguments,
                dictionary_list(&d.dictionaries)
            )
        })
        .collect();
    format!("[{}]", entries.join("; "))
}

pub fn format_leaf(leaf: &LoweredLeaf) -> String {
    let f = &leaf.function;
    let mut out = format!(
        "fn f{} [module {}, binder {}] -> {:?}\n",
        f.id.0, f.module, f.owner, f.result_ty
    );
    for param in &f.type_params {
        writeln!(out, "  type param {} [{}]", param.occ, param.unique).unwrap();
    }
    for argument in &f.type_arguments {
        writeln!(out, "  specialized at {argument:?}").unwrap();
    }
    if !f.dictionaries.is_empty() {
        writeln!(out, "  dictionaries {}", dictionary_list(&f.dictionaries)).unwrap();
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
                Operation::MakeClosure { target, arguments } => {
                    format!("make-closure b{} {arguments:?}", target.0)
                }
                Operation::Apply { callee, arguments } => {
                    format!("apply v{} {arguments:?}", callee.0)
                }
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
                Operation::MakeUnboxedTuple { arguments } => {
                    format!("unboxed-tuple {arguments:?}")
                }
                Operation::UnboxedTupleField { tuple, index } => {
                    format!("unboxed-tuple-field v{} .{index}", tuple.0)
                }
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
                Operation::CharCompare { op, arguments } => {
                    format!("char-{op:?} {arguments:?}")
                }
                Operation::OrdChar(value) => format!("ord-char v{}", value.0),
                Operation::ChrChar(value) => format!("chr-char v{}", value.0),
                Operation::AppendList { left, right, .. } => {
                    format!("append-list v{} v{}", left.0, right.0)
                }
                Operation::ListPredicate(predicate) => format!(
                    "list-{:?} {:?} v{} v{}",
                    predicate.predicate, predicate.equality, predicate.left.0, predicate.right.0
                ),
                Operation::ListFunction(list) => format!(
                    "list-{:?} {}",
                    list.function,
                    list.arguments
                        .iter()
                        .map(|v| format!("v{}", v.0))
                        .collect::<Vec<_>>()
                        .join(" ")
                ),
                Operation::DataToTag {
                    value,
                    constructors,
                } => format!("data-to-tag v{} of {}", value.0, constructors.len()),
                Operation::TagToEnum { tag, constructors } => {
                    format!("tag-to-enum v{} of {}", tag.0, constructors.len())
                }
                Operation::PointerEquality { left, right } => {
                    format!("pointer-equality v{} v{}", left.0, right.0)
                }
                Operation::CompareStrings(compare) => {
                    format!("compare-strings v{} v{}", compare.left.0, compare.right.0)
                }
                Operation::RaiseError { message } => format!("raise-error v{}", message.0),
                Operation::EmptyCase { scrutinee } => format!("empty-case v{}", scrutinee.0),
                Operation::UnpackString(unpack) => format!(
                    "unpack-string {:?} {} bytes{}",
                    unpack.encoding,
                    unpack.bytes.len(),
                    match unpack.tail {
                        Some(tail) => format!(" onto v{}", tail.0),
                        None => String::new(),
                    }
                ),
                Operation::EvaluateBlock { target, arguments } => {
                    format!("evaluate b{} {arguments:?}", target.0)
                }
                Operation::Literal(lit) => format!("literal {} {:?}", lit.kind, lit.pretty),
                Operation::Move(value) => format!("move v{}", value.0),
                Operation::Force(value) => format!("force v{}", value.0),
                Operation::TopReference {
                    module,
                    binder,
                    type_arguments,
                    dictionaries,
                } => {
                    format!(
                        "top-ref module {module} binder {binder} types {type_arguments:?} dicts {}",
                        dictionary_list(dictionaries)
                    )
                }
                Operation::CallTop {
                    module,
                    binder,
                    type_arguments,
                    dictionaries,
                    arguments,
                } => {
                    format!(
                        "call-top module {module} binder {binder} types {type_arguments:?} dicts {} args {arguments:?}",
                        dictionary_list(dictionaries)
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
            Exit::Diverge { name, .. } => format!("diverge {name}"),
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
    for (expr, binder, argument) in &leaf.type_instantiations {
        writeln!(
            out,
            "  instantiated type lambda Expr({expr}) -> Binder({binder}) = {argument:?}"
        )
        .unwrap();
    }
    for (expr, binder, dictionary) in &leaf.dictionary_parameters {
        writeln!(
            out,
            "  erased dictionary lambda Expr({expr}) -> Binder({binder}) = {}",
            dictionary_list(std::slice::from_ref(dictionary))
        )
        .unwrap();
    }
    for expr in &leaf.erased_ticks {
        writeln!(out, "  erased tick Expr({expr})").unwrap();
    }
    out
}
