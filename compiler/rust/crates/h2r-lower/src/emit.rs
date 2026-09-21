//! Acyclic monomorphic scalar/algebraic functions and their complete dependency
//! closure. Text I/O is an explicit integer-only generated CLI adapter,
//! not a translation of Haskell IO. Unsupported carriers/operations fail closed.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write;

use h2r_core_ir::{Module, Ty};

use crate::nir::{
    Block, Exit, FnId, Function, IntBinary, Operation, boxed, data, lower::lower_leaf_in_world,
};

type Key = (usize, u32);

fn scalar(ty: &Ty) -> bool {
    boxed::is_int(ty)
        || matches!(ty, Ty::Con { tycon, args } if tycon.name == "$ghc-prim$GHC.Prim$Int#" && args.is_empty())
}

fn carrier(ty: &Ty) -> &'static str {
    if boxed::is_int(ty) {
        "HInt"
    } else if scalar(ty) {
        "i64"
    } else {
        "HData"
    }
}

// Source correspondence has already established acyclic regions and consistent
// return types along every successor, independently of block numbering.
fn block_result<'a>(function: &'a Function, block: &'a Block) -> &'a Ty {
    let target = match &block.terminator.exit {
        Exit::Return(value) => {
            return &block
                .params
                .iter()
                .chain(block.instructions.iter().map(|i| &i.result))
                .find(|v| v.id == *value)
                .expect("verified return")
                .ty;
        }
        Exit::Jump { target, .. } => target,
        Exit::IntSwitch { default, .. } => default,
    };
    block_result(
        function,
        function
            .blocks
            .iter()
            .find(|b| b.id == *target)
            .expect("verified target"),
    )
}

fn integer(kind: &str, pretty: &str) -> Result<i64, String> {
    if kind != "number" {
        return Err("Int# emission requires a numeric Core literal".into());
    }
    pretty
        .strip_suffix('#')
        .ok_or("unsupported Int# literal spelling")?
        .parse()
        .map_err(|_| "Int# literal is not a signed 64-bit decimal".into())
}

/// Select one exact external entry and lower every required definition. No
/// source is returned until the entire closure has passed lowering and checks.
pub fn emit_entry(modules: &[Module], entry: &str) -> Result<String, String> {
    if !h2r_core_ir::is_external_name(entry) {
        return Err("Rust emission requires an external stable entry name".into());
    }
    let matches: Vec<_> = modules
        .iter()
        .enumerate()
        .flat_map(|(m, module)| {
            module
                .top
                .iter()
                .flat_map(|group| &group.pairs)
                .filter(move |pair| module.binder(pair.binder).name == entry)
                .map(move |pair| (m, pair.binder))
        })
        .collect();
    let [root] = matches.as_slice() else {
        return Err(format!("entry matched {} definitions", matches.len()));
    };
    let mut pending = vec![*root];
    let mut functions = BTreeMap::new();
    let mut edges = BTreeMap::<Key, BTreeSet<Key>>::new();
    let supported = |ty: &Ty| scalar(ty) || modules.iter().any(|m| data::is_data(m, ty));
    while let Some(key @ (module, binder)) = pending.pop() {
        if functions.contains_key(&key) {
            continue;
        }
        let leaf = lower_leaf_in_world(modules, module, binder, FnId(functions.len() as u32))
            .map_err(|error| {
                format!(
                    "module {module} binder {binder} at {:?}: {}",
                    error.source, error.reason
                )
            })?;
        let function = &leaf.function;
        if !function.type_params.is_empty()
            || !supported(&function.result_ty)
            || function
                .blocks
                .iter()
                .flat_map(|b| &b.params)
                .any(|p| !supported(&p.ty))
        {
            return Err(format!(
                "module {module} binder {binder}: emission requires monomorphic supported scalar/algebraic carriers"
            ));
        }
        let mut dependencies = BTreeSet::new();
        for instruction in function.blocks.iter().flat_map(|b| &b.instructions) {
            if !supported(&instruction.result.ty) {
                return Err("unsupported instruction carrier".into());
            }
            match &instruction.operation {
                Operation::Construct { .. }
                | Operation::MatchData { .. }
                | Operation::IntBinary { .. }
                | Operation::Move(_)
                | Operation::BoxInt(_)
                | Operation::UnboxInt(_)
                | Operation::DelayBlock { .. }
                | Operation::EvaluateBlock { .. } => {}
                Operation::Literal(lit) => {
                    if carrier(&instruction.result.ty) != "i64" {
                        return Err("boxed Int requires constructor evidence, not a literal".into());
                    }
                    integer(&lit.kind, &lit.pretty)?;
                }
                Operation::TopReference { module, binder }
                | Operation::CallTop { module, binder, .. } => {
                    dependencies.insert((*module, *binder));
                }
                _ => return Err("unsupported operation in scalar Rust backend".into()),
            }
        }
        pending.extend(dependencies.iter().copied());
        edges.insert(key, dependencies);
        functions.insert(key, leaf);
    }
    if !scalar(&functions[root].function.result_ty)
        || functions[root].function.blocks[0]
            .params
            .iter()
            .any(|p| !scalar(&p.ty))
    {
        return Err(
            "CLI adapter requires Int#/Int inputs and output; algebraic values may be internal"
                .into(),
        );
    }
    // Refuse recursive definitions until the runtime/stack semantics are covered.
    let mut done = BTreeSet::new();
    while done.len() != functions.len() {
        let before = done.len();
        for (key, dependencies) in &edges {
            if dependencies.is_subset(&done) {
                done.insert(*key);
            }
        }
        if done.len() == before {
            return Err("recursive scalar dependency closure is not supported".into());
        }
    }
    let mut out = String::from(
        "// Generated from source-verified scalar NIR. CLI I/O is an adapter.\n#[cfg(not(target_pointer_width = \"64\"))]\ncompile_error!(\"Int# backend requires a 64-bit target\");\n",
    );
    let has_boxed = functions.values().any(|leaf| {
        carrier(&leaf.function.result_ty) != "i64"
            || leaf.function.blocks.iter().any(|b| {
                b.params
                    .iter()
                    .chain(b.instructions.iter().map(|i| &i.result))
                    .any(|v| carrier(&v.ty) != "i64")
            })
    });
    if has_boxed {
        out.push_str("\n#[allow(dead_code)]\nmod h2r_rt {\n");
        out.push_str(include_str!("../../h2r-rt/src/lib.rs"));
        out.push_str("\n}\n#[allow(unused_imports)]\nuse h2r_rt::Int as HInt;\n#[allow(unused_imports)]\nuse h2r_rt::{Data as HData, Field as HField};\n");
    }
    for ((module, binder), leaf) in &functions {
        let block = &leaf.function.blocks[0];
        let parameters = block
            .params
            .iter()
            .map(|p| format!("v{}: {}", p.id.0, carrier(&p.ty)))
            .collect::<Vec<_>>()
            .join(", ");
        writeln!(
            out,
            "#[allow(unused_variables)]\nfn f_{module}_{binder}({parameters}) -> {} {{",
            carrier(&leaf.function.result_ty)
        )
        .unwrap();
        for block in &leaf.function.blocks {
            let block_parameters = block
                .params
                .iter()
                .map(|p| format!("v{}: {}", p.id.0, carrier(&p.ty)))
                .collect::<Vec<_>>()
                .join(", ");
            writeln!(
                out,
                "    #[allow(unused_variables)]\n    fn b_{}({block_parameters}) -> {} {{",
                block.id.0,
                carrier(block_result(&leaf.function, block))
            )
            .unwrap();
            let value = |id: crate::nir::ValueId| {
                let ty = &block
                    .params
                    .iter()
                    .chain(block.instructions.iter().map(|i| &i.result))
                    .find(|v| v.id == id)
                    .expect("verified operand")
                    .ty;
                if carrier(ty) != "i64" {
                    format!("v{}.clone()", id.0)
                } else {
                    format!("v{}", id.0)
                }
            };
            for instruction in &block.instructions {
                let expression = match &instruction.operation {
                    Operation::Construct {
                        constructor,
                        arguments,
                    } => {
                        let fields = arguments
                            .iter()
                            .zip(&constructor.fields)
                            .map(|(v, t)| {
                                let variant = match carrier(t) {
                                    "i64" => "Int64",
                                    "HInt" => "Int",
                                    _ => "Data",
                                };
                                format!("HField::{variant}({})", value(*v))
                            })
                            .collect::<Vec<_>>()
                            .join(", ");
                        let strict = constructor
                            .strict
                            .iter()
                            .enumerate()
                            .filter(|(_, s)| **s)
                            .map(|(i, _)| format!("fields[{i}].force();"))
                            .collect::<Vec<_>>()
                            .join(" ");
                        format!(
                            "{{ let fields = vec![{fields}]; {strict} HData::ready({:?}, fields) }}",
                            constructor.name
                        )
                    }
                    Operation::MatchData {
                        scrutinee,
                        arguments,
                        arms,
                    } => {
                        let captures = arguments
                            .iter()
                            .map(|v| value(*v))
                            .chain(std::iter::once(value(*scrutinee)))
                            .collect::<Vec<_>>();
                        let mut code = format!(
                            "{{ let node = v{}.force(); match node.constructor {{",
                            scrutinee.0
                        );
                        // DEFAULT may be first in Core; Rust's wildcard must be last.
                        for arm in arms
                            .iter()
                            .filter(|a| a.constructor.is_some())
                            .chain(arms.iter().filter(|a| a.constructor.is_none()))
                        {
                            let mut args = captures.clone();
                            let pattern = if let Some(c) = &arm.constructor {
                                for (i, t) in c.fields.iter().enumerate() {
                                    let method = match carrier(t) {
                                        "i64" => "int64",
                                        "HInt" => "int",
                                        _ => "data",
                                    };
                                    args.push(format!("node.fields[{i}].{method}()"));
                                }
                                format!("{:?}", c.name)
                            } else {
                                "_".into()
                            };
                            write!(
                                code,
                                " {pattern} => b_{}({}),",
                                arm.target.0,
                                args.join(", ")
                            )
                            .unwrap();
                        }
                        if arms.iter().all(|a| a.constructor.is_some()) {
                            code.push_str(" _ => panic!(\"invalid constructor family\"),");
                        }
                        code.push_str(" } }");
                        code
                    }
                    Operation::DelayBlock { target, arguments } => {
                        let captures = arguments
                            .iter()
                            .enumerate()
                            .map(|(n, v)| format!("let c{n} = {};", value(*v)))
                            .collect::<Vec<_>>()
                            .join(" ");
                        let args = (0..arguments.len())
                            .map(|n| format!("c{n}"))
                            .collect::<Vec<_>>()
                            .join(", ");
                        format!(
                            "{{ {captures} {}::defer(move || b_{}({args}).force()) }}",
                            carrier(&instruction.result.ty),
                            target.0
                        )
                    }
                    Operation::BoxInt(v) => format!("HInt::ready(v{})", v.0),
                    Operation::UnboxInt(v) => format!("v{}.force()", v.0),
                    Operation::EvaluateBlock { target, arguments } => {
                        let args = arguments
                            .iter()
                            .map(|v| value(*v))
                            .collect::<Vec<_>>()
                            .join(", ");
                        format!("b_{}({args})", target.0)
                    }
                    Operation::Move(v) => value(*v),
                    Operation::IntBinary { op, arguments } => {
                        let left = arguments[0].0;
                        let right = arguments[1].0;
                        match op {
                            IntBinary::Add => format!("v{left}.wrapping_add(v{right})"),
                            IntBinary::Subtract => format!("v{left}.wrapping_sub(v{right})"),
                            IntBinary::Multiply => format!("v{left}.wrapping_mul(v{right})"),
                            IntBinary::Equal => format!("i64::from(v{left} == v{right})"),
                            IntBinary::NotEqual => format!("i64::from(v{left} != v{right})"),
                            IntBinary::Less => format!("i64::from(v{left} < v{right})"),
                            IntBinary::LessEqual => format!("i64::from(v{left} <= v{right})"),
                            IntBinary::Greater => format!("i64::from(v{left} > v{right})"),
                            IntBinary::GreaterEqual => format!("i64::from(v{left} >= v{right})"),
                        }
                    }
                    Operation::Literal(lit) => format!("{}i64", integer(&lit.kind, &lit.pretty)?),
                    Operation::TopReference { module, binder } => {
                        if !functions[&(*module, *binder)].function.blocks[0]
                            .params
                            .is_empty()
                        {
                            return Err(
                                "function-valued reference cannot use the Int# carrier".into()
                            );
                        }
                        format!("f_{module}_{binder}()")
                    }
                    Operation::CallTop {
                        module,
                        binder,
                        arguments,
                        type_arguments,
                    } => {
                        if !type_arguments.is_empty() {
                            return Err(
                                "polymorphic calls need specialization before emission".into()
                            );
                        }
                        if functions[&(*module, *binder)].function.blocks[0]
                            .params
                            .len()
                            != arguments.len()
                        {
                            return Err("emitted target parameter count disagrees with call".into());
                        }
                        let args = arguments
                            .iter()
                            .map(|arg| value(*arg))
                            .collect::<Vec<_>>()
                            .join(", ");
                        format!("f_{module}_{binder}({args})")
                    }
                    _ => return Err("unsupported operation in scalar Rust backend".into()),
                };
                writeln!(
                    out,
                    "    let v{}: {} = {expression};",
                    instruction.result.id.0,
                    carrier(&instruction.result.ty)
                )
                .unwrap();
            }
            let call = |target: &crate::nir::BlockId, args: &[crate::nir::ValueId]| {
                format!(
                    "b_{}({})",
                    target.0,
                    args.iter()
                        .map(|v| value(*v))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            };
            match &block.terminator.exit {
                Exit::Return(v) => writeln!(out, "    {}", value(*v)).unwrap(),
                Exit::Jump { target, args } => writeln!(out, "    {}", call(target, args)).unwrap(),
                Exit::IntSwitch {
                    scrutinee,
                    arms,
                    default,
                    args,
                } => {
                    writeln!(out, "    match v{} {{", scrutinee.0).unwrap();
                    for (pattern, target) in arms {
                        writeln!(out, "        {pattern}i64 => {},", call(target, args)).unwrap();
                    }
                    writeln!(out, "        _ => {},\n    }}", call(default, args)).unwrap();
                }
            }
            writeln!(out, "    }}").unwrap();
        }
        let args = leaf.function.blocks[0]
            .params
            .iter()
            .map(|p| format!("v{}", p.id.0))
            .collect::<Vec<_>>()
            .join(", ");
        if carrier(&leaf.function.result_ty) != "i64" {
            let result_carrier = carrier(&leaf.function.result_ty);
            if block.params.is_empty() {
                writeln!(out, "    std::thread_local! {{ static VALUE: {result_carrier} = {result_carrier}::defer(|| b_{}().force()); }}\n    VALUE.with(Clone::clone)\n}}", leaf.function.entry.0).unwrap();
            } else {
                writeln!(
                    out,
                    "    {result_carrier}::defer(move || b_{}({args}).force())\n}}",
                    leaf.function.entry.0
                )
                .unwrap();
            }
        } else {
            writeln!(out, "    b_{}({args})\n}}", leaf.function.entry.0).unwrap();
        }
    }
    let arity = functions[root].function.blocks[0].params.len();
    let args = functions[root].function.blocks[0]
        .params
        .iter()
        .enumerate()
        .map(|(i, p)| {
            if boxed::is_int(&p.ty) {
                format!("HInt::ready(args[{i}])")
            } else {
                format!("args[{i}]")
            }
        })
        .collect::<Vec<_>>()
        .join(", ");
    writeln!(
        out,
        "#[allow(unused_imports)]\nuse f_{}_{} as h2r_entry;",
        root.0, root.1
    )
    .unwrap();
    let force = if boxed::is_int(&functions[root].function.result_ty) {
        ".force()"
    } else {
        ""
    };
    writeln!(out, "fn main() {{\n    let args: Vec<i64> = std::env::args().skip(1).map(|s| s.parse().expect(\"expected signed 64-bit integer\")).collect();\n    assert_eq!(args.len(), {arity}, \"wrong argument count\");\n    println!(\"{{}}\", f_{}_{}({args}){force});\n}}", root.0, root.1).unwrap();
    Ok(out)
}
