//! Monomorphic scalar/algebraic functions and their complete dependency
//! closure. Text I/O is an explicit integer-only generated CLI adapter,
//! not a translation of Haskell IO. Unsupported carriers/operations fail closed.
//!
//! Emission works on *instances*, not bindings: one polymorphic or
//! dictionary-taking source binding becomes one Rust function per instance the
//! program actually needs, named by its instance index. A call site names the
//! instance it resolved to, so nothing here re-derives a specialization.

use std::collections::BTreeSet;
use std::fmt::Write;

use h2r_core_ir::{Module, Ty};

use crate::nir::{
    Block, DictionaryRef, Exit, Function, IntBinary, Operation, boxed, data,
    specialize::{self, Instance},
};

fn scalar(ty: &Ty) -> bool {
    boxed::is_int(ty)
        || matches!(ty, Ty::Con { tycon, args } if tycon.name == "$ghc-prim$GHC.Prim$Int#" && args.is_empty())
}

fn carrier(ty: &Ty) -> &'static str {
    if boxed::is_int(ty) {
        "HInt"
    } else if scalar(ty) {
        "i64"
    } else if matches!(ty, Ty::Fun { .. }) {
        "HClosure"
    } else {
        "HData"
    }
}

fn field_kind(ty: &Ty) -> (&'static str, &'static str) {
    match carrier(ty) {
        "i64" => ("Int64", "int64"),
        "HInt" => ("Int", "int"),
        "HClosure" => ("Closure", "closure"),
        _ => ("Data", "data"),
    }
}

fn closure(
    target: &str,
    captures: &[String],
    signature: &Ty,
    arity: usize,
) -> Result<String, String> {
    if arity == 0 {
        return Err("closure has no value parameters".into());
    }
    let bindings = captures
        .iter()
        .enumerate()
        .map(|(n, v)| format!("let c{n} = {v};"))
        .collect::<Vec<_>>()
        .join(" ");
    let mut args = captures
        .iter()
        .enumerate()
        .map(|(n, _)| format!("c{n}.clone()"))
        .collect::<Vec<_>>();
    let mut result = signature;
    for n in 0..arity {
        let Ty::Fun { arg, res, .. } = result else {
            return Err("closure code arity exceeds signature".into());
        };
        args.push(format!("a[{n}].{}()", field_kind(arg).1));
        result = res;
    }
    Ok(format!(
        "{{ {bindings} HClosure::ready({arity}, move |a| HField::{}({target}({}))) }}",
        field_kind(result).0,
        args.join(", ")
    ))
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

/// The instance a reference names. Specialization interned it already, so a
/// missing entry would be a driver defect rather than a source refusal.
fn instance_of(
    specialization: &specialize::Specialization,
    reference: &DictionaryRef,
) -> Result<usize, String> {
    specialization
        .resolve(reference)
        .ok_or_else(|| "a call names an instance the specialization pass did not lower".into())
}

fn reference_of(
    module: usize,
    binder: u32,
    type_arguments: &[Ty],
    dictionaries: &[DictionaryRef],
) -> DictionaryRef {
    DictionaryRef {
        module,
        binder,
        type_arguments: type_arguments.to_vec(),
        dictionaries: dictionaries.to_vec(),
    }
}

/// Select one exact external entry and lower every required instance. No
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
    let [(root_module, root_binder)] = matches.as_slice() else {
        return Err(format!("entry matched {} definitions", matches.len()));
    };
    let specialization =
        specialize::specialize(modules, &[Instance::whole(*root_module, *root_binder)])
            .map_err(|error| error.to_string())?;
    let evidence = crate::nir::World::of(modules, 0)?;
    let supported = |ty: &Ty| data::supported(&evidence, ty);
    let leaves: Vec<&crate::nir::lower::LoweredLeaf> = specialization
        .lowered
        .iter()
        .map(|leaf| {
            leaf.as_ref()
                .expect("a complete specialization lowers every instance")
        })
        .collect();
    let mut edges: Vec<BTreeSet<usize>> = Vec::with_capacity(leaves.len());
    for (index, leaf) in leaves.iter().enumerate() {
        let function = &leaf.function;
        let instance = &specialization.instances[index];
        if !function.type_params.is_empty()
            || !supported(&function.result_ty)
            || function
                .blocks
                .iter()
                .flat_map(|b| &b.params)
                .any(|p| !supported(&p.ty))
        {
            return Err(format!(
                "module {} binder {}: emission requires monomorphic supported scalar/algebraic carriers",
                instance.module, instance.binder
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
                Operation::CallLocal { .. }
                | Operation::LocalScope { .. }
                | Operation::MakeClosure { .. }
                | Operation::Apply { .. } => {}
                Operation::Literal(lit) => {
                    if carrier(&instruction.result.ty) != "i64" {
                        return Err("boxed Int requires constructor evidence, not a literal".into());
                    }
                    integer(&lit.kind, &lit.pretty)?;
                }
                Operation::TopReference {
                    module,
                    binder,
                    type_arguments,
                    dictionaries,
                }
                | Operation::CallTop {
                    module,
                    binder,
                    type_arguments,
                    dictionaries,
                    ..
                } => {
                    dependencies.insert(instance_of(
                        &specialization,
                        &reference_of(*module, *binder, type_arguments, dictionaries),
                    )?);
                }
                _ => return Err("unsupported operation in scalar Rust backend".into()),
            }
        }
        edges.push(dependencies);
    }
    let entry_function = &leaves[0].function;
    let direct_arity = entry_function.blocks[0].params.len();
    let mut entry_types: Vec<_> = entry_function.blocks[0]
        .params
        .iter()
        .map(|p| &p.ty)
        .collect();
    let mut entry_result = &entry_function.result_ty;
    while let Ty::Fun { arg, res, .. } = entry_result {
        entry_types.push(arg);
        entry_result = res;
    }
    if !scalar(entry_result) || entry_types.iter().any(|t| !scalar(t)) {
        return Err(
            "CLI adapter requires Int#/Int inputs and output; algebraic values may be internal"
                .into(),
        );
    }
    // Refuse cycles involving a value, even through a function. Only function
    // recursion is supported here, not productive recursive thunk graphs.
    for (index, leaf) in leaves.iter().enumerate() {
        if !leaf.function.blocks[0].params.is_empty() {
            continue;
        }
        let mut seen = BTreeSet::new();
        let mut pending: Vec<_> = edges[index].iter().copied().collect();
        while let Some(next) = pending.pop() {
            if next == index {
                return Err("recursive value dependency closure is not supported".into());
            }
            if seen.insert(next) {
                pending.extend(edges[next].iter().copied());
            }
        }
    }
    let mut out = String::from(
        "// Generated from source-verified scalar NIR. CLI I/O is an adapter.\n#[cfg(not(target_pointer_width = \"64\"))]\ncompile_error!(\"Int# backend requires a 64-bit target\");\n",
    );
    let has_boxed = leaves.iter().any(|leaf| {
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
        out.push_str("\n}\n#[allow(unused_imports)]\nuse h2r_rt::Int as HInt;\n#[allow(unused_imports)]\nuse h2r_rt::{Data as HData, Field as HField, Closure as HClosure};\n");
    }
    // An explicit dispatcher makes scalar tail transfers stack bounded,
    // including mutually recursive top-level functions and local join loops.
    out.push_str("#[allow(non_camel_case_types)]\nenum HState {\n");
    let mut dispatch = String::new();
    for (index, leaf) in leaves.iter().enumerate() {
        for block in &leaf.function.blocks {
            if carrier(block_result(&leaf.function, block)) != "i64" {
                continue;
            }
            let types = block
                .params
                .iter()
                .map(|p| carrier(&p.ty))
                .collect::<Vec<_>>()
                .join(", ");
            let args = block
                .params
                .iter()
                .map(|p| format!("v{}", p.id.0))
                .collect::<Vec<_>>()
                .join(", ");
            writeln!(out, "B_{index}_{}({types}),", block.id.0).unwrap();
            writeln!(
                dispatch,
                "HState::B_{index}_{}({args}) => s_{index}_{}({args}),",
                block.id.0, block.id.0
            )
            .unwrap();
        }
    }
    out.push_str("}\nenum HStep { Done(i64), Next(HState) }\nfn h_run(mut state: HState) -> i64 { loop { let step = match state {\n");
    out.push_str(&dispatch);
    out.push_str("}; match step { HStep::Done(value) => return value, HStep::Next(next) => state = next } } }\n");
    for (index, leaf) in leaves.iter().enumerate() {
        let block = &leaf.function.blocks[0];
        let parameters = block
            .params
            .iter()
            .map(|p| format!("v{}: {}", p.id.0, carrier(&p.ty)))
            .collect::<Vec<_>>()
            .join(", ");
        for block in &leaf.function.blocks {
            let scalar_block = carrier(block_result(&leaf.function, block)) == "i64";
            let block_parameters = block
                .params
                .iter()
                .map(|p| format!("v{}: {}", p.id.0, carrier(&p.ty)))
                .collect::<Vec<_>>()
                .join(", ");
            if scalar_block {
                let args = block
                    .params
                    .iter()
                    .map(|p| format!("v{}", p.id.0))
                    .collect::<Vec<_>>()
                    .join(", ");
                writeln!(out, "fn b_{index}_{}({block_parameters}) -> i64 {{ h_run(HState::B_{index}_{}({args})) }}", block.id.0, block.id.0).unwrap();
            }
            writeln!(
                out,
                "    #[allow(unused_variables)]\n    fn {}_{index}_{}({block_parameters}) -> {} {{",
                if scalar_block { "s" } else { "b" },
                block.id.0,
                if scalar_block {
                    "HStep"
                } else {
                    carrier(block_result(&leaf.function, block))
                }
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
            let mut tail_transfer = false;
            for (position, instruction) in block.instructions.iter().enumerate() {
                if scalar_block
                    && position + 1 == block.instructions.len()
                    && matches!(block.terminator.exit, Exit::Return(v) if v == instruction.result.id)
                {
                    let destination = match &instruction.operation {
                        Operation::CallLocal { target, arguments }
                        | Operation::EvaluateBlock { target, arguments }
                        | Operation::LocalScope {
                            target, arguments, ..
                        } => Some((index, *target, arguments)),
                        Operation::CallTop {
                            module,
                            binder,
                            type_arguments,
                            dictionaries,
                            arguments,
                        } => {
                            let target = instance_of(
                                &specialization,
                                &reference_of(*module, *binder, type_arguments, dictionaries),
                            )?;
                            Some((target, leaves[target].function.entry, arguments))
                        }
                        _ => None,
                    };
                    if let Some((target_index, target, arguments)) = destination {
                        let target_block = leaves[target_index]
                            .function
                            .blocks
                            .iter()
                            .find(|block| block.id == target)
                            .expect("verified target");
                        if target_block.params.len() != arguments.len() {
                            return Err("tail transfer argument count mismatch".into());
                        }
                        let args = arguments
                            .iter()
                            .map(|v| value(*v))
                            .collect::<Vec<_>>()
                            .join(", ");
                        writeln!(
                            out,
                            "    HStep::Next(HState::B_{target_index}_{}({args}))",
                            target.0
                        )
                        .unwrap();
                        tail_transfer = true;
                        break;
                    }
                }
                let expression = match &instruction.operation {
                    Operation::MakeClosure { target, arguments } => {
                        let target_block = leaf
                            .function
                            .blocks
                            .iter()
                            .find(|b| b.id == *target)
                            .expect("verified closure target");
                        closure(
                            &format!("b_{index}_{}", target.0),
                            &arguments.iter().map(|v| value(*v)).collect::<Vec<_>>(),
                            &instruction.result.ty,
                            target_block.params.len() - arguments.len(),
                        )?
                    }
                    Operation::Apply { callee, arguments } => {
                        let args = arguments
                            .iter()
                            .map(|v| {
                                let ty = &block
                                    .params
                                    .iter()
                                    .chain(block.instructions.iter().map(|i| &i.result))
                                    .find(|p| p.id == *v)
                                    .expect("verified argument")
                                    .ty;
                                format!("HField::{}({})", field_kind(ty).0, value(*v))
                            })
                            .collect::<Vec<_>>()
                            .join(", ");
                        format!(
                            "v{}.apply(vec![{args}]).{}()",
                            callee.0,
                            field_kind(&instruction.result.ty).1
                        )
                    }
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
                                    "HClosure" => "Closure",
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
                                        "HClosure" => "closure",
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
                                " {pattern} => b_{index}_{}({}),",
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
                            "{{ {captures} {}::defer(move || b_{index}_{}({args}).force()) }}",
                            carrier(&instruction.result.ty),
                            target.0
                        )
                    }
                    Operation::BoxInt(v) => format!("HInt::ready(v{})", v.0),
                    Operation::UnboxInt(v) => format!("v{}.force()", v.0),
                    Operation::EvaluateBlock { target, arguments }
                    | Operation::CallLocal { target, arguments }
                    | Operation::LocalScope {
                        target, arguments, ..
                    } => {
                        let args = arguments
                            .iter()
                            .map(|v| value(*v))
                            .collect::<Vec<_>>()
                            .join(", ");
                        format!("b_{index}_{}({args})", target.0)
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
                    Operation::TopReference {
                        module,
                        binder,
                        type_arguments,
                        dictionaries,
                    } => {
                        let target = instance_of(
                            &specialization,
                            &reference_of(*module, *binder, type_arguments, dictionaries),
                        )?;
                        let arity = leaves[target].function.blocks[0].params.len();
                        if arity == 0 {
                            format!("f_{target}()")
                        } else {
                            closure(&format!("f_{target}"), &[], &instruction.result.ty, arity)?
                        }
                    }
                    Operation::CallTop {
                        module,
                        binder,
                        type_arguments,
                        dictionaries,
                        arguments,
                    } => {
                        let target = instance_of(
                            &specialization,
                            &reference_of(*module, *binder, type_arguments, dictionaries),
                        )?;
                        if leaves[target].function.blocks[0].params.len() != arguments.len() {
                            return Err("emitted target parameter count disagrees with call".into());
                        }
                        let args = arguments
                            .iter()
                            .map(|arg| value(*arg))
                            .collect::<Vec<_>>()
                            .join(", ");
                        format!("f_{target}({args})")
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
                    "b_{index}_{}({})",
                    target.0,
                    args.iter()
                        .map(|v| value(*v))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            };
            let transfer = |target: &crate::nir::BlockId, args: &[crate::nir::ValueId]| {
                if scalar_block {
                    format!(
                        "HStep::Next(HState::B_{index}_{}({}))",
                        target.0,
                        args.iter()
                            .map(|v| value(*v))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                } else {
                    call(target, args)
                }
            };
            if !tail_transfer {
                match &block.terminator.exit {
                    Exit::Return(v) => writeln!(
                        out,
                        "    {}",
                        if scalar_block {
                            format!("HStep::Done({})", value(*v))
                        } else {
                            value(*v)
                        }
                    )
                    .unwrap(),
                    Exit::Jump { target, args } => {
                        writeln!(out, "    {}", transfer(target, args)).unwrap()
                    }
                    Exit::IntSwitch {
                        scrutinee,
                        arms,
                        default,
                        args,
                    } => {
                        writeln!(out, "    match v{} {{", scrutinee.0).unwrap();
                        for (pattern, target) in arms {
                            writeln!(out, "        {pattern}i64 => {},", transfer(target, args))
                                .unwrap();
                        }
                        writeln!(out, "        _ => {},\n    }}", transfer(default, args)).unwrap();
                    }
                }
            }
            writeln!(out, "    }}").unwrap();
        }
        writeln!(
            out,
            "#[allow(unused_variables)]\nfn f_{index}({parameters}) -> {} {{",
            carrier(&leaf.function.result_ty)
        )
        .unwrap();
        let args = leaf.function.blocks[0]
            .params
            .iter()
            .map(|p| format!("v{}", p.id.0))
            .collect::<Vec<_>>()
            .join(", ");
        if carrier(&leaf.function.result_ty) != "i64" {
            let result_carrier = carrier(&leaf.function.result_ty);
            if block.params.is_empty() {
                writeln!(out, "    std::thread_local! {{ static VALUE: {result_carrier} = {result_carrier}::defer(|| b_{index}_{}().force()); }}\n    VALUE.with(Clone::clone)\n}}", leaf.function.entry.0).unwrap();
            } else {
                writeln!(
                    out,
                    "    {result_carrier}::defer(move || b_{index}_{}({args}).force())\n}}",
                    leaf.function.entry.0
                )
                .unwrap();
            }
        } else {
            writeln!(out, "    b_{index}_{}({args})\n}}", leaf.function.entry.0).unwrap();
        }
    }
    let arity = entry_types.len();
    let args = entry_types
        .iter()
        .enumerate()
        .map(|(i, p)| {
            if boxed::is_int(p) {
                format!("HInt::ready(args[{i}])")
            } else {
                format!("args[{i}]")
            }
        })
        .collect::<Vec<_>>()
        .join(", ");
    if direct_arity == arity {
        writeln!(out, "#[allow(unused_imports)]\nuse f_0 as h2r_entry;").unwrap();
    } else {
        let params = entry_types
            .iter()
            .enumerate()
            .map(|(n, t)| format!("a{n}: {}", carrier(t)))
            .collect::<Vec<_>>()
            .join(", ");
        let direct = (0..direct_arity)
            .map(|n| format!("a{n}"))
            .collect::<Vec<_>>()
            .join(", ");
        let extra = entry_types
            .iter()
            .enumerate()
            .skip(direct_arity)
            .map(|(n, t)| format!("HField::{}(a{n})", field_kind(t).0))
            .collect::<Vec<_>>()
            .join(", ");
        writeln!(
            out,
            "fn h2r_entry({params}) -> {} {{ f_0({direct}).apply(vec![{extra}]).{}() }}",
            carrier(entry_result),
            field_kind(entry_result).1
        )
        .unwrap();
    }
    let force = if boxed::is_int(entry_result) {
        ".force()"
    } else {
        ""
    };
    writeln!(out, "fn main() {{\n    let args: Vec<i64> = std::env::args().skip(1).map(|s| s.parse().expect(\"expected signed 64-bit integer\")).collect();\n    assert_eq!(args.len(), {arity}, \"wrong argument count\");\n    println!(\"{{}}\", h2r_entry({args}){force});\n}}").unwrap();
    Ok(out)
}
