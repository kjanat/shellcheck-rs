//! First executable backend: acyclic, monomorphic Int# entry points and their
//! complete dependency closure. Text I/O is an explicit generated CLI adapter,
//! not a translation of Haskell IO. Unsupported carriers/operations fail closed.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write;

use h2r_core_ir::{Module, Ty};

use crate::nir::{Exit, FnId, Operation, lower::lower_leaf_in_world};

type Key = (usize, u32);

fn scalar(ty: &Ty) -> bool {
    matches!(ty, Ty::Con { tycon, args } if tycon.name == "$ghc-prim$GHC.Prim$Int#" && args.is_empty())
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
            || !scalar(&function.result_ty)
            || function.blocks[0].params.iter().any(|p| !scalar(&p.ty))
        {
            return Err(format!(
                "module {module} binder {binder}: only monomorphic Int# functions can be emitted"
            ));
        }
        let mut dependencies = BTreeSet::new();
        for instruction in &function.blocks[0].instructions {
            if !scalar(&instruction.result.ty) {
                return Err("unsupported instruction carrier".into());
            }
            match &instruction.operation {
                Operation::Literal(lit) => {
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
    for ((module, binder), leaf) in &functions {
        let block = &leaf.function.blocks[0];
        let parameters = block
            .params
            .iter()
            .map(|p| format!("v{}: i64", p.id.0))
            .collect::<Vec<_>>()
            .join(", ");
        writeln!(
            out,
            "#[allow(unused_variables)]\nfn f_{module}_{binder}({parameters}) -> i64 {{"
        )
        .unwrap();
        for instruction in &block.instructions {
            let expression = match &instruction.operation {
                Operation::Literal(lit) => format!("{}i64", integer(&lit.kind, &lit.pretty)?),
                Operation::TopReference { module, binder } => {
                    if !functions[&(*module, *binder)].function.blocks[0]
                        .params
                        .is_empty()
                    {
                        return Err("function-valued reference cannot use the Int# carrier".into());
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
                        return Err("polymorphic calls need specialization before emission".into());
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
                        .map(|arg| format!("v{}", arg.0))
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!("f_{module}_{binder}({args})")
                }
                _ => return Err("unsupported operation in scalar Rust backend".into()),
            };
            writeln!(
                out,
                "    let v{}: i64 = {expression};",
                instruction.result.id.0
            )
            .unwrap();
        }
        let Exit::Return(value) = block.terminator.exit else {
            return Err("scalar backend requires a return".into());
        };
        writeln!(out, "    v{}\n}}", value.0).unwrap();
    }
    let arity = functions[root].function.blocks[0].params.len();
    let args = (0..arity)
        .map(|i| format!("args[{i}]"))
        .collect::<Vec<_>>()
        .join(", ");
    writeln!(out, "fn main() {{\n    let args: Vec<i64> = std::env::args().skip(1).map(|s| s.parse().expect(\"expected signed 64-bit integer\")).collect();\n    assert_eq!(args.len(), {arity}, \"wrong argument count\");\n    println!(\"{{}}\", f_{}_{}({args}));\n}}", root.0, root.1).unwrap();
    Ok(out)
}
