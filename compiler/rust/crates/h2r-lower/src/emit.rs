//! Monomorphic scalar/algebraic functions and their complete dependency
//! closure. Text I/O is an explicit integer-only generated CLI adapter,
//! not a translation of Haskell IO. Unsupported carriers/operations fail closed.
//!
//! Emission works on *instances*, not bindings: one polymorphic or
//! dictionary-taking source binding becomes one Rust function per instance the
//! program actually needs, named by its instance index. A call site names the
//! instance it resolved to, so nothing here re-derives a specialization.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write;

use h2r_core_ir::{Module, Ty};

use crate::nir::{
    Block, CharCompare, DictionaryRef, Exit, Function, IntBinary, ListOp, Operation, World, boxed,
    data,
    lower::LoweredLeaf,
    specialize::{self, Instance},
};

/// An unboxed scalar, or the boxed `Int` the CLI adapter also accepts.
fn scalar(world: &World<'_>, ty: &Ty) -> bool {
    let ty = represented(world, ty);
    boxed::is_int(&ty) || unboxed(&ty)
}

/// A newtype is carried as the type it wraps, so every carrier question below
/// is asked of the representation. A type whose representation cannot be
/// determined is left as it is; it has no carrier either way, and is refused
/// where that matters rather than guessed at here.
fn represented(world: &World<'_>, ty: &Ty) -> Ty {
    data::represented(world, ty).unwrap_or_else(|| ty.clone())
}

/// `Int#` and `Char#` both ride a machine word. Which one a value is stays in
/// its NIR type and in its runtime field tag; it is never inferred from the
/// carrier, which is why `field_kind` reads the type rather than the carrier.
fn unboxed(ty: &Ty) -> bool {
    matches!(ty, Ty::Con { tycon, args } if args.is_empty()
        && (tycon.name == "$ghc-prim$GHC.Prim$Int#"
            || tycon.name == "$ghc-prim$GHC.Prim$Char#"
            || tycon.name == "$ghc-prim$GHC.Prim$Word#"))
}

fn is_word(ty: &Ty) -> bool {
    matches!(ty, Ty::Con { tycon, args } if tycon.name == "$ghc-prim$GHC.Prim$Word#" && args.is_empty())
}

fn is_char(ty: &Ty) -> bool {
    matches!(ty, Ty::Con { tycon, args } if tycon.name == "$ghc-prim$GHC.Prim$Char#" && args.is_empty())
}

/// The Rust type a carrier is held in. The cases are `data::Carrier`'s, named
/// here rather than decided again: a value whose NIR type says one thing and
/// whose emitted type says another is a miscompile.
///
/// An unboxed tuple is the one composite: it has no representation of its own,
/// so its Rust type is built from its components' and nests as they do.
fn carrier(world: &World<'_>, ty: &Ty) -> String {
    let ty = represented(world, ty);
    if boxed::is_int(&ty) {
        "HInt".into()
    } else if unboxed(&ty) {
        "i64".into()
    } else if matches!(ty, Ty::Fun { .. }) {
        "HClosure".into()
    } else if let Ok(Some(fields)) = data::unboxed_tuple_fields(world, &ty) {
        let components: Vec<String> = fields.iter().map(|f| carrier(world, f)).collect();
        // Rust needs the trailing comma to tell a one-tuple from a
        // parenthesised type; GHC's `Solo#` is exactly that case.
        match components.as_slice() {
            [one] => format!("({one},)"),
            many => format!("({})", many.join(", ")),
        }
    } else {
        "HData".into()
    }
}

/// Whether the two agree. `carrier` answers structurally and calls anything
/// that is neither a scalar nor an arrow `HData`, which is a plausible answer
/// for a type that has no carrier at all; `data::carrier` consults the world's
/// constructor evidence and says so. Every emitted type is checked against
/// both, so a type that reached emission without a carrier is an error rather
/// than an `HData` that nothing can build.
fn carrier_agrees(world: &World<'_>, ty: &Ty) -> bool {
    match data::carrier(world, ty) {
        Some(data::Carrier::Scalar) => carrier(world, ty) == "i64",
        Some(data::Carrier::Int) => carrier(world, ty) == "HInt",
        Some(data::Carrier::Function) => carrier(world, ty) == "HClosure",
        Some(data::Carrier::Data) => carrier(world, ty) == "HData",
        Some(data::Carrier::Tuple) => carrier(world, ty).starts_with('('),
        None => true,
    }
}

fn field_kind(world: &World<'_>, ty: &Ty) -> (&'static str, &'static str) {
    if is_char(&represented(world, ty)) {
        return ("Char", "char_code");
    }
    match carrier(world, ty).as_str() {
        "i64" => ("Int64", "int64"),
        "HInt" => ("Int", "int"),
        "HClosure" => ("Closure", "closure"),
        _ => ("Data", "data"),
    }
}

fn closure(
    world: &World<'_>,
    target: &str,
    entry: Option<&str>,
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
        .map(|(n, v)| format!("let c{n} = {v}; let e{n} = c{n}.clone();"))
        .collect::<Vec<_>>()
        .join(" ");
    let mut args = Vec::new();
    let mut result = signature;
    for n in 0..arity {
        let Ty::Fun { arg, res, .. } = result else {
            return Err("closure code arity exceeds signature".into());
        };
        args.push(format!("a[{n}].{}()", field_kind(world, arg).1));
        result = res;
    }
    let with = |prefix: char| {
        (0..captures.len())
            .map(|n| format!("{prefix}{n}.clone()"))
            .chain(args.iter().cloned())
            .collect::<Vec<_>>()
            .join(", ")
    };
    let code = format!(
        "move |a| HField::{}({target}({}))",
        field_kind(world, result).0,
        with('c')
    );
    Ok(match entry {
        Some(state) => format!(
            "{{ {bindings} HClosure::entering({arity}, {code}, move |a| Box::new({state}({})) as Box<dyn std::any::Any>) }}",
            with('e')
        ),
        None => format!("{{ {bindings} HClosure::ready({arity}, {code}) }}"),
    })
}

fn match_data(
    world: &World<'_>,
    scrutinee: crate::nir::ValueId,
    captures: &[String],
    arms: &[crate::nir::DataArm],
    enter: impl Fn(crate::nir::BlockId, String) -> String,
) -> String {
    let mut code = format!(
        "{{ let node = v{}.force(); let constructor = node.constructor; match constructor {{",
        scrutinee.0
    );
    // DEFAULT may be first in Core; Rust's wildcard must be last.
    for arm in arms
        .iter()
        .filter(|a| a.constructor.is_some())
        .chain(arms.iter().filter(|a| a.constructor.is_none()))
    {
        let mut args = captures.to_vec();
        let pattern = if let Some(c) = &arm.constructor {
            for (i, t) in c.fields.iter().enumerate() {
                args.push(format!("node.fields[{i}].{}()", field_kind(world, t).1));
            }
            format!("{:?}", c.name)
        } else {
            "_".into()
        };
        write!(
            code,
            " {pattern} => {},",
            enter(arm.target, args.join(", "))
        )
        .unwrap();
    }
    if arms.iter().all(|a| a.constructor.is_some()) {
        code.push_str(" _ => panic!(\"invalid constructor family\"),");
    }
    code.push_str(" } }");
    code
}

fn successors(block: &Block) -> Vec<crate::nir::BlockId> {
    let mut out = Vec::new();
    match &block.terminator.exit {
        Exit::Jump { target, .. } => out.push(*target),
        Exit::IntSwitch { arms, default, .. } => {
            out.extend(arms.iter().map(|(_, target)| *target));
            out.push(*default);
        }
        Exit::Return(_) | Exit::Diverge { .. } => {}
    }
    for instruction in &block.instructions {
        match &instruction.operation {
            Operation::MatchData { arms, .. } => out.extend(arms.iter().map(|arm| arm.target)),
            Operation::LocalScope {
                definitions,
                target,
                ..
            } => {
                out.extend(definitions.iter().map(|definition| definition.target));
                out.push(*target);
            }
            Operation::CallLocal { target, .. }
            | Operation::EvaluateBlock { target, .. }
            | Operation::MakeClosure { target, .. }
            | Operation::DelayBlock { target, .. } => out.push(*target),
            _ => {}
        }
    }
    out
}

type Successors = BTreeMap<crate::nir::BlockId, Vec<crate::nir::BlockId>>;

fn reaches(graph: &Successors, from: crate::nir::BlockId, to: crate::nir::BlockId) -> bool {
    let mut seen = BTreeSet::new();
    let mut pending = vec![from];
    while let Some(block) = pending.pop() {
        if block == to {
            return true;
        }
        if seen.insert(block)
            && let Some(next) = graph.get(&block)
        {
            pending.extend(next.iter().copied());
        }
    }
    false
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
        // A dead end returns nothing, so its type is the one the exit was
        // built against rather than one read off a successor.
        Exit::Diverge { ty, .. } => return ty,
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

/// The machine word an unboxed literal denotes: the number itself for `Int#`,
/// the code point for `Char#`. Read from the dump's exact value, never from
/// GHC's rendering, which escapes.
fn scalar_literal(world: &World<'_>, ty: &Ty, lit: &h2r_core_ir::Lit) -> Result<i64, String> {
    if is_char(&represented(world, ty)) {
        let codepoint = lit.char_codepoint()?;
        char::from_u32(codepoint).ok_or("Char# literal is not a Unicode code point")?;
        return Ok(i64::from(codepoint));
    }
    if is_word(&represented(world, ty)) {
        return u64::try_from(lit.number("Word")?)
            .map(u64::cast_signed)
            .map_err(|error| {
                format!("Word# literal does not fit an unsigned 64-bit word: {error}")
            });
    }
    i64::try_from(lit.number("Int")?)
        .map_err(|error| format!("Int# literal does not fit a signed 64-bit word: {error}"))
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

fn dependencies(
    world: &World<'_>,
    specialization: &specialize::Specialization,
    index: usize,
    leaf: &LoweredLeaf,
) -> Result<BTreeSet<usize>, String> {
    let supported = |ty: &Ty| data::supported(world, ty);
    let function = &leaf.function;
    for block in &function.blocks {
        if let Exit::Diverge { name, .. } = &block.terminator.exit {
            return Err(format!(
                "unimplemented non-returning call: {name}; demand evidence does not specify its runtime behavior"
            ));
        }
    }
    let instance = &specialization.instances[index];
    if !function.type_params.is_empty() {
        return Err(format!(
            "module {} binder {}: emission requires a monomorphic instance",
            instance.module, instance.binder
        ));
    }
    if let Some(ty) = std::iter::once(&function.result_ty)
        .chain(
            function
                .blocks
                .iter()
                .flat_map(|b| &b.params)
                .map(|p| &p.ty),
        )
        .find(|ty| !supported(ty))
    {
        return Err(format!(
            "module {} binder {}: emission requires a carrier for {}",
            instance.module,
            instance.binder,
            label(uncarried(world, ty))
        ));
    }
    let mut dependencies = BTreeSet::new();
    for instruction in function.blocks.iter().flat_map(|b| &b.instructions) {
        if !supported(&instruction.result.ty) {
            return Err(format!(
                "unsupported instruction carrier: {}",
                label(uncarried(world, &instruction.result.ty))
            ));
        }
        if !carrier_agrees(world, &instruction.result.ty) {
            return Err("an emitted carrier disagrees with the NIR's".into());
        }
        match &instruction.operation {
            Operation::Construct { .. }
            | Operation::MatchData { .. }
            | Operation::IntBinary { .. }
            | Operation::Move(_)
            | Operation::BoxInt(_)
            | Operation::UnboxInt(_)
            | Operation::CharCompare { .. }
            | Operation::WordCompare { .. }
            | Operation::IntToWord(_)
            | Operation::OrdChar(_)
            | Operation::ChrChar(_)
            | Operation::UnpackString(_)
            | Operation::AppendList { .. }
            | Operation::ListPredicate(_)
            | Operation::ListFunction(_)
            | Operation::CompareStrings(_)
            | Operation::DataToTag { .. }
            | Operation::TagToEnum { .. }
            | Operation::PointerEquality { .. }
            | Operation::RaiseError { .. }
            | Operation::RaiseCallStackError(_)
            | Operation::EmptyCase { .. }
            | Operation::DelayBlock { .. }
            | Operation::MakeUnboxedTuple { .. }
            | Operation::UnboxedTupleField { .. }
            | Operation::EvaluateBlock { .. } => {}
            Operation::CallLocal { .. }
            | Operation::LocalScope { .. }
            | Operation::MakeClosure { .. }
            | Operation::Apply { .. } => {}
            Operation::Literal(lit) => {
                if carrier(world, &instruction.result.ty) != "i64" {
                    return Err("boxed Int requires constructor evidence, not a literal".into());
                }
                scalar_literal(world, &instruction.result.ty, lit)?;
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
                    specialization,
                    &reference_of(*module, *binder, type_arguments, dictionaries),
                )?);
            }
            Operation::Force(_) => {
                return Err("unsupported operation in scalar Rust backend".into());
            }
        }
    }
    Ok(dependencies)
}

fn uncarried<'a>(world: &World<'_>, ty: &'a Ty) -> &'a Ty {
    let parts: Vec<&Ty> = match ty {
        Ty::Fun { arg, res, .. } => vec![arg, res],
        Ty::Con { args, .. } => args.iter().collect(),
        Ty::App { fun, arg } => vec![fun, arg],
        _ => Vec::new(),
    };
    parts
        .into_iter()
        .find(|part| !data::supported(world, part))
        .map_or(ty, |part| uncarried(world, part))
}

fn label(ty: &Ty) -> String {
    match ty {
        Ty::Con { tycon, .. } => tycon.name.clone(),
        Ty::Var(_) => "a type variable".into(),
        Ty::ForAll { .. } => "a polymorphic type".into(),
        other => other.render(),
    }
}

fn recursive_value(
    leaves: &BTreeMap<usize, &LoweredLeaf>,
    edges: &BTreeMap<usize, BTreeSet<usize>>,
    index: usize,
) -> bool {
    if !leaves[&index].function.blocks[0].params.is_empty() {
        return false;
    }
    let mut seen = BTreeSet::new();
    let mut pending: Vec<_> = edges[&index].iter().copied().collect();
    while let Some(next) = pending.pop() {
        if next == index {
            return true;
        }
        if seen.insert(next) {
            pending.extend(edges[&next].iter().copied());
        }
    }
    false
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
    let world = &evidence;
    let leaves: BTreeMap<usize, &LoweredLeaf> = specialization
        .lowered
        .iter()
        .map(|leaf| {
            leaf.as_ref()
                .expect("a complete specialization lowers every instance")
        })
        .enumerate()
        .collect();
    let mut edges = BTreeMap::new();
    for (&index, leaf) in &leaves {
        edges.insert(index, dependencies(world, &specialization, index, leaf)?);
    }
    let entry_function = &leaves[&0].function;
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
    let inputs = entry_types
        .iter()
        .enumerate()
        .map(|(i, ty)| argument(world, ty, i))
        .collect::<Result<Vec<_>, _>>()?;
    let mut shows = Shows::default();
    let rendered = if scalar(world, entry_result) {
        None
    } else {
        Some(show_function(world, entry_result, &mut shows)?)
    };
    // Refuse cycles involving a value, even through a function. Only function
    // recursion is supported here, not productive recursive thunk graphs.
    if leaves
        .keys()
        .any(|&index| recursive_value(&leaves, &edges, index))
    {
        return Err("recursive value dependency closure is not supported".into());
    }
    let mut out = functions(world, &specialization, &leaves, None)?;
    let arity = entry_types.len();
    let args = inputs.join(", ");
    if direct_arity == arity {
        writeln!(out, "#[allow(unused_imports)]\nuse f_0 as h2r_entry;").unwrap();
    } else {
        let params = entry_types
            .iter()
            .enumerate()
            .map(|(n, t)| format!("a{n}: {}", carrier(world, t)))
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
            .map(|(n, t)| format!("HField::{}(a{n})", field_kind(world, t).0))
            .collect::<Vec<_>>()
            .join(", ");
        writeln!(
            out,
            "fn h2r_entry({params}) -> {} {{ f_0({direct}).apply(vec![{extra}]).{}() }}",
            carrier(world, entry_result),
            field_kind(world, entry_result).1
        )
        .unwrap();
    }
    let result = match &rendered {
        Some(show) => format!(
            "{show}(&HField::{}(h2r_entry({args})), 0)",
            field_kind(world, entry_result).0
        ),
        None if boxed::is_int(entry_result) => format!("h2r_entry({args}).force()"),
        None => format!("h2r_entry({args})"),
    };
    for function in &shows.functions {
        out.push_str(function);
    }
    writeln!(out, "fn main() {{\n    let raw: Vec<String> = std::env::args().skip(1).collect();\n    assert_eq!(raw.len(), {arity}, \"wrong argument count\");\n    h2r_on_program_stack(move || println!(\"{{}}\", {result}));\n}}").unwrap();
    out.push_str(PROGRAM_STACK);
    Ok(out)
}

const PROGRAM_CHUNK: usize = 64;

// GHC's default maximum stack is 80% of physical memory.
const PROGRAM_STACK: &str = r#"fn h2r_on_program_stack(run: impl FnOnce() + Send + 'static) {
    let memory = std::fs::read_to_string("/proc/meminfo")
        .ok()
        .and_then(|text| {
            text.lines()
                .find_map(|line| line.strip_prefix("MemTotal:"))
                .and_then(|kib| kib.trim().trim_end_matches("kB").trim().parse::<u64>().ok())
        })
        .map_or(1 << 30, |kib| kib / 5 * 4 * 1024);
    let run = std::sync::Arc::new(std::sync::Mutex::new(Some(run)));
    let mut size = memory;
    loop {
        let task = run.clone();
        let started = std::thread::Builder::new()
            .stack_size(usize::try_from(size).unwrap_or(usize::MAX))
            .spawn(move || {
                let run = task.lock().expect("program lock").take().expect("program runs once");
                run()
            });
        match started {
            Ok(thread) => {
                if let Err(panic) = thread.join() {
                    std::panic::resume_unwind(panic);
                }
                return;
            }
            Err(_) if size > 64 << 20 => size /= 2,
            Err(error) => panic!("cannot start the program's thread: {error}"),
        }
    }
}
"#;

pub struct Program {
    pub source: String,
    pub instances: usize,
    pub lowered: usize,
    pub emittable: usize,
    pub emitted: usize,
    pub recursive_values: usize,
    pub roots: Vec<RootOutcome>,
    pub refusals: BTreeMap<String, usize>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RootOutcome {
    Emitted,
    NotLowered,
    Refused(String),
    DependencyRefused,
}

pub fn emit_program(modules: &[Module], roots: &[Instance]) -> Result<Program, String> {
    let specialization = specialize::survey(modules, roots);
    let evidence = crate::nir::World::of(modules, 0)?;
    let world = &evidence;
    let mut edges = BTreeMap::new();
    let mut refusals = BTreeMap::new();
    let mut refused = BTreeMap::new();
    for (index, leaf) in specialization.lowered.iter().enumerate() {
        let Some(leaf) = leaf else {
            continue;
        };
        match dependencies(world, &specialization, index, leaf) {
            Ok(dependencies) => {
                edges.insert(index, dependencies);
            }
            Err(reason) => {
                let reason = match reason.split_once(": emission requires ") {
                    Some((_, tail)) if reason.starts_with("module ") => {
                        format!("emission requires {tail}")
                    }
                    _ => reason,
                };
                *refusals.entry(reason.clone()).or_insert(0) += 1;
                refused.insert(index, reason);
            }
        }
    }
    let emittable = edges.len();
    let mut members: BTreeSet<usize> = edges.keys().copied().collect();
    let mut recursive_values = 0;
    loop {
        loop {
            let open: Vec<usize> = members
                .iter()
                .copied()
                .filter(|index| !edges[index].iter().all(|d| members.contains(d)))
                .collect();
            if open.is_empty() {
                break;
            }
            for index in open {
                members.remove(&index);
            }
        }
        let leaves: BTreeMap<usize, &LoweredLeaf> = members
            .iter()
            .map(|&index| {
                (
                    index,
                    specialization.lowered[index].as_ref().expect("lowered"),
                )
            })
            .collect();
        let closed: BTreeMap<usize, BTreeSet<usize>> = members
            .iter()
            .map(|&index| (index, edges[&index].clone()))
            .collect();
        let cyclic: Vec<usize> = members
            .iter()
            .copied()
            .filter(|&index| recursive_value(&leaves, &closed, index))
            .collect();
        if cyclic.is_empty() {
            break;
        }
        recursive_values += cyclic.len();
        for index in cyclic {
            members.remove(&index);
        }
    }
    let leaves: BTreeMap<usize, &LoweredLeaf> = members
        .iter()
        .map(|&index| {
            (
                index,
                specialization.lowered[index].as_ref().expect("lowered"),
            )
        })
        .collect();
    let mut source = functions(world, &specialization, &leaves, Some(PROGRAM_CHUNK))?;
    let addresses: Vec<String> = members
        .iter()
        .map(|index| format!("f_{index} as *const ()"))
        .collect();
    writeln!(
        source,
        "fn main() {{\n    std::hint::black_box([{}]);\n}}",
        addresses.join(", ")
    )
    .unwrap();
    let outcomes = roots
        .iter()
        .map(|root| {
            let index = specialization.resolve(&reference_of(
                root.module,
                root.binder,
                &root.type_arguments,
                &root.dictionaries,
            ));
            match index {
                Some(index) if members.contains(&index) => RootOutcome::Emitted,
                Some(index) if specialization.leaf(index).is_none() => RootOutcome::NotLowered,
                None => RootOutcome::NotLowered,
                Some(index) => refused
                    .get(&index)
                    .map_or(RootOutcome::DependencyRefused, |reason| {
                        RootOutcome::Refused(reason.clone())
                    }),
            }
        })
        .collect();
    Ok(Program {
        source,
        instances: specialization.lowered_count() + specialization.refused.len(),
        lowered: specialization.lowered_count(),
        emittable,
        emitted: members.len(),
        recursive_values,
        roots: outcomes,
        refusals,
    })
}

fn functions(
    world: &World<'_>,
    specialization: &specialize::Specialization,
    leaves: &BTreeMap<usize, &LoweredLeaf>,
    chunk: Option<usize>,
) -> Result<String, String> {
    let vis = if chunk.is_some() { "pub(crate) " } else { "" };
    let mut chunks = 0;
    // rustc counts nested instantiations of one generic against `recursion_limit`, default 128.
    let shim_sites = 2 * leaves.len()
        + leaves
            .values()
            .flat_map(|leaf| &leaf.function.blocks)
            .map(|block| block.instructions.len())
            .sum::<usize>();
    let mut out = if shim_sites > 128 {
        format!("#![recursion_limit = \"{shim_sites}\"]\n")
    } else {
        String::new()
    };
    out.push_str(
        "// Generated from source-verified scalar NIR. CLI I/O is an adapter.\n#[cfg(not(target_pointer_width = \"64\"))]\ncompile_error!(\"Int# backend requires a 64-bit target\");\n",
    );
    let has_boxed = leaves.values().any(|leaf| {
        carrier(world, &leaf.function.result_ty) != "i64"
            || leaf.function.blocks.iter().any(|b| {
                b.params
                    .iter()
                    .chain(b.instructions.iter().map(|i| &i.result))
                    .any(|v| carrier(world, &v.ty) != "i64")
            })
    });
    if has_boxed {
        out.push_str("\n#[allow(dead_code)]\nmod h2r_rt {\n");
        out.push_str(include_str!("../../h2r-rt/src/lib.rs"));
        out.push_str("\n}\n#[allow(unused_imports)]\nuse h2r_rt::Int as HInt;\n#[allow(unused_imports)]\nuse h2r_rt::{Data as HData, Field as HField, Closure as HClosure};\n#[allow(unused_imports)]\nuse h2r_rt::{Encoding as HEncoding, ListNames as HListNames, StringNames as HStringNames};\n");
    }
    let unlifted = |function: &Function, block: &Block| {
        let ty = block_result(function, block);
        (!data::lifted(world, ty)).then(|| carrier(world, ty))
    };
    let mut suffixes: BTreeMap<String, String> = BTreeMap::new();
    for leaf in leaves.values() {
        for block in &leaf.function.blocks {
            if let Some(result) = unlifted(&leaf.function, block) {
                let next = suffixes.len();
                suffixes.entry(result.clone()).or_insert_with(|| {
                    if result == "i64" {
                        String::new()
                    } else {
                        format!("_{next}")
                    }
                });
            }
        }
    }
    let dispatcher = |function: &Function, block: &Block| {
        unlifted(function, block).map(|result| suffixes[&result].as_str())
    };
    for (result, suffix) in &suffixes {
        let mut states = String::new();
        let mut dispatch = String::new();
        for (&index, leaf) in leaves {
            for block in &leaf.function.blocks {
                if dispatcher(&leaf.function, block) != Some(suffix.as_str()) {
                    continue;
                }
                let types = block
                    .params
                    .iter()
                    .map(|p| carrier(world, &p.ty))
                    .collect::<Vec<_>>()
                    .join(", ");
                let args = block
                    .params
                    .iter()
                    .map(|p| format!("v{}", p.id.0))
                    .collect::<Vec<_>>()
                    .join(", ");
                writeln!(states, "B_{index}_{}({types}),", block.id.0).unwrap();
                writeln!(
                    dispatch,
                    "HState{suffix}::B_{index}_{}({args}) => s_{index}_{}({args}),",
                    block.id.0, block.id.0
                )
                .unwrap();
            }
        }
        let applies = suffix.is_empty() && has_boxed;
        writeln!(
            out,
            "#[allow(non_camel_case_types)]\nenum HState{suffix} {{\n{states}}}\nenum HStep{suffix} {{ Done({result}), Next(HState{suffix}){} }}\nfn h_run{suffix}(mut state: HState{suffix}) -> {result} {{ loop {{ let step = match state {{\n{dispatch}}}; match step {{ HStep{suffix}::Done(value) => return value, HStep{suffix}::Next(next) => state = next{} }} }} }}",
            if applies {
                ", Apply(HClosure, Vec<HField>, fn(&HField) -> i64)"
            } else {
                ""
            },
            if applies {
                ", HStep::Apply(function, arguments, read) => match function.apply_tail(arguments) { h2r_rt::Tail::Enter(next) => state = *next.downcast::<HState>().expect(\"a closure entry is a dispatcher state\"), h2r_rt::Tail::Value(value) => return read(&value) }"
            } else {
                ""
            }
        )
        .unwrap();
    }
    for (position, (&index, leaf)) in leaves.iter().enumerate() {
        if let Some(size) = chunk
            && position % size == 0
        {
            if chunks != 0 {
                out.push_str("}\n");
            }
            writeln!(out, "mod h_chunk_{chunks} {{\nuse super::*;").unwrap();
            chunks += 1;
        }
        let block = &leaf.function.blocks[0];
        let parameters = block
            .params
            .iter()
            .map(|p| format!("v{}: {}", p.id.0, carrier(world, &p.ty)))
            .collect::<Vec<_>>()
            .join(", ");
        let graph: Successors = leaf
            .function
            .blocks
            .iter()
            .map(|block| (block.id, successors(block)))
            .collect();
        for block in &leaf.function.blocks {
            let result = carrier(world, block_result(&leaf.function, block));
            let suffix = dispatcher(&leaf.function, block);
            let looping =
                |target: crate::nir::BlockId| suffix.is_none() && reaches(&graph, target, block.id);
            let block_parameters = block
                .params
                .iter()
                .map(|p| format!("v{}: {}", p.id.0, carrier(world, &p.ty)))
                .collect::<Vec<_>>()
                .join(", ");
            if let Some(suffix) = suffix {
                let args = block
                    .params
                    .iter()
                    .map(|p| format!("v{}", p.id.0))
                    .collect::<Vec<_>>()
                    .join(", ");
                writeln!(out, "{vis}fn b_{index}_{}({block_parameters}) -> {result} {{ h_run{suffix}(HState{suffix}::B_{index}_{}({args})) }}", block.id.0, block.id.0).unwrap();
            }
            writeln!(
                out,
                "    #[allow(unused_variables)]\n    {vis}fn {}_{index}_{}({block_parameters}) -> {} {{",
                if suffix.is_some() { "s" } else { "b" },
                block.id.0,
                match suffix {
                    Some(suffix) => format!("HStep{suffix}"),
                    None => result.clone(),
                }
            )
            .unwrap();
            let value_ty = |id: crate::nir::ValueId| {
                &block
                    .params
                    .iter()
                    .chain(block.instructions.iter().map(|i| &i.result))
                    .find(|v| v.id == id)
                    .expect("verified operand")
                    .ty
            };
            let value = |id: crate::nir::ValueId| {
                let ty = value_ty(id);
                if carrier(world, ty) != "i64" {
                    format!("v{}.clone()", id.0)
                } else {
                    format!("v{}", id.0)
                }
            };
            let mut tail_transfer = false;
            for (position, instruction) in block.instructions.iter().enumerate() {
                if position + 1 == block.instructions.len()
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
                                specialization,
                                &reference_of(*module, *binder, type_arguments, dictionaries),
                            )?;
                            Some((target, leaves[&target].function.entry, arguments))
                        }
                        _ => None,
                    };
                    let applied =
                        |callee: &crate::nir::ValueId, arguments: &[crate::nir::ValueId]| {
                            let args = arguments
                                .iter()
                                .map(|v| {
                                    format!(
                                        "HField::{}({})",
                                        field_kind(world, value_ty(*v)).0,
                                        value(*v)
                                    )
                                })
                                .collect::<Vec<_>>()
                                .join(", ");
                            (
                                format!("v{}", callee.0),
                                args,
                                field_kind(world, &instruction.result.ty).1,
                            )
                        };
                    let code = match (suffix, destination, &instruction.operation) {
                        (Some(suffix), Some((target_index, target, arguments)), _) => {
                            let target_block = leaves[&target_index]
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
                            Some(format!(
                                "HStep{suffix}::Next(HState{suffix}::B_{target_index}_{}({args}))",
                                target.0
                            ))
                        }
                        (None, Some((target_index, target, arguments)), _)
                            if target_index == index && looping(target) =>
                        {
                            let args = arguments
                                .iter()
                                .map(|v| value(*v))
                                .collect::<Vec<_>>()
                                .join(", ");
                            Some(format!(
                                "{result}::defer_to(move || b_{index}_{}({args}))",
                                target.0
                            ))
                        }
                        (
                            _,
                            _,
                            Operation::MatchData {
                                scrutinee,
                                arguments,
                                arms,
                            },
                        ) if suffix.is_some() || arms.iter().any(|arm| looping(arm.target)) => {
                            let captures = arguments
                                .iter()
                                .map(|v| value(*v))
                                .chain(std::iter::once(value(*scrutinee)))
                                .collect::<Vec<_>>();
                            Some(match_data(
                                world,
                                *scrutinee,
                                &captures,
                                arms,
                                |target, args| match suffix {
                                    Some(suffix) => format!(
                                        "HStep{suffix}::Next(HState{suffix}::B_{index}_{}({args}))",
                                        target.0
                                    ),
                                    None if looping(target) => format!(
                                        "{result}::defer_to(move || b_{index}_{}({args}))",
                                        target.0
                                    ),
                                    None => format!("b_{index}_{}({args})", target.0),
                                },
                            ))
                        }
                        (Some(""), _, Operation::Apply { callee, arguments }) if has_boxed => {
                            let (callee, args, read) = applied(callee, arguments);
                            Some(format!(
                                "HStep::Apply({callee}, vec![{args}], HField::{read})"
                            ))
                        }
                        (None, _, Operation::Apply { callee, arguments }) => {
                            let (callee, args, read) = applied(callee, arguments);
                            Some(format!(
                                "{result}::defer_to(move || {callee}.apply(vec![{args}]).{read}())"
                            ))
                        }
                        _ => None,
                    };
                    if let Some(code) = code {
                        writeln!(out, "    {code}").unwrap();
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
                            world,
                            &format!("b_{index}_{}", target.0),
                            (dispatcher(&leaf.function, target_block) == Some("") && has_boxed)
                                .then(|| format!("HState::B_{index}_{}", target.0))
                                .as_deref(),
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
                                format!("HField::{}({})", field_kind(world, ty).0, value(*v))
                            })
                            .collect::<Vec<_>>()
                            .join(", ");
                        format!(
                            "v{}.apply(vec![{args}]).{}()",
                            callee.0,
                            field_kind(world, &instruction.result.ty).1
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
                                format!("HField::{}({})", field_kind(world, t).0, value(*v))
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
                        match_data(world, *scrutinee, &captures, arms, |target, args| {
                            format!("b_{index}_{}({args})", target.0)
                        })
                    }
                    // No allocation and no tag: a Rust tuple is exactly what
                    // GHC's unboxed tuple is.
                    Operation::MakeUnboxedTuple { arguments } => {
                        let components: Vec<String> = arguments.iter().map(|v| value(*v)).collect();
                        match components.as_slice() {
                            [one] => format!("({one},)"),
                            many => format!("({})", many.join(", ")),
                        }
                    }
                    Operation::UnboxedTupleField { tuple, index } => {
                        format!("{}.{index}", value(*tuple))
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
                            "{{ {captures} {}::defer_to(move || b_{index}_{}({args})) }}",
                            carrier(world, &instruction.result.ty),
                            target.0
                        )
                    }
                    Operation::RaiseError { message } => {
                        let (nil, cons, character) = data::string_layouts(world)?;
                        format!(
                            "h2r_rt::raise_error({}, HStringNames {{ nil: {:?}, cons: {:?}, character: {:?} }})",
                            value(*message),
                            nil.name,
                            cons.name,
                            character.name
                        )
                    }
                    Operation::RaiseCallStackError(error) => {
                        let (nil, cons, character) = data::string_layouts(world)?;
                        format!(
                            "h2r_rt::raise_call_stack_error({}, {}, HStringNames {{ nil: {:?}, cons: {:?}, character: {:?} }}, h2r_rt::CallStackNames {{ empty: {:?}, push: {:?}, freeze: {:?}, location: {:?} }})",
                            value(error.message),
                            value(error.stack),
                            nil.name,
                            cons.name,
                            character.name,
                            error.layouts.empty.name,
                            error.layouts.push.name,
                            error.layouts.freeze.name,
                            error.layouts.location.name
                        )
                    }
                    Operation::EmptyCase { scrutinee } => {
                        let force = if data::lifted(world, value_ty(*scrutinee)) {
                            ".force()"
                        } else {
                            ""
                        };
                        format!(
                            "{{ let _ = {}{force}; unreachable!(\"non-returning scrutinee returned\") }}",
                            value(*scrutinee)
                        )
                    }
                    Operation::AppendList {
                        left,
                        right,
                        nil,
                        cons,
                    } => format!(
                        "h2r_rt::append_list({}, {}, HListNames {{ cons: {:?}, nil: {:?} }})",
                        value(*left),
                        value(*right),
                        cons.name,
                        nil.name
                    ),
                    Operation::DataToTag {
                        value: operand,
                        constructors,
                    } => {
                        let arms: String = constructors
                            .iter()
                            .map(|c| format!("{:?} => {}, ", c.name, i64::from(c.tag) - 1))
                            .collect();
                        format!(
                            "{{ let node = {}.force(); match node.constructor {{ {arms}other => panic!(\"dataToTag#: {{other}} is not in the family\") }} }}",
                            value(*operand)
                        )
                    }
                    Operation::TagToEnum { tag, constructors } => {
                        let arms: String = constructors
                            .iter()
                            .map(|c| {
                                format!(
                                    "{} => HData::ready({:?}, vec![]), ",
                                    i64::from(c.tag) - 1,
                                    c.name
                                )
                            })
                            .collect();
                        format!(
                            "match {} {{ {arms}other => panic!(\"tagToEnum#: {{other}} is not a tag of this family\") }}",
                            value(*tag)
                        )
                    }
                    Operation::PointerEquality { left, right } => format!(
                        "i64::from({}.shares_with(&{}))",
                        value(*left),
                        value(*right)
                    ),
                    Operation::CompareStrings(compare) => format!(
                        "h2r_rt::compare_lists({}, {}, HStringNames {{ cons: {:?}, nil: {:?}, character: {:?} }}, h2r_rt::Orderings {{ lt: {:?}, eq: {:?}, gt: {:?} }})",
                        value(compare.left),
                        value(compare.right),
                        compare.cons.name,
                        compare.nil.name,
                        compare.character.name,
                        compare.lt.name,
                        compare.eq.name,
                        compare.gt.name
                    ),
                    Operation::ListPredicate(predicate) => format!(
                        "h2r_rt::{}({}, {}, h2r_rt::Equality::{:?}, HStringNames {{ cons: {:?}, nil: {:?}, character: {:?} }}, h2r_rt::Truth {{ false_: {:?}, true_: {:?} }})",
                        match predicate.predicate {
                            crate::nir::Predicate::EqString => "equal_lists",
                            crate::nir::Predicate::Elem => "elem_list",
                            crate::nir::Predicate::IsPrefixOf => "is_prefix_of",
                        },
                        value(predicate.left),
                        value(predicate.right),
                        predicate.equality,
                        predicate.cons.name,
                        predicate.nil.name,
                        predicate.character.name,
                        predicate.false_.name,
                        predicate.true_.name
                    ),
                    Operation::ListFunction(list) => {
                        let names = |nil: &data::Constructor, cons: &data::Constructor| {
                            format!(
                                "HListNames {{ cons: {:?}, nil: {:?} }}",
                                cons.name, nil.name
                            )
                        };
                        let input = names(&list.nil, &list.cons);
                        let truth = list
                            .truth
                            .as_ref()
                            .map(|(false_, true_)| {
                                format!(
                                    "h2r_rt::Truth {{ false_: {:?}, true_: {:?} }}",
                                    false_.name, true_.name
                                )
                            })
                            .ok_or("a list function without a predicate's Bool");
                        let a: Vec<String> = list.arguments.iter().map(|v| value(*v)).collect();
                        match list.function {
                            ListOp::Map => {
                                let (nil, cons) =
                                    list.mapped.as_ref().ok_or("map without its result cells")?;
                                let element = match field_kind(world, &cons.fields[0]).0 {
                                    kind @ ("Int" | "Data" | "Closure") => kind,
                                    other => {
                                        return Err(format!(
                                            "map's element carrier {other} is not lifted"
                                        ));
                                    }
                                };
                                format!(
                                    "h2r_rt::map_list({}, {}, h2r_rt::Lifted::{element}, {input}, {})",
                                    a[0],
                                    a[1],
                                    names(nil, cons)
                                )
                            }
                            ListOp::Filter => {
                                format!(
                                    "h2r_rt::filter_list({}, {}, {input}, {})",
                                    a[0], a[1], truth?
                                )
                            }
                            ListOp::TakeWhile => {
                                format!(
                                    "h2r_rt::take_while({}, {}, {input}, {})",
                                    a[0], a[1], truth?
                                )
                            }
                            ListOp::DropWhile => {
                                format!(
                                    "h2r_rt::drop_while({}, {}, {input}, {})",
                                    a[0], a[1], truth?
                                )
                            }
                            ListOp::Reverse => format!("h2r_rt::reverse_list({}, {input})", a[0]),
                            ListOp::ReverseOnto => {
                                format!("h2r_rt::reverse_onto({}, {}, {input})", a[0], a[1])
                            }
                            ListOp::Length => {
                                format!("h2r_rt::length_from({}, {}, {input})", a[0], a[1])
                            }
                            ListOp::ConsAppend => format!(
                                "h2r_rt::cons_append(HField::{}({}), {}, {}, {input})",
                                field_kind(world, value_ty(list.arguments[0])).0,
                                a[0],
                                a[1],
                                a[2]
                            ),
                        }
                    }
                    Operation::UnpackString(unpack) => {
                        let bytes: String = unpack
                            .bytes
                            .iter()
                            .map(|byte| format!("\\x{byte:02x}"))
                            .collect();
                        let names = format!(
                            "HStringNames {{ cons: {:?}, nil: {:?}, character: {:?} }}",
                            unpack.cons.name, unpack.nil.name, unpack.character.name
                        );
                        let encoding = match unpack.encoding {
                            crate::nir::strings::Encoding::Latin1 => "Latin1",
                            crate::nir::strings::Encoding::Utf8 => "Utf8",
                        };
                        match unpack.tail {
                            Some(tail) => format!(
                                "h2r_rt::unpack_string(b\"{bytes}\", HEncoding::{encoding}, {names}, {})",
                                value(tail)
                            ),
                            None => format!(
                                "h2r_rt::unpack_literal(b\"{bytes}\", HEncoding::{encoding}, {names})"
                            ),
                        }
                    }
                    Operation::BoxInt(v) => format!("HInt::ready(v{})", v.0),
                    Operation::UnboxInt(v) => format!("v{}.force()", v.0),
                    // Char# and Int# share the carrier, so a code-point
                    // conversion moves the word and changes only the type.
                    Operation::OrdChar(v) | Operation::ChrChar(v) | Operation::IntToWord(v) => {
                        format!("v{}", v.0)
                    }
                    Operation::CharCompare { op, arguments }
                    | Operation::WordCompare { op, arguments } => {
                        let left = arguments[0].0;
                        let right = arguments[1].0;
                        let comparison = match op {
                            CharCompare::Equal => "==",
                            CharCompare::NotEqual => "!=",
                            CharCompare::Less => "<",
                            CharCompare::LessEqual => "<=",
                            CharCompare::Greater => ">",
                            CharCompare::GreaterEqual => ">=",
                        };
                        // GHC orders Char# as an unsigned machine word, and
                        // `chr#` narrows nothing, so `chr# -1#` is the largest
                        // Char# rather than the smallest. Equality does not
                        // care about the signedness; the four orderings do.
                        match op {
                            CharCompare::Equal | CharCompare::NotEqual => {
                                format!("i64::from(v{left} {comparison} v{right})")
                            }
                            _ => format!(
                                "i64::from((v{left} as u64) {comparison} (v{right} as u64))"
                            ),
                        }
                    }
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
                            IntBinary::ShiftLeft => {
                                format!("v{left}.wrapping_shl(v{right} as u32)")
                            }
                            IntBinary::ShiftRightArithmetic => {
                                format!("v{left}.wrapping_shr(v{right} as u32)")
                            }
                        }
                    }
                    Operation::Literal(lit) => {
                        format!("{}i64", scalar_literal(world, &instruction.result.ty, lit)?)
                    }
                    Operation::TopReference {
                        module,
                        binder,
                        type_arguments,
                        dictionaries,
                    } => {
                        let target = instance_of(
                            specialization,
                            &reference_of(*module, *binder, type_arguments, dictionaries),
                        )?;
                        let callee = &leaves[&target].function;
                        let arity = callee.blocks[0].params.len();
                        if arity == 0 {
                            format!("f_{target}()")
                        } else {
                            closure(
                                world,
                                &format!("f_{target}"),
                                (dispatcher(callee, &callee.blocks[0]) == Some("") && has_boxed)
                                    .then(|| format!("HState::B_{target}_{}", callee.entry.0))
                                    .as_deref(),
                                &[],
                                &instruction.result.ty,
                                arity,
                            )?
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
                            specialization,
                            &reference_of(*module, *binder, type_arguments, dictionaries),
                        )?;
                        if leaves[&target].function.blocks[0].params.len() != arguments.len() {
                            return Err("emitted target parameter count disagrees with call".into());
                        }
                        let args = arguments
                            .iter()
                            .map(|arg| value(*arg))
                            .collect::<Vec<_>>()
                            .join(", ");
                        format!("f_{target}({args})")
                    }
                    Operation::Force(_) => {
                        return Err("unsupported operation in scalar Rust backend".into());
                    }
                };
                writeln!(
                    out,
                    "    let v{}: {} = {expression};",
                    instruction.result.id.0,
                    carrier(world, &instruction.result.ty)
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
            let transfer = |target: &crate::nir::BlockId, args: &[crate::nir::ValueId]| match suffix
            {
                Some(suffix) => format!(
                    "HStep{suffix}::Next(HState{suffix}::B_{index}_{}({}))",
                    target.0,
                    args.iter()
                        .map(|v| value(*v))
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
                None if looping(*target) => {
                    format!("{result}::defer_to(move || {})", call(target, args))
                }
                None => call(target, args),
            };
            if !tail_transfer {
                match &block.terminator.exit {
                    Exit::Return(v) => writeln!(
                        out,
                        "    {}",
                        match suffix {
                            Some(suffix) => format!("HStep{suffix}::Done({})", value(*v)),
                            None => value(*v),
                        }
                    )
                    .unwrap(),
                    Exit::Diverge { .. } => {
                        return Err("unimplemented non-returning call".into());
                    }
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
            "#[allow(unused_variables)]\n{vis}fn f_{index}({parameters}) -> {} {{",
            carrier(world, &leaf.function.result_ty)
        )
        .unwrap();
        let args = leaf.function.blocks[0]
            .params
            .iter()
            .map(|p| format!("v{}", p.id.0))
            .collect::<Vec<_>>()
            .join(", ");
        // A lifted result is returned as a thunk the caller forces; an
        // unlifted one is returned as it is. An unboxed tuple is unlifted and
        // cannot be delayed at all — GHC's type system already forbids it, so
        // deferring one would be emitting code for a value that cannot exist.
        if data::lifted(world, &leaf.function.result_ty) {
            let result_carrier = carrier(world, &leaf.function.result_ty);
            if block.params.is_empty() {
                writeln!(out, "    std::thread_local! {{ static VALUE: {result_carrier} = {result_carrier}::defer_to(|| b_{index}_{}()); }}\n    VALUE.with(Clone::clone)\n}}", leaf.function.entry.0).unwrap();
            } else {
                writeln!(
                    out,
                    "    {result_carrier}::defer_to(move || b_{index}_{}({args}))\n}}",
                    leaf.function.entry.0
                )
                .unwrap();
            }
        } else {
            writeln!(out, "    b_{index}_{}({args})\n}}", leaf.function.entry.0).unwrap();
        }
    }
    if chunks != 0 {
        out.push_str("}\n");
    }
    for chunk in 0..chunks {
        writeln!(out, "use h_chunk_{chunk}::*;").unwrap();
    }
    Ok(out)
}

/// One command-line argument, read at the type the entry takes it at.
fn argument(world: &World<'_>, ty: &Ty, index: usize) -> Result<String, String> {
    let parsed = format!("raw[{index}].parse::<i64>().expect(\"expected signed 64-bit integer\")");
    let ty = represented(world, ty);
    if unboxed(&ty) && !is_char(&ty) {
        Ok(parsed)
    } else if boxed::is_int(&ty) {
        Ok(format!("HInt::ready({parsed})"))
    } else if ty.list_elem().is_some_and(Ty::is_char) {
        Ok(format!(
            "h2r_rt::string_argument(&raw[{index}], {})",
            string_names(world)?
        ))
    } else {
        Err(format!(
            "CLI adapter reads Int#, Int and String arguments, not {}",
            ty.render()
        ))
    }
}

fn string_names(world: &World<'_>) -> Result<String, String> {
    let (nil, cons, character) = data::string_layouts(world)?;
    Ok(format!(
        "HStringNames {{ cons: {:?}, nil: {:?}, character: {:?} }}",
        cons.name, nil.name, character.name
    ))
}

/// The `show` functions a result needs, one per type, named by position.
#[derive(Default)]
struct Shows {
    named: std::collections::BTreeMap<String, String>,
    functions: Vec<String>,
}

/// The name of a generated `fn(&HField, u8) -> String` that renders a value
/// of `ty` as GHC's `show` does for `Int`, `Char`, `String`, lists, tuples and
/// derived `Show` over positional constructors.
fn show_function(world: &World<'_>, ty: &Ty, shows: &mut Shows) -> Result<String, String> {
    let ty = represented(world, ty);
    let key = ty.render();
    if let Some(name) = shows.named.get(&key) {
        return Ok(name.clone());
    }
    let name = format!("show_{}", shows.named.len());
    shows.named.insert(key.clone(), name.clone());
    let body = if boxed::is_int(&ty) {
        "h2r_rt::show_int(value.int().force(), precedence)".to_string()
    } else if ty.is_char() {
        format!("h2r_rt::show_char(&value.data(), {})", string_names(world)?)
    } else if ty.list_elem().is_some_and(Ty::is_char) {
        format!(
            "h2r_rt::show_string(&value.data(), {})",
            string_names(world)?
        )
    } else if let Some(element) = ty.list_elem() {
        let (nil, _) = data::list_layouts(world, element)?;
        let item = show_function(world, element, shows)?;
        format!(
            "{{ let _ = precedence; let mut out = String::from(\"[\"); let mut cell = value.data(); loop {{ let node = cell.force(); if node.constructor == {:?} {{ break; }} if out.len() > 1 {{ out.push(','); }} out.push_str(&{item}(&node.fields[0], 0)); cell = node.fields[1].data(); }} out.push(']'); out }}",
            nil.name
        )
    } else if data::carrier(world, &ty) == Some(data::Carrier::Data) {
        let family = data::family(world, &ty)?;
        let tuple = matches!(&ty, Ty::Con { tycon, .. } if tycon.occ.starts_with("(,"));
        let mut arms = String::new();
        for constructor in &family {
            let occ = constructor
                .name
                .rsplit('$')
                .next()
                .unwrap_or_default()
                .to_string();
            let mut fields = Vec::new();
            for (index, field) in constructor.fields.iter().enumerate() {
                if !data::lifted(world, field) {
                    return Err(format!(
                        "CLI adapter cannot show the unlifted field of {occ}"
                    ));
                }
                let show = show_function(world, field, shows)?;
                fields.push(format!(
                    "{show}(&node.fields[{index}], {})",
                    if tuple { 0 } else { 11 }
                ));
            }
            let text = if tuple {
                format!(
                    "format!(\"({})\", {})",
                    vec!["{}"; fields.len()].join(","),
                    fields.join(", ")
                )
            } else if fields.is_empty() {
                format!("{occ:?}.to_string()")
            } else if occ.starts_with(|c: char| c.is_ascii_uppercase()) {
                format!(
                    "{{ let text = format!(\"{} {}\", {}); if precedence >= 11 {{ format!(\"({{text}})\") }} else {{ text }} }}",
                    occ.replace('{', "{{").replace('}', "}}"),
                    vec!["{}"; fields.len()].join(" "),
                    fields.join(", ")
                )
            } else {
                return Err(format!(
                    "CLI adapter cannot show the infix constructor {occ}"
                ));
            };
            write!(arms, "{:?} => {text}, ", constructor.name).unwrap();
        }
        format!(
            "{{ let _ = precedence; let node = value.data().force(); match node.constructor {{ {arms}other => panic!(\"show: {{other}} is not in this family\") }} }}"
        )
    } else {
        return Err(format!("CLI adapter cannot show a value of type {key}"));
    };
    shows.functions.push(format!(
        "#[allow(dead_code)]\nfn {name}(value: &HField, precedence: u8) -> String {{ {body} }}\n"
    ));
    Ok(name)
}
