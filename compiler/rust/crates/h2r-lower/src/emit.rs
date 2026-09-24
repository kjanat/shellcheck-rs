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
    Block, CharCompare, DictionaryRef, Exit, Function, IntBinary, ListOp, Machine, Operation,
    World, boxed, data,
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
            || tycon.name == "$ghc-prim$GHC.Prim$Word#"
            || tycon.name == "$ghc-prim$GHC.Prim$Word8#")
        || matches!(ty, Ty::Con { tycon, args } if args.len() == 1
            && tycon.name == "$ghc-prim$GHC.Prim$State#"))
}

fn is_addr(ty: &Ty) -> bool {
    matches!(ty, Ty::Con { tycon, args } if tycon.name == "$ghc-prim$GHC.Prim$Addr#" && args.is_empty())
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
    if let Ty::ForAll { .. } = ty {
        return carrier(world, &data::erase_quantifiers(&ty));
    }
    if data::is_erased(&ty) {
        "HField".into()
    } else if boxed::is_int(&ty) {
        "HInt".into()
    } else if unboxed(&ty) {
        "i64".into()
    } else if is_addr(&ty) {
        "HAddr".into()
    } else if matches!(&ty, Ty::Con { tycon, args } if tycon.name == "$ghc-prim$GHC.Prim$MutVar#" && args.len() == 3)
    {
        "HMutVar".into()
    } else if matches!(&ty, Ty::Con { tycon, args }
        if (tycon.name == "$ghc-prim$GHC.Prim$ByteArray#" && args.is_empty())
            || (tycon.name == "$ghc-prim$GHC.Prim$MutableByteArray#" && args.len() == 1))
    {
        "HBytes".into()
    } else if matches!(&ty, Ty::Con { tycon, args }
        if (tycon.name == "$ghc-prim$GHC.Prim$Array#" && args.len() == 2)
            || (tycon.name == "$ghc-prim$GHC.Prim$MutableArray#" && args.len() == 3))
    {
        "HArray".into()
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
        Some(data::Carrier::Address) => carrier(world, ty) == "HAddr",
        Some(data::Carrier::MutVar) => carrier(world, ty) == "HMutVar",
        Some(data::Carrier::Bytes) => carrier(world, ty) == "HBytes",
        Some(data::Carrier::Array) => carrier(world, ty) == "HArray",
        Some(data::Carrier::Dynamic) => carrier(world, ty) == "HField",
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
        "HMutVar" => ("MutVar", "mut_var"),
        "HBytes" => ("Bytes", "bytes"),
        "HArray" => ("Array", "array"),
        "HAddr" => ("Addr", "addr"),
        "HField" => ("Dynamic", "dynamic"),
        _ => ("Data", "data"),
    }
}

fn pack(world: &World<'_>, ty: &Ty, value: &str) -> String {
    if let Ok(Some(components)) = data::unboxed_tuple_fields(world, &represented(world, ty)) {
        let fields: Vec<String> = components
            .iter()
            .enumerate()
            .map(|(n, component)| pack(world, component, &format!("t.{n}")))
            .collect();
        return format!(
            "{{ let t = {value}; HField::Tuple(std::rc::Rc::new(vec![{}])) }}",
            fields.join(", ")
        );
    }
    match field_kind(world, ty).0 {
        "Dynamic" => value.to_string(),
        kind => format!("HField::{kind}({value})"),
    }
}

fn unpack(world: &World<'_>, ty: &Ty, field: &str) -> String {
    if let Ok(Some(components)) = data::unboxed_tuple_fields(world, &represented(world, ty)) {
        let reads: Vec<String> = components
            .iter()
            .enumerate()
            .map(|(n, component)| unpack(world, component, &format!("t[{n}]")))
            .collect();
        return match reads.as_slice() {
            [one] => format!("{{ let t = {field}.tuple(); ({one},) }}"),
            many => format!("{{ let t = {field}.tuple(); ({}) }}", many.join(", ")),
        };
    }
    format!("{field}.{}()", field_kind(world, ty).1)
}

fn closure(
    world: &World<'_>,
    target: &str,
    entry: Option<&str>,
    captures: &[String],
    parameters: &[&Ty],
    result: &Ty,
) -> Result<String, String> {
    let arity = parameters.len();
    if arity == 0 {
        return Err("closure has no value parameters".into());
    }
    let bindings = captures
        .iter()
        .enumerate()
        .map(|(n, v)| format!("let c{n} = {v}; let e{n} = c{n}.clone();"))
        .collect::<Vec<_>>()
        .join(" ");
    let args: Vec<String> = parameters
        .iter()
        .enumerate()
        .map(|(n, parameter)| unpack(world, parameter, &format!("a[{n}]")))
        .collect();
    let with = |prefix: char| {
        (0..captures.len())
            .map(|n| format!("{prefix}{n}.clone()"))
            .chain(args.iter().cloned())
            .collect::<Vec<_>>()
            .join(", ")
    };
    let code = format!(
        "move |a| {}",
        pack(world, result, &format!("{target}({})", with('c')))
    );
    Ok(match entry {
        Some(state) => format!(
            "{{ {bindings} HClosure::entering({arity}, {code}, move |a| {state}({})) }}",
            with('e')
        ),
        None => format!("{{ {bindings} HClosure::ready({arity}, {code}) }}"),
    })
}

fn step_to(callee: &str, args: &str) -> String {
    format!("h2r_rt::Step::Next(Box::new(move || {callee}({args})))")
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
        let mut fields = String::new();
        let pattern = if let Some(c) = &arm.constructor {
            for (i, t) in c.fields.iter().enumerate() {
                write!(
                    fields,
                    "let f{i} = node.fields[{i}].{}(); ",
                    field_kind(world, t).1
                )
                .unwrap();
                args.push(format!("f{i}"));
            }
            format!("{:?}", c.name)
        } else {
            "_".into()
        };
        write!(
            code,
            " {pattern} => {{ {fields}{} }},",
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
    if matches!(represented(world, ty), Ty::Con { tycon, args } if tycon.name == "$ghc-prim$GHC.Prim$Word8#" && args.is_empty())
    {
        return u8::try_from(lit.number("Word8")?)
            .map(i64::from)
            .map_err(|error| format!("Word8# literal does not fit an unsigned byte: {error}"));
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
                .map(|p| &*p.ty),
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
            | Operation::WordBinary { .. }
            | Operation::IntToWord(_)
            | Operation::WordToInt(_)
            | Operation::NegateInt(_)
            | Operation::IndexCharAddr { .. }
            | Operation::PlusAddr { .. }
            | Operation::AddrLiteral(_)
            | Operation::PendingCell
            | Operation::FillCell { .. }
            | Operation::Machine { .. }
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
            Operation::Literal(lit) if carrier(world, &instruction.result.ty) == "HBytes" => {
                big_nat_limbs(lit)?;
            }
            Operation::Literal(lit) => {
                if carrier(world, &instruction.result.ty) != "i64" {
                    return Err(format!(
                        "a literal of type {} has no scalar carrier",
                        instruction.result.ty.render()
                    ));
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
            Operation::Force(_) => {}
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
        Ty::Con { tycon, .. } => tycon.name.to_string(),
        Ty::Var(_) => "a type variable".into(),
        Ty::ForAll { .. } => "a polymorphic type".into(),
        other => other.render(),
    }
}

/// Select one exact external entry and lower every required instance. No
/// source is returned until the entire closure has passed lowering and checks.
struct Prepared<'a> {
    world: &'a World<'a>,
    specialization: &'a specialize::Specialization,
    leaves: &'a BTreeMap<usize, &'a LoweredLeaf>,
    edges: &'a BTreeMap<usize, BTreeSet<usize>>,
    roots: usize,
    adapter: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Driver {
    Print,
    Lint,
    Api,
}

fn prepare<R>(
    modules: &[Module],
    entries: &[&str],
    driver: Driver,
    emit: impl FnOnce(Prepared<'_>) -> Result<R, String>,
) -> Result<R, String> {
    if entries.is_empty() || (driver != Driver::Api && entries.len() > 1) {
        return Err("a program runs one entry, and only a typed API takes several".into());
    }
    let mut roots = Vec::new();
    for &entry in entries {
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
            return Err(format!(
                "entry {entry} matched {} definitions",
                matches.len()
            ));
        };
        let root = Instance::whole(*root_module, *root_binder);
        if roots.contains(&root) {
            return Err(format!("entry {entry} is named twice"));
        }
        roots.push(root);
    }
    let specialization =
        specialize::specialize(modules, &roots).map_err(|error| error.to_string())?;
    if specialization.instances[..roots.len()] != roots[..] {
        return Err("the specialization did not number the entries first".into());
    }
    let catalog = crate::nir::Catalog::of(modules);
    let evidence = crate::nir::World::cataloged(modules, 0, &catalog)?;
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
    let mut refusals: BTreeMap<String, (usize, String)> = BTreeMap::new();
    for (&index, leaf) in &leaves {
        match dependencies(world, &specialization, index, leaf) {
            Ok(dependencies) => {
                edges.insert(index, dependencies);
            }
            Err(reason) => {
                let instance = &specialization.instances[index];
                let refusal = refusals.entry(reason).or_insert_with(|| {
                    (
                        0,
                        modules[instance.module]
                            .binder(instance.binder)
                            .name
                            .clone(),
                    )
                });
                refusal.0 += 1;
            }
        }
    }
    if !refusals.is_empty() {
        return Err(refusals
            .iter()
            .map(|(reason, (count, example))| {
                format!("{count} instances, e.g. {example}: {reason}")
            })
            .collect::<Vec<_>>()
            .join("\n"));
    }
    let mut adapter = String::new();
    for (index, &entry) in entries.iter().enumerate() {
        let name = match driver {
            Driver::Api => format!("h2r_entry_{index}"),
            Driver::Print | Driver::Lint => "h2r_entry".to_string(),
        };
        let entry_function = &leaves[&index].function;
        let direct_arity = entry_function.blocks[0].params.len();
        let mut entry_types: Vec<_> = entry_function.blocks[0]
            .params
            .iter()
            .map(|p| &*p.ty)
            .collect();
        let mut entry_result = &entry_function.result_ty;
        while let Ty::Fun { arg, res, .. } = entry_result {
            entry_types.push(arg);
            entry_result = res;
        }
        entry_adapter(
            world,
            index,
            &name,
            direct_arity,
            &entry_types,
            entry_result,
            &mut adapter,
        );
        match driver {
            Driver::Print => print_main(world, &mut adapter, &entry_types, entry_result)?,
            Driver::Lint => lint_main(world, &mut adapter, &entry_types, entry_result)?,
            Driver::Api => {
                api_function(
                    world,
                    &mut adapter,
                    entry,
                    &name,
                    &entry_types,
                    entry_result,
                )?;
            }
        }
    }
    if driver == Driver::Api {
        writeln!(adapter, "pub use h2r_rt::on_program_stack;").unwrap();
    }
    emit(Prepared {
        world,
        specialization: &specialization,
        leaves: &leaves,
        edges: &edges,
        roots: entries.len(),
        adapter,
    })
}

fn entry_adapter(
    world: &World<'_>,
    index: usize,
    name: &str,
    direct_arity: usize,
    entry_types: &[&Ty],
    entry_result: &Ty,
    adapter: &mut String,
) {
    if direct_arity == entry_types.len() {
        writeln!(
            adapter,
            "#[allow(unused_imports)]\nuse f_{index} as {name};"
        )
        .unwrap();
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
            .map(|(n, t)| pack(world, t, &format!("a{n}")))
            .collect::<Vec<_>>()
            .join(", ");
        writeln!(
            adapter,
            "fn {name}({params}) -> {} {{ {} }}",
            carrier(world, entry_result),
            unpack(
                world,
                entry_result,
                &format!("f_{index}({direct}).apply(vec![{extra}])")
            )
        )
        .unwrap();
    }
}

fn print_main(
    world: &World<'_>,
    adapter: &mut String,
    entry_types: &[&Ty],
    entry_result: &Ty,
) -> Result<(), String> {
    let arity = entry_types.len();
    let args = entry_types
        .iter()
        .enumerate()
        .map(|(i, ty)| argument(world, ty, i))
        .collect::<Result<Vec<_>, _>>()?
        .join(", ");
    let mut shows = Shows::default();
    let result = if !scalar(world, entry_result) {
        let show = show_function(world, entry_result, &mut shows)?;
        format!(
            "{show}(&{}, 0)",
            pack(world, entry_result, &format!("h2r_entry({args})"))
        )
    } else if boxed::is_int(entry_result) {
        format!("h2r_entry({args}).force()")
    } else {
        format!("h2r_entry({args})")
    };
    for function in &shows.functions {
        adapter.push_str(function);
    }
    writeln!(adapter, "fn main() {{\n    let raw: Vec<String> = std::env::args().skip(1).collect();\n    assert_eq!(raw.len(), {arity}, \"wrong argument count\");\n    h2r_rt::on_program_stack(move || println!(\"{{}}\", {result}));\n}}").unwrap();
    Ok(())
}

fn lint_main(
    world: &World<'_>,
    adapter: &mut String,
    entry_types: &[&Ty],
    entry_result: &Ty,
) -> Result<(), String> {
    let text = |ty: &Ty| represented(world, ty).list_elem().is_some_and(Ty::is_char);
    let lines = represented(world, entry_result)
        .list_elem()
        .is_some_and(&text);
    if !(entry_types.len() == 2 && entry_types.iter().all(|ty| text(ty)) && lines) {
        return Err("a lint entry takes a path and the file's text and returns lines".into());
    }
    let names = string_names(world)?;
    writeln!(
        adapter,
        r#"fn main() {{
    let paths: Vec<String> = std::env::args().skip(1).collect();
    if paths.is_empty() {{
        eprintln!("No files specified.");
        std::process::exit(3);
    }}
    let status = std::sync::Arc::new(std::sync::atomic::AtomicI32::new(0));
    let shared = status.clone();
    h2r_rt::on_program_stack(move || {{
        let mut out = std::io::BufWriter::new(std::io::stdout().lock());
        for path in paths {{
            match std::fs::read(&path) {{
                Ok(bytes) => {{
                    let text: String = bytes.iter().map(|&byte| char::from(byte)).collect();
                    let report = h2r_entry(h2r_rt::string_argument(&path, {names}), h2r_rt::string_argument(&text, {names}));
                    if h2r_rt::put_lines(report, {names}, &mut out) > 0 {{
                        shared.fetch_max(1, std::sync::atomic::Ordering::Relaxed);
                    }}
                }}
                Err(error) => {{
                    std::io::Write::flush(&mut out).expect("writing to stdout");
                    eprintln!("{{path}}: {{error}}");
                    shared.fetch_max(2, std::sync::atomic::Ordering::Relaxed);
                }}
            }}
        }}
        std::io::Write::flush(&mut out).expect("writing to stdout");
    }});
    std::process::exit(status.load(std::sync::atomic::Ordering::Relaxed));
}}"#
    )
    .unwrap();
    Ok(())
}

pub fn emit_entry(modules: &[Module], entry: &str) -> Result<String, String> {
    prepare(modules, &[entry], Driver::Print, |prepared| {
        let mut out = functions(
            prepared.world,
            prepared.specialization,
            prepared.leaves,
            None,
        )?;
        out.push_str(&prepared.adapter);
        Ok(out)
    })
}

pub struct CrateSource {
    pub name: String,
    pub source: String,
    pub dependencies: Vec<String>,
}

pub struct SplitProgram {
    pub runtime: String,
    pub crates: Vec<CrateSource>,
    pub main: String,
    pub main_dependencies: Vec<String>,
}

const RUNTIME_ALIASES: &str = "#[allow(unused_imports)]\nuse h2r_rt::Int as HInt;\n#[allow(unused_imports)]\nuse h2r_rt::{Data as HData, Field as HField, Closure as HClosure};\n#[allow(unused_imports)]\nuse h2r_rt::{Encoding as HEncoding, ListNames as HListNames, StringNames as HStringNames};\n#[allow(unused_imports)]\nuse h2r_rt::Addr as HAddr;\n#[allow(unused_imports)]\nuse h2r_rt::{Array as HArray, Bytes as HBytes, MutVar as HMutVar};\n";

pub fn emit_entry_split(
    modules: &[Module],
    entries: &[&str],
    budget: usize,
    driver: Driver,
) -> Result<SplitProgram, String> {
    prepare(modules, entries, driver, |prepared| {
        let world = prepared.world;
        let has_boxed = has_boxed(world, prepared.leaves);
        let mut code = BTreeMap::new();
        for (&index, leaf) in prepared.leaves {
            code.insert(
                index,
                leaf_code(
                    world,
                    prepared.specialization,
                    prepared.leaves,
                    index,
                    leaf,
                    "pub ",
                    has_boxed,
                )?,
            );
        }
        let mut crate_of: BTreeMap<usize, usize> = BTreeMap::new();
        let mut members: Vec<Vec<usize>> = Vec::new();
        let mut size = 0;
        for component in components(prepared.edges) {
            let bytes: usize = component.iter().map(|index| code[index].len()).sum();
            if members.is_empty() || (size > 0 && size + bytes > budget) {
                members.push(Vec::new());
                size = 0;
            }
            let current = members.len() - 1;
            for &index in &component {
                crate_of.insert(index, current);
            }
            members[current].extend(component);
            size += bytes;
        }
        let name = |number: usize| format!("h2r_c{number}");
        let mut crates = Vec::new();
        for (number, indices) in members.iter().enumerate() {
            let dependencies: BTreeSet<usize> = indices
                .iter()
                .flat_map(|index| &prepared.edges[index])
                .map(|target| crate_of[target])
                .filter(|&other| other != number)
                .collect();
            let sites = 2 * indices.len()
                + indices
                    .iter()
                    .flat_map(|index| &prepared.leaves[index].function.blocks)
                    .map(|block| block.instructions.len())
                    .sum::<usize>();
            let mut source = if sites > 128 {
                format!("#![recursion_limit = \"{sites}\"]\n")
            } else {
                String::new()
            };
            source.push_str(RUNTIME_ALIASES);
            for dependency in &dependencies {
                writeln!(source, "use {}::*;", name(*dependency)).unwrap();
            }
            let mut ordered = indices.clone();
            ordered.sort_unstable();
            for index in ordered {
                source.push_str(&code[&index]);
            }
            crates.push(CrateSource {
                name: name(number),
                source,
                dependencies: dependencies.into_iter().map(name).collect(),
            });
        }
        let entry_crates: BTreeSet<String> = (0..prepared.roots)
            .map(|index| name(crate_of[&index]))
            .collect();
        let mut main = String::from(
            "#[cfg(not(target_pointer_width = \"64\"))]\ncompile_error!(\"Int# backend requires a 64-bit target\");\n",
        );
        main.push_str(RUNTIME_ALIASES);
        for entry_crate in &entry_crates {
            writeln!(main, "use {entry_crate}::*;").unwrap();
        }
        main.push_str(&prepared.adapter);
        Ok(SplitProgram {
            runtime: include_str!("../../h2r-rt/src/lib.rs").to_string(),
            crates,
            main,
            main_dependencies: entry_crates.into_iter().collect(),
        })
    })
}

fn components(edges: &BTreeMap<usize, BTreeSet<usize>>) -> Vec<Vec<usize>> {
    let mut order: BTreeMap<usize, usize> = BTreeMap::new();
    let mut low: BTreeMap<usize, usize> = BTreeMap::new();
    let mut stack: Vec<usize> = Vec::new();
    let mut on_stack: BTreeSet<usize> = BTreeSet::new();
    let mut found = Vec::new();
    for &root in edges.keys() {
        if order.contains_key(&root) {
            continue;
        }
        let mut work: Vec<(usize, Vec<usize>)> = Vec::new();
        let visit = |node: usize,
                     order: &mut BTreeMap<usize, usize>,
                     low: &mut BTreeMap<usize, usize>,
                     stack: &mut Vec<usize>,
                     on_stack: &mut BTreeSet<usize>,
                     work: &mut Vec<(usize, Vec<usize>)>| {
            let next = order.len();
            order.insert(node, next);
            low.insert(node, next);
            stack.push(node);
            on_stack.insert(node);
            work.push((node, edges[&node].iter().rev().copied().collect()));
        };
        visit(
            root,
            &mut order,
            &mut low,
            &mut stack,
            &mut on_stack,
            &mut work,
        );
        while let Some((node, pending)) = work.last_mut() {
            let node = *node;
            if let Some(target) = pending.pop() {
                if !order.contains_key(&target) {
                    visit(
                        target,
                        &mut order,
                        &mut low,
                        &mut stack,
                        &mut on_stack,
                        &mut work,
                    );
                } else if on_stack.contains(&target) {
                    let reached = order[&target].min(low[&node]);
                    low.insert(node, reached);
                }
                continue;
            }
            work.pop();
            if let Some((parent, _)) = work.last() {
                let reached = low[&node].min(low[parent]);
                low.insert(*parent, reached);
            }
            if low[&node] == order[&node] {
                let mut component = Vec::new();
                while let Some(member) = stack.pop() {
                    on_stack.remove(&member);
                    component.push(member);
                    if member == node {
                        break;
                    }
                }
                found.push(component);
            }
        }
    }
    found
}

const PROGRAM_CHUNK: usize = 64;

// GHC's default maximum stack is 80% of physical memory.

pub struct Program {
    pub source: String,
    pub instances: usize,
    pub lowered: usize,
    pub emittable: usize,
    pub emitted: usize,
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
    let catalog = crate::nir::Catalog::of(modules);
    let evidence = crate::nir::World::cataloged(modules, 0, &catalog)?;
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
    let has_boxed = has_boxed(world, leaves);
    out.push_str("\n#[allow(dead_code)]\nmod h2r_rt {\n");
    out.push_str(include_str!("../../h2r-rt/src/lib.rs"));
    out.push_str("\n}\n");
    out.push_str(RUNTIME_ALIASES);
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
        out.push_str(&leaf_code(
            world,
            specialization,
            leaves,
            index,
            leaf,
            vis,
            has_boxed,
        )?);
    }
    if chunks != 0 {
        out.push_str("}\n");
    }
    for chunk in 0..chunks {
        writeln!(out, "use h_chunk_{chunk}::*;").unwrap();
    }
    Ok(out)
}

fn has_boxed(world: &World<'_>, leaves: &BTreeMap<usize, &LoweredLeaf>) -> bool {
    leaves.values().any(|leaf| {
        carrier(world, &leaf.function.result_ty) != "i64"
            || leaf.function.blocks.iter().any(|b| {
                b.params
                    .iter()
                    .chain(b.instructions.iter().map(|i| &i.result))
                    .any(|v| carrier(world, &v.ty) != "i64")
            })
    })
}

fn leaf_code(
    world: &World<'_>,
    specialization: &specialize::Specialization,
    leaves: &BTreeMap<usize, &LoweredLeaf>,
    index: usize,
    leaf: &LoweredLeaf,
    vis: &str,
    has_boxed: bool,
) -> Result<String, String> {
    let mut out = String::new();
    let unlifted = |function: &Function, block: &Block| {
        let ty = block_result(function, block);
        (!data::lifted(world, ty)).then(|| carrier(world, ty))
    };
    {
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
            let stepped = unlifted(&leaf.function, block);
            let looping = |target: crate::nir::BlockId| {
                stepped.is_none() && reaches(&graph, target, block.id)
            };
            let block_parameters = block
                .params
                .iter()
                .map(|p| format!("v{}: {}", p.id.0, carrier(world, &p.ty)))
                .collect::<Vec<_>>()
                .join(", ");
            if stepped.is_some() {
                let args = block
                    .params
                    .iter()
                    .map(|p| format!("v{}", p.id.0))
                    .collect::<Vec<_>>()
                    .join(", ");
                writeln!(
                    out,
                    "{vis}fn b_{index}_{}({block_parameters}) -> {result} {{ s_{index}_{}({args}).run() }}",
                    block.id.0, block.id.0
                )
                .unwrap();
            }
            writeln!(
                out,
                "    #[allow(unused_variables)]\n    {vis}fn {}_{index}_{}({block_parameters}) -> {} {{",
                if stepped.is_some() { "s" } else { "b" },
                block.id.0,
                match stepped {
                    Some(_) => format!("h2r_rt::Step<{result}>"),
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
            let last = last_uses(block);
            let at = std::cell::Cell::new(0);
            let moves = |id: crate::nir::ValueId| last.get(&id) == Some(&(at.get(), true));
            let value = |id: crate::nir::ValueId| {
                let ty = value_ty(id);
                if carrier(world, ty) == "i64" || moves(id) {
                    format!("v{}", id.0)
                } else {
                    format!("v{}.clone()", id.0)
                }
            };
            let mut tail_transfer = false;
            for (position, instruction) in block.instructions.iter().enumerate() {
                at.set(position);
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
                                .map(|v| pack(world, value_ty(*v), &value(*v)))
                                .collect::<Vec<_>>()
                                .join(", ");
                            (
                                format!("v{}", callee.0),
                                args,
                                field_kind(world, &instruction.result.ty).1,
                            )
                        };
                    let code = match (stepped.as_deref(), destination, &instruction.operation) {
                        (Some(_), Some((target_index, target, arguments)), _) => {
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
                            Some(step_to(&format!("s_{target_index}_{}", target.0), &args))
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
                        ) if stepped.is_some() || arms.iter().any(|arm| looping(arm.target)) => {
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
                                |target, args| match stepped {
                                    Some(_) => step_to(&format!("s_{index}_{}", target.0), &args),
                                    None if looping(target) => format!(
                                        "{result}::defer_to(move || b_{index}_{}({args}))",
                                        target.0
                                    ),
                                    None => format!("b_{index}_{}({args})", target.0),
                                },
                            ))
                        }
                        (Some("i64"), _, Operation::Apply { callee, arguments }) if has_boxed => {
                            let (callee, args, read) = applied(callee, arguments);
                            Some(format!(
                                "h2r_rt::Step::Next(Box::new(move || match {callee}.apply_tail(vec![{args}]) {{ h2r_rt::Tail::Enter(step) => step, h2r_rt::Tail::Value(value) => h2r_rt::Step::Done(value.{read}()) }}))"
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
                            (unlifted(&leaf.function, target_block).as_deref() == Some("i64")
                                && has_boxed)
                                .then(|| format!("s_{index}_{}", target.0))
                                .as_deref(),
                            &arguments.iter().map(|v| value(*v)).collect::<Vec<_>>(),
                            &target_block.params[arguments.len()..]
                                .iter()
                                .map(|p| &*p.ty)
                                .collect::<Vec<_>>(),
                            block_result(&leaf.function, target_block),
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
                                pack(world, ty, &value(*v))
                            })
                            .collect::<Vec<_>>()
                            .join(", ");
                        unpack(
                            world,
                            &instruction.result.ty,
                            &format!("v{}.apply(vec![{args}])", callee.0),
                        )
                    }
                    Operation::Construct {
                        constructor,
                        arguments,
                    } => {
                        let fields = arguments
                            .iter()
                            .zip(&constructor.fields)
                            .map(|(v, t)| pack(world, t, &value(*v)))
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
                        let collection = if arguments.len() <= 3 { "" } else { "vec!" };
                        format!(
                            "{{ let fields = {collection}[{fields}]; {strict} HData::ready({:?}, fields) }}",
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
                        if moves(*tuple) {
                            format!("v{}.{index}", tuple.0)
                        } else {
                            format!("v{}.{index}.clone()", tuple.0)
                        }
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
                            "{{ let scrutinee = {}; let node = scrutinee.force(); match node.constructor {{ {arms}other => panic!(\"dataToTag#: {{other}} is not in the family\") }} }}",
                            value(*operand)
                        )
                    }
                    Operation::TagToEnum { tag, constructors } => {
                        let arms: String = constructors
                            .iter()
                            .map(|c| {
                                format!(
                                    "{} => HData::ready({:?}, []), ",
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
                                    kind @ ("Int" | "Data" | "Closure" | "Dynamic") => kind,
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
                                "h2r_rt::cons_append({}, {}, {}, {input})",
                                pack(world, value_ty(list.arguments[0]), &a[0]),
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
                    Operation::OrdChar(v)
                    | Operation::ChrChar(v)
                    | Operation::IntToWord(v)
                    | Operation::WordToInt(v) => {
                        format!("v{}", v.0)
                    }
                    Operation::NegateInt(v) => format!("v{}.wrapping_neg()", v.0),
                    Operation::Machine {
                        op,
                        type_arguments,
                        arguments,
                    } => {
                        let a: Vec<String> = arguments.iter().map(|v| value(*v)).collect();
                        let element = |index: usize| field_kind(world, &type_arguments[index]);
                        let unsigned = |i: usize| format!("({} as u64)", a[i]);
                        let wide = |i: usize| format!("({} as u64 as u128)", a[i]);
                        match op {
                            Machine::XorWord | Machine::XorInt => format!("{} ^ {}", a[0], a[1]),
                            Machine::OrWord => format!("{} | {}", a[0], a[1]),
                            Machine::NotWord | Machine::NotInt => format!("!{}", a[0]),
                            Machine::QuotRemInt => {
                                format!(
                                    "({0}.wrapping_div({1}), {0}.wrapping_rem({1}))",
                                    a[0], a[1]
                                )
                            }
                            Machine::Word8ToWord => a[0].clone(),
                            Machine::WordToWord8 => format!("{} & 0xff", a[0]),
                            Machine::IndexWord8Addr => format!("{}.index_word8({})", a[0], a[1]),
                            Machine::ShiftLeftWord => {
                                format!("{}.wrapping_shl({} as u32)", a[0], a[1])
                            }
                            Machine::ShiftRightWord | Machine::ShiftRightLogicalInt => {
                                format!("{}.wrapping_shr({} as u32) as i64", unsigned(0), a[1])
                            }
                            Machine::PlusWord => format!("{}.wrapping_add({})", a[0], a[1]),
                            Machine::TimesWord => format!("{}.wrapping_mul({})", a[0], a[1]),
                            Machine::QuotWord => {
                                format!("({} / {}) as i64", unsigned(0), unsigned(1))
                            }
                            Machine::RemWord => {
                                format!("({} % {}) as i64", unsigned(0), unsigned(1))
                            }
                            Machine::QuotRemWord => format!(
                                "(({0} / {1}) as i64, ({0} % {1}) as i64)",
                                unsigned(0),
                                unsigned(1)
                            ),
                            Machine::QuotRemWord2 => format!(
                                "{{ let n = ({} << 64) | {}; let d = {} as u64 as u128; ((n / d) as u64 as i64, (n % d) as u64 as i64) }}",
                                wide(0),
                                wide(1),
                                a[2]
                            ),
                            Machine::PlusWord2 | Machine::TimesWord2 => format!(
                                "{{ let n = {} {} {}; ((n >> 64) as u64 as i64, n as u64 as i64) }}",
                                wide(0),
                                if *op == Machine::PlusWord2 { "+" } else { "*" },
                                wide(1)
                            ),
                            Machine::AddWordC | Machine::SubWordC => format!(
                                "{{ let (n, c) = {}.{}({} as u64); (n as i64, i64::from(c)) }}",
                                unsigned(0),
                                if *op == Machine::AddWordC {
                                    "overflowing_add"
                                } else {
                                    "overflowing_sub"
                                },
                                a[1]
                            ),
                            Machine::AddIntC | Machine::SubIntC => format!(
                                "{{ let (n, c) = {}.{}({}); (n, i64::from(c)) }}",
                                a[0],
                                if *op == Machine::AddIntC {
                                    "overflowing_add"
                                } else {
                                    "overflowing_sub"
                                },
                                a[1]
                            ),
                            Machine::MulIntMayOflo => {
                                format!("i64::from({}.checked_mul({}).is_none())", a[0], a[1])
                            }
                            Machine::TimesInt2 => format!(
                                "{{ let n = ({} as i128) * ({} as i128); let (high, low) = ((n >> 64) as i64, n as i64); (i64::from(high != low >> 63), high, low) }}",
                                a[0], a[1]
                            ),
                            Machine::Clz => format!("i64::from({}.leading_zeros())", unsigned(0)),
                            Machine::Ctz => format!("i64::from({}.trailing_zeros())", unsigned(0)),
                            Machine::PopCnt => format!("i64::from({}.count_ones())", unsigned(0)),
                            Machine::NewMutVar => format!(
                                "({}, HMutVar::new({}))",
                                a[1],
                                pack(world, &type_arguments[1], &a[0])
                            ),
                            Machine::ReadMutVar => {
                                format!("({}, {}.read().{}())", a[1], a[0], element(2).1)
                            }
                            Machine::WriteMutVar => format!(
                                "{{ {}.write({}); {} }}",
                                a[0],
                                pack(world, &type_arguments[2], &a[1]),
                                a[2]
                            ),
                            Machine::Raise => "h2r_rt::raise_exception()".into(),
                            Machine::RaiseDivZero => {
                                "h2r_rt::raise_arithmetic(\"divide by zero\")".into()
                            }
                            Machine::RaiseUnderflow => {
                                "h2r_rt::raise_arithmetic(\"arithmetic underflow\")".into()
                            }
                            Machine::RaiseOverflow => {
                                "h2r_rt::raise_arithmetic(\"arithmetic overflow\")".into()
                            }
                            Machine::AbsentError => format!("h2r_rt::absent_error({})", a[0]),
                            Machine::NoDuplicate => a[0].clone(),
                            Machine::Memcpy => format!(
                                "{{ HBytes::copy(&{}, 0, &{}, 0, {}); ({}, HAddr::literal(b\"\")) }}",
                                a[1], a[0], a[2], a[3]
                            ),
                            Machine::RealWorld => "0".into(),
                            Machine::NewByteArray => format!("({}, HBytes::new({}))", a[1], a[0]),
                            Machine::ReadWordArray | Machine::ReadIntArray => {
                                format!("({}, {}.index_word({}))", a[2], a[0], a[1])
                            }
                            Machine::WriteWordArray | Machine::WriteIntArray => {
                                format!("{{ {}.write_word({}, {}); {} }}", a[0], a[1], a[2], a[3])
                            }
                            Machine::IndexWordArray | Machine::IndexIntArray => {
                                format!("{}.index_word({})", a[0], a[1])
                            }
                            Machine::SizeofByteArray => format!("{}.size()", a[0]),
                            Machine::GetSizeofMutableByteArray => {
                                format!("({}, {}.size())", a[1], a[0])
                            }
                            Machine::ShrinkMutableByteArray => {
                                format!("{{ {}.shrink({}); {} }}", a[0], a[1], a[2])
                            }
                            Machine::UnsafeFreezeByteArray => format!("({}, {})", a[1], a[0]),
                            Machine::CopyByteArray | Machine::CopyMutableByteArray => format!(
                                "{{ HBytes::copy(&{}, {}, &{}, {}, {}); {} }}",
                                a[0], a[1], a[2], a[3], a[4], a[5]
                            ),
                            Machine::SetByteArray => {
                                format!(
                                    "{{ {}.set({}, {}, {}); {} }}",
                                    a[0], a[1], a[2], a[3], a[4]
                                )
                            }
                            Machine::NewArray => format!(
                                "({}, HArray::new({}, {}))",
                                a[2],
                                a[0],
                                pack(world, &type_arguments[1], &a[1])
                            ),
                            Machine::ReadArray => {
                                format!("({}, {}.read({}).{}())", a[2], a[0], a[1], element(2).1)
                            }
                            Machine::WriteArray => format!(
                                "{{ {}.write({}, {}); {} }}",
                                a[0],
                                a[1],
                                pack(world, &type_arguments[2], &a[2]),
                                a[3]
                            ),
                            Machine::IndexArray => {
                                format!("({}.read({}).{}(),)", a[0], a[1], element(1).1)
                            }
                            Machine::UnsafeFreezeArray | Machine::UnsafeThawArray => {
                                format!("({}, {})", a[1], a[0])
                            }
                        }
                    }
                    Operation::IndexCharAddr { arguments } => {
                        format!("v{}.index_char(v{})", arguments[0].0, arguments[1].0)
                    }
                    Operation::PlusAddr { arguments } => {
                        format!("v{}.plus(v{})", arguments[0].0, arguments[1].0)
                    }
                    Operation::AddrLiteral(bytes) => {
                        let bytes: String =
                            bytes.iter().map(|byte| format!("\\x{byte:02x}")).collect();
                        format!("HAddr::literal(b\"{bytes}\\x00\")")
                    }
                    Operation::WordBinary { op, arguments } => {
                        let (left, right) = (arguments[0].0, arguments[1].0);
                        match op {
                            IntBinary::Subtract => format!("v{left}.wrapping_sub(v{right})"),
                            IntBinary::And => format!("v{left} & v{right}"),
                            _ => return Err(format!("unsupported Word# operation {op:?}")),
                        }
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
                    Operation::Move(v) => {
                        let from = carrier(world, value_ty(*v));
                        let to = carrier(world, &instruction.result.ty);
                        if from == to {
                            value(*v)
                        } else if to == "HField" {
                            pack(world, value_ty(*v), &value(*v))
                        } else if from == "HField" {
                            format!(
                                "{}.{}()",
                                value(*v),
                                field_kind(world, &instruction.result.ty).1
                            )
                        } else {
                            return Err(format!("a move changes its carrier from {from} to {to}"));
                        }
                    }
                    Operation::PendingCell => {
                        format!("{}::pending()", carrier(world, &instruction.result.ty))
                    }
                    Operation::FillCell {
                        cell,
                        value: filled,
                    } => format!(
                        "{{ v{}.fill(v{}.clone()); v{}.clone() }}",
                        cell.0, filled.0, cell.0
                    ),
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
                            IntBinary::And => format!("v{left} & v{right}"),
                            IntBinary::Or => format!("v{left} | v{right}"),
                            IntBinary::Quot => format!("v{left}.wrapping_div(v{right})"),
                            IntBinary::Rem => format!("v{left}.wrapping_rem(v{right})"),
                        }
                    }
                    Operation::Literal(lit)
                        if carrier(world, &instruction.result.ty) == "HBytes" =>
                    {
                        let limbs: Vec<String> = big_nat_limbs(lit)?
                            .iter()
                            .map(|limb| format!("{limb:#x}"))
                            .collect();
                        format!("HBytes::from_words(&[{}])", limbs.join(", "))
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
                        if callee.blocks[0].params.is_empty() {
                            format!("f_{target}()")
                        } else {
                            closure(
                                world,
                                &format!("f_{target}"),
                                (unlifted(callee, &callee.blocks[0]).as_deref() == Some("i64")
                                    && has_boxed)
                                    .then(|| format!("s_{target}_{}", callee.entry.0))
                                    .as_deref(),
                                &[],
                                &callee.blocks[0]
                                    .params
                                    .iter()
                                    .map(|p| &*p.ty)
                                    .collect::<Vec<_>>(),
                                &callee.result_ty,
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
                        let takes = leaves[&target].function.blocks[0].params.len();
                        if takes != arguments.len() {
                            let name = |index: usize| {
                                let instance = &specialization.instances[index];
                                world.at(instance.module).map_or_else(
                                    |_| format!("instance {index}"),
                                    |module| module.binder(instance.binder).name.clone(),
                                )
                            };
                            return Err(format!(
                                "emitted target parameter count disagrees with call: {} calls {} with {} arguments, it takes {takes}",
                                name(index),
                                name(target),
                                arguments.len()
                            ));
                        }
                        let args = arguments
                            .iter()
                            .map(|arg| value(*arg))
                            .collect::<Vec<_>>()
                            .join(", ");
                        format!("f_{target}({args})")
                    }
                    Operation::Force(v) => format!("{{ v{0}.force(); v{0}.clone() }}", v.0),
                };
                if diverges(&instruction.operation) {
                    writeln!(out, "    {expression}").unwrap();
                    tail_transfer = true;
                    break;
                }
                writeln!(
                    out,
                    "    let v{}: {} = {expression};",
                    instruction.result.id.0,
                    carrier(world, &instruction.result.ty)
                )
                .unwrap();
            }
            at.set(block.instructions.len());
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
            let transfer =
                |target: &crate::nir::BlockId, args: &[crate::nir::ValueId]| match stepped {
                    Some(_) => step_to(
                        &format!("s_{index}_{}", target.0),
                        &args
                            .iter()
                            .map(|v| value(*v))
                            .collect::<Vec<_>>()
                            .join(", "),
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
                        match stepped {
                            Some(_) => format!("h2r_rt::Step::Done({})", value(*v)),
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

// ghc-bignum's native BigNat# is its little-endian limbs with no leading zero limb.
pub(crate) fn big_nat_limbs(lit: &h2r_core_ir::Lit) -> Result<Vec<u64>, String> {
    let (Some("BigNat"), Some(decimal)) = (lit.num_type.as_deref(), lit.value.as_deref()) else {
        return Err(format!(
            "a ByteArray# literal must be a BigNat, not {}",
            lit.pretty
        ));
    };
    let mut limbs: Vec<u64> = Vec::new();
    for digit in decimal.bytes() {
        if !digit.is_ascii_digit() {
            return Err(format!("a BigNat literal is decimal, not {decimal:?}"));
        }
        let mut carry = u128::from(digit - b'0');
        for limb in &mut limbs {
            let next = u128::from(*limb) * 10 + carry;
            *limb = next as u64;
            carry = next >> 64;
        }
        if carry != 0 {
            limbs.push(carry as u64);
        }
    }
    Ok(limbs)
}

enum Shape {
    Int,
    Bool {
        false_: String,
        true_: String,
    },
    String,
    List(Ty),
    Maybe {
        nothing: String,
        just: String,
        element: Ty,
    },
    Either {
        left: (String, Ty),
        right: (String, Ty),
    },
    Tuple {
        constructor: String,
        fields: Vec<Ty>,
    },
    Function {
        arguments: Vec<Ty>,
        result: Ty,
    },
}

fn shape(world: &World<'_>, ty: &Ty) -> Result<Shape, String> {
    let ty = represented(world, ty);
    if boxed::is_int(&ty) {
        return Ok(Shape::Int);
    }
    if let Ty::Fun { .. } = ty {
        let mut arguments = Vec::new();
        let mut result = ty;
        while let Ty::Fun { arg, res, .. } = result {
            arguments.push(*arg);
            result = represented(world, &res);
        }
        return Ok(Shape::Function { arguments, result });
    }
    if let Some(element) = ty.list_elem() {
        return Ok(if element.is_char() {
            Shape::String
        } else {
            Shape::List(element.clone())
        });
    }
    let refuse = || {
        format!(
            "a typed API carries Int, Bool, String, lists, Maybe, Either, tuples and functions, not {}",
            ty.render()
        )
    };
    let Ty::Con { tycon, .. } = &ty else {
        return Err(refuse());
    };
    let mut family = data::family(world, &ty)?;
    family.sort_by_key(|constructor| constructor.tag);
    match (tycon.name.as_str(), family.as_mut_slice()) {
        ("$ghc-prim$GHC.Types$Bool", [false_, true_]) => Ok(Shape::Bool {
            false_: false_.name.clone(),
            true_: true_.name.clone(),
        }),
        ("$base$GHC.Maybe$Maybe", [nothing, just]) if just.fields.len() == 1 => Ok(Shape::Maybe {
            nothing: nothing.name.clone(),
            just: just.name.clone(),
            element: just.fields.remove(0),
        }),
        ("$base$Data.Either$Either", [left, right])
            if left.fields.len() == 1 && right.fields.len() == 1 =>
        {
            Ok(Shape::Either {
                left: (left.name.clone(), left.fields.remove(0)),
                right: (right.name.clone(), right.fields.remove(0)),
            })
        }
        (_, [tuple]) if tycon.occ.starts_with("(,") => Ok(Shape::Tuple {
            constructor: tuple.name.clone(),
            fields: std::mem::take(&mut tuple.fields),
        }),
        _ => Err(refuse()),
    }
}

fn list_names(world: &World<'_>, element: &Ty) -> Result<String, String> {
    let (nil, cons) = data::list_layouts(world, element)?;
    Ok(format!(
        "HListNames {{ cons: {:?}, nil: {:?} }}",
        cons.name, nil.name
    ))
}

fn rust_type(world: &World<'_>, ty: &Ty) -> Result<String, String> {
    Ok(match shape(world, ty)? {
        Shape::Int => "i64".into(),
        Shape::Bool { .. } => "bool".into(),
        Shape::String => "String".into(),
        Shape::List(element) => format!("Vec<{}>", rust_type(world, &element)?),
        Shape::Maybe { element, .. } => format!("Option<{}>", rust_type(world, &element)?),
        Shape::Either { left, right } => format!(
            "Result<{}, {}>",
            rust_type(world, &right.1)?,
            rust_type(world, &left.1)?
        ),
        Shape::Function { arguments, result } => format!(
            "std::rc::Rc<dyn Fn({}) -> {}>",
            arguments
                .iter()
                .map(|argument| rust_type(world, argument))
                .collect::<Result<Vec<_>, _>>()?
                .join(", "),
            rust_type(world, &result)?
        ),
        Shape::Tuple { fields, .. } => format!(
            "({})",
            fields
                .iter()
                .map(|field| rust_type(world, field))
                .collect::<Result<Vec<_>, _>>()?
                .join(", ")
        ),
    })
}

fn into_field(world: &World<'_>, ty: &Ty, value: &str) -> Result<String, String> {
    Ok(match shape(world, ty)? {
        Shape::Int => format!("HField::Int(HInt::ready({value}))"),
        Shape::Bool { false_, true_ } => {
            format!(
                "HField::Data(HData::ready(if {value} {{ {true_:?} }} else {{ {false_:?} }}, []))"
            )
        }
        Shape::String => format!(
            "HField::Data(h2r_rt::string_argument(&{value}, {}))",
            string_names(world)?
        ),
        Shape::List(element) => format!(
            "HField::Data(h2r_rt::list_argument({value}.into_iter().map(|e| {}).collect(), {}))",
            into_field(world, &element, "e")?,
            list_names(world, &element)?
        ),
        Shape::Maybe {
            nothing,
            just,
            element,
        } => format!(
            "HField::Data(match {value} {{ Some(e) => HData::ready({just:?}, [{}]), None => HData::ready({nothing:?}, []) }})",
            into_field(world, &element, "e")?
        ),
        Shape::Either { left, right } => format!(
            "HField::Data(match {value} {{ Ok(e) => HData::ready({:?}, [{}]), Err(e) => HData::ready({:?}, [{}]) }})",
            right.0,
            into_field(world, &right.1, "e")?,
            left.0,
            into_field(world, &left.1, "e")?
        ),
        Shape::Function { arguments, result } => {
            let read = arguments
                .iter()
                .enumerate()
                .map(|(index, argument)| from_field(world, argument, &format!("a[{index}]")))
                .collect::<Result<Vec<_>, _>>()?
                .join(", ");
            format!(
                "HField::Closure({{ let f = {value}; HClosure::ready({}, move |a| {{ let r = f({read}); {} }}) }})",
                arguments.len(),
                into_field(world, &result, "r")?
            )
        }
        Shape::Tuple {
            constructor,
            fields,
        } => {
            let components = fields
                .iter()
                .enumerate()
                .map(|(index, field)| into_field(world, field, &format!("t.{index}")))
                .collect::<Result<Vec<_>, _>>()?
                .join(", ");
            let collection = if fields.len() <= 3 { "" } else { "vec!" };
            format!(
                "HField::Data({{ let t = {value}; HData::ready({constructor:?}, {collection}[{components}]) }})"
            )
        }
    })
}

fn from_field(world: &World<'_>, ty: &Ty, field: &str) -> Result<String, String> {
    Ok(match shape(world, ty)? {
        Shape::Int => format!("{field}.int().force()"),
        Shape::Bool { true_, .. } => {
            format!("{{ let d = {field}.data(); d.force().constructor == {true_:?} }}")
        }
        Shape::String => format!(
            "h2r_rt::string_value(&{field}.data(), {})",
            string_names(world)?
        ),
        Shape::List(element) => format!(
            "h2r_rt::list_fields(&{field}.data(), {}).into_iter().map(|e| {}).collect::<Vec<_>>()",
            list_names(world, &element)?,
            from_field(world, &element, "e")?
        ),
        Shape::Maybe { just, element, .. } => format!(
            "{{ let d = {field}.data(); let n = d.force(); if n.constructor == {just:?} {{ Some({}) }} else {{ None }} }}",
            from_field(world, &element, "n.fields[0]")?
        ),
        Shape::Either { left, right } => format!(
            "{{ let d = {field}.data(); let n = d.force(); if n.constructor == {:?} {{ Ok({}) }} else {{ Err({}) }} }}",
            right.0,
            from_field(world, &right.1, "n.fields[0]")?,
            from_field(world, &left.1, "n.fields[0]")?
        ),
        Shape::Function { .. } => {
            return Err(
                "a typed API passes Rust functions into Haskell and returns no Haskell function"
                    .into(),
            );
        }
        Shape::Tuple { fields, .. } => {
            let components = fields
                .iter()
                .enumerate()
                .map(|(index, field)| from_field(world, field, &format!("n.fields[{index}]")))
                .collect::<Result<Vec<_>, _>>()?;
            let components = match components.as_slice() {
                [one] => format!("{one},"),
                many => many.join(", "),
            };
            format!("{{ let d = {field}.data(); let n = d.force(); ({components}) }}")
        }
    })
}

fn api_function(
    world: &World<'_>,
    adapter: &mut String,
    entry: &str,
    adapter_name: &str,
    entry_types: &[&Ty],
    entry_result: &Ty,
) -> Result<(), String> {
    let occ = entry.rsplit('$').next().unwrap_or_default();
    if !occ.starts_with(|c: char| c.is_ascii_lowercase() || c == '_')
        || !occ.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
    {
        return Err(format!(
            "a typed API names its function after the entry, and {occ:?} is not a Rust identifier"
        ));
    }
    let name: String = occ
        .chars()
        .flat_map(|c| {
            let separator = c.is_ascii_uppercase().then_some('_');
            separator
                .into_iter()
                .chain(std::iter::once(c.to_ascii_lowercase()))
        })
        .collect();
    let parameters = entry_types
        .iter()
        .enumerate()
        .map(|(index, ty)| Ok(format!("a{index}: {}", rust_type(world, ty)?)))
        .collect::<Result<Vec<_>, String>>()?
        .join(", ");
    let arguments = entry_types
        .iter()
        .enumerate()
        .map(|(index, ty)| {
            Ok(unpack(
                world,
                ty,
                &format!("({})", into_field(world, ty, &format!("a{index}"))?),
            ))
        })
        .collect::<Result<Vec<_>, String>>()?
        .join(", ");
    let result = pack(world, entry_result, &format!("{adapter_name}({arguments})"));
    writeln!(
        adapter,
        "pub fn {name}({parameters}) -> {} {{\n    let r = {result};\n    {}\n}}",
        rust_type(world, entry_result)?,
        from_field(world, entry_result, "r")?
    )
    .unwrap();
    Ok(())
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

fn operands(operation: &Operation) -> Vec<(crate::nir::ValueId, bool)> {
    let moved = |values: &[crate::nir::ValueId]| values.iter().map(|v| (*v, true)).collect();
    let read = |values: &[crate::nir::ValueId]| values.iter().map(|v| (*v, false)).collect();
    match operation {
        Operation::MakeClosure { arguments, .. }
        | Operation::LocalScope { arguments, .. }
        | Operation::CallLocal { arguments, .. }
        | Operation::Construct { arguments, .. }
        | Operation::MakeUnboxedTuple { arguments }
        | Operation::DelayBlock { arguments, .. }
        | Operation::EvaluateBlock { arguments, .. }
        | Operation::CallTop { arguments, .. } => moved(arguments),
        Operation::UnboxedTupleField { tuple: v, .. } | Operation::Move(v) => moved(&[*v]),
        Operation::AppendList { left, right, .. } => moved(&[*left, *right]),
        Operation::Apply { callee, arguments } => {
            let mut uses: Vec<_> = moved(arguments);
            uses.push((*callee, false));
            uses
        }
        Operation::MatchData {
            scrutinee,
            arguments,
            ..
        } => {
            let mut uses: Vec<_> = moved(arguments);
            uses.push((*scrutinee, false));
            uses
        }
        Operation::IntBinary { arguments, .. }
        | Operation::CharCompare { arguments, .. }
        | Operation::WordCompare { arguments, .. }
        | Operation::WordBinary { arguments, .. }
        | Operation::IndexCharAddr { arguments }
        | Operation::PlusAddr { arguments }
        | Operation::Machine { arguments, .. } => read(arguments),
        Operation::BoxInt(v)
        | Operation::UnboxInt(v)
        | Operation::IntToWord(v)
        | Operation::WordToInt(v)
        | Operation::NegateInt(v)
        | Operation::OrdChar(v)
        | Operation::ChrChar(v)
        | Operation::Force(v)
        | Operation::DataToTag { value: v, .. }
        | Operation::TagToEnum { tag: v, .. }
        | Operation::RaiseError { message: v }
        | Operation::EmptyCase { scrutinee: v } => read(&[*v]),
        Operation::FillCell { cell, value } => read(&[*cell, *value]),
        Operation::PointerEquality { left, right } => read(&[*left, *right]),
        Operation::UnpackString(unpack) => read(unpack.tail.as_slice()),
        Operation::ListPredicate(predicate) => read(&[predicate.left, predicate.right]),
        Operation::ListFunction(function) => read(&function.arguments),
        Operation::CompareStrings(compare) => read(&[compare.left, compare.right]),
        Operation::RaiseCallStackError(error) => read(&[error.message, error.stack]),
        Operation::AddrLiteral(_)
        | Operation::PendingCell
        | Operation::Literal(_)
        | Operation::TopReference { .. } => Vec::new(),
    }
}

fn last_uses(block: &Block) -> BTreeMap<crate::nir::ValueId, (usize, bool)> {
    let mut last: BTreeMap<crate::nir::ValueId, (usize, bool)> = BTreeMap::new();
    let mut record = |position: usize, id: crate::nir::ValueId, moved: bool| match last.get_mut(&id)
    {
        Some(entry) if entry.0 == position => entry.1 = false,
        _ => {
            last.insert(id, (position, moved));
        }
    };
    for (position, instruction) in block.instructions.iter().enumerate() {
        for (id, moved) in operands(&instruction.operation) {
            record(position, id, moved);
        }
    }
    let end = block.instructions.len();
    match &block.terminator.exit {
        Exit::Return(v) => record(end, *v, true),
        Exit::Jump { args, .. } => {
            for v in args {
                record(end, *v, true);
            }
        }
        Exit::IntSwitch {
            scrutinee, args, ..
        } => {
            record(end, *scrutinee, false);
            for v in args {
                record(end, *v, true);
            }
        }
        Exit::Diverge { .. } => {}
    }
    last
}

fn diverges(operation: &Operation) -> bool {
    matches!(
        operation,
        Operation::RaiseError { .. }
            | Operation::RaiseCallStackError(_)
            | Operation::EmptyCase { .. }
            | Operation::Machine {
                op: Machine::Raise
                    | Machine::RaiseDivZero
                    | Machine::RaiseUnderflow
                    | Machine::RaiseOverflow
                    | Machine::AbsentError,
                ..
            }
    )
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
        format!(
            "{{ let _ = precedence; h2r_rt::show_char(&value.data(), {}) }}",
            string_names(world)?
        )
    } else if ty.list_elem().is_some_and(Ty::is_char) {
        format!(
            "{{ let _ = precedence; h2r_rt::show_string(&value.data(), {}) }}",
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
            "{{ let _ = precedence; let data = value.data(); let node = data.force(); match node.constructor {{ {arms}other => panic!(\"show: {{other}} is not in this family\") }} }}"
        )
    } else {
        return Err(format!("CLI adapter cannot show a value of type {key}"));
    };
    shows.functions.push(format!(
        "#[allow(dead_code)]\nfn {name}(value: &HField, precedence: u8) -> String {{ {body} }}\n"
    ));
    Ok(name)
}
