//! Constructor layouts come from GHC worker signatures, never printed types.
//!
//! Layouts are whole-world facts. A function from one module, specialized at a
//! type declared in another, needs that other module's constructor evidence, so
//! every query here searches the loaded world rather than one module's table.
//! The same constructor appears in every module that mentions it; those entries
//! must agree, and a disagreement is an error rather than a first-wins pick.

use h2r_core_ir::{Expr, ExprId, Module, Ty, raw::ConstructorInfo};

use super::linkage::closed_type;
use super::{World, boxed, instantiate, primitive};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Constructor {
    pub name: String,
    pub tag: u32,
    pub result: Ty,
    pub fields: Vec<Ty>,
    pub strict: Vec<bool>,
}

/// How many newtype layers [`represented`] will peel before giving up. A
/// newtype cannot wrap itself directly, but a chain can be arbitrarily long,
/// and a dump that claims a cycle must refuse rather than loop.
const NEWTYPE_DEPTH: usize = 32;

/// The one field of a newtype, instantiated at this type's arguments, or
/// `None` when this is not a newtype.
///
/// A newtype has no runtime existence: `newtype N = MkN T` *is* `T` once the
/// program runs, which is why GHC turns every wrap and unwrap into a cast
/// rather than a constructor. The evidence is the declaring module's own —
/// `newtype`, a representation arity of one, a family of one — and the field
/// comes from the worker's signature, never from the name.
fn newtype_field(world: &World<'_>, ty: &Ty) -> Result<Option<Ty>, String> {
    let Ty::Con { tycon, args } = ty else {
        return Ok(None);
    };
    let Some(module) = declaring(world, &tycon.name)? else {
        return Ok(None);
    };
    let found: Vec<_> = module
        .constructors
        .iter()
        .filter(|c| c.family == tycon.name)
        .collect();
    let [info] = found.as_slice() else {
        return Ok(None);
    };
    if info.newtype != Some(true) || info.rep_arity != 1 || info.family_size != 1 {
        return Ok(None);
    }
    let signature = module
        .types
        .get(info.signature as usize)
        .ok_or("invalid constructor signature index")?;
    let instantiated = instantiate::apply(signature, args)?;
    let Ty::Fun { arg, res, .. } = &instantiated else {
        return Err("a newtype's worker is not a one-argument function".into());
    };
    if !res.alpha_eq(ty) {
        return Err("a newtype's worker does not return its own type".into());
    }
    Ok(Some((**arg).clone()))
}

/// The component types of an unboxed tuple, in runtime order, or `None` when
/// this type is not one.
///
/// An unboxed tuple has no heap object, no tag and no laziness: it *is* its
/// components, side by side, and GHC's type system already guarantees it is
/// never bound lazily, stored in a lifted field or passed where a value is
/// expected. So there is nothing to allocate and nothing to force — the only
/// question is what the components are, and the worker's signature answers it.
pub fn unboxed_tuple_fields(world: &World<'_>, ty: &Ty) -> Result<Option<Vec<Ty>>, String> {
    Ok(unboxed_tuple_constructor(world, ty)?.map(|(_, fields)| fields))
}

/// The one constructor of an unboxed tuple and its components, so a `case` can
/// check the pattern it matched is the only one the family has.
pub fn unboxed_tuple_constructor(
    world: &World<'_>,
    ty: &Ty,
) -> Result<Option<(String, Vec<Ty>)>, String> {
    let Ty::Con { tycon, args } = ty else {
        return Ok(None);
    };
    let Some(module) = declaring(world, &tycon.name)? else {
        return Ok(None);
    };
    let found: Vec<_> = module
        .constructors
        .iter()
        .filter(|c| c.family == tycon.name)
        .collect();
    let [info] = found.as_slice() else {
        return Ok(None);
    };
    if !info.unboxed_tuple() {
        return Ok(None);
    }
    let signature = module
        .types
        .get(info.signature as usize)
        .ok_or("invalid constructor signature index")?;
    // The worker is quantified over the components' runtime representations as
    // well as the components themselves, so the type arguments that reach it
    // are more than this type's own. `apply` drops the leading quantifiers it
    // is given arguments for; the representation ones carry no value.
    let instantiated = instantiate::apply(signature, args)?;
    let mut fields = Vec::new();
    let mut remaining = &instantiated;
    while let Ty::Fun { arg, res, .. } = remaining {
        fields.push((**arg).clone());
        remaining = res;
    }
    if fields.len() != info.rep_arity as usize {
        return Err(format!(
            "an unboxed tuple worker takes {} arguments, not its representation arity {}",
            fields.len(),
            info.rep_arity
        ));
    }
    if !remaining.alpha_eq(ty) {
        return Err("an unboxed tuple worker does not return its own type".into());
    }
    Ok(Some((info.name.clone(), fields)))
}

/// The type a value of this type is actually held as, with newtypes peeled
/// away. Every carrier question is asked of this rather than of the source
/// type, so `Id` and the `Int` it wraps are one value and the cast between
/// them moves nothing.
pub fn represented(world: &World<'_>, ty: &Ty) -> Option<Ty> {
    let mut current = ty.clone();
    for _ in 0..NEWTYPE_DEPTH {
        match newtype_field(world, &current) {
            Ok(Some(inner)) => current = inner,
            Ok(None) => return Some(current),
            Err(_) => return None,
        }
    }
    None
}

/// Does any readable module carry a usable constructor of this family? Asked
/// of the representation, so a newtype answers for what it wraps.
pub fn is_data(world: &World<'_>, ty: &Ty) -> bool {
    represented(world, ty).is_some_and(|ty| is_data_directly(world, &ty))
}

fn is_data_directly(world: &World<'_>, ty: &Ty) -> bool {
    !boxed::is_int(ty)
        && closed_type(ty)
        && matches!(ty, Ty::Con { tycon, .. } if family_tables(world, &tycon.name)
            .iter()
            .any(|(_, _, here)| here.iter().any(|c| c.boxed_record())))
}

fn family_tables<'a>(
    world: &World<'a>,
    family: &str,
) -> Vec<(usize, &'a Module, Vec<&'a ConstructorInfo>)> {
    let mut tables: Vec<(usize, &'a Module, Vec<&'a ConstructorInfo>)> = Vec::new();
    if let (Some(catalog), Some(modules)) = (world.catalog, world.modules) {
        for &(index, position) in catalog.family(family) {
            let module = &modules[index];
            match tables.last_mut() {
                Some((last, _, here)) if *last == index => {
                    here.push(&module.constructors[position])
                }
                _ => tables.push((index, module, vec![&module.constructors[position]])),
            }
        }
        return tables;
    }
    for (index, module) in world.iter() {
        let here: Vec<&ConstructorInfo> = module
            .constructors
            .iter()
            .filter(|c| c.family == family)
            .collect();
        if !here.is_empty() {
            tables.push((index, module, here));
        }
    }
    tables
}

pub fn lifted(world: &World<'_>, ty: &Ty) -> bool {
    matches!(
        carrier(world, ty),
        Some(Carrier::Int | Carrier::Data | Carrier::Function | Carrier::Dynamic)
    )
}

pub const ERASED: &str = "$h2r$H2R.Erased$Erased";

pub fn erased_ty() -> Ty {
    Ty::Con {
        tycon: h2r_core_ir::TyConId {
            name: ERASED.into(),
            occ: "Erased".into(),
            unique: Default::default(),
        },
        args: vec![],
    }
}

pub fn is_erased(ty: &Ty) -> bool {
    match ty {
        Ty::Con { tycon, .. } => tycon.name == ERASED,
        Ty::App { fun, .. } => is_erased(fun),
        _ => false,
    }
}

pub fn erase_free(mut ty: Ty) -> Ty {
    for unique in super::subst::free_uniques(&ty) {
        super::subst::substitute_capture_safe(&mut ty, &unique, &erased_ty());
    }
    ty
}

pub fn erase_quantifiers(ty: &Ty) -> Ty {
    let mut current = ty.clone();
    while let Ty::ForAll { binder, body } = current {
        let mut body = *body;
        super::subst::substitute_capture_safe(&mut body, &binder.unique, &erased_ty());
        current = body;
    }
    current
}

pub fn same_representation(world: &World<'_>, left: &Ty, right: &Ty) -> bool {
    if left.alpha_eq(right) {
        return true;
    }
    if matches!(left, Ty::ForAll { .. }) || matches!(right, Ty::ForAll { .. }) {
        return same_representation(world, &erase_quantifiers(left), &erase_quantifiers(right));
    }
    if let (
        Ty::Fun {
            arg: la, res: lr, ..
        },
        Ty::Fun {
            arg: ra, res: rr, ..
        },
    ) = (left, right)
    {
        return same_representation(world, la, ra) && same_representation(world, lr, rr);
    }
    let (Some(l), Some(r)) = (represented(world, left), represented(world, right)) else {
        return false;
    };
    if l.alpha_eq(left) && r.alpha_eq(right) {
        return false;
    }
    same_representation(world, &l, &r)
}

pub fn function(world: &World<'_>, ty: &Ty) -> bool {
    represented(world, ty).is_some_and(|ty| function_directly(world, &erase_quantifiers(&ty)))
}

fn function_directly(world: &World<'_>, ty: &Ty) -> bool {
    matches!(ty, Ty::Fun { arg, res, .. }
        if closed_type(ty) && supported(world, arg) && supported(world, res))
}

/// Whether two values of these types can be compared as heap objects: both
/// held in one shared carrier, a boxed `Int` or algebraic data.
pub fn same_heap_carrier(world: &World<'_>, left: &Ty, right: &Ty) -> bool {
    matches!(
        (carrier(world, left), carrier(world, right)),
        (Some(Carrier::Int), Some(Carrier::Int)) | (Some(Carrier::Data), Some(Carrier::Data))
    )
}

pub fn supported(world: &World<'_>, ty: &Ty) -> bool {
    carrier(world, ty).is_some()
}

/// How a value of this type is held at run time.
///
/// Two types a coercion relates must agree here before the cast between them
/// can be erased: a coercion has no runtime content, but this backend's NIR is
/// typed, and a value read at the wrong carrier is a miscompile. This is the
/// one definition of the question — the Rust backend names the same four
/// cases rather than deciding them again.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Carrier {
    /// An unboxed scalar in a machine word: `Int#`, `Char#`.
    Scalar,
    /// A shared, call-by-need boxed `Int`.
    Int,
    /// A shared, call-by-need algebraic value.
    Data,
    /// A shared, call-by-need function value.
    Function,
    /// Several values side by side, with no box around them: GHC's unboxed
    /// tuple. It holds no representation of its own, so what its components
    /// are is read from the type with [`unboxed_tuple_fields`] rather than
    /// carried here.
    Tuple,
    Address,
    MutVar,
    Bytes,
    Array,
    Dynamic,
}

pub fn carrier(world: &World<'_>, ty: &Ty) -> Option<Carrier> {
    let ty = represented(world, ty)?;
    if let Ty::ForAll { .. } = ty {
        return carrier(world, &erase_quantifiers(&ty));
    }
    if is_erased(&ty) {
        return Some(Carrier::Dynamic);
    }
    if primitive::is_scalar(&ty) {
        Some(Carrier::Scalar)
    } else if boxed::is_int(&ty) {
        Some(Carrier::Int)
    } else if function_directly(world, &ty) {
        Some(Carrier::Function)
    } else if is_data_directly(world, &ty) {
        Some(Carrier::Data)
    } else if unboxed_tuple_carried(world, &ty) {
        Some(Carrier::Tuple)
    } else if primitive::is_addr(&ty) {
        Some(Carrier::Address)
    } else if primitive::is_mut_var(&ty) && lifted(world, &ty.args()[2]) {
        Some(Carrier::MutVar)
    } else if primitive::is_bytes(&ty) {
        Some(Carrier::Bytes)
    } else if primitive::array_element(&ty).is_some_and(|element| lifted(world, element)) {
        Some(Carrier::Array)
    } else {
        None
    }
}

/// An unboxed tuple every one of whose components this backend can carry. A
/// component it cannot carry is refused here rather than at the point of use,
/// so the refusal names the tuple rather than whatever happened to read it.
fn unboxed_tuple_carried(world: &World<'_>, ty: &Ty) -> bool {
    matches!(unboxed_tuple_fields(world, ty), Ok(Some(fields))
        if fields.iter().all(|field| carrier(world, field).is_some()))
}

/// The module whose table the family's layouts are read from, with every other
/// module's entries checked to agree. A constructor that two modules describe
/// differently is an error, not a first-wins pick.
fn declaring<'a>(world: &World<'a>, family: &str) -> Result<Option<&'a Module>, String> {
    if let (Some(catalog), Some(modules)) = (world.catalog, world.modules) {
        let chosen = match catalog.declaring(family) {
            Some(chosen) => chosen,
            None => {
                let chosen = agreeing(world, family);
                catalog.declare(family, chosen.clone());
                chosen
            }
        };
        return chosen.map(|index| index.map(|index| &modules[index]));
    }
    agreeing(world, family)
        .map(|index| index.map(|index| world.at(index).expect("a readable module")))
}

fn agreeing(world: &World<'_>, family: &str) -> Result<Option<usize>, String> {
    let tables = family_tables(world, family);
    let Some((chosen, first, there)) = tables.first() else {
        return Ok(None);
    };
    for (_, module, here) in &tables[1..] {
        if here.len() != there.len()
            || here.iter().zip(there.iter()).any(|(a, b)| {
                (
                    &a.name,
                    a.tag,
                    a.family_size,
                    a.rep_arity,
                    &a.strict,
                    a.boxed_record(),
                ) != (
                    &b.name,
                    b.tag,
                    b.family_size,
                    b.rep_arity,
                    &b.strict,
                    b.boxed_record(),
                ) || !module
                    .types
                    .get(a.signature as usize)
                    .zip(first.types.get(b.signature as usize))
                    .is_some_and(|(x, y)| x.alpha_eq(y))
            })
        {
            return Err("modules disagree about a constructor family's layout".into());
        }
    }
    Ok(Some(*chosen))
}

pub fn layout(world: &World<'_>, name: &str, ty: &Ty) -> Result<Constructor, String> {
    let Ty::Con { tycon, args } = ty else {
        return Err("constructor requires an algebraic result type".into());
    };
    let module =
        declaring(world, &tycon.name)?.ok_or("missing or ambiguous constructor layout evidence")?;
    let found: Vec<_> = module
        .constructors
        .iter()
        .filter(|c| c.name == name && c.family == tycon.name)
        .collect();
    let [info] = found.as_slice() else {
        return Err("missing or ambiguous constructor layout evidence".into());
    };
    if !info.boxed_record() || info.tag == 0 || boxed::is_int(ty) {
        return Err("unsupported constructor family or representation".into());
    }
    let signature = module
        .types
        .get(info.signature as usize)
        .ok_or("invalid constructor signature index")?;
    let instantiated = instantiate::apply(signature, args)?;
    let mut result = &instantiated;
    let mut fields = Vec::new();
    while let Ty::Fun { arg, res, .. } = result {
        if !supported(world, arg) {
            return Err("unsupported constructor field carrier".into());
        }
        fields.push((**arg).clone());
        result = res;
    }
    if !result.alpha_eq(ty)
        || fields.len() != info.rep_arity as usize
        || fields.len() != info.strict.len()
    {
        return Err("constructor worker signature/layout mismatch".into());
    }
    Ok(Constructor {
        name: name.into(),
        tag: info.tag,
        result: ty.clone(),
        fields,
        strict: info.strict.clone(),
    })
}

/// The two cells of `[element]`, read out of the loaded world. Code that fills
/// a list cell is handed the layout; it never assumes the shape of one.
pub fn list_layouts(world: &World<'_>, element: &Ty) -> Result<(Constructor, Constructor), String> {
    let list = Ty::Con {
        tycon: h2r_core_ir::TyConId {
            name: h2r_core_ir::LIST_TYCON.into(),
            occ: "List".into(),
            unique: Default::default(),
        },
        args: vec![element.clone()],
    };
    let nil = layout(world, "$ghc-prim$GHC.Types$[]", &list)?;
    let cons = layout(world, "$ghc-prim$GHC.Types$:", &list)?;
    if !nil.fields.is_empty()
        || cons.fields.len() != 2
        || !cons.fields[0].alpha_eq(element)
        || !cons.fields[1].alpha_eq(&list)
    {
        return Err("the loaded world's list layout is not the expected one".into());
    }
    Ok((nil, cons))
}

pub fn bool_ty() -> Ty {
    Ty::Con {
        tycon: h2r_core_ir::TyConId {
            name: "$ghc-prim$GHC.Types$Bool".into(),
            occ: "Bool".into(),
            unique: Default::default(),
        },
        args: vec![],
    }
}

pub fn ordering_ty() -> Ty {
    Ty::Con {
        tycon: h2r_core_ir::TyConId {
            name: "$ghc-prim$GHC.Types$Ordering".into(),
            occ: "Ordering".into(),
            unique: Default::default(),
        },
        args: vec![],
    }
}

/// `LT`, `EQ` and `GT`, read out of the loaded world.
pub fn ordering_layouts(
    world: &World<'_>,
) -> Result<(Constructor, Constructor, Constructor), String> {
    let ty = ordering_ty();
    let lt = layout(world, "$ghc-prim$GHC.Types$LT", &ty)?;
    let eq = layout(world, "$ghc-prim$GHC.Types$EQ", &ty)?;
    let gt = layout(world, "$ghc-prim$GHC.Types$GT", &ty)?;
    if [&lt, &eq, &gt].iter().any(|c| !c.fields.is_empty()) {
        return Err("the loaded world's Ordering layout is not the expected one".into());
    }
    Ok((lt, eq, gt))
}

/// `False` and `True`, read out of the loaded world.
pub fn bool_layouts(world: &World<'_>) -> Result<(Constructor, Constructor), String> {
    let ty = bool_ty();
    let false_ = layout(world, "$ghc-prim$GHC.Types$False", &ty)?;
    let true_ = layout(world, "$ghc-prim$GHC.Types$True", &ty)?;
    if !false_.fields.is_empty() || !true_.fields.is_empty() {
        return Err("the loaded world's Bool layout is not the expected one".into());
    }
    Ok((false_, true_))
}

/// The constructor evidence a `[Char]` is built from: nil, cons and `C#`. Read
/// out of the loaded world like any other layout, so the shape of a list cell
/// is never assumed by the code that fills one.
pub fn string_layouts(
    world: &World<'_>,
) -> Result<(Constructor, Constructor, Constructor), String> {
    let character = super::strings::char_ty();
    let (nil, cons) = list_layouts(world, &character)?;
    let wrapper = layout(world, "$ghc-prim$GHC.Types$C#", &character)?;
    if wrapper.fields.len() != 1 || !super::primitive::is_char(&wrapper.fields[0]) {
        return Err("the loaded world's Char layout is not the expected one".into());
    }
    Ok((nil, cons, wrapper))
}

/// `EmptyCallStack`, `PushCallStack` and `FreezeCallStack`, and `SrcLoc`,
/// read out of the loaded world with their field types checked.
pub fn call_stack_layouts(world: &World<'_>) -> Result<super::CallStackLayouts, String> {
    let stack = super::external::call_stack_ty();
    let location = super::external::src_loc_ty();
    let string = super::strings::string_ty();
    let empty = layout(world, "$base$GHC.Stack.Types$EmptyCallStack", &stack)?;
    let push = layout(world, "$base$GHC.Stack.Types$PushCallStack", &stack)?;
    let freeze = layout(world, "$base$GHC.Stack.Types$FreezeCallStack", &stack)?;
    let at = layout(world, "$base$GHC.Stack.Types$SrcLoc", &location)?;
    let int = |ty: &Ty| boxed::is_int(ty);
    if !empty.fields.is_empty()
        || !matches!(push.fields.as_slice(), [f, l, s]
            if f.alpha_eq(&string) && l.alpha_eq(&location) && s.alpha_eq(&stack))
        || !matches!(freeze.fields.as_slice(), [s] if s.alpha_eq(&stack))
        || at.fields.len() != 7
        || !at.fields[..3].iter().all(|f| f.alpha_eq(&string))
        || !at.fields[3..].iter().all(int)
    {
        return Err("the loaded world's CallStack layout is not base's".into());
    }
    Ok(super::CallStackLayouts {
        empty,
        push,
        freeze,
        location: at,
    })
}

/// Resolve only unbound global worker occurrences. A local shadow never gains
/// constructor semantics from its spelling or an unrelated id-table entry.
pub fn resolve(
    world: &World<'_>,
    module_index: usize,
    source: ExprId,
    ty: &Ty,
) -> Result<Option<Constructor>, String> {
    let module = world.at(module_index)?;
    let Expr::Var { name, .. } = module.expr(source) else {
        return Ok(None);
    };
    if module.reference(source) != Some(h2r_core_ir::Ref::Global) {
        return Ok(None);
    }
    let mut constructor = None;
    for (_, readable) in world.iter() {
        for info in readable.constructors.iter().filter(|c| c.worker == *name) {
            match constructor {
                None => constructor = Some(info.name.clone()),
                Some(ref already) if *already == info.name => {}
                Some(_) => return Err("ambiguous constructor worker".into()),
            }
        }
    }
    let Some(constructor) = constructor else {
        return Ok(None);
    };
    if boxed::is_int(ty) {
        return Ok(None);
    }
    layout(world, &constructor, ty).map(Some)
}

/// Does this occurrence name the worker of an unboxed tuple, and if so what
/// are its components at this result type?
///
/// Asked before the ordinary constructor path, because an unboxed tuple has no
/// layout to read: there is no box, no tag and no allocation, so `layout`
/// refuses it and is right to.
pub fn unboxed_tuple_worker(
    world: &World<'_>,
    module_index: usize,
    source: ExprId,
    ty: &Ty,
) -> Result<Option<Vec<Ty>>, String> {
    let module = world.at(module_index)?;
    let Expr::Var { name, .. } = module.expr(source) else {
        return Ok(None);
    };
    if module.reference(source) != Some(h2r_core_ir::Ref::Global) {
        return Ok(None);
    }
    let names_a_tuple = world.iter().any(|(_, readable)| {
        readable
            .constructors
            .iter()
            .any(|c| c.worker == *name && c.unboxed_tuple())
    });
    if !names_a_tuple {
        return Ok(None);
    }
    let Some(fields) = unboxed_tuple_fields(world, ty)? else {
        return Err("an unboxed tuple worker does not build an unboxed tuple".into());
    };
    for field in &fields {
        if carrier(world, field).is_none() {
            return Err("unsupported unboxed tuple component carrier".into());
        }
    }
    Ok(Some(fields))
}

pub fn family(world: &World<'_>, ty: &Ty) -> Result<Vec<Constructor>, String> {
    let Ty::Con { tycon, .. } = ty else {
        return Err("non-algebraic case type".into());
    };
    let module = declaring(world, &tycon.name)?.ok_or("missing or ambiguous constructor family")?;
    let layouts = module
        .constructors
        .iter()
        .filter(|c| c.family == tycon.name)
        .map(|c| layout(world, &c.name, ty))
        .collect::<Result<Vec<_>, _>>()?;
    let mut tags = std::collections::BTreeSet::new();
    if layouts.is_empty() || layouts.iter().any(|c| !tags.insert(c.tag)) {
        return Err("missing or ambiguous constructor family".into());
    }
    if module
        .constructors
        .iter()
        .filter(|c| c.family == tycon.name)
        .any(|c| c.family_size as usize != layouts.len())
    {
        return Err("incomplete constructor family census".into());
    }
    // GHC tags are contiguous, starting at one. Missing entries fail closed.
    if tags.iter().copied().ne(1..=layouts.len() as u32) {
        return Err("incomplete constructor family".into());
    }
    Ok(layouts)
}
