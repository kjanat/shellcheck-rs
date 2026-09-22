//! `h2r lower` — the lowering reports. M3a: `Main.main`-rooted
//! reachability over the closed world, with the independent verifier's
//! result printed beside it.
//!
//! Kept out of `main.rs` for the reason [`crate::m23`] and [`crate::m24`]
//! are: every later sub-milestone prints into the same report.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use anyhow::{Result, bail};
use h2r_analysis::dictflow::{self, DictFlow, Outcome};
use h2r_analysis::higher::{Higher, Slot, Verdict as HigherVerdict};
use h2r_core_ir::{BinderId, ExprId, Module, load_dir};
use h2r_lower::reachability::{
    DeadReason, LinkError, LiveSet, NodeId, RULES, TRUSTED, enclosing_top_pair, root_name,
    top_pair_binders,
};
use h2r_lower::verify::{Audit, verify};

/// Lower only an explicitly selected live leaf. No successful result here
/// implies that the rest of the program has been lowered.
pub fn nir(dir: &Path, name: &str) -> Result<()> {
    let modules = load_dir(dir)?;
    print!("{}", nir_report(&modules, name)?);
    Ok(())
}

/// Print all outcomes before returning failure for an incomplete lowering pass.
pub fn nir_program(dir: &Path) -> Result<()> {
    let modules = load_dir(dir)?;
    let (report, refused) = nir_program_report(&modules)?;
    print!("{report}");
    if refused != 0 {
        bail!("NIR lowering incomplete: {refused} live bindings refused");
    }
    Ok(())
}

/// Specialize and report every instance the roots need. With `--fn` the root
/// is that one binding and the full NIR of each instance is printed; without
/// it, every live binding is a root and the report is the whole-program
/// measure: how many instances the live set requires, how many lower, and what
/// the remaining blockers are.
///
/// Refusals are recorded rather than fatal, so the report is the whole picture
/// of what the roots reach. The instances a refused one would itself have
/// required stay unknown, which makes every count a lower bound.
pub fn nir_specialize(dir: &Path, name: Option<&str>) -> Result<()> {
    let modules = load_dir(dir)?;
    let (report, refused) = nir_specialize_report(&modules, name)?;
    print!("{report}");
    if refused != 0 {
        bail!("specialization incomplete: {refused} instances refused");
    }
    Ok(())
}

/// The live set every NIR path roots from: complete in-world linkage, and no
/// disagreement with the independent verifier.
fn audited_live_set(modules: &[Module]) -> Result<LiveSet> {
    let selected: Vec<_> = modules.iter().collect();
    let live = LiveSet::of_modules(selected.iter().copied())
        .map_err(|error| anyhow::anyhow!("the live graph has no root: {error}"))?;
    if !live.in_world_missing.is_empty() {
        bail!("NIR requires complete in-world linkage; A5-IN-WORLD-MISSING is nonzero");
    }
    let audit = verify(&selected, &live);
    if audit.total_disagreements != 0 {
        bail!(
            "reachability verification failed: {} disagreements",
            audit.total_disagreements
        );
    }
    Ok(live)
}

fn nir_specialize_report(modules: &[Module], name: Option<&str>) -> Result<(String, usize)> {
    use h2r_lower::nir::{pretty::format_leaf, specialize};
    use std::fmt::Write;

    let live = audited_live_set(modules)?;
    let (roots, heading) = match name {
        Some(name) => {
            let matches = live.by_name(name);
            let [node] = matches.as_slice() else {
                bail!(
                    "specialization needs one exact stable root name; {name:?} matched {} bindings",
                    matches.len()
                );
            };
            if !live.is_live(*node) {
                bail!("selected binding {name:?} is not reachable from Main.main");
            }
            let binding = live.node(*node);
            (
                vec![specialize::Instance::whole(
                    binding.key.module as usize,
                    binding.key.binder,
                )],
                format!("NIR specialization root: {name}"),
            )
        }
        None => {
            let roots: Vec<_> = live
                .live
                .iter()
                .map(|binding| {
                    let key = live.node(binding.node).key;
                    specialize::Instance::whole(key.module as usize, key.binder)
                })
                .collect();
            let heading = format!(
                "NIR specialization roots: {} live bindings\nScope: the instances a \
                 dependency-closed program would need, as far as the lowered ones reveal; \
                 a refused instance hides its own requirements, so every count is a lower bound",
                roots.len()
            );
            (roots, heading)
        }
    };
    let program = specialize::survey(modules, &roots);
    let owners = program.instances_per_owner();
    let specialized = program
        .instances
        .iter()
        .filter(|i| !i.type_arguments.is_empty() || !i.dictionaries.is_empty())
        .count();
    let dictionaries = program
        .instances
        .iter()
        .filter(|i| !i.dictionaries.is_empty())
        .count();
    let lowered = program.lowered_count();
    let refused = program.refused.len();
    let mut out = format!(
        "{heading}\nInstances: {} = {lowered} lowered + {refused} refused, over {} owners\nSpecialized: {specialized} at type or dictionary arguments, of which {dictionaries} carry a dictionary\n",
        lowered + refused,
        owners.len(),
    );
    if name.is_some() {
        for (index, instance) in program.instances.iter().enumerate() {
            let Some(leaf) = program.leaf(index) else {
                continue;
            };
            writeln!(
                out,
                "INSTANCE {index} {:?} at {}, {} dictionaries",
                modules[instance.module].binder(instance.binder).name,
                type_arguments(instance),
                instance.dictionaries.len(),
            )
            .unwrap();
            out.push_str(&format_leaf(leaf));
        }
        for error in &program.refused {
            writeln!(
                out,
                "REFUSED {:?}: {} [required through {}]",
                modules[error.instance.module]
                    .binder(error.instance.binder)
                    .name,
                error.reason,
                error
                    .path
                    .iter()
                    .map(|step| modules[step.module].binder(step.binder).name.clone())
                    .collect::<Vec<_>>()
                    .join(" -> "),
            )
            .unwrap();
        }
    } else {
        let (open, closed): (Vec<_>, Vec<_>) = program
            .refused
            .iter()
            .partition(|error| open_signature(modules, &error.instance));
        let requested_closed: BTreeSet<_> = program
            .instances
            .iter()
            .filter(|instance| !open_signature(modules, instance))
            .map(|instance| (instance.module, instance.binder))
            .collect();
        let open_owners: BTreeSet<_> = open
            .iter()
            .map(|error| (error.instance.module, error.instance.binder))
            .collect();
        writeln!(
            out,
            "Refused: {refused} = {} at a closed signature + {} at an open signature",
            closed.len(),
            open.len()
        )
        .unwrap();
        writeln!(out, "Blockers, by reason:").unwrap();
        out.push_str(&rank_reasons(&closed));
        out.push_str(&blocked_subjects("Blockers", &closed));
        writeln!(
            out,
            "Open signatures: {} refused instances of {} bindings quantified over types they were not given; {} of those bindings were also requested at closed types",
            open.len(),
            open_owners.len(),
            open_owners.intersection(&requested_closed).count(),
        )
        .unwrap();
        out.push_str(&rank_reasons(&open));
        out.push_str(&blocked_subjects("Open signatures", &open));
        out.push_str(&external_demand(&program));
        writeln!(out, "Specialized instances:").unwrap();
        for (index, instance) in program.instances.iter().enumerate() {
            if instance.type_arguments.is_empty() && instance.dictionaries.is_empty() {
                continue;
            }
            writeln!(
                out,
                "    {} {:?} at {}, {} dictionaries",
                if program.leaf(index).is_some() {
                    "lowered"
                } else {
                    "refused"
                },
                modules[instance.module].binder(instance.binder).name,
                type_arguments(instance),
                instance.dictionaries.len(),
            )
            .unwrap();
        }
    }
    Ok((out, refused))
}

fn type_arguments(instance: &h2r_lower::nir::specialize::Instance) -> String {
    let rendered: Vec<_> = instance
        .type_arguments
        .iter()
        .map(h2r_core_ir::Ty::render)
        .collect();
    format!("[{}]", rendered.join(", "))
}

fn open_signature(modules: &[Module], instance: &h2r_lower::nir::specialize::Instance) -> bool {
    let mut ty = modules[instance.module].binder_ty(instance.binder);
    let mut quantifiers = 0;
    while let h2r_core_ir::Ty::ForAll { body, .. } = ty {
        quantifiers += 1;
        ty = body;
    }
    instance.type_arguments.len() < quantifiers
}

fn refusal_reason(error: &h2r_lower::nir::specialize::SpecializeError) -> &str {
    error
        .reason
        .split(" (at source expression ")
        .next()
        .unwrap_or(&error.reason)
}

fn rank_reasons(errors: &[&h2r_lower::nir::specialize::SpecializeError]) -> String {
    use std::fmt::Write;

    let mut reasons: BTreeMap<&str, usize> = BTreeMap::new();
    for error in errors {
        *reasons.entry(refusal_reason(error)).or_insert(0) += 1;
    }
    let mut out = String::new();
    for (reason, count) in rank_counts(reasons) {
        writeln!(out, "{count:8}  {reason}").unwrap();
    }
    out
}

/// Most demanded first, ties broken by the key so a report is reproducible.
fn rank_counts<K: Ord>(counts: BTreeMap<K, usize>) -> Vec<(K, usize)> {
    let mut ranked: Vec<_> = counts.into_iter().collect();
    ranked.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
    ranked
}

/// What each refusal was about, where the refusing site knew: the type
/// constructor whose carrier is missing, the family whose layout is not
/// supported. A reason says which rule stopped an instance; this says which
/// type would have to be carried for that rule to pass. Refusals whose site
/// named no subject are counted but not itemised.
fn blocked_subjects(
    heading: &str,
    errors: &[&h2r_lower::nir::specialize::SpecializeError],
) -> String {
    use std::fmt::Write;

    const EXTERNAL: &str = "imported binding is outside the loaded world";
    let mut subjects: BTreeMap<(&str, &str), usize> = BTreeMap::new();
    for error in errors {
        let reason = refusal_reason(error);
        if reason == EXTERNAL {
            continue;
        }
        if let Some(subject) = error.detail.as_deref() {
            *subjects.entry((reason, subject)).or_insert(0) += 1;
        }
    }
    if subjects.is_empty() {
        return String::new();
    }
    let mut out = format!("{heading}, by the type they are about:\n");
    for ((reason, subject), count) in rank_counts(subjects) {
        writeln!(out, "{count:8}  {subject}  ({reason})").unwrap();
    }
    out
}

/// The external boundary, ranked by demand: which library bindings the survey
/// asked for and could not find in the loaded world. One instance may name the
/// same binding at several sites and is counted once per site it refused at, so
/// these are refusals, not distinct call sites, and — like every survey count —
/// a lower bound: a refused instance never revealed its own requirements.
fn external_demand(program: &h2r_lower::nir::specialize::Specialization) -> String {
    use h2r_core_ir::split_stable_name;
    use std::fmt::Write;

    const OUTSIDE: &str = "imported binding is outside the loaded world";
    let mut bindings: BTreeMap<&str, usize> = BTreeMap::new();
    let mut origins: BTreeMap<(&str, &str), usize> = BTreeMap::new();
    for error in &program.refused {
        if !error.reason.starts_with(OUTSIDE) {
            continue;
        }
        let Some(name) = error.detail.as_deref() else {
            continue;
        };
        *bindings.entry(name).or_insert(0) += 1;
        if let Some((unit, module, _)) = split_stable_name(name) {
            *origins.entry((unit, module)).or_insert(0) += 1;
        }
    }
    if bindings.is_empty() {
        return String::new();
    }
    let named: usize = bindings.values().sum();
    let unnamed = program
        .refused
        .iter()
        .filter(|error| error.reason.starts_with(OUTSIDE) && error.detail.is_none())
        .count();
    let mut out = format!(
        "External boundary: {} distinct bindings over {named} refusals, in {} modules{}\n",
        bindings.len(),
        origins.len(),
        if unnamed == 0 {
            String::new()
        } else {
            format!("; {unnamed} refusals named no occurrence")
        }
    );
    writeln!(out, "External modules, by refusals:").unwrap();
    for ((unit, module), count) in rank_counts(origins) {
        writeln!(out, "{count:8}  {unit}:{module}").unwrap();
    }
    writeln!(out, "External bindings, by refusals:").unwrap();
    for (name, count) in rank_counts(bindings) {
        writeln!(out, "{count:8}  {name}").unwrap();
    }
    out
}

fn nir_program_report(modules: &[Module]) -> Result<(String, usize)> {
    use h2r_lower::nir::{pretty::format_leaf, program::lower_program};
    use std::fmt::Write;

    let attempt = lower_program(modules).map_err(anyhow::Error::msg)?;
    let mut out = format!(
        "NIR program attempt (leaf subset; no executable output)\nLive owners: {} = {} lowered + {} refused; {} dead skipped\n",
        attempt.live,
        attempt.lowered.len(),
        attempt.refused.len(),
        attempt.dead,
    );
    for leaf in &attempt.lowered {
        let function = &leaf.function;
        writeln!(
            out,
            "LOWERED {:?}",
            modules[function.module].binder(function.owner).name
        )
        .unwrap();
        out.push_str(&format_leaf(leaf));
    }
    for error in &attempt.refused {
        writeln!(
            out,
            "REFUSED module {} binder {} {:?} at {:?}: {}",
            error.module,
            error.owner,
            modules[error.module].binder(error.owner).name,
            error.source,
            error.reason
        )
        .unwrap();
    }
    Ok((out, attempt.refused.len()))
}

fn nir_report(modules: &[Module], name: &str) -> Result<String> {
    use h2r_lower::nir::{
        FnId, lower::lower_leaf_in_world, pretty::format_leaf, verify::verify_leaf_in_world,
    };

    let live = audited_live_set(modules)?;
    let matches = live.by_name(name);
    let [node] = matches.as_slice() else {
        bail!(
            "--fn requires one exact stable name; {name:?} matched {} bindings",
            matches.len()
        );
    };
    if !live.is_live(*node) {
        bail!("selected binding {name:?} is not reachable from Main.main");
    }
    let binding = live.node(*node);
    let module_index = binding.key.module as usize;
    let owner = binding.key.binder;
    let id = FnId(*node);
    let lowered = lower_leaf_in_world(modules, module_index, owner, id).map_err(|error| {
        anyhow::anyhow!(
            "cannot lower {name:?} at {:?}: {}",
            error.source,
            error.reason
        )
    })?;
    let accounting = verify_leaf_in_world(modules, module_index, owner, id, &lowered)
        .map_err(|error| anyhow::anyhow!("NIR source verification failed: {error}"))?;
    Ok(format!(
        "NIR leaf: {name}\nScope: one reachable function; not whole-program lowering\nVerified source nodes: {} = {} parameters + {} type parameters + {} value + {} erased ticks + {} type applications + {} type arguments + {} value applications + {} value arguments\n{}",
        accounting.source_nodes,
        accounting.parameter_nodes,
        accounting.type_parameter_nodes,
        accounting.value_nodes,
        accounting.erased_ticks,
        accounting.type_application_nodes,
        accounting.type_argument_nodes,
        accounting.value_application_nodes,
        accounting.value_argument_nodes,
        format_leaf(&lowered),
    ))
}

/// One row of the [`A5-IN-WORLD-MISSING`] table, grouped by the module the
/// unlinkable name points into: how many names, how many occurrences, and
/// which live modules carry them.
type TargetRow<'a> = (usize, u32, BTreeSet<&'a str>);

/// How many bindings `--explain` spells out when a name matches several.
const EXPLAIN_CAP: usize = 20;

/// How many import names the summary lists.
const TOP_IMPORTS: usize = 20;

#[allow(clippy::too_many_arguments)]
pub fn lower(
    dir: &Path,
    reachability: bool,
    json: bool,
    rules: bool,
    explain: Option<String>,
    link: Option<String>,
    m24_link: bool,
) -> Result<()> {
    if rules {
        print_rules();
        return Ok(());
    }
    if !reachability {
        bail!(
            "h2r lower needs --reachability or --nir [--fn <stable-name>]. \
             --rules prints the reachability rule table."
        );
    }
    let modules = load_dir(dir)?;
    let selected: Vec<&Module> = modules.iter().collect();
    let live = match LiveSet::of_modules(selected.iter().copied()) {
        Ok(l) => l,
        Err(e) => bail!("the live graph has no root: {e}"),
    };
    let audit = verify(&selected, &live);

    if json {
        let v = serde_json::json!({
            "reachability": &live,
            "verifier": &audit,
            "rules": RULES,
        });
        println!("{}", serde_json::to_string_pretty(&v)?);
        return Ok(());
    }

    if let Some(what) = link {
        return print_link(&live, &what);
    }

    if let Some(what) = explain {
        return print_explain(&live, &what);
    }

    print_report(&selected, &live, &audit);
    if m24_link {
        println!();
        print_m24_link(&selected, &live);
    }
    Ok(())
}

fn print_rules() {
    println!("  rules");
    for (id, level, meaning) in RULES {
        println!("  {id:<24} level {level}  {meaning}");
    }
}

fn print_report(modules: &[&Module], live: &LiveSet, audit: &Audit) {
    let a = &live.accounting;
    println!(
        "M3a — the Main.main-rooted live set. The nodes are the {} top-level\n\
         bindings of the {} modules in the dump; the edges are the references\n\
         between them, established by the resolver (A2-EDGE-LOCAL) and by stable\n\
         name (A3-EDGE-GLOBAL); live is the transitive closure from the roots.",
        a.top,
        modules.len()
    );
    println!();
    println!("  trusted inputs (consulted, never verified — the verifier shares exactly these)");
    for t in TRUSTED {
        println!("    - {t}");
    }
    println!();

    println!("  roots [{}]", crate::lower::root_rule(live));
    for r in &live.roots {
        let t = live.node(r.node);
        println!("    {} {}  ({})", t.module_name, t.occ, t.name);
    }
    if live.roots.is_empty() {
        println!("    (none)");
    }
    // The GHC-generated `:Main.main` wrapper is not the M3a root; say so
    // rather than leave a reader wondering where it went.
    for n in live.by_name("$main$:Main$main") {
        let state = if live.is_live(n) { "live" } else { "dead" };
        println!(
            "    note: GHC's own entry wrapper $main$:Main$main is {state}; M3a's root is\n\
             \x20         $<unit>$Main$main, which it calls through base's runMainIO."
        );
    }
    println!();

    if a.in_world_missing > 0 {
        println!("  STATUS — THE DEAD SET IS CONDITIONAL [A5-IN-WORLD-MISSING]");
        println!(
            "    {} stable name(s) over {} occurrence(s) name a module of this world and no\n\
             \x20   top-level binding of it. The plugin serialises the CoreProgram *before*\n\
             \x20   GHC's CoreTidy pass, and CoreTidy is what externalises a top-level binder\n\
             \x20   GHC has kept internal — so the defining module's dump carries $_in$$wchecker\n\
             \x20   where a downstream module, which read the tidied interface, refers to\n\
             \x20   $<unit>$<module>$$wchecker. The closed world cannot see that the two are one\n\
             \x20   binding, so the reference establishes no edge and the binding can be called\n\
             \x20   dead although the program calls it.",
            a.in_world_missing, a.missing_impact.occurrences
        );
        println!(
            "    {} of those names are referenced from LIVE code. Every dead verdict in the {} \n\
             \x20   module(s) they point into — {} of the {} — is therefore conditional on a\n\
             \x20   linkage the dump cannot supply, and the live set below is a LOWER BOUND.\n\
             \x20   This is not a defect of the walk; it is the dump's naming, and it is the\n\
             \x20   first thing M3 has to fix.",
            a.missing_impact.names_referenced_from_live,
            a.missing_impact.suspect_modules.len(),
            a.missing_impact.suspect_dead,
            a.dead
        );
        println!();
    } else {
        // The check stays; only the verdict changes. The conditional block
        // above is what M3a had to print, and M3a' is the milestone that
        // removed its cause.
        println!("  A5-IN-WORLD-MISSING 0: the dead set is unconditional");
        println!();
    }

    println!("  per module");
    println!(
        "  {:<34} {:>6} {:>6} {:>10} {:>12}",
        "module", "top", "live", "dead(0-ref)", "dead(only-dead)"
    );
    for m in &a.modules {
        println!(
            "  {:<34} {:>6} {:>6} {:>10} {:>12}",
            m.module, m.top, m.live, m.dead_no_refs, m.dead_only_from_dead
        );
    }
    println!(
        "  {:<34} {:>6} {:>6} {:>10} {:>12}",
        "TOTAL", a.top, a.live, a.dead_no_refs, a.dead_only_from_dead
    );
    println!();
    println!(
        "  top {} = live {} + dead {} ({:.1}% dead): asserted per module and in total \
         [A10-ACCOUNTING]",
        a.top,
        a.live,
        a.dead,
        100.0 * a.dead as f64 / a.top.max(1) as f64
    );
    println!(
        "  dead {} = no-references {} + only-dead-referrers {}: asserted [A10-ACCOUNTING]",
        a.dead, a.dead_no_refs, a.dead_only_from_dead
    );
    println!(
        "  edges {} ({} intra-module [A2-EDGE-LOCAL], {} inter-module [A3-EDGE-GLOBAL]) over {} \
         occurrences",
        a.edges, a.edges_local, a.edges_global, a.edge_occurrences
    );
    println!();

    println!("  the subset check against M2.4c's zero-reference set");
    println!(
        "    zero-reference (dictflow's own T_UNREACHABLE predicate)      {:>6}",
        a.zero_reference
    );
    println!(
        "    …of which are roots (an entry point is not called by the\n\
         \x20    program, so the root is zero-reference by construction)     {:>6}",
        a.zero_reference_roots
    );
    for n in live.zero_reference_not_dead() {
        let t = live.node(n);
        println!(
            "        {} {}  ({}){}",
            t.module_name,
            t.occ,
            t.name,
            if live.is_root(n) {
                "  [A1-ROOT-MAIN]"
            } else {
                "  NOT A ROOT"
            }
        );
    }
    println!(
        "    …of which are rooted-dead                                    {:>6}",
        a.zero_reference - a.zero_reference_roots - a.zero_reference_live
    );
    println!(
        "    …neither dead nor a root (the gate asserts 0)                {:>6}",
        a.zero_reference_live
    );
    println!(
        "    rooted dead                                                 {:>6}",
        a.dead
    );
    println!(
        "    …additional dead the rooted analysis finds                   {:>6}",
        a.additional_dead
    );
    println!(
        "    subset: {}",
        if a.zero_reference_live == 0 {
            "every zero-reference binding but the root is rooted-dead [A7-DEAD-NO-REFS]"
        } else {
            "FAILED — see the accounting"
        }
    );
    println!();

    println!("  imports — external names referenced from live code, top {TOP_IMPORTS} by count");
    println!(
        "    {} distinct external stable names in all, {} occurrences from live code and {} \
         from dead [A4-IMPORT]",
        a.import_names, a.import_occurrences_live, a.import_occurrences_dead
    );
    for (name, use_) in live.imports_by_live_use().into_iter().take(TOP_IMPORTS) {
        println!("    {:>7}  {}", use_.from_live, name);
    }
    println!();

    println!("  in-world missing [A5-IN-WORLD-MISSING]");
    println!(
        "    a global occurrence naming an in-world module that GHC's own flags explain \n\
         \x20   without a top-level binding is not a hole: {} data-constructor name(s) over {} \n\
         \x20   occurrences and {} class-op selector(s) over {} occurrences.",
        a.in_world_non_bindings.data_con_names,
        a.in_world_non_bindings.data_con_occurrences,
        a.in_world_non_bindings.class_op_names,
        a.in_world_non_bindings.class_op_occurrences
    );
    if a.in_world_missing == 0 {
        println!("    0 names remain: the closed world links every other in-world reference.");
    } else {
        let mi = &a.missing_impact;
        println!(
            "    {} name(s) remain, over {} occurrence(s): a linkage hole, NOT 0. The plugin\n\
             \x20   serialises the CoreProgram before GHC's CoreTidy pass, so a top-level\n\
             \x20   binding GHC has not externalised yet carries an internal name in its own\n\
             \x20   module's dump while a downstream module — which read the tidied interface —\n\
             \x20   names it externally. Every stable-name linkage in the compiler has this\n\
             \x20   gap; M3a is the first pass to measure it.",
            mi.names, mi.occurrences
        );
        println!(
            "    {} of the {} names are referenced from live code; {} have no name-matched\n\
             \x20   candidate binding at all.",
            mi.names_referenced_from_live, mi.names, mi.names_without_candidate
        );
        println!(
            "    the sound bound, which needs no name: the {} module(s) an unlinkable name\n\
             \x20   referenced from live code points into hold {} of the {} dead bindings, and\n\
             \x20   those verdicts are conditional on the linkage:\n\
             \x20   {}",
            mi.suspect_modules.len(),
            mi.suspect_dead,
            a.dead,
            mi.suspect_modules.join(", ")
        );
        println!(
            "    the constructive bound [A11-MISSING-IMPACT, evidence level 6 — a NAME match,\n\
             \x20   never an edge]: re-running the closure with every name-matched edge added\n\
             \x20   makes {} further binding(s) live, from {} candidate binding(s), {} of them\n\
             \x20   currently dead. Where it lands:",
            mi.would_become_live, mi.candidates, mi.candidates_dead
        );
        let mut by: Vec<(&String, &usize)> = mi.would_become_live_by_module.iter().collect();
        by.sort_by(|x, y| y.1.cmp(x.1).then(x.0.cmp(y.0)));
        for (m, k) in by {
            println!("      {k:>6}  {m}");
        }
        let mut by_target: BTreeMap<&str, TargetRow<'_>> = BTreeMap::new();
        for m in &live.in_world_missing {
            let e = by_target.entry(m.in_module.as_str()).or_default();
            e.0 += 1;
            e.1 += m.occurrences;
            for r in &m.live_referrer_modules {
                e.2.insert(r.as_str());
            }
        }
        println!("    by the module the name points into, with the live modules that name it");
        let mut tr: Vec<(&&str, &TargetRow<'_>)> = by_target.iter().collect();
        tr.sort_by(|x, y| y.1.1.cmp(&x.1.1).then(x.0.cmp(y.0)));
        for (target, (names, occs, from)) in tr {
            println!(
                "      {occs:>6} occ over {names:>3} name(s)  {target}  <- {}",
                if from.is_empty() {
                    "(nothing live)".to_string()
                } else {
                    from.iter().copied().collect::<Vec<_>>().join(", ")
                }
            );
        }
        let mut rows: Vec<&h2r_lower::reachability::Missing> =
            live.in_world_missing.iter().collect();
        rows.sort_by(|x, y| y.occurrences.cmp(&x.occurrences).then(x.name.cmp(&y.name)));
        println!("    the ten most referenced, with their name-matched candidates");
        for m in rows.iter().take(10) {
            println!(
                "      {:>6}  {}  ({} candidate(s), {} dead, {})",
                m.occurrences,
                m.name,
                m.candidates.len(),
                m.candidates_dead,
                if m.referenced_from_live {
                    "referenced from live code"
                } else {
                    "referenced only from dead code"
                }
            );
        }
    }
    println!();

    println!("  the identity rules, with their counts");
    println!(
        "    [{A12}] external stable names an in-world top-level binding defines  {:>6}",
        a.external_names_defined,
        A12 = h2r_lower::reachability::A12_EXTERNAL_UNIQUE
    );
    println!(
        "      ...defined by more than one binding (the graph refuses to build     {:>6}\n\
         \x20      otherwise, so this is 0 or there is no report)",
        a.external_name_collisions
    );
    println!(
        "    [{A13}] Ref::Global occurrences carrying an internal stable name    {:>6}",
        a.global_internal_occurrences,
        A13 = h2r_lower::reachability::A13_GLOBAL_EXTERNAL
    );
    println!(
        "      ...distinct such names                                              {:>6}",
        a.global_internal_names
    );
    println!(
        "    the IR resolver's unique-collision guard, over the whole world        {:>6}",
        a.unique_collisions
    );
    println!();

    println!("  accounting [A10-ACCOUNTING]");
    let bad = a.check();
    if bad.is_empty() {
        println!("    every identity holds");
    } else {
        for b in &bad {
            println!("    FAILED  {b}");
        }
    }
    println!();

    println!("  the independent verifier ({})", audit.headline());
    for line in audit.report_lines() {
        println!("    {line}");
    }
    println!();

    println!("  the largest dead components, by module");
    let mut rows: Vec<(&str, usize, usize)> = a
        .modules
        .iter()
        .map(|m| (m.module.as_str(), m.dead(), m.top))
        .collect();
    rows.sort_by(|x, y| y.1.cmp(&x.1).then(x.0.cmp(y.0)));
    for (name, dead, top) in rows.iter().take(10) {
        println!("    {dead:>6} of {top:<6}  {name}");
    }
    println!();

    println!("  what the rooted analysis adds over the zero-reference subset, by example");
    let mut extra: Vec<NodeId> = live
        .dead
        .iter()
        .filter(|d| d.reason == DeadReason::DeadReferencedOnlyFromDead)
        .map(|d| d.node)
        .collect();
    extra.sort_by_key(|&n| {
        let t = live.node(n);
        (t.module_name.clone(), t.name.clone(), n)
    });
    println!(
        "    {} bindings are referenced and still dead, because every binding that\n\
         \x20   references them is itself dead [A8-DEAD-ONLY-FROM-DEAD]",
        extra.len()
    );
    for n in extra.iter().take(10) {
        let t = live.node(*n);
        let d = live.dead_of(*n).expect("dead");
        let from: Vec<String> = d
            .referrers
            .iter()
            .take(3)
            .map(|&r| live.node(r).occ.clone())
            .collect();
        println!(
            "      {} {}  referenced by {} dead binding(s): {}",
            t.module_name,
            t.occ,
            d.referrers.len(),
            from.join(", ")
        );
    }
}

fn root_rule(live: &LiveSet) -> &'static str {
    live.roots
        .first()
        .map(|r| r.rule)
        .unwrap_or(h2r_lower::reachability::A1_ROOT_MAIN)
}

fn print_explain(live: &LiveSet, what: &str) -> Result<()> {
    let hits = live.by_name_or_occ(what);
    if hits.is_empty() {
        bail!(
            "no top-level binding is named {what}. Give a stable name \
             (e.g. {}) or an occurrence name.",
            root_name("<unit>")
        );
    }
    if hits.len() > 1 {
        println!(
            "{} top-level bindings answer to {what}; a name is not an identity{}.",
            hits.len(),
            if hits.len() > EXPLAIN_CAP {
                format!(", so the first {EXPLAIN_CAP} follow")
            } else {
                ", so all of them follow".to_string()
            }
        );
    }
    for n in hits.into_iter().take(EXPLAIN_CAP) {
        let t = live.node(n);
        println!();
        println!(
            "{} {}  ({})  binder {}{}{}",
            t.module_name,
            t.occ,
            t.name,
            t.key.binder,
            if t.exported { ", exported" } else { "" },
            if t.external {
                ""
            } else {
                ", internal name (reachable only through A2-EDGE-LOCAL)"
            }
        );
        match live.live_of(n) {
            Some(l) => {
                println!(
                    "  LIVE — witness [{}], {} hop(s)",
                    l.rule,
                    l.witness.len() - 1
                );
                print_witness(live, &l.witness);
            }
            None => {
                let d = live.dead_of(n).expect("neither live nor dead");
                println!("  DEAD — {} [{}]", d.reason.label(), d.rule);
                match d.reason {
                    DeadReason::DeadNoReferences => println!(
                        "    no occurrence anywhere in the closed world: under A0-CLOSED-WORLD \
                         nothing can name it"
                    ),
                    DeadReason::DeadReferencedOnlyFromDead => {
                        println!(
                            "    referenced by {} top-level binding(s), every one of them dead:",
                            d.referrers.len()
                        );
                        for &r in &d.referrers {
                            let s = live.node(r);
                            let rd = live.dead_of(r).expect("a live referrer of a dead binding");
                            println!("      {} {}  ({})", s.module_name, s.occ, rd.reason.label());
                        }
                    }
                }
            }
        }
    }
    Ok(())
}

/// `--link <stable name>`: the whole-program linkage of one name, end to
/// end.
///
/// This is the view M3a′ exists to make possible. It answers, for one
/// external stable name: which single top-level binding of which module
/// defines it ([`A12-EXTERNAL-UNIQUE`]), which modules' bindings refer to it
/// and under which rule ([`A2-EDGE-LOCAL`] inside the defining module,
/// [`A3-EDGE-GLOBAL`] from outside), and — if it is live — the shortest
/// chain of edges from `Main.main` to it ([`A9-WITNESS`]).
///
/// The defining binding is found through the external-name index, never by
/// a name heuristic: an internal stable name is not an identity, so
/// `--link` refuses one and says why.
fn print_link(live: &LiveSet, what: &str) -> Result<()> {
    let link = match live.link(what) {
        Ok(l) => l,
        Err(LinkError::NotFound) => bail!(
            "no top-level binding of this world carries the stable name {what}. \
             --link takes a stable name ($<unit>$<Module>$<occ>), which is an \
             identity; --explain also accepts an occurrence name, which is not."
        ),
        Err(LinkError::InternalName) => bail!(
            "{what} is an INTERNAL stable name. Internal names are not unique \
             — several top-level bindings can render as one — so nothing links \
             through them and --link has no single answer. Such a binding is \
             reachable only through A2-EDGE-LOCAL, inside its own module; ask \
             --explain instead."
        ),
        Err(LinkError::Ambiguous(k)) => bail!(
            "{k} top-level bindings carry the external stable name {what}: \
             A12-EXTERNAL-UNIQUE does not hold and nothing here is an identity."
        ),
    };
    let t = live.node(link.node);

    println!("  link — {}", link.name);
    println!();
    println!("  defined by exactly one top-level binding [{}]", link.rule);
    println!(
        "    module {}   binder #{}   occ {}",
        t.module_name, t.key.binder, t.occ
    );
    println!(
        "    the name is external, so another module can name it [A3-EDGE-GLOBAL]{}",
        if t.exported {
            "; GHC also marks the binder exported"
        } else {
            ""
        }
    );
    println!();

    let bindings: usize = link.referrers.iter().map(|r| r.bindings).sum();
    let occurrences: u32 = link.referrers.iter().map(|r| r.occurrences).sum();
    let modules: BTreeSet<&str> = link.referrers.iter().map(|r| r.module.as_str()).collect();
    println!(
        "  referenced by {bindings} top-level binding(s) over {occurrences} occurrence(s), \
         in {} module(s)",
        modules.len()
    );
    if link.referrers.is_empty() {
        println!("    (nothing in the closed world names it)");
    }
    for r in &link.referrers {
        println!(
            "    {:>6} occ over {:>4} binding(s)  {:<34} [{}]",
            r.occurrences, r.bindings, r.module, r.rule
        );
    }
    println!();

    match &link.witness {
        Some(w) => {
            println!(
                "  LIVE — witness [{}], {} hop(s) from the root",
                h2r_lower::reachability::A9_WITNESS,
                w.len() - 1
            );
            print_witness(live, w);
        }
        None => {
            let d = live.dead_of(link.node).expect("neither live nor dead");
            println!("  DEAD — {} [{}]", d.reason.label(), d.rule);
            for &r in d.referrers.iter().take(EXPLAIN_CAP) {
                let s = live.node(r);
                println!("    referenced by {} {}  (dead)", s.module_name, s.occ);
            }
        }
    }
    Ok(())
}

/// One witness chain, with the rule that made each step.
fn print_witness(live: &LiveSet, witness: &[NodeId]) {
    for (i, &step) in witness.iter().enumerate() {
        let s = live.node(step);
        let rule = if i == 0 {
            live.roots
                .iter()
                .find(|r| r.node == step)
                .map(|r| r.rule)
                .unwrap_or("?")
        } else {
            let prev = witness[i - 1];
            live.edges
                .iter()
                .find(|e| e.from == prev && e.to == step)
                .map(|e| e.rule)
                .unwrap_or("?")
        };
        println!(
            "    {:>3}. {:<32} {}{}  [{}]",
            i,
            s.module_name,
            s.name,
            if s.external {
                String::new()
            } else {
                format!("#{}", s.key.binder)
            },
            rule
        );
    }
}

//------------------------------------------------------------------------------
// The cross-reference with M2.4
//------------------------------------------------------------------------------

/// Which top-level binding a node lies in, for the whole world. Built the
/// way the verifier builds it — by climbing to the arena root — so the
/// cross-reference reads the same owner relation the audit checked.
struct Owners {
    pair_binder: Vec<Vec<BinderId>>,
    node_of: Vec<std::collections::HashMap<BinderId, NodeId>>,
}

impl Owners {
    fn new(modules: &[&Module], live: &LiveSet) -> Owners {
        let mut node_of = vec![std::collections::HashMap::new(); modules.len()];
        for (i, t) in live.nodes.iter().enumerate() {
            node_of[t.key.module as usize].insert(t.key.binder, i as NodeId);
        }
        Owners {
            pair_binder: modules.iter().map(|m| top_pair_binders(m)).collect(),
            node_of,
        }
    }

    fn of(&self, modules: &[&Module], mi: usize, node: ExprId) -> Option<NodeId> {
        let pair = enclosing_top_pair(modules[mi], node)?;
        let b = *self.pair_binder[mi].get(pair)?;
        self.node_of[mi].get(&b).copied()
    }
}

/// How much of M2.4's residual is inside code `Main.main` cannot reach.
///
/// The counts are cross-references, not verdicts: they say where an
/// existing `Unresolved` sits, and nothing about whether it is resolvable.
/// Every one of them inherits M3a's own `A5` caveat — a site inside a
/// binding the linkage hole wrongly calls dead is counted here as dead.
fn print_m24_link(modules: &[&Module], live: &LiveSet) {
    let owners = Owners::new(modules, live);
    let flow = DictFlow::of_modules(modules.iter().copied());
    let higher = Higher::of_modules(modules.iter().copied());

    let mut sites = 0usize;
    let mut unresolved = 0usize;
    let mut unresolved_dead = 0usize;
    let mut unreachable_reason = 0usize;
    let mut unreachable_reason_dead = 0usize;
    let mut unlocated = 0usize;
    for s in &flow.sites {
        sites += 1;
        let Outcome::Unresolved(reason) = &s.outcome else {
            continue;
        };
        unresolved += 1;
        let by_unreachable = reason.starts_with(dictflow::T_UNREACHABLE);
        if by_unreachable {
            unreachable_reason += 1;
        }
        match owners.of(modules, s.mi, s.node) {
            Some(n) if !live.is_live(n) => {
                unresolved_dead += 1;
                if by_unreachable {
                    unreachable_reason_dead += 1;
                }
            }
            Some(_) => {}
            None => unlocated += 1,
        }
    }

    let mut bounds = 0usize;
    let mut b_unresolved = 0usize;
    let mut b_unresolved_dead = 0usize;
    let mut b_field = 0usize;
    for b in &higher.boundaries {
        bounds += 1;
        if !matches!(b.verdict, HigherVerdict::Unresolved(_)) {
            continue;
        }
        b_unresolved += 1;
        let mi = match b.slot {
            Slot::Param { mi, .. } | Slot::Return { mi, .. } => mi,
            // A constructor field is a slot of a *type*, not a site in one
            // binding: it has no enclosing top-level binding to be dead in.
            Slot::Field { .. } => {
                b_field += 1;
                continue;
            }
        };
        if let Some(n) = owners.of(modules, mi, b.node)
            && !live.is_live(n)
        {
            b_unresolved_dead += 1;
        }
    }

    println!("  cross-reference with M2.4 — where its residual sits in the live set");
    println!(
        "    these are cross-references, not verdicts, and they inherit A5: a site inside a\n\
         \x20   binding the linkage hole wrongly calls dead is counted dead here too."
    );
    println!("    class-op dispatch sites                              {sites:>6}");
    println!("      Unresolved                                         {unresolved:>6}");
    println!("        …inside a rooted-dead top-level binding          {unresolved_dead:>6}");
    println!(
        "      Unresolved with reason {:<28} {unreachable_reason:>6}",
        dictflow::T_UNREACHABLE
    );
    println!(
        "        …inside a rooted-dead top-level binding          {unreachable_reason_dead:>6}"
    );
    if unlocated > 0 {
        println!("        …not inside any top-level right-hand side        {unlocated:>6}");
    }
    println!("    function-valued boundaries                           {bounds:>6}");
    println!("      Unresolved                                         {b_unresolved:>6}");
    println!("        …inside a rooted-dead top-level binding          {b_unresolved_dead:>6}");
    println!("        …a constructor field, with no one binding to be in {b_field:>4}");
}

#[cfg(test)]
mod nir_tests {
    use super::*;
    use h2r_core_ir::raw;
    use serde_json::{Value, json};

    fn binder(name: &str) -> Value {
        json!({
            "kind": "id", "name": format!("$u$Main${name}"), "occ": name, "unique": name,
            "type": "T", "ty": 0, "arity": 0, "callArity": 0, "exported": true,
            "dmdSig": {"args": [], "diverges": false, "pretty": ""}, "cprSig": "",
            "demand": {"strict": false, "absent": false, "usedOnce": false, "pretty": "L"},
            "occInfo": {"kind": "many", "tailCalled": false}, "oneShot": false,
            "details": "", "hasUnfolding": false, "isJoinPoint": false, "isDataCon": false
        })
    }

    fn fixture() -> Module {
        fixture_with_link(false)
    }

    fn fixture_with_link(missing: bool) -> Module {
        let lit = json!({
            "node": "Lit",
            "lit": {"kind": "number", "pretty": "7#", "value": "7", "numType": "Int"},
        });
        let target = if missing { "missing" } else { "leaf" };
        let mut binds = Vec::new();
        for (name, rhs) in [
            (
                "main",
                json!({"node": "Var", "name": format!("$u$Main${target}"), "occ": target, "unique": target, "isGlobal": missing}),
            ),
            ("leaf", lit.clone()),
            ("dead", lit),
        ] {
            binds.push(
                json!({"rec": false, "pairs": [{"binder": binder(name), "rhs": rhs,
                "whnf": true, "trivial": true, "cheap": true, "okForSpec": true}]}),
            );
        }
        Module::from_raw(serde_json::from_value(json!({
            "format": raw::FORMAT, "module": "Main", "unit": "u", "ids": {},
            "types": [{"kind": "TyConApp", "tycon": {"name": "$u$Main$T", "occ": "T", "unique": "T"}, "args": []}],
            "binds": binds
        })).unwrap()).unwrap()
    }

    #[test]
    fn program_attempt_accounts_for_every_live_owner_and_skips_dead() {
        use h2r_lower::nir::{FnId, program::lower_program};
        let mut modules = [fixture()];
        // Dead unsupported code must not turn the attempt into a refusal.
        let dead_rhs = modules[0].top[2].pairs[0].rhs;
        modules[0].exprs[dead_rhs as usize] = h2r_core_ir::Expr::Coercion;
        let attempt = lower_program(&modules).unwrap();
        assert_eq!((attempt.live, attempt.dead), (2, 1));
        assert!(attempt.refused.is_empty());
        assert_eq!(
            attempt
                .lowered
                .iter()
                .map(|leaf| leaf.function.id)
                .collect::<Vec<_>>(),
            vec![FnId(0), FnId(1)]
        );
        let (report, refusals) = nir_program_report(&modules).unwrap();
        assert_eq!(refusals, 0);
        assert!(report.contains("2 = 2 lowered + 0 refused; 1 dead skipped"));
        assert!(report.contains("no executable output"));
        assert_eq!(report, nir_program_report(&modules).unwrap().0);
    }

    #[test]
    fn program_attempt_retains_successes_and_addressed_refusals() {
        use h2r_lower::nir::program::lower_program;
        let mut modules = [fixture()];
        let pair = &modules[0].top[1].pairs[0];
        let (owner, rhs) = (pair.binder, pair.rhs);
        modules[0].exprs[rhs as usize] = h2r_core_ir::Expr::Coercion;
        let attempt = lower_program(&modules).unwrap();
        // Main's reference can lower even when its target cannot. Never mistake
        // the accepted vector for a dependency-closed executable program.
        assert_eq!((attempt.lowered.len(), attempt.refused.len()), (1, 1));
        let refusal = &attempt.refused[0];
        assert_eq!(
            (refusal.module, refusal.owner, refusal.source),
            (0, owner, Some(rhs))
        );
        assert!(refusal.reason.contains("type or coercion"));
        let (report, refusals) = nir_program_report(&modules).unwrap();
        assert_eq!(refusals, 1);
        assert!(report.contains("2 = 1 lowered + 1 refused"));
        assert!(report.contains("LOWERED"));
        assert!(report.contains("REFUSED"));
        assert!(report.contains(&format!("at Some({rhs})")));
    }

    #[test]
    fn program_attempt_requires_authoritative_reachability() {
        use h2r_lower::nir::program::lower_program;
        assert!(lower_program(&[]).unwrap_err().contains("no root"));
        assert!(
            lower_program(&[fixture_with_link(true)])
                .unwrap_err()
                .contains("A5-IN-WORLD-MISSING")
        );
    }

    #[test]
    fn reports_verified_live_leaf_deterministically() {
        let modules = [fixture()];
        let first = nir_report(&modules, "$u$Main$leaf").unwrap();
        assert_eq!(first, nir_report(&modules, "$u$Main$leaf").unwrap());
        assert!(first.contains("not whole-program lowering"));
        assert!(first.contains("1 = 0 parameters + 0 type parameters + 1 value + 0 erased ticks"));
        assert!(first.contains("literal number \"7#\""));
        assert!(first.contains("return v0"));
        assert!(first.contains("Expr("));
    }

    #[test]
    fn refuses_dead_missing_ambiguous_and_unsupported_bindings() {
        let mut modules = [fixture()];
        assert!(
            nir_report(&modules, "$u$Main$dead")
                .unwrap_err()
                .to_string()
                .contains("not reachable")
        );
        assert!(
            nir_report(&modules, "leaf")
                .unwrap_err()
                .to_string()
                .contains("matched 0")
        );
        assert!(
            nir_report(&modules, "$u$Main$main")
                .unwrap()
                .contains("top-ref module 0")
        );
        let dead = modules[0].top[2].pairs[0].binder;
        modules[0].binders[dead as usize].name = "$u$Main$leaf".into();
        assert!(nir_report(&modules, "$u$Main$leaf").is_err());
        let mut modules = [fixture()];
        let source = modules[0].top[1].pairs[0].rhs;
        modules[0].exprs[source as usize] = h2r_core_ir::Expr::Coercion;
        assert!(
            nir_report(&modules, "$u$Main$leaf")
                .unwrap_err()
                .to_string()
                .contains("type or coercion")
        );
    }

    #[test]
    fn specialization_roots_from_an_audited_live_set() {
        let mut m = fixture();
        let owner = m.top[0].pairs[0].binder;
        m.binders[owner as usize].name = "$u$Main$notMain".into();
        assert!(
            nir_specialize_report(&[m], None)
                .unwrap_err()
                .to_string()
                .contains("no root")
        );
        assert!(
            nir_specialize_report(&[fixture_with_link(true)], None)
                .unwrap_err()
                .to_string()
                .contains("A5-IN-WORLD-MISSING")
        );
        let (report, refused) = nir_specialize_report(&[fixture()], None).unwrap();
        assert_eq!(refused, 0);
        assert!(report.contains("NIR specialization roots: 2 live bindings"));
    }

    #[test]
    fn refuses_missing_root_and_incomplete_linkage() {
        let mut m = fixture();
        let owner = m.top[0].pairs[0].binder;
        m.binders[owner as usize].name = "$u$Main$notMain".into();
        assert!(
            nir_report(&[m], "$u$Main$leaf")
                .unwrap_err()
                .to_string()
                .contains("no root")
        );
        assert!(
            nir_report(&[fixture_with_link(true)], "$u$Main$leaf")
                .unwrap_err()
                .to_string()
                .contains("A5-IN-WORLD-MISSING")
        );
    }
}
