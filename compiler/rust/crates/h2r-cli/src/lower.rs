//! `h2r lower` — the lowering reports. M3a: `Main.main`-rooted
//! reachability over the closed world, with the independent verifier's
//! result printed beside it.
//!
//! Kept out of `main.rs` for the reason [`crate::m23`] and [`crate::m24`]
//! are: every later sub-milestone prints into the same report.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use anyhow::{Result, bail};
use h2r_core_ir::{Module, load_dir};
use h2r_lower::reachability::{DeadReason, LiveSet, NodeId, RULES, TRUSTED, root_name};
use h2r_lower::verify::{Audit, verify};

/// One row of the [`A5-IN-WORLD-MISSING`] table, grouped by the module the
/// unlinkable name points into: how many names, how many occurrences, and
/// which live modules carry them.
type TargetRow<'a> = (usize, u32, BTreeSet<&'a str>);

/// How many bindings `--explain` spells out when a name matches several.
const EXPLAIN_CAP: usize = 20;

/// How many import names the summary lists.
const TOP_IMPORTS: usize = 20;

pub fn lower(
    dir: &Path,
    reachability: bool,
    json: bool,
    rules: bool,
    explain: Option<String>,
) -> Result<()> {
    if rules {
        print_rules();
        return Ok(());
    }
    if !reachability {
        bail!(
            "h2r lower needs a question. M3a implements one: --reachability \
             (the Main.main-rooted live set). --rules prints the rule table."
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

    if let Some(what) = explain {
        return print_explain(&live, &what);
    }

    print_report(&selected, &live, &audit);
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
                for (i, &step) in l.witness.iter().enumerate() {
                    let s = live.node(step);
                    let rule = if i == 0 {
                        live.roots
                            .iter()
                            .find(|r| r.node == step)
                            .map(|r| r.rule)
                            .unwrap_or("?")
                    } else {
                        let prev = l.witness[i - 1];
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
