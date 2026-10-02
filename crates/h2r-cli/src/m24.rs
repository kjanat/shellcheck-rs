//! Printing for M2.4g: the two views, the milestone accounting, and the
//! cross-milestone links.
//!
//! Kept out of `main.rs` for the reason [`crate::m23`] is: `classops`,
//! `higher` and `m24` all print the same accounting and `show` prints the
//! same provenance footers — one shape, one place.

use h2r_analysis::m24::{Accounting, BoundaryView, ClassopView, LinkSection, M1Link, M24};
use h2r_core_ir::Module;

//------------------------------------------------------------------------------
// The views
//------------------------------------------------------------------------------

/// One class-op site: the site, the class and the method, the dictionary
/// argument and its origin chain, the whole-program producer set of every
/// parameter hop, the target outcome, the totality fact, the erasure
/// verdict and its reason, and the owner's clone plan row.
pub fn print_classop_view(v: &ClassopView) {
    println!("{}", v.header());
    println!(
        "    class {} … method {} (field {}) … selector {}",
        v.class,
        v.method,
        v.field
            .map(|f| f.to_string())
            .unwrap_or_else(|| "?".to_string()),
        v.selector
    );
    match v.dict_arg {
        Some(d) => println!("    dictionary argument  node {d}  [K1-DICT-ARG]"),
        None => println!("    dictionary argument  none (the selector is the value) [K12-PARTIAL]"),
    }
    if v.origins.is_empty() {
        println!("    origin chain (per module)  none reached");
    } else {
        println!("    origin chain (per module), outermost step first");
        for o in &v.origins {
            println!("        {}", o.headline);
            for s in &o.steps {
                println!("            via {} [{}]", s.step, s.rule);
            }
        }
    }
    println!("    whole-program producer set, per parameter hop [W3-PARAM-UNION]");
    if v.hops.is_empty() {
        println!("        (the dictionary argument is not a dictionary parameter)");
    }
    for h in &v.hops {
        println!(
            "        {} {}.{} (binder {}){}",
            h.module,
            h.owner,
            h.occ,
            h.binder,
            if h.exported { ", exported" } else { "" }
        );
        match &h.top {
            Some(r) => println!("            set Top({r})"),
            None => println!(
                "            set {{{}}}  [verified: {}]",
                h.set.join(", "),
                h.verified_set.name()
            ),
        }
        println!(
            "            totality {} … erasure {} [verified: {}]",
            h.totality.label(),
            h.erasure,
            h.verified_erasure.name()
        );
    }
    println!(
        "    target   {}  [verified: {}]",
        v.outcome,
        v.verified_target.name()
    );
    println!("    per module (M2.4b)  {}", v.per_module_outcome);
    println!(
        "    dictionary set  {}  [verified: {}]",
        match &v.dict_top {
            Some(r) => format!("Top({r})"),
            None => format!("{{{}}}", v.dict_set.join(", ")),
        },
        v.verified_set.name()
    );
    println!(
        "    totality {}  [E6-TOTALITY-*]",
        v.totality
            .map(|t| t.label().to_string())
            .unwrap_or_else(|| "n/a (no dictionary this flow names)".into())
    );
    println!(
        "    erasure  {}{}  [verified: {}]",
        v.erasure.clone().unwrap_or_else(|| "n/a".into()),
        v.erasure_reason
            .as_ref()
            .map(|r| format!(" — {r}"))
            .unwrap_or_default(),
        v.verified_erasure.name()
    );
    match &v.clone_plan {
        Some(p) => println!("    owner clone plan  {p}"),
        None => println!("    owner clone plan  none (this owner needs no clone)"),
    }
    println!("    facts (no verdict attached)");
    for f in &v.facts {
        println!("        {f}");
    }
    println!("    rules  {}", v.rules.join(" "));
}

/// One function-valued boundary: the boundary, every producer with its
/// shape class and capture types, every use, the verdict with the rule
/// order that produced it, and the owner's clone tuples.
pub fn print_boundary_view(v: &BoundaryView) {
    println!("{}", v.header());
    println!(
        "    slot     {} {} at node {} of {}{}{}",
        v.kind,
        v.name,
        v.node,
        v.owner,
        if v.exported { ", exported" } else { "" },
        if v.valued { ", used as a value" } else { "" }
    );
    println!(
        "    facts    enumerated {} … {} shape class(es) … {}  [H11-SEPARATE: an enumerated \
         producer set is not one representation]",
        v.enumerated,
        v.classes,
        match &v.set_top {
            Some(r) => format!("set Top({r})"),
            None => "the producer set is accounted for".to_string(),
        }
    );
    println!("    producers ({})", v.producers.len());
    for p in &v.producers {
        println!(
            "        {:<40} {:<38} {}",
            p.key,
            p.kind,
            match p.arity {
                Some(a) => format!("arity {a}"),
                None => "opaque".to_string(),
            }
        );
        if p.opaque {
            println!(
                "            opaque: {} — equal to nothing, not even to another opaque shape",
                p.captures.join(", ")
            );
        } else {
            println!(
                "            captures [{}]  class {}",
                p.captures.join(" | "),
                p.shape_class
            );
        }
    }
    println!("    uses ({})", v.uses.len());
    for u in &v.uses {
        println!("        {:<44} node {}  args {}", u.kind, u.at, u.args);
    }
    println!("    the rule order that produced the verdict (H8 before H5/H6)");
    for r in &v.rule_order {
        println!(
            "        {} {:<14} {:<64} {}",
            if r.fired { "→" } else { " " },
            r.rule,
            r.asks,
            r.answer
        );
    }
    println!(
        "    verdict  {}{}  [verified: {}]",
        v.verdict,
        v.verdict_detail
            .as_ref()
            .map(|d| format!(" — {d}"))
            .unwrap_or_default(),
        v.verified.name()
    );
    println!(
        "    one representation {} … rewritable as one {} (strictly stronger: the rewrite must \
         own the slot)",
        v.one_representation, v.rewritable_as_one
    );
    match &v.owner_plan {
        Some(p) => {
            println!(
                "    owner clone plan  {p}  [verified: {}]",
                v.verified_plan.name()
            );
            for t in &v.owner_tuples {
                println!("        tuple {t}");
            }
            if v.owner_set_valued > 0 {
                println!(
                    "        {} tuple(s) have a set-valued component: this owner's clone count \
                     is a LOWER BOUND",
                    v.owner_set_valued
                );
            }
        }
        None => println!("    owner clone plan  none (this owner needs no clone)"),
    }
}

//------------------------------------------------------------------------------
// The accounting
//------------------------------------------------------------------------------

/// The milestone accounting, always whole: three separate questions, never
/// collapsed. Printed by `classops`, `higher` and `m24`.
pub fn print_accounting(a: &Accounting) {
    let ok = match a.check() {
        Ok(()) => "asserted".to_string(),
        Err(e) => format!("FAILED: {e}"),
    };
    println!();
    println!("M2.4 accounting — three questions, never collapsed. A known method target is not");
    println!("a removable dictionary (M2.4c); an enumerated producer set is not one");
    println!("representation (M2.4d). Every equation below: {ok}.");

    println!();
    println!("(1) can the call target be enumerated?   sites = Exact + FiniteSet + Unresolved");
    println!(
        "  {:<44} {:>8}",
        "class-op dispatch sites (population)", a.targets.sites
    );
    println!("  {:<44} {:>8}", "Exact(target)", a.targets.exact);
    println!("  {:<44} {:>8}", "FiniteSet(targets)", a.targets.finite);
    println!("  {:<44} {:>8}", "Unresolved", a.targets.unresolved);
    println!(
        "  {:<44} {:>8}   a SEPARATE fact, never added in",
        "… sites whose dictionary is bounded", a.targets.dict_bounded
    );
    println!(
        "  {:<44} {:>8} / {}",
        "re-derived by verify-m24 (Exact / bounded)",
        a.targets.verified_exact,
        a.targets.verified_bounded
    );

    println!();
    println!("(2) can this abstraction boundary use one representation?");
    println!("    boundaries = ExactClosure + TypeShapeUniform + FiniteClosureSet + CloneRequired");
    println!("               + Preserve + Unresolved");
    println!(
        "  {:<44} {:>8}",
        "function-valued boundaries (population)", a.representation.boundaries
    );
    for (i, name) in h2r_analysis::higher::VERDICTS.iter().enumerate() {
        println!("  {name:<44} {:>8}", a.representation.verdicts[i]);
    }
    println!(
        "  {:<44} {:>8}   enumerated, one shape class, no opaque producer",
        "one representation (the theorem)", a.representation.one_representation
    );
    println!(
        "  {:<44} {:>8}   strictly stronger: the rewrite must own the slot",
        "rewritable as one", a.representation.rewritable_as_one
    );
    println!(
        "  {:<44} {:>8}   a different fact again (H11-SEPARATE)",
        "producer set enumerated", a.representation.enumerated
    );
    println!(
        "  {:<44} {:>8} / {}",
        "re-derived by verify-m24 (of the claims)",
        a.representation.verified,
        a.representation.claims
    );

    println!();
    println!("(3) can the dictionary or closure object actually disappear?");
    println!("    values / parameters = Erasable + WithObligation + WithClone + Preserve");
    println!("                        + Unresolved");
    println!("  {:<28} {:>10} {:>12}", "verdict", "values", "parameters");
    for (i, name) in h2r_analysis::dictflow::VERDICTS.iter().enumerate() {
        println!(
            "  {name:<28} {:>10} {:>12}",
            a.erasure.value_verdicts[i], a.erasure.param_verdicts[i]
        );
    }
    println!(
        "  {:<28} {:>10} {:>12}",
        "total", a.erasure.values, a.erasure.params
    );
    println!(
        "  parameter totality: {} ProvenTotal, {} MustPreserveForce, {} Unknown; named force \
         obligations {}",
        a.erasure.param_totality[0],
        a.erasure.param_totality[1],
        a.erasure.param_totality[2],
        a.erasure.obligations
    );
    println!(
        "  re-derived by verify-m24: {} value claim(s), {} parameter claim(s)",
        a.erasure.verified_values, a.erasure.verified_params
    );
    println!();
    println!("  the two clone plans — OWNER-LEVEL. A per-slot cardinality is evidence and must");
    println!("  never be summed: a function is cloned once per DISTINCT call-site assignment");
    println!("  tuple, which is neither the sum nor the product of the per-slot counts.");
    println!(
        "  {:<36} {:>12} {:>8} {:>9} {:>9} {:>13}",
        "plan", "cardinality", "clones", "planned", "refused", "lower bounds"
    );
    for p in &a.erasure.plans {
        println!(
            "  {:<36} {:>12} {:>8} {:>9} {:>9} {:>13}",
            p.label,
            p.cardinality_sum,
            p.clones,
            p.owners_planned,
            p.owners_refused,
            p.lower_bounds
        );
    }
    println!("  a LOWER BOUND is a plan with a set-valued tuple component: the monovariant");
    println!("  fixpoint can only give one call site's argument as a set, and only a call-string");
    println!("  analysis can close it.");

    println!();
    println!("the two questions crossed — (target outcome) × (dictionary verdict)");
    print!("  {:<14}", "");
    for v in h2r_analysis::dictflow::VERDICTS {
        print!(" {v:>22}");
    }
    println!();
    for (i, row) in ["Exact", "FiniteSet", "Unresolved"].iter().enumerate() {
        print!("  {row:<14}");
        for n in a.matrix[i] {
            print!(" {n:>22}");
        }
        println!();
    }
    println!(
        "  a site whose method is known but whose dictionary must survive anyway: {}",
        a.preserved_dispatch
    );

    println!();
    println!("the residual, itemised and owned — class-op sites");
    for r in &a.residual_sites {
        println!("  {:>6}  {:<62} {}", r.n, r.what, r.whose);
    }
    println!();
    println!("the residual, itemised and owned — function-valued boundaries");
    for r in &a.residual_boundaries {
        println!("  {:>6}  {:<62} {}", r.n, r.what, r.whose);
    }
    println!();
    println!(
        "verify-m24: {} claim(s), {} disagreement(s), {} coverage refusal(s)",
        a.claims, a.disagreements, a.coverage_refusals
    );
}

//------------------------------------------------------------------------------
// The cross-milestone links
//------------------------------------------------------------------------------

pub fn print_link_section(s: &LinkSection) {
    println!();
    println!("  {} ({} site(s))", s.label, s.population);
    for r in &s.rows {
        println!("  {:>6}  {:<38} {}", r.n, r.what, r.note);
    }
    println!(
        "  {:>6}  COULD be reclassified by a later pass. Reported, not acted on.",
        s.could_reclassify
    );
    if !s.note.is_empty() {
        println!("          {}", s.note);
    }
}

/// The M1 table, with M2.4's column added and the invariant stated.
pub fn print_m1_link(l: &M1Link) {
    println!();
    println!("Thunk sites explained by M2.4 (M1 × M2.2 × M2.3 × M2.4)");
    println!(
        "  {:<50} {:>7} {:>10} {:>9} {:>9} {:>7}",
        "", "before", "by tuples", "by M2.3", "by M2.4", "after"
    );
    for r in &l.rows {
        println!(
            "  {:<50} {:>7} {:>10} {:>9} {:>9} {:>7}",
            r.label,
            r.before,
            r.by_tuples,
            r.by_m23,
            r.by_m24,
            r.after()
        );
    }
    println!(
        "  {:<50} {:>7} {:>10} {:>9} {:>9} {:>7}",
        "potential thunk sites",
        l.thunk_sites,
        l.by_tuples,
        l.by_m23,
        l.explained.len(),
        l.remaining()
    );
    println!(
        "  remaining + explained-by-tuples + explained-by-M2.3 + explained-by-M2.4 = {}: asserted,\n  \
         and no site is counted twice — a site an earlier milestone explains is that\n  \
         milestone's, and this walk skips it before it can claim it.",
        l.thunk_sites
    );
    println!(
        "  the population this link draws on: {} of the {} thunk sites are $d… dictionary\n  \
         bindings (Origin::Dictionary); {} of those have a dictionary value at the binding's\n  \
         own node for the whole-program flow to name.",
        l.dictionary_sites, l.thunk_sites, l.dictionary_sites_with_a_value
    );
    println!(
        "  by the rule  {} {}",
        h2r_analysis::m24::M24_D_DICT_ERASED,
        l.explained.len()
    );
    println!("  what was deliberately NOT counted");
    for (what, n, why) in &l.not_counted {
        println!("  {n:>6}  {what}");
        println!("          {why}");
    }
    if !l.not_erasable_reasons.is_empty() {
        println!("  …and why those dictionaries are not Erasable, by the verdict's own reason");
        for (why, n) in &l.not_erasable_reasons {
            println!("  {n:>6}  {why}");
        }
    }
    for e in l.explained.iter().take(20) {
        println!(
            "    {} {} (let {} rhs {}) — {}",
            e.module, e.occ, e.let_node, e.rhs, e.detail
        );
    }
}

//------------------------------------------------------------------------------
// The M2.4 summary command
//------------------------------------------------------------------------------

/// Everything the milestone claims, in one place: the accounting, the
/// matrix, the residual, the four cross-links and the verifier's result.
pub struct Summary<'m> {
    pub m24: M24<'m>,
    pub accounting: Accounting,
}

impl<'m> Summary<'m> {
    pub fn of(modules: &[&'m Module]) -> Summary<'m> {
        let m24 = M24::of_modules(modules);
        let accounting = h2r_analysis::m24::accounting(&m24);
        accounting
            .check()
            .unwrap_or_else(|e| panic!("the M2.4 accounting must close: {e}"));
        Summary { m24, accounting }
    }
}

/// The verifier's own result, in the shape M2.4f publishes it.
pub fn print_verifier(m24: &M24) {
    let a = &m24.audit;
    println!();
    println!("verify-m24 (M2.4f), re-run here rather than quoted");
    println!("  {:<44} {:>8}", "positive claims re-derived", a.checked);
    println!("  {:<44} {:>8}", "agreed", a.agreed);
    println!("  {:<44} {:>8}", "DISAGREEMENTS", a.real_disagreements());
    println!("  {:<44} {:>8}", "coverage refusals", a.coverage_refusals());
    println!("  trusted inputs, consulted and not verified:");
    println!("    1. the 17-class method-field table (classops::CLASSES), a level-5 axiom");
    println!("    2. W0-CLOSED-WORLD / H0-CLOSED-WORLD: the 28 modules are the whole program");
    println!("    3. GHC's own flags: isClassOpId, isExportedId, the demand signatures");
    println!("    4. the structured Ty, and TyCon stable-name identity");
}
