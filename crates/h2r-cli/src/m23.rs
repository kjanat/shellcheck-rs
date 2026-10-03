//! Printing for M2.3f: the three representation views, the milestone
//! accounting, and the cross-milestone link.
//!
//! Kept out of `main.rs` because all three commands (`fields`, `lists`,
//! `text`) print the same accounting and `show` prints the same provenance
//! footer: one shape, one place.

use anyhow::{Result, anyhow};
use h2r_analysis::fields::FieldCensus;
use h2r_analysis::laziness::Census;
use h2r_analysis::lists::ListCensus;
use h2r_analysis::m23::{RepAccounting, RepLink};
use h2r_analysis::text::TextCensus;
use h2r_analysis::views::{FieldView, ListView, TextView, Verdicts, verify_all};
use h2r_core_ir::Module;

/// The three censuses, the verifier's answer for every claim, and the
/// milestone accounting derived from them. Every M2.3 command builds this
/// so that what it prints about a verdict is what `verify-rep` says about
/// it, rather than a second opinion.
pub struct M23<'m> {
    pub census: Census,
    pub fc: FieldCensus<'m>,
    pub lc: ListCensus<'m>,
    pub tc: TextCensus,
    pub cc: h2r_analysis::verify_rep::RepCrossCheck,
    pub verdicts: Verdicts,
    pub accounting: RepAccounting,
}

impl<'m> M23<'m> {
    pub fn of(selected: &'m [&'m Module]) -> M23<'m> {
        let census = Census::raw(selected.iter().copied());
        let fc = FieldCensus::of_modules(selected, &census);
        let lc = ListCensus::of_modules(selected, &census);
        let tc = TextCensus::of_modules(selected, &lc, &census);
        let (cc, verdicts) = verify_all(selected, &census, &fc, &lc, &tc);
        let accounting = h2r_analysis::m23::accounting(&fc, &lc, &tc, &verdicts);
        M23 {
            census,
            fc,
            lc,
            tc,
            cc,
            verdicts,
            accounting,
        }
    }
}

//------------------------------------------------------------------------------
// The accounting
//------------------------------------------------------------------------------

/// The milestone equation, in the shape M2.2's `before = normalised +
/// preserved + unsupported` established. Printed by `fields`, `lists`,
/// `text` and `verify-rep`, always whole, so that no command shows a
/// fragment of it.
pub fn print_accounting(a: &RepAccounting) {
    println!();
    println!("M2.3 accounting — fields: total = proven-eager + proven-lazy + dead + unsupported");
    println!(
        "  {:<20} {:>8} {:>12} {:>12} {:>6} {:>12}",
        "", "total", "proven-eager", "proven-lazy", "dead", "unsupported"
    );
    for r in &a.fields {
        println!(
            "  {:<20} {:>8} {:>12} {:>12} {:>6} {:>12}",
            r.label, r.before, r.proven_eager, r.proven_lazy, r.dead, r.unsupported
        );
    }
    println!("  proven-eager = Direct AND re-derived by the independent verifier; proven-lazy =");
    println!(
        "  Deferred (a coverage-only verdict nothing re-derives) plus Recursive where it was;"
    );
    println!("  `!` is a GHC-strict field. Any claim the verifier did not confirm is unsupported.");

    println!();
    println!("M2.3 accounting — lists and text: total = advised + unsupported");
    println!(
        "  {:<20} {:>8} {:>12} {:>12}   advised, by advisory",
        "", "total", "advised", "unsupported"
    );
    for r in [&a.lists, &a.text] {
        println!(
            "  {:<20} {:>8} {:>12} {:>12}   {}",
            r.label,
            r.before,
            r.advised,
            r.unsupported,
            r.by_advisory
                .iter()
                .map(|(n, c)| format!("{n} {c}"))
                .collect::<Vec<_>>()
                .join(", ")
        );
    }
    println!(
        "  advised = a named advisory, verified where the advisory is a claim (Vec, Iterator,"
    );
    println!("  StrongString, and the knot a LazyCandidate rests on); Unknown is unsupported.");

    println!();
    println!("M2.3 accounting — the M2 census' argument sites");
    println!(
        "  {:<58} {:>7} {:>8} {:>12} {:>9} {:>12}",
        "", "total", "proven", "advised-lazy", "deferred", "unsupported"
    );
    for r in &a.sites {
        println!(
            "  {:<58} {:>7} {:>8} {:>12} {:>9} {:>12}",
            r.label, r.before, r.proven, r.advised_lazy, r.deferred, r.unsupported
        );
    }

    println!();
    println!("Direct, by the route **set** that proves it (printed in full, zeros included)");
    for (key, n) in &a.routes {
        println!("  {:>7}  {key}", n);
    }
    println!("  R1 = the field is already strict · R2 = the expression is already a value ·");
    println!("  R3 = every scrutiny is at the construction's own evaluation frontier");
    if a.unconfirmed.is_empty() {
        println!(
            "  0 claim(s) unconfirmed by the verifier: nothing is counted as proven on one walk"
        );
    } else {
        println!("  claims the verifier did not confirm, counted as unsupported:");
        for (k, n) in &a.unconfirmed {
            println!("    {n:>5}  {k}");
        }
    }
}

//------------------------------------------------------------------------------
// The views
//------------------------------------------------------------------------------

pub fn print_field_view(v: &FieldView) {
    println!("{}", v.header());
    for l in &v.lines {
        println!("    {}", l.headline);
        if l.force_on_whnf {
            println!("        (GHC forces the field at WHNF even though nothing demands it)");
        }
        for o in &l.observations {
            println!("        {o}");
        }
        if let Some(e) = &l.escape {
            println!("        {e}");
        }
        for (rule, note) in &l.evidence {
            println!("        {rule}: {note}");
        }
        println!(
            "        verified: {}   field expression at node {}",
            l.verified.name(),
            l.expr
        );
    }
}

pub fn print_list_view(v: &ListView) {
    println!("{}", v.header());
    println!(
        "    producer  node {}{}{}",
        v.producer,
        v.bound
            .as_ref()
            .map(|b| format!(", bound to {b}"))
            .unwrap_or_default(),
        match (&v.list_ty, &v.elem_ty) {
            (Some(l), Some(e)) => format!("  [{l} / elem {e}]"),
            (Some(l), None) => format!("  [{l}]"),
            (None, Some(e)) => format!("  [elem {e}]"),
            (None, None) => String::new(),
        }
    );
    if !v.cells.is_empty() {
        println!(
            "    cells     {}{}",
            v.cells
                .iter()
                .map(|c| c.to_string())
                .collect::<Vec<_>>()
                .join(", "),
            if v.nil_terminated {
                " (nil-terminated)"
            } else {
                ""
            }
        );
    }
    println!(
        "    consumers ({}), each with the demand it contributes",
        v.consumers.len()
    );
    for c in &v.consumers {
        println!("        {}", c.headline);
        println!("            {}", c.what);
    }
    println!("    the facts");
    for (name, value, rule) in &v.facts {
        println!("        {name:<13} {value:<28} [{rule}]");
    }
    println!(
        "        {:<13} {:<28} [{}]",
        "traversals",
        format!(
            "{}{}",
            v.traversals,
            if v.streaming {
                ", every spine consumer streaming"
            } else {
                ""
            }
        ),
        if v.traversals > 1 {
            h2r_analysis::lists::L15_MULTIPASS
        } else {
            "one entry into the spine"
        }
    );
    println!(
        "        {:<13} {:<28} [what any representation must support, whatever the advisory says]",
        "constraints",
        if v.constraints.is_empty() {
            "none".to_string()
        } else {
            v.constraints.join(" ∧ ")
        }
    );
    for e in &v.escapes {
        println!("        escape        {e}");
    }
    if !v.successors.is_empty() {
        println!(
            "        successors    {}",
            v.successors
                .iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        );
    }
    println!(
        "    advisory  {} [{}] from {}",
        v.advisory.name(),
        v.advisory_rule,
        v.advisory_from
    );
    if let Some(r) = &v.advisory_reason {
        println!("        reason    {r}");
    }
    println!("        verified: {}", v.verified.name());
}

pub fn print_text_view(v: &TextView) {
    println!("{}", v.header());
    println!(
        "    selection (how Char was established: {})",
        v.element_type_evidence.name()
    );
    for (rule, note) in &v.selection {
        println!("        {rule}: {note}");
    }
    println!(
        "    shape     {} [{}]{}{}",
        v.shape.name(),
        v.shape_rule,
        if v.literal { ", a string literal" } else { "" },
        if v.append_operand {
            ", an operand of an append"
        } else {
            ""
        }
    );
    if let Some(a) = v.append_chain {
        println!(
            "    append    {} operand segment(s), {}, {} opaque",
            a.length,
            if a.all_literal {
                "all literal"
            } else {
                "not all literal"
            },
            a.opaque
        );
    }
    println!("    consumer classes");
    for (name, n) in &v.classes {
        println!("        {name:<16} {n}");
    }
    for c in &v.consumers {
        println!("        {c}");
    }
    println!("    char_semantics_required: {}", v.char_semantics_required);
    for r in &v.char_reasons {
        println!("        {r}");
    }
    if !v.shared_tails.is_empty() {
        println!(
            "    shared tails (inherited from L14): {}",
            v.shared_tails
                .iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        );
    }
    if !v.prefix_consumers.is_empty() {
        println!(
            "    prefix consumers (inherited): {}",
            v.prefix_consumers
                .iter()
                .map(|s| s.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        );
    }
    println!(
        "    advisory  {} [{}]{}",
        v.advisory.name(),
        v.advisory_rule,
        v.advisory_reason
            .as_ref()
            .map(|r| format!("  [{r}]"))
            .unwrap_or_default()
    );
    println!("        verified: {}", v.verified.name());
    println!();
    println!("  the list flow it refines");
    print_list_view(&v.list);
}

//------------------------------------------------------------------------------
// The view entry points
//------------------------------------------------------------------------------

pub fn field_views(
    m: &M23<'_>,
    modules: &[&Module],
    module: Option<&str>,
    node: Option<u32>,
    all: bool,
    json: bool,
) -> Result<()> {
    let want = |mo: &str, at: u32| match (module, node) {
        (Some(mm), Some(n)) => mo == mm && at == n,
        (Some(mm), None) => mo == mm,
        (None, Some(n)) => at == n,
        (None, None) => true,
    };
    let by_name: std::collections::HashMap<&str, &Module> =
        modules.iter().map(|x| (x.name.as_str(), *x)).collect();
    let mut views = Vec::new();
    for f in &m.fc.flows {
        if !want(&f.module, f.construction) {
            continue;
        }
        let Some(mm) = by_name.get(f.module.as_str()) else {
            continue;
        };
        views.push(FieldView::of(mm, f, &m.verdicts));
        if !all && node.is_some() {
            break;
        }
    }
    if views.is_empty() {
        return Err(anyhow!(
            "no constructor-field construction matches (use --module with --view)"
        ));
    }
    if json {
        serde_json::to_writer(std::io::stdout().lock(), &views)?;
        println!();
        return Ok(());
    }
    println!("The representation view — constructor fields");
    println!("  every field of every construction below appears exactly once (asserted)");
    println!();
    for v in &views {
        print_field_view(v);
        println!();
    }
    println!(
        "{} construction(s), {} field(s)",
        views.len(),
        views.iter().map(|v| v.lines.len()).sum::<usize>()
    );
    Ok(())
}

pub fn list_views(
    m: &M23<'_>,
    modules: &[&Module],
    module: Option<&str>,
    node: Option<u32>,
    all: bool,
    json: bool,
) -> Result<()> {
    let want = |mo: &str, at: u32| match (module, node) {
        (Some(mm), Some(n)) => mo == mm && at == n,
        (Some(mm), None) => mo == mm,
        (None, Some(n)) => at == n,
        (None, None) => true,
    };
    let by_name: std::collections::HashMap<&str, &Module> =
        modules.iter().map(|x| (x.name.as_str(), *x)).collect();
    let mut views = Vec::new();
    for f in &m.lc.flows {
        if !want(&f.module, f.producer) {
            continue;
        }
        let Some(mm) = by_name.get(f.module.as_str()) else {
            continue;
        };
        views.push(ListView::of(mm, f, &m.verdicts));
        if !all && node.is_some() {
            break;
        }
    }
    if views.is_empty() {
        return Err(anyhow!("no list flow matches (use --module with --view)"));
    }
    if json {
        serde_json::to_writer(std::io::stdout().lock(), &views)?;
        println!();
        return Ok(());
    }
    println!("The representation view — list flows");
    println!("  every consumer of every flow below appears exactly once (asserted)");
    println!();
    for v in &views {
        print_list_view(v);
        println!();
    }
    println!(
        "{} flow(s), {} consumer(s)",
        views.len(),
        views.iter().map(|v| v.consumers.len()).sum::<usize>()
    );
    Ok(())
}

pub fn text_views(
    m: &M23<'_>,
    modules: &[&Module],
    module: Option<&str>,
    node: Option<u32>,
    all: bool,
    json: bool,
) -> Result<()> {
    let want = |mo: &str, at: u32| match (module, node) {
        (Some(mm), Some(n)) => mo == mm && at == n,
        (Some(mm), None) => mo == mm,
        (None, Some(n)) => at == n,
        (None, None) => true,
    };
    let by_name: std::collections::HashMap<&str, &Module> =
        modules.iter().map(|x| (x.name.as_str(), *x)).collect();
    let mut views = Vec::new();
    for f in &m.tc.flows {
        if !want(&f.module, f.producer) {
            continue;
        }
        let Some(mm) = by_name.get(f.module.as_str()) else {
            continue;
        };
        views.push(TextView::of(mm, f, &m.lc.flows[f.list_flow], &m.verdicts));
        if !all && node.is_some() {
            break;
        }
    }
    if views.is_empty() {
        return Err(anyhow!("no text flow matches (use --module with --view)"));
    }
    if json {
        serde_json::to_writer(std::io::stdout().lock(), &views)?;
        println!();
        return Ok(());
    }
    println!("The representation view — text flows");
    println!("  the text facts on top of the list view; every consumer appears exactly once");
    println!();
    for v in &views {
        print_text_view(v);
        println!();
    }
    println!("{} text flow(s)", views.len());
    Ok(())
}

//------------------------------------------------------------------------------
// The cross-milestone link
//------------------------------------------------------------------------------

pub fn print_link(l: &RepLink) {
    println!();
    println!("Thunk sites explained by M2.3 (M1 × M2.2 × M2.3)");
    println!(
        "  of M1's {} potential thunk site(s), {} are explained by tuple transport (M2.2) and",
        l.thunk_sites, l.by_tuples
    );
    println!(
        "  {} by an M2.3 representation verdict the verifier confirms; {} remain.",
        l.explained.len(),
        l.remaining()
    );
    println!(
        "  {:<46} {:>7} {:>10} {:>9} {:>7}",
        "", "before", "by tuples", "by M2.3", "after"
    );
    for r in &l.fates {
        println!(
            "  {:<46} {:>7} {:>10} {:>9} {:>7}",
            r.label,
            r.before,
            r.by_tuples,
            r.by_m23,
            r.after()
        );
    }
    for r in &l.memo {
        println!(
            "  … {:<44} {:>7} {:>10} {:>9} {:>7}",
            r.label,
            r.before,
            r.by_tuples,
            r.by_m23,
            r.after()
        );
    }
    let all_before: usize = l.fates.iter().map(|r| r.before).sum();
    println!(
        "  {:<46} {:>7} {:>10} {:>9} {:>7}",
        "potential thunk sites",
        all_before,
        l.by_tuples,
        l.explained.len(),
        l.remaining()
    );
    println!(
        "  remaining + explained-by-tuples + explained-by-M2.3 = {} (asserted, and no site twice)",
        l.thunk_sites
    );
    println!("  by binder origin");
    for (o, before, t, mine) in &l.origins {
        println!(
            "    {:<44} {:>7} {:>10} {:>9} {:>7}",
            format!("{o:?}"),
            before,
            t,
            mine,
            before - t - mine
        );
    }
    println!("  by the rule that explains it");
    for (rule, n) in &l.by_rule {
        println!("    {:<44} {:>7}", rule, n);
    }
    println!();
    println!("  the M2 lazy-argument sites, from the other side");
    println!(
        "    {} of the 1,996 constructor-field sites stop being lazy positions: the field is",
        l.sites_1996_explained
    );
    println!(
        "    Direct and verified, or the spine it is consed into is consumed by one eager pass"
    );
    println!(
        "    {} of the {} append argument sites likewise",
        l.sites_1118_explained, l.sites_1118
    );
    println!();
    println!("  what is deliberately NOT counted, and why");
    for (what, n, why) in &l.not_counted {
        println!("    {n:>6}  {what}");
        println!("            {why}");
    }
}

//------------------------------------------------------------------------------
// The M2.2 side of the link
//------------------------------------------------------------------------------

/// The set of M1 thunk sites M2.2's own link explains, keyed the way M1
/// keys a binding. Read from `link::ThunkLink` rather than recomputed, so
/// the two milestones cannot disagree about who owns a site.
pub fn tuple_explained(
    tl: &h2r_analysis::link::ThunkLink,
) -> std::collections::HashSet<(String, u32, u32)> {
    tl.explained
        .iter()
        .map(|e| (e.module.clone(), e.let_node, e.rhs))
        .collect()
}
