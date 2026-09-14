//! `h2r` -- driver for the Haskell-to-Rust compiler.
//!
//! Right now it only inspects the Core that `h2r-plugin` dumps. The lowering
//! passes will hang off the same subcommand structure.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use anyhow::Result;
use clap::{Parser, Subcommand};
use h2r_analysis::callee::{Family, Resolution, Tier};
use h2r_analysis::laziness::{Census, Class, Fate, Origin, TopClass};
use h2r_analysis::shape::{ArgShape, Position};
use h2r_core_ir::{BinderKind, Expr, Module, load_dir, with_big_stack};

mod m23;

#[derive(Parser)]
#[command(name = "h2r", about = "Haskell (GHC Core) to Rust compiler driver")]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Summarise the Core dumps in a directory.
    Stats {
        /// Directory containing *.core.json
        dir: PathBuf,
        /// Print a per-module breakdown as well as the totals.
        #[arg(long)]
        per_module: bool,
    },
    /// List the top-level binders of one module, with their demand signatures.
    Binders {
        dir: PathBuf,
        /// Module name, e.g. ShellCheck.Parser
        module: String,
    },
    /// Print the Core subtree at a node id (as reported by `laziness --explain`).
    Show {
        dir: PathBuf,
        module: String,
        /// Node id; omit to print every top-level binding.
        node: Option<u32>,
        #[arg(long, default_value_t = 8)]
        depth: usize,
        /// Print the enclosing context this many ancestors up.
        #[arg(long, default_value_t = 0)]
        up: usize,
        /// Do not load the Parsec proof object. It is loaded by default
        /// whenever the module has recognised regions, which is what
        /// annotates region entries, role binders, their occurrences and
        /// the spine roots of proven edges, and prints the evidence footer.
        #[arg(long)]
        no_parsec: bool,
        /// Do not load the tuple proof object. It is loaded by default
        /// whenever the module has tuple flows, and annotates
        /// constructions, alias binders, consumers and their occurrences
        /// inline, with the flow's own evidence as a footer.
        #[arg(long)]
        no_tuples: bool,
        /// Do not load M2.3b's constructor-field proof object. It is
        /// loaded by default whenever the module has constructions, and
        /// annotates constructions and field binders inline with the
        /// per-field verdict and its verification status as a footer.
        #[arg(long)]
        no_fields: bool,
        /// Do not load M2.3c's list proof object: producers, cells, tail
        /// aliases and consumers, with the six facts and the advisory.
        #[arg(long)]
        no_lists: bool,
        /// Do not load M2.3d's text proof object, which refines a list
        /// flow's footer with the text facts and the text advisory.
        #[arg(long)]
        no_text: bool,
    },
    /// Compare census metrics across several Core dump directories
    /// (e.g. the GHC flag matrix). Arguments are `label=dir` or plain dirs.
    Compare { dirs: Vec<String> },
    /// Prove Parsec's CPS roles structurally and account for the sites the
    /// census leaves unresolved with a Parsec-shaped head.
    Parsec {
        dir: PathBuf,
        /// Restrict to one module.
        #[arg(long)]
        module: Option<String>,
        /// Emit regions, edges and the accounting as JSON.
        #[arg(long)]
        json: bool,
        /// Print per-region evidence and per-reject reasons with node ids.
        #[arg(long)]
        explain: bool,
        /// Print the recovered control-flow graph of the region whose entry
        /// is this node (or of the innermost region containing it).
        #[arg(long)]
        cfg: Option<u32>,
        /// Print one control-flow graph block per region. Use --module.
        #[arg(long)]
        cfg_all: bool,
    },
    /// Census every saturated tuple construction and prove, by def-use,
    /// which ones are transformer/worker plumbing and which are real values.
    Tuples {
        dir: PathBuf,
        /// Restrict to one module.
        #[arg(long)]
        module: Option<String>,
        /// Emit the flows and the accounting as JSON.
        #[arg(long)]
        json: bool,
        /// Print every construction with its evidence and node ids.
        #[arg(long)]
        explain: bool,
        /// Re-derive every removable verdict with the independent
        /// verifier and report the disagreements.
        #[arg(long)]
        verify: bool,
        /// Print the normalised scalar view of one construction: what the
        /// program looks like with that tuple gone.
        #[arg(long)]
        scalar: Option<u32>,
        /// Print the scalar view of every removable construction. Use
        /// --module.
        #[arg(long)]
        scalar_all: bool,
        /// Enumerate the representation boundaries the removable flows
        /// cross, and report which of them can be split uniformly.
        #[arg(long)]
        boundaries: bool,
    },
    /// Census every saturated non-tuple, non-list data-constructor
    /// application and prove, per field, what the Core demands of it and
    /// when.
    Fields {
        dir: PathBuf,
        /// Restrict to one module.
        #[arg(long)]
        module: Option<String>,
        /// Emit the flows and the accounting as JSON.
        #[arg(long)]
        json: bool,
        /// Print every construction with its observations and evidence.
        #[arg(long)]
        explain: bool,
        /// Print one data constructor's fields, with the per-construction
        /// verdicts behind each one. Matches on the occurrence name.
        #[arg(long)]
        con: Option<String>,
        /// Print the representation view of one construction: every field
        /// on one line with the three facts, the derived rep and the route
        /// that proved it, then the observations that justify the facts.
        #[arg(long)]
        view: Option<u32>,
        /// The same for every construction. Use --module.
        #[arg(long)]
        view_all: bool,
    },
    /// Census every list flow and prove, by def-use plus an explicit
    /// library demand-semantics table, when and how much of each spine is
    /// demanded, by whom, how often, and what aliases its tail.
    Lists {
        dir: PathBuf,
        /// Restrict to one module.
        #[arg(long)]
        module: Option<String>,
        /// Emit the flows and the accounting as JSON.
        #[arg(long)]
        json: bool,
        /// Print every flow with its facts, consumers and node ids.
        #[arg(long)]
        explain: bool,
        /// Print the library demand-semantics table.
        #[arg(long)]
        axioms: bool,
        /// Print the representation view of one flow: its producer, every
        /// cell, every consumer with its rule and the demand it
        /// contributes, the six facts, and the advisory.
        #[arg(long)]
        view: Option<u32>,
        /// The same for every flow. Use --module.
        #[arg(long)]
        view_all: bool,
    },
    /// Select the text (`[Char]`) flows out of the list census and record
    /// what the program does with them. Nothing here decides `String`.
    Text {
        dir: PathBuf,
        /// Restrict to one module.
        #[arg(long)]
        module: Option<String>,
        /// Emit the flows and the accounting as JSON.
        #[arg(long)]
        json: bool,
        /// Print every text flow with its facts, consumers and node ids.
        #[arg(long)]
        explain: bool,
        /// Print the text-head table.
        #[arg(long)]
        heads: bool,
        /// Print the representation view of one text flow: the text facts
        /// on top of the list view.
        #[arg(long)]
        view: Option<u32>,
        /// The same for every text flow. Use --module.
        #[arg(long)]
        view_all: bool,
    },
    /// Re-derive, with a second walk that shares nothing with them but the
    /// IR, every M2.3 verdict whose being wrong would be a miscompile:
    /// `Direct` and `Dead` fields, `VecCandidate`/`IteratorCandidate`
    /// spines and `StrongStringCandidate` text.
    VerifyRep {
        dir: PathBuf,
        /// Restrict to one module.
        #[arg(long)]
        module: Option<String>,
        /// Emit the cross-check as JSON.
        #[arg(long)]
        json: bool,
        /// Print every disagreement, not just the summary by reason.
        #[arg(long)]
        explain: bool,
    },
    /// The residual-laziness census: why does each local binding still exist?
    Laziness {
        dir: PathBuf,
        /// Restrict to one module.
        #[arg(long)]
        module: Option<String>,
        /// Print every binding with its classification and reasons.
        #[arg(long)]
        explain: bool,
        /// Only explain bindings that are potential thunk sites.
        #[arg(long)]
        thunks_only: bool,
        /// Emit the full census as JSON instead of a report.
        #[arg(long)]
        json: bool,
    },
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    with_big_stack(move || match cli.command {
        Command::Stats { dir, per_module } => stats(&dir, per_module),
        Command::Binders { dir, module } => binders(&dir, &module),
        Command::Compare { dirs } => compare(&dirs),
        Command::Show {
            dir,
            module,
            node,
            depth,
            up,
            no_parsec,
            no_fields,
            no_lists,
            no_text,
            no_tuples,
        } => show(
            &dir, &module, node, depth, up, !no_parsec, !no_tuples, !no_fields, !no_lists, !no_text,
        ),
        Command::Laziness {
            dir,
            module,
            explain,
            thunks_only,
            json,
        } => laziness(&dir, module.as_deref(), explain, thunks_only, json),
        Command::Tuples {
            dir,
            module,
            json,
            explain,
            verify,
            scalar,
            scalar_all,
            boundaries,
        } => tuples(
            &dir,
            module.as_deref(),
            json,
            explain,
            verify,
            scalar,
            scalar_all,
            boundaries,
        ),
        Command::Fields {
            dir,
            module,
            json,
            explain,
            con,
            view,
            view_all,
        } => fields(
            &dir,
            module.as_deref(),
            json,
            explain,
            con.as_deref(),
            view,
            view_all,
        ),
        Command::Lists {
            dir,
            module,
            json,
            explain,
            axioms,
            view,
            view_all,
        } => lists(
            &dir,
            module.as_deref(),
            json,
            explain,
            axioms,
            view,
            view_all,
        ),
        Command::Text {
            dir,
            module,
            json,
            explain,
            heads,
            view,
            view_all,
        } => text(
            &dir,
            module.as_deref(),
            json,
            explain,
            heads,
            view,
            view_all,
        ),
        Command::VerifyRep {
            dir,
            module,
            json,
            explain,
        } => verify_rep(&dir, module.as_deref(), json, explain),
        Command::Parsec {
            dir,
            module,
            json,
            explain,
            cfg,
            cfg_all,
        } => parsec(&dir, module.as_deref(), json, explain, cfg, cfg_all),
    })?
}

//------------------------------------------------------------------------------
// stats
//------------------------------------------------------------------------------

#[derive(Default)]
struct Counts {
    modules: usize,
    top_level_binds: usize,
    rec_groups: usize,
    binders: usize,
    join_points: usize,
    nodes: BTreeMap<&'static str, usize>,
    dmd_sigs: BTreeMap<String, usize>,
}

fn node_name(e: &Expr) -> &'static str {
    match e {
        Expr::Var { .. } => "Var",
        Expr::Lit(_) => "Lit",
        Expr::App { .. } => "App",
        Expr::Lam { .. } => "Lam",
        Expr::Let { .. } => "Let",
        Expr::Case { .. } => "Case",
        Expr::Cast(_) => "Cast",
        Expr::Tick(_) => "Tick",
        Expr::Type(_) => "Type",
        Expr::Coercion => "Coercion",
    }
}

impl Counts {
    fn add_module(&mut self, m: &Module) {
        self.modules += 1;
        for bind in &m.top {
            if bind.recursive {
                self.rec_groups += 1;
            }
            self.top_level_binds += bind.pairs.len();
        }
        for e in &m.exprs {
            *self.nodes.entry(node_name(e)).or_default() += 1;
        }
        for b in &m.binders {
            self.binders += 1;
            if b.is_join_point == Some(true) {
                self.join_points += 1;
            }
            if b.kind == BinderKind::Id
                && let Some(sig) = &b.dmd_sig
            {
                *self.dmd_sigs.entry(sig.pretty.clone()).or_default() += 1;
            }
        }
    }
}

fn stats(dir: &Path, per_module: bool) -> Result<()> {
    let modules = load_dir(dir)?;
    let mut total = Counts::default();

    for m in &modules {
        if per_module {
            let mut one = Counts::default();
            one.add_module(m);
            let nodes: usize = one.nodes.values().sum();
            println!(
                "{:<34} binds={:<6} rec-groups={:<4} binders={:<7} nodes={}",
                m.name, one.top_level_binds, one.rec_groups, one.binders, nodes
            );
        }
        total.add_module(m);
    }

    if per_module {
        println!();
    }
    println!("modules          {}", total.modules);
    println!("top-level binds  {}", total.top_level_binds);
    println!("recursive groups {}", total.rec_groups);
    println!("binders          {}", total.binders);
    println!("join points      {}", total.join_points);
    println!("core nodes       {}", total.nodes.values().sum::<usize>());
    println!();
    println!("node histogram:");
    let mut nodes: Vec<_> = total.nodes.iter().collect();
    nodes.sort_by(|a, b| b.1.cmp(a.1));
    for (name, count) in nodes {
        println!("  {name:<10} {count:>9}");
    }

    println!();
    println!("most common demand signatures:");
    let mut sigs: Vec<_> = total.dmd_sigs.iter().collect();
    sigs.sort_by(|a, b| b.1.cmp(a.1).then(a.0.cmp(b.0)));
    for (sig, count) in sigs.into_iter().take(15) {
        let shown = if sig.is_empty() { "<none>" } else { sig };
        println!("  {count:>8}  {shown}");
    }

    Ok(())
}

//------------------------------------------------------------------------------
// binders
//------------------------------------------------------------------------------

fn nonempty(s: Option<&str>) -> &str {
    match s {
        Some(s) if !s.is_empty() => s,
        _ => "-",
    }
}

fn find_module<'a>(modules: &'a [Module], name: &str) -> Result<&'a Module> {
    modules.iter().find(|m| m.name == name).ok_or_else(|| {
        anyhow::anyhow!(
            "no Core dump for module {name}; have: {}",
            modules
                .iter()
                .map(|m| m.name.as_str())
                .collect::<Vec<_>>()
                .join(", ")
        )
    })
}

fn binders(dir: &Path, module: &str) -> Result<()> {
    let modules = load_dir(dir)?;
    let m = find_module(&modules, module)?;

    for bind in &m.top {
        for pair in &bind.pairs {
            let b = m.binder(pair.binder);
            println!(
                "{}{:<38} arity={:<3} dmd={:<22} cpr={}",
                if bind.recursive { "rec " } else { "    " },
                b.occ,
                b.arity.unwrap_or(0),
                nonempty(b.dmd_sig.as_ref().map(|s| s.pretty.as_str())),
                nonempty(b.cpr_sig.as_deref()),
            );
            println!("        :: {}", b.ty);
        }
    }
    Ok(())
}

//------------------------------------------------------------------------------
// show
//------------------------------------------------------------------------------

/// Both proof objects can have something to say about one node; the marks
/// are concatenated, never merged, so it stays visible which object said
/// what.
fn join_notes(a: Option<String>, b: Option<String>) -> Option<String> {
    match (a, b) {
        (Some(x), Some(y)) => Some(format!("{x}; {y}")),
        (x, y) => x.or(y),
    }
}

#[allow(clippy::too_many_arguments)]
fn show(
    dir: &Path,
    module: &str,
    node: Option<u32>,
    depth: usize,
    up: usize,
    parsec: bool,
    tuples_on: bool,
    fields_on: bool,
    lists_on: bool,
    text_on: bool,
) -> Result<()> {
    let modules = load_dir(dir)?;
    let m = find_module(&modules, module)?;
    // The proof object is loaded once, by default, and only when this
    // module actually has regions; `--no-parsec` skips it.
    let analysis = match parsec {
        true => {
            let a = h2r_analysis::parsec::Analysis::of_module(m);
            if a.regions.is_empty() { None } else { Some(a) }
        }
        false => None,
    };
    // The tuple proof object, on the same terms: loaded by default when the
    // module has flows, `--no-tuples` skips it. The Parsec hops are read
    // for it exactly as `h2r tuples` reads them, so a continuation-carried
    // tuple is annotated here too.
    let tuples = match tuples_on {
        true => {
            let hops = analysis
                .as_ref()
                .map(h2r_analysis::tuples::parsec_hops)
                .unwrap_or_default();
            let mut t = h2r_analysis::tuples::Tuples::of_module_with(m, Some(&hops));
            // The boundary check is part of the verdict, not a report, so
            // the fate `show` prints is the same one `h2r tuples` counts.
            t.settle_boundaries();
            if t.flows.is_empty() { None } else { Some(t) }
        }
        false => None,
    };
    // Only the flows actually printed are verified, so `show` stays a
    // per-node query rather than a whole-module analysis.
    let prov = tuples.as_ref().map(|t| {
        let mut v = h2r_analysis::verify::Verifier::new(m).with_hops(t.hops.clone());
        let verified = t
            .flows
            .iter()
            .filter(|f| {
                matches!(
                    f.fate,
                    h2r_analysis::tuples::TupleFate::ScalarReplace
                        | h2r_analysis::tuples::TupleFate::WorkerReturn
                )
            })
            .filter(|f| v.verify(f.construction).is_ok())
            .map(|f| f.construction)
            .collect();
        h2r_analysis::scalar::Provenance::of(t, verified)
    });
    // The three M2.3 proof objects, on exactly the terms the tuple one is
    // loaded on: by default when the module has any, and skipped by
    // `--no-fields` / `--no-lists` / `--no-text`. The list census needs the
    // field census' reads, and the text census needs the list one, so what
    // is actually *computed* is the smallest set that answers what was
    // asked for; what is *annotated* is only what was not turned off.
    let one = [m];
    let m23_census = Census::raw(one.iter().copied());
    let m23_fields = fields_on
        .then(|| h2r_analysis::fields::Fields::of_module(m, &m23_census))
        .filter(|f| !f.flows.is_empty());
    let m23_lists = (lists_on || text_on).then(|| {
        let reads = h2r_analysis::fields::Fields::of_module(m, &m23_census).field_reads();
        h2r_analysis::lists::Lists::of_module(m, &m23_census, &reads)
    });
    let m23_lists = m23_lists.filter(|l| !l.flows.is_empty());
    let m23_text: Vec<h2r_analysis::text::TextFlow> = match (text_on, &m23_lists) {
        (true, Some(_)) => {
            let lc = h2r_analysis::lists::ListCensus::of_modules(&one, &m23_census);
            let tc = h2r_analysis::text::TextCensus::of_modules(&one, &lc, &m23_census);
            tc.flows
        }
        _ => Vec::new(),
    };
    // Only the claims of this module are verified, so `show` stays a
    // per-node query rather than a whole-program analysis — the same rule
    // the tuple verifier above follows.
    let m23_verdicts = match (&m23_fields, &m23_lists) {
        (None, None) => h2r_analysis::views::Verdicts::default(),
        _ => {
            let fc = h2r_analysis::fields::FieldCensus::of_modules(&one, &m23_census);
            let lc = h2r_analysis::lists::ListCensus::of_modules(&one, &m23_census);
            let tc = h2r_analysis::text::TextCensus::of_modules(&one, &lc, &m23_census);
            h2r_analysis::views::verify_all(&one, &m23_census, &fc, &lc, &tc).1
        }
    };
    let rep = (m23_fields.is_some() || (lists_on && m23_lists.is_some()) || !m23_text.is_empty())
        .then(|| {
            h2r_analysis::views::Provenance::of(
                m,
                m23_fields.as_ref(),
                m23_lists.as_ref(),
                &m23_text,
                &m23_verdicts,
                lists_on,
            )
        });
    let note = |id: u32| {
        join_notes(
            join_notes(
                analysis.as_ref().and_then(|a| a.node_note(id)),
                prov.as_ref().and_then(|p| p.node_note(id)),
            ),
            rep.as_ref().and_then(|p| p.node_note(id)),
        )
    };
    let bnote = |b: u32| {
        join_notes(
            join_notes(
                analysis.as_ref().and_then(|a| a.binder_note(b)),
                prov.as_ref().and_then(|p| p.binder_note(b)),
            ),
            rep.as_ref().and_then(|p| p.binder_note(b)),
        )
    };
    let pretty = h2r_core_ir::pretty::Pretty {
        module: m,
        max_depth: depth,
        ids: true,
        note: Some(&note),
        binder_note: Some(&bnote),
    };
    match node {
        Some(mut id) => {
            let requested = id;
            for _ in 0..up {
                match m.parent[id as usize] {
                    Some(p) => id = p,
                    None => break,
                }
            }
            let mut top = id;
            while let Some(p) = m.parent[top as usize] {
                top = p;
            }
            if let h2r_core_ir::Edge::Top { pair } = m.edge[top as usize] {
                let occ = &m
                    .binder(
                        m.top
                            .iter()
                            .flat_map(|b| &b.pairs)
                            .nth(pair as usize)
                            .unwrap()
                            .binder,
                    )
                    .occ;
                println!("-- in top-level binding {occ}, node {id}");
            }
            println!("{}", pretty.render(id));
            if let Some(a) = &analysis {
                let p = a.proof_at(requested);
                if !p.is_empty() {
                    println!();
                    println!("node {}", p.node);
                    if let Some(n) = &p.normalized {
                        println!("  normalized as: {n}");
                    }
                    if let Some(c) = &p.continuation {
                        println!("  continuation: {c}");
                    }
                    if let Some(r) = &p.role {
                        println!("  intrinsic role: {r}");
                    }
                    if !p.evidence.is_empty() {
                        println!("  evidence:");
                        for (rule, note) in &p.evidence {
                            println!("    {rule}: {note}");
                        }
                    }
                }
            }
            if let Some(pv) = &prov {
                for i in pv.flows_at(requested) {
                    let p = pv.proof_at(requested, i);
                    println!();
                    println!("node {}", p.node);
                    if let Some(t) = &p.tuple {
                        println!("  tuple: {t}");
                    }
                    if let Some(f) = &p.fate {
                        println!("  fate: {f}");
                    }
                    if let Some(r) = &p.role {
                        println!("  this node: {r}");
                    }
                    if !p.consumers.is_empty() {
                        println!("  consumers:");
                        for c in &p.consumers {
                            println!("    {c}");
                        }
                    }
                    if !p.evidence.is_empty() {
                        println!("  evidence:");
                        for (rule, note) in &p.evidence {
                            println!("    {rule}: {note}");
                        }
                    }
                }
            }
            if let Some(rp) = &rep {
                for p in rp.proofs_at(requested) {
                    if p.is_empty() {
                        continue;
                    }
                    println!();
                    println!("node {}", p.node);
                    if let Some(w) = &p.what {
                        println!("  {w}");
                    }
                    if let Some(v) = &p.verdict {
                        println!("  {v}");
                    }
                    if let Some(r) = &p.role {
                        println!("  this node: {r}");
                    }
                    for f in &p.facts {
                        println!("  {f}");
                    }
                    if !p.consumers.is_empty() {
                        println!("  consumers:");
                        for c in &p.consumers {
                            println!("    {c}");
                        }
                    }
                    if !p.evidence.is_empty() {
                        println!("  evidence:");
                        for (rule, note) in &p.evidence {
                            println!("    {rule}: {note}");
                        }
                    }
                }
            }
        }
        None => {
            for bind in &m.top {
                for pair in &bind.pairs {
                    println!(
                        "{} = {}",
                        m.binder(pair.binder).occ,
                        pretty.render(pair.rhs)
                    );
                    println!();
                }
            }
        }
    }
    Ok(())
}

//------------------------------------------------------------------------------
// compare
//------------------------------------------------------------------------------

fn compare(specs: &[String]) -> Result<()> {
    let mut columns: Vec<(String, h2r_analysis::metrics::Metrics)> = Vec::new();
    let mut module_sets: Vec<Vec<String>> = Vec::new();
    for spec in specs {
        let (label, dir) = match spec.split_once('=') {
            Some((l, d)) => (l.to_string(), PathBuf::from(d)),
            None => (spec.clone(), PathBuf::from(spec)),
        };
        let modules = load_dir(&dir)?;
        let census = Census::of_modules(modules.iter());
        let core_nodes = modules.iter().map(|m| m.exprs.len()).sum();
        let top = modules
            .iter()
            .map(|m| m.top.iter().map(|b| b.pairs.len()).sum::<usize>())
            .sum();
        let selected: Vec<&Module> = modules.iter().collect();
        let raw = Census::raw(selected.iter().copied());
        let analyses: Vec<h2r_analysis::parsec::Analysis> = selected
            .iter()
            .map(|m| h2r_analysis::parsec::Analysis::of_module(m))
            .collect();
        let hops: Vec<h2r_analysis::tuples::ParsecHops> = analyses
            .iter()
            .map(h2r_analysis::tuples::parsec_hops)
            .collect();
        let tuples = h2r_analysis::tuples::TupleCensus::of_modules_with(&selected, &raw, &hops);
        columns.push((
            label,
            h2r_analysis::metrics::Metrics::of(&census, Some(&tuples), core_nodes, top),
        ));
        let mut names: Vec<String> = modules.iter().map(|m| m.name.clone()).collect();
        names.sort();
        module_sets.push(names);
    }
    let Some((_, first)) = columns.first() else {
        anyhow::bail!("no directories given");
    };
    print!("{:<32}", "");
    for (label, _) in &columns {
        print!(" {label:>9}");
    }
    println!();
    print!("{:<32}", "modules");
    for set in &module_sets {
        print!(" {:>9}", set.len());
    }
    println!();
    for (i, (name, _)) in first.rows().iter().enumerate() {
        print!("{name:<32}");
        for (_, m) in &columns {
            print!(" {:>9}", m.rows()[i].1);
        }
        println!();
    }
    // The columns only compare if they cover the same program.
    if module_sets.iter().any(|s| *s != module_sets[0]) {
        println!();
        println!("WARNING: the module sets differ between columns:");
        for ((label, _), set) in columns.iter().zip(&module_sets) {
            let extra: Vec<_> = set.iter().filter(|m| !module_sets[0].contains(m)).collect();
            let missing: Vec<_> = module_sets[0].iter().filter(|m| !set.contains(m)).collect();
            if !extra.is_empty() || !missing.is_empty() {
                println!("  {label}: +{extra:?} -{missing:?}");
            }
        }
    }
    Ok(())
}

//------------------------------------------------------------------------------
// laziness
//------------------------------------------------------------------------------

fn laziness(
    dir: &Path,
    module: Option<&str>,
    explain: bool,
    thunks_only: bool,
    json: bool,
) -> Result<()> {
    let modules = load_dir(dir)?;
    let selected: Vec<&Module> = match module {
        Some(name) => vec![find_module(&modules, name)?],
        None => modules.iter().collect(),
    };
    let census = Census::of_modules(selected.iter().copied());

    if json {
        serde_json::to_writer(std::io::stdout().lock(), &census)?;
        println!();
        return Ok(());
    }

    if explain {
        for b in &census.bindings {
            if thunks_only && b.fate == Fate::NotAThunk {
                continue;
            }
            println!(
                "{}  {}  (let node {}, rhs {})",
                b.module, b.occ, b.let_node, b.rhs
            );
            println!("  class:        {:?}", b.class);
            println!("  origin:       {:?}", b.origin);
            println!("  rhs:          {:?}", b.rhs_kind);
            println!("  demanded:     {:?}  [{}]", b.demand, b.demand_pretty);
            println!(
                "  multiplicity: {:?}  (ghc used-once: {}, syntactic once: {})",
                b.multiplicity,
                b.ghc_used_once.map(|x| x.to_string()).unwrap_or("?".into()),
                b.syntactic_once
                    .map(|x| x.to_string())
                    .unwrap_or("?".into()),
            );
            println!("  recursive:    {}", b.recursive);
            println!(
                "  whnf: {}   cheap: {}   ok-for-spec: {}   uses: {}",
                b.whnf, b.cheap, b.ok_for_spec, b.occurrences
            );
            if b.fate != Fate::NotAThunk {
                println!("  fate:         {:?}", b.fate);
                println!("  sink:         {:?}", b.sink);
            }
            println!("  reason:");
            for r in &b.reasons {
                println!("    {r}");
            }
            println!();
        }
    }

    report(&census, selected.len());
    Ok(())
}

//------------------------------------------------------------------------------
// parsec
//------------------------------------------------------------------------------

type ExprIdLike = (String, u32);

/// The recovered parser graph, as an auditable object: for each region its
/// parameters with their roles, then every edge — each terminator with the
/// values it hands back, and each parser call with the continuation filling
/// every slot, so a reader can follow every path from the entry to a
/// terminator. No lowering: the graph *is* the deliverable.
fn print_cfgs(
    analyses: &[h2r_analysis::parsec::Analysis<'_>],
    one: Option<u32>,
    json: bool,
) -> Result<()> {
    use h2r_analysis::parsec::{Cfg, EdgeKind, ParamRole, slots_str};

    let mut cfgs: Vec<Cfg> = Vec::new();
    for a in analyses {
        match one {
            Some(node) => {
                // Node ids are per module; a module whose arena is shorter
                // simply does not contain this node.
                if node as usize >= a.module.exprs.len() {
                    continue;
                }
                let ri = a
                    .regions
                    .iter()
                    .position(|r| r.entry == node)
                    .or_else(|| a.enclosing_region_of(node));
                if let Some(ri) = ri {
                    cfgs.push(a.cfg(ri));
                }
            }
            None => cfgs.extend((0..a.regions.len()).map(|ri| a.cfg(ri))),
        }
    }
    if json {
        serde_json::to_writer(std::io::stdout().lock(), &cfgs)?;
        println!();
        return Ok(());
    }
    if cfgs.is_empty() {
        println!("no region found");
        return Ok(());
    }
    for c in &cfgs {
        println!(
            "region {} of {} — entry node {} ({})",
            c.region,
            c.module,
            c.entry,
            if c.proven { "PROVEN" } else { "REJECTED" }
        );
        println!(
            "  unParser: state {}, value {}, result {} (erases to {} trailing argument(s))",
            c.sig.state.clone().unwrap_or_else(|| "-".into()),
            c.sig.value.clone().unwrap_or_else(|| "-".into()),
            c.sig.result,
            c.sig.trailing.len()
        );
        println!("  parameters");
        for p in &c.params {
            let role = match p.role {
                ParamRole::Leading => "argument".to_string(),
                ParamRole::State => "state".to_string(),
                ParamRole::UnboxedState(i) => format!("state field {i}"),
                ParamRole::Cont(s) => slots_str(s),
                ParamRole::Trailing(i) => format!("trailing {i}"),
            };
            println!(
                "    #{:<6} {:<12} {:<14} :: {}",
                p.binder, p.label, role, p.ty
            );
        }
        println!("  edges");
        for n in &c.nodes {
            match n.kind {
                EdgeKind::CallParser => {
                    let mut parts: Vec<String> = Vec::new();
                    parts.push(format!(
                        "parser={}",
                        n.parser.clone().unwrap_or_else(|| "?".into())
                    ));
                    if let Some(st) = &n.state {
                        parts.push(format!("state={}", st.text));
                    }
                    for s in &n.succ {
                        parts.push(format!(
                            "{}←{}",
                            slots_str(s.slots).to_lowercase(),
                            s.source.describe()
                        ));
                    }
                    println!(
                        "    CallParser({}) at node {}   [{}]",
                        parts.join(", "),
                        n.at,
                        n.rule
                    );
                }
                k => {
                    let args: Vec<String> = n
                        .args
                        .iter()
                        .map(|a| format!("{}={}", a.role, a.text))
                        .collect();
                    println!(
                        "    {k:?}({}) at node {}   [{}, {} role {}]",
                        args.join(", "),
                        n.at,
                        n.rule,
                        n.label,
                        slots_str(n.role)
                    );
                }
            }
        }
        let edges: usize = c.nodes.iter().map(|n| n.edges.len()).sum();
        println!(
            "  {} node(s), {} region edge(s) accounted for, {} unplaced",
            c.nodes.len(),
            edges,
            c.unplaced.len()
        );
        println!();
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn parsec(
    dir: &Path,
    module: Option<&str>,
    json: bool,
    explain: bool,
    cfg: Option<u32>,
    cfg_all: bool,
) -> Result<()> {
    use h2r_analysis::parsec::{Analysis, Bucket, EdgeFact, account};

    let modules = load_dir(dir)?;
    let selected: Vec<&Module> = match module {
        Some(name) => vec![find_module(&modules, name)?],
        None => modules.iter().collect(),
    };
    if cfg.is_some() || cfg_all {
        let analyses: Vec<Analysis> = selected.iter().map(|m| Analysis::of_module(m)).collect();
        return print_cfgs(&analyses, cfg, json);
    }
    // The raw census plus the analyses this command reports on: building
    // the integrated census would run the same recogniser a second time.
    let census = Census::raw(selected.iter().copied());
    let analyses: Vec<Analysis> = selected.iter().map(|m| Analysis::of_module(m)).collect();
    let acct = account(&census, &analyses);

    if json {
        let regions: Vec<_> = analyses.iter().flat_map(|a| a.regions.iter()).collect();
        let skipped: Vec<_> = analyses.iter().flat_map(|a| a.skipped.iter()).collect();
        let checks: Vec<_> = analyses.iter().map(|a| &a.checks).collect();
        let out = serde_json::json!({
            "regions": regions, "skipped": skipped, "checks": checks,
            "accounting": acct
        });
        serde_json::to_writer(std::io::stdout().lock(), &out)?;
        println!();
        return Ok(());
    }

    let regions: Vec<&h2r_analysis::parsec::ParserRegion> =
        analyses.iter().flat_map(|a| a.regions.iter()).collect();
    let proven = regions.iter().filter(|r| r.proven).count();
    println!("Parsec CPS recognition — {} module(s)", selected.len());
    println!();
    println!("Regions (lambda chains carrying ParsecT's representation)");
    println!(
        "  candidate regions                            {:>7}",
        regions.len()
    );
    println!("  proven                                       {proven:>7}");
    println!(
        "  rejected                                     {:>7}",
        regions.len() - proven
    );
    let with_state = regions.iter().filter(|r| r.state.is_some()).count();
    let full4 = regions
        .iter()
        .filter(|r| r.cok.is_some() && r.cerr.is_some() && r.eok.is_some() && r.eerr.is_some())
        .count();
    let trailing = regions.iter().filter(|r| !r.extra.is_empty()).count();
    let ambiguous = regions
        .iter()
        .filter(|r| r.conts.iter().any(|c| c.slots.len() > 1))
        .count();
    println!("  … with a state parameter in the chain        {with_state:>7}");
    println!("  … with all four continuation slots present   {full4:>7}");
    println!("  … with trailing transformer parameters       {trailing:>7}");
    println!("  … with an ambiguous slot embedding           {ambiguous:>7}");
    let derived: usize = regions.iter().map(|r| r.derived.len()).sum();
    println!("  derived (let-bound) continuations promoted   {derived:>7}");
    let skipped: usize = analyses.iter().map(|a| a.skipped.len()).sum();
    println!("  chains with continuation params but no region {skipped:>6}");
    let mut skip_by: BTreeMap<&'static str, (usize, ExprIdLike)> = BTreeMap::new();
    for a in &analyses {
        for sk in &a.skipped {
            let e = skip_by.entry(sk.reason).or_insert((0, (String::new(), 0)));
            e.0 += 1;
            if e.1.0.is_empty() {
                e.1 = (a.module.name.clone(), sk.entry);
            }
        }
    }
    for (reason, (n, (md, node))) in &skip_by {
        println!("    {n:>5}  {reason:<38} e.g. {md} node {node}");
    }

    println!();
    println!("Layout checks derived from the types (not assumed from the dump)");
    let c = analyses
        .iter()
        .fold(h2r_analysis::parsec::Checks::default(), |mut a, x| {
            let k = &x.checks;
            a.sig_checked += k.sig_checked;
            a.sig_refused += k.sig_refused;
            a.agree_refused += k.agree_refused;
            a.order_refused += k.order_refused;
            a.trailing_params_checked += k.trailing_params_checked;
            a.trailing_params += k.trailing_params;
            a.trailing_params_refused += k.trailing_params_refused;
            a.trailing_call_args += k.trailing_call_args;
            a.trailing_calls_refused += k.trailing_calls_refused;
            a.trailing_cont_calls += k.trailing_cont_calls;
            a.trailing_cont_calls_refused += k.trailing_cont_calls_refused;
            a.derived_connected += k.derived_connected;
            a.derived_unconnected += k.derived_unconnected;
            for (r, n) in &k.examples {
                a.examples.entry(r.clone()).or_insert(*n);
            }
            a
        });
    println!(
        "  R1-UNPARSER-SIG  chains checked against unParser's argument list {:>6}",
        c.sig_checked
    );
    println!(
        "    … refused: continuation types are not unParser's              {:>6}",
        c.sig_refused
    );
    println!(
        "    … refused: a / s / u / r do not agree (R1-TYPE-AGREE)         {:>6}",
        c.agree_refused
    );
    println!(
        "    … refused: continuation order is not cok·cerr·eok·eerr        {:>6}",
        c.order_refused
    );
    println!(
        "  R1-TRAILING-ERASURE  regions with trailing parameters checked   {:>6}  ({} parameter(s))",
        c.trailing_params_checked, c.trailing_params
    );
    println!(
        "    … refused: not a prefix of the result type's erasure          {:>6}",
        c.trailing_params_refused
    );
    println!(
        "    parser calls carrying trailing transformer arguments          {:>6}",
        c.trailing_call_args
    );
    println!(
        "    … calls refused that a fixed \"at most two\" would have taken   {:>6}",
        c.trailing_calls_refused
    );
    println!(
        "    continuation calls with trailing arguments (R3-…-TRAILING)    {:>6}",
        c.trailing_cont_calls
    );
    println!(
        "    … refused by the erasure                                     {:>6}",
        c.trailing_cont_calls_refused
    );
    println!(
        "  R8-DERIVED-CONT  let-bound continuations connected to a region  {:>6}",
        c.derived_connected
    );
    println!(
        "    … unconnected: excluded from the region's obligations         {:>6}",
        c.derived_unconnected
    );
    for (r, n) in &c.examples {
        println!("    e.g. {r} at node {n}");
    }

    println!();
    println!("Edges by kind");
    let mut by_kind: BTreeMap<String, usize> = BTreeMap::new();
    let mut by_rule: BTreeMap<&'static str, usize> = BTreeMap::new();
    for r in &regions {
        for e in &r.edges {
            let key = if e.exact() {
                format!("{:?}", e.kind)
            } else {
                format!(
                    "{{{}}}",
                    e.candidates
                        .iter()
                        .map(|k| format!("{k:?}"))
                        .collect::<Vec<_>>()
                        .join("|")
                )
            };
            *by_kind.entry(key).or_default() += 1;
            *by_rule.entry(e.provenance.rule).or_default() += 1;
        }
    }
    for (k, n) in &by_kind {
        println!("  {k:<44} {n:>7}");
    }
    println!();
    println!("Edges by recognition rule");
    for (k, n) in &by_rule {
        println!("  {k:<44} {n:>7}");
    }

    // Role identity and role forwarding are different facts.
    let invoke = regions
        .iter()
        .flat_map(|r| r.edges.iter())
        .filter(|e| e.fact == EdgeFact::Invoke)
        .count();
    let forward = regions
        .iter()
        .flat_map(|r| r.edges.iter())
        .filter(|e| e.fact == EdgeFact::Forward)
        .count();
    let reroute = regions
        .iter()
        .flat_map(|r| r.edges.iter())
        .filter(|e| e.reroutes())
        .count();
    println!();
    println!("Role identity vs role forwarding");
    println!("  invocations of a role (control goes to what it is)  {invoke:>7}");
    println!("  forwardings into a slot of a parser call            {forward:>7}");
    println!("    … of which into a slot other than its own role    {reroute:>7}");
    let mapped = regions.iter().filter(|r| r.wrapper.is_some()).count();
    println!("  ambiguous embeddings resolved by R9-WRAPPER-MAP    {mapped:>8}");

    println!();
    println!(
        "Accounting over the census' Parsec-shaped unresolved sites  {:>7}",
        acct.population
    );
    row("exact role proven", acct.exact, acct.population);
    row("finite role set proven", acct.finite, acct.population);
    row(
        "Parsec region recognised, target unresolved",
        acct.region_unresolved,
        acct.population,
    );
    row(
        "rejected as non-Parsec / escape",
        acct.rejected,
        acct.population,
    );
    println!(
        "  {:<44} {:>7}",
        "(invariant: the four buckets sum to the population)",
        acct.exact + acct.finite + acct.region_unresolved + acct.rejected
    );
    println!();
    println!(
        "Proven edges at sites OUTSIDE that population   {:>7}  (exact {}, finite {})",
        acct.outside_exact + acct.outside_finite,
        acct.outside_exact,
        acct.outside_finite
    );

    if !acct.reasons.is_empty() {
        println!();
        println!("Top reasons a population site is not an exact edge");
        let mut rs: Vec<(&String, &usize)> = acct.reasons.iter().collect();
        rs.sort_by(|a, b| b.1.cmp(a.1).then(a.0.cmp(b.0)));
        for (r, n) in rs.into_iter().take(10) {
            let node = acct
                .verdicts
                .iter()
                .find(|v| {
                    v.reason.is_some_and(|x| r.starts_with(x))
                        && (r.len() == v.reason.unwrap().len() || r.ends_with(&v.detail))
                })
                .map(|v| format!("{} node {}", v.module, v.root))
                .unwrap_or_default();
            println!("  {n:>6}  {r}");
            if !node.is_empty() {
                println!("          e.g. {node}");
            }
        }
    }

    let mut rejects: BTreeMap<&'static str, (usize, String)> = BTreeMap::new();
    for r in &regions {
        for j in &r.rejects {
            let e = rejects.entry(j.reason).or_insert((0, String::new()));
            e.0 += 1;
            if e.1.is_empty() {
                e.1 = format!("{} node {} ({})", r.module, j.at, j.detail);
            }
        }
    }
    if !rejects.is_empty() {
        println!();
        println!("Region reject reasons");
        let mut rs: Vec<_> = rejects.into_iter().collect();
        rs.sort_by_key(|a| std::cmp::Reverse(a.1.0));
        for (reason, (n, sample)) in rs {
            println!("  {n:>6}  {reason:<28} e.g. {sample}");
        }
    }

    println!();
    println!("Regions per module");
    println!(
        "  {:<34} {:>9} {:>7} {:>8} {:>7}",
        "module", "candidate", "proven", "rejected", "edges"
    );
    for a in &analyses {
        if a.regions.is_empty() {
            continue;
        }
        let p = a.regions.iter().filter(|r| r.proven).count();
        let e: usize = a.regions.iter().map(|r| r.edges.len()).sum();
        println!(
            "  {:<34} {:>9} {:>7} {:>8} {:>7}",
            a.module.name,
            a.regions.len(),
            p,
            a.regions.len() - p,
            e
        );
    }

    if explain {
        println!();
        for a in &analyses {
            for (i, r) in a.regions.iter().enumerate() {
                println!(
                    "-- {} region {i} at node {} ({}) state={:?} cok={:?} cerr={:?} eok={:?} eerr={:?}",
                    r.module,
                    r.entry,
                    if r.proven { "PROVEN" } else { "REJECTED" },
                    r.state,
                    r.cok,
                    r.cerr,
                    r.eok,
                    r.eerr
                );
                for c in &r.conts {
                    println!(
                        "   cont {} :: {}  slots {:?} arity {}",
                        c.label,
                        c.ty,
                        c.slots.iter().collect::<Vec<_>>(),
                        c.arity
                    );
                }
                for ev in &r.evidence {
                    println!("   [{}] node {}: {}", ev.rule, ev.node, ev.note);
                }
                for e in &r.edges {
                    println!(
                        "   edge {:?}{} at node {} by {} ({})",
                        e.kind,
                        if e.exact() { "" } else { " (finite set)" },
                        e.at,
                        e.provenance.rule,
                        e.provenance.label
                    );
                }
                for j in &r.rejects {
                    println!(
                        "   REJECT {} at node {}: {} [{}]",
                        j.reason, j.at, j.detail, j.label
                    );
                }
                println!();
            }
        }
        println!("Population sites that are not exact edges:");
        for v in &acct.verdicts {
            if v.bucket == Bucket::ExactRole {
                continue;
            }
            println!(
                "  {:?} {} app {} arg {} root {} head {} :: {} — {} {}",
                v.bucket,
                v.module,
                v.app,
                v.arg,
                v.root,
                v.head_label,
                v.head_ty,
                v.reason.unwrap_or(""),
                v.detail
            );
        }
    }
    Ok(())
}

fn count_by<T: Ord + Copy, I: IntoIterator<Item = T>>(items: I) -> BTreeMap<T, usize> {
    let mut map = BTreeMap::new();
    for t in items {
        *map.entry(t).or_insert(0) += 1;
    }
    map
}

fn row(label: &str, n: usize, total: usize) {
    let pct = if total == 0 {
        0.0
    } else {
        100.0 * n as f64 / total as f64
    };
    println!("  {label:<44} {n:>7}  {pct:>5.1}%");
}

fn report(c: &Census, n_modules: usize) {
    let total = c.bindings.len();
    println!("Residual binding census — {n_modules} module(s)");
    println!();
    println!("Local bindings (let / letrec)                  {total:>7}");
    let classes = count_by(c.bindings.iter().map(|b| b.class));
    for (class, label) in [
        (Class::Function, "function (closure)"),
        (Class::JoinPoint, "join point (control flow)"),
        (Class::Dead, "dead"),
        (Class::Alias, "alias (trivial RHS)"),
        (Class::Value, "value (already WHNF)"),
        (Class::StrictValue, "strict value   (MUST, once)"),
        (Class::StrictShared, "strict shared  (MUST, many)"),
        (Class::LazyOnce, "lazy once      (MAY, once)"),
        (Class::LazyShared, "lazy shared    (MAY, many)"),
        (Class::RecursiveValue, "recursive value"),
        (Class::Unknown, "unknown"),
    ] {
        row(label, classes.get(&class).copied().unwrap_or(0), total);
    }

    let thunks: Vec<_> = c
        .bindings
        .iter()
        .filter(|b| b.fate != Fate::NotAThunk)
        .collect();
    let fates = count_by(thunks.iter().map(|b| b.fate));
    println!();
    println!(
        "Potential thunk sites                          {:>7}",
        thunks.len()
    );
    for (fate, label) in [
        (Fate::SinkEager, "sinkable, lands in an evaluating position"),
        (Fate::SinkLazyPosition, "sinkable, lands in a lazy position"),
        (Fate::Memo, "memoisation required"),
        (Fate::Recursive, "recursive value"),
        (Fate::Unknown, "unknown"),
    ] {
        row(label, fates.get(&fate).copied().unwrap_or(0), thunks.len());
    }
    let memo: Vec<_> = thunks.iter().filter(|b| b.fate == Fate::Memo).collect();
    let memo_lambda = memo
        .iter()
        .filter(|b| matches!(b.sink, h2r_analysis::laziness::Sink::UnderLambda { .. }))
        .count();
    let memo_spec = memo.iter().filter(|b| b.ok_for_spec).count();
    let memo_cheap = memo.iter().filter(|b| b.cheap && !b.ok_for_spec).count();
    println!();
    println!("Memoisation is never needed for correctness here (only recursive values are):");
    println!("it preserves *sharing*. Sinking into every use is always semantically valid.");
    println!(
        "  memoisation required to keep sharing            {:>7}",
        memo.len()
    );
    row("captured by a many-entry lambda", memo_lambda, memo.len());
    row("shared on a path", memo.len() - memo_lambda, memo.len());
    row(
        "ok-for-speculation (could just be eager)",
        memo_spec,
        memo.len(),
    );
    row("cheap but not speculatable", memo_cheap, memo.len());

    println!();
    println!("Potential thunk sites by binder origin");
    let origins = count_by(thunks.iter().map(|b| b.origin));
    let memo_origins = count_by(memo.iter().map(|b| b.origin));
    println!("  {:<44} {:>7} {:>7}", "", "sites", "memo");
    for (o, label) in [
        (
            Origin::Dictionary,
            "$d…  dictionary (gone after specialisation)",
        ),
        (
            Origin::FloatOut,
            "lvl… full-laziness float-out (re-sinkable)",
        ),
        (Origin::Desugar, "ds…  desugared lazy pattern binding"),
        (Origin::Eta, "eta… eta-expansion / monad plumbing"),
        (Origin::WorkerOrSpec, "$w/$s worker or specialisation"),
        (Origin::Join, "$j   join point"),
        (Origin::User, "user-named"),
    ] {
        println!(
            "  {label:<44} {:>7} {:>7}",
            origins.get(&o).copied().unwrap_or(0),
            memo_origins.get(&o).copied().unwrap_or(0)
        );
    }

    println!();
    println!("Potential thunk sites by module");
    let mut per: BTreeMap<&str, (usize, usize, usize)> = BTreeMap::new();
    for b in &thunks {
        let e = per.entry(b.module.as_str()).or_default();
        e.0 += 1;
        if b.fate == Fate::Memo {
            e.1 += 1;
            if b.ok_for_spec {
                e.2 += 1;
            }
        }
    }
    let mut per: Vec<_> = per.into_iter().collect();
    per.sort_by_key(|(_, (sites, _, _))| std::cmp::Reverse(*sites));
    println!(
        "  {:<34} {:>6} {:>6} {:>8}",
        "module", "sites", "memo", "of which spec-ok"
    );
    for (name, (sites, memo, spec)) in per {
        println!("  {name:<34} {sites:>6} {memo:>6} {spec:>8}");
    }

    println!();
    println!("Multiplicity cross-check on thunk candidates (GHC cardinality vs syntactic)");
    let a = &c.agreement;
    let n = a.both_once + a.ghc_once_syntax_many + a.ghc_many_syntax_once + a.both_many;
    row("both once", a.both_once, n);
    row("GHC once, syntax many", a.ghc_once_syntax_many, n);
    row("GHC many, syntax once", a.ghc_many_syntax_once, n);
    row("both many", a.both_many, n);

    let top = c.top.len();
    let tops = count_by(c.top.iter().map(|t| t.class));
    println!();
    println!("Top-level bindings                             {top:>7}");
    for (class, label) in [
        (TopClass::Function, "function"),
        (TopClass::Value, "value (already WHNF)"),
        (TopClass::Alias, "alias"),
        (TopClass::StringLiteral, "string literal (static data)"),
        (TopClass::Bottom, "bottom (error / pattern failure)"),
        (TopClass::Caf, "CAF (genuine top-level thunk)"),
    ] {
        row(label, tops.get(&class).copied().unwrap_or(0), top);
    }
    let caf_spec = c
        .top
        .iter()
        .filter(|t| t.class == TopClass::Caf && t.ok_for_spec)
        .count();
    println!("    of CAFs: {caf_spec} are ok-for-speculation (could be initialised eagerly)");

    let nargs = c.args.len();
    println!();
    println!("Non-trivial arguments (allocations the let census cannot see) {nargs:>7}");
    let values = c
        .args
        .iter()
        .filter(|a| a.shape != ArgShape::Computation)
        .count();
    row("already a value (closure / con / PAP)", values, nargs);
    let comps: Vec<_> = c
        .args
        .iter()
        .filter(|a| a.shape == ArgShape::Computation)
        .collect();
    let dict = comps.iter().filter(|a| a.dictionary).count();
    row("dictionary construction", dict, nargs);
    let positions = count_by(comps.iter().filter(|a| !a.dictionary).map(|a| a.position));
    for (pos, label) in [
        (
            Position::StrictArg,
            "computation, strict param/field (eager)",
        ),
        (Position::AbsentArg, "computation, absent param"),
        (Position::LazyField, "computation, lazy constructor field"),
        (Position::LazyParam, "computation, lazy function param"),
        (
            Position::UnsaturatedArg,
            "computation, unsaturated call (PAP holds it)",
        ),
        (
            Position::PastSigArg,
            "computation, past the callee's signature",
        ),
        (Position::UnknownArg, "computation, callee has no signature"),
    ] {
        row(label, positions.get(&pos).copied().unwrap_or(0), nargs);
    }
    let other: usize = positions
        .iter()
        .filter(|(p, _)| {
            !matches!(
                p,
                Position::StrictArg
                    | Position::AbsentArg
                    | Position::LazyField
                    | Position::LazyParam
                    | Position::UnsaturatedArg
                    | Position::PastSigArg
                    | Position::UnknownArg
            )
        })
        .map(|(_, n)| n)
        .sum();
    if other > 0 {
        row("computation, other position", other, nargs);
    }

    // The M2 question: who receives the lazy ones, and can we see them?
    let lazy: Vec<_> = comps.iter().filter(|a| a.position.escapes()).collect();
    let n = lazy.len();
    println!();
    println!("Computations in lazy / unknown positions       {n:>7}");
    println!();
    println!("  by callee resolution");
    let res = count_by(lazy.iter().map(|a| a.callee.resolution));
    for (r, label) in [
        (Resolution::DataCon, "known data constructor"),
        (
            Resolution::ExactGlobal,
            "known global function, signature covers arg",
        ),
        (
            Resolution::ExactLocal,
            "known local function, signature covers arg",
        ),
        (
            Resolution::ClassOp,
            "class-op dispatch (needs specialisation)",
        ),
        (
            Resolution::HigherOrderParam,
            "unknown: higher-order parameter",
        ),
        (
            Resolution::ImportedOpaque,
            "unknown: imported, no signature",
        ),
        (Resolution::PastArity, "global applied past its signature"),
        (
            Resolution::KnownLambdaNoDemand,
            "local lambda param, no demand info",
        ),
        (
            Resolution::KnownLambdaPastArity,
            "local lambda applied past its params",
        ),
        (
            Resolution::ClosureFromKnownCall,
            "closure from a known call (target not followed)",
        ),
        (
            Resolution::ComputedClosure,
            "closure from a case/let computation",
        ),
        (Resolution::NonVarHead, "unknown: non-variable head"),
    ] {
        row(label, res.get(&r).copied().unwrap_or(0), n);
    }
    println!();
    println!("  by target tier (what is actually proven about the code that runs)");
    let tiers = count_by(lazy.iter().map(|a| a.callee.tier()));
    for (t, label) in [
        (Tier::Exact, "exact target proven"),
        (Tier::FiniteSet, "finite target set proven"),
        (
            Tier::ProducerKnown,
            "producer known, returned target unresolved",
        ),
        (Tier::Unresolved, "target unresolved"),
    ] {
        row(label, tiers.get(&t).copied().unwrap_or(0), n);
    }
    // Where the proof came from. The two sources are independent and the
    // tier is the better of them; this says how much the second one adds.
    let from_parsec = lazy
        .iter()
        .filter(|a| {
            a.callee.resolution.tier() == Tier::Unresolved && a.callee.tier() != Tier::Unresolved
        })
        .count();
    println!();
    println!(
        "  note: the Parsec CPS recogniser moved {from_parsec} sites OUT of the unresolved\n        \
         tier ({:.1}% of all lazy/unknown argument sites) — the head alone proves\n        \
         nothing about them. They are *not* part of the {} still unresolved.",
        100.0 * from_parsec as f64 / n as f64,
        tiers.get(&Tier::Unresolved).copied().unwrap_or(0)
    );
    println!();
    println!("  by callee family");
    let fam = count_by(lazy.iter().map(|a| a.callee.family));
    for (f, label) in [
        (Family::Parsec, "Parsec (calls into Text.Parsec)"),
        (
            Family::ParsecContinuation,
            "Parsec continuation (cok/cerr/eok/eerr)",
        ),
        (Family::EtaParam, "eta-expanded monadic function (eta…)"),
        (Family::Transformers, "monad transformers / mtl (calls)"),
        (Family::Tuple, "boxed tuple constructor"),
        (Family::UnboxedTuple, "unboxed tuple constructor"),
        (Family::MonadOps, "monad ops from base (>>=, fmap, ...)"),
        (Family::ClassOp, "class-op dispatch"),
        (Family::Dictionary, "dfun / dictionary binding"),
        (Family::ProgramDataCon, "program data constructor"),
        (Family::ProgramFunction, "program function"),
        (Family::LocalFunction, "local let-bound function"),
        (Family::ListCons, "list cons"),
        (Family::LibraryDataCon, "other library data constructor"),
        (Family::BaseList, "base list / Foldable ops"),
        (Family::Containers, "containers"),
        (Family::BaseOther, "other base"),
        (Family::OtherLibrary, "other library"),
        (Family::Unknown, "unknown value"),
    ] {
        row(label, fam.get(&f).copied().unwrap_or(0), n);
    }
    println!();
    println!("  attributable to a normalisation family (first-order estimate)");
    let attr = |fs: &[Family]| {
        lazy.iter()
            .filter(|a| fs.contains(&a.callee.family))
            .count()
    };
    row(
        "Parsec / CPS normalisation",
        attr(&[Family::Parsec, Family::ParsecContinuation, Family::EtaParam]),
        n,
    );
    row(
        "dictionary specialisation",
        attr(&[Family::ClassOp, Family::Dictionary, Family::MonadOps]),
        n,
    );
    row(
        "transformer collapse (tuple results)",
        attr(&[Family::Transformers, Family::Tuple, Family::UnboxedTuple]),
        n,
    );
    row(
        "constructor-field strategy",
        attr(&[
            Family::ProgramDataCon,
            Family::ListCons,
            Family::LibraryDataCon,
        ]),
        n,
    );
    row(
        "ordinary calls with a visible signature",
        attr(&[
            Family::ProgramFunction,
            Family::LocalFunction,
            Family::BaseList,
            Family::Containers,
            Family::BaseOther,
            Family::OtherLibrary,
        ]),
        n,
    );
    row("unknown", attr(&[Family::Unknown]), n);
    println!();
    println!("  top callees");
    let mut heads: BTreeMap<String, usize> = BTreeMap::new();
    for a in &lazy {
        let key = match &a.callee.module {
            Some(md) => format!("{md}.{}", a.callee.occ),
            None => format!("<local> {}", a.callee.occ),
        };
        *heads.entry(key).or_default() += 1;
    }
    let mut heads: Vec<_> = heads.into_iter().collect();
    heads.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
    for (name, count) in heads.into_iter().take(25) {
        println!("    {count:>6}  {name}");
    }
}

//------------------------------------------------------------------------------
// tuples
//------------------------------------------------------------------------------

/// The normalised scalar view: what the program looks like with one proven
/// tuple gone. An IR-level view — nothing is lowered and no Core is
/// rewritten — and a complete one: every consumer of the flow and every
/// call site it proved is placed in exactly one line, and the block ends
/// the way the recovered Parsec graph does, with `0 unplaced`.
fn print_view(v: &h2r_analysis::scalar::ScalarView) {
    use h2r_analysis::scalar::LineKind;

    v.check();
    println!(
        "{} node {} — {} {} of arity {}, fate {:?} [verified: {}]",
        v.module,
        v.construction,
        if v.boxed { "boxed" } else { "unboxed" },
        v.con,
        v.arity,
        v.fate,
        if v.verified { "yes" } else { "no" }
    );
    println!("  scalars");
    for sc in &v.scalars {
        println!("    {:<6} := {:<40} [node {}]", sc.name, sc.text, sc.node);
    }
    println!("  normalised");
    for l in &v.lines {
        let tag = match l.kind {
            LineKind::Scalar => "scalar",
            LineKind::Hop => "hop",
            LineKind::CallSite => "call",
            LineKind::Binding => "bind",
            LineKind::Note => "note",
        };
        println!("    {tag:<5} {}", l.text);
        println!("    {:<5}   [{}]", "", l.rules.join(", "));
    }
    println!(
        "  {} consumer(s), {} call site(s) accounted for, {} unplaced",
        v.consumers,
        v.call_sites,
        v.unplaced.len()
    );
}

fn scalar_views(
    tc: &h2r_analysis::tuples::TupleCensus<'_>,
    node: Option<u32>,
    all: bool,
    json: bool,
) -> Result<()> {
    use h2r_analysis::scalar::view;
    use h2r_analysis::tuples::TupleFate;

    let mut out = Vec::new();
    let mut found = false;
    for t in &tc.per_module {
        for f in &t.flows {
            if let Some(n) = node
                && f.construction != n
            {
                continue;
            }
            found = true;
            // A flow the boundary check moved to RemovableWithClone keeps
            // its own proof — what it lost is the right to be counted as
            // normalised — so its view is still printed, with that fate in
            // the header.
            let removable = matches!(
                f.fate,
                TupleFate::ScalarReplace | TupleFate::WorkerReturn | TupleFate::RemovableWithClone
            );
            if !removable {
                if node.is_some() {
                    println!(
                        "{} node {} is {:?}{} — there is no scalar view of a tuple that stays",
                        f.module,
                        f.construction,
                        f.fate,
                        match f.reason_key() {
                            Some(r) => format!(" ({r})"),
                            None => String::new(),
                        }
                    );
                }
                continue;
            }
            if all && node.is_none() || node.is_some() {
                out.push(view(t, f, tc.is_verified(f)));
            }
        }
    }
    if let Some(n) = node {
        if !found {
            println!("no saturated tuple construction at node {n} in the selected module(s)");
        }
        if out.is_empty() {
            return Ok(());
        }
    }
    if json {
        serde_json::to_writer(std::io::stdout().lock(), &out)?;
        println!();
        return Ok(());
    }
    for (i, v) in out.iter().enumerate() {
        if i > 0 {
            println!();
        }
        print_view(v);
    }
    if all {
        println!();
        println!(
            "{} removable construction(s), every consumer and call site placed",
            out.len()
        );
    }
    Ok(())
}

/// The representation boundaries the removable flows cross, and whether
/// each can be split uniformly. A flow's own def-use proof says the tuple
/// is transport; this says whether every *other* value that arrives at the
/// same parameter or return agrees on one representation, which is what
/// applying all the scalar views at once needs.
fn print_boundaries(
    tc: &h2r_analysis::tuples::TupleCensus<'_>,
    explain: bool,
    json: bool,
) -> Result<()> {
    use h2r_analysis::boundary::{BoundaryVerdict, Representation, verdict_rows};
    use h2r_analysis::tuples::TupleFate;

    if json {
        let out = serde_json::json!({
            "boundaries": tc.boundaries,
            "downgrades": tc.downgrades,
            "rows": verdict_rows(&tc.boundaries),
        });
        serde_json::to_writer(std::io::stdout().lock(), &out)?;
        println!();
        return Ok(());
    }

    let reports: Vec<&h2r_analysis::boundary::BoundaryReport> = tc
        .boundaries
        .iter()
        .flat_map(|b| b.reports.iter())
        .collect();
    println!(
        "Representation boundaries — {} module(s)",
        tc.per_module.len()
    );
    println!();
    println!("Every parameter and return a removable flow's scalar view crosses, with every");
    println!(
        "value that reaches it enumerated from the IR's occurrences — not from the flow walk."
    );
    println!();
    println!(
        "  {:<16} {:<11} {:>8} {:>8} {:>6} {:>8}",
        "verdict", "kind", "boxed", "unboxed", "both", "total"
    );
    for r in verdict_rows(&tc.boundaries) {
        println!(
            "  {:<16} {:<11} {:>8} {:>8} {:>6} {:>8}",
            r.verdict, r.kind, r.boxed, r.unboxed, r.both, r.total
        );
    }
    println!(
        "  {:<16} {:<11} {:>8} {:>8} {:>6} {:>8}",
        "total",
        "",
        "",
        "",
        "",
        reports.len()
    );

    // How many flows cross a boundary at all. The boundary object keeps the
    // crossings of the downgraded flows too, so this is the whole
    // population def-use proved removable before the boundary check.
    let crossing: usize = tc.boundaries.iter().map(|b| b.crossed.len()).sum();
    let before = tc
        .flows
        .iter()
        .filter(|f| matches!(f.fate, TupleFate::ScalarReplace | TupleFate::WorkerReturn))
        .count()
        + tc.downgrades.len();
    println!();
    println!(
        "  of the {before} flow(s) def-use proved removable, {crossing} cross at least one \
         boundary and {} cross none",
        before.saturating_sub(crossing)
    );
    println!(
        "  {} of them were downgraded here: {} to RemovableWithClone, {} to Unresolved",
        tc.downgrades.len(),
        tc.downgrades
            .iter()
            .filter(|d| d.to == TupleFate::RemovableWithClone)
            .count(),
        tc.downgrades
            .iter()
            .filter(|d| d.to == TupleFate::Unresolved)
            .count()
    );
    println!(
        "  the downgrade fixpoint settled in {} round(s)",
        tc.boundary_rounds
    );

    // Why a boundary is not a uniform split.
    println!();
    println!("Why a boundary is not a uniform split");
    let mut by: BTreeMap<(&str, &str), (usize, String, String)> = BTreeMap::new();
    for r in reports.iter().filter(|r| !r.verdict.ok()) {
        let e = by
            .entry((r.verdict.name(), r.reason.unwrap_or("no-reason")))
            .or_insert((0, String::new(), String::new()));
        e.0 += 1;
        if e.1.is_empty() {
            e.1 = r.module.clone();
            e.2 = r.name.clone();
        }
    }
    let mut rows: Vec<_> = by.into_iter().collect();
    rows.sort_by_key(|a| std::cmp::Reverse(a.1.0));
    for ((verdict, reason), (n, module, name)) in &rows {
        println!("  {n:>6}  {verdict:<14} {reason}");
        println!("          e.g. {module} {name}");
    }

    // What the producers of a non-uniform boundary actually are.
    println!();
    println!("What reaches a boundary that is not a uniform split");
    let mut kinds: BTreeMap<&str, (usize, String, u32)> = BTreeMap::new();
    for r in reports.iter().filter(|r| !r.verdict.ok()) {
        for p in &r.producers {
            if p.representation != Representation::Tuple {
                continue;
            }
            let e = kinds.entry(p.kind.name()).or_insert((0, String::new(), 0));
            e.0 += 1;
            if e.1.is_empty() {
                e.1 = r.module.clone();
                e.2 = p.at;
            }
        }
    }
    let mut krows: Vec<_> = kinds.into_iter().collect();
    krows.sort_by_key(|a| std::cmp::Reverse(a.1.0));
    for (kind, (n, module, at)) in &krows {
        println!("  {n:>6}  {kind:<42} e.g. {module} node {at}");
    }

    // The flows that lost their fate.
    println!();
    println!("Flows downgraded, by reason");
    let mut dr: BTreeMap<(&str, &str), (usize, String, u32, String)> = BTreeMap::new();
    for d in &tc.downgrades {
        let to = match d.to {
            TupleFate::RemovableWithClone => "RemovableWithClone",
            _ => "Unresolved",
        };
        let e = dr
            .entry((to, d.reason))
            .or_insert((0, String::new(), 0, String::new()));
        e.0 += 1;
        if e.1.is_empty() {
            e.1 = d.module.clone();
            e.2 = d.construction;
            e.3 = d.boundary.clone();
        }
    }
    let mut drows: Vec<_> = dr.into_iter().collect();
    drows.sort_by_key(|a| std::cmp::Reverse(a.1.0));
    for ((to, reason), (n, module, at, boundary)) in &drows {
        println!("  {n:>6}  {to:<20} {reason}");
        println!("          e.g. {module} node {at} — {boundary}");
    }
    let db = tc.downgrades.iter().filter(|d| d.boxed).count();
    println!("  {} boxed, {} unboxed", db, tc.downgrades.len() - db);

    // Per module.
    println!();
    println!("Per module");
    println!(
        "  {:<34} {:>9} {:>9} {:>7} {:>7} {:>7}",
        "module", "boundaries", "uniform", "clone", "presrv", "unres"
    );
    for b in &tc.boundaries {
        if b.reports.is_empty() {
            continue;
        }
        let n =
            |v: fn(&BoundaryVerdict) -> bool| b.reports.iter().filter(|r| v(&r.verdict)).count();
        println!(
            "  {:<34} {:>9} {:>9} {:>7} {:>7} {:>7}",
            b.module,
            b.reports.len(),
            n(|v| matches!(v, BoundaryVerdict::UniformSplit { .. })),
            n(|v| *v == BoundaryVerdict::CloneRequired),
            n(|v| *v == BoundaryVerdict::Preserve),
            n(|v| *v == BoundaryVerdict::Unresolved),
        );
    }

    if explain {
        for b in &tc.boundaries {
            for r in &b.reports {
                println!();
                println!(
                    "{} {} — {:?}{}",
                    r.module,
                    r.name,
                    r.verdict,
                    match r.reason {
                        Some(x) => format!(" ({x})"),
                        None => String::new(),
                    }
                );
                println!(
                    "  crossed by {}{}{} tuple(s)",
                    if r.boxed { "boxed" } else { "" },
                    if r.boxed && r.unboxed { " and " } else { "" },
                    if r.unboxed { "unboxed" } else { "" }
                );
                println!("  producers");
                for p in &r.producers {
                    let rep = match p.representation {
                        Representation::Scalars(k) => format!("Scalars({k})"),
                        Representation::Tuple => "Tuple".to_string(),
                    };
                    println!(
                        "    node {:<8} {:<12} {:<42}{}",
                        p.at,
                        rep,
                        p.kind.name(),
                        match p.call {
                            Some(c) => format!(" at call {c}"),
                            None => String::new(),
                        }
                    );
                }
                if !r.other_uses.is_empty() {
                    println!("  other uses of the function");
                    for u in &r.other_uses {
                        println!("    node {:<8} {}", u.at, u.why);
                    }
                }
                println!(
                    "  consumers: {}",
                    r.consumers
                        .iter()
                        .map(|c| c.to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                );
            }
        }
    }
    Ok(())
}

/// Re-derive every removable verdict with the independent verifier
/// (`h2r_analysis::verify`) and report the disagreements.
fn verify_tuples(tc: &h2r_analysis::tuples::TupleCensus<'_>) -> Result<()> {
    // The cross-check is part of the census now — the milestone's
    // accounting counts only verified removals as normalised — so this
    // reports it rather than running it again.
    let out = &tc.cross;
    println!("Independent verification of every removable verdict");
    println!();
    println!("  {:<44} {:>8}", "removable verdicts checked", out.checked);
    println!("  {:<44} {:>8}", "  re-derived by the verifier", out.agreed);
    println!(
        "  {:<44} {:>8}",
        "  …of which using a Parsec hop", out.via_hops
    );
    println!("  {:<44} {:>8}", "  DISAGREEMENTS", out.disagreements.len());
    println!(
        "  {:<44} {:>8}",
        "verifier accepts, census does not", out.census_stricter
    );
    println!(
        "  {:<44} {:>8}",
        "  …of which the boundary check downgraded",
        tc.downgrades.len()
    );
    println!(
        "  {:<44} {:>8}",
        "population: only the verifier found it",
        out.only_here.len()
    );
    println!(
        "  {:<44} {:>8}",
        "population: only the census found it",
        out.only_there.len()
    );
    println!(
        "  {:<44} {:>8}",
        "rounds the tuple-in-tuple fixpoint took",
        tc.per_module
            .iter()
            .map(|t| t.nesting_rounds)
            .max()
            .unwrap_or(0)
    );
    println!();
    println!("The audited shapes, in this dump");
    println!("  {:<44} {:>6}  fates / example", "shape", "n");
    for p in h2r_analysis::tuples::patterns(&tc.per_module) {
        let fates: Vec<String> = p.fates.iter().map(|(f, n)| format!("{f} {n}")).collect();
        println!("  {:<44} {:>6}  {}", p.name, p.n, fates.join(", "));
        if p.n > 0 {
            println!("  {:<44}         e.g. {} node {}", "", p.module, p.at);
        }
    }
    if !out.disagreements.is_empty() {
        println!();
        let mut by: BTreeMap<(&str, String), (usize, String, u32)> = BTreeMap::new();
        for d in &out.disagreements {
            let e = by
                .entry((d.rejection.why, d.rejection.detail.clone()))
                .or_insert((0, String::new(), 0));
            e.0 += 1;
            if e.1.is_empty() {
                e.1 = d.module.clone();
                e.2 = d.construction;
            }
        }
        println!("Disagreements by reason");
        let mut rows: Vec<_> = by.into_iter().collect();
        rows.sort_by_key(|(_, v)| std::cmp::Reverse(v.0));
        for ((why, detail), (n, module, at)) in rows {
            println!("  {n:>6}  {why} ({detail})");
            println!("          e.g. {module} node {at}");
        }
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn tuples(
    dir: &Path,
    module: Option<&str>,
    json: bool,
    explain: bool,
    verify: bool,
    scalar: Option<u32>,
    scalar_all: bool,
    boundaries: bool,
) -> Result<()> {
    use h2r_analysis::tuples::{TupleCensus, TupleFate};

    let modules = load_dir(dir)?;
    let selected: Vec<&Module> = match module {
        Some(name) => vec![find_module(&modules, name)?],
        None => modules.iter().collect(),
    };
    // The census is only read for its tuple-attributed argument sites, so
    // the raw one (without the Parsec proof, which says nothing about
    // tuples) is enough and costs one pass instead of two.
    let census = Census::raw(selected.iter().copied());
    // The Parsec proof object resolves the continuation calls the tuple
    // rules see as an unknown higher-order callee; it is read, never
    // re-derived (`tuples::parsec_hops`).
    let analyses: Vec<h2r_analysis::parsec::Analysis> = selected
        .iter()
        .map(|m| h2r_analysis::parsec::Analysis::of_module(m))
        .collect();
    let hops: Vec<h2r_analysis::tuples::ParsecHops> = analyses
        .iter()
        .map(h2r_analysis::tuples::parsec_hops)
        .collect();
    let tc = TupleCensus::of_modules_with(&selected, &census, &hops);

    if verify {
        return verify_tuples(&tc);
    }
    if boundaries {
        return print_boundaries(&tc, explain, json);
    }
    if scalar.is_some() || scalar_all {
        return scalar_views(&tc, scalar, scalar_all, json);
    }

    if json {
        let out = serde_json::json!({
            "flows": tc.flows,
            "skipped": tc.per_module.iter().flat_map(|t| t.skipped.iter()).collect::<Vec<_>>(),
            "accounting": tc.accounting,
            "boundaries": tc.boundaries,
            "downgrades": tc.downgrades,
        });
        serde_json::to_writer(std::io::stdout().lock(), &out)?;
        println!();
        return Ok(());
    }

    let flows = &tc.flows;
    let acct = &tc.accounting;
    println!("Tuple constructions — {} module(s)", selected.len());
    println!();

    // Constructions by arity.
    println!("Saturated constructions by arity");
    let mut by_arity: BTreeMap<u32, (usize, usize)> = BTreeMap::new();
    for f in flows {
        let e = by_arity.entry(f.arity).or_default();
        if f.boxed {
            e.0 += 1;
        } else {
            e.1 += 1;
        }
    }
    println!("  {:<10} {:>10} {:>10}", "arity", "boxed", "unboxed");
    for (arity, (b, u)) in &by_arity {
        println!("  {arity:<10} {b:>10} {u:>10}");
    }
    println!(
        "  {:<10} {:>10} {:>10}",
        "total", acct.constructions_boxed, acct.constructions_unboxed
    );
    let skipped: usize = tc.per_module.iter().map(|t| t.skipped.len()).sum();
    if skipped > 0 {
        let mut by: BTreeMap<&str, (usize, String, u32)> = BTreeMap::new();
        for t in &tc.per_module {
            for s in &t.skipped {
                let e = by.entry(s.reason).or_insert((0, String::new(), 0));
                e.0 += 1;
                if e.1.is_empty() {
                    e.1 = t.module.name.clone();
                    e.2 = s.at;
                }
            }
        }
        println!("  tuple constructors that are not a saturated construction");
        for (reason, (n, md, node)) in &by {
            println!("    {n:>6}  {reason:<28} e.g. {md} node {node}");
        }
    }

    // Fates.
    println!();
    println!("Fates, proved by def-use");
    println!("  {:<20} {:>10} {:>10}", "fate", "boxed", "unboxed");
    let fates = [
        TupleFate::ScalarReplace,
        TupleFate::WorkerReturn,
        TupleFate::RemovableWithClone,
        TupleFate::Preserve,
        TupleFate::Unresolved,
    ];
    for fate in fates {
        let b = acct.count(true, fate);
        let u = acct.count(false, fate);
        println!("  {:<20} {b:>10} {u:>10}", format!("{fate:?}"));
    }
    println!(
        "  {:<20} {:>10} {:>10}",
        "total", acct.constructions_boxed, acct.constructions_unboxed
    );
    // How the fields of a removable tuple are read is a fact about the
    // flow, not a fate: both are removed the same way, so it is reported
    // beside the fates rather than as one of them.
    let removable = |f: &&h2r_analysis::tuples::TupleFlow| {
        matches!(
            f.fate,
            TupleFate::ScalarReplace | TupleFate::WorkerReturn | TupleFate::RemovableWithClone
        )
    };
    println!(
        "  of the removable ones, {} boxed and {} unboxed have at least one field read on its own",
        flows
            .iter()
            .filter(|f| removable(f) && f.boxed && f.selected)
            .count(),
        flows
            .iter()
            .filter(|f| removable(f) && !f.boxed && f.selected)
            .count()
    );

    // The milestone's accounting: before = normalised + preserved +
    // unsupported, per representation. `Accounting::check` asserts every
    // cell of this; printing it is the audit trail, not the check.
    println!();
    println!("M2.2 accounting — before = normalised + preserved + unsupported");
    println!(
        "  {:<16} {:>8} {:>11} {:>10} {:>12}",
        "", "before", "normalised", "preserved", "unsupported"
    );
    for (label, boxed) in [("boxed", true), ("unboxed", false)] {
        let b = acct.bucket(boxed);
        println!(
            "  {label:<16} {:>8} {:>11} {:>10} {:>12}",
            b.before, b.normalised, b.preserved, b.unsupported
        );
    }
    let all = |f: fn(&h2r_analysis::tuples::Bucket) -> usize| -> usize {
        acct.milestone.iter().map(f).sum()
    };
    println!(
        "  {:<16} {:>8} {:>11} {:>10} {:>12}",
        "total",
        all(|b| b.before),
        all(|b| b.normalised),
        all(|b| b.preserved),
        all(|b| b.unsupported)
    );
    println!(
        "  normalised = removable and re-derived by the independent verifier; \
         {} removable verdict(s) unverified",
        acct.removable_unverified
    );
    println!();
    println!(
        "  the census' {} tuple-attributed argument sites, the same way",
        acct.sites_mapped
    );
    for (label, boxed) in [("boxed", true), ("unboxed", false)] {
        let b = acct.site_bucket(boxed);
        println!(
            "  {label:<16} {:>8} {:>11} {:>10} {:>12}",
            b.before, b.normalised, b.preserved, b.unsupported
        );
    }
    let sall = |f: fn(&h2r_analysis::tuples::Bucket) -> usize| -> usize {
        acct.site_milestone.iter().map(f).sum()
    };
    println!(
        "  {:<16} {:>8} {:>11} {:>10} {:>12}",
        "total",
        sall(|b| b.before),
        sall(|b| b.normalised),
        sall(|b| b.preserved),
        sall(|b| b.unsupported)
    );
    println!();
    println!("  the unsupported residual, itemised by what holds the value");
    for (reason, n) in &acct.residual {
        println!("    {n:>6}  {reason}");
    }

    // The census' tuple-attributed argument sites, on their own.
    println!();
    println!(
        "The census' {} tuple-attributed lazy argument sites",
        acct.sites.len()
    );
    println!("  {:<20} {:>10} {:>10}", "fate", "boxed", "unboxed");
    for fate in fates {
        let b = acct
            .sites
            .iter()
            .filter(|s| s.boxed && s.fate == Some(fate))
            .count();
        let u = acct
            .sites
            .iter()
            .filter(|s| !s.boxed && s.fate == Some(fate))
            .count();
        println!("  {:<20} {b:>10} {u:>10}", format!("{fate:?}"));
    }
    let mapped_b = acct
        .sites
        .iter()
        .filter(|s| s.boxed && s.flow.is_some())
        .count();
    let mapped_u = acct
        .sites
        .iter()
        .filter(|s| !s.boxed && s.flow.is_some())
        .count();
    println!("  {:<20} {mapped_b:>10} {mapped_u:>10}", "mapped");
    if acct.sites_unmapped > 0 {
        let mut by: BTreeMap<&str, (usize, String, u32)> = BTreeMap::new();
        for s in acct.sites.iter().filter(|s| s.flow.is_none()) {
            let e = by.entry(s.reason.unwrap()).or_insert((0, String::new(), 0));
            e.0 += 1;
            if e.1.is_empty() {
                e.1 = s.module.clone();
                e.2 = s.app;
            }
        }
        println!("  not a saturated construction");
        for (reason, (n, md, node)) in &by {
            println!("    {n:>6}  {reason:<28} e.g. {md} node {node}");
        }
    }
    println!(
        "  each mapped site belongs to exactly one construction; {} distinct construction(s)",
        acct.sites
            .iter()
            .filter_map(|s| s.flow)
            .collect::<std::collections::BTreeSet<_>>()
            .len()
    );

    // Consumers.
    println!();
    println!("Consumers by kind");
    let mut kinds: BTreeMap<&str, (usize, usize)> = BTreeMap::new();
    for f in flows {
        for u in &f.consumers {
            let e = kinds.entry(u.kind()).or_default();
            if f.boxed {
                e.0 += 1;
            } else {
                e.1 += 1;
            }
        }
    }
    println!("  {:<20} {:>10} {:>10}", "kind", "boxed", "unboxed");
    for (k, (b, u)) in &kinds {
        println!("  {k:<20} {b:>10} {u:>10}");
    }
    let no_consumer = flows.iter().filter(|f| f.consumers.is_empty()).count();
    println!("  constructions with no surviving consumer: {no_consumer}");

    // Rules.
    println!();
    println!("Rules by the number of constructions they fire on");
    let mut rules: BTreeMap<&str, usize> = BTreeMap::new();
    for f in flows {
        let mut seen: std::collections::BTreeSet<&str> = Default::default();
        for e in &f.evidence {
            if seen.insert(e.rule) {
                *rules.entry(e.rule).or_default() += 1;
            }
        }
    }
    for (r, n) in &rules {
        println!("  {r:<24} {n:>8}");
    }

    // Reasons.
    for (title, fate) in [
        ("Preserve", TupleFate::Preserve),
        ("Unresolved", TupleFate::Unresolved),
    ] {
        println!();
        println!("Top reasons for {title}");
        let mut by: BTreeMap<String, (usize, String, u32)> = BTreeMap::new();
        for f in flows.iter().filter(|f| f.fate == fate) {
            let Some(key) = f.reason_key() else { continue };
            let e = by.entry(key).or_insert((0, String::new(), 0));
            e.0 += 1;
            if e.1.is_empty() {
                e.1 = f.module.clone();
                e.2 = f.construction;
            }
        }
        let mut rows: Vec<_> = by.into_iter().collect();
        rows.sort_by(|a, b| b.1.0.cmp(&a.1.0).then(a.0.cmp(&b.0)));
        for (reason, (n, md, node)) in rows.into_iter().take(10) {
            println!("  {n:>6}  {reason}");
            println!("          e.g. {md} node {node}");
        }
    }

    // Per module.
    println!();
    println!("Per module");
    println!(
        "  {:<34} {:>7} {:>7} {:>7} {:>7} {:>6} {:>7} {:>7}",
        "module", "boxed", "unbox", "scalar", "return", "clone", "presrv", "unres"
    );
    for t in &tc.per_module {
        if t.flows.is_empty() {
            continue;
        }
        let n = |fate: TupleFate| t.flows.iter().filter(|f| f.fate == fate).count();
        println!(
            "  {:<34} {:>7} {:>7} {:>7} {:>7} {:>6} {:>7} {:>7}",
            t.module.name,
            t.flows.iter().filter(|f| f.boxed).count(),
            t.flows.iter().filter(|f| !f.boxed).count(),
            n(TupleFate::ScalarReplace),
            n(TupleFate::WorkerReturn),
            n(TupleFate::RemovableWithClone),
            n(TupleFate::Preserve),
            n(TupleFate::Unresolved),
        );
    }

    // The cross-milestone link: the M1 thunk sites that are these tuples'
    // lazy selectors, and therefore disappear with them.
    let l = h2r_analysis::link::link(&census, &tc, &selected);
    println!();
    println!("Thunk sites explained by tuple transport (M1 × M2.2)");
    println!(
        "  {} of M1's {} potential thunk site(s) have a right-hand side that is a lazy",
        l.explained.len(),
        l.thunk_sites
    );
    println!(
        "  selector or a field-wise re-tupling over a removable, verified tuple; \
         {} remain.",
        l.remaining()
    );
    println!(
        "  {:<44} {:>8} {:>9} {:>8}",
        "", "before", "explained", "after"
    );
    for r in &l.fates {
        println!(
            "  {:<44} {:>8} {:>9} {:>8}",
            r.label,
            r.before,
            r.explained,
            r.after()
        );
    }
    for r in &l.memo {
        println!(
            "  {:<44} {:>8} {:>9} {:>8}",
            format!("… {}", r.label),
            r.before,
            r.explained,
            r.after()
        );
    }
    println!(
        "  {:<44} {:>8} {:>9} {:>8}",
        "potential thunk sites",
        l.thunk_sites,
        l.explained.len(),
        l.remaining()
    );
    println!("  by binder origin");
    for (o, before, explained) in &l.origins {
        if *before == 0 && *explained == 0 {
            continue;
        }
        println!(
            "    {:<42} {:>8} {:>9} {:>8}",
            format!("{o:?}"),
            before,
            explained,
            before - explained
        );
    }
    println!("  by the rule that explains it");
    for (rule, n) in &l.by_rule {
        println!("    {rule:<42} {n:>8}");
    }
    // Reported beside the table, never in it: a binding whose right-hand
    // side *is* the tuple holds a box that will not exist, but what
    // replaces it is n scalar bindings, and whether those are thunks is a
    // question for the let census to answer again after the rewrite.
    let mut held_by_origin: BTreeMap<String, usize> = BTreeMap::new();
    for e in &l.holds {
        *held_by_origin.entry(format!("{:?}", e.origin)).or_default() += 1;
    }
    println!(
        "  beside them, {} thunk site(s) *hold* a normalised tuple (T1-LET-BOUND): the box",
        l.holds.len()
    );
    println!("  is gone, but what replaces each is one scalar binding per field, so they");
    println!(
        "  are not counted as explained — by origin: {}",
        held_by_origin
            .iter()
            .map(|(o, n)| format!("{o} {n}"))
            .collect::<Vec<_>>()
            .join(", ")
    );
    println!(
        "  of the census' {} tuple-attributed lazy argument sites, {} become a scalar",
        l.sites, l.sites_explained
    );
    println!(
        "  binding because their tuple is normalised ({} boxed, {} unboxed)",
        l.sites_explained_boxed, l.sites_explained_unboxed
    );

    if explain {
        println!();
        println!("Constructions");
        for t in &tc.per_module {
            for f in &t.flows {
                println!();
                println!(
                    "{} node {} — {} tuple of arity {}, fate {:?}{}",
                    f.module,
                    f.construction,
                    if f.boxed { "boxed" } else { "unboxed" },
                    f.arity,
                    f.fate,
                    match f.reason_key() {
                        Some(r) => format!(" ({r})"),
                        None => String::new(),
                    }
                );
                for e in &f.evidence {
                    let nodes = e
                        .nodes
                        .iter()
                        .map(|n| n.to_string())
                        .collect::<Vec<_>>()
                        .join(", ");
                    let b = match e.binder {
                        Some(b) => format!(" [binder #{b} {}]", t.binder(b).occ),
                        None => String::new(),
                    };
                    println!("    {:<22} node(s) {nodes}{b}: {}", e.rule, e.note);
                }
                for u in &f.consumers {
                    println!("    use {:<18} node {}", u.kind(), u.at());
                }
            }
        }
    }

    Ok(())
}

//------------------------------------------------------------------------------
// fields
//------------------------------------------------------------------------------

/// The constructor-field census: what does the optimised Core prove about
/// *when* each field of each saturated construction is evaluated?
fn fields(
    dir: &Path,
    module: Option<&str>,
    json: bool,
    explain: bool,
    con: Option<&str>,
    view: Option<u32>,
    view_all: bool,
) -> Result<()> {
    use h2r_analysis::fields::FieldRep;

    let modules = load_dir(dir)?;
    let selected: Vec<&Module> = match module {
        Some(name) => vec![find_module(&modules, name)?],
        None => modules.iter().collect(),
    };
    // M1's census is read for two things and nothing else: its
    // `RecursiveValue` verdicts (the knot definition is M1's) and its
    // constructor-field argument sites. The other two censuses and the
    // verifier come with it so that the milestone accounting this command
    // prints says the same thing `verify-rep` does.
    let all = m23::M23::of(&selected);
    let fc = &all.fc;
    let acct = &fc.accounting;

    if view.is_some() || view_all {
        return m23::field_views(&all, &selected, module, view, view_all, json);
    }

    if json {
        let out = serde_json::json!({
            "flows": fc.flows,
            "accounting": acct,
            "conFields": fc.con_fields,
            "m23Accounting": all.accounting,
        });
        serde_json::to_writer(std::io::stdout().lock(), &out)?;
        println!();
        return Ok(());
    }

    if let Some(name) = con {
        return one_con(fc, name);
    }

    println!("Constructor fields — {} module(s)", selected.len());
    println!();
    println!(
        "Saturated non-tuple, non-list constructions          {:>7}",
        acct.constructions
    );
    println!(
        "  the program's own constructors                     {:>7}",
        acct.constructions_program
    );
    println!(
        "  library constructors                               {:>7}",
        acct.constructions_library
    );
    println!(
        "  observed / unobserved / escaped before observation  {} / {} / {}",
        acct.observed, acct.unobserved, acct.escaped_before_observation
    );
    println!(
        "  alternatives a value of the constructor cannot select, skipped   {:>7}",
        acct.unreachable_alts
    );
    println!(
        "  case-binder occurrences excluded by that reachability            {:>7}",
        acct.alias_occurrences_unreachable
    );
    println!(
        "  nesting fixpoint rounds                            {:>7}",
        fc.per_module
            .iter()
            .map(|f| f.nesting_rounds)
            .max()
            .unwrap_or(0)
    );

    println!();
    println!("Constructions by data constructor (top 25)");
    let mut by_con: BTreeMap<(bool, String), usize> = BTreeMap::new();
    for f in &fc.flows {
        *by_con.entry((f.program, f.occ.clone())).or_default() += 1;
    }
    let mut rows: Vec<_> = by_con.into_iter().collect();
    rows.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
    println!("  {:>7}  {:<8} constructor", "n", "origin");
    for ((program, occ), n) in rows.iter().take(25) {
        println!(
            "  {n:>7}  {:<8} {occ}",
            if *program { "program" } else { "library" }
        );
    }

    // The three orthogonal facts, before any rep is derived from them.
    println!();
    println!("The three facts per (construction, field), before any rep is derived");
    println!(
        "  {:<12} {:<13} {:<14} {:>8}",
        "demand", "strictness", "recursion", "fields"
    );
    for c in &acct.facts {
        println!(
            "  {:<12} {:<13} {:<14} {:>8}",
            format!("{:?}", c.demand),
            format!("{:?}", c.strictness),
            format!("{:?}", c.recursion),
            c.n
        );
    }
    println!(
        "  {:<12} {:<13} {:<14} {:>8}",
        "total", "", "", acct.fields_total
    );
    println!(
        "  of which strict fields nothing demands (forced at WHNF, not Dead)   {:>7}",
        acct.strict_unused
    );

    println!();
    println!("Fields by rep, program/library x GHC-strict/lazy");
    println!(
        "  {:<10} {:>10} {:>10} {:>10} {:>10} {:>10}",
        "", "Dead", "Direct", "Deferred", "Recursive", "Unknown"
    );
    for (program, ghc_strict, label) in [
        (true, true, "program !"),
        (true, false, "program"),
        (false, true, "library !"),
        (false, false, "library"),
    ] {
        let cell = |rep: FieldRep| {
            acct.by_class
                .iter()
                .find(|c| c.program == program && c.ghc_strict == ghc_strict && c.rep == rep)
                .map(|c| c.n)
                .unwrap_or(0)
        };
        println!(
            "  {label:<10} {:>10} {:>10} {:>10} {:>10} {:>10}",
            cell(FieldRep::Dead),
            cell(FieldRep::Direct),
            cell(FieldRep::Deferred),
            cell(FieldRep::Recursive),
            cell(FieldRep::Unknown)
        );
    }
    println!(
        "  {:<10} {:>10} {:>10} {:>10} {:>10} {:>10}",
        "total",
        acct.count(FieldRep::Dead),
        acct.count(FieldRep::Direct),
        acct.count(FieldRep::Deferred),
        acct.count(FieldRep::Recursive),
        acct.count(FieldRep::Unknown)
    );
    println!("  (`!` is a GHC-strict field)");
    println!();
    println!("  Direct, by the rule that proved the timing");
    for (rule, n) in &acct.direct_by_rule {
        println!("    {n:>7}  {rule}");
    }

    println!();
    println!("Observations by kind");
    for (kind, n) in &acct.observations_by_kind {
        println!("  {n:>7}  {kind}");
    }
    println!();
    println!("Rules, by the number of times each fired");
    for (rule, n) in &acct.rules {
        println!("  {n:>7}  {rule}");
    }

    // The M2 census' constructor-field argument sites.
    println!();
    println!(
        "The M2 census' {} constructor-field argument sites",
        acct.sites.len()
    );
    println!(
        "  {:>7}  mapped onto a (construction, field)",
        acct.sites_mapped
    );
    println!(
        "  {:>7}  deferred to M2.3c (the list cons)",
        acct.sites_deferred_to_m23c
    );
    println!("  {:>7}  unmapped, with a reason", acct.sites_unmapped);
    let mut unmapped: BTreeMap<&str, (usize, String, u32)> = BTreeMap::new();
    for s in &acct.sites {
        if s.list_cons {
            continue;
        }
        if let Some(r) = s.reason {
            let e = unmapped.entry(r).or_insert((0, String::new(), 0));
            e.0 += 1;
            if e.1.is_empty() {
                e.1 = s.module.clone();
                e.2 = s.app;
            }
        }
    }
    for (reason, (n, md, node)) in &unmapped {
        println!("    {n:>6}  {reason:<46} e.g. {md} node {node}");
    }
    println!();
    println!("  their FieldRep");
    let mut site_rep: BTreeMap<String, usize> = BTreeMap::new();
    for s in &acct.sites {
        let key = match s.rep {
            Some(r) => r.name().to_string(),
            None if s.list_cons => "deferred to M2.3c".to_string(),
            None => "unmapped".to_string(),
        };
        *site_rep.entry(key).or_default() += 1;
    }
    for (rep, n) in &site_rep {
        println!("    {n:>6}  {rep}");
    }

    // Why the residual is what it is.
    println!();
    for (title, want) in [
        ("Top Deferred reasons", FieldRep::Deferred),
        ("Top Unknown reasons", FieldRep::Unknown),
    ] {
        let mut by: BTreeMap<String, (usize, String, u32)> = BTreeMap::new();
        for f in &fc.flows {
            for v in &f.verdicts {
                if v.rep != want {
                    continue;
                }
                let Some(key) = v.reason_key() else { continue };
                let e = by.entry(key).or_insert((0, String::new(), 0));
                e.0 += 1;
                if e.1.is_empty() {
                    e.1 = f.module.clone();
                    e.2 = f.construction;
                }
            }
        }
        let mut by: Vec<_> = by.into_iter().collect();
        by.sort_by(|a, b| b.1.0.cmp(&a.1.0).then(a.0.cmp(&b.0)));
        println!("{title} (top 10)");
        for (reason, (n, md, node)) in by.iter().take(10) {
            println!("  {n:>7}  {reason:<64} e.g. {md} node {node}");
        }
        println!();
    }

    // The program's own types, field by field.
    println!("The program's own constructors, field by field (top 25 by constructions)");
    println!(
        "  {:>7}  {:<28} {:<6} {:<4} rep",
        "n", "constructor", "field", "GHC"
    );
    for r in fc.con_fields.iter().filter(|r| r.program).take(25) {
        println!(
            "  {:>7}  {:<28} {:<6} {:<4} {:<10} {}",
            r.constructions,
            r.occ,
            r.index,
            if r.ghc_strict { "!" } else { "" },
            r.rep.name(),
            r.by_rep
                .iter()
                .map(|(rep, n)| format!("{} {n}", rep.name()))
                .collect::<Vec<_>>()
                .join(", ")
        );
    }

    if explain {
        println!();
        println!("Every construction");
        for f in &fc.flows {
            println!(
                "{} node {} — {} of arity {} [{}]",
                f.module,
                f.construction,
                f.occ,
                f.arity,
                if f.program { "program" } else { "library" }
            );
            for o in &f.observations {
                println!(
                    "    obs   {:<18} {:<10} node {:<8} {} [{}]",
                    format!("{:?}", o.kind),
                    o.field.map(|i| format!("field {i}")).unwrap_or_default(),
                    o.at,
                    o.detail,
                    o.rule
                );
            }
            for v in &f.verdicts {
                println!(
                    "    field {} — demand {:?}, {:?}, {:?} => {} [{}]{}",
                    v.index,
                    v.demand,
                    v.strictness,
                    v.recursion,
                    v.rep.name(),
                    v.rule,
                    v.reason.map(|r| format!(" ({r})")).unwrap_or_default()
                );
                for e in &v.evidence {
                    println!("            {} — {} {:?}", e.rule, e.note, e.nodes);
                }
            }
            for e in &f.evidence {
                println!("    why   {} — {} {:?}", e.rule, e.note, e.nodes);
            }
        }
    }
    m23::print_accounting(&all.accounting);
    Ok(())
}

/// One data constructor's fields, with the per-construction verdicts behind
/// each of them.
fn one_con(fc: &h2r_analysis::fields::FieldCensus<'_>, name: &str) -> Result<()> {
    let rows: Vec<_> = fc
        .con_fields
        .iter()
        .filter(|r| r.occ == name || r.con == name)
        .collect();
    if rows.is_empty() {
        anyhow::bail!("no saturated construction of {name} in the selected module(s)");
    }
    println!("{name}");
    for r in &rows {
        println!(
            "  field {} {:<2} {:<10} over {} construction(s): {}",
            r.index,
            if r.ghc_strict { "!" } else { "" },
            r.rep.name(),
            r.constructions,
            r.by_rep
                .iter()
                .map(|(rep, n)| format!("{} {n}", rep.name()))
                .collect::<Vec<_>>()
                .join(", ")
        );
    }
    let all: Vec<_> = fc
        .flows
        .iter()
        .filter(|f| f.occ == name || f.con == name)
        .collect();
    println!();
    println!("  per construction ({} in all, first 25)", all.len());
    for f in all.iter().take(25) {
        println!(
            "    {} node {:<8} {}",
            f.module,
            f.construction,
            f.verdicts
                .iter()
                .map(|v| format!(
                    "f{}={}{}",
                    v.index,
                    v.rep.name(),
                    v.reason_key()
                        .map(|r| format!(" [{r}]"))
                        .unwrap_or_default()
                ))
                .collect::<Vec<_>>()
                .join("  ")
        );
    }
    Ok(())
}

//------------------------------------------------------------------------------
// lists
//------------------------------------------------------------------------------

/// The list census: when and how much of each spine is demanded, by whom,
/// how often, and does anything alias its tail?
fn lists(
    dir: &Path,
    module: Option<&str>,
    json: bool,
    explain: bool,
    show_axioms: bool,
    view: Option<u32>,
    view_all: bool,
) -> Result<()> {
    use h2r_analysis::lists::axioms;
    use h2r_analysis::lists::{ConsumerKind, Recommendation};

    if show_axioms && module.is_none() && dir.as_os_str().is_empty() {
        return print_axioms();
    }

    let modules = load_dir(dir)?;
    let selected: Vec<&Module> = match module {
        Some(name) => vec![find_module(&modules, name)?],
        None => modules.iter().collect(),
    };
    // M1's census is read for two things only: its `RecursiveValue`
    // verdicts (the knot definition is M1's) and its list-cons argument
    // sites — the 1,310 the constructor-field census deferred here.
    let all = m23::M23::of(&selected);
    let lc = &all.lc;
    let acct = &lc.accounting;

    if view.is_some() || view_all {
        return m23::list_views(&all, &selected, module, view, view_all, json);
    }

    if json {
        let out = serde_json::json!({
            "flows": lc.flows,
            "accounting": acct,
            "axioms": axioms::all(),
            "baseVersion": axioms::BASE_VERSION,
            "m23Accounting": all.accounting,
        });
        serde_json::to_writer(std::io::stdout().lock(), &out)?;
        println!();
        return Ok(());
    }

    if show_axioms {
        print_axioms()?;
        println!();
    }

    println!("List flows — {} module(s)", selected.len());
    println!();
    println!(
        "Flows                                                {:>7}",
        acct.flows
    );
    println!(
        "  cons cells built by those producers                {:>7}",
        acct.cells
    );
    println!(
        "  alternatives a value of the constructor cannot select, skipped   {:>7}",
        acct.unreachable_alts
    );
    println!(
        "  case-binder occurrences excluded by that reachability            {:>7}",
        acct.alias_occurrences_unreachable
    );
    println!(
        "  flows abandoned at the location budget             {:>7}",
        acct.over_budget
    );
    println!(
        "  successor fixpoint updates                         {:>7}",
        lc.per_module
            .iter()
            .map(|l| l.successor_rounds)
            .max()
            .unwrap_or(0)
    );

    println!();
    println!("By producer kind");
    for (kind, n) in &acct.by_kind {
        println!("  {n:>7}  {}", kind.name());
    }

    println!();
    println!("The six facts, each recorded independently");
    for (title, rows) in [
        ("SpineDemand", &acct.by_spine),
        ("HeadDemand", &acct.by_head),
        ("Reuse", &acct.by_reuse),
        ("Storage", &acct.by_storage),
        ("Recursion", &acct.by_recursion),
    ] {
        println!("  {title}");
        let mut rows: Vec<_> = rows.iter().collect();
        rows.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(b.0)));
        for (name, n) in rows {
            println!("    {n:>7}  {name}");
        }
    }
    println!("  ShortCircuit");
    println!(
        "    {:>7}  yes (a consumer may stop before the end)",
        acct.short_circuit_yes
    );
    println!("    {:>7}  no", acct.short_circuit_no);
    println!(
        "  of the flows, {} have only streaming spine consumers",
        acct.streaming
    );

    println!();
    println!("Recommendation (advisory — the theorem is the facts above)");
    for r in [
        Recommendation::VecCandidate,
        Recommendation::IteratorCandidate,
        Recommendation::PersistentCandidate,
        Recommendation::LazyCandidate,
        Recommendation::Unknown,
    ] {
        println!("  {:>7}  {}", acct.count(r), r.name());
    }

    println!();
    println!("Recommendation x SpineDemand");
    let mut grid: BTreeMap<(&str, &str), usize> = BTreeMap::new();
    for f in &lc.flows {
        *grid.entry((f.rec.name(), f.spine.name())).or_default() += 1;
    }
    for ((rec, spine), n) in &grid {
        println!("  {n:>7}  {rec:<20} {spine}");
    }

    println!();
    println!(
        "Imported heads the flows reached: {} ({} with an axiom, {} without)",
        acct.heads.len(),
        acct.heads_with_axiom,
        acct.heads_without_axiom
    );
    println!("  (the table was written against {})", axioms::BASE_VERSION);
    println!(
        "  {:>7}  {:<6} {:<58} example",
        "calls", "axiom", "stable name"
    );
    for (name, n, has, node) in &acct.heads {
        println!(
            "  {n:>7}  {:<6} {name:<58} node {node}",
            if *has { "yes" } else { "NO" }
        );
    }

    println!();
    println!("Consumers by kind");
    for (kind, n) in &acct.consumers_by_kind {
        println!("  {n:>7}  {kind}");
    }
    println!();
    println!("Rules, by the number of times each fired");
    for (rule, n) in &acct.rules {
        println!("  {n:>7}  {rule}");
    }

    // The 1,310 the constructor-field census deferred here.
    println!();
    println!(
        "The M2 census' {} list-cons argument sites (deferred to M2.3c by the field census)",
        acct.sites.len()
    );
    println!(
        "  {:>7}  mapped onto the cell they are an argument of",
        acct.sites_mapped
    );
    println!("  {:>7}  unmapped, with a reason", acct.sites_unmapped);
    let mut unmapped: BTreeMap<&str, (usize, String, u32)> = BTreeMap::new();
    for s in &acct.sites {
        if let Some(r) = s.reason {
            let e = unmapped.entry(r).or_insert((0, String::new(), 0));
            e.0 += 1;
            if e.1.is_empty() {
                e.1 = s.module.clone();
                e.2 = s.app;
            }
        }
    }
    for (reason, (n, md, node)) in &unmapped {
        println!("    {n:>6}  {reason:<46} e.g. {md} node {node}");
    }
    println!();
    println!("  by recommendation, and by the field of the cell they land in");
    let mut by_rec: BTreeMap<&str, usize> = BTreeMap::new();
    let mut by_spine: BTreeMap<&str, usize> = BTreeMap::new();
    let mut by_field: BTreeMap<String, usize> = BTreeMap::new();
    for s in &acct.sites {
        *by_rec
            .entry(s.rec.map(|r| r.name()).unwrap_or("unmapped"))
            .or_default() += 1;
        *by_spine
            .entry(s.spine.map(|x| x.name()).unwrap_or("unmapped"))
            .or_default() += 1;
        *by_field
            .entry(match s.field {
                Some(0) => "field 0 (the element)".to_string(),
                Some(1) => "field 1 (the tail)".to_string(),
                Some(k) => format!("field {k}"),
                None => "unmapped".to_string(),
            })
            .or_default() += 1;
    }
    for (rec, n) in &by_rec {
        println!("    {n:>6}  {rec}");
    }
    println!();
    println!("  and by SpineDemand");
    for (spine, n) in &by_spine {
        println!("    {n:>6}  {spine}");
    }
    println!();
    for (field, n) in &by_field {
        println!("    {n:>6}  {field}");
    }

    // Why the residual is what it is.
    println!();
    println!("Top Unknown reasons (top 10)");
    let mut by: BTreeMap<String, (usize, String, u32)> = BTreeMap::new();
    for f in &lc.flows {
        if f.rec != Recommendation::Unknown {
            continue;
        }
        let key = f
            .rec_reason
            .clone()
            .unwrap_or_else(|| "unstated".to_string());
        let e = by.entry(key).or_insert((0, String::new(), 0));
        e.0 += 1;
        if e.1.is_empty() {
            e.1 = f.module.clone();
            e.2 = f.producer;
        }
    }
    let mut by: Vec<_> = by.into_iter().collect();
    by.sort_by(|a, b| b.1.0.cmp(&a.1.0).then(a.0.cmp(&b.0)));
    for (reason, (n, md, node)) in by.iter().take(10) {
        println!("  {n:>7}  {reason:<66} e.g. {md} node {node}");
    }

    println!();
    println!("Element types, as GHC rendered them (corroboration only — M2.3d decides text)");
    let mut tys: BTreeMap<String, usize> = BTreeMap::new();
    for f in &lc.flows {
        if let Some(t) = &f.elem_ty {
            *tys.entry(t.clone()).or_default() += 1;
        }
    }
    let mut tys: Vec<_> = tys.into_iter().collect();
    tys.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
    for (ty, n) in tys.iter().take(15) {
        println!("  {n:>7}  {ty}");
    }

    if explain {
        println!();
        println!("Every flow");
        for f in &lc.flows {
            println!(
                "{} node {} — {} [{} cell(s)]{}",
                f.module,
                f.producer,
                f.kind.name(),
                f.cells.len(),
                if f.producer_name.is_empty() {
                    String::new()
                } else {
                    format!(" {}", f.producer_name)
                }
            );
            println!(
                "    facts  spine {} [{}], head {}, reuse {}, storage {}, {:?}, short-circuit {}",
                f.spine.name(),
                f.spine_rule,
                f.head.name(),
                f.reuse.name(),
                f.storage.name(),
                f.recursion,
                if f.short_circuit.no() {
                    "no".to_string()
                } else {
                    format!("{:?}", f.short_circuit.yes)
                }
            );
            println!(
                "    types  list {:?}, element {:?}",
                f.list_ty.as_deref().unwrap_or("-"),
                f.elem_ty.as_deref().unwrap_or("-")
            );
            for c in &f.consumers {
                println!(
                    "    use    {:<14} node {:<8} spine {:<22} head {:<8} {}{} [{}] {}",
                    match &c.kind {
                        ConsumerKind::Axiom { rule, .. } => (*rule).to_string(),
                        k => h2r_analysis::lists::consumer_name(k).to_string(),
                    },
                    c.at,
                    c.spine.name(),
                    c.head.name(),
                    if c.streaming {
                        "streaming "
                    } else {
                        "retaining "
                    },
                    if c.tail_derived { "tail-derived" } else { "" },
                    c.rule,
                    c.detail
                );
            }
            println!(
                "    => {} [{}]{}",
                f.rec.name(),
                f.rec_rule,
                f.rec_reason
                    .as_ref()
                    .map(|r| format!(" ({r})"))
                    .unwrap_or_default()
            );
            for e in &f.evidence {
                println!("    why    {} — {} {:?}", e.rule, e.note, e.nodes);
            }
        }
    }
    m23::print_accounting(&all.accounting);
    Ok(())
}

/// The library demand-semantics table, printed in full.
fn print_axioms() -> Result<()> {
    use h2r_analysis::lists::axioms;
    println!(
        "Library demand-semantics table — {} entries, written against {}",
        axioms::all().len(),
        axioms::BASE_VERSION
    );
    println!(
        "Evidence level: library axiom (below def-use dataflow, above textual type comparison)."
    );
    println!("List arguments are indexed from the END of the call's value arguments.");
    println!();
    println!(
        "  {:<26} {:<52} {:<3} {:<24} {:<8} {:<24} {:<3} {:<3} alias",
        "rule", "stable name", "n", "list args (End(i)=spine)", "head", "result", "sc", "str"
    );
    for a in axioms::all() {
        println!(
            "  {:<26} {:<52} {:<3} {:<24} {:<8} {:<24} {:<3} {:<3} {:?}",
            a.rule,
            a.name,
            a.min_args,
            a.list_args
                .iter()
                .map(|(e, s)| format!("End({e})={s:?}"))
                .collect::<Vec<_>>()
                .join(" "),
            a.head.name(),
            format!("{:?}", a.produces),
            if a.short_circuit { "yes" } else { "no" },
            if a.streaming { "yes" } else { "no" },
            a.alias
        );
        println!("  {:<26} {}", "", a.note);
    }
    Ok(())
}

//------------------------------------------------------------------------------
// text
//------------------------------------------------------------------------------

/// The text census: which list flows are `[Char]`, how that was
/// established, and what the program does with them.
fn text(
    dir: &Path,
    module: Option<&str>,
    json: bool,
    explain: bool,
    show_heads: bool,
    view: Option<u32>,
    view_all: bool,
) -> Result<()> {
    use h2r_analysis::text::{Advisory, ConsumerShape, ElementTypeEvidence, TEXT_HEADS, TextShape};

    let modules = load_dir(dir)?;
    let selected: Vec<&Module> = match module {
        Some(name) => vec![find_module(&modules, name)?],
        None => modules.iter().collect(),
    };
    let all = m23::M23::of(&selected);
    let tc = &all.tc;
    let acct = &tc.accounting;

    if view.is_some() || view_all {
        return m23::text_views(&all, &selected, module, view, view_all, json);
    }

    if json {
        let out = serde_json::json!({
            "flows": tc.flows,
            "accounting": acct,
            "heads": TEXT_HEADS,
            "m23Accounting": all.accounting,
        });
        serde_json::to_writer(std::io::stdout().lock(), &out)?;
        println!();
        return Ok(());
    }

    if show_heads {
        println!(
            "Text-head table — {} entries, keyed on (module, occ), imported heads only",
            TEXT_HEADS.len()
        );
        println!("Evidence level: library axiom (5) — asserted, not derived.");
        println!();
        println!(
            "  {:<24} {:<26} {:<12} {:<16} {:<5} {:<5} fixes [Char]",
            "module", "occ", "family", "class override", "char", "pos"
        );
        for h in TEXT_HEADS {
            println!(
                "  {:<24} {:<26} {:<12} {:<16} {:<5} {:<5} {}",
                h.module,
                h.occ,
                h.family.name(),
                h.class_override.map(|c| c.name()).unwrap_or("-"),
                if h.char_exposing { "yes" } else { "no" },
                if h.position_semantics { "yes" } else { "no" },
                if h.fixes_char { "yes" } else { "no" },
            );
            println!("  {:<24} {}", "", h.note);
        }
        println!();
    }

    println!("Text flows — {} module(s)", selected.len());
    println!();
    println!("The caveat this milestone is built on");
    println!("  The dump carries pretty-printed type strings, not TyCon identity.");
    println!("  Reading `Char` off a rendered type is level-6 evidence (textual type");
    println!("  comparison, corroboration) — not `TyConApp [] [Char]`. Every selection");
    println!("  below says which evidence established it.");

    println!();
    println!("Selection, out of M2.3c's list flows");
    println!("  {:>7}  list flows", acct.list_flows);
    println!("  {:>7}  text", acct.text_flows);
    println!(
        "  {:>7}  not text (element type reads as something else)",
        acct.non_text
    );
    println!(
        "  {:>7}  element-type-unknown (a type variable, or nothing readable) — never assumed text",
        acct.elem_unknown
    );
    println!();
    println!("  how Char was established, for the text flows");
    println!(
        "  {:>7}  {} (level 6 only)",
        acct.type_only,
        ElementTypeEvidence::TypeStringOnly.name()
    );
    println!(
        "  {:>7}  {} (an unpack producer, a Char literal, a Char scrutiny, or a signature)",
        acct.structural_only,
        ElementTypeEvidence::StructuralOnly.name()
    );
    println!(
        "  {:>7}  {} (a rendered type and a structural fact agree)",
        acct.both,
        ElementTypeEvidence::Both.name()
    );
    println!(
        "  {:>7}  of the structural selections came from the append-chain rule (X24)",
        acct.propagated
    );
    println!(
        "  {:>7}  propagations refused: they would have contradicted a rendered element type",
        acct.propagation_refused
    );
    println!(
        "  {:>7}  flows still element-type-unknown that a consumer signature would have fixed",
        acct.elem_unknown_with_char_axiom
    );

    println!();
    println!("Rendered element types of the flows that are not text (top 10)");
    for (ty, n) in acct.non_text_types.iter().take(10) {
        println!("  {n:>7}  {ty}");
    }

    println!();
    println!("Fact: is every consumer text-shaped?");
    for s in [
        TextShape::TextOnly,
        TextShape::Mixed,
        TextShape::Unobserved,
        TextShape::Unknown,
    ] {
        let n = acct
            .by_shape
            .iter()
            .find(|(x, _)| *x == s.name())
            .map(|(_, n)| *n)
            .unwrap_or(0);
        println!("  {n:>7}  {}", s.name());
    }

    println!();
    println!("Fact: consumers, by what they need of the text");
    for (class, n) in &acct.by_class {
        println!("  {n:>7}  {class}");
    }
    println!(
        "  ({} consumer classes are asserted by the text-head table rather than derived)",
        acct.asserted_class_consumers
    );
    println!();
    println!("Fact: consumers, by which side of the text line they fall on");
    for (shape, n) in &acct.by_consumer_shape {
        println!("  {n:>7}  {shape}");
    }
    println!();
    println!("Fact: text-shaped consumers, by family");
    for (fam, n) in &acct.by_family {
        println!("  {n:>7}  {fam}");
    }

    println!();
    println!("Fact: construction");
    println!(
        "  {:>7}  literal (an unpackCString#-family producer)",
        acct.literal_flows
    );
    println!("  {:>7}  built by an append", acct.append_flows);
    println!(
        "  {:>7}  of those, every operand a literal",
        acct.append_all_literal
    );
    println!("  {:>7}  an operand of an append", acct.append_operands);
    println!();
    println!("  append-chain histogram (operand segments)");
    for (len, n) in &acct.append_hist {
        println!("    {n:>6}  {len} segment(s)");
    }

    println!();
    println!("Fact: inherited from the list flow, cited and not recomputed");
    println!(
        "  {:>7}  with a shared tail (L14-SHARED-TAIL)",
        acct.shared_tail_flows
    );
    println!(
        "  {:>7}  with a prefix consumer",
        acct.prefix_consumer_flows
    );
    println!(
        "  {:>7}  that escape what the walk follows (L11-ESCAPE)",
        acct.escaping_flows
    );
    println!("  Storage");
    for (s, n) in &acct.by_storage {
        println!("    {n:>6}  {s}");
    }
    println!("  Recursion");
    for (s, n) in &acct.by_recursion {
        println!("    {n:>6}  {s}");
    }

    println!();
    println!(
        "Fact: char_semantics_required — {} of {} flows",
        acct.char_semantics, acct.text_flows
    );
    println!("  (this does NOT preclude String: it says a representation must keep");
    println!("   character semantics explicit rather than treating the value as bytes)");
    for (reason, n) in &acct.char_reasons {
        println!("  {n:>7}  {reason}");
    }

    println!();
    println!("Advisory — clearly separated; the theorem is the facts above.");
    println!("Nothing here decides that any of these is a Rust String.");
    for a in [
        Advisory::StrongStringCandidate,
        Advisory::TextValueUndecided,
        Advisory::NotText,
        Advisory::Unknown,
    ] {
        println!("  {:>7}  {}", acct.count(a), a.name());
    }
    println!(
        "  ({} flows have no text-shaped consumer at all, whatever else is unknown about them)",
        tc.flows.iter().filter(|f| !f.has_text_consumer()).count()
    );

    println!();
    println!("Advisory x shape");
    let mut grid: BTreeMap<(&str, &str), usize> = BTreeMap::new();
    for f in &tc.flows {
        *grid.entry((f.advisory.name(), f.shape.name())).or_default() += 1;
    }
    for ((a, s), n) in &grid {
        println!("  {n:>7}  {a:<22} {s}");
    }

    println!();
    println!("M2.3c's append consumer sites, and how many sit on a text flow");
    println!("  {:>7}  {:>7}  stable name", "sites", "on text");
    for (name, total, on_text) in &acct.append_consumer_sites {
        println!("  {total:>7}  {on_text:>7}  {name}");
    }

    println!();
    println!(
        "The M2 census' lazy-argument sites at the two append heads ({} sites)",
        acct.sites.len()
    );
    println!("  {:>7}  map onto a text flow", acct.sites_mapped);
    println!("  {:>7}  do not, with a reason", acct.sites_unmapped);
    let mut by_callee: BTreeMap<&str, (usize, usize)> = BTreeMap::new();
    for s in &acct.sites {
        let e = by_callee.entry(s.callee.as_str()).or_insert((0, 0));
        e.0 += 1;
        if s.flow.is_some() {
            e.1 += 1;
        }
    }
    for (callee, (n, mapped)) in &by_callee {
        println!("    {n:>6}  {callee} ({mapped} on a text flow)");
    }
    println!();
    println!("  by advisory");
    let mut by_adv: BTreeMap<&str, usize> = BTreeMap::new();
    for s in &acct.sites {
        *by_adv
            .entry(s.advisory.map(|a| a.name()).unwrap_or("unmapped"))
            .or_default() += 1;
    }
    for (a, n) in &by_adv {
        println!("    {n:>6}  {a}");
    }
    println!();
    println!("  unmapped, by reason");
    let mut unmapped: BTreeMap<&str, (usize, String, u32)> = BTreeMap::new();
    for s in &acct.sites {
        if let Some(r) = s.reason {
            let e = unmapped.entry(r).or_insert((0, String::new(), 0));
            e.0 += 1;
            if e.1.is_empty() {
                e.1 = s.module.clone();
                e.2 = s.app;
            }
        }
    }
    for (r, (n, md, node)) in &unmapped {
        println!("    {n:>6}  {r:<52} e.g. {md} node {node}");
    }

    println!();
    println!("Per module");
    println!("  {:>7}  {:>7}  module", "list", "text");
    for (name, list, text) in &acct.per_module {
        if *text > 0 {
            println!("  {list:>7}  {text:>7}  {name}");
        }
    }

    println!();
    println!("Rules, by the number of times each fired");
    for (rule, n) in &acct.rules {
        println!("  {n:>7}  {rule}");
    }

    println!();
    println!("Top Unknown reasons (top 10)");
    let mut by: BTreeMap<String, (usize, String, u32)> = BTreeMap::new();
    for f in &tc.flows {
        if f.advisory != Advisory::Unknown {
            continue;
        }
        for r in f.unknown_reasons() {
            let e = by.entry(r).or_insert((0, String::new(), 0));
            e.0 += 1;
            if e.1.is_empty() {
                e.1 = f.module.clone();
                e.2 = f.producer;
            }
        }
    }
    let mut by: Vec<_> = by.into_iter().collect();
    by.sort_by(|a, b| b.1.0.cmp(&a.1.0).then(a.0.cmp(&b.0)));
    for (reason, (n, md, node)) in by.iter().take(10) {
        println!("  {n:>7}  {reason:<70} e.g. {md} node {node}");
    }

    println!();
    println!("Top Mixed reasons — the generic or structural consumer that mixed it (top 10)");
    let mut mixed: BTreeMap<String, (usize, String, u32)> = BTreeMap::new();
    for f in &tc.flows {
        if f.shape != TextShape::Mixed {
            continue;
        }
        for c in &f.consumers {
            if !matches!(c.shape, ConsumerShape::Generic | ConsumerShape::Structural) {
                continue;
            }
            let key = if c.name.is_empty() {
                format!("{} ({})", c.shape.name(), c.list_rule)
            } else {
                format!("{} {}", c.shape.name(), c.name)
            };
            let e = mixed.entry(key).or_insert((0, String::new(), 0));
            e.0 += 1;
            if e.1.is_empty() {
                e.1 = f.module.clone();
                e.2 = c.at;
            }
        }
    }
    let mut mixed: Vec<_> = mixed.into_iter().collect();
    mixed.sort_by(|a, b| b.1.0.cmp(&a.1.0).then(a.0.cmp(&b.0)));
    for (reason, (n, md, node)) in mixed.iter().take(10) {
        println!("  {n:>7}  {reason:<70} e.g. {md} node {node}");
    }

    if explain {
        println!();
        println!("Every text flow");
        for f in &tc.flows {
            println!(
                "{} node {} — {} {}",
                f.module,
                f.producer,
                f.kind.name(),
                f.producer_name
            );
            println!(
                "    types  list {:?}, element {:?} — {}",
                f.list_ty.as_deref().unwrap_or("-"),
                f.elem_ty.as_deref().unwrap_or("-"),
                f.element_type_evidence.name()
            );
            for e in &f.selection {
                println!("    select {} — {} {:?}", e.rule, e.note, e.nodes);
            }
            println!(
                "    facts  shape {} [{}], literal {}, append {:?}, complete {}, prefix {}, \
                 incremental {}, retained {}, unknown {}",
                f.shape.name(),
                f.shape_rule,
                f.literal,
                f.append_chain,
                f.complete,
                f.prefix,
                f.incremental,
                f.retained,
                f.class_unknown
            );
            println!(
                "    inherit spine {}, head {}, storage {}, shared tails {:?}, escape {:?}",
                f.spine.name(),
                f.head.name(),
                f.storage.name(),
                f.shared_tails,
                f.escaped
            );
            if f.char_semantics_required {
                for (rule, reason, node) in &f.char_reasons {
                    println!("    char   {rule} — {reason} node {node}");
                }
            }
            for c in &f.consumers {
                println!(
                    "    use    {:<10} {:<16} node {:<8} [{} / {}] {}{}",
                    c.shape.name(),
                    c.class.name(),
                    c.at,
                    c.list_rule,
                    c.rule,
                    c.name,
                    if c.asserted { " (asserted)" } else { "" }
                );
            }
            println!(
                "    => {} [{}]{}",
                f.advisory.name(),
                f.advisory_rule,
                f.advisory_reason
                    .as_ref()
                    .map(|r| format!(" ({r})"))
                    .unwrap_or_default()
            );
            for e in &f.evidence {
                println!("    why    {} — {} {:?}", e.rule, e.note, e.nodes);
            }
        }
    }
    m23::print_accounting(&all.accounting);
    Ok(())
}

//------------------------------------------------------------------------------
// verify-rep
//------------------------------------------------------------------------------

/// Re-derive every M2.3 verdict whose being wrong would be a miscompile,
/// with `h2r_analysis::verify_rep` — a walk that shares nothing with
/// `fields.rs`, `lists/` or `text.rs` beyond the IR, and does not use the
/// generic aggregate walk those three are built on.
fn verify_rep(dir: &Path, module: Option<&str>, json: bool, explain: bool) -> Result<()> {
    let modules = load_dir(dir)?;
    let selected: Vec<&Module> = match module {
        Some(name) => vec![find_module(&modules, name)?],
        None => modules.iter().collect(),
    };
    // The claim set, the verifier's answer for each claim and the
    // milestone accounting all come from one place, so that what this
    // command reports and what `h2r fields` / `lists` / `text` report about
    // the same verdict cannot differ.
    let all = m23::M23::of(&selected);
    let census = &all.census;
    let fc = &all.fc;
    let lc = &all.lc;
    let tc = &all.tc;
    let out = all.cc.clone();

    if json {
        let payload = serde_json::json!({
            "crossCheck": out,
            "m23Accounting": all.accounting,
        });
        serde_json::to_writer(std::io::stdout().lock(), &payload)?;
        println!();
        return Ok(());
    }

    println!("Independent re-derivation of the M2.3 representation verdicts");
    println!();
    println!("  The walk below shares nothing with fields.rs, lists/ or text.rs but the IR, and");
    println!(
        "  does not use the generic aggregate walk they are built on. Two things are asserted"
    );
    println!("  rather than derived anywhere and are therefore *consulted*, not re-invented: the");
    println!(
        "  library demand-semantics table and the text-head table (the argument position, the"
    );
    println!("  saturation and the head's import-ness are re-derived here), and M1's");
    println!("  RecursiveValue verdicts.");
    println!();
    println!(
        "  {:<34} {:>8} {:>10} {:>8}",
        "claim", "checked", "re-derived", "refused"
    );
    for (k, n, ok) in &out.by_kind {
        println!("  {:<34} {n:>8} {ok:>10} {:>8}", k.name(), n - ok);
    }
    println!(
        "  {:<34} {:>8} {:>10} {:>8}",
        "total",
        out.checked,
        out.agreed,
        out.checked - out.agreed
    );
    println!();
    println!("Direct, by the rule the census says proved the timing");
    println!("  {:>7}  R1-STRICT-FIELD", out.r1_total);
    println!("  {:>7}  R2-FIELD-IS-VALUE", out.r2_total);
    println!(
        "  {:>7}  …of which the *only* evidence is that the expression is a string literal",
        out.r2_string_literal_only
    );
    println!("           (accepted on okForSpeculation grounds — total, terminating, cheap — and");
    println!("            explicitly NOT because it is in WHNF; GHC's exprIsHNF rejects it)");
    println!("  {:>7}  R3-SAME-FRONTIER", out.r3_total);
    println!();
    println!();
    println!("The audited shapes, in this dump");
    println!("  {:<58} {:>6}  example", "shape", "n");
    for (name, n, at) in rep_patterns(fc, lc, tc) {
        println!("  {name:<58} {n:>6}  {at}");
    }
    println!();
    println!(
        "  {:<44} {:>8}",
        "DISAGREEMENTS (the census claimed it, this walk refutes it)",
        out.real_disagreements()
    );
    println!(
        "  {:<44} {:>8}",
        "coverage refusals (this walk is blunter, no claim)",
        out.coverage_refusals()
    );
    println!();
    if out.disagreements.is_empty() {
        println!("Disagreements: none");
        return Ok(());
    }
    let mut by: BTreeMap<(&str, &str), (usize, String, u32)> = BTreeMap::new();
    for d in &out.disagreements {
        let e = by
            .entry((d.claim.kind.name(), d.refusal.why))
            .or_insert((0, String::new(), 0));
        e.0 += 1;
        if e.1.is_empty() {
            e.1 = d.claim.module.clone();
            e.2 = d.refusal.at;
        }
    }
    println!("Refusals by claim and reason (D = a disagreement, C = coverage only)");
    let mut rows: Vec<_> = by.into_iter().collect();
    rows.sort_by_key(|(_, v)| std::cmp::Reverse(v.0));
    for ((kind, why), (n, m, at)) in rows {
        let tag = if h2r_analysis::verify_rep::is_coverage_refusal(why) {
            'C'
        } else {
            'D'
        };
        println!("  {n:>6}  {tag}  {kind:<28} {why}");
        println!("          e.g. {m} node {at}");
    }
    if explain {
        println!();
        for d in &out.disagreements {
            println!(
                "  {} {} field {} node {} — {} ({})",
                d.claim.module,
                d.claim.kind.name(),
                d.claim.field,
                d.claim.at,
                d.refusal.why,
                d.refusal.detail
            );
        }
    }
    m23::print_accounting(&all.accounting);

    // The cross-milestone link. M2.2's tuple census and its own thunk link
    // are built here rather than read from `h2r tuples`, for the one thing
    // this needs from them: which M1 thunk sites that milestone already
    // explains, so that this one never counts a site twice.
    // Built exactly the way `h2r tuples` builds it — the Parsec proof
    // object included — so the "by tuples" column here is the same 92 that
    // milestone publishes, not a second computation of it.
    let analyses: Vec<h2r_analysis::parsec::Analysis> = selected
        .iter()
        .map(|m| h2r_analysis::parsec::Analysis::of_module(m))
        .collect();
    let hops: Vec<h2r_analysis::tuples::ParsecHops> = analyses
        .iter()
        .map(h2r_analysis::tuples::parsec_hops)
        .collect();
    let tcen = h2r_analysis::tuples::TupleCensus::of_modules_with(&selected, census, &hops);
    let tl = h2r_analysis::link::link(census, &tcen, &selected);
    let theirs = m23::tuple_explained(&tl);
    let rl = h2r_analysis::m23::link(census, fc, lc, tc, &all.verdicts, &selected, &theirs);
    m23::print_link(&rl);

    Ok(())
}

/// The adversarial shapes M2.3e audits, counted in the real dump so that a
/// hand-built regression test is never the only evidence a rule was
/// exercised. Reporting only: every row reads published verdicts.
#[allow(clippy::type_complexity)]
fn rep_patterns(
    fc: &h2r_analysis::fields::FieldCensus<'_>,
    lc: &h2r_analysis::lists::ListCensus<'_>,
    tc: &h2r_analysis::text::TextCensus,
) -> Vec<(&'static str, usize, String)> {
    use h2r_analysis::fields::{ConStrictness, FieldDemand, FieldRep, ObsKind};
    use h2r_analysis::lists::{
        ConsumerKind, PrefixBound, Recommendation, Recursion, Reuse, SpineDemand, Storage,
    };
    use h2r_analysis::text::{Advisory, TextShape};

    let mut out: Vec<(&'static str, usize, String)> = Vec::new();
    let mut row = |name: &'static str, hits: Vec<(String, u32)>| {
        let at = hits
            .first()
            .map(|(m, n)| format!("{m} node {n}"))
            .unwrap_or_else(|| "—".into());
        out.push((name, hits.len(), at));
    };

    // 1 — observed at WHNF only: the bottom-preservation case.
    row(
        "1  observed only at WHNF, no field read — never Direct",
        fc.flows
            .iter()
            .filter(|f| {
                f.observations.iter().any(|o| o.kind == ObsKind::WhnfOnly)
                    && !f
                        .observations
                        .iter()
                        .any(|o| o.kind == ObsKind::FieldDemanded)
                    && f.verdicts.iter().all(|v| v.rep != FieldRep::Direct)
            })
            .map(|f| (f.module.clone(), f.construction))
            .collect(),
    );
    // 2 — an unused *lazy* field is Dead; an unused *strict* one is not.
    row(
        "2a an unused lazy field — Dead",
        fc.flows
            .iter()
            .filter(|f| f.verdicts.iter().any(|v| v.rep == FieldRep::Dead))
            .map(|f| (f.module.clone(), f.construction))
            .collect(),
    );
    row(
        "2b an unused STRICT field — forced at WHNF, never Dead",
        fc.flows
            .iter()
            .filter(|f| {
                f.verdicts.iter().any(|v| {
                    v.demand == FieldDemand::Never
                        && v.strictness == ConStrictness::StrictField
                        && v.rep != FieldRep::Dead
                })
            })
            .map(|f| (f.module.clone(), f.construction))
            .collect(),
    );
    // 3 — demanded on one observation and not another.
    row(
        "3  demanded on some observations only — Deferred",
        fc.flows
            .iter()
            .filter(|f| {
                f.verdicts
                    .iter()
                    .any(|v| v.demand == FieldDemand::Conditional && v.rep == FieldRep::Deferred)
            })
            .map(|f| (f.module.clone(), f.construction))
            .collect(),
    );
    // 4 — a literal prefix bound.
    row(
        "4  a bounded prefix with a literal count — never Vec",
        lc.flows
            .iter()
            .filter(|f| {
                matches!(f.spine, SpineDemand::Prefix(PrefixBound::Known(_)))
                    && f.rec != Recommendation::VecCandidate
            })
            .map(|f| (f.module.clone(), f.producer))
            .collect(),
    );
    // 5 — a short-circuiting consumer.
    row(
        "5  a short-circuiting consumer — data-dependent prefix, never Vec",
        lc.flows
            .iter()
            .filter(|f| {
                !f.short_circuit.no()
                    && matches!(f.spine, SpineDemand::Prefix(PrefixBound::DataDependent))
                    && f.rec != Recommendation::VecCandidate
            })
            .map(|f| (f.module.clone(), f.producer))
            .collect(),
    );
    // 6 — two owners of one tail.
    row(
        "6  a tail that survives in a second place — Persistent, never Iterator",
        lc.flows
            .iter()
            .filter(|f| {
                matches!(f.reuse, Reuse::SharedTail { .. })
                    && f.rec != Recommendation::IteratorCandidate
            })
            .map(|f| (f.module.clone(), f.producer))
            .collect(),
    );
    // 7 — a recursive *function* building a finite list.
    row(
        "7  a finite recursive producer — FiniteProducer, not a knot",
        lc.flows
            .iter()
            .filter(|f| {
                f.recursion == Recursion::FiniteProducer
                    && f.consumers
                        .iter()
                        .any(|c| matches!(c.kind, ConsumerKind::ConsedAsTail { .. }))
                    && f.returned
            })
            .map(|f| (f.module.clone(), f.producer))
            .collect(),
    );
    // 8 — an actual recursive list *value*.
    row(
        "8  a value knot — LazyCandidate",
        lc.flows
            .iter()
            .filter(|f| {
                f.recursion == Recursion::RecursiveKnot && f.rec == Recommendation::LazyCandidate
            })
            .map(|f| (f.module.clone(), f.producer))
            .collect(),
    );
    // 9 — stored in another ADT, and followed or not.
    row(
        "9a stored in another ADT, the holder's field read structurally",
        lc.flows
            .iter()
            .filter(|f| {
                matches!(&f.storage, Storage::StoredIn(c) if c != ":")
                    && f.spine > SpineDemand::None
                    && f.spine != SpineDemand::Unknown
            })
            .map(|f| (f.module.clone(), f.producer))
            .collect(),
    );
    row(
        "9b stored in another ADT, the holder escapes — Unknown",
        lc.flows
            .iter()
            .filter(|f| {
                matches!(&f.storage, Storage::StoredIn(c) if c != ":")
                    && f.rec == Recommendation::Unknown
            })
            .map(|f| (f.module.clone(), f.producer))
            .collect(),
    );
    // 10 — a higher-order hop.
    row(
        "10 through a higher-order parameter — Unknown with a reason",
        lc.flows
            .iter()
            .filter(|f| {
                f.rec == Recommendation::Unknown
                    && f.rec_reason
                        .as_deref()
                        .is_some_and(|r| r.contains("higher-order") || r.contains("unknown"))
            })
            .map(|f| (f.module.clone(), f.producer))
            .collect(),
    );
    // 11 — text and structure at once.
    row(
        "11 [Char] used textually and structurally — never StrongString",
        tc.flows
            .iter()
            .filter(|f| {
                f.char_semantics_required
                    && f.shape != TextShape::TextOnly
                    && f.advisory != Advisory::StrongStringCandidate
            })
            .map(|f| (f.module.clone(), f.producer))
            .collect(),
    );
    // 12 — the whole spine, streamed.
    row(
        "12 the whole spine, one pass, nothing retained — Iterator not Vec",
        lc.flows
            .iter()
            .filter(|f| f.spine == SpineDemand::Whole && f.rec == Recommendation::IteratorCandidate)
            .map(|f| (f.module.clone(), f.producer))
            .collect(),
    );
    // 13 — the right operand of an append is the result's tail.
    row(
        "13 the right operand of an append — SharedTail on it",
        lc.flows
            .iter()
            .filter(|f| {
                f.consumers
                    .iter()
                    .any(|c| c.aliases && matches!(c.kind, ConsumerKind::Axiom { .. }))
            })
            .map(|f| (f.module.clone(), f.producer))
            .collect(),
    );
    // 14 — an alias under an alternative this value cannot take.
    row(
        "14 a case-binder alias under an unreachable alternative — no escape",
        fc.flows
            .iter()
            .filter(|f| f.alias_occurrences_unreachable > 0)
            .map(|f| (f.module.clone(), f.construction))
            .collect(),
    );
    out
}
