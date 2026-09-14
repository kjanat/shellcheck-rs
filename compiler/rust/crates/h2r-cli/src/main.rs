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
        } => show(&dir, &module, node, depth, up),
        Command::Laziness {
            dir,
            module,
            explain,
            thunks_only,
            json,
        } => laziness(&dir, module.as_deref(), explain, thunks_only, json),
        Command::Parsec {
            dir,
            module,
            json,
            explain,
        } => parsec(&dir, module.as_deref(), json, explain),
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

fn show(dir: &Path, module: &str, node: Option<u32>, depth: usize, up: usize) -> Result<()> {
    let modules = load_dir(dir)?;
    let m = find_module(&modules, module)?;
    let pretty = h2r_core_ir::pretty::Pretty {
        module: m,
        max_depth: depth,
        ids: true,
    };
    match node {
        Some(mut id) => {
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
        columns.push((
            label,
            h2r_analysis::metrics::Metrics::of(&census, core_nodes, top),
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

fn parsec(dir: &Path, module: Option<&str>, json: bool, explain: bool) -> Result<()> {
    use h2r_analysis::parsec::{Analysis, Bucket, account};

    let modules = load_dir(dir)?;
    let selected: Vec<&Module> = match module {
        Some(name) => vec![find_module(&modules, name)?],
        None => modules.iter().collect(),
    };
    let census = Census::of_modules(selected.iter().copied());
    let analyses: Vec<Analysis> = selected.iter().map(|m| Analysis::of_module(m)).collect();
    let acct = account(&census, &analyses);

    if json {
        let regions: Vec<_> = analyses.iter().flat_map(|a| a.regions.iter()).collect();
        let out = serde_json::json!({"regions": regions, "accounting": acct});
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
    let tiers = count_by(lazy.iter().map(|a| a.callee.resolution.tier()));
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
