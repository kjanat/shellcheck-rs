//! `h2r` -- driver for the Haskell-to-Rust compiler.
//!
//! Right now it only inspects the Core that `h2r-plugin` dumps. The lowering
//! passes will hang off the same subcommand structure.

use std::collections::BTreeMap;
use std::path::PathBuf;

use anyhow::Result;
use clap::{Parser, Subcommand};
use h2r_core_ir::{Binder, BinderKind, CoreModule, Expr, load_dir, with_big_stack};

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
        /// Directory containing *.core.json
        dir: PathBuf,
        /// Module name, e.g. ShellCheck.Parser
        module: String,
    },
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    with_big_stack(move || match cli.command {
        Command::Stats { dir, per_module } => stats(&dir, per_module),
        Command::Binders { dir, module } => binders(&dir, &module),
    })?
}

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

impl Counts {
    fn add_module(&mut self, m: &CoreModule) {
        self.modules += 1;
        for bind in &m.binds {
            if bind.recursive {
                self.rec_groups += 1;
            }
            self.top_level_binds += bind.pairs.len();
            for pair in &bind.pairs {
                pair.rhs.visit(&mut |e: &Expr| {
                    *self.nodes.entry(e.node_name()).or_default() += 1;
                });
            }
        }
        m.visit_binders(&mut |b: &Binder| {
            self.binders += 1;
            if b.is_join_point == Some(true) {
                self.join_points += 1;
            }
            if b.kind == BinderKind::Id
                && let Some(sig) = &b.dmd_sig
            {
                *self.dmd_sigs.entry(sig.clone()).or_default() += 1;
            }
        });
    }
}

fn stats(dir: &PathBuf, per_module: bool) -> Result<()> {
    let modules = load_dir(dir)?;
    let mut total = Counts::default();

    for m in &modules {
        if per_module {
            let mut one = Counts::default();
            one.add_module(m);
            let nodes: usize = one.nodes.values().sum();
            println!(
                "{:<34} binds={:<6} rec-groups={:<4} binders={:<7} nodes={}",
                m.module, one.top_level_binds, one.rec_groups, one.binders, nodes
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

fn nonempty(s: Option<&str>) -> &str {
    match s {
        Some(s) if !s.is_empty() => s,
        _ => "-",
    }
}

fn binders(dir: &PathBuf, module: &str) -> Result<()> {
    let modules = load_dir(dir)?;
    let Some(m) = modules.iter().find(|m| m.module == module) else {
        anyhow::bail!(
            "no Core dump for module {module}; have: {}",
            modules
                .iter()
                .map(|m| m.module.as_str())
                .collect::<Vec<_>>()
                .join(", ")
        );
    };

    for bind in &m.binds {
        for pair in &bind.pairs {
            let b = &pair.binder;
            println!(
                "{}{:<38} arity={:<3} dmd={:<22} cpr={}",
                if bind.recursive { "rec " } else { "    " },
                b.occ,
                b.arity.unwrap_or(0),
                nonempty(b.dmd_sig.as_deref()),
                nonempty(b.cpr_sig.as_deref()),
            );
            println!("        :: {}", b.ty);
        }
    }
    Ok(())
}
