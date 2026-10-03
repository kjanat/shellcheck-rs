use std::cmp::Reverse;
use std::collections::{BTreeMap, BTreeSet};

use h2r_lower::graph::{Graph, Instances, Normal, Unplaced};

pub fn report(title: &str, graph: &Graph, instances: Option<&BTreeMap<usize, usize>>) {
    let normal = graph.normalize();
    let condensed: usize = normal.condensed.iter().map(BTreeSet::len).sum();
    let reduced: usize = normal.reduced.iter().map(BTreeSet::len).sum();
    let single = normal
        .components
        .iter()
        .filter(|members| members.len() == 1)
        .count();
    println!(
        "{title}: {} modules, {} edges",
        graph.edges.len(),
        graph.edge_count()
    );
    println!(
        "  normalized: {} components ({single} of one module), {condensed} edges between them, {reduced} after transitive reduction, longest chain {}",
        normal.components.len(),
        normal.depth()
    );
    let mut cycles: Vec<&Vec<usize>> = normal
        .components
        .iter()
        .filter(|members| members.len() > 1)
        .collect();
    cycles.sort_by_key(|members| Reverse(members.len()));
    for members in cycles {
        let owned = instances.map(|instances| {
            members
                .iter()
                .map(|member| instances.get(member).copied().unwrap_or(0))
                .sum::<usize>()
        });
        println!(
            "  cycle of {} modules{}:",
            members.len(),
            owned
                .map(|owned| format!(", {owned} instances"))
                .unwrap_or_default()
        );
        let mut names: Vec<&str> = members
            .iter()
            .map(|&member| graph.names[member].as_str())
            .collect();
        names.sort_unstable();
        for name in names {
            println!("    {name}");
        }
    }
}

pub fn added(references: &Graph, instances: &Graph) {
    let unit = |module: usize| {
        instances.names[module]
            .split_once(':')
            .map_or("", |(unit, _)| unit)
    };
    let mut by_units: BTreeMap<(&str, &str), usize> = BTreeMap::new();
    let mut total = 0;
    for (&from, targets) in &instances.edges {
        for &to in targets {
            if !references.edges[&from].contains(&to) {
                total += 1;
                *by_units.entry((unit(from), unit(to))).or_default() += 1;
            }
        }
    }
    println!("Edges the instances add to the Core references: {total}");
    let mut ranked: Vec<_> = by_units.into_iter().collect();
    ranked.sort_by_key(|&(_, count)| Reverse(count));
    for ((from, to), count) in ranked {
        println!("  {count:>6}  {from} -> {to}");
    }
}

pub fn largest(
    placed: &Graph,
    members: &BTreeMap<usize, usize>,
    instances: &Instances,
    normal: &Normal,
    placement: &[usize],
) {
    let moved = (0..instances.owner.len())
        .filter(|&index| placement[index] != normal.component_of[&instances.owner[index]])
        .count();
    println!(
        "Instances outside their owner's module: {moved} of {}",
        instances.owner.len()
    );
    let mut ranked: Vec<(&usize, &usize)> = members.iter().collect();
    ranked.sort_by_key(|&(_, count)| Reverse(*count));
    println!("Modules holding the most instances:");
    for (component, count) in ranked.into_iter().take(25) {
        println!("  {count:>6}  {}", placed.names[*component]);
    }
}

pub fn unplaced(unplaced: &Unplaced, instances: &Instances, normal: &Normal, names: &[String]) {
    let components = normal.names(names);
    println!(
        "No module reaches everything these {} instances need:",
        unplaced.instances.len()
    );
    for &index in &unplaced.instances {
        println!(
            "  {} (owner {})",
            instances.names[index], names[instances.owner[index]]
        );
    }
    println!("They need:");
    for &component in &unplaced.required {
        println!("  {}", components[component]);
    }
}
