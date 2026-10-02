use std::collections::{BTreeMap, BTreeSet, HashMap};

use h2r_core_ir::{Module, split_stable_name};

pub struct Graph {
    pub names: Vec<String>,
    pub edges: BTreeMap<usize, BTreeSet<usize>>,
}

pub struct Normal {
    pub components: Vec<Vec<usize>>,
    pub component_of: BTreeMap<usize, usize>,
    pub condensed: Vec<BTreeSet<usize>>,
    pub reduced: Vec<BTreeSet<usize>>,
}

pub struct Instances {
    pub names: Vec<String>,
    pub owner: Vec<usize>,
    pub edges: BTreeMap<usize, BTreeSet<usize>>,
}

pub struct Unplaced {
    pub instances: Vec<usize>,
    pub required: Vec<usize>,
}

impl Graph {
    pub fn names(modules: &[Module]) -> Vec<String> {
        modules
            .iter()
            .map(|module| format!("{}:{}", module.unit, module.name))
            .collect()
    }

    pub fn of_references(modules: &[Module]) -> Graph {
        let index: HashMap<(&str, &str), usize> = modules
            .iter()
            .enumerate()
            .map(|(at, module)| ((module.unit.as_str(), module.name.as_str()), at))
            .collect();
        let edges = modules
            .iter()
            .enumerate()
            .map(|(at, module)| {
                let targets = module
                    .ids
                    .keys()
                    .filter_map(|name| split_stable_name(name))
                    .filter_map(|(unit, name, _)| index.get(&(unit, name)).copied())
                    .filter(|&target| target != at)
                    .collect();
                (at, targets)
            })
            .collect();
        Graph {
            names: Graph::names(modules),
            edges,
        }
    }

    pub fn edge_count(&self) -> usize {
        self.edges.values().map(BTreeSet::len).sum()
    }

    pub fn normalize(&self) -> Normal {
        let components = components(&self.edges);
        let component_of: BTreeMap<usize, usize> = components
            .iter()
            .enumerate()
            .flat_map(|(at, members)| members.iter().map(move |&member| (member, at)))
            .collect();
        let condensed: Vec<BTreeSet<usize>> = components
            .iter()
            .enumerate()
            .map(|(at, members)| {
                members
                    .iter()
                    .flat_map(|member| &self.edges[member])
                    .map(|target| component_of[target])
                    .filter(|&target| target != at)
                    .collect()
            })
            .collect();
        let mut reach: Vec<BTreeSet<usize>> = Vec::with_capacity(condensed.len());
        for targets in &condensed {
            let reached = targets
                .iter()
                .flat_map(|&target| std::iter::once(target).chain(reach[target].iter().copied()))
                .collect();
            reach.push(reached);
        }
        let reduced = condensed
            .iter()
            .map(|targets| {
                targets
                    .iter()
                    .copied()
                    .filter(|&target| {
                        !targets
                            .iter()
                            .any(|&other| other != target && reach[other].contains(&target))
                    })
                    .collect()
            })
            .collect();
        Normal {
            components,
            component_of,
            condensed,
            reduced,
        }
    }
}

impl Instances {
    pub fn by_owner(&self, names: Vec<String>) -> (Graph, BTreeMap<usize, usize>) {
        self.grouped(names, |index| self.owner[index])
    }

    pub fn by_placement(
        &self,
        names: Vec<String>,
        placement: &[usize],
    ) -> (Graph, BTreeMap<usize, usize>) {
        self.grouped(names, |index| placement[index])
    }

    fn grouped(
        &self,
        names: Vec<String>,
        group: impl Fn(usize) -> usize,
    ) -> (Graph, BTreeMap<usize, usize>) {
        let mut edges: BTreeMap<usize, BTreeSet<usize>> = BTreeMap::new();
        let mut members: BTreeMap<usize, usize> = BTreeMap::new();
        for (&index, targets) in &self.edges {
            let from = group(index);
            *members.entry(from).or_default() += 1;
            let reached = edges.entry(from).or_default();
            reached.extend(
                targets
                    .iter()
                    .map(|&target| group(target))
                    .filter(|&to| to != from),
            );
        }
        (Graph { names, edges }, members)
    }

    pub fn place(&self, modules: &Normal) -> Result<Vec<usize>, Unplaced> {
        let count = modules.components.len();
        let words = count.div_ceil(64);
        let mut reach: Vec<Vec<u64>> = Vec::with_capacity(count);
        for (component, targets) in modules.condensed.iter().enumerate() {
            let mut reached = vec![0u64; words];
            reached[component / 64] |= 1 << (component % 64);
            for &target in targets {
                for (word, below) in reached.iter_mut().zip(&reach[target]) {
                    *word |= below;
                }
            }
            reach.push(reached);
        }
        let mut placement = vec![usize::MAX; self.owner.len()];
        for group in components(&self.edges) {
            let mut required = vec![0u64; words];
            let mut require = |component: usize| required[component / 64] |= 1 << (component % 64);
            for &index in &group {
                require(modules.component_of[&self.owner[index]]);
                for &target in &self.edges[&index] {
                    if !group.contains(&target) {
                        require(placement[target]);
                    }
                }
            }
            let Some(home) = reach.iter().position(|reached| {
                reached
                    .iter()
                    .zip(&required)
                    .all(|(reached, required)| required & !reached == 0)
            }) else {
                return Err(Unplaced {
                    instances: group,
                    required: (0..count)
                        .filter(|&component| {
                            required[component / 64] & (1 << (component % 64)) != 0
                        })
                        .collect(),
                });
            };
            for &index in &group {
                placement[index] = home;
            }
        }
        Ok(placement)
    }
}

impl Normal {
    pub fn names(&self, names: &[String]) -> Vec<String> {
        self.components
            .iter()
            .map(|members| {
                let mut sorted: Vec<&str> = members.iter().map(|&m| names[m].as_str()).collect();
                sorted.sort_unstable();
                match sorted.as_slice() {
                    [single] => (*single).to_string(),
                    [first, ..] => format!("{first} (+{} modules)", sorted.len() - 1),
                    [] => String::new(),
                }
            })
            .collect()
    }

    pub fn depth(&self) -> usize {
        let mut longest: Vec<usize> = Vec::with_capacity(self.reduced.len());
        for targets in &self.reduced {
            let below = targets.iter().map(|&target| longest[target]).max();
            longest.push(below.map_or(1, |below| below + 1));
        }
        longest.into_iter().max().unwrap_or(0)
    }
}

pub(crate) fn components(edges: &BTreeMap<usize, BTreeSet<usize>>) -> Vec<Vec<usize>> {
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

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};

    use super::Graph;

    fn graph(edges: &[(usize, &[usize])]) -> Graph {
        Graph {
            names: (0..edges.len()).map(|at| at.to_string()).collect(),
            edges: edges
                .iter()
                .map(|(from, to)| (*from, to.iter().copied().collect::<BTreeSet<_>>()))
                .collect::<BTreeMap<_, _>>(),
        }
    }

    #[test]
    fn a_specialization_moves_to_the_lowest_module_that_reaches_its_callees() {
        let modules = graph(&[(0, &[]), (1, &[0]), (2, &[1]), (3, &[0, 2])]).normalize();
        let instances = super::Instances {
            names: vec!["i0".into(), "i1".into(), "i2".into()],
            owner: vec![0, 2, 3],
            edges: [
                (0, [1].into_iter().collect()),
                (1, BTreeSet::new()),
                (2, [0].into_iter().collect()),
            ]
            .into_iter()
            .collect(),
        };
        let Ok(placement) = instances.place(&modules) else {
            panic!("every instance has a module that reaches its callees");
        };
        assert_eq!(placement[1], modules.component_of[&2]);
        assert_eq!(placement[0], modules.component_of[&2]);
        assert_eq!(placement[2], modules.component_of[&3]);
    }

    #[test]
    fn a_cycle_is_one_component_and_a_shortcut_is_reduced_away() {
        let normal = graph(&[(0, &[1, 2]), (1, &[2]), (2, &[3]), (3, &[2])]).normalize();
        assert_eq!(normal.components.len(), 3);
        let cycle = normal.component_of[&2];
        assert_eq!(normal.component_of[&3], cycle);
        let top = normal.component_of[&0];
        let middle = normal.component_of[&1];
        assert_eq!(
            normal.condensed[top],
            [middle, cycle].into_iter().collect::<BTreeSet<_>>()
        );
        assert_eq!(normal.reduced[top], [middle].into_iter().collect());
        assert_eq!(normal.depth(), 3);
    }
}
