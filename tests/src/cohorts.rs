// src/cohorts.rs
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet, VecDeque};
use std::fs::File;
use std::io::{Read, Write};
use std::path::Path;

// Type aliases to make the code more readable
pub type Bead = i32;
pub type Parents = HashMap<Bead, HashSet<Bead>>;
pub type Children = HashMap<Bead, HashSet<Bead>>;

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq)]
pub struct Dag {
    pub description: Option<String>,
    #[serde(deserialize_with = "deserialize_parents")]
    pub parents: Parents,
    #[serde(deserialize_with = "deserialize_parents")]
    pub children: Children,
    #[serde(deserialize_with = "deserialize_cohorts")]
    pub cohorts: Vec<HashSet<Bead>>,
    #[serde(deserialize_with = "deserialize_set")]
    pub geneses: HashSet<Bead>,
    #[serde(deserialize_with = "deserialize_set")]
    pub tips: HashSet<Bead>,
    pub highest_work_path: Vec<Bead>,
}

impl Dag {
    pub fn new(parents: Parents, description: Option<String>) -> Self {
        let children = reverse(&parents);
        let cohorts = get_cohorts(&parents).collect();
        let geneses = get_geneses(&parents);
        let tips = get_geneses(&children);
        let highest_work_path = highest_work_path(&parents, &children);

        Dag {
            description,
            parents,
            children,
            cohorts,
            geneses,
            tips,
            highest_work_path,
        }
    }

    pub fn load(path: impl AsRef<Path>) -> std::io::Result<Self> {
        let mut file = File::open(path)?;
        let mut contents = String::new();
        file.read_to_string(&mut contents)?;
        Ok(serde_json::from_str(&contents)?)
    }

    pub fn save(&self, path: impl AsRef<Path>) -> std::io::Result<()> {
        let json = serde_json::to_string_pretty(&self)?;
        let mut file = File::create(path)?;
        file.write_all(json.as_bytes())?;
        Ok(())
    }
}

struct CohortsIterator {
    dag: HashMap<String, HashMap<Bead, HashSet<Bead>>>,
    cohort: HashSet<Bead>,
    old_cohort: HashSet<Bead>,
    head: HashSet<Bead>,
    tail: HashSet<Bead>,
}

// Custom deserializers for JSON format compatibility
fn deserialize_parents<'de, D>(deserializer: D) -> Result<HashMap<Bead, HashSet<Bead>>, D::Error>
where
    D: serde::Deserializer<'de>,
{
    let map: HashMap<String, Vec<Bead>> = HashMap::deserialize(deserializer)?;
    Ok(map
        .into_iter()
        .map(|(k, v)| (k.parse::<Bead>().unwrap(), v.into_iter().collect()))
        .collect())
}

fn deserialize_cohorts<'de, D>(deserializer: D) -> Result<Vec<HashSet<Bead>>, D::Error>
where
    D: serde::Deserializer<'de>,
{
    let vec: Vec<Vec<Bead>> = Vec::deserialize(deserializer)?;
    Ok(vec.into_iter().map(|v| v.into_iter().collect()).collect())
}

fn deserialize_set<'de, D>(deserializer: D) -> Result<HashSet<Bead>, D::Error>
where
    D: serde::Deserializer<'de>,
{
    let vec: Vec<Bead> = Vec::deserialize(deserializer)?;
    Ok(vec.into_iter().collect())
}

pub fn get_geneses(parents: &Parents) -> HashSet<Bead> {
    parents
        .iter()
        .filter(|(_, p)| p.is_empty())
        .map(|(b, _)| *b)
        .collect()
}

pub fn get_tips(parents: &Parents) -> HashSet<Bead> {
    get_geneses(&reverse(parents))
}

pub fn reverse(parents: &Parents) -> Children {
    let mut children: Children = HashMap::new();

    for (&bead, bparents) in parents.iter() {
        children.entry(bead).or_insert_with(HashSet::new);

        for &p in bparents {
            children.entry(p).or_insert_with(HashSet::new).insert(bead);
        }
    }
    children
}

fn generation(beads: &HashSet<Bead>, map: &HashMap<Bead, HashSet<Bead>>) -> HashSet<Bead> {
    if beads.is_empty() {
        return HashSet::new();
    }
    let mut result = HashSet::new();
    for &b in beads {
        if let Some(set) = map.get(&b) {
            result.extend(set);
        }
    }
    result
}

fn get_all_ancestors(b: Bead, parents: &Parents, ancestors: &mut HashMap<Bead, HashSet<Bead>>) {
    if !ancestors.contains_key(&b) {
        // Get parent beads first
        let parent_beads = parents.get(&b).cloned().unwrap_or_default();

        // Create initial ancestor set with just parents
        let mut b_ancestors = parent_beads.clone();

        // Process each parent's ancestors
        for p in parent_beads {
            if !ancestors.contains_key(&p) {
                get_all_ancestors(p, parents, ancestors);
            }
            if let Some(p_ancestors) = ancestors.get(&p) {
                b_ancestors.extend(p_ancestors);
            }
        }

        // Insert the complete ancestor set
        ancestors.insert(b, b_ancestors);
    }
}

impl CohortsIterator {
    pub fn new(parents: &Parents) -> Self {
        let children = reverse(parents);
        let initial_cohort = get_geneses(parents);

        let mut dag = HashMap::new();
        dag.insert("parents".to_string(), parents.clone());
        dag.insert("children".to_string(), children);

        CohortsIterator {
            dag,
            cohort: initial_cohort.clone(),
            old_cohort: HashSet::new(),
            head: initial_cohort.clone(),
            tail: initial_cohort,
        }
    }
}

impl Iterator for CohortsIterator {
    type Item = HashSet<Bead>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.head.is_empty() {
            return None;
        }

        let parents = self.dag.get("parents").unwrap();
        let children = self.dag.get("children").unwrap();
        let tips = get_tips(parents);

        let mut ancestors: HashMap<Bead, HashSet<Bead>> =
            self.head.iter().map(|&h| (h, HashSet::new())).collect();

        self.cohort = self.head.clone();

        loop {
            // Calculate new tail
            let mut new_tail = HashSet::new();
            for b in self.cohort.difference(&self.old_cohort) {
                if let Some(b_children) = children.get(b) {
                    new_tail.extend(b_children.iter().copied());
                }
            }

            // Add any beads in the oldcohort but not in the new cohort
            new_tail.extend(self.cohort.symmetric_difference(&self.old_cohort));

            // Handle tips in cohort
            if !self.cohort.is_disjoint(&tips) {
                // If there are tips in cohort, add remaining tips
                new_tail.extend(tips.difference(&self.cohort));
            } else {
                // If there are no tips in the cohort subtract off the cohort
                new_tail = &new_tail - &self.cohort;
            }

            self.tail = new_tail;
            self.old_cohort = self.cohort.clone();

            // Calculate ancestors
            for &t in &self.tail {
                if !ancestors.contains_key(&t) {
                    get_all_ancestors(t, parents, &mut ancestors);
                }
            }

            // Calculate cohort
            let mut new_cohort = HashSet::new();
            for (_, ancestor_set) in &ancestors {
                new_cohort.extend(ancestor_set);
            }
            self.cohort = new_cohort;

            // Check termination cases
            if tips.is_subset(&self.cohort) {
                // Cohort contains all tips
                self.head.clear();
                break;
            } else if !self.cohort.is_empty()
                && self
                    .tail
                    .iter()
                    .all(|t| ancestors.get(t).map_or(false, |a| a == &self.cohort))
            {
                // Standard cohort case
                self.head = self.tail.clone();
                break;
            } else if self.cohort == self.old_cohort {
                // Cohort hasn't changed, we may be looping
                if tips.is_subset(&self.tail) {
                    self.head.clear();
                    self.cohort.extend(&self.tail);
                    self.tail.clear();
                    break;
                } else {
                    self.cohort.extend(&self.tail);
                }
            }
        }

        self.old_cohort.clear();
        Some(self.cohort.clone())
    }
}

pub fn get_cohorts(parents: &Parents) -> impl Iterator<Item = HashSet<Bead>> + '_ {
    let children = reverse(parents);
    let initial_cohort = get_geneses(parents);
    let dag = DagInfo {
        parents: parents.clone(),
        children: children.clone(),
        tips: get_geneses(&children),
    };

    std::iter::from_fn(move || {
        static mut COHORT: Option<HashSet<Bead>> = None;
        static mut HEAD: Option<HashSet<Bead>> = None;

        // Initialize state if first iteration
        unsafe {
            if COHORT.is_none() {
                COHORT = Some(initial_cohort.clone());
                HEAD = Some(initial_cohort.clone());
            }

            let head = HEAD.as_mut()?;
            if head.is_empty() {
                return None;
            }

            let mut tail = head.clone();
            let mut cohort = head.clone();
            let mut old_cohort = HashSet::new();

            while !head.is_empty() {
                let mut ancestors: HashMap<Bead, HashSet<Bead>> =
                    head.iter().map(|&h| (h, HashSet::new())).collect();

                cohort = head.clone();

                // Inner loop (DFS search)
                loop {
                    // Calculate new tail
                    for b in cohort.difference(&old_cohort) {
                        if let Some(children_set) = dag.children.get(b) {
                            tail.extend(children_set);
                        }
                    }
                    tail.extend(cohort.symmetric_difference(&old_cohort));

                    if !cohort.is_disjoint(&dag.tips) {
                        tail.extend(dag.tips.difference(&cohort));
                    } else {
                        tail = tail.difference(&cohort).copied().collect();
                    }

                    old_cohort = cohort.clone();

                    // Calculate ancestors
                    for &t in &tail {
                        if !ancestors.contains_key(&t) {
                            get_all_ancestors(t, &dag.parents, &mut ancestors);
                        }
                    }

                    // Calculate cohort
                    let mut new_cohort = HashSet::new();
                    for ancestors_set in ancestors.values() {
                        new_cohort.extend(ancestors_set);
                    }
                    cohort = new_cohort;

                    // Check termination cases
                    if dag.tips.is_subset(&cohort) {
                        head.clear();
                        break;
                    } else if !cohort.is_empty()
                        && tail
                            .iter()
                            .all(|t| ancestors.get(t).map_or(false, |a| *a == cohort))
                    {
                        *head = tail.clone();
                        break;
                    } else if cohort == old_cohort {
                        if dag.tips.is_subset(&tail) {
                            head.clear();
                            cohort.extend(&tail);
                            break;
                        } else {
                            cohort.extend(&tail);
                        }
                    }
                }

                if head.is_empty() {
                    COHORT = None;
                    HEAD = None;
                }

                return Some(cohort);
            }

            None
        }
    })
}

pub fn highest_work_path(parents: &Parents, children: &Children) -> Vec<Bead> {
    let mut hwpath = Vec::new();
    let work = 1; // work per bead

    // Get cohorts iterator once and collect it so we process each cohort exactly once
    let cohorts: Vec<_> = get_cohorts(parents).collect();

    for c in cohorts {
        let head = cohort_head(&c, parents, children);
        let tail = cohort_tail(&c, parents, children);

        // Special case: if head equals tail, just take one bead from the cohort
        if head == tail {
            if let Some(&bead) = c.iter().next() {
                hwpath.push(bead);
                continue;
            }
        }

        // Initialize queue with union of all children of head beads
        let mut queue = VecDeque::new();
        for h in &head {
            if let Some(h_children) = children.get(h) {
                queue.extend(h_children.iter().copied());
            }
        }

        // Initialize weights for head beads
        let mut weights: HashMap<Bead, i32> = head.iter().map(|&h| (h, work)).collect();

        // Build weights dict
        while let Some(b) = queue.pop_front() {
            if !weights.contains_key(&b) {
                let cparents = generation(&HashSet::from([b]), parents);
                let missing_parents: Vec<_> = cparents
                    .iter()
                    .filter(|&p| !weights.contains_key(p))
                    .copied()
                    .collect();

                if !missing_parents.is_empty() {
                    // If any parents are missing weights, process them first
                    queue.extend(missing_parents);
                    continue;
                } else {
                    // Calculate weight for current bead
                    let weight = work + cparents.iter().map(|p| weights[p]).sum::<i32>();
                    weights.insert(b, weight);

                    // Add children to left of queue (equivalent to extendleft in Python)
                    if let Some(b_children) = children.get(&b) {
                        for &child in b_children {
                            queue.push_front(child);
                        }
                    }
                }
            }
        }

        // Follow highest weights from tail to head
        if !tail.is_empty() {
            // Find starting bead in tail with highest weight
            let mut current = *tail
                .iter()
                .max_by_key(|&&x| weights.get(&x).unwrap_or(&0))
                .unwrap();

            let mut chwpath = vec![current];

            // Follow path to head
            while !head.contains(&current) {
                let next = generation(&HashSet::from([current]), parents)
                    .iter()
                    .max_by_key(|&&x| weights.get(&x).unwrap_or(&0))
                    .copied()
                    .unwrap();
                chwpath.push(next);
                current = next;
            }

            // Add reversed path to hwpath
            hwpath.extend(chwpath.into_iter().rev());
        }
    }

    hwpath
}

pub fn cohort_head(
    cohort: &HashSet<Bead>,
    parents: &Parents,
    children: &Children,
) -> HashSet<Bead> {
    cohort_headtail(cohort, parents, children)
}

pub fn cohort_tail(
    cohort: &HashSet<Bead>,
    parents: &Parents,
    children: &Children,
) -> HashSet<Bead> {
    cohort_headtail(cohort, children, parents)
}

pub fn cohort_headtail(
    cohort: &HashSet<Bead>,
    parents: &Parents,
    children: &Children,
) -> HashSet<Bead> {
    let gen1 = generation(&generation(cohort, parents), children);
    let diff: HashSet<_> = gen1.difference(cohort).copied().collect();
    let tips = get_geneses(parents);

    if diff.is_empty() || diff.iter().any(|t| tips.contains(t)) {
        tips
    } else {
        diff
    }
}

pub fn load_braid(filename: &str) -> std::io::Result<Dag> {
    let mut file = File::open(filename)?;
    let mut contents = String::new();
    file.read_to_string(&mut contents)?;
    Ok(serde_json::from_str(&contents)?)
}

pub fn save_braid(
    parents: &Parents,
    filename: &str,
    description: Option<String>,
) -> std::io::Result<()> {
    let dag = Dag::new(parents.clone(), description);
    let json = serde_json::to_string_pretty(&dag)?;
    let mut file = File::create(filename)?;
    file.write_all(json.as_bytes())?;
    Ok(())
}
