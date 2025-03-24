//! Braid data structure and algorithms
//!
//! This module provides tools for manipulating braids, which are directed acyclic graphs (DAGs)
//! where each node (bead) can have multiple parents and children.

use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::fs::File;
use std::io::{Read, Write};
use std::path::Path;
use std::str::FromStr;
use num::BigUint;
use serde::{Serialize, Deserialize};
use serde_json::{self, Value};

// Add serde support for BigUint
mod biguint_serde {
    use num::BigUint;
    use serde::{self, Serializer, Deserializer};
    use serde::de::{self, Visitor};
    use std::fmt;
    use std::str::FromStr;

    pub fn serialize<S>(biguint: &BigUint, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&biguint.to_string())
    }

    struct BigUintVisitor;

    impl<'de> Visitor<'de> for BigUintVisitor {
        type Value = BigUint;

        fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
            formatter.write_str("a string representing a BigUint")
        }

        fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
        where
            E: de::Error,
        {
            BigUint::from_str(value).map_err(|_| de::Error::custom("failed to parse BigUint"))
        }
    }

    pub fn deserialize<'de, D>(deserializer: D) -> Result<BigUint, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_str(BigUintVisitor)
    }
}

/// The work per bead if work is not passed
const FIXED_BEAD_WORK: u64 = 1;

/// A type alias for a map from bead to its parents
pub type Parents = HashMap<BigUint, HashSet<BigUint>>;

/// A type alias for a map from bead to its children
pub type Children = HashMap<BigUint, HashSet<BigUint>>;

/// A type alias for a map from bead to its work
pub type BeadWork = HashMap<BigUint, u64>;

/// A type alias for a cohort (set of beads)
pub type Cohort = HashSet<BigUint>;

/// A DAG structure representing a braid
#[derive(Debug, Clone)]
pub struct Dag {
    /// Optional description of the DAG
    pub description: Option<String>,

    /// Map from bead to its parents
    pub parents: Parents,

    /// Map from bead to its children
    pub children: Children,

    /// Set of genesis beads (beads with no parents)
    pub geneses: HashSet<BigUint>,

    /// Set of tip beads (beads with no children)
    pub tips: HashSet<BigUint>,

    /// List of cohorts in the DAG
    pub cohorts: Vec<Cohort>,

    /// Map from bead to its work
    pub bead_work: BeadWork,

    /// Map from bead to its cumulative work
    pub work: HashMap<BigUint, u64>,

    /// Path with highest work through the DAG
    pub highest_work_path: Vec<BigUint>,
}

// Implement Serialize and Deserialize for Dag
impl Serialize for Dag {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        use serde::ser::SerializeStruct;
        let mut state = serializer.serialize_struct("Dag", 9)?;
        state.serialize_field("description", &self.description)?;
        state.serialize_field("parents", &self.parents)?;
        state.serialize_field("children", &self.children)?;
        state.serialize_field("geneses", &self.geneses)?;
        state.serialize_field("tips", &self.tips)?;
        state.serialize_field("cohorts", &self.cohorts)?;
        state.serialize_field("bead_work", &self.bead_work)?;
        state.serialize_field("work", &self.work)?;
        state.serialize_field("highest_work_path", &self.highest_work_path)?;
        state.end()
    }
}

impl<'de> Deserialize<'de> for Dag {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        #[derive(Deserialize)]
        struct DagHelper {
            description: Option<String>,
            #[serde(with = "biguint_map_serde")]
            parents: Parents,
            #[serde(with = "biguint_map_serde")]
            children: Children,
            #[serde(with = "biguint_set_serde")]
            geneses: HashSet<BigUint>,
            #[serde(with = "biguint_set_serde")]
            tips: HashSet<BigUint>,
            #[serde(with = "biguint_cohorts_serde")]
            cohorts: Vec<Cohort>,
            #[serde(with = "biguint_work_serde")]
            bead_work: BeadWork,
            #[serde(with = "biguint_work_serde")]
            work: HashMap<BigUint, u64>,
            #[serde(with = "biguint_vec_serde")]
            highest_work_path: Vec<BigUint>,
        }

        let helper = DagHelper::deserialize(deserializer)?;
        Ok(Dag {
            description: helper.description,
            parents: helper.parents,
            children: helper.children,
            geneses: helper.geneses,
            tips: helper.tips,
            cohorts: helper.cohorts,
            bead_work: helper.bead_work,
            work: helper.work,
            highest_work_path: helper.highest_work_path,
        })
    }
}

// Serde modules for various BigUint collections
mod biguint_map_serde {
    use super::*;
    use serde::{Deserialize, Deserializer, Serializer};
    use std::collections::{HashMap, HashSet};

    pub fn serialize<S>(map: &HashMap<BigUint, HashSet<BigUint>>, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut string_map: HashMap<String, Vec<String>> = HashMap::new();
        for (k, v) in map {
            let key = k.to_string();
            let values: Vec<String> = v.iter().map(|b| b.to_string()).collect();
            string_map.insert(key, values);
        }
        string_map.serialize(serializer)
    }

    pub fn deserialize<'de, D>(deserializer: D) -> Result<HashMap<BigUint, HashSet<BigUint>>, D::Error>
    where
        D: Deserializer<'de>,
    {
        let string_map: HashMap<String, Vec<String>> = HashMap::deserialize(deserializer)?;
        let mut result = HashMap::new();
        for (k, v) in string_map {
            let key = BigUint::from_str(&k).map_err(serde::de::Error::custom)?;
            let mut values = HashSet::new();
            for val in v {
                let value = BigUint::from_str(&val).map_err(serde::de::Error::custom)?;
                values.insert(value);
            }
            result.insert(key, values);
        }
        Ok(result)
    }
}

mod biguint_set_serde {
    use super::*;
    use serde::{Deserialize, Deserializer, Serializer};
    use std::collections::HashSet;

    pub fn serialize<S>(set: &HashSet<BigUint>, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let string_set: Vec<String> = set.iter().map(|b| b.to_string()).collect();
        string_set.serialize(serializer)
    }

    pub fn deserialize<'de, D>(deserializer: D) -> Result<HashSet<BigUint>, D::Error>
    where
        D: Deserializer<'de>,
    {
        let string_vec: Vec<String> = Vec::deserialize(deserializer)?;
        let mut result = HashSet::new();
        for s in string_vec {
            let value = BigUint::from_str(&s).map_err(serde::de::Error::custom)?;
            result.insert(value);
        }
        Ok(result)
    }
}

mod biguint_cohorts_serde {
    use super::*;
    use serde::{Deserialize, Deserializer, Serializer};
    use std::collections::HashSet;

    pub fn serialize<S>(cohorts: &Vec<HashSet<BigUint>>, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let string_cohorts: Vec<Vec<String>> = cohorts
            .iter()
            .map(|cohort| cohort.iter().map(|b| b.to_string()).collect())
            .collect();
        string_cohorts.serialize(serializer)
    }

    pub fn deserialize<'de, D>(deserializer: D) -> Result<Vec<HashSet<BigUint>>, D::Error>
    where
        D: Deserializer<'de>,
    {
        let string_cohorts: Vec<Vec<String>> = Vec::deserialize(deserializer)?;
        let mut result = Vec::new();
        for string_cohort in string_cohorts {
            let mut cohort = HashSet::new();
            for s in string_cohort {
                let value = BigUint::from_str(&s).map_err(serde::de::Error::custom)?;
                cohort.insert(value);
            }
            result.push(cohort);
        }
        Ok(result)
    }
}

mod biguint_work_serde {
    use super::*;
    use serde::{Deserialize, Deserializer, Serializer};
    use std::collections::HashMap;

    pub fn serialize<S>(map: &HashMap<BigUint, u64>, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let string_map: HashMap<String, u64> = map
            .iter()
            .map(|(k, v)| (k.to_string(), *v))
            .collect();
        string_map.serialize(serializer)
    }

    pub fn deserialize<'de, D>(deserializer: D) -> Result<HashMap<BigUint, u64>, D::Error>
    where
        D: Deserializer<'de>,
    {
        let string_map: HashMap<String, u64> = HashMap::deserialize(deserializer)?;
        let mut result = HashMap::new();
        for (k, v) in string_map {
            let key = BigUint::from_str(&k).map_err(serde::de::Error::custom)?;
            result.insert(key, v);
        }
        Ok(result)
    }
}

mod biguint_vec_serde {
    use super::*;
    use serde::{Deserialize, Deserializer, Serializer};

    pub fn serialize<S>(vec: &Vec<BigUint>, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let string_vec: Vec<String> = vec.iter().map(|b| b.to_string()).collect();
        string_vec.serialize(serializer)
    }

    pub fn deserialize<'de, D>(deserializer: D) -> Result<Vec<BigUint>, D::Error>
    where
        D: Deserializer<'de>,
    {
        let string_vec: Vec<String> = Vec::deserialize(deserializer)?;
        let mut result = Vec::new();
        for s in string_vec {
            let value = BigUint::from_str(&s).map_err(serde::de::Error::custom)?;
            result.push(value);
        }
        Ok(result)
    }
}

/// Make a DAG object which caches the children, geneses, tips, cohorts, and highest work path
pub fn make_dag(hashed_parents: &Parents, bead_work: Option<&BeadWork>, description: Option<&str>) -> Dag {
    let parents = number_beads(hashed_parents);
    let children = reverse(&parents);
    let geneses = geneses(&parents);
    let tips = tips(&parents, Some(&children));
    let cohorts = cohorts(&parents, None, None);

    let bead_work = match bead_work {
        Some(bw) => bw.clone(),
        None => parents.keys().map(|b| (b.clone(), FIXED_BEAD_WORK)).collect(),
    };

    let work = descendant_work(&parents, Some(&children), Some(&bead_work), Some(&cohorts));
    let highest_work_path = highest_work_path(&parents, Some(&children), Some(&work), None);

    Dag {
        description: description.map(String::from),
        parents,
        children,
        geneses,
        tips,
        cohorts,
        bead_work,
        work,
        highest_work_path,
    }
}

/// Given a dict of {bead: {parents}}, return the set of beads which have no parents
pub fn geneses(parents: &Parents) -> HashSet<BigUint> {
    let mut retval = HashSet::new();
    for (b, p) in parents {
        if p.is_empty() {
            retval.insert(b.clone());
        }
    }
    retval
}

/// Given a dict of {bead: {parents}}, return the set of beads which have no children
pub fn tips(parents: &Parents, children: Option<&Children>) -> HashSet<BigUint> {
    let children_map = match children {
        Some(c) => c.clone(),
        None => reverse(parents),
    };
    geneses(&children_map)
}

/// Given a dict of {bead: {parents}}, compute the corresponding {bead: {children}} (or vice-versa)
pub fn reverse(parents: &Parents) -> Children {
    let mut children: Children = HashMap::new();

    for (bead, bparents) in parents {
        if !children.contains_key(bead) {
            children.insert(bead.clone(), HashSet::new());
        }

        for p in bparents {
            children.entry(p.clone()).or_insert_with(HashSet::new).insert(bead.clone());
        }
    }

    children
}

/// Given a set of beads, compute the set of all children of all beads
pub fn generation(beads: &HashSet<BigUint>, children: &Children) -> HashSet<BigUint> {
    let mut retval = HashSet::new();
    for b in beads {
        if let Some(child_set) = children.get(b) {
            for child in child_set {
                retval.insert(child.clone());
            }
        }
    }
    retval
}

/// Gets all ancestors for a bead, filling in ancestors of any other ancestors encountered
pub fn all_ancestors<'a>(b: &BigUint, parents: &Parents, ancestors: &'a mut HashMap<BigUint, HashSet<BigUint>>)
    -> &'a HashMap<BigUint, HashSet<BigUint>> {

    let mut work_stack = vec![(b.clone(), false)]; // (bead, is_processed)

    while !work_stack.is_empty() {
        let (current, is_processed) = work_stack.pop().unwrap();

        if is_processed {
            // We've finished processing all parents, compute ancestors
            let mut current_ancestors = HashSet::new();
            if let Some(current_parents) = parents.get(&current) {
                for p in current_parents {
                    current_ancestors.insert(p.clone());
                }

                // Update with ancestors of all parents
                for p in current_parents {
                    if let Some(parent_ancestors) = ancestors.get(p) {
                        for a in parent_ancestors {
                            current_ancestors.insert(a.clone());
                        }
                    }
                }
            }

            ancestors.insert(current, current_ancestors);
        } else {
            // Mark as being processed
            work_stack.push((current.clone(), true));

            // Add any unprocessed parents to the stack
            if let Some(current_parents) = parents.get(&current) {
                for p in current_parents {
                    if !ancestors.contains_key(p) {
                        work_stack.push((p.clone(), false));
                    }
                }
            }
        }
    }

    ancestors
}

/// Given the seed of the next cohort, build an ancestor/descendant set for each visited bead
pub fn cohorts(parents: &Parents, children: Option<&Children>, initial_cohort: Option<&HashSet<BigUint>>)
    -> Vec<HashSet<BigUint>> {

    let child_map = match children {
        Some(c) => c.clone(),
        None => reverse(parents),
    };

    let dag_tips = tips(parents, Some(&child_map));
    let mut cohort = match initial_cohort {
        Some(c) => c.clone(),
        None => geneses(parents),
    };

    let mut result = Vec::new();
    let mut oldcohort = HashSet::new();
    let mut head = cohort.clone();
    let mut tail = cohort.clone();

    'outer: loop {
        let mut ancestors: HashMap<BigUint, HashSet<BigUint>> = HashMap::new();
        for h in &head {
            ancestors.insert(h.clone(), HashSet::new()); // Don't let head have ancestors to stop iteration
        }

        cohort = head.clone(); // Initial cohort is the head

        'inner: loop {
            // Calculate new tail
            if head.is_empty() {
                break 'outer; // StopIteration and return
            }

            for b in cohort.difference(&oldcohort) {
                if let Some(children_set) = child_map.get(b) {
                    for child in children_set {
                        tail.insert(child.clone());
                    }
                }
            }

            // Add any beads in oldcohort but not in cohort
            for b in oldcohort.difference(&cohort) {
                tail.insert(b.clone());
            }

            // If there are any tips in cohort, add tips to tail
            let mut has_tips = false;
            for tip in &dag_tips {
                if cohort.contains(tip) {
                    has_tips = true;
                    break;
                }
            }

            if has_tips {
                for tip in &dag_tips {
                    if !cohort.contains(tip) {
                        tail.insert(tip.clone());
                    }
                }
            } else {
                // If there are no tips in cohort subtract off cohort
                tail = tail.difference(&cohort).cloned().collect();
            }

            oldcohort = cohort.clone(); // Copy so we can tell if new tail has changed anything

            // Calculate ancestors
            for t in &tail {
                if !ancestors.contains_key(t) {
                    all_ancestors(t, parents, &mut ancestors);
                }
            }

            // Calculate cohort
            cohort = HashSet::new();
            for (_, ancestor_set) in &ancestors {
                for a in ancestor_set {
                    cohort.insert(a.clone());
                }
            }

            // Check termination cases
            let all_tips_in_cohort = dag_tips.iter().all(|tip| cohort.contains(tip));

            if all_tips_in_cohort {
                // Cohort contains all tips
                head.clear(); // StopIteration and return
                break 'inner; // and yield the current cohort
            }

            let all_ancestors_match_cohort = !tail.is_empty() &&
                tail.iter().all(|t| {
                    ancestors.get(t).map_or(false, |a| *a == cohort)
                });

            if !cohort.is_empty() && all_ancestors_match_cohort {
                // Standard cohort case
                head = tail.clone(); // Head of next cohort is tail from previous iteration
                break 'inner; // Yield successful cohort
            }

            if cohort == oldcohort {
                // Cohort hasn't changed, we may be looping
                let all_tips_in_tail = dag_tips.iter().all(|tip| tail.contains(tip));

                if all_tips_in_tail {
                    // Tail contains all tips but we didn't form a cohort
                    head.clear();
                    for t in &tail {
                        cohort.insert(t.clone());
                    }
                    tail.clear();
                    break 'inner; // Yield cohort+tail
                }

                for t in &tail {
                    cohort.insert(t.clone());
                }
            }
        }

        if !cohort.is_empty() {
            result.push(cohort.clone());
        }

        oldcohort.clear();
    }

    result
}

/// Given a cohort as a set of beads, compute its tail
pub fn cohort_tail(cohort: &HashSet<BigUint>, parents: &Parents, children: Option<&Children>) -> HashSet<BigUint> {
    let children = match children {
        Some(c) => c,
        None => &reverse(parents),
    };

    cohort_head(cohort, &reverse(parents), Some(children))
}

/// Given a cohort as a set of beads, compute its head
pub fn cohort_head(cohort: &HashSet<BigUint>, parents: &Parents, children: Option<&Children>) -> HashSet<BigUint> {
    let children = match children {
        Some(c) => c,
        None => &reverse(parents),
    };

    let parent_gen = generation(cohort, parents);
    let parent_gen_minus_cohort: HashSet<_> = parent_gen.difference(cohort).cloned().collect();
    let tail = generation(&parent_gen_minus_cohort, children);

    let cohort_tips = geneses(parents);

    if tail.is_empty() || tail.iter().any(|t| cohort_tips.contains(t)) {
        return cohort_tips;
    }

    tail
}

/// Given a set of beads, return the sub-DAG corresponding to only those beads
pub fn sub_braid(beads: &HashSet<BigUint>, parents: &Parents) -> Parents {
    let mut result = Parents::new();

    for b in beads {
        let mut sub_parents = HashSet::new();
        if let Some(bparents) = parents.get(b) {
            for p in bparents {
                if beads.contains(p) {
                    sub_parents.insert(p.clone());
                }
            }
        }
        result.insert(b.clone(), sub_parents);
    }

    result
}

/// Find the work in descendants
pub fn descendant_work(
    parents: &Parents,
    children: Option<&Children>,
    bead_work: Option<&BeadWork>,
    in_cohorts: Option<&Vec<HashSet<BigUint>>>
) -> HashMap<BigUint, u64> {

    let child_map = match children {
        Some(c) => c.clone(),
        None => reverse(parents),
    };

    let bead_work = match bead_work {
        Some(bw) => bw.clone(),
        None => parents.keys().map(|b| (b.clone(), FIXED_BEAD_WORK)).collect(),
    };

    let mut previous_work = 0;
    let cohorts = match in_cohorts {
        Some(c) => c.iter().rev().cloned().collect::<Vec<_>>(),
        None => cohorts(parents, Some(&child_map), None),
    };

    let mut retval = HashMap::new(); // The cumulative work for each bead

    for c in cohorts {
        let sub_children = sub_braid(&c, &child_map);
        let mut sub_descendants = HashMap::new();

        for b in &c {
            all_ancestors(b, &sub_children, &mut sub_descendants);

            let mut b_work = previous_work + bead_work.get(b).cloned().unwrap_or(FIXED_BEAD_WORK);

            if let Some(descendants) = sub_descendants.get(b) {
                for a in descendants {
                    b_work += bead_work.get(a).cloned().unwrap_or(FIXED_BEAD_WORK);
                }
            }

            retval.insert(b.clone(), b_work);
        }

        // All beads in the next cohort have ALL beads in this cohort as descendants
        for b in &c {
            previous_work += bead_work.get(b).cloned().unwrap_or(FIXED_BEAD_WORK);
        }
    }

    retval
}

/// A custom comparison function for sorting beads
pub fn bead_cmp(a: &BigUint, b: &BigUint, dwork: &HashMap<BigUint, u64>, awork: Option<&HashMap<BigUint, u64>>) -> std::cmp::Ordering {
    let a_dwork = dwork.get(a).unwrap_or(&0);
    let b_dwork = dwork.get(b).unwrap_or(&0);

    if a_dwork < b_dwork {
        return std::cmp::Ordering::Less;
    }
    if a_dwork > b_dwork {
        return std::cmp::Ordering::Greater;
    }

    if let Some(awork) = awork {
        let a_awork = awork.get(a).unwrap_or(&0);
        let b_awork = awork.get(b).unwrap_or(&0);

        if a_awork < b_awork {
            return std::cmp::Ordering::Less;
        }
        if a_awork > b_awork {
            return std::cmp::Ordering::Greater;
        }
    }

    // Same work, fall back on lexical order
    a.cmp(b)
}

/// Return a sorting function for beads based on work
pub fn work_sort_key<'a>(
    parents: &'a Parents,
    children: Option<&'a Children>,
    bead_work: Option<&'a BeadWork>
) -> impl Fn(&BigUint, &BigUint) -> std::cmp::Ordering + 'a {

    let children = match children {
        Some(c) => c.clone(),
        None => reverse(parents),
    };

    let bead_work = match bead_work {
        Some(bw) => bw.clone(),
        None => parents.keys().map(|b| (b.clone(), FIXED_BEAD_WORK)).collect(),
    };

    let dwork = descendant_work(parents, Some(&children), Some(&bead_work), None);
    let awork = descendant_work(&children, Some(parents), Some(&bead_work), None);

    move |a, b| bead_cmp(a, b, &dwork, Some(&awork))
}

/// Find the highest (descendant) work path, by following the highest weights through the DAG
pub fn highest_work_path(
    parents: &Parents,
    children: Option<&Children>,
    work: Option<&HashMap<BigUint, u64>>,
    bead_work: Option<&BeadWork>
) -> Vec<BigUint> {

    let children = match children {
        Some(c) => c.clone(),
        None => reverse(parents),
    };

    let bead_work = match bead_work {
        Some(bw) => bw.clone(),
        None => parents.keys().map(|b| (b.clone(), FIXED_BEAD_WORK)).collect(),
    };

    let sort_key = work_sort_key(parents, Some(&children), Some(&bead_work));
    let genesis_beads = geneses(parents);

    // Find the genesis bead with maximum work
    let mut max_genesis = None;
    let mut max_work = 0;

    for bead in &genesis_beads {
        if let Some(work_map) = work {
            if let Some(&bead_work) = work_map.get(bead) {
                if max_genesis.is_none() || bead_work > max_work {
                    max_genesis = Some(bead.clone());
                    max_work = bead_work;
                }
            }
        } else {
            if max_genesis.is_none() || sort_key(bead, max_genesis.as_ref().unwrap()) == std::cmp::Ordering::Greater {
                max_genesis = Some(bead.clone());
            }
        }
    }

    let mut hwpath = vec![max_genesis.unwrap()];
    let dag_tips = tips(parents, Some(&children));

    while !dag_tips.contains(&hwpath[hwpath.len() - 1]) {
        let last_bead = hwpath[hwpath.len() - 1].clone();
        let mut next_gen = HashSet::new();
        next_gen.insert(last_bead);

        let children_set = generation(&next_gen, &children);

        // Find the child with maximum work
        let mut max_child = None;
        let mut max_child_work = 0;

        for child in &children_set {
            if let Some(work_map) = work {
                if let Some(&child_work) = work_map.get(child) {
                    if max_child.is_none() || child_work > max_child_work {
                        max_child = Some(child.clone());
                        max_child_work = child_work;
                    }
                }
            } else {
                if max_child.is_none() || sort_key(child, max_child.as_ref().unwrap()) == std::cmp::Ordering::Greater {
                    max_child = Some(child.clone());
                }
            }
        }

        hwpath.push(max_child.unwrap());
    }

    hwpath
}

/// Check a cohort using check_cohort_ancestors in both directions
pub fn check_cohort(cohort: &HashSet<BigUint>, parents: &Parents, children: Option<&Children>) -> bool {
    let children = match children {
        Some(c) => c.clone(),
        None => reverse(parents),
    };

    check_cohort_ancestors(cohort, parents, Some(&children)) &&
    check_cohort_ancestors(cohort, &children, Some(parents))
}

/// Check a cohort by determining the set of ancestors of all beads
pub fn check_cohort_ancestors(cohort: &HashSet<BigUint>, parents: &Parents, children: Option<&Children>) -> bool {
    let children = match children {
        Some(c) => c.clone(),
        None => reverse(parents),
    };

    let mut ancestors = HashMap::new();
    let mut allancestors = HashSet::new();
    let head = cohort_head(cohort, parents, Some(&children));

    for b in cohort {
        all_ancestors(b, parents, &mut ancestors);
        if let Some(b_ancestors) = ancestors.get(b) {
            for a in b_ancestors {
                if !cohort.contains(a) {
                    allancestors.insert(a.clone());
                }
            }
        }
    }

    if !allancestors.is_empty() {
        let gen = generation(&allancestors, &children);
        let gen_minus_allancestors: HashSet<_> = gen.difference(&allancestors).cloned().collect();

        if gen_minus_allancestors != head {
            return false;
        }
    }

    true
}

/// Number the beads in a braid sequentially in topological order starting at genesis
pub fn number_beads(hashed_parents: &Parents) -> Parents {
    let mut bead_id: u64 = 0;
    let mut parents = Parents::new();
    let mut bead_ids = HashMap::new();
    let mut reverse_bead_ids = HashMap::new();

    // First handle genesis beads
    for bead_hash in geneses(hashed_parents) {
        bead_ids.insert(bead_hash.clone(), BigUint::from(bead_id));
        reverse_bead_ids.insert(BigUint::from(bead_id), bead_hash);
        parents.insert(BigUint::from(bead_id), HashSet::new());
        bead_id += 1;
    }

    // Traverse the DAG in BFS in the descendant direction
    let hashed_children = reverse(hashed_parents);
    let mut next_parents = parents.clone();

    while !next_parents.is_empty() {
        let working_parents = next_parents.clone();
        next_parents = Parents::new();

        for (parent, _) in working_parents {
            if let Some(parent_hash) = reverse_bead_ids.get(&parent) {
                if let Some(children_set) = hashed_children.get(parent_hash) {
                    for bead_hash in children_set {
                        let this_id;

                        if let Some(id) = bead_ids.get(bead_hash) {
                            this_id = id.clone();
                        } else {
                            this_id = BigUint::from(bead_id);
                            bead_ids.insert(bead_hash.clone(), this_id.clone());
                            reverse_bead_ids.insert(this_id.clone(), bead_hash.clone());
                            bead_id += 1;
                        }

                        parents.entry(this_id.clone()).or_insert_with(HashSet::new).insert(parent.clone());
                        next_parents.entry(this_id).or_insert_with(HashSet::new).insert(parent.clone());
                    }
                }
            }
        }
    }

    parents
}

/// Load a JSON file containing a braid
pub fn load_braid<P: AsRef<Path>>(filename: P) -> Result<Dag, Box<dyn Error>> {
    let mut file = File::open(filename)?;
    let mut contents = String::new();
    file.read_to_string(&mut contents)?;

    let value: Value = serde_json::from_str(&contents)?;

    let description = value.get("description").and_then(|v| v.as_str()).map(String::from);

    // Parse parents
    let mut parents = Parents::new();
    if let Some(obj) = value.get("parents").and_then(|v| v.as_object()) {
        for (k, v) in obj {
            let bead = BigUint::from(k.parse::<u64>()?);
            let mut parent_set = HashSet::new();

            if let Some(arr) = v.as_array() {
                for p in arr {
                    if let Some(p_val) = p.as_u64() {
                        parent_set.insert(BigUint::from(p_val));
                    }
                }
            }

            parents.insert(bead, parent_set);
        }
    }

    // Parse children
    let mut children = Children::new();
    if let Some(obj) = value.get("children").and_then(|v| v.as_object()) {
        for (k, v) in obj {
            let bead = BigUint::from(k.parse::<u64>()?);
            let mut child_set = HashSet::new();

            if let Some(arr) = v.as_array() {
                for c in arr {
                    if let Some(c_val) = c.as_u64() {
                        child_set.insert(BigUint::from(c_val));
                    }
                }
            }

            children.insert(bead, child_set);
        }
    }

    // Parse geneses
    let mut geneses = HashSet::new();
    if let Some(arr) = value.get("geneses").and_then(|v| v.as_array()) {
        for g in arr {
            if let Some(g_val) = g.as_u64() {
                geneses.insert(BigUint::from(g_val));
            }
        }
    }

    // Parse tips
    let mut tips = HashSet::new();
    if let Some(arr) = value.get("tips").and_then(|v| v.as_array()) {
        for t in arr {
            if let Some(t_val) = t.as_u64() {
                tips.insert(BigUint::from(t_val));
            }
        }
    }

    // Parse cohorts
    let mut cohorts = Vec::new();
    if let Some(arr) = value.get("cohorts").and_then(|v| v.as_array()) {
        for c in arr {
            let mut cohort = HashSet::new();
            if let Some(c_arr) = c.as_array() {
                for b in c_arr {
                    if let Some(b_val) = b.as_u64() {
                        cohort.insert(BigUint::from(b_val));
                    }
                }
            }
            cohorts.push(cohort);
        }
    }

    // Parse bead_work
    let mut bead_work = BeadWork::new();
    if let Some(obj) = value.get("bead_work").and_then(|v| v.as_object()) {
        for (k, v) in obj {
            let bead = BigUint::from(k.parse::<u64>()?);
            if let Some(w) = v.as_u64() {
                bead_work.insert(bead, w);
            }
        }
    } else {
        // Default to 1 work per bead
        for b in parents.keys() {
            bead_work.insert(b.clone(), FIXED_BEAD_WORK);
        }
    }

    // Parse work
    let mut work = HashMap::new();
    if let Some(obj) = value.get("work").and_then(|v| v.as_object()) {
        for (k, v) in obj {
            let bead = BigUint::from(k.parse::<u64>()?);
            if let Some(w) = v.as_u64() {
                work.insert(bead, w);
            }
        }
    }

    // Parse highest_work_path
    let mut highest_work_path = Vec::new();
    if let Some(arr) = value.get("highest_work_path").and_then(|v| v.as_array()) {
        for b in arr {
            if let Some(b_val) = b.as_u64() {
                highest_work_path.push(BigUint::from(b_val));
            }
        }
    }

    Ok(Dag {
        description,
        parents,
        children,
        geneses,
        tips,
        cohorts,
        bead_work,
        work,
        highest_work_path,
    })
}

/// Save a JSON file containing a braid
pub fn save_braid<P: AsRef<Path>>(parents: &Parents, filename: P, description: Option<&str>) -> Result<Dag, Box<dyn Error>> {
    let dag = make_dag(parents, None, description);

    let mut result = serde_json::Map::new();
    result.insert("description".to_string(), serde_json::Value::String(description.unwrap_or("").to_string()));

    // Convert parents
    let mut parents_map = serde_json::Map::new();
    for (bead, parent_set) in &dag.parents {
        let bead_str = bead.to_string();
        let parents_array = serde_json::Value::Array(
            parent_set.iter().map(|p| serde_json::Value::String(p.to_string())).collect()
        );
        parents_map.insert(bead_str, parents_array);
    }
    result.insert("parents".to_string(), serde_json::Value::Object(parents_map));

    // Convert children
    let mut children_map = serde_json::Map::new();
    for (bead, child_set) in &dag.children {
        let bead_str = bead.to_string();
        let children_array = serde_json::Value::Array(
            child_set.iter().map(|c| serde_json::Value::String(c.to_string())).collect()
        );
        children_map.insert(bead_str, children_array);
    }
    result.insert("children".to_string(), serde_json::Value::Object(children_map));

    // Convert geneses
    let geneses_array = serde_json::Value::Array(
        dag.geneses.iter().map(|g| serde_json::Value::String(g.to_string())).collect()
    );
    result.insert("geneses".to_string(), geneses_array);

    // Convert tips
    let tips_array = serde_json::Value::Array(
        dag.tips.iter().map(|t| serde_json::Value::String(t.to_string())).collect()
    );
    result.insert("tips".to_string(), tips_array);

    // Convert cohorts
    let cohorts_array = serde_json::Value::Array(
        dag.cohorts.iter().map(|cohort| {
            let mut sorted_cohort: Vec<_> = cohort.iter().collect();
            sorted_cohort.sort();
            serde_json::Value::Array(
                sorted_cohort.iter().map(|b| serde_json::Value::String(b.to_string())).collect()
            )
        }).collect()
    );
    result.insert("cohorts".to_string(), cohorts_array);

    // Convert bead_work
    let mut bead_work_map = serde_json::Map::new();
    for (bead, work) in &dag.bead_work {
        let bead_str = bead.to_string();
        bead_work_map.insert(bead_str, serde_json::Value::Number(serde_json::Number::from(*work)));
    }
    result.insert("bead_work".to_string(), serde_json::Value::Object(bead_work_map));

    // Convert work
    let mut work_map = serde_json::Map::new();
    for (bead, work) in &dag.work {
        let bead_str = bead.to_string();
        work_map.insert(bead_str, serde_json::Value::Number(serde_json::Number::from(*work)));
    }
    result.insert("work".to_string(), serde_json::Value::Object(work_map));

    // Convert highest_work_path
    let hwp_array = serde_json::Value::Array(
        dag.highest_work_path.iter().map(|b| serde_json::Value::String(b.to_string())).collect()
    );
    result.insert("highest_work_path".to_string(), hwp_array);

    let json_string = serde_json::to_string_pretty(&serde_json::Value::Object(result))?;
    let mut file = File::create(filename)?;
    file.write_all(json_string.as_bytes())?;

    Ok(dag)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_geneses() {
        let parents1: Parents = [
            (BigUint::from(0u64), HashSet::new()),
            (BigUint::from(1u64), [BigUint::from(0u64)].iter().cloned().collect()),
            (BigUint::from(2u64), [BigUint::from(1u64)].iter().cloned().collect()),
            (BigUint::from(3u64), [BigUint::from(2u64)].iter().cloned().collect()),
        ].iter().cloned().collect();

        assert_eq!(geneses(&parents1), [BigUint::from(0u64)].iter().cloned().collect());

        let parents2: Parents = [
            (BigUint::from(0u64), HashSet::new()),
            (BigUint::from(1u64), HashSet::new()),
            (BigUint::from(2u64), [BigUint::from(1u64)].iter().cloned().collect()),
            (BigUint::from(3u64), [BigUint::from(1u64)].iter().cloned().collect()),
        ].iter().cloned().collect();

        assert_eq!(geneses(&parents2), [BigUint::from(0u64), BigUint::from(1u64)].iter().cloned().collect());
    }

    #[test]
    fn test_tips() {
        let parents1: Parents = [
            (BigUint::from(0u64), HashSet::new()),
            (BigUint::from(1u64), [BigUint::from(0u64)].iter().cloned().collect()),
            (BigUint::from(2u64), [BigUint::from(1u64)].iter().cloned().collect()),
            (BigUint::from(3u64), [BigUint::from(2u64)].iter().cloned().collect()),
        ].iter().cloned().collect();

        assert_eq!(tips(&parents1, None), [BigUint::from(3u64)].iter().cloned().collect());

        let parents2: Parents = [
            (BigUint::from(0u64), HashSet::new()),
            (BigUint::from(1u64), [BigUint::from(0u64)].iter().cloned().collect()),
            (BigUint::from(2u64), [BigUint::from(1u64)].iter().cloned().collect()),
            (BigUint::from(3u64), [BigUint::from(1u64)].iter().cloned().collect()),
        ].iter().cloned().collect();

        assert_eq!(tips(&parents2, None), [BigUint::from(2u64), BigUint::from(3u64)].iter().cloned().collect());
    }

    #[test]
    fn test_reverse() {
        let parents: Parents = [
            (BigUint::from(0u64), HashSet::new()),
            (BigUint::from(1u64), HashSet::new()),
            (BigUint::from(2u64), HashSet::new()),
            (BigUint::from(3u64), [BigUint::from(0u64), BigUint::from(1u64), BigUint::from(2u64)].iter().cloned().collect()),
            (BigUint::from(4u64), [BigUint::from(0u64), BigUint::from(1u64), BigUint::from(2u64)].iter().cloned().collect()),
            (BigUint::from(5u64), [BigUint::from(0u64), BigUint::from(1u64), BigUint::from(2u64)].iter().cloned().collect()),
        ].iter().cloned().collect();

        let expected: Children = [
            (BigUint::from(0u64), [BigUint::from(3u64), BigUint::from(4u64), BigUint::from(5u64)].iter().cloned().collect()),
            (BigUint::from(1u64), [BigUint::from(3u64), BigUint::from(4u64), BigUint::from(5u64)].iter().cloned().collect()),
            (BigUint::from(2u64), [BigUint::from(3u64), BigUint::from(4u64), BigUint::from(5u64)].iter().cloned().collect()),
            (BigUint::from(3u64), HashSet::new()),
            (BigUint::from(4u64), HashSet::new()),
            (BigUint::from(5u64), HashSet::new()),
        ].iter().cloned().collect();

        assert_eq!(reverse(&parents), expected);
    }

    #[test]
    fn test_cohorts() {
        let parents1: Parents = [
            (BigUint::from(0u64), HashSet::new()),
            (BigUint::from(1u64), [BigUint::from(0u64)].iter().cloned().collect()),
            (BigUint::from(2u64), [BigUint::from(1u64)].iter().cloned().collect()),
            (BigUint::from(3u64), [BigUint::from(2u64)].iter().cloned().collect()),
        ].iter().cloned().collect();

        let expected = vec![
            [BigUint::from(0u64)].iter().cloned().collect(),
            [BigUint::from(1u64)].iter().cloned().collect(),
            [BigUint::from(2u64)].iter().cloned().collect(),
            [BigUint::from(3u64)].iter().cloned().collect(),
        ];

        assert_eq!(cohorts(&parents1, None, None), expected);
    }

    #[test]
    fn test_highest_work_path() {
        let parents1: Parents = [
            (BigUint::from(0u64), HashSet::new()),
            (BigUint::from(1u64), [BigUint::from(0u64)].iter().cloned().collect()),
            (BigUint::from(2u64), [BigUint::from(1u64)].iter().cloned().collect()),
            (BigUint::from(3u64), [BigUint::from(2u64)].iter().cloned().collect()),
        ].iter().cloned().collect();

        let children1 = reverse(&parents1);

        let expected = vec![
            BigUint::from(0u64),
            BigUint::from(1u64),
            BigUint::from(2u64),
            BigUint::from(3u64),
        ];

        assert_eq!(highest_work_path(&parents1, Some(&children1), None, None), expected);
    }
}
