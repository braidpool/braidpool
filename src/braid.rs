use serde::{Deserialize, Serialize};
use serde_json;
use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use std::fs::File;
use std::io::{Read, Write};
//use bitcoin_hashes::sha256d::Hash;
type Bead = i32; // bitcoin_hashes::sha256d::Hash; // Not serializable
type Relatives = HashMap<Bead, HashSet<Bead>>; // either parents or children

struct BraidInfo {
    description: Option<String>,
    children: Relatives,
    cohorts: Vec<HashSet<Bead>>,
    geneses: HashSet<Bead>,
    tips: HashSet<Bead>,
    highest_work_path: Vec<Bead>,
}

#[derive(Serialize, Deserialize, Debug)]
struct Braid {
    parents: Relatives,
    info: Option<BraidInfo>,
}

impl Braid {
    fn new(parents: Relatives, description: Option<String>) -> Self {
        let children = reverse(parents);
        let cohorts = self.cohorts().collect();
        let geneses = self.geneses();
        let tips = self.geneses();
        let highest_work_path = self.highest_work_path();
        let self = Braid { parents, None };
        let info = BraidInfo;

        Braid { parents, None }
    }

    // File I/O functions
    fn load(filename: &str) -> std::io::Result<Braid> {
        let mut file = File::open(filename)?;
        let mut contents = String::new();
        file.read_to_string(&mut contents)?;
        Ok(serde_json::from_str(&contents)?)
    }

    fn save(&self, filename: &str, description: Option<String>) -> std::io::Result<()> {
        let dag = Braid::new(self.parents.clone(), description);
        let json = serde_json::to_string_pretty(&dag)?;
        let mut file = File::create(filename)?;
        file.write_all(json.as_bytes())?;
        Ok(())
    }

    fn generation(&self, beads: &HashSet<Bead>, children: &Relatives) -> HashSet<Bead> {
        if beads.is_empty() {
            return HashSet::new();
        }

        beads
            .iter()
            .flat_map(|b| children.get(b).unwrap_or(&HashSet::new()))
            .copied()
            .collect()
    }

    fn all_ancestors(
        &self,
        b: Bead,
        parents: &Relatives,
        ancestors: &mut HashMap<Bead, HashSet<Bead>>,
    ) {
        if !ancestors.contains_key(&b) {
            let parent_beads = parents.get(&b).cloned().unwrap_or_default();
            let mut b_ancestors = parent_beads.clone();

            for p in parent_beads {
                if !ancestors.contains_key(&p) {
                    self.all_ancestors(p, parents, ancestors);
                }
                if let Some(p_ancestors) = ancestors.get(&p) {
                    b_ancestors.extend(p_ancestors);
                }
            }

            ancestors.insert(b, b_ancestors);
        }
    }

    fn cohort_head(
        &self,
        cohort: &HashSet<Bead>,
        parents: &Relatives,
        children: &Relatives,
    ) -> HashSet<Bead> {
        self.cohort_headtail(cohort, parents, children)
    }

    fn cohort_tail(
        &self,
        cohort: &HashSet<Bead>,
        parents: &Relatives,
        children: &Relatives,
    ) -> HashSet<Bead> {
        self.cohort_headtail(cohort, children, parents)
    }

    fn cohort_headtail(
        &self,
        cohort: &HashSet<Bead>,
        parents: &Relatives,
        children: &Relatives,
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

    pub fn cohorts(&self) -> impl Iterator<Item = HashSet<Bead>> + '_ {}

    fn highest_work_path(&self) -> Vec<Bead> {}
}

fn reverse(parents: &Relatives) -> Relatives {
    let mut children: Relatives = HashMap::new();

    for (&bead, bparents) in parents.iter() {
        children.entry(bead).or_insert_with(HashSet::new);

        for &p in bparents {
            children.entry(p).or_insert_with(HashSet::new).insert(bead);
        }
    }
    children
}

fn geneses(&parents: &Relatives) -> HashSet<Bead> {
    parents
        .iter()
        .filter(|(_, p)| p.is_empty())
        .map(|(b, _)| *b)
        .collect()
}

fn tips(&parents: &Relatives) -> HashSet<Bead> {
    reverse(parents)
        .iter()
        .filter(|(_, p)| p.is_empty())
        .map(|(b, _)| *b)
        .collect()
}
