use super::*;
use num::BigUint;
use serde::{Deserialize, Serialize};
use std::{
    collections::{HashMap, HashSet},
    error::Error,
    fs::File,
    io::{Read, Write},
    path::Path,
};

/// The work per bead if work is not passed
fn fixed_bead_work() -> Work {
    Work::from(1u32)
}

/// A DAG structure representing a braid
#[derive(Debug, Clone)]
pub struct Dag {
    /// Optional description of the DAG
    pub description: Option<String>,

    /// Map from bead to its parents
    pub parents: Relatives,

    /// Map from bead to its children
    pub children: Relatives,

    /// Set of genesis beads (beads with no parents)
    pub geneses: HashSet<BeadHash>,

    /// Set of tip beads (beads with no children)
    pub tips: HashSet<BeadHash>,

    /// List of cohorts in the DAG
    pub cohorts: Vec<HashSet<BeadHash>>,

    /// Map from bead to its work
    pub bead_work: HashMap<BeadHash, Work>,

    /// Map from bead to its cumulative work
    pub work: HashMap<BeadHash, Work>,

    /// Path with highest work through the DAG
    pub highest_work_path: Vec<BeadHash>,
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
        use serde::de::Error;
        use std::str::FromStr;

        // Helper function to convert string to BigUint
        fn parse_biguint<E: Error>(s: &str) -> Result<BigUint, E> {
            BigUint::from_str(s).map_err(|_| E::custom(format!("Failed to parse BigUint: {}", s)))
        }

        let value = serde_json::Value::deserialize(deserializer)?;

        // Parse description
        let description = value
            .get("description")
            .and_then(|v| v.as_str())
            .map(String::from);

        // Parse parents
        let mut parents = Relatives::new();
        if let Some(obj) = value.get("parents").and_then(|v| v.as_object()) {
            for (k, v) in obj {
                let bead = parse_biguint::<D::Error>(k)?;
                let mut parent_set = HashSet::new();

                if let Some(arr) = v.as_array() {
                    for p in arr {
                        if let Some(p_str) = p.as_str() {
                            parent_set.insert(parse_biguint::<D::Error>(p_str)?);
                        } else if let Some(p_num) = p.as_u64() {
                            parent_set.insert(BeadHash::from(p_num));
                        }
                    }
                }

                parents.insert(bead, parent_set);
            }
        }

        // Parse children
        let mut children = Relatives::new();
        if let Some(obj) = value.get("children").and_then(|v| v.as_object()) {
            for (k, v) in obj {
                let bead = parse_biguint::<D::Error>(k)?;
                let mut child_set = HashSet::new();

                if let Some(arr) = v.as_array() {
                    for c in arr {
                        if let Some(c_str) = c.as_str() {
                            child_set.insert(parse_biguint::<D::Error>(c_str)?);
                        } else if let Some(c_num) = c.as_u64() {
                            child_set.insert(BeadHash::from(c_num));
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
                if let Some(g_str) = g.as_str() {
                    geneses.insert(parse_biguint::<D::Error>(g_str)?);
                } else if let Some(g_num) = g.as_u64() {
                    geneses.insert(BeadHash::from(g_num));
                }
            }
        }

        // Parse tips
        let mut tips = HashSet::new();
        if let Some(arr) = value.get("tips").and_then(|v| v.as_array()) {
            for t in arr {
                if let Some(t_str) = t.as_str() {
                    tips.insert(parse_biguint::<D::Error>(t_str)?);
                } else if let Some(t_num) = t.as_u64() {
                    tips.insert(BeadHash::from(t_num));
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
                        if let Some(b_str) = b.as_str() {
                            cohort.insert(parse_biguint::<D::Error>(b_str)?);
                        } else if let Some(b_num) = b.as_u64() {
                            cohort.insert(BeadHash::from(b_num));
                        }
                    }
                }
                cohorts.push(cohort);
            }
        }

        // Parse bead_work
        let mut bead_work = HashMap::new();
        if let Some(obj) = value.get("bead_work").and_then(|v| v.as_object()) {
            for (k, v) in obj {
                let bead = parse_biguint::<D::Error>(k)?;
                let w = if let Some(v_str) = v.as_str() {
                    parse_biguint::<D::Error>(v_str)?
                } else if let Some(v_num) = v.as_u64() {
                    BeadHash::from(v_num)
                } else {
                    return Err(D::Error::custom(format!("Invalid work value: {:?}", v)));
                };
                bead_work.insert(bead, w);
            }
        } else {
            // Default to 1 work per bead
            for b in parents.keys() {
                bead_work.insert(b.clone(), fixed_bead_work());
            }
        }

        // Parse work
        let mut work = HashMap::new();
        if let Some(obj) = value.get("work").and_then(|v| v.as_object()) {
            for (k, v) in obj {
                let bead = parse_biguint::<D::Error>(k)?;
                let w = if let Some(v_str) = v.as_str() {
                    parse_biguint::<D::Error>(v_str)?
                } else if let Some(v_num) = v.as_u64() {
                    Work::from(v_num)
                } else {
                    return Err(D::Error::custom(format!("Invalid work value: {:?}", v)));
                };
                work.insert(bead, w);
            }
        }

        // Parse highest_work_path
        let mut highest_work_path = Vec::new();
        if let Some(arr) = value.get("highest_work_path").and_then(|v| v.as_array()) {
            for b in arr {
                if let Some(b_str) = b.as_str() {
                    highest_work_path.push(parse_biguint::<D::Error>(b_str)?);
                } else if let Some(b_num) = b.as_u64() {
                    highest_work_path.push(BeadHash::from(b_num));
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
}

/// Make a DAG object which caches the children, geneses, tips, cohorts, and highest work path
#[allow(dead_code)]
pub fn make_dag(
    hashed_parents: &Relatives,
    bead_work: Option<&HashMap<BeadHash, Work>>,
    description: Option<&str>,
) -> Dag {
    let parents = number_beads(hashed_parents);
    let children = reverse(&parents);
    let geneses = geneses(&parents);
    let tips = tips(&parents, Some(&children));
    let cohorts = cohorts(&parents, None, None);

    let bead_work = match bead_work {
        Some(bw) => bw.clone(),
        None => parents
            .keys()
            .map(|b| (b.clone(), fixed_bead_work()))
            .collect(),
    };

    let work = descendant_work(&parents, Some(&children), &bead_work, Some(&cohorts));
    let highest_work_path = highest_work_path(&parents, Some(&children), &bead_work);

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

/// Load a JSON file containing a braid
#[allow(dead_code)]
pub fn load_braid<P: AsRef<Path>>(filename: P) -> Result<Dag, Box<dyn Error>> {
    let mut file = File::open(filename)?;
    let mut contents = String::new();
    file.read_to_string(&mut contents)?;

    let dag: Dag = serde_json::from_str(&contents)?;
    Ok(dag)
}

/// Save a JSON file containing a braid
#[allow(dead_code)]
pub fn save_braid<P: AsRef<Path>>(
    parents: &Relatives,
    filename: P,
    description: Option<&str>,
) -> Result<Dag, Box<dyn Error>> {
    let dag = make_dag(parents, None, description);

    let mut result = serde_json::Map::new();
    result.insert(
        "description".to_string(),
        serde_json::Value::String(description.unwrap_or("").to_string()),
    );

    // Convert parents
    let mut parents_map = serde_json::Map::new();
    for (bead, parent_set) in &dag.parents {
        let bead_str = bead.to_string();
        let parents_array = serde_json::Value::Array(
            parent_set
                .iter()
                .map(|p| serde_json::Value::String(p.to_string()))
                .collect(),
        );
        parents_map.insert(bead_str, parents_array);
    }
    result.insert(
        "parents".to_string(),
        serde_json::Value::Object(parents_map),
    );

    // Convert children
    let mut children_map = serde_json::Map::new();
    for (bead, child_set) in &dag.children {
        let bead_str = bead.to_string();
        let children_array = serde_json::Value::Array(
            child_set
                .iter()
                .map(|c| serde_json::Value::String(c.to_string()))
                .collect(),
        );
        children_map.insert(bead_str, children_array);
    }
    result.insert(
        "children".to_string(),
        serde_json::Value::Object(children_map),
    );

    // Convert geneses
    let geneses_array = serde_json::Value::Array(
        dag.geneses
            .iter()
            .map(|g| serde_json::Value::String(g.to_string()))
            .collect(),
    );
    result.insert("geneses".to_string(), geneses_array);

    // Convert tips
    let tips_array = serde_json::Value::Array(
        dag.tips
            .iter()
            .map(|t| serde_json::Value::String(t.to_string()))
            .collect(),
    );
    result.insert("tips".to_string(), tips_array);

    // Convert cohorts
    let cohorts_array = serde_json::Value::Array(
        dag.cohorts
            .iter()
            .map(|cohort| {
                let mut sorted_cohort: Vec<_> = cohort.iter().collect();
                sorted_cohort.sort();
                serde_json::Value::Array(
                    sorted_cohort
                        .iter()
                        .map(|b| serde_json::Value::String(b.to_string()))
                        .collect(),
                )
            })
            .collect(),
    );
    result.insert("cohorts".to_string(), cohorts_array);

    // Convert bead_work
    let mut bead_work_map = serde_json::Map::new();
    for (bead, work) in &dag.bead_work {
        bead_work_map.insert(
            bead.to_string(),
            serde_json::Value::String(work.to_string()),
        );
    }
    result.insert(
        "bead_work".to_string(),
        serde_json::Value::Object(bead_work_map),
    );

    // Convert work
    let mut work_map = serde_json::Map::new();
    for (bead, work) in &dag.work {
        work_map.insert(
            bead.to_string(),
            serde_json::Value::String(work.to_string()),
        );
    }
    result.insert("work".to_string(), serde_json::Value::Object(work_map));

    // Convert highest_work_path
    let hwp_array = serde_json::Value::Array(
        dag.highest_work_path
            .iter()
            .map(|b| serde_json::Value::String(b.to_string()))
            .collect(),
    );
    result.insert("highest_work_path".to_string(), hwp_array);

    let json_string = serde_json::to_string_pretty(&serde_json::Value::Object(result))?;
    let mut file = File::create(filename)?;
    file.write_all(json_string.as_bytes())?;

    Ok(dag)
}

/// Check a cohort using check_cohort_ancestors in both directions
#[allow(dead_code)]
pub fn check_cohort(
    cohort: &HashSet<BeadHash>,
    parents: &Relatives,
    children: Option<&Relatives>,
) -> bool {
    let children = match children {
        Some(c) => c.clone(),
        None => reverse(parents),
    };

    check_cohort_ancestors(cohort, parents, Some(&children))
        && check_cohort_ancestors(cohort, &children, Some(parents))
}

/// Check a cohort by determining the set of ancestors of all beads
#[allow(dead_code)]
pub fn check_cohort_ancestors(
    cohort: &HashSet<BeadHash>,
    parents: &Relatives,
    children: Option<&Relatives>,
) -> bool {
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
