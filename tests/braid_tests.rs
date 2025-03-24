use std::collections::{HashMap, HashSet};
use std::fs;
use std::fs::{File};
use std::error::Error;
use num::BigUint;
use braidpool::*;
use braidpool::braid::*; //{self, BeadWork, Cohort, Relatives};
use serde::{Serialize, Deserialize};
use serde_json::{self, Value};
use std::path::Path;
use std::str::FromStr;
use std::io::{Read, Write};

const TEST_CASE_DIR: &str = "tests/braids/";

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
            parents: Relatives,
            #[serde(with = "biguint_map_serde")]
            children: Relatives,
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
pub fn make_dag(hashed_parents: &Relatives, bead_work: Option<&BeadWork>, description: Option<&str>) -> Dag {
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
    let highest_work_path = highest_work_path(&parents, Some(&children), Some(&bead_work));

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
pub fn load_braid<P: AsRef<Path>>(filename: P) -> Result<Dag, Box<dyn Error>> {
    let mut file = File::open(filename)?;
    let mut contents = String::new();
    file.read_to_string(&mut contents)?;

    let value: Value = serde_json::from_str(&contents)?;

    let description = value.get("description").and_then(|v| v.as_str()).map(String::from);

    // Parse parents
    let mut parents = Relatives::new();
    if let Some(obj) = value.get("parents").and_then(|v| v.as_object()) {
        for (k, v) in obj {
            let bead = BigUint::from_str(k)?;
            let mut parent_set = HashSet::new();

            if let Some(arr) = v.as_array() {
                for p in arr {
                    if let Some(p_str) = p.as_str() {
                        parent_set.insert(BigUint::from_str(p_str)?);
                    } else if let Some(p_num) = p.as_u64() {
                        parent_set.insert(BigUint::from(p_num));
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
            let bead = BigUint::from_str(k)?;
            let mut child_set = HashSet::new();

            if let Some(arr) = v.as_array() {
                for c in arr {
                    if let Some(c_str) = c.as_str() {
                        child_set.insert(BigUint::from_str(c_str)?);
                    } else if let Some(c_num) = c.as_u64() {
                        child_set.insert(BigUint::from(c_num));
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
                geneses.insert(BigUint::from_str(g_str)?);
            } else if let Some(g_num) = g.as_u64() {
                geneses.insert(BigUint::from(g_num));
            }
        }
    }

    // Parse tips
    let mut tips = HashSet::new();
    if let Some(arr) = value.get("tips").and_then(|v| v.as_array()) {
        for t in arr {
            if let Some(t_str) = t.as_str() {
                tips.insert(BigUint::from_str(t_str)?);
            } else if let Some(t_num) = t.as_u64() {
                tips.insert(BigUint::from(t_num));
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
                        cohort.insert(BigUint::from_str(b_str)?);
                    } else if let Some(b_num) = b.as_u64() {
                        cohort.insert(BigUint::from(b_num));
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
            if let Some(b_str) = b.as_str() {
                highest_work_path.push(BigUint::from_str(b_str)?);
            } else if let Some(b_num) = b.as_u64() {
                highest_work_path.push(BigUint::from(b_num));
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
pub fn save_braid<P: AsRef<Path>>(parents: &Relatives, filename: P, description: Option<&str>) -> Result<Dag, Box<dyn Error>> {
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


#[test]
fn test_geneses1() {
    let parents1: Relatives = [
        (BigUint::from(0u64), HashSet::new()),
        (BigUint::from(1u64), [BigUint::from(0u64)].iter().cloned().collect()),
        (BigUint::from(2u64), [BigUint::from(1u64)].iter().cloned().collect()),
        (BigUint::from(3u64), [BigUint::from(2u64)].iter().cloned().collect()),
    ].iter().cloned().collect();

    assert_eq!(braid::geneses(&parents1), [BigUint::from(0u64)].iter().cloned().collect::<HashSet<_>>());
}

#[test]
fn test_geneses2() {
    let parents2: Relatives = [
        (BigUint::from(0u64), HashSet::new()),
        (BigUint::from(1u64), HashSet::new()),
        (BigUint::from(2u64), [BigUint::from(1u64)].iter().cloned().collect()),
        (BigUint::from(3u64), [BigUint::from(1u64)].iter().cloned().collect()),
    ].iter().cloned().collect();

    assert_eq!(braid::geneses(&parents2), [BigUint::from(0u64), BigUint::from(1u64)].iter().cloned().collect::<HashSet<_>>());
}

#[test]
fn test_geneses3() {
    let parents3: Relatives = [
        (BigUint::from(0u64), HashSet::new()),
        (BigUint::from(1u64), HashSet::new()),
        (BigUint::from(2u64), HashSet::new()),
        (BigUint::from(3u64), [BigUint::from(1u64)].iter().cloned().collect()),
        (BigUint::from(4u64), [BigUint::from(0u64)].iter().cloned().collect()),
    ].iter().cloned().collect();

    assert_eq!(braid::geneses(&parents3), [BigUint::from(0u64), BigUint::from(1u64), BigUint::from(2u64)].iter().cloned().collect::<HashSet<_>>());
}

#[test]
fn test_geneses_files() {
    for entry in fs::read_dir(TEST_CASE_DIR).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();

        if path.extension().map_or(false, |ext| ext == "json") {
            let path_str = path.to_string_lossy();
            let dag = load_braid(&path).unwrap();
            assert_eq!(
                braid::geneses(&dag.parents),
                [BigUint::from(0u64)].iter().cloned().collect::<HashSet<_>>(),
                "Failed on file: {}", path_str
            );
        }
    }
}

#[test]
fn test_tips1() {
    let parents1: Relatives = [
        (BigUint::from(0u64), HashSet::new()),
        (BigUint::from(1u64), [BigUint::from(0u64)].iter().cloned().collect()),
        (BigUint::from(2u64), [BigUint::from(1u64)].iter().cloned().collect()),
        (BigUint::from(3u64), [BigUint::from(2u64)].iter().cloned().collect()),
    ].iter().cloned().collect();

    assert_eq!(braid::tips(&parents1, None), [BigUint::from(3u64)].iter().cloned().collect::<HashSet<_>>());
}

#[test]
fn test_tips2() {
    let parents2: Relatives = [
        (BigUint::from(0u64), HashSet::new()),
        (BigUint::from(1u64), [BigUint::from(0u64)].iter().cloned().collect()),
        (BigUint::from(2u64), [BigUint::from(1u64)].iter().cloned().collect()),
        (BigUint::from(3u64), [BigUint::from(1u64)].iter().cloned().collect()),
    ].iter().cloned().collect();

    assert_eq!(braid::tips(&parents2, None), [BigUint::from(2u64), BigUint::from(3u64)].iter().cloned().collect::<HashSet<_>>());
}

#[test]
fn test_tips3() {
    let parents3: Relatives = [
        (BigUint::from(0u64), HashSet::new()),
        (BigUint::from(1u64), HashSet::new()),
        (BigUint::from(2u64), HashSet::new()),
        (BigUint::from(3u64), [BigUint::from(0u64), BigUint::from(1u64), BigUint::from(2u64)].iter().cloned().collect()),
        (BigUint::from(4u64), [BigUint::from(0u64), BigUint::from(1u64), BigUint::from(2u64)].iter().cloned().collect()),
        (BigUint::from(5u64), [BigUint::from(0u64), BigUint::from(1u64), BigUint::from(2u64)].iter().cloned().collect()),
    ].iter().cloned().collect();

    assert_eq!(braid::tips(&parents3, None), [BigUint::from(3u64), BigUint::from(4u64), BigUint::from(5u64)].iter().cloned().collect::<HashSet<_>>());
}

#[test]
fn test_reverse() {
    let parents: Relatives = [
        (BigUint::from(0u64), HashSet::new()),
        (BigUint::from(1u64), HashSet::new()),
        (BigUint::from(2u64), HashSet::new()),
        (BigUint::from(3u64), [BigUint::from(0u64), BigUint::from(1u64), BigUint::from(2u64)].iter().cloned().collect()),
        (BigUint::from(4u64), [BigUint::from(0u64), BigUint::from(1u64), BigUint::from(2u64)].iter().cloned().collect()),
        (BigUint::from(5u64), [BigUint::from(0u64), BigUint::from(1u64), BigUint::from(2u64)].iter().cloned().collect()),
    ].iter().cloned().collect();

    let expected: HashMap<BigUint, HashSet<BigUint>> = [
        (BigUint::from(0u64), [BigUint::from(3u64), BigUint::from(4u64), BigUint::from(5u64)].iter().cloned().collect()),
        (BigUint::from(1u64), [BigUint::from(3u64), BigUint::from(4u64), BigUint::from(5u64)].iter().cloned().collect()),
        (BigUint::from(2u64), [BigUint::from(3u64), BigUint::from(4u64), BigUint::from(5u64)].iter().cloned().collect()),
        (BigUint::from(3u64), HashSet::new()),
        (BigUint::from(4u64), HashSet::new()),
        (BigUint::from(5u64), HashSet::new()),
    ].iter().cloned().collect();

    assert_eq!(braid::reverse(&parents), expected);
}

#[test]
fn test_cohorts() {
    let parents1: Relatives = [
        (BigUint::from(0u64), HashSet::new()),
        (BigUint::from(1u64), [BigUint::from(0u64)].iter().cloned().collect()),
        (BigUint::from(2u64), [BigUint::from(1u64)].iter().cloned().collect()),
        (BigUint::from(3u64), [BigUint::from(2u64)].iter().cloned().collect()),
    ].iter().cloned().collect();

    let expected = vec![
        [BigUint::from(0u64)].iter().cloned().collect::<HashSet<_>>(),
        [BigUint::from(1u64)].iter().cloned().collect::<HashSet<_>>(),
        [BigUint::from(2u64)].iter().cloned().collect::<HashSet<_>>(),
        [BigUint::from(3u64)].iter().cloned().collect::<HashSet<_>>(),
    ];

    assert_eq!(braid::cohorts(&parents1, None, None), expected);
}

#[test]
fn test_cohorts_files() {
    for entry in fs::read_dir(TEST_CASE_DIR).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();

        if path.extension().map_or(false, |ext| ext == "json") {
            let path_str = path.to_string_lossy();
            let dag = load_braid(&path).unwrap();
            assert_eq!(
                braid::cohorts(&dag.parents, None, None),
                dag.cohorts,
                "Failed on file: {}", path_str
            );
        }
    }
}

#[test]
fn test_cohorts_reversed_files() {
    for entry in fs::read_dir(TEST_CASE_DIR).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();

        if path.extension().map_or(false, |ext| ext == "json") {
            let path_str = path.to_string_lossy();
            let dag = load_braid(&path).unwrap();
            let p = braid::reverse(&dag.parents);
            let mut c = dag.cohorts.clone();
            c.reverse();
            assert_eq!(
                braid::cohorts(&p, None, None),
                c,
                "Failed on file: {}", path_str
            );
        }
    }
}

#[test]
fn test_highest_work_path() {
    let parents1: Relatives = [
        (BigUint::from(0u64), HashSet::new()),
        (BigUint::from(1u64), [BigUint::from(0u64)].iter().cloned().collect()),
        (BigUint::from(2u64), [BigUint::from(1u64)].iter().cloned().collect()),
        (BigUint::from(3u64), [BigUint::from(2u64)].iter().cloned().collect()),
    ].iter().cloned().collect();

    let children1 = braid::reverse(&parents1);

    let expected = vec![
        BigUint::from(0u64),
        BigUint::from(1u64),
        BigUint::from(2u64),
        BigUint::from(3u64),
    ];

    assert_eq!(braid::highest_work_path(&parents1, Some(&children1), None), expected);
}

#[test]
fn test_highest_work_path_files() {
    for entry in fs::read_dir(TEST_CASE_DIR).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();

        if path.extension().map_or(false, |ext| ext == "json") {
            let path_str = path.to_string_lossy();
            let dag = load_braid(&path).unwrap();
            assert_eq!(
                braid::highest_work_path(&dag.parents, Some(&dag.children), None),
                dag.highest_work_path,
                "Failed on file: {}", path_str
            );
        }
    }
}

#[test]
fn test_check_cohort_files() {
    for entry in fs::read_dir(TEST_CASE_DIR).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();

        if path.extension().map_or(false, |ext| ext == "json") {
            let path_str = path.to_string_lossy();
            let dag = load_braid(&path).unwrap();
            for (i, c) in dag.cohorts.iter().enumerate() {
                assert!(
                    braid::check_cohort(c, &dag.parents, Some(&dag.children)),
                    "Failed on file: {}, cohort index: {}", path_str, i
                );
            }
        }
    }
}

#[test]
fn test_check_work_files() {
    for entry in fs::read_dir(TEST_CASE_DIR).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();

        if path.extension().map_or(false, |ext| ext == "json") {
            let path_str = path.to_string_lossy();
            let dag = load_braid(&path).unwrap();
            assert_eq!(
                dag.work,
                braid::descendant_work(&dag.parents, Some(&dag.children), Some(&dag.bead_work), None),
                "Failed on file: {}", path_str
            );
        }
    }
}

#[test]
fn test_sub_braid_files() {
    for entry in fs::read_dir(TEST_CASE_DIR).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();

        if path.extension().map_or(false, |ext| ext == "json") {
            let path_str = path.to_string_lossy();
            let dag = load_braid(&path).unwrap();
            for (i, c) in dag.cohorts.iter().enumerate() {
                assert_eq!(
                    braid::geneses(&braid::sub_braid(c, &dag.parents)),
                    braid::cohort_head(c, &dag.parents, Some(&dag.children)),
                    "Failed on file: {}, cohort index: {}, geneses check", path_str, i
                );

                assert_eq!(
                    braid::tips(&braid::sub_braid(c, &dag.parents), None),
                    braid::cohort_tail(c, &dag.parents, Some(&dag.children)),
                    "Failed on file: {}, cohort index: {}, tips check", path_str, i
                );

                assert_eq!(
                    braid::cohorts(&braid::sub_braid(c, &dag.parents), None, None),
                    vec![c.clone()],
                    "Failed on file: {}, cohort index: {}, cohorts check", path_str, i
                );
            }
        }
    }
}

#[test]
fn test_head_tail_files() {
    for entry in fs::read_dir(TEST_CASE_DIR).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();

        if path.extension().map_or(false, |ext| ext == "json") {
            let path_str = path.to_string_lossy();
            let dag = load_braid(&path).unwrap();
            for (i, c) in dag.cohorts.iter().enumerate() {
                assert_eq!(
                    braid::cohort_head(c, &dag.parents, Some(&dag.children)),
                    braid::geneses(&braid::sub_braid(c, &dag.parents)),
                    "Failed on file: {}, cohort index: {}, head check", path_str, i
                );

                assert_eq!(
                    braid::cohort_tail(c, &dag.parents, Some(&dag.children)),
                    braid::tips(&braid::sub_braid(c, &dag.parents), None),
                    "Failed on file: {}, cohort index: {}, tail check", path_str, i
                );
            }
        }
    }
}

#[test]
fn test_all_ancestors() {
    let parents = [
        (BigUint::from(0u64), HashSet::new()),
        (BigUint::from(1u64), [BigUint::from(0u64)].iter().cloned().collect()),
        (BigUint::from(2u64), [BigUint::from(1u64)].iter().cloned().collect()),
        (BigUint::from(3u64), [BigUint::from(2u64)].iter().cloned().collect()),
    ].iter().cloned().collect();

    let mut ancestors = std::collections::HashMap::new();
    braid::all_ancestors(&BigUint::from(3u64), &parents, &mut ancestors);

    let expected_ancestors = [
        (BigUint::from(3u64), [BigUint::from(0u64), BigUint::from(1u64), BigUint::from(2u64)].iter().cloned().collect()),
        (BigUint::from(2u64), [BigUint::from(0u64), BigUint::from(1u64)].iter().cloned().collect()),
        (BigUint::from(1u64), [BigUint::from(0u64)].iter().cloned().collect()),
        (BigUint::from(0u64), HashSet::new()),
    ].iter().cloned().collect();

    assert_eq!(ancestors, expected_ancestors);
}

#[test]
fn test_save_load_braid() {
    let parents = [
        (BigUint::from(0u64), HashSet::new()),
        (BigUint::from(1u64), [BigUint::from(0u64)].iter().cloned().collect()),
        (BigUint::from(2u64), [BigUint::from(1u64)].iter().cloned().collect()),
        (BigUint::from(3u64), [BigUint::from(2u64)].iter().cloned().collect()),
    ].iter().cloned().collect();

    let temp_file = "tests/temp_braid_test.json";
    let description = "Test braid";

    // Save the braid
    let dag = save_braid(&parents, temp_file, Some(description)).unwrap();

    // Load the braid
    let loaded_dag = load_braid(temp_file).unwrap();

    // Compare the original and loaded DAGs
    assert_eq!(loaded_dag.description.unwrap(), description);
    assert_eq!(loaded_dag.parents, dag.parents);
    assert_eq!(loaded_dag.children, dag.children);
    assert_eq!(loaded_dag.geneses, dag.geneses);
    assert_eq!(loaded_dag.tips, dag.tips);
    assert_eq!(loaded_dag.cohorts, dag.cohorts);
    assert_eq!(loaded_dag.bead_work, dag.bead_work);
    assert_eq!(loaded_dag.work, dag.work);
    assert_eq!(loaded_dag.highest_work_path, dag.highest_work_path);

    // Clean up
    std::fs::remove_file(temp_file).unwrap();
}

#[test]
fn test_geneses_from_braid_rs() {
    let parents1 = [
        (BigUint::from(0u64), HashSet::new()),
        (BigUint::from(1u64), [BigUint::from(0u64)].iter().cloned().collect()),
        (BigUint::from(2u64), [BigUint::from(1u64)].iter().cloned().collect()),
        (BigUint::from(3u64), [BigUint::from(2u64)].iter().cloned().collect()),
    ].iter().cloned().collect();

    assert_eq!(braid::geneses(&parents1), [BigUint::from(0u64)].iter().cloned().collect());

    let parents2 = [
        (BigUint::from(0u64), HashSet::new()),
        (BigUint::from(1u64), HashSet::new()),
        (BigUint::from(2u64), [BigUint::from(1u64)].iter().cloned().collect()),
        (BigUint::from(3u64), [BigUint::from(1u64)].iter().cloned().collect()),
    ].iter().cloned().collect();

    assert_eq!(braid::geneses(&parents2), [BigUint::from(0u64), BigUint::from(1u64)].iter().cloned().collect());
}

#[test]
fn test_tips_from_braid_rs() {
    let parents1 = [
        (BigUint::from(0u64), HashSet::new()),
        (BigUint::from(1u64), [BigUint::from(0u64)].iter().cloned().collect()),
        (BigUint::from(2u64), [BigUint::from(1u64)].iter().cloned().collect()),
        (BigUint::from(3u64), [BigUint::from(2u64)].iter().cloned().collect()),
    ].iter().cloned().collect();

    assert_eq!(braid::tips(&parents1, None), [BigUint::from(3u64)].iter().cloned().collect());

    let parents2 = [
        (BigUint::from(0u64), HashSet::new()),
        (BigUint::from(1u64), [BigUint::from(0u64)].iter().cloned().collect()),
        (BigUint::from(2u64), [BigUint::from(1u64)].iter().cloned().collect()),
        (BigUint::from(3u64), [BigUint::from(1u64)].iter().cloned().collect()),
    ].iter().cloned().collect();

    assert_eq!(braid::tips(&parents2, None), [BigUint::from(2u64), BigUint::from(3u64)].iter().cloned().collect());
}

#[test]
fn test_reverse_from_braid_rs() {
    let parents = [
        (BigUint::from(0u64), HashSet::new()),
        (BigUint::from(1u64), HashSet::new()),
        (BigUint::from(2u64), HashSet::new()),
        (BigUint::from(3u64), [BigUint::from(0u64), BigUint::from(1u64), BigUint::from(2u64)].iter().cloned().collect()),
        (BigUint::from(4u64), [BigUint::from(0u64), BigUint::from(1u64), BigUint::from(2u64)].iter().cloned().collect()),
        (BigUint::from(5u64), [BigUint::from(0u64), BigUint::from(1u64), BigUint::from(2u64)].iter().cloned().collect()),
    ].iter().cloned().collect();

    let expected = [
        (BigUint::from(0u64), [BigUint::from(3u64), BigUint::from(4u64), BigUint::from(5u64)].iter().cloned().collect()),
        (BigUint::from(1u64), [BigUint::from(3u64), BigUint::from(4u64), BigUint::from(5u64)].iter().cloned().collect()),
        (BigUint::from(2u64), [BigUint::from(3u64), BigUint::from(4u64), BigUint::from(5u64)].iter().cloned().collect()),
        (BigUint::from(3u64), HashSet::new()),
        (BigUint::from(4u64), HashSet::new()),
        (BigUint::from(5u64), HashSet::new()),
    ].iter().cloned().collect();

    assert_eq!(braid::reverse(&parents), expected);
}

#[test]
fn test_cohorts_from_braid_rs() {
    let parents1 = [
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

    assert_eq!(braid::cohorts(&parents1, None, None), expected);
}

#[test]
fn test_highest_work_path_from_braid_rs() {
    let parents1 = [
        (BigUint::from(0u64), HashSet::new()),
        (BigUint::from(1u64), [BigUint::from(0u64)].iter().cloned().collect()),
        (BigUint::from(2u64), [BigUint::from(1u64)].iter().cloned().collect()),
        (BigUint::from(3u64), [BigUint::from(2u64)].iter().cloned().collect()),
    ].iter().cloned().collect();

    let children1 = braid::reverse(&parents1);

    let expected = vec![
        BigUint::from(0u64),
        BigUint::from(1u64),
        BigUint::from(2u64),
        BigUint::from(3u64),
    ];

    assert_eq!(braid::highest_work_path(&parents1, Some(&children1), None), expected);
}
