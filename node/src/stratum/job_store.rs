use std::{collections::HashMap, sync::Arc};

use crate::error::StratumErrors;
use crate::TemplateId;

use super::types::JobDetails;
#[allow(unused_imports)]
use tracing::{debug, error, info, trace, warn};

/// Global job store shared across all miner connections.
///
/// Templates are stored once as `Arc<JobDetails>` and shared by pointer — no per-miner
/// cloning of `BlockTemplate` data. At 10k miners and 150ms bead rate, this brings
/// per-template memory from ~5GB (cloned) down to ~500KB (one allocation + pointers).
///
/// Eviction: when `capacity` is reached, the oldest job_id entry is removed. Template
/// data is only freed once no remaining job_id references that template_id, which
/// prevents `get` from returning stale entries for in-flight submits.
pub struct GlobalJobStore {
    jobs: HashMap<TemplateId, Arc<JobDetails>>,
    job_id_to_template: HashMap<u64, TemplateId>,
    next_job_id: u64,
    capacity: usize,
}

impl GlobalJobStore {
    pub fn new(capacity: usize) -> Self {
        Self {
            jobs: HashMap::new(),
            job_id_to_template: HashMap::new(),
            next_job_id: 0,
            capacity: capacity.max(1),
        }
    }

    pub fn clear_upstream_jobs(&mut self) {
        let upstream_template_ids: Vec<TemplateId> = self
            .job_id_to_template
            .values()
            .filter(|tid| matches!(tid, TemplateId::Upstream(_)))
            .cloned()
            .collect();

        if upstream_template_ids.is_empty() {
            return;
        }

        info!(
            count = %upstream_template_ids.len(),
            "Clearing stale upstream jobs from store due to disconnect"
        );

        self.job_id_to_template
            .retain(|_, tid| !matches!(tid, TemplateId::Upstream(_)));
        for tid in upstream_template_ids {
            self.jobs.remove(&tid);
        }
    }

    /// Insert a job into the store. Returns the assigned numeric job_id.
    ///
    /// Uses `entry().or_insert()` so if `template_id` already exists the existing
    /// `Arc` is reused instead of creating a duplicate allocation.
    pub fn insert(&mut self, template_id: TemplateId, job: Arc<JobDetails>) -> u64 {
        let job_id = self.next_job_id;
        debug!(job_id = %job_id, template_id = %template_id, "Inserting job into GlobalJobStore");

        // Evict oldest job_id when at capacity; only free template data if unreferenced.
        // Use the actual minimum key rather than (next_job_id - capacity) because
        // clear_upstream_jobs() can create holes in job_id_to_template that would
        // cause the arithmetic approach to miss the eviction target entirely.
        if self.job_id_to_template.len() >= self.capacity {
            if let Some(oldest_id) = self.job_id_to_template.keys().min().copied() {
                if let Some(old_template_id) = self.job_id_to_template.remove(&oldest_id) {
                    let still_referenced = self
                        .job_id_to_template
                        .values()
                        .any(|tid| tid == &old_template_id);
                    if !still_referenced {
                        self.jobs.remove(&old_template_id);
                        debug!(template_id = %old_template_id, "Evicted template from GlobalJobStore");
                    }
                }
            }
        }

        self.jobs.entry(template_id.clone()).or_insert(job);
        self.job_id_to_template.insert(job_id, template_id);
        self.next_job_id += 1;
        job_id
    }

    /// Looks up an upstream job by its original string ID.
    /// Returns an `Arc` clone so callers can drop the store lock before accessing data.
    pub fn get_by_string_job_id(
        &self,
        job_id_str: &str,
    ) -> Result<(Arc<JobDetails>, TemplateId), StratumErrors> {
        let tid = TemplateId::Upstream(job_id_str.to_string());
        self.jobs
            .get(&tid)
            .cloned()
            .map(|job| (job, tid))
            .ok_or_else(|| StratumErrors::MiningJobNotFound {
                job_id: None,
                template_id: None,
            })
    }

    /// Get job by template_id.
    pub fn get_by_template_id(
        &self,
        template_id: &TemplateId,
    ) -> Result<Arc<JobDetails>, StratumErrors> {
        self.jobs
            .get(template_id)
            .cloned()
            .ok_or_else(|| StratumErrors::MiningJobNotFound {
                job_id: None,
                template_id: Some(template_id.clone()),
            })
    }

    /// Returns an `Arc` clone for the job, allowing callers to drop the store lock
    /// before accessing template data.
    pub fn get_by_job_id(&self, job_id: u64) -> Result<Arc<JobDetails>, StratumErrors> {
        let template_id = self.job_id_to_template.get(&job_id).ok_or_else(|| {
            StratumErrors::MiningJobNotFound {
                job_id: Some(job_id),
                template_id: None,
            }
        })?;
        let job = self.jobs.get(template_id).cloned().ok_or_else(|| {
            StratumErrors::MiningJobNotFound {
                job_id: Some(job_id),
                template_id: Some(template_id.clone()),
            }
        })?;
        Ok(job)
    }

    /// Get template_id from numeric job_id for mining.submit validation.
    pub fn template_id_from_job_id(&self, job_id: u64) -> Option<TemplateId> {
        self.job_id_to_template.get(&job_id).cloned()
    }

    /// Returns the highest job_id currently mapped to `template_id`, or `None` if no
    /// live entry exists for that template.
    ///
    /// Used by the resend path to reuse an existing job_id for a reconnecting miner
    /// instead of minting a new one. Minting would advance `next_job_id`, eventually
    /// evicting the job_id that already-connected miners are submitting against.
    pub fn latest_job_id_for(&self, template_id: &TemplateId) -> Option<u64> {
        self.job_id_to_template
            .iter()
            .filter(|(_, tid)| **tid == *template_id)
            .map(|(&id, _)| id)
            .max()
    }
}
