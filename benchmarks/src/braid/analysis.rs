/// Simple timing point describing how long a scenario took to run for a given bead count.
#[derive(Clone, Copy, Debug)]
pub struct TimingPoint {
    pub total_beads: f64,
    pub duration_ms: f64,
}

/// Regression summary for a fit of time ≈ c0 + c1·n + c2·n² + c3·n³.
pub struct RegressionResult {
    coefficients: [f64; 4],
    std_errors: [f64; 4],
    pub residual_variance: f64,
}

impl RegressionResult {
    pub fn coefficients(&self) -> &[f64; 4] {
        &self.coefficients
    }

    pub fn std_errors(&self) -> &[f64; 4] {
        &self.std_errors
    }

    pub fn format_line(&self, label: &str) -> String {
        let mut parts = Vec::new();
        for i in 0..4 {
            parts.push(format!(
                "c{}={:.6e} ±{:.6e}",
                i, self.coefficients[i], self.std_errors[i]
            ));
        }
        format!("{:<12} {}", label, parts.join(", "))
    }
}

/// Fit a cubic polynomial to the provided timing points.
pub fn fit_cubic(points: &[TimingPoint]) -> Option<RegressionResult> {
    if points.len() < 4 {
        return None;
    }

    let scale = points
        .iter()
        .map(|p| p.total_beads.abs())
        .fold(0.0f64, f64::max)
        .max(1.0);

    let mut sums_n_pow = [0.0f64; 7];
    let mut sums_n_pow_y = [0.0f64; 4];

    for pt in points {
        let n = pt.total_beads / scale;
        let mut power = 1.0;
        for k in 0..7 {
            sums_n_pow[k] += power;
            power *= n;
        }

        power = 1.0;
        for k in 0..4 {
            sums_n_pow_y[k] += power * pt.duration_ms;
            power *= n;
        }
    }

    let mut xtx = [[0.0f64; 4]; 4];
    for i in 0..4 {
        for j in 0..4 {
            xtx[i][j] = sums_n_pow[i + j];
        }
    }

    let xty = sums_n_pow_y;
    let coefficients_scaled = solve_linear_system(xtx, xty)?;
    let mut rss = 0.0;

    for pt in points {
        let n = pt.total_beads / scale;
        let mut estimate = coefficients_scaled[0];
        let mut power = n;
        for &coef in &coefficients_scaled[1..] {
            estimate += coef * power;
            power *= n;
        }
        let diff = pt.duration_ms - estimate;
        rss += diff * diff;
    }

    let denom = (points.len() as f64 - 4.0).max(1e-6);
    let residual_variance = rss / denom;
    let inv_xtx = invert_matrix(xtx)?;
    let mut std_errors = [0.0f64; 4];
    for i in 0..4 {
        let diag = inv_xtx[i][i];
        std_errors[i] = (diag * residual_variance).max(0.0).sqrt();
    }

    let coefficients = [
        coefficients_scaled[0],
        coefficients_scaled[1] / scale,
        coefficients_scaled[2] / (scale * scale),
        coefficients_scaled[3] / (scale * scale * scale),
    ];

    Some(RegressionResult {
        coefficients,
        std_errors,
        residual_variance,
    })
}

fn solve_linear_system(mut matrix: [[f64; 4]; 4], mut rhs: [f64; 4]) -> Option<[f64; 4]> {
    for pivot in 0..4 {
        let mut max_row = pivot;
        for row in (pivot + 1)..4 {
            if matrix[row][pivot].abs() > matrix[max_row][pivot].abs() {
                max_row = row;
            }
        }

        if matrix[max_row][pivot].abs() < 1e-12 {
            return None;
        }

        if max_row != pivot {
            matrix.swap(pivot, max_row);
            rhs.swap(pivot, max_row);
        }

        let divisor = matrix[pivot][pivot];
        for col in pivot..4 {
            matrix[pivot][col] /= divisor;
        }
        rhs[pivot] /= divisor;

        for row in 0..4 {
            if row != pivot {
                let factor = matrix[row][pivot];
                for col in pivot..4 {
                    matrix[row][col] -= factor * matrix[pivot][col];
                }
                rhs[row] -= factor * rhs[pivot];
            }
        }
    }

    Some(rhs)
}

fn invert_matrix(matrix: [[f64; 4]; 4]) -> Option<[[f64; 4]; 4]> {
    let mut aug = [[0.0f64; 8]; 4];
    for i in 0..4 {
        for j in 0..4 {
            aug[i][j] = matrix[i][j];
        }
        aug[i][4 + i] = 1.0;
    }

    for pivot in 0..4 {
        let mut max_row = pivot;
        for row in (pivot + 1)..4 {
            if aug[row][pivot].abs() > aug[max_row][pivot].abs() {
                max_row = row;
            }
        }

        if aug[max_row][pivot].abs() < 1e-12 {
            return None;
        }

        if max_row != pivot {
            aug.swap(pivot, max_row);
        }

        let divisor = aug[pivot][pivot];
        for col in pivot..8 {
            aug[pivot][col] /= divisor;
        }

        for row in 0..4 {
            if row != pivot {
                let factor = aug[row][pivot];
                for col in pivot..8 {
                    aug[row][col] -= factor * aug[pivot][col];
                }
            }
        }
    }

    let mut inverse = [[0.0f64; 4]; 4];
    for i in 0..4 {
        for j in 0..4 {
            inverse[i][j] = aug[i][4 + j];
        }
    }

    Some(inverse)
}
