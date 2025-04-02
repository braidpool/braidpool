
import random
import multiprocessing
import concurrent.futures
import math
import numpy as np
from scipy import special
from scipy import stats
from simulator import *

# Worker function for parallel execution - must be at module level for pickling
def run_single_simulation(params):
    run_index, kp, ki, kd, nodes, beads, peers, target_value, log = params

    if log:
        print(f"  Run {run_index+1} for Kp={kp:.4f}, Ki={ki:.4f}, Kd={kd:.4f}")

    # Create a new random seed for each run to ensure diversity
    run_seed = random.randint(1, 10000)
    random.seed(run_seed)

    # Run a simulation with these parameters
    n = Network(int(nodes), NETWORK_HASHRATE, target=target_value,
               target_algo="pid", npeers=int(peers), log=log)
    n.simulate(nbeads=int(beads), mine=False)

    # Calculate metrics to evaluate performance
    errors = []
    for node in n.nodes:
        errors.extend(node.prev_errors)

    if not errors:
        return None

    # Calculate metrics
    mean_error = sum(abs(e) for e in errors) / len(errors)
    error_variance = sum((abs(e) - mean_error)**2 for e in errors) / len(errors)

    # Calculate oscillation by looking at sign changes
    sign_changes = sum(1 for i in range(1, len(errors)) if errors[i] * errors[i-1] < 0)
    oscillation_factor = sign_changes / len(errors) if errors else 1

    # Combined score (lower is better)
    score = mean_error + 0.5 * error_variance + 2 * oscillation_factor

    return (score, mean_error, error_variance, oscillation_factor)

def calibrate_pid_parameters(nodes=25, beads=100, peers=4, target=239, log=True, iterations=20, runs_per_eval=3):
    """
    Calibrate PID controller parameters using gradient descent to find optimal values
    that minimize error and oscillation.

    Args:
        nodes: Number of nodes in the network
        beads: Number of beads to simulate
        peers: Number of peers per node
        target: Target difficulty exponent
        log: Whether to log simulation details
        iterations: Number of gradient descent iterations
        runs_per_eval: Number of simulation runs to average for each parameter set

    Returns:
        tuple: The optimal (Kp, Ki, Kd) values
    """
    print("Starting PID parameter calibration using gradient descent...")

    # Store original values to restore later
    original_calc_target_pid = Node.calc_target_pid

    target_value = 2**int(target)-1

    # Initial parameter values
    #1. Kp=0.0481, Ki=0.0000, Kd=0.0262, Score=0.5927
    #1. Kp=0.0640, Ki=0.0000, Kd=0.0221, Score=0.5681
    #1. Kp=0.1344, Ki=0.0000, Kd=0.0962, Score=0.7460 (long run)
    # After transformation to Lambert W-based estimation:
    #1. Kp=0.1216, Ki=0.0000, Kd=0.0663, Score=0.3985
    #1. Kp=0.0643, Ki=0.0410, Kd=0.1040, Score=0.3992
    params = {
        'Kp': 0.1216,
        'Ki': 0.00,
        'Kd': 0.0663
    }

    # Learning rates for each parameter
    learning_rates = {
        'Kp': 0.02,
        'Ki': 0.005,
        'Kd': 0.01
    }

    # Parameter bounds
    bounds = {
        'Kp': (0.00001, 1.0),
        'Ki': (0.0, 1.0),
        'Kd': (0.0, 1.0)
    }

    # Keep track of all results
    results = []

    # Function to evaluate a parameter set
    def evaluate_params(kp, ki, kd):
        # Create a modified PID function with these parameters
        def modified_pid(self, parents):
            # Get the current state
            Nb = sum(map(len, self.braid.cohorts[-TARGET_NC:]))
            Nc = len(self.braid.cohorts[-TARGET_NC:])
            Nb_Nc = Nb/Nc

            # Calculate the error (difference between current and target ratio)
            target_ratio = TARGET_NB/TARGET_NC
            error = target_ratio - Nb_Nc

            # Harmonic average of parent targets
            x_1 = len(parents)*MAX_HASH//sum(MAX_HASH//p.target for p in parents)

            # Initialize parameter estimation data if not already present
            if not hasattr(self, 'param_history'):
                self.param_history = {
                    'x_values': [],
                    'w_values': [],
                    'a_lambda': 1.0,  # Initial estimate for a*lambda
                    'confidence': 0.0  # Confidence in our estimate (0-1)
                }
                self.param_window_size = 20  # Number of data points to keep for estimation
                self.forgetting_factor = 0.95  # Weight for older observations (0.9-0.99)

            # Calculate the target w value using the target ratio
            target_w = special.lambertw((target_ratio - 1)).real

            # Calculate the current w value
            current_w = special.lambertw((Nb_Nc - 1)).real if Nb_Nc > 1 else 0

            # Store the current data point for parameter estimation
            # Only store if we have a valid parent target and a valid Nb/Nc ratio
            if x_1 > 0 and Nb_Nc > 1:
                self.param_history['x_values'].append(x_1)
                self.param_history['w_values'].append(current_w)

                # Keep only the most recent window_size points
                if len(self.param_history['x_values']) > self.param_window_size:
                    self.param_history['x_values'].pop(0)
                    self.param_history['w_values'].pop(0)

                # Update parameter estimate if we have enough data points
                if len(self.param_history['x_values']) >= 3:
                    # Apply forgetting factor to give more weight to recent observations
                    weights = np.array([self.forgetting_factor ** (len(self.param_history['x_values']) - i - 1)
                                       for i in range(len(self.param_history['x_values']))])

                    # Normalize weights
                    weights = weights / np.sum(weights)

                    # Perform weighted linear regression to estimate a*lambda
                    # The relationship is w = a*lambda*x, so we're fitting w = k*x where k = a*lambda
                    x_array = np.array(self.param_history['x_values'])
                    w_array = np.array(self.param_history['w_values'])

                    # Handle potential numerical issues
                    # Convert arrays to float type to ensure compatibility with isfinite
                    x_array_float = x_array.astype(float)
                    w_array_float = w_array.astype(float)
                    valid_indices = (x_array > 0) & (w_array > 0) & np.isfinite(x_array_float) & np.isfinite(w_array_float)
                    if np.sum(valid_indices) >= 3:
                        x_valid = x_array[valid_indices]
                        w_valid = w_array[valid_indices]
                        weights_valid = weights[valid_indices]

                        # Check if we have enough unique x values for regression
                        if len(np.unique(x_valid)) >= 2:
                            try:
                                # Fit w = k*x through origin (no intercept)
                                k, _, r_value, p_value, _ = stats.linregress(x_valid, w_valid)
                            except Exception as e:
                                # If regression fails, use the current estimate
                                if self.log and self.nodeid == 0:
                                    print(f"Regression failed: {str(e)}. Using current estimate.")
                                k = self.param_history['a_lambda']
                                r_value = 0
                                p_value = 1.0
                        else:
                            # Not enough unique x values, use current estimate
                            if self.log and self.nodeid == 0:
                                print(f"Not enough unique x values for regression. Using current estimate.")
                            k = self.param_history['a_lambda']
                            r_value = 0
                            p_value = 1.0

                        # Only update if the fit is reasonable and statistically significant
                        if k > 0 and p_value < 0.05 and r_value > 0.5:
                            # Smooth the update to avoid abrupt changes
                            self.param_history['a_lambda'] = 0.8 * self.param_history['a_lambda'] + 0.2 * k
                            self.param_history['confidence'] = min(1.0, r_value**2)  # R² as confidence

            # Use the estimated a*lambda parameter
            a_lambda = self.param_history['a_lambda']

            # Error in the transformed space
            transformed_error = target_w - current_w

            # Log parameter estimation details if needed
            if self.log and self.nodeid == 0 and hasattr(self, 'param_history') and len(self.param_history['x_values']) > 0:
                print(f"Parameter estimation: a*lambda={a_lambda:.6f}, confidence={self.param_history['confidence']:.2f}, "
                      f"data points={len(self.param_history['x_values'])}")

            # PID controller parameters - use the current test values
            Kp = kp  # Proportional gain
            Ki = ki  # Integral gain
            Kd = kd  # Derivative gain

            # Store the transformed error for integral and derivative terms
            self.prev_errors.append(transformed_error)
            if len(self.prev_errors) > self.max_error_history:
                self.prev_errors.pop(0)  # Remove oldest error

            # Proportional term
            p_term = Kp * transformed_error

            # Integral term - sum of all previous errors
            i_term = Ki * sum(self.prev_errors)

            # Derivative term - rate of change of error
            d_term = 0
            if len(self.prev_errors) >= 2:
                d_term = Kd * (self.prev_errors[-1] - self.prev_errors[-2])

            # Combine terms to get the control output in the transformed space
            w_control = p_term + i_term + d_term

            # Convert back to the original space using the relationship a*lambda*x = w
            # x = w / (a*lambda)
            x_ideal = w_control / a_lambda

            # Calculate adjustment factor relative to the current x_1
            adjustment_factor = x_ideal / x_1 if x_1 > 0 else 1.0

            # Apply a constraint to the adjustment factor for safety
            constrained_adjustment = 0.9 * (2 / (1 + math.exp(-2 * adjustment_factor)) - 1)

            # Apply the constrained adjustment
            new_target = int(x_1 * (1 + constrained_adjustment))

            # Additional safety check to ensure target stays within reasonable bounds
            new_target = max(1, min(MAX_HASH, new_target))

            if self.log and self.nodeid == 0:
                print(f"Lambert-PID: Nb/Nc={Nb_Nc:.4f} Target={target_ratio:.4f} "
                      f"Error={error:.4f} Transformed Error={transformed_error:.4f} "
                      f"P={p_term:.4f} I={i_term:.4f} D={d_term:.4f} "
                      f"W-control={w_control:.4f} X-ideal={x_ideal:.4f} "
                      f"Adjustment={constrained_adjustment:.4f} "
                      f"Old={print_hash_simple(x_1)} New={print_hash_simple(new_target)}")

            return new_target

        # Replace the PID function temporarily
        Node.calc_target_pid = modified_pid

        # Run multiple simulations in parallel and average the results
        all_scores = []
        all_mean_errors = []
        all_error_variances = []
        all_oscillation_factors = []

        num_cores = multiprocessing.cpu_count()
        if log:
            print(f"  Running {runs_per_eval} simulations in parallel using {num_cores} CPU cores")

        # Prepare parameters for each simulation
        sim_params = [
            (run, kp, ki, kd, nodes, beads, peers, target_value, log)
            for run in range(runs_per_eval)
        ]

        # Run simulations in parallel
        with concurrent.futures.ProcessPoolExecutor(max_workers=num_cores) as executor:
            results = list(executor.map(run_single_simulation, sim_params))

            for result in results:
                if result is not None:
                    score, mean_error, error_variance, oscillation_factor = result
                    all_scores.append(score)
                    all_mean_errors.append(mean_error)
                    all_error_variances.append(error_variance)
                    all_oscillation_factors.append(oscillation_factor)

            # Metrics calculation moved to the worker function

        # If all runs failed, return infinity
        if not all_scores:
            return float('inf'), 0, 0, 0

        # Average the results
        avg_score = sum(all_scores) / len(all_scores)
        avg_mean_error = sum(all_mean_errors) / len(all_mean_errors)
        avg_error_variance = sum(all_error_variances) / len(all_error_variances)
        avg_oscillation_factor = sum(all_oscillation_factors) / len(all_oscillation_factors)

        if log:
            print(f"  Average score over {len(all_scores)} runs: {avg_score:.4f}")
            print(f"  Score range: {min(all_scores):.4f} - {max(all_scores):.4f}")

        return avg_score, avg_mean_error, avg_error_variance, avg_oscillation_factor

    # Function to compute numerical gradient
    def compute_gradient(params, epsilon=0.01):
        gradient = {}
        base_score, base_mean, base_var, base_osc = evaluate_params(
            params['Kp'], params['Ki'], params['Kd'])

        # For each parameter, compute partial derivative
        for param in params:
            # Create a copy with slightly increased parameter
            params_plus = params.copy()
            params_plus[param] += epsilon

            # Evaluate with increased parameter
            score_plus, _, _, _ = evaluate_params(
                params_plus['Kp'], params_plus['Ki'], params_plus['Kd'])

            # Compute approximate gradient
            gradient[param] = (score_plus - base_score) / epsilon

        return gradient, base_score, base_mean, base_var, base_osc

    best_score = float('inf')
    best_params = params.copy()

    # Gradient descent iterations
    for i in range(iterations):
        print(f"\nIteration {i+1}/{iterations}")
        print(f"Current parameters: Kp={params['Kp']:.4f}, Ki={params['Ki']:.4f}, Kd={params['Kd']:.4f}")

        # Compute gradient
        gradient, score, mean_error, error_variance, oscillation_factor = compute_gradient(params)

        print(f"Score: {score:.4f} (Mean error: {mean_error:.4f}, Variance: {error_variance:.4f}, Oscillation: {oscillation_factor:.4f})")

        # Store result
        results.append({
            'Kp': params['Kp'],
            'Ki': params['Ki'],
            'Kd': params['Kd'],
            'mean_error': mean_error,
            'error_variance': error_variance,
            'oscillation_factor': oscillation_factor,
            'score': score
        })

        # Update best parameters if we found a better score
        if score < best_score:
            best_score = score
            best_params = params.copy()
            print(f"New best parameters found: Kp={params['Kp']:.4f}, Ki={params['Ki']:.4f}, Kd={params['Kd']:.4f}, Score={score:.4f}")

        # Update parameters using gradient descent
        for param in params:
            # Update parameter in the opposite direction of the gradient
            update = -learning_rates[param] * gradient[param]

            # Apply momentum to smooth updates (optional)
            params[param] += update

            # Ensure parameters stay within bounds
            params[param] = max(bounds[param][0], min(bounds[param][1], params[param]))

        # Adaptive learning rate - reduce if we're not making progress
        if i > 2 and results[-1]['score'] > results[-3]['score']:
            for param in learning_rates:
                learning_rates[param] *= 0.8
                print(f"Reducing learning rate for {param} to {learning_rates[param]:.6f}")

    # Restore original function
    Node.calc_target_pid = original_calc_target_pid

    # Sort results by score
    results.sort(key=lambda x: x['score'])

    # Print top 5 results
    print("\nTop 5 parameter combinations:")
    for i, result in enumerate(results[:5]):
        print(f"{i+1}. Kp={result['Kp']:.4f}, Ki={result['Ki']:.4f}, Kd={result['Kd']:.4f}, Score={result['score']:.4f}")

    print(f"\nOptimal PID parameters: Kp={best_params['Kp']:.4f}, Ki={best_params['Ki']:.4f}, Kd={best_params['Kd']:.4f}")
    return (best_params['Kp'], best_params['Ki'], best_params['Kd'])

def main():
    global NETWORK_HASHRATE, TARGET_NB, TARGET_NC, TARGET_DAMPING, DEBUG
    parser = ArgumentParser()
    parser.add_argument("-n", "--nodes",
        help="Number of nodes to simulate",
        default=25)
    parser.add_argument("-t", "--target",
        help="Target difficulty exponent t where T=2**t-1",
        default=239)
    parser.add_argument("-b", "--beads",
        help="Number of beads to simulate",
        default=50)
    parser.add_argument("-p", "--peers",
        help="Number of peers per node",
        default=4)
    parser.add_argument("-R", "--target-ratio",
        help="Target N_B/N_C ratio",
        default=f"{TARGET_NB}/{TARGET_NC}")
    parser.add_argument("-l", "--log", action=BooleanOptionalAction,
        help="Log each bead as it is found to make plots.", default=False)
    parser.add_argument("--debug", action=BooleanOptionalAction,
        help="Print extra debugging information", default=False)
    parser.add_argument("--pid-iterations",
        help="Number of iterations for PID calibration gradient descent", default=20)
    parser.add_argument("--pid-runs-per-eval",
        help="Number of simulation runs to average for each parameter evaluation", default=3)
    parser.add_argument("--initial-a-lambda",
        help="Initial estimate for a*lambda parameter", default=1.0, type=float)
    parser.add_argument("--forgetting-factor",
        help="Forgetting factor for parameter estimation (0.9-0.99)", default=0.95, type=float)
    parser.add_argument("--param-window",
        help="Window size for parameter estimation", default=20, type=int)
    args = parser.parse_args()
    DEBUG = args.debug
    if DEBUG: args.log = True
    TARGET_NB, TARGET_NC = map(int, re.search(r"(\d+)/(\d+)", args.target_ratio).groups())

    optimal_params = calibrate_pid_parameters(
        nodes=int(args.nodes),
        beads=int(args.beads),
        peers=int(args.peers),
        target=args.target,
        log=args.log,
        iterations=int(args.pid_iterations),
        runs_per_eval=int(args.pid_runs_per_eval)
    )
    print("\nTo use these parameters with the adaptive Lambert W transformation, update the calc_target_pid function with:")
    print(f"Kp = {optimal_params[0]}  # Proportional gain")
    print(f"Ki = {optimal_params[1]}  # Integral gain")
    print(f"Kd = {optimal_params[2]}  # Derivative gain")
    print(f"initial_a_lambda = {args.initial_a_lambda}  # Initial estimate for a*lambda")
    print(f"forgetting_factor = {args.forgetting_factor}  # Forgetting factor for parameter estimation")
    print(f"param_window_size = {args.param_window}  # Window size for parameter estimation")
    return

if __name__ == "__main__":
    main()
