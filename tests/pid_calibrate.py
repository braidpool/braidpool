
import random
import multiprocessing
import concurrent.futures
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
    params = {
        'Kp': 0.0481,
        'Ki': 0.00,
        'Kd': 0.0262
    }

    # Learning rates for each parameter
    learning_rates = {
        'Kp': 0.02,
        'Ki': 0.005,
        'Kd': 0.01
    }

    # Parameter bounds
    bounds = {
        'Kp': (0.00001, 0.3),
        'Ki': (0.0, 0.00),
        'Kd': (0.0, 0.3)
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

            # PID controller parameters - use the current test values
            Kp = kp  # Proportional gain
            Ki = ki  # Integral gain
            Kd = kd  # Derivative gain

            # Harmonic average of parent targets
            x_1 = len(parents)*MAX_HASH//sum(MAX_HASH//p.target for p in parents)

            # Proportional term
            p_term = Kp * error

            # Integral term - sum of all previous errors
            self.prev_errors.append(error)
            if len(self.prev_errors) > self.max_error_history:
                self.prev_errors.pop(0)  # Remove oldest error
            i_term = Ki * sum(self.prev_errors)

            # Derivative term - rate of change of error
            d_term = 0
            if len(self.prev_errors) >= 2:
                d_term = Kd * (self.prev_errors[-1] - self.prev_errors[-2])

            # Combine terms to get the adjustment factor
            adjustment = p_term + i_term + d_term

            # Apply adjustment to the target using a constrained approach
            # Use tanh-like function to limit adjustment to [-0.9, 0.9] range
            constrained_adjustment = 0.9 * (2 / (1 + math.exp(-2 * adjustment)) - 1)

            # Apply the constrained adjustment
            new_target = int(x_1 * (1 + constrained_adjustment))

            # Additional safety check to ensure target stays within reasonable bounds
            new_target = max(1, min(MAX_HASH, new_target))

            if self.log and self.nodeid == 0:
                print(f"PID: Nb/Nc={Nb_Nc:.4f} Target={target_ratio:.4f} Error={error:.4f} "
                      f"P={p_term:.4f} I={i_term:.4f} D={d_term:.4f} "
                      f"Adjustment={adjustment:.4f} Old={print_hash_simple(x_1)} New={print_hash_simple(new_target)}")

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
    print("\nTo use these parameters, update the calc_target_pid function with:")
    print(f"Kp = {optimal_params[0]}  # Proportional gain")
    print(f"Ki = {optimal_params[1]}  # Integral gain")
    print(f"Kd = {optimal_params[2]}  # Derivative gain")
    return

if __name__ == "__main__":
    main()
