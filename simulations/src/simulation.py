import numpy as np

from config import config

seed = int(config["simulation"]["random_seed"])
rng = np.random.default_rng(seed=seed)


def get_random(*, period):
    return rng.exponential(period)
