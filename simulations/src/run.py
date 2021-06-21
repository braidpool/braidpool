import random

import simpy

from node import Node

RANDOM_SEED = 42
SIM_TIME = 10_000


def run():
    # Setup and start the simulation
    print('Process communication')
    random.seed(RANDOM_SEED)
    env = simpy.Environment()

    node_a = Node(name='a', env=env)
    node_b = Node(name='b', env=env)
    node_c = Node(name='c', env=env)

    node_a.add_neighbour(node_b)
    node_b.add_neighbour(node_a)
    node_b.add_neighbour(node_c)
    node_c.add_neighbour(node_b)
    node_a.start()
    node_b.start()
    node_c.start()

    print('\nP2P broadcast communication\n')
    env.run(until=SIM_TIME)


if __name__ == '__main__':
    run()
