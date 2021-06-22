import random

import simpy

from node import Node
from config import config

def run():
    # Setup and start the simulation
    print('Process communication')
    random.seed(config['simulation']['random_seed'])
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
    env.run(until=config['simulation']['run_time'])
    print('At node_a')
    print(node_a.dag.edges())

    print('At node_b')
    print(node_b.dag.edges())

    print('At node_c')
    print(node_c.dag.edges())


if __name__ == '__main__':
    run()
