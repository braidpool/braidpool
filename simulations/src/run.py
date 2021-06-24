import networkx as nx
import random

import simpy
import logging

from node import Node
from config import config


def run():
    # Setup and start the simulation
    logging.basicConfig(format='%(levelname)s:%(message)s', level=config['logging']['level'])

    logging.info('Process communication')
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

    logging.info('\nP2P broadcast communication\n')
    env.run(until=config['simulation']['run_time'])

    for node in [node_a, node_b, node_c]:
        logging.info(f'At {node.name}')
        logging.info(list(nx.lexicographical_topological_sort(node.dag)))
        logging.info(node.dag.edges())
        if config.getboolean('simulation', 'save_dot'):
            g = nx.nx_agraph.to_agraph(node.dag)
            g.layout()
            g.draw(f'/tmp/node_{node.name}.png', prog='dot')


if __name__ == '__main__':
    run()
