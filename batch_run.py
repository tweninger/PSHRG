#!/usr/bin/python2.7

from __future__ import print_function
from itertools import combinations

import ast
import pickle

import multiprocessing
import os, sys

import networkx as nx
import numpy as np

import PSHRG

CORES = 8
TRIALS = range(1)
TIMEOUT = 1800


def usage(status):
    print( '''Usage: {} [OPTION]... [FILE]...
Runs PSHRG on each temporal graph (file) and logs results
  --help             prints help message')
  --cores num        uses NUM subprocesses (default: 2)
  --trials num       number of trials (default: 1)
  --timeout num      timeout for the process (default: 30 minutes)

Note: pkl files should be specified with .pkl extension
Otherwise: files are assumed to be parseable by "ast" module
'''.format(os.path.basename(sys.argv[0])), end='')
    exit(status)


def build_graph(add_edge_events, del_edge_events={}):
    # for thing in (add_edge_events):
    #    print(thing)
    g = nx.DiGraph()
    g.name = 'true-graph'
    for time, event in add_edge_events.items():
        for u, v in event:
            g.add_edge(u, v, label='e')
    for time, event in del_edge_events.items():
        for u, v in event:
            if (u, v) in g_next.edges():
                g.remove_edge(u, v)
    return g


def run(filename):
    try:
        ext = filename.split('.')[-1]
        name = filename.split('/')[-2]
    except ValueError:
        name = filename
        ext = ''
    add_edges = []

    if ext == 'pkl':
        add_edges.append(pickle.load(open(filename, 'rb')))
    else: # it is a text file with each line being a dictionary 
        with open(filename) as f:
            add_edges = [ast.literal_eval(l.strip()) for l in f]

    for add_edge in add_edges:
        for num in TRIALS:
            predict_graph = one_trial(filename, num, add_edge)

ok_count = 0
goal_count = 0
def one_trial(filename, trial, add_edges):
    global ok_count, goal_count
    try:
        os.stat(filename)
    except:
        print('{} does not exist or has wrong permissions!'.format(filename))
        usage(1)

    try:
        ext = filename.split('.')[-1]
        name = filename.split('/')[-1]
    except ValueError:
        name = filename
        ext = ''

    results_path = 'results_new/{}'.format(name)
    final_stats  = 'results_new/{}/overall_stats.txt'.format(name)

    if not os.path.isdir(results_path):
        os.makedirs(results_path)


    stats_file = open(final_stats, 'a')

    if os.path.getsize(final_stats) == 0: # write headers only on file creation
        stats_file.write(','.join(['trial', 'status', 'elapsed time\n']))

    status, graph, shrg_rules, runtime = PSHRG.main(add_edges)

    if status == 'fail':
        goal_count += 1
        num = goal_count
        return 

    elif status == 'pass':
        ok_count += 1
        num = ok_count
        edges_file = '{}/shrg_edges_{}'.format(results_path, ok_count)
        nx.write_edgelist(graph, edges_file, data=False)

        pickle_path = '{}/shrg_{:02}.pkl'.format(results_path, num)
        with open(pickle_path, 'wb') as f:
            pickle.dump(shrg_rules, f)

        ae_path = '{}/add_edges.txt'.format(results_path)

        print(str(add_edges), file=open(ae_path, 'a'))

    stats_file.write('{}, {}, {:.5}\n'.format(goal_count + ok_count, status, runtime)) 

    if status == 'fail' or graph is None:
        return

    stergm_graph = PSHRG.exteRnal(add_edges)
    true_graph = build_graph(add_edges)

    n = graph.number_of_nodes()
    p = float(graph.number_of_edges()) / (n*(n-1))
    er_graph = nx.erdos_renyi_graph(n, p, directed=True)
    er_graph.name = 'erdos-renyi'
    graph.name = 'pshrg'


    for g0, g1 in combinations([graph, true_graph, er_graph, stergm_graph], 2):
        PSHRG.cmp(g0, g1, '{}/{}_{}'.format(results_path, g0.name, g1.name))
    stats_file.close()


if __name__ == '__main__':
    np.seterr(all='ignore')
    args = sys.argv[1:]
    try:
        while args[0][0] == '-':
            arg = args.pop(0)
            if arg == '--help':
                usage(0)
            if arg == '--cores':
                CORES = int(args.pop(0))
	    if arg == '--trials':
                TRIALS = range(int(args.pop(0)))
            if arg == '--timeout':
                TIMEOUT = int(args.pop(0)) * 60
    
        assert len(args) > 0
    except:
        usage(1)
    
    pool = multiprocessing.Pool(CORES)
    result = pool.imap(run, args)
    count = 0
    while True:
        count += 1
        try:
            result.next(TIMEOUT)
        except multiprocessing.TimeoutError:
            print("Process took too long, aborting...")
            print('{}\n'.format(count), file=open('timeouts.txt', 'a'))
        except StopIteration:
            break
        finally:
            pass
