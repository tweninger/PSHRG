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


CORES = 2
TRIALS = range(1)
TIMEOUT = 1800


def usage(status):
    print( '''Usage: {} [OPTION]... [FILE]...
Runs PSHRG on each temporal graph (file) and logs results
  --help             prints help message')
  --cores num        uses NUM subprocesses (default: 2)
  --trials num       uses NUM subprocesses (default: 1)
  --timeout num      uses NUM subprocesses (default: 30)

Note: pkl files should be specified with .pkl extension
Otherwise: files are assumed to be parseable by "ast" module
'''.format(os.path.basename(sys.argv[0])), end='')
    exit(status)


def build_graph(add_edge_events, del_edge_events={}):
    for thing in (add_edge_events):
        print(thing)
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
    for num in TRIALS:
        predict_graph = one_trial(filename, num)


def one_trial(filename, trial):
    try:
        os.stat(filename)
    except:
        print('{} does not exist or has wrong permissions!'.format(filename))
        usage(1)

    try:
        name, ext = filename.split('.')
    except ValueError:
        name = filename
        ext = ''

    results_path = 'results/{}/trial{:02}'.format(name, trial)
    fail_path    = '{}/fail'.format(results_path)
    pass_path    = '{}/pass'.format(results_path)
    final_stats  = '{}/overall_stats.txt'.format(results_path)

    for path in [results_path, fail_path, pass_path]:
        if not os.path.isdir(path):
            os.makedirs(path)

    goal_count = 0
    ok_count = 0

    with open(filename) as graph_file:
        if ext == 'pkl':
            add_edges_list = pickle.load(graph_file)
        else:
            try:
                add_edges_list = [ast.literal_eval(l.strip()) for l in graph_file]
            except ValueError:
                print('Could not parse {}, exiting...'.format(filename))
                usage(1)

    stats_file = open(final_stats, 'w')
    stats_file.write(','.join(['count', 'status', 'elapsed time\n']))

    for count, add_edges in enumerate(add_edges_list):
        status, graph, shrg_rules, runtime = PSHRG.main(add_edges)

        if status == 'fail':
            goal_count += 1
            num = goal_count
            path = fail_path

        elif status == 'pass':
            ok_count += 1
            num = ok_count
            path = pass_path
            edges_file = '{}/shrg_{}_edges'.format(path, ok_count)
            nx.write_edgelist(graph, edges_file, data=False)

        pickle_path = '{}/shrg_{}.pkl'.format(path,num)
        ae_path     = '{}/add_edges.txt'.format(path)

        with open(pickle_path, 'wb') as f:
            pickle.dump(shrg_rules, f)

        print(str(add_edges), file=open(ae_path, 'a'))

        stats_file.write('{},{},{:.5}\n'.format(count+1, status, runtime)) 

        if status == 'fail':
            continue

        # TODO: verify stergm
        stergm_graph = PSHRG.exteRnal(add_edges)
        true_graph = build_graph(add_edges)

        n = graph.number_of_nodes()
        p = graph.number_of_edges() / n*(n-1)
        er_graph = nx.erdos_renyi_graph(n, p, directed=True)
        er_graph.name = 'erdos-renyi'
        graph.name = 'pshrg'


        for g0, g1 in combinations([graph, true_graph, er_graph], 2):
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

    for arg in args:
        run(arg)

    '''
    while True:
        result.next(TIMEOUT)
        try:
            result.next(TIMEOUT)
        except multiprocessing.TimeoutError:
            print("Process took too long, aborting...")
        except StopIteration:
            break
    '''
