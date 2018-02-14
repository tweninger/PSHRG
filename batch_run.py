#!/usr/bin/python2.7

from __future__ import print_function, division
from itertools import combinations
import csv

import ast
import pickle

import multiprocessing
import os, sys

import networkx as nx
import numpy as np

import PSHRG

CORES = 2
TRIALS = range(2)
TIMEOUT = 5 * 60


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
            if (u, v) in g.edges():
                g.remove_edge(u, v)
    return g


def run(filename):

    try:
        ext = filename.split('.')[-1]
        name = filename.split('/')[-1]
    except ValueError:
        name = filename
        ext = ''

    with open(filename) as f:
        add_edges = [ast.literal_eval(l.strip()) for l in f]

    results_path = './final_dump/{}'.format(name)

    if not os.path.isdir(results_path):
        os.makedirs(results_path)


    goal_count = 0
    ok_count = 0
    time_count = 0
    overall_stats = results_path + '/overall_stats'
    print('#,status,time', file=open(overall_stats, 'w'))

    ae_path = '{}/add_edges.txt'.format(results_path)
    print('', file=open(ae_path, 'w'))

    for i, add_edge in enumerate(add_edges[: 20]):
        i += 1
        print('i = ', i)
        manager = multiprocessing.Manager()
        return_dict = manager.dict()
        p = multiprocessing.Process(target=PSHRG.main, args=(add_edge, return_dict))
        p.start()
        p.join(TIMEOUT)

        if p.is_alive():
            time_count += 1
            print('Timeout!!')
            p.terminate()
            p.join()
            print('{},timeout,{}'.format(i, TIMEOUT), file=open(overall_stats, 'a'))
            continue

        status, g_pshrg, shrg_rules, runtime = return_dict['status'], return_dict['graph'], return_dict['shrg_rules'], return_dict['time']

        if status == 'fail':
            goal_count += 1
            print('fail!')
            print('{},fail,{}'.format(i, runtime), file=open(overall_stats, 'a'))
            continue

        elif status == 'pass':
            g_pshrg.name = 'pshrg'
            ok_count += 1
            print('{},pass,{}'.format(i, runtime), file=open(overall_stats, 'a'))
            edges_file = '{}/shrg_edges_{}'.format(results_path, i)
            nx.write_edgelist(g_pshrg, edges_file, data=False)

            pickle_path = '{}/shrg_{}.pkl'.format(results_path, i)
            with open(pickle_path, 'wb') as f:
                pickle.dump(shrg_rules, f)

            print(str(add_edge), file=open(ae_path, 'a'))

            g_stergm = PSHRG.exteRnal(add_edge, results_path, i)
            g_true = build_graph(add_edge)
            g_true.name = name

            n = g_true.number_of_nodes()
            p = g_true.number_of_edges() / (n * (n - 1))
            g_er = nx.erdos_renyi_graph(n, p, directed=True)
            g_er.name = 'erdos-renyi'

            write_stats(g_true=g_true, g_pshrg=g_pshrg, g_stergm=g_stergm, g_er=g_er, count=ok_count)



def write_stats(g_true, g_pshrg, g_stergm, g_er, count):
    true_in = g_true.in_degree().values()
    true_out = g_true.out_degree().values()
    true_page = map(lambda x: round(x, 3), nx.pagerank_numpy(g_true).values())

    pshrg_in = g_pshrg.in_degree().values()
    pshrg_out = g_pshrg.out_degree().values()
    pshrg_page = map(lambda x: round(x, 3), nx.pagerank_numpy(g_pshrg).values())

    er_in = g_er.in_degree().values()
    er_out = g_er.out_degree().values()
    er_page = map(lambda x: round(x, 3), nx.pagerank_numpy(g_er).values())

    stergm_in = g_stergm.in_degree().values()
    stergm_out = g_stergm.out_degree().values()
    stergm_page = map(lambda x: round(x, 3), nx.pagerank_numpy(g_stergm).values())

    gcd_pshrg = PSHRG.GCD(g_pshrg, g_true)
    cdf_in_pshrg = PSHRG.cdf_sum(pshrg_in, true_in)
    cdf_out_pshrg = PSHRG.cdf_sum(pshrg_out, true_out)
    cdf_page_pshrg = PSHRG.cdf_sum(pshrg_page, true_page)

    gcd_er = PSHRG.GCD(g_er, g_true)
    cdf_in_er = PSHRG.cdf_sum(er_in, true_in)
    cdf_out_er = PSHRG.cdf_sum(er_out, true_out)
    cdf_page_er = PSHRG.cdf_sum(er_page, true_page)

    gcd_stergm = PSHRG.GCD(g_stergm, g_true)
    cdf_in_stergm = PSHRG.cdf_sum(stergm_in, true_in)
    cdf_out_stergm = PSHRG.cdf_sum(stergm_out, true_out)
    cdf_page_stergm = PSHRG.cdf_sum(stergm_page, true_page)

    with open('./final_dump/stats.csv', 'a') as f:
        csvwriter = csv.writer(f, quoting=csv.QUOTE_MINIMAL)
        csvwriter.writerow([g_true.name, count, g_true.order(), g_true.size(), g_pshrg.order(), g_pshrg.size(),
                            g_er.order(), g_er.size(), g_stergm.order(), g_stergm.size(),
                            gcd_pshrg, cdf_in_pshrg, cdf_out_pshrg, cdf_page_pshrg,
                            gcd_er, cdf_in_er, cdf_out_er, cdf_page_er,
                            gcd_stergm, cdf_in_stergm, cdf_out_stergm, cdf_page_stergm])

if __name__ == '__main__':
    np.seterr(all='ignore')

    if len(sys.argv) < 2:
        print('Enter list of add edges as command line args')
    else:
        run(sys.argv[1])

