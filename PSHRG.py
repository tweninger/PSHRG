#!/usr/bin/python2.7
from __future__ import print_function


import ast
import os
import pickle
import random
import re
import sys
from time import time
import math

import hypergraphs

import grammar
import graph_parser as p
import graph_sampler as gs
import tree_decomposition as td

import subprocess
import networkx as nx
import pandas as pd
import platform
import scipy.stats

from networkx import random_graphs as rg
from collections import Counter

import numpy as np
import cProfile

DEBUG = True

logfile = 'log.txt'


def graph_checks(G):
    ## Target number of nodes
    num_nodes = G.number_of_nodes()

    if not nx.is_connected(G):
        # if DEBUG: # print"Graph must be connected";
        os._exit(1)

    if G.number_of_selfloops() > 0:
        # if DEBUG: # print"Graph must be not contain self-loops";
        os._exit(1)


def matcher(lhs, N):
    if lhs == "S":
        return [("S", "S")]
    m = []
    for x in N:
        if len(x) == lhs.count(",") + 1:
            i = 0
            for y in lhs.split(","):
                m.append((x[i], y))
                i += 1
            return m


def print_tree_decomp(tree, indent=""):
    (node, children) = tree
    # printindent, node
    [print_tree_decomp(child, indent = indent + "  ") for child in children]


def grow(rule_list, grammar, diam=0):
    D = list()
    newD = diam
    H = list()
    N = list()
    N.append(["S"])  # starting node
    ttt = 0
    # pick non terminal
    num = 0
    for r in rule_list:
        rule = grammar.by_id[r][0]
        lhs_match = matcher(rule.lhs, N)
        e = []  # edge list
        match = []
        for tup in lhs_match:
            match.append(tup[0])
            e.append(tup[1])
        lhs_str = "(" + ",".join(str(x) for x in sorted(e)) + ")"

        new_idx = {}
        n_rhs = rule.rhs
        # if 0: # printlhs_str, "->", n_rhs
        for x in n_rhs:
            new_he = []
            he = x.split(":")[0]
            term_symb = x.split(":")[1]
            for y in he.split(","):
                if y.isdigit():  # y is internal node
                    if y not in new_idx:
                        new_idx[y] = num
                        num += 1
                        if diam > 0 and num >= newD and len(H) > 0:
                            newD = newD + diam
                            newG = nx.Graph()
                            for e in H:
                                if (len(e) == 1):
                                    newG.add_node(e[0])
                                else:
                                    newG.add_edge(e[0], e[1])
                                    # D.append(metrics.bfs_eff_diam(newG, 20, 0.9))
                    new_he.append(new_idx[y])
                else:  # y is external node
                    for tup in lhs_match:  # which external node?
                        if tup[1] == y:
                            new_he.append(tup[0])
                            break
            # prod = "(" + ",".join(str(x) for x in new_he) + ")"
            if term_symb == "N":
                N.append(sorted(new_he))
            elif term_symb == "T":
                H.append(new_he)  # new (h)yper(e)dge
                # # printn_rhs, new_he
        match = sorted(match)
        N.remove(match)

    newG = nx.Graph()
    for e in H:
        if (len(e) == 1):
            newG.add_node(e[0])
        else:
            newG.add_edge(e[0], e[1])

    return newG, D


def tree_decomposition(g):
    """
      Rule extraction procedure
    """
    if g is None: return []

    g.remove_edges_from(g.selfloop_edges())
    giant_nodes = max(nx.connected_component_subgraphs(g), key=len)
    g = nx.subgraph(g, giant_nodes)

    graph_checks(g)

    tree_decomp_l = []
    if g.number_of_nodes() >= 500:
        for g_prime in gs.rwr_sample(g, 2, 300):
            _t = td.quickbb(g_prime)
            root = list(_t)[0]
            _t = td.make_rooted(_t, root)
            _t = binarize(_t)
            tree_decomp_l.append(_t)
    else:
        _t = td.quickbb(g)
        root = list(_t)[0]
        _t = td.make_rooted(_t, root)
        #_t = binarize(_t)
        tree_decomp_l.append(_t)

    return tree_decomp_l


def probabilistic_shrg():
    prod_rules = {}
    # if DEBUG: print
    # if DEBUG: # print"--------------------"
    # if DEBUG: # print"- Production Rules -"
    # if DEBUG: # print"--------------------"

    for k in prod_rules.iterkeys():
        # if DEBUG: # printk
        s = 0
        for d in prod_rules[k]:
            s += prod_rules[k][d]
        for d in prod_rules[k]:
            prod_rules[k][d] = float(prod_rules[k][d]) / float(s)  # normailization step to create probs not counts.
            # if DEBUG: # print'\t -> ', d, prod_rules[k][d]

    # pp.pprint(prod_rules)

    rules = []
    id = 0
    for k, v in prod_rules.iteritems():
        sid = 0
        for x in prod_rules[k]:
            rhs = re.findall("[^()]+", x)
            rules.append(("r%d.%d" % (id, sid), "%s" % re.findall("[^()]+", k)[0], rhs, prod_rules[k][x]))
            # if DEBUG: # print("r%d.%d" % (id, sid), "%s" % re.findall("[^()]+", k)[0], rhs, prod_rules[k][x])
            sid += 1
        id += 1

    return rules


def try_combination(lhs, N):
    for i in range(0, len(N)):
        n = N[i]
        if lhs[0] == "S":
            break
        if len(lhs) == len(n):
            t = []
            for i in n:
                t.append(i)
            random.shuffle(t)
            return zip(t, lhs)
    return []


def union_graph(g_prev, g_next):
    g_union = nx.Graph()
    for n in g_prev.nodes():
        g_union.add_node(n)
    for n in g_next.nodes():
        g_union.add_node(n)

    for u, v in g_prev.edges():
        g_union.add_edge(u, v)
    for u, v in g_next.edges():
        g_union.add_edge(u, v)

    return g_union


def binarize(tree):
    (node, children) = tree
    children = [binarize(child) for child in children]
    if len(children) <= 2:
        return (node, children)
    else:
        # Just make copies of node.
        # This is the simplest way to do it, but it might be better to trim unnecessary members from each copy.
        # The order that the children is visited is arbitrary.
        full_node = node.copy()
        node = node.intersection(children[0][0] | children[1][0])
        binarized = (node, children[:2])
        for child in children[2:]:
            node = full_node.intersection(binarized[0] | child[0])
            binarized = (node, [binarized, child])
        return (full_node, binarized[1])

def prune(tree, parent):
    (node, children) = tree
    children = [prune(child, node) for child in children]
    #prune nones
    newchildren = []
    for child in children:
        if type(child) is list:
            for c in child:
                if c[0] is not None:
                    newchildren.append(c)
        else:
            if child[0] is not None:
                newchildren.append( child )
    children = newchildren
    if len(children) == 0 and len(node.difference(parent)) == 0:
        return (None, [])
    elif (len(node.difference(parent)) == 0):
        return children
    else:
        return (node, children)

def powerlaw_cluster_graph(n, m, p, seed=None):
    p = 0
    if m < 1 or n < m:
        raise nx.NetworkXError(\
              "NetworkXError must have m>1 and m<n, m=%d,n=%d"%(m,n))

    if p > 1 or p < 0:
        raise nx.NetworkXError(\
              "NetworkXError p must be in [0,1], p=%f"%(p))
    if seed is not None:
        random.seed(seed)

    G=rg.empty_graph(m, create_using=nx.DiGraph()) # add m initial nodes (m0 in barabasi-speak)
    G.name="PL {} {} {}".format(n, m, p)
    repeated_nodes=G.nodes()  # list of existing nodes to sample from
                           # with nodes repeated once for each adjacent edge
    source=m               # next node is m
    t = 0
    while source<n:        # Now add the other n-1 nodes
        possible_targets = rg._random_subset(repeated_nodes,m)
        # do one preferential attachment for new node
        target=possible_targets.pop()
        G.add_edge(source,target, t=t)
        repeated_nodes.append(target) # add one node to list for each new link
        count=1
        while count<m:  # add m-1 more new links
            if random.random()<p: # clustering step: add triangle
                neighborhood=[nbr for nbr in G.neighbors(target) \
                               if not G.has_edge(source,nbr) \
                               and not nbr==source]
                if neighborhood: # if there is a neighbor without a link
                    nbr=random.choice(neighborhood)
                    G.add_edge(source,nbr, t=t) # add triangle
                    repeated_nodes.append(nbr)
                    count=count+1
                    continue # go to top of while loop
            # else do preferential attachment step if above fails
            target=possible_targets.pop()
            G.add_edge(source,target,t=t)
            repeated_nodes.append(target)
            count = count + 1
        t += 1

        repeated_nodes.extend([source]*m)  # add source node to list m times
        source += 1
    return G


def external_rage(G,netname):

    G = nx.Graph(G)
    # giant_nodes = max(nx.connected_component_subgraphs(G), key=len)
    giant_nodes = sorted(nx.connected_component_subgraphs(G), key=len, reverse=True)

    G = nx.subgraph(G, giant_nodes[0])
    tmp_file = "tmp_{}.txt".format(netname)
    with open(tmp_file, 'w') as tmp:
        for e in G.edges_iter():
            tmp.write(str(int(e[0])+1) + ' ' + str(int(e[1])+1) + '\n')

    if 'Windows' in platform.platform():
        args = ("./RAGE_windows.exe", tmp_file)
    elif 'Linux' in platform.platform():
        args = ('./RAGE_linux', tmp_file)
    else:
        args = ("./RAGE", tmp_file)

    popen = subprocess.Popen(args, stdout=subprocess.PIPE)
    
    popen.wait()
    output = popen.stdout.read()

    # Results are hardcoded in the exe
    df = pd.read_csv('./Results/UNDIR_RESULTS_tmp_{}.csv'.format(netname),
                     header=0, sep=',', index_col=0)
    df = df.drop('ASType', 1)
    return df


def tijana_eval_compute_gcm(G_df):

    l = len(G_df.columns)
    gcm = np.zeros((l, l))
    i = 0
    for column_G in G_df:
        j = 0
        for column_H in G_df:
            gcm[i, j] = scipy.stats.spearmanr(G_df[column_G].tolist(), G_df[column_H].tolist())[0]
            if scipy.isnan(gcm[i, j]):
                gcm[i, j] = 1.0
            j += 1
        i += 1
    return gcm


def tijana_eval_compute_gcd(gcm_g, gcm_h):

    if len(gcm_h) != len(gcm_g):
        raise "Graphs must be same size"
    s = 0
    for i in range(0, len(gcm_g)):
        for j in range(i, len(gcm_h)):
            s += math.pow((gcm_g[i, j] - gcm_h[i, j]), 2)

    gcd = math.sqrt(s)
    return gcd


def cdf_sum(data1, data2):
    data1, data2 = map(np.asarray, (data1, data2))
    n1 = data1.shape[0]
    n2 = data2.shape[0]
    n1 = len(data1)
    n2 = len(data2)
    data1 = np.sort(data1)
    data2 = np.sort(data2)
    data_all = np.concatenate([data1,data2])
    cdf1 = np.searchsorted(data1,data_all,side='right')/(1.0*n1)
    cdf2 = (np.searchsorted(data2,data_all,side='right'))/(1.0*n2)
    d = np.sum(np.absolute(cdf1-cdf2))
    return round(d, 3)


def GCD(h1, h2):
    df_g = external_rage(h1, 'Orig')
    df_h = external_rage(h2, 'Test')
    gcm_g = tijana_eval_compute_gcm(df_g)
    gcm_h = tijana_eval_compute_gcm(df_h)
    gcd = tijana_eval_compute_gcd(gcm_g, gcm_h)
    return round(gcd, 3)

def cmp(g0, g1, filename=""):
    g0_in = g0.in_degree().values()
    g1_in = g1.in_degree().values()
    g0_out = g0.out_degree().values()
    g1_out = g1.out_degree().values()
    g0_page = map(lambda x: round(x, 3), nx.pagerank_numpy(g0).values())
    g1_page = map(lambda x: round(x, 3), nx.pagerank_numpy(g1).values())

    with open(filename + "_separate.txt", "w") as cmp_file:
        cmp_file.write(",{},{}\n".format(g0.name, g1.name))
        cmp_file.write("nodes,{},{}\n".format(g0.order(), g1.order()))
        cmp_file.write("edges,{},{}\n".format(g0.size(), g1.size()))
        cmp_file.write("in-deg,{},{}\n".format(g0_in, g1_in))
        cmp_file.write("out-deg,{},{}\n".format(g0_out, g1_out))
        cmp_file.write("nodes,{},{}\n")
        cmp_file.write("nodes,{},{}\n")

    with open(filename + "_together.txt", "w") as cmp_file:
        cmp_file.write("gcd,cdf-in,cdf-out,pagerank")
        cmp_file.write("{},{},{},{}\n".format(GCD(g0, g1),
                                            cdf_sum(g0_in, g1_in),
                                            cdf_sum(g0_out, g1_out),
                                            cdf_sum(g0_page, g1_page)))


def exteRnal(add_edge_events):
    """
    Works only for add_edge_events
    """

    max_t = max(add_edge_events.keys())
    name = 'pl{}'.format(max_t + 3)
    r_comms = []
    # r_comms.append("install.packages(c('statnet'), repos='http://cran.us.r-project.org', dependencies=T)")
    r_comms.append("""if(!require(statnet)){
    install.packages('statnet', repos='http://cran.us.r-project.org', dependencies=T)
    library(statnet)}""")
    # r_comms.append("library(statnet)")
    r_comms.append('{} <- network.initialize(0)'.format(name))

    r_comms.append('add.vertices.active({}, 2, onset=0, terminus={})'.format(name, max_t + 1))

    max_t = max(add_edge_events.keys())
    for t in sorted(add_edge_events.keys()):
        r_comms.append('\nadd.vertices.active({}, 1, onset={}, terminus={}) #{}'.format(name, t, max_t + 1, t + 3))
        for u, v in add_edge_events[t]:
            r_comms.append(
                'add.edges.active({}, tail={}, head={}, onset={}, terminus={})'.format(name, u + 1, v + 1, t,
                                                                                       max_t + 1))

    r_comms.append('\n#plots\npar(mfrow=c(2, 2))')
    r_comms.append("plot({}, main='whole graph', displaylabels=T)".format(name))
    for t in sorted(add_edge_events.keys()):
        r_comms.append("plot(network.extract({}, at={}), main='t={}', displaylabels=T)".format(name, t, t))

    r_comms.append("""\n{}.fit <- stergm({}, 
                       formation=~edges+gwesp(0,fixed=T),
                       dissolution=~edges,
                       estimate='CMLE',
                       times=0:{},
                       verbose=T)""".format(name, name, max_t - 1))

    r_comms.append("\n{}.sim <- simulate.stergm({}.fit, nsim=1, nw.start={})".format(name, name, max_t))
    r_comms.append("mat <- as.matrix({}.sim, matrix.type='edgelist')".format(name))
    r_comms.append("write.table(mat, file='{}_stergm.txt', sep=' ', quote=F, col.names=F, row.names=F)".format(name))
    print('\n'.join(r_comms), file=open('{}_script.r'.format(name), 'w'))

    exit_code = subprocess.call("cat {}_script.r | R --no-save".format(name), shell=True)

    # In case of error, execute 'sudo conda install -c r r-irkernel zeromq' and rerun this code

    if exit_code != 0:
        print('Error running STERGM', file=open(logfile, 'a'))
        return None
    g_stergm = nx.read_edgelist('{}_stergm.txt'.format(name), create_using=nx.DiGraph())
    return g_stergm


def main(add_edge_events = {}, del_edge_events = {}):
    start = time()
    print(add_edge_events, file=open(logfile, 'a'))

    g_prev = nx.DiGraph()
    g_next = nx.DiGraph()

    events = sorted(list(set(add_edge_events.keys() + del_edge_events.keys())))
    
    name = None

    shrg_rules = {}
    i=0
    for t in events[:-1]:
        decomp_time = time()

        if t in add_edge_events:
            for u, v in add_edge_events[t]:
                g_next.add_edge(u, v, label='e')
        if t in del_edge_events:
            for u, v in del_edge_events[t]:
                if (u,v) in g_next.edges():
                    g_next.remove_edge(u, v)
        nx.set_node_attributes(g_next, 'label', 'u')

        #get WCC
        if not nx.is_weakly_connected(g_next):
            g_next = max(nx.weakly_connected_component_subgraphs(g_next), key=len)

        g_union = union_graph(g_prev, g_next)
        tree_decomp_l = tree_decomposition(g_union)

        i += 1

        tree_decomp = tree_decomp_l[0]
        tree_decomp = prune(tree_decomp, frozenset())
        tree_decomp = binarize(tree_decomp)
        tree_decomp = prune(tree_decomp, frozenset())

        td.new_visit(tree_decomp, g_prev, g_next, shrg_rules, i)
        g_prev = g_next.copy()
        print('tree decomp #{} done in {} sec'.format(t, time() - decomp_time), file=open(logfile, 'a'))

    prev_rules = []
    next_rules = []
    anchor_candidates = []

    for lhs_set in shrg_rules.values():
        for rule_tuple in lhs_set:
            nonterm = False
            for n in rule_tuple[0].rhs.nodes(data=True):
                if isinstance(n[1]['label'], grammar.Nonterminal):
                    nonterm = True
                    break
            if not nonterm and rule_tuple[1].time == i and rule_tuple[1].iso == False:
                for n in rule_tuple[0].rhs.nodes(data=True):
                    if 'external' not in n[1] and not isinstance(n[1]['label'], grammar.Nonterminal):
                        anchor_candidates.append( (n[1]['oid'], rule_tuple) )

    print('Number of Anchors', len(anchor_candidates), file=open(logfile, 'a'))
    anchors = random.sample(anchor_candidates, len(anchor_candidates))
    for anchor in anchors:
        oid, rule = anchor
        prev, next = rule
        for n in prev.rhs.nodes(data=True):
            if 'oid' in n[1] and n[1]['oid'] == oid:
                n[1]['label'] = oid
        for n in next.rhs.nodes(data=True):
            if 'oid' in n[1] and n[1]['oid'] == oid:
                n[1]['label'] = oid
                print('label changed to oid', rule[1].id, rule[1].time, n, file=open(logfile, 'a'))

        for n in g_next.nodes(data=True):
            if n[0] == oid:
                n[1]['label'] = oid

        for n in g_prev.nodes(data=True):
            if n[0] == oid:
                n[1]['label'] = oid

    for lhs_set in shrg_rules.values():
        s = 0
        for rule_tuple in lhs_set:
            prev, next = rule_tuple
            s += prev.weight

        for rule_tuple in lhs_set:
            rule_tuple[1].weight /= float(s)
            next_rules.append(rule_tuple[1])

            rule_tuple[0].weight /= float(s)
            prev_rules.append(rule_tuple[0])

    assert len(prev_rules) == len(next_rules)

    print('Parse start, time elapsed: {} sec'.format(time() - start), file=open(logfile, 'a'))

    print('Number of Rules ', len(prev_rules), file=open(logfile, 'a'))

    forest = p.parse( prev_rules, [grammar.Nonterminal('0')], g_next )
    print('Parse end, time elapsed: {} sec'.format(time() - start), file=open(logfile, 'a'))

    try:
        new_g = p.derive(p.viterbi(forest), next_rules)
    except KeyError:
        print('Goal error!', file=open(logfile, 'a'))
        return 'fail', None, shrg_rules, time() - start

    h_shrg = nx.DiGraph()
    for e in hypergraphs.edges(new_g):
        h_shrg.add_edge(e.h[0], e.h[1])

    return 'pass', h_shrg, shrg_rules, time() - start
