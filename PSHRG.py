from __future__ import print_function

import os
import pickle
import random
import re
import sys
from time import time

import networkx as nx

import grammar
import graph_parser as p
import graph_sampler as gs
import tree_decomposition as td
from collections import Counter
import numpy as np
import scipy
import cProfile

DEBUG = True


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
    from networkx import random_graphs as rg
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
    import subprocess
    import networkx as nx
    import  pandas as pd
    from os.path import expanduser

    G = nx.Graph(G)
    # giant_nodes = max(nx.connected_component_subgraphs(G), key=len)
    giant_nodes = sorted(nx.connected_component_subgraphs(G), key=len, reverse=True)

    G = nx.subgraph(G, giant_nodes[0])
    tmp_file = "tmp_{}.txt".format(netname)
    with open(tmp_file, 'w') as tmp:
        for e in G.edges_iter():
            tmp.write(str(int(e[0])+1) + ' ' + str(int(e[1])+1) + '\n')

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
    import scipy.stats

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
    import math

    if len(gcm_h) != len(gcm_g):
        raise "Graphs must be same size"
    s = 0
    for i in range(0, len(gcm_g)):
        for j in range(i, len(gcm_h)):
            s += math.pow((gcm_g[i, j] - gcm_h[i, j]), 2)

    gcd = math.sqrt(s)
    return gcd

def KL_dist(ds1, ds2):
    v1 = []
    v2 = []
    for d in sorted(ds1.keys()):
        if d in ds2:
            v1.append(ds1[d])
            v2.append(ds2[d])
    if len(v1) == 0:
        return None
    return round(scipy.stats.entropy(v1, v2), 3)

def GCD(h1, h2):
    df_g = external_rage(h1, 'Orig')
    df_h = external_rage(h2, 'Test')
    gcm_g = tijana_eval_compute_gcm(df_g)
    gcm_h = tijana_eval_compute_gcm(df_h)
    gcd = tijana_eval_compute_gcd(gcm_g, gcm_h)
    return round(gcd, 3)

def cmp(h1, h2):
    """
    Compares two graphs h1 and h2
    """
    print('\n------Statistics-------\n')
    print('n1 = {}, n2 = {}'.format(h1.order(), h2.order()))
    print('m1 = {}, m2 = {}'.format(h1.size(), h2.size()))

    print('\nGCD: ', GCD(h1, h2))

    print('\nKL stats\n')
    # In-degree
    in1 = Counter(h1.in_degree().values())
    in2 = Counter(h2.in_degree().values())
    print('In-degree:', KL_dist(in1, in2))

    # Out-degree
    out1 = Counter(h1.out_degree().values())
    out2 = Counter(h2.out_degree().values())
    print('Out-degree:', KL_dist(out1, out2))

    # PageRank
    pr1 = Counter(map(lambda x: round(x, 3), nx.pagerank_numpy(h1).values()))
    pr2 = Counter(map(lambda x: round(x, 3), nx.pagerank_numpy(h2).values()))
    print('PageRank: ', KL_dist(pr1, pr2))

    print('-------------------------')

    return

def main():

    add_edge_events = {}
    del_edge_events = {}

    g = powerlaw_cluster_graph(8,2,.2)
    print(g.name)
    #print (g.edges(data=True))
    #print (sorted(g.edges(data=True), key=lambda x: x[2]['t']))
    #print (g.size())

    for e in g.edges_iter(data=True):
        if e[2]['t'] not in add_edge_events:
            add_edge_events[e[2]['t']] = [(e[0], e[1])]
        else:
            add_edge_events[e[2]['t']].append( (e[0], e[1]) )


    #exit()
    #add_edge_events[1] = [(1, 2), (2, 3), (1,3)]

    #add_edge_events[0] = [(2, 0), (2, 1)]
    #add_edge_events[1] = [(3, 0), (3, 2), (4, 0), (4, 1)]
    #add_edge_events[2] = [(5, 0), (5, 2)]
    #add_edge_events[3] = [(6, 0), (6, 3)]

    #del_edge_events[2] = [(2, 0)]
    #add_edge_events[5] = [ ]
    #add_edge_events[6] = [ ]
    #add_edge_events[9] = [(11, 1), (11, 2), ]

    #add_edge_events = {0: [(0, 1), (0, 3), (1, 2), (2, 3)], 1: [(2, 4), (3, 5), (4, 5)], 2: [(4, 6), (5, 7), (6, 7)],
    # 3: [(6, 8), (7, 9), (8, 9)]}


    #add_edge_events[0] = [(0, 1), (1, 2), ]
    #add_edge_events[1] = [(2, 3), (3, 4), ]
    #add_edge_events[2] = [(4, 5), (5, 6), ]
    #add_edge_events[3] = [(6, 7), (7, 8), ]

    # del_edge_events[1] = [(1, 3)]

    ### Read pickled add and del_edge events ##########
    start = time()
    # filename = './test/pickles/enron/5'
    # filename = './test/pickles/enron/10'
    # filename = './test/pickles/enron/full'

    # filename = './test/pickles/dutch/23'
    #filename = './test/pickles/dutch/3'
    # filename = './test/pickles/dutch/full'
    # filename = './test/pickles/classrooms/'
    # #
    # add_edge_filename = filename + 'add.pkl'
    # with open(add_edge_filename, 'rb') as f:
    #    add_edge_events = pickle.load(f)
    # #
    # del_edge_filename = filename + 'del.pkl'
    # with open(del_edge_filename, 'rb') as f:
    #    del_edge_events = pickle.load(f)
    #############
    print('Loading done!', file=sys.stderr)

    g_prev = nx.DiGraph()
    g_next = nx.DiGraph()

    events = sorted(list(set(add_edge_events.keys() + del_edge_events.keys())))

    print(add_edge_events)

    # add_edge_events = {0: [(2, 0), (2, 1)], 1: [(3, 0), (3, 2)], 2: [(4, 1), (4, 2)], 3: [(5, 0), (5, 1)], 4: [(6, 1), (6, 2)]}
    # add_edge_events = {0: [(2, 0), (2, 1)], 1: [(3, 0), (3, 2)], 2: [(4, 0), (4, 2)], 3: [(5, 0), (5, 2)], 4: [(6, 0), (6, 2)]}
    # add_edge_events = {0: [(2, 0), (2, 1)], 1: [(3, 0), (3, 2)], 2: [(4, 2), (4, 3)], 3: [(5, 0), (5, 3)], 4: [(6, 0), (6, 4)]}
    add_edge_events = {0: [(2, 0), (2, 1)], 1: [(3, 1), (3, 2)], 2: [(4, 2), (4, 3)], 3: [(5, 0), (5, 2)], 4: [(6, 2), (6, 3)], 5: [(7, 2), (7, 5)]}

    shrg_rules = {}
    i=0
    for t in events[: -1]:
        decomp_time = time()

        if t in add_edge_events:
            for u, v in add_edge_events[t]:
                g_next.add_edge(u, v, label='e')
                # # printu, v, t
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
        print('tree decomp #{} done in {} sec'.format(t, time() - decomp_time), file=sys.stderr)


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

    print('Number of Anchors', len(anchor_candidates))
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
                print('label changed to oid', rule[1].id, rule[1].time, n)

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

    #(prev_rules, next_rules) = normalize_shrg(prev_rules, next_rules)
    assert len(prev_rules) == len(next_rules)

    print('Parse start, time elapsed: {} sec'.format(time() - start))

    print('Number of Rules ', len(prev_rules))

    forest = p.parse( prev_rules, [grammar.Nonterminal('0')], g_next )
    print('Parse end, time elapsed: {} sec'.format(time() - start))
    # print'start deriving'

    new_g = p.derive(p.viterbi(forest), next_rules)
    print()
    print('new Graph:')
    import hypergraphs
    # print ('Edges: ', len(hypergraphs.edges(new_g)))
    h_prime = nx.DiGraph()
    for e in hypergraphs.edges(new_g):
        # print(e)
        h_prime.add_edge(e.h[0], e.h[1])

    # TODO: Satyaki
    h_true = nx.DiGraph()
    for t in events:
        if t in add_edge_events:
            for u, v in add_edge_events[t]:
                h_true.add_edge(u, v)
        if t in del_edge_events:
            for u, v in del_edge_events[t]:
                h_true.remove_edge(u, v)

    cmp(h_prime, h_true)

    print('End in', time() - start, 'sec!!')

if __name__ == "__main__":
    np.seterr(all='ignore')
    main()
