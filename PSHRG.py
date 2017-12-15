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
    G.name="Powerlaw-Cluster Graph"
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

def main():
    # Example From PAMI Paper
    # Graph is undirected

    ###################################
    add_edge_events = {}
    del_edge_events = {}

    g = powerlaw_cluster_graph(10,2,.2)

    print (g.edges(data=True))
    print (sorted(g.edges(data=True), key=lambda x: x[2]['t']))
    print (g.size())

    for e in g.edges_iter(data=True):
        if e[2]['t'] not in add_edge_events:
            add_edge_events[e[2]['t']] = [(e[0], e[1])]
        else:
            add_edge_events[e[2]['t']].append( (e[0], e[1]) )


    #exit()
    #add_edge_events[1] = [(1, 2), (2, 3), (1,3)]

    #add_edge_events[0] = [(2, 0), (2, 1), ]
    #add_edge_events[1] = [(3, 0), (3, 2), ]
    #add_edge_events[2] = [(4, 0), (4, 1), ]
    #add_edge_events[3] = [(5, 0), (5, 2), (6, 0), (6, 2),]
    #add_edge_events[4] = [(7, 1), (7, 3), (8, 1), (8, 7), (9, 4), (9, 2), (10, 1), (10, 4),]
    #add_edge_events[5] = [ ]
    #add_edge_events[6] = [ ]
    #add_edge_events[9] = [(11, 1), (11, 2), ]


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
    #filename = './test/pickles/dutch/full'
    
    #add_edge_filename = filename + '_add_edge.pkl'
    #with open(add_edge_filename, 'rb') as f:
    #    add_edge_events = pickle.load(f)

    #del_edge_filename = filename + '_del_edge.pkl'
    #with open(del_edge_filename, 'rb') as f:
    #    del_edge_events = pickle.load(f)
    #############
    print('Loading done!', file=sys.stderr)

    g_prev = nx.DiGraph()
    g_next = nx.DiGraph()
    events = sorted(list(set(add_edge_events.keys() + del_edge_events.keys())))

    shrg_rules = {}
    i=0
    for t in events:
        decomp_time = time()

        if t in add_edge_events:
            for u, v in add_edge_events[t]:
                g_next.add_edge(u, v, label='e')
                # # printu, v, t
        if t in del_edge_events:
            for u, v in del_edge_events[t]:
                if (u,v) in g_next:
                    g_next.remove_edge(u, v)
        nx.set_node_attributes(g_next, 'label', 'u')

        #get WCC
        if not nx.is_weakly_connected(g_next):
            g_next = max(nx.weakly_connected_component_subgraphs(g_next), key=len)

        g_union = union_graph(g_prev, g_next)
        tree_decomp_l = tree_decomposition(g_union)

        i += 1
        #if i < len(events)-2:
        #    continue

        tree_decomp = prune(tree_decomp_l[0], frozenset())
        tree_decomp = binarize(tree_decomp)

        # print_tree_decomp(tree_decomp)
        # 

        td.new_visit(tree_decomp, g_prev, g_next, shrg_rules, i)
        g_prev = g_next.copy()
        print('tree decomp #{} done in {} sec'.format(t, time() - decomp_time), file=sys.stderr)



    DEBUG = False
    # if DEBUG: print
    # if DEBUG: # print"--------------------"
    # if DEBUG: # print"- Production Rules -"
    # if DEBUG: # print"--------------------"

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

            #if nonterm and rule_tuple[1].iso == False:
            #    for n in rule_tuple[0].rhs.nodes(data=True):
            #        if not isinstance(n[1]['label'], grammar.Nonterminal):
            #            print('Candidates: ', rule_tuple)

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

    print('Parse start, time elapsed: {} sec'.format(time() - start), file=sys.stderr)

    print('Number of Rules ', len(prev_rules))

    forest = p.parse( prev_rules, [grammar.Nonterminal('0')], g_next )
    print('Parse end, time elapsed: {} sec'.format(time() - start), file=sys.stderr)
    # print'start deriving'

    # print(p.derive(p.viterbi(forest), next_rules))
    print('Derive start, time elapsed:', time() - start, 'sec', file=sys.stderr)
    p.derive(p.viterbi(forest), next_rules)
    print('Derive end, time elapsed:', time() - start, 'sec', file=sys.stderr)
    # print(p.get_rule_list(p.viterbi(forest)))
    p.get_rule_list(p.viterbi(forest))
    print('End in', time() - start, 'sec!!', file=sys.stderr)

if __name__ == "__main__":
    main()
    #cProfile.runctx('main()', globals(), locals())
