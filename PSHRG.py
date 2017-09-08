import os
import random
import re

import networkx as nx

import grammar
import amr
import hypergraphs
import graph_parser as p
import graph_sampler as gs
import probabilistic_cfg as pcfg
import probabilistic_gen as pg
import tree_decomposition as td

# prod_rules = {}
DEBUG = True


def graph_checks(G):
    ## Target number of nodes
    num_nodes = G.number_of_nodes()

    if not nx.is_connected(G):
        if DEBUG: print "Graph must be connected";
        os._exit(1)

    if G.number_of_selfloops() > 0:
        if DEBUG: print "Graph must be not contain self-loops";
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


def binarize(tree):
    (node, children) = tree
    children = [binarize(child) for child in children]
    if len(children) <= 2:
        return (node, children)
    else:
        # Just make copies of node.
        # This is the simplest way to do it, but it might be better to trim unnecessary members from each copy.
        # The order that the children is visited is arbitrary.
        binarized = (node, children[:2])
        for child in children[2:]:
            binarized = (node, [binarized, child])
        return binarized


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
        if 0: print lhs_str, "->", n_rhs
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
                # print n_rhs, new_he
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
        _t = binarize(_t)
        tree_decomp_l.append(_t)

    return tree_decomp_l


def probabilistic_shrg():
    prod_rules = {}
    if DEBUG: print
    if DEBUG: print "--------------------"
    if DEBUG: print "- Production Rules -"
    if DEBUG: print "--------------------"

    for k in prod_rules.iterkeys():
        if DEBUG: print k
        s = 0
        for d in prod_rules[k]:
            s += prod_rules[k][d]
        for d in prod_rules[k]:
            prod_rules[k][d] = float(prod_rules[k][d]) / float(s)  # normailization step to create probs not counts.
            if DEBUG: print '\t -> ', d, prod_rules[k][d]

    # pp.pprint(prod_rules)

    rules = []
    id = 0
    for k, v in prod_rules.iteritems():
        sid = 0
        for x in prod_rules[k]:
            rhs = re.findall("[^()]+", x)
            rules.append(("r%d.%d" % (id, sid), "%s" % re.findall("[^()]+", k)[0], rhs, prod_rules[k][x]))
            if DEBUG: print ("r%d.%d" % (id, sid), "%s" % re.findall("[^()]+", k)[0], rhs, prod_rules[k][x])
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
        binarized = (node, children[:2])
        for child in children[2:]:
            binarized = (node, [binarized, child])
        return binarized

def prune(tree, parent):
    (node, children) = tree
    children = [prune(child, node) for child in children]
    #prune nones
    newchildren = []
    for child in children:
        if child[0] is not None:
            newchildren.append( child )
    children = newchildren
    if len(children) == 0 and len(node.difference(parent)) == 0:
        return (None, [])
    else:
        return (node, children)


def normalize_shrg(prev_rules, next_rules):
    #TODO - Satyaki get to work!
    """Condense rule set so that isomorphic rules are combined and counted"""
    return (prev_rules, next_rules)


def main():
    # Example From PAMI Paper
    # Graph is undirected
    add_edge_events = {}
    del_edge_events = {}

    #add_edge_events[1] = [(1, 2), (2, 3), (1,3)]

    #add_edge_events[1] = [(1,2), (2,3), (3,1)]
    #add_edge_events[1] = [(1, 2), (2, 1), (2, 3), (3, 2), (3, 4), (5, 3), (4, 3), (1, 5), (1, 6), (2, 6), (6, 3)]
    add_edge_events[1] = [(1, 2), (2, 3), (3, 4),  ]
    add_edge_events[2] = [(4, 5), (5, 6), (6, 7)]
    add_edge_events[3] = [(1, 5), (1, 6), (2, 6), (6, 3)]
    add_edge_events[4] = [(5, 1), ]

    # del_edge_events[1] = [(1, 3)]

    g_prev = nx.DiGraph()
    g_next = nx.DiGraph()
    events = sorted(list(set(add_edge_events.keys() + del_edge_events.keys())))

    shrg_rules = {}
    for t in events:
        if t in add_edge_events:
            for u, v in add_edge_events[t]:
                g_next.add_edge(u, v, label='e')
        if t in del_edge_events:
            for u, v in del_edge_events[t]:
                g_next.remove_edge(u, v)
        nx.set_node_attributes(g_next, 'label', 'u')
        g_union = union_graph(g_prev, g_next)
        tree_decomp_l = tree_decomposition(g_union)
        #tree_decomp = tree_decomp_l[0]
        tree_decomp = binarize(tree_decomp_l[0])
        tree_decomp = prune(tree_decomp, frozenset())
        td.new_visit(tree_decomp, g_prev, g_next, shrg_rules)
        g_prev = g_next

    print(tree_decomp)

    if DEBUG: print
    if DEBUG: print "--------------------"
    if DEBUG: print "- Production Rules -"
    if DEBUG: print "--------------------"

    prev_rules = []
    next_rules = []
    for lhs_set in shrg_rules.values():
        for rule_tuple in lhs_set:
            prev_rules.append(rule_tuple[0])

    for lhs_set in shrg_rules.values():
        for rule_tuple in lhs_set:
            next_rules.append(rule_tuple[1])


    (prev_rules, next_rules) = normalize_shrg(prev_rules, next_rules)
    assert len(prev_rules) == len(next_rules)

    forest = p.parse( next_rules, [grammar.Nonterminal('0')], g_next )

    print(p.derive(p.viterbi(forest), next_rules))
    print(p.get_rule_list(p.viterbi(forest)))


if __name__ == "__main__":
    main()
