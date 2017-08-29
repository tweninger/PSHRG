import os
import random
import re

import networkx as nx

import graph_parser.grammar
import graph_parser.graph
import graph_parser.parser
import graph_sampler as gs
import probabilistic_cfg as pcfg
import probabilistic_gen as pg
import tree_decomposition as td
import graph_parser.amr

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

    if DEBUG: print
    if DEBUG: print "--------------------"
    if DEBUG: print "-Tree Decomposition-"
    if DEBUG: print "--------------------"
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




def parse(rules, nx_g):

    h = graph_parser.amr.format_amr(nx_g)

    g = []
    for (_id, lhs, rhs_prev, rhs_next, prob) in rules:
        prev_gl, nt_map = str_to_graphlet(rhs_prev)
        next_gl, _ = str_to_graphlet(rhs_next, nt_map)
        lhs_size = 0
        if lhs != 'S':
            lhs_size = len(lhs.split(','))
        r = graph_parser.grammar.Rule(graph_parser.grammar.Nonterminal(str(lhs_size)), next_gl, prob, prev_gl)
        r.id = _id
        g.append(r)

    for x in g:
        print x

    print h

    return graph_parser.parser.parse(g, [graph_parser.grammar.Nonterminal('0')], h)

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

def prune(tree):
    (node, children) = tree
    children = [prune(child) for child in children]
    if len(children) > 0 and len(children[0][0].difference(node)) == 0:
        return (node, [])
    else:
        return (node, children)



def main():
    # Example From PAMI Paper
    # Graph is undirected
    add_edge_events = {}
    del_edge_events = {}

    #add_edge_events[1] = [(1, 2), (1, 5), (2, 3), (2, 4),(3, 4), (3, 5), (4, 6), (5, 6)]
    #add_edge_events[1] = [(2, 1)]
    add_edge_events[1] = [(1, 2), (2, 1), (2, 3), (3,2), (4,3), (3,4), (4,5), (5,4)]
    #add_edge_events[2] = [(2, 3), (3, 2), (1, 3), (3, 1)]

    # del_edge_events[1] = [(1, 3)]

    g_prev = nx.DiGraph()
    g_next = nx.DiGraph()
    events = sorted(list(set(add_edge_events.keys() + del_edge_events.keys())))

    shrg_rules = {}
    for t in events:
        if t in add_edge_events:
            for u, v in add_edge_events[t]:
                g_next.add_edge(u, v)
        if t in del_edge_events:
            for u, v in del_edge_events[t]:
                g_next.remove_edge(u, v)
        g_union = union_graph(g_prev, g_next)
        tree_decomp_l = tree_decomposition(g_union)
        tree_decomp = tree_decomp_l[0]
        #tree_decomp = binarize(tree_decomp_l[0])
        #tree_decomp = prune(tree_decomp)
        td.new_visit(tree_decomp, g_prev, g_next, shrg_rules)
        g_prev = g_next

    if DEBUG: print
    if DEBUG: print "--------------------"
    if DEBUG: print "- Production Rules -"
    if DEBUG: print "--------------------"

    for k in shrg_rules.iterkeys():
        if DEBUG: print k
        s = 0
        for d in shrg_rules[k]:
            s += shrg_rules[k][d]
        for d in shrg_rules[k]:
            shrg_rules[k][d] = float(shrg_rules[k][d]) / float(s)  # normailization step to create probs not counts.
            if DEBUG: print '\t -> ', d, shrg_rules[k][d]

    # pp.pprint(prod_rules)

    rules = []
    id = 0
    for k, v in shrg_rules.iteritems():
        sid = 0
        for x in shrg_rules[k]:
            rhs_prev = re.findall("[^()]+", x[0])
            rhs_next = re.findall("[^()]+", x[1])
            rules.append(
                ("r%d.%d" % (id, sid), "%s" % re.findall("[^()]+", k)[0], rhs_prev, rhs_next, shrg_rules[k][x]))
            if DEBUG: print (
            "r%d.%d" % (id, sid), "%s" % re.findall("[^()]+", k)[0], rhs_prev, rhs_next, shrg_rules[k][x])
            sid += 1
        id += 1

    g = pcfg.Grammar('S')
    for (id, lhs, rhs_prev, rhs_next, prob) in rules:
        g.add_rule(pcfg.Rule(id, lhs, (rhs_prev, rhs_next), prob, True))
    print '> prod rules added to Grammar g'  #
    forest = parse(rules, g_next )
    print graph_parser.parser.derive(forest.viterbi())
    exit()

    g.set_max_size(15, 1)
    print '> max-size set.'

    rids = g.sample(15, 1)
    print rids

    new_graph = pg.gen(rids, g, 0)

    print "nodes: ", new_graph.number_of_nodes()
    print "edges: ", new_graph.number_of_edges()
    print
    print


if __name__ == "__main__":
    main()
