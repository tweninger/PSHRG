from __future__ import division
from __future__ import print_function

import networkx

def make_clique(graph, nodes):
    for v1 in nodes:
        for v2 in nodes:
            if v1 != v2:
                graph.add_edge(v1, v2)

def count_fillin(graph, nodes):
    """How many edges would be needed to make v a clique."""
    count = 0
    for v1 in nodes:
        for v2 in nodes:
            if v1 != v2 and v2 not in graph[v1]:
                count += 1
    return count//2

def is_clique(graph, vs):
    for v1 in vs:
        for v2 in vs:
            if v1 != v2 and v2 not in graph[v1]:
                return False
    return True

def simplicial(graph, v):
    return is_clique(graph, graph[v])

def almost_simplicial(graph, v):
    for u in graph[v]:
        if is_clique(graph, set(graph[v]) - {u}):
            return True
    return False

def eliminate_node(graph, v):
    if v not in graph:
        raise KeyError("node not in")
    make_clique(graph, graph[v])
    graph.remove_node(v)

def upper_bound(graph):
    """Min-fill."""
    graph = graph.copy()
    dmax = 0
    order = []
    while len(graph) > 0:
        #d, u = min((len(graph[u]), u) for u in graph) # min-width
        d, u = min((count_fillin(graph, graph[u]), u) for u in graph)
        dmax = max(dmax, len(graph[u]))
        eliminate_node(graph, u)
        order.append(u)
    return dmax, order

def lower_bound(graph):
    """Minor-min-width"""
    graph = graph.copy()
    dmax = 0
    while len(graph) > 0:
        # pick node of minimum degree
        d, u = min((len(graph[u]), u) for u in graph)
        dmax = max(dmax, d)

        # Gogate and Dechter: minor-min-width
        nb = set(graph[u]) - {u}
        if len(nb) > 0:
            _, v = min((len(set(graph[v]) & nb), v) for v in nb)
            graph = networkx.contracted_edge(graph, (u, v), self_loops=False)
        else:
            graph.remove_node(u)
    return dmax

class Solution(object):
    pass

def quickbb(graph):
    """Gogate and Dechter, A complete anytime algorithm for treewidth. UAI
    2004. http://arxiv.org/pdf/1207.4109.pdf

    Given a permutation of the nodes (called an elimination ordering),
    for each node, remove the node and make its neighbors into a clique.
    The maximum degree of the nodes at the time of their elimination is
    the width of the tree decomposition corresponding to that ordering.
    The treewidth of the graph is the minimum over all possible
    permutations.
    """

    # Make into an undirected graph without self-loops
    g1 = networkx.Graph()
    for u in graph:
        g1.add_node(u)
        for v in graph[u]:
            if u != v:
                g1.add_edge(u, v)
    graph = g1

    best = Solution() # this gets around the lack of nonlocal in Python 2
    best.count = 0

    def bb(graph, order, f, g):
        best.count += 1
        if len(graph) < 2:
            if f < best.ub:
                assert f == g
                best.ub = f
                best.order = list(order) + list(graph)
        else:
            vs = []
            for v in graph:
                # very important pruning rule
                if simplicial(graph, v) or almost_simplicial(graph, v) and len(graph[v]) <= lb:
                    vs = [v]
                    break
                else:
                    vs.append(v)

            for v in vs:
                graph1 = graph.copy()
                eliminate_node(graph1, v)
                order1 = order + [v]
                # treewidth for current order so far
                g1 = max(g, len(graph[v])) 
                # lower bound given where we are
                f1 = max(g, lower_bound(graph1)) 
                if f1 < best.ub:
                    bb(graph1, order1, f1, g1)

    order = []
    best.ub, best.order = upper_bound(graph)
    lb = lower_bound(graph)
    if lb < best.ub:
        bb(graph, order, lb, 0)

    # Build the tree decomposition
    tree = networkx.Graph()
    def build(order):
        if len(order) < 2:
            tree.add_node(len(tree), nodes=set(order))
            return
        v = order[0]
        clique = set(graph[v])
        eliminate_node(graph, v)
        build(order[1:])
        for tv in tree:
            if clique.issubset(tree.node[tv]['nodes']):
                break
        else:
            assert False
        tnew = len(tree)
        tree.add_node(tnew, nodes=clique|{v})
        tree.add_edge(tv, tnew)
    build(best.order)
    return tree

if __name__ == "__main__":
    import fileinput
    import amr

    total = n = 0
    for line in fileinput.input():
        try:
            graph = amr.parse_amr(line)
        except amr.ParseError:
            print("parse error")
            continue
        tree = quickbb(graph)
        tw = max(len(tv)-1 for tv in tree)
        print(tw)
        total += tw
        n += 1
    print("average width:", total/n)