from collections import defaultdict
import itertools
import networkx as nx
from num_to_word import num_to_word
import grammar



def make_clique(graph, nodes):
    for v1 in nodes:
        for v2 in nodes:
            if v1 != v2:
                graph[v1].add(v2)


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
        if is_clique(graph, graph[v] - {u}):
            return True
    return False


def eliminate_node(graph, v):
    make_clique(graph, graph[v])
    delete_node(graph, v)


def delete_node(graph, v):
    for u in graph[v]:
        graph[u].remove(v)
    del graph[v]


def copy_graph(graph):
    return {u: set(graph[u]) for u in graph}


def contract_edge(graph, u, v):
    """Contract edge (u,v) by removing u"""
    graph[v] = (graph[v] | graph[u]) - {u, v}
    del graph[u]
    for w in graph:
        if u in graph[w]:
            graph[w] = (graph[w] | {v}) - {u, w}


def upper_bound(graph):
    """Min-fill."""
    graph = copy_graph(graph)
    dmax = 0
    order = []
    while len(graph) > 0:
        # d, u = min((len(graph[u]), u) for u in graph) # min-width
        d, u = min((count_fillin(graph, graph[u]), u) for u in graph)
        dmax = max(dmax, len(graph[u]))
        eliminate_node(graph, u)
        order.append(u)
    return dmax, order


def count_fillin(graph, nodes):
    """How many edges would be needed to make v a clique."""
    count = 0
    for v1 in nodes:
        for v2 in nodes:
            if v1 != v2 and v2 not in graph[v1]:
                count += 1
    return count / 2


def lower_bound(graph):
    """Minor-min-width"""
    graph = copy_graph(graph)
    dmax = 0
    while len(graph) > 0:
        # pick node of minimum degree
        d, u = min((len(graph[u]), u) for u in graph)
        dmax = max(dmax, d)

        # Gogate and Dechter: minor-min-width
        nb = graph[u] - {u}
        if len(nb) > 0:
            _, v = min((len(graph[v] & nb), v) for v in nb)
            contract_edge(graph, u, v)
        else:
            delete_node(graph, u)
    return dmax


class Solution(object):
    pass


def quickbb(graph, fast=True):
    """Gogate and Dechter, A complete anytime algorithm for treewidth. UAI
       2004. http://arxiv.org/pdf/1207.4109.pdf"""

    """Given a permutation of the nodes (called an elimination ordering),
       for each node, remove the node and make its neighbors into a clique.
       The maximum degree of the nodes at the time of their elimination is
       the width of the tree decomposition corresponding to that ordering.
       The treewidth of the graph is the minimum over all possible
       permutations.
       """

    best = Solution()  # this gets around the lack of nonlocal in Python 2
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
                graph1 = copy_graph(graph)
                eliminate_node(graph1, v)
                order1 = order + [v]
                # treewidth for current order so far
                g1 = max(g, len(graph[v]))
                # lower bound given where we are
                f1 = max(g, lower_bound(graph1))
                if f1 < best.ub:
                    bb(graph1, order1, f1, g1)
                    return

    graph = {u: set(graph[u]) for u in graph}

    order = []
    best.ub, best.order = upper_bound(graph)
    lb = lower_bound(graph)

    # This turns on the branch and bound algorithm that
    # gets better treewidth results, but takes a lot
    # longer to process
    if not fast:
        if lb < best.ub:
            bb(graph, order, lb, 0)

    # Build the tree decomposition
    tree = defaultdict(set)

    def build(order):
        if len(order) < 2:
            bag = frozenset(order)
            tree[bag] = set()
            return
        v = order[0]
        clique = graph[v]
        eliminate_node(graph, v)
        build(order[1:])
        for tv in tree:
            if clique.issubset(tv):
                break
        bag = frozenset(clique | {v})
        tree[bag].add(tv)
        tree[tv].add(bag)

    build(best.order)
    # print tree
    return tree


def make_rooted(graph, u, memo=None):
    """Returns: a tree in the format (label, children) where children is a list of trees"""
    if memo is None: memo = set()
    memo.add(u)
    children = [make_rooted(graph, v, memo) for v in graph[u] if v not in memo]
    return (u, children)


def new_visit(datree, g_prev, g_next, shrg_rules, i, indent=0, parent=None):

    node, subtrees = datree
    itx = parent & node if parent else set()
    rhs_prev = get_production_rule(g_prev, node, itx)
    rhs_next = get_production_rule(g_next, node, itx)
    s = [list(node & child) for child, _ in subtrees]

    add_to_shrg_rules(shrg_rules, itx, rhs_prev, rhs_next, s, i)

    # print " "*indent, " ".join(str(x) for x in node) # prints Tree
    for subtree in subtrees:
        tv, subsubtrees = subtree
        new_visit(subtree, g_prev, g_next, shrg_rules, i, indent=indent + 2, parent=node)


def get_production_rule(g, child, itx):
    # lhs = nx.Graph()
    # for n in G.subgraph(itx).nodes():
    #    lhs.add_node(n)
    # for e in G.subgraph(itx).edges():
    #    lhs.add_edge(e[0], e[1])

    rhs = nx.DiGraph()
    for n in child:
        rhs.add_node(n)
    for e in g.subgraph(child).edges():
        rhs.add_edge(e[0], e[1])

    # remove links between external nodes (edges in itx)
    for x in itertools.permutations(itx, 2):
        if rhs.has_edge(x[0], x[1]):
            rhs.remove_edge(x[0], x[1])

    # return lhs, rhs
    return rhs


def make_rule(rhs, ext, s):
    import hypergraphs
    d = {}
    ext_id = 0
    i = 0
    rhs_s = nx.MultiDiGraph()
    for n in rhs.nodes():
        if n in d:
            n = d[n]
        else:
            d[n] = i
            i += 1
        if n in ext:
            nid = '_' + str(d[n])
            rhs_s.add_node(nid, label='u', nid = nid, external = ext_id, oid = n)
            ext_id += 1
        else:
            nid = '_' + str(d[n])
            rhs_s.add_node(nid, label='u', nid = nid, oid = n)

    attrs = {'label': 'e'}
    for e in rhs.edges():
        u = '_' + str(d[e[0]])
        v = '_' + str(d[e[1]])
        if rhs_s.has_edge(u,v):
            print 'has'
        rhs_s.add_edge(u, v, label='e')

    i = 0
    for c in s:

        #rhs_s.add_node(nonterm, label=grammar.Nonterminal(len(c)))

        nt = str(len(c))
        #if len(c) == 2:
        #    u = '_' + str(d[c[0]])
        #    v = '_' + str(d[c[1]])
        #    rhs_s.add_edge(u, v, **attrs)
        #else:
        nodes = ['_' + str(d[x]) for x in sorted(c)]
        hypergraphs.add_hyperedge(rhs_s, nodes, i, label=grammar.Nonterminal(nt), link=i)
        #TODO 'link' attribute = i??
        i+=1

    return rhs_s

def edge_isomorph(x, y):
    if 'label' in x or 'label' in y:
        if 'label' not in x or 'label' not in y:
            return False
        if x['label'] != y['label']:
            return False
    return True


def node_isomorph(x, y):
    if 'nid' in x and 'nid' in y and x['nid'] != y['nid']: return False
    if x['label'] != y['label']: return False
    if 'external' in x or 'external' in y:
        if 'external' not in x or 'external' not in y:
            return False
    return True


def add_to_shrg_rules(shrg_rules, lhs, rhs_prev, rhs_next, s, t):

    lhs_he = grammar.Nonterminal(str(len(lhs)))

    rule_prev = grammar.Rule(lhs_he, make_rule(rhs_prev, lhs, s), t)
    rule_next = grammar.Rule(lhs_he, make_rule(rhs_next, lhs, s), t)

    # print lhs_he, '->', rule_prev.rhs.edges(), rule_next.rhs.edges()

    if lhs_he not in shrg_rules:
        shrg_rules[lhs_he] = [(rule_prev, rule_next)]
    else:
        #prev side
        rhs_list = shrg_rules[lhs_he]
        match = None
        for i in range(0,len(rhs_list)):
            rhs = rhs_list[i]
            if nx.is_isomorphic(rhs[0].rhs, rule_prev.rhs, edge_match=edge_isomorph, node_match=node_isomorph):
                # print("prev isomorph")
                if nx.is_isomorphic(rhs[1].rhs, rule_next.rhs, edge_match=edge_isomorph, node_match=node_isomorph):
                    # print("next isomorph")
                    match = rhs_list[i]
                    match[0].weight *= 2
                    match[0].iso = True
                    match[1].weight *= 2
                    match[1].iso = True

        if not match:
            shrg_rules[lhs_he] += [(rule_prev, rule_next)]
