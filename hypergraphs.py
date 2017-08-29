import networkx

class Hyperedge(tuple):
    pass

def add_hyperedge(g, nodes, **attrs):
    """Adds a Hyperedge as a node of g and tentacles as edges from the
    Hyperedge to the endpoint nodes.

    Note that regardless of the type of g, the order of tentacles matters,
    and multiple hyperedges are not allowed.
    """
    e = Hyperedge(nodes)
    g.add_node(e, **attrs)
    for v in nodes:
        g.add_edge(v, e)
    return e

def remove_node(g, v):
    for e in edges(g, v):
        g.remove_hyperedge(e)
    g.remove_node(v)

def remove_hyperedge(g, e):
    g.remove_node(e)

def nodes(g):
    result = []
    for x in g.nodes():
        if not isinstance(x, Hyperedge):
            result.append(x)
    return result

def edge(g, e):
    """Returns a dict of attributes of hyperedge e."""
    if isinstance(e, Hyperedge):
        if isinstance(g, networkx.MultiGraph):
            return {0: g.node[e]}
        else:
            return g.node[e]
    else:
        (u,v) = e
        return g.edge[u][v]

def edges_iter(g, nbunch=None, tentacle=0):
    """Returns a set of all edges and hyperedges incident to nodes in nbunch.

    By default, only returns (hyper)edges with tentacle 0 incident to
    nodes in nbunch.

    Does not work with MultiGraphs.

    tentacle: select which tentacle(s) can be incident to nodes in nbunch.
      - True: all tentacles
      - int i: only tentacle i
      - callable f: tentacles i such that f(i) is True

    """

    t = tentacle
    seen = set()
    for u in g.nbunch_iter(nbunch):
        if t in [True, 0] or callable(t) and t(0):
            for (u,v) in g.edges(u):
                if not isinstance(v, Hyperedge) and (u,v) not in seen:
                    seen.add((u,v))
                    yield (u,v)
        if (isinstance(g, networkx.DiGraph) and
            t in [True, 1] or callable(t) and t(1)):
            for v in g.predecessors(u):
                if not isinstance(v, Hyperedge) and (v,u) not in seen:
                    seen.add((v,u))
                    yield (v,u)
        for e in g.neighbors(u):
            if isinstance(e, Hyperedge) and e not in seen:
                if t == True or isinstance(t, int) and e[t] == u:
                    seen.add(e)
                    yield e
                elif callable(t):
                    for i,v in enumerate(e):
                        if f(i) and i == v:
                            seen.add(e)
                            yield e
                            break

def edges(g, nbunch=None, tentacle=0):
    return list(edges_iter(g, nbunch, tentacle))

def clique_graph(g):
    """Every hyperedge becomes a clique."""
    cg = networkx.Graph()
    for v in nodes(g):
        cg.add_node(v, **g.node[v])
    for e in edges(g):
        for u in e:
            for v in e:
                if v != u:
                    cg.add_edge(u, v, **edge(g, e))
    return cg