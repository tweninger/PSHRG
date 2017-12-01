import networkx

class Hyperedge():
    def __init__(self, tup, n):
        self.h = tup
        self.n = n

    def __str__(self):
        return repr(self)

    def __repr__(self):
        return '<'+str(self.h)+', '+ str(self.n) + '>'

    def __iter__(self):
        for x in self.h:
            yield x

def add_hyperedge(g, nodes, n=-1, **attrs):
    """Adds a Hyperedge as a node of g and tentacles as edges from the
    Hyperedge to the endpoint nodes.

    Note that regardless of the type of g, the order of tentacles matters,
    and multiple hyperedges are not allowed.
    """

    #see if edges already exists
    if n == -1:
        i=0
        while True:
            e = Hyperedge(nodes, i)
            if not g.has_node(e):
                break
            i+=1
        n = i

    e = Hyperedge(nodes,n)
    g.add_node(e, attrs)
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
            return g.node[e]
        else:
            return g.node[e]
    else:
        #TODO only one terminal edge type in this implementation
        (u,v) = e
        if isinstance(g, networkx.MultiGraph):
            return g.edge[u][v][0]
        else:
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
    for u in g.nbunch_iter(nbunch):
        if t in [True, 0] or callable(t) and t(0):
            for e in g.edges(u):
                if not isinstance(e[1], Hyperedge) :
                    yield e
                else:
                    if e[1].h[t] == u:
                        yield e[1]
        if (isinstance(g, networkx.DiGraph) and
            t in [True, 1] or callable(t) and t(1)):
            for v in g.predecessors(u):
                if not isinstance(v, Hyperedge):
                    yield (v,u)

def edges(g, nbunch=None, tentacle=0):
    return list(edges_iter(g, nbunch, tentacle))

def clique_graph(g):
    """Every hyperedge becomes a clique."""
    cg = networkx.MultiGraph()
    for v in nodes(g):
        cg.add_node(v, **g.node[v])
    for e in edges(g):
        if isinstance(e, Hyperedge):
            eh = e.h
        else:
            eh = e
        for u in eh:
            for v in eh:
                if v != u:
                    cg.add_edge(u, v, **edge(g, e))
    return cg