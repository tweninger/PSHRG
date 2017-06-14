import networkx

class Hyperedge(object):
    pass

def add_hyperedge(g, tails, heads, **attrs):
    e = Hyperedge()
    g.add_node(e, **attrs)
    for v in tails:
        g.add_edge(v, e)
    for v in heads:
        g.add_edge(e, v)

def get_hyperedges(*args):
    if len(args) == 1:
        [g] = args
        for x in g.nodes():
            if isinstance(x, Hyperedge):
                yield x
    elif len(args) == 2:
        [g, v] = args
        for e in g.neighbors(v):
            if not isinstance(e, Hyperedge):
                raise TypeError("this is not a hypergraph")
            yield e
    else:
        raise TypeError("wrong number of arguments")