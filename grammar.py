import itertools, collections
import re

import networkx
import amr
import hypergraphs
import treewidth


class Nonterminal(object):
    def __init__(self, x):
        if isinstance(x, Nonterminal):
            self.label = x.label
        else:
            self.label = x

    def __str__(self):
        return self.label

    def __repr__(self):
        return "Nonterminal({0})".format(self.label)

    def __hash__(self):
        return hash(self.label)

    def __eq__(self, other):
        return isinstance(other, Nonterminal) and self.label == other.label

    def __ne__(self, other):
        return not (isinstance(other, Nonterminal) and self.label == other.label)


nonterminal_re = re.compile(r"""(.*)\[(\d+)\]$""")
# nonterminal_re = re.compile(r"""(.*)\$(.*)$""") # bolinas
external_re = re.compile(r"""(.*)\*(\d+)$""")
lhs_re = re.compile(r"""\s*(\S+)\s*->""")
rhs_divider_re = re.compile(r"""\s*:\s*""")


def parse_graphlet(s):
    g = amr.parse_amr(s)
    external = []
    for v in hypergraphs.nodes(g):
        m = external_re.match(g.node[v]['label'])
        if m:
            g.node[v]['label'] = m.group(1)
            i = int(m.group(2)) - 1
            g.node[v]['external'] = i
            external.append((i, v))
    if list(range(len(external))) != sorted(i for (i, v) in external):
        raise amr.ParseError("external nodes must be consecutively numbered starting from 1")
    return g


def format_graphlet(g, show_all=False):
    g = g.copy()
    for v in hypergraphs.nodes(g):
        if 'external' in g.node[v]:
            g.node[v]['label'] += "*{}".format(g.node[v]['external'] + 1)
    return amr.format_amr(g, show_all=show_all)


def external_nodes(g):
    external = {}
    for v in hypergraphs.nodes(g):
        if 'external' in g.node[v]:
            external[g.node[v]['external']] = v
    return external.values()


def decompose_graphlet(g):
    # Join external nodes and form tree decomposition
    g1 = g.copy()
    external = external_nodes(g)
    if len(external) > 0:
        hypergraphs.add_hyperedge(g1, external)
    t = treewidth.quickbb(hypergraphs.clique_graph(g1))

    # The root bag is the one containing the external nodes
    for tv in reversed(t.nodes()):
        if t.node[tv]['nodes'].issuperset(external):
            tr = tv
            break
    else:
        assert False

    t = to_arborescence(t, tr)
    t = binarize(t)
    t = add_edges(g, t)
    return t


def to_arborescence(t, r=None):
    """Convert an undirected tree to an arborescence (tree whose edges are all from parent to child)."""
    if not networkx.is_tree(t):
        raise ValueError("t must be a tree")
    if r is None:
        r = t.nodes()[0]
    a = networkx.DiGraph(**t.graph)
    for v in t.nodes():
        a.add_node(v, **t.node[v])
    visited = set()

    def visit(u):
        visited.add(u)
        for v in t.neighbors(u):
            if v not in visited:
                a.add_edge(u, v, **t.edge[u][v])
                visit(v)

    visit(r)
    a.graph['root'] = r
    return a


def binarize(t):
    """Make an arborescence binary branching. Every interior node v with
    more than two children is split into r-1 copies labeled (v,0),
    ..., (v,r-2).
    """

    if not networkx.is_arborescence(t):
        raise ValueError("t must be an arborescence")
    t1 = networkx.DiGraph(**t.graph)

    def visit(node):
        children = t.successors(node)
        if len(children) > 2:
            prev = visit(children[0])
            for i, child in enumerate(children[1:]):
                new = (node, i)
                t1.add_node(new, **t.node[node])
                t1.add_edge(new, prev)
                t1.add_edge(new, visit(child), **t.edge[node][child])
                prev = new
            return prev
        else:
            t1.add_node(node, **t.node[node])
            for child in children:
                t1.add_edge(node, visit(child), **t.edge[node][child])
            return node

    t1.graph['root'] = visit(t.graph['root'])
    return t1


def add_edges(g, t):
    t = t.copy()
    edges = hypergraphs.edges(g)

    def visit(u):
        t.node[u]['edges'] = []
        for e in edges:
            if t.node[u]['nodes'].issuperset(e):
                t.node[u]['edges'].append(e)
        for e in t.node[u]['edges']:
            edges.remove(e)
        for v in t.successors(u):
            visit(v)

    visit(t.graph['root'])
    assert (len(edges) == 0)

    return t


class Rule(object):
    next_id = 0

    def __init__(self, lhs, rhs, id=None, weight=1.):
        self.lhs = lhs
        self.rhs = rhs
        if id is None:
            self.id = Rule.next_id
            Rule.next_id += 1
        else:
            self.id = id
        self.weight = weight

    def lhs_signature(self):
        sig = (self.lhs,)
        sig += tuple(self.rhs.node[v]['label'] for v in external_nodes(self.rhs))
        return sig

    def rhs_signature(self, e):
        sig = (hypergraphs.edge(self.rhs, e)['label'],)
        sig += tuple(self.rhs.node[v]['label'] for v in e)
        return sig


def parse_rhs(s):
    g = parse_graphlet(s)
    links = []
    for e in hypergraphs.edges(g):
        attrs = hypergraphs.edge(g, e)
        if attrs['label'] is not None:
            m = nonterminal_re.match(attrs['label'])
            if m:
                attrs['label'] = Nonterminal(m.group(1))
                link = int(m.group(2)) - 1
                attrs['link'] = link
                links.append((link, e))
    if list(range(len(links))) != sorted(link for (link, e) in links):
        raise amr.ParseError("nonterminal links must be consecutively numbered starting from 1")
    return g


def format_rhs(g, show_all=False):
    g = g.copy()
    for e in hypergraphs.edges(g):
        attrs = hypergraphs.edge(g, e)
        if isinstance(attrs.get('label', None), Nonterminal):
            attrs['label'] = "{}[{}]".format(attrs['label'].label,
                                             attrs['link'] + 1)
    return format_graphlet(g, show_all)


def derive(deriv, rules):
    """
    Construct a derived hypergraph from a derivation tree.

    deriv: a tree (arborescence) where
      - 'root' attribute is the root node
      - each node's 'rule' attribute is a rule id
      - each edge's 'link' attribute indicates where the replacement occurs
    rules: a list of Rules.

    Currently does not check either nonterminal symbols or node labels."""

    h = networkx.DiGraph()
    rules = {r.id: r for r in rules}

    def visit(dnode, hedge):
        """
        dnode: current derivation node
        hedge: nonterminal edge that current rule replaces
        """
        print dnode.rule.id
        dchildren = {}
        for dchild in deriv.successors(dnode):
            dchildren[deriv[dnode][dchild]['link']] = dchild
        rule = rules[deriv.node[dnode]['rule']]
        m = {}
        for v in hypergraphs.nodes(rule.rhs):
            if 'external' in rule.rhs.node[v]:
                m[v] = hedge[rule.rhs.node[v]['external']]
            else:
                m[v] = len(h)
                h.add_node(m[v], **rule.rhs.node[v])
            if dnode == deriv.graph['root'] and 'root' in rule.rhs.graph and v == rule.rhs.graph['root']:
                h.graph['root'] = m[v]

        for e in hypergraphs.edges(rule.rhs):
            attrs = hypergraphs.edge(rule.rhs, e)
            me = tuple(m[v] for v in e)
            if isinstance(attrs.get('label', None), Nonterminal):
                visit(dchildren[attrs['link']], me)
            else:
                hypergraphs.add_hyperedge(h, me, **attrs)

    visit(deriv.graph['root'], ())
    return h



def get_rule_list(deriv):
    """
    deriv: a tree (arborescence) where
      - 'root' attribute is the root node
      - each node's 'rule' attribute is a rule id
      - each edge's 'link' attribute indicates where the replacement occurs
    rules: a list of Rules.
    """

    rules = [deriv.graph['root']]
    def visit(dnode):
        """
        dnode: current derivation node
        hedge: nonterminal edge that current rule replaces
        """

        dchildren = {}
        for dchild in deriv.successors(dnode):
            rules.append(dchild)
            dchildren[deriv[dnode][dchild]['link']] = dchild

    visit(deriv.graph['root'])
    return rules

if __name__ == "__main__":
    import sys

    for s in sys.stdin:
        g = parse_rhs(s)
        print(format_rhs(g))