import itertools, collections
import re
import sys
from graph import *


class Nonterminal(object):
    def __init__(self, label):
        self.label = label

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


nonterminal_re = re.compile(r"""(.*)\[(.*)\]$""")
# nonterminal_re = re.compile(r"""(.*)\$(.*)$""") # bolinas
external_re = re.compile(r"""(.*)\*(.*)$""")
lhs_re = re.compile(r"""\s*(\S+)\s*->""")
rhs_divider_re = re.compile(r"""\s*:\s*""")


class Graphlet(Graph):
    """Graph with external nodes."""

    def __init__(self, root, exts=None):
        convert_from_str = type(root) in [str, unicode]

        if convert_from_str:
            root = amr_to_graph(root).root

        Graph.__init__(self, root)

        if convert_from_str:
            if exts is not None:
                raise ValueError()

            # look for nodes ending with * and make them external nodes
            exts = []
            for node in self.dfs():
                if node.label is None:
                    continue
                m = external_re.match(node.label)
                if m:
                    node.label = m.group(1)
                    i = int(m.group(2)) if m.group(2) else 1
                    if not i >= 1:
                        raise ValueError("External nodes should be labeled starting from 1")
                    while len(exts) < i:
                        exts.append(None)
                    exts[i - 1] = node
            self.exts = exts

        else:
            self.exts = exts or []

    def __str__(self):
        def node_to_str(node):
            if node in self.exts:
                return "%s*%d" % (node.label, self.exts.index(node))
            else:
                return str(node.label)

        return self.to_amr(node_to_str)

    def copy(self, memo=None):
        if memo is None: memo = {}
        g = self.root.copy(memo)
        exts = [memo[id(ext)] for ext in self.exts]
        return Graphlet(g, exts)

    def tree_decomposition(self):
        """
        Each tree node has:
          - label: a string
          - hnodes: a list of graph nodes
          - hedges: a list of graph edges that connect hnodes. We guarantee that for every graph edge e, there is some tree node whose hedges contains e, but we don't guarantee that for each tree node, all the edges that connect hnodes are in hedges.

        The tree is binary branching. Does it have to be nice?

        exts is a collection of nodes that should be in the tree root.

        """
        # Build adjacency list representation which treewidth routine uses
        adjacency = collections.defaultdict(set)
        for node in self.dfs():
            adjacency.setdefault(node, set())
            for edge in node.outedges:
                treewidth.make_clique(adjacency, [node] + edge.tails)

        # Connect root and external nodes
        exts = list(self.exts) + [self.root]
        treewidth.make_clique(adjacency, exts)

        # Compute treewidth
        tree = treewidth.quickbb(adjacency)

        # Find tree node that contains root and external nodes
        for tv in tree:
            if tv.issuperset(exts):
                tr = tv
                break

        # Convert back to Graph
        def visit(node, visited_nodes, visited_edges):
            visited_nodes.add(node)

            node1 = Node("bag")
            node1.hnodes = node
            node1.hedges = []
            # find edges between nodes in bag
            for u in node:
                for edge in u.outedges:
                    if edge not in visited_edges and node.issuperset(edge.tails):
                        node1.hedges.append(edge)
                        visited_edges.add(edge)

            children = list(tree[node].difference(visited_nodes))

            curnode1 = node1
            while len(children) > 2:
                child = children.pop()
                child1 = visit(child, visited_nodes, visited_edges)
                curnode1.outedges.append(Edge('child', [child1]))
                node2 = Node("bag")
                node2.hnodes = node1.hnodes
                node2.hedges = []
                curnode1.outedges.append(Edge('dummy', [node2]))
                curnode1 = node2

            for child in children:
                child1 = visit(child, visited_nodes, visited_edges)
                curnode1.outedges.append(Edge('child', [child1]))
            return node1

        tr1 = visit(tr, set(), set())
        g = Graph(tr1)
        return g


class Rule(object):
    def __init__(self, lhs, rhs, weight=1., erhs=None):
        """Nonterminals in rhs and erhs are linked by identity (not equality)."""
        self.lhs = lhs

        if isinstance(rhs, Graph):
            self.rhs = rhs

        elif type(rhs) in [str, unicode]:
            rhs = Graphlet(rhs)
            nonterminals = {}

            for edge in rhs.dfs_edges():
                if edge.label:
                    m = nonterminal_re.match(edge.label)
                    if m:
                        edge.label = Nonterminal(m.group(1))
                        index = m.group(2) or len(nonterminals)
                        nonterminals[index] = edge.label

            self.rhs = rhs

        if isinstance(erhs, Graph):
            self.erhs = erhs

        elif type(erhs) in [str, unicode]:
            erhs = Graphlet(erhs)

            counter = 0
            for edge in erhs.dfs_edges():
                if edge.label:
                    m = nonterminal_re.match(edge.label)
                    if m:
                        index = m.group(2)
                        if index == "":
                            index = counter
                            counter += 1
                        label = nonterminals[index]
                        if label != Nonterminal(m.group(1)):
                            raise ValueError("erhs nonterminals must match coindexed frhs nonterminals")
                        edge.label = label

            self.erhs = erhs

        self.rhs_index = {}
        for edge in rhs.dfs_edges():
            self.rhs_index[id(edge.label)] = edge
        self.erhs_index = {}
        for edge in erhs.dfs_edges():
            self.erhs_index[id(edge.label)] = edge

        self.weight = weight

    def lhs_signature(self):
        sig = (self.lhs,)
        sig = sig + (self.rhs.root.label,) + tuple(ext.label for ext in self.rhs.exts)
        if hasattr(self, 'erhs'):
            sig = sig + (self.erhs.root.label,) + tuple(ext.label for ext in self.erhs.exts)
        return sig

    def rhs_signature(self, edge):
        sig = (edge.label,)
        sig = sig + (edge.head.label,) + tuple(tail.label for tail in edge.tails)
        if hasattr(self, 'erhs'):
            edge = self.erhs_index[id(edge.label)]
            sig = sig + (edge.head.label,) + tuple(tail.label for tail in edge.tails)
        return sig

    def __str__(self):
        exts = {}

        if len(self.rhs.exts) == 1:
            exts[self.rhs.exts[0]] = ""
        else:
            for i, node in enumerate(self.rhs.exts):
                exts[node] = i + 1

        if len(self.erhs.exts) == 1:
            exts[self.erhs.exts[0]] = ""
        else:
            for i, node in enumerate(self.erhs.exts):
                exts[node] = i + 1

        def node_to_str(node):
            if node in exts:
                return "{0}*{1}".format(str(node.label), exts[node])
            else:
                return str(node.label)

        nonterminals = {}
        for edge in self.rhs.dfs_edges():
            if isinstance(edge.label, Nonterminal):
                nonterminals[id(edge.label)] = len(nonterminals) + 1

        def edge_to_str(edge):
            if id(edge.label) in nonterminals:
                return str("{0}[{1}]".format(edge.label, nonterminals[id(edge.label)]))
            else:
                return str(edge.label)

        if hasattr(self, "erhs"):
            for edge in self.rhs.dfs_edges():
                if isinstance(edge.label, Nonterminal):
                    if id(edge.label) not in nonterminals:
                        nonterminals[id(edge.label)] = len(nonterminals) + 1

            return "{0} ||| {1} ||| {2} ||| {3}".format(str(self.lhs),
                                                        self.rhs.to_amr(node_to_str, edge_to_str),
                                                        self.erhs.to_amr(node_to_str, edge_to_str),
                                                        self.weight)
        else:
            def edge_to_str(edge):
                return str(edge.label)

            return "{0} ||| {1}".format(str(self.lhs),
                                        self.rhs.to_str(node_to_str, edge_to_str))


def subst(h, nonterminals):
    """
    h is a Graphlet
    nonterminals is a mapping from Nonterminal ids to Graphlets
    """
    if len(nonterminals) == 0:
        return h
    h = h.copy()
    for node in list(h.dfs()):
        newedges = []
        for edge in node.outedges:
            if isinstance(edge.label, Nonterminal):
                rhs = nonterminals[id(edge.label)].copy()
                if node.label != rhs.root.label:
                    raise ValueError("inconsistent node labels")

                # attach rhs root outedges to head of edge
                newedges.extend(rhs.root.outedges)

                # attach tails of edge to rhs exts
                if len(rhs.exts) != len(edge.tails):
                    raise ValueError("different number of external nodes and tails")
                for ext, tail in itertools.izip(rhs.exts, edge.tails):
                    if ext.label != tail.label:
                        raise ValueError("inconsistent node labels")
                    # find and replace all references to ext. this is kind of slow
                    for inedge in ext.inedges:
                        i = inedge.tails.index(ext)
                        inedge.tails[i] = tail
                    tail.outedges.extend(ext.outedges)
            else:
                newedges.append(edge)
        node.outedges = newedges

    return Graphlet(h.root, h.exts)