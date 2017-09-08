#!/usr/bin/env python

# bugs: 
#   need to check whether rewrite is legal on English side as well

from __future__ import print_function
from six import iteritems
from six.moves import zip
import sys
import collections, itertools
import networkx
from grammar import *
import bigfloat

verbose = 1


class UnificationFailure(Exception):
    pass


class Subgraph(object):
    """Represents a weakly connected edge-induced subgraph of
    a weakly connected Graph/DiGraph h.
    """

    def __init__(self, h, marker=False, exts=None):
        self.h = h
        self.boundary = {}
        self.marker = marker

    @staticmethod
    def singleton(h, edge):
        """Creates a Subgraph with a single edge and no external nodes."""
        g = Subgraph(h)
        for node in edge:
            g.boundary[node] = {edge}
            g.marker = g.marker or h.node[node].get('marker', False)
        return g

    def copy(self):
        g = Subgraph(self.h)
        g.boundary = dict((node, edges.copy()) for (node, edges) in iteritems(self.boundary))
        g.marker = self.marker
        return g

    def __eq__(self, other):
        return self.__handle__() == other.__handle__()

    def __ne__(self, other):
        return not self == other

    def __hash__(self, other):
        return hash(self.__handle__())

    def __handle__(self):
        return (
        id(self.h), self.marker, frozenset((node, frozenset(edges)) for node, edges in iteritems(self.boundary)))

    def __str__(self):
        return '{{{0}}}'.format(','.join(
            "{0}{{{1}}}".format(node, ','.join(str(edge) for edge in edges)) for node, edges in
            iteritems(self.boundary)))

    def empty(self):
        return len(self.boundary) == 0 and not self.marker

    def full(self):
        if not self.marker: return False
        for node in self.boundary:
            if len(self.boundary[node]) < self.h.degree(node):
                return False
        return True

    def merge(self, other):
        """Merge with another subgraph.
           To ensure that the resulting subgraph is connected,
           require that the new boundary has at least one node in common with ours."""
        if self.marker and other.marker:
            if all(not self.h.node[node]['marker'] for node in set(self.boundary) & set(other.boundary)):
                raise UnificationFailure("subgraphs must be disjoint")

        for node, edges in iteritems(other.boundary):
            res = []
            if node in self.boundary:
                for e in self.boundary[node]:
                    for f in edges:
                        if e == f and type(e) == type(f):
                            res.append(e)
                if res:
                    raise UnificationFailure("subgraphs must be disjoint")
            if node not in self.boundary:
                self.boundary[node] = set()
            self.boundary[node].update(edges)
        self.marker = self.marker or other.marker

    @staticmethod
    def multigraph_intersection(self, e1, e2):
        res = []
        for e in e1:
            for f in e2:
                if e == f and type(e) == type(f):
                    res.append(e)
        return res


    def forget_node(self, node):
        """Forget about a node. But this is only possible if all the node's edges have been added.
           Otherwise, we lose information."""
        if len(self.boundary[node]) != self.h.degree(node):
            raise UnificationFailure("can't forget a node until all its edges are recognized")
        del self.boundary[node]


class Item(object):
    def __init__(self, rule, tnode, dot, map):
        """
        Let H be the input graph.

        rule is a grammar rule
        tnode is a node of rule.rhs_tree
        dot is the number of edges in tnode that have been recognized

        Let R' be the subgraph of rule.rhs induced by the union of:
          - the edges to the left of the dot in tnode
          - the edges in the descendants of tnode

        map is a one-to-one mapping from the boundary nodes and edges of R' to H.

        Parser invariant: There is an extension of map that is an
        isomorphism f between R' and an induced subgraph H'.
        """
        self.rule = rule
        self.tnode = tnode
        self.dot = dot
        self.map = map

    def __handle__(self):
        return (self.rule, self.tnode, self.dot, self.map.__handle__())

    def __eq__(self, other):
        return isinstance(other, Item) and self.__handle__() == other.__handle__()

    def __ne__(self, other):
        return not (isinstance(other, Item) and self.__handle__() == other.__handle__())

    def __hash__(self):
        return hash(self.__handle__())

    @property
    def edges(self):
        return self.rule.rhs_tree.node[self.tnode]['edges']

    @property
    def nextedge(self):
        return self.edges[self.dot]

    @property
    def nextedgelabel(self):
        return hypergraphs.edge(self.rule.rhs, self.nextedge)['label']

    def __str__(self):
        return "[{},{},{},{}]".format(self.rule.id, self.tnode, self.dot, self.map)


class Goal(object):
    def __init__(self):
        pass

    def __eq__(self, other):
        return isinstance(other, Goal)

    def __ne__(self, other):
        return not isinstance(other, Goal)

    def __hash__(self):
        return hash("Goal")

    def __str__(self):
        return "[Goal]"


class Mapping(object):
    """Represents a bijection between a subgraph of R and a subgraph of H."""

    def __init__(self, r, h):
        self.r = r
        self.h = h
        self.rspan = Subgraph(r)  # R'
        self.hspan = Subgraph(h)  # H'
        self.nodemap = {}  # node of R' -> node of H'

    def copy(self):
        newmap = Mapping(self.r, self.h)
        newmap.nodemap = self.nodemap.copy()
        newmap.rspan = self.rspan.copy()
        newmap.hspan = self.hspan.copy()
        return newmap

    def __str__(self):
        s = ','.join("{0}->{1}".format(
            rnode,
            hnode) for rnode, hnode in iteritems(self.nodemap))
        return "{{{0}}}".format(s)

    def __handle__(self):
        return (self.rspan.__handle__(),
                self.hspan.__handle__(),
                frozenset(iteritems(self.nodemap)))

    def __eq__(self, other):
        return isinstance(other, Item) and self.__handle__() == other.__handle__()

    def __ne__(self, other):
        return not self == other

    def __hash__(self):
        return hash(self.__handle__())

    def add(self, rnode, hnode):
        if self.r.node[rnode]['label'] != self.h.node[hnode]['label']:
            raise UnificationFailure()

        # ensure that nodemap is bijective, and
        # that we update it monotonically
        if rnode in self.nodemap:
            if self.nodemap[rnode] != hnode:
                raise UnificationFailure()
        else:
            if hnode in self.hspan.boundary:
                raise UnificationFailure()
            self.nodemap[rnode] = hnode

    # All modifications to mapping are made via the methods below

    def set_domain(self, domain):
        for rnode in list(self.nodemap):
            if rnode not in domain:
                self.rspan.forget_node(rnode)
                self.hspan.forget_node(self.nodemap[rnode])
                del self.nodemap[rnode]

    def add_edge(self, redge, hedge):
        if hypergraphs.edge(self.r, redge)['label'] != hypergraphs.edge(self.h, hedge)['label']:
            raise UnificationFailure()

        for rnode, hnode in zip(redge, hedge):
            self.add(rnode, hnode)

        self.rspan.merge(Subgraph.singleton(self.r, redge))
        self.hspan.merge(Subgraph.singleton(self.h, hedge))

    def add_rewrite(self, redge, subrule, submap):
        external = external_nodes(subrule.rhs)
        if hypergraphs.edge(self.r, redge)['label'] != subrule.lhs:
            raise UnificationFailure()
        if len(redge) != len(external):
            raise UnificationFailure()

        for rnode, snode in zip(redge, external):
            # Special case for when snode is just a node with no edges.
            # In this case, rnode is mapped to a node but snode is not.
            # So we need to check that the node labels match,
            # but don't need to update self.nodemap.
            if subrule.rhs.degree(snode) == 0:
                if self.r.node[rnode]['label'] != subrule.rhs.node[snode]['label']:
                    raise UnificationFailure("node labels do not match")
                if rnode not in self.nodemap:
                    print('e')
                assert rnode in self.nodemap
            else:
                self.add(rnode, submap.nodemap[snode])

        self.rspan.merge(Subgraph.singleton(self.r, redge))
        self.hspan.merge(submap.hspan)

    def merge(self, other):
        for rnode in other.nodemap:
            self.add(rnode, other.nodemap[rnode])

        self.rspan.merge(other.rspan)
        self.hspan.merge(other.hspan)


class Chart(object):
    def __init__(self):
        self.chart = networkx.Graph()
        self.tnode_index = collections.defaultdict(list)
        self.lhs_index = collections.defaultdict(list)
        self.edge_index = collections.defaultdict(list)
        self.agenda = set()
        self.indent_level = 2

    def add(self, item, ants=(), label=None, weight=1.):
        if verbose >= 3:
            print(" " * self.indent_level + "add: " + str(item))

        if item in self.chart:
            if verbose >= 3:
                print(" " * self.indent_level + "  already in chart")
                if item not in self.agenda:
                    print(" " * self.indent_level + "  warning: not in agenda (inside weights will be incorrect)")
        else:
            self.agenda.add(item)

        hypergraphs.add_hyperedge(self.chart, (item,) + ants, label=label, weight=weight)

    def get(self):
        item = self.agenda.pop()

        if isinstance(item, Goal):
            return item

        # We index the item only upon removing it from the agenda
        # so that a deduction always involves exactly one agenda item
        # and zero or more non-agenda items.

        # index for completed tree nodes
        if item.dot == len(item.edges):
            self.tnode_index[item.rule, item.tnode].append(item)

            # index for completed rhs's
            if item.tnode == item.rule.rhs_tree.graph['root']:
                lhs = item.rule.lhs_signature()
                self.lhs_index[lhs].append(item)

        else:
            redge = item.edges[item.dot]
            if isinstance(hypergraphs.edge(item.rule.rhs, redge)['label'], Nonterminal):
                lhs = item.rule.rhs_signature(redge)
                self.edge_index[lhs].append(item)

        return item

    def __contains__(self, item):
        return item in self.chart

    def __getitem__(self, item):
        return self.chart[item]


def viterbi(chart):
    weight = {}
    ant = {}

    # Find maximum weight
    def visit(u):
        if u not in chart:
            return bigfloat.bigfloat(0.)
        if u in weight:
            return weight[u]
        w_max = None
        e_max = None
        for e in hypergraphs.edges(chart, u):
            if e[0] != u: continue
            w = bigfloat.bigfloat(1.)
            for v in e[1:]:
                w *= visit(v)
            if w_max is None or w > w_max:
                w_max = w
                e_max = e
        weight[u] = w_max
        ant[u] = e_max
        return w_max
    visit(Goal())

    # Reconstruct derivation
    deriv = networkx.DiGraph()
    def visit(ritem, item):
        # ritem: item at the root of the rule
        # item: current item
        deriv.add_node(ritem, rule=ritem.rule.id)
        e = ant[item]
        if hypergraphs.edge(chart, e)['label'] == "Complete":
            _, aitem, pitem = e
            link = hypergraphs.edge(aitem.rule.rhs, aitem.nextedge)['link']
            visit(ritem, aitem)
            visit(pitem, pitem)
            deriv.add_edge(ritem, pitem, link=link)
        else:
            for item in e[1:]:
                visit(ritem, item)

    [_, item] = ant[Goal()]
    visit(item, item)
    [deriv.graph['root']] = [v for v in deriv if len(deriv.predecessors(v)) == 0]
    return deriv


class ParserError(Exception):
    pass


def parse(g, starts, h):
    # Preprocess input

    # Arbitrarily choose a marker node in each weakly connected component
    if verbose >= 3:
        for e in h.edges():
            print(e)
    if not networkx.is_weakly_connected(h):
        raise NotImplementedError("parsing of disconnected graphs not implemented")
    for comp in networkx.weakly_connected_components(h):
        marker = True
        for v in comp:
            if not isinstance(v, hypergraphs.Hyperedge):
                h.node[v]['marker'] = marker
                if verbose >= 3 and marker:
                    print("  marker node:", v)
                marker = False

    # Preprocess grammar

    # Could filter out rules that use labels not found in h

    for rule in g:
        if verbose >= 3:
            print('Rule', str(rule.id) + ':')
            print('\t' + str(rule.lhs) + '->')
            print('\tNodes:')
            for n in rule.rhs.nodes(data=True):
                print('\t\t' + str(n))
            print('\tEdges:')
            for e in rule.rhs.edges():
                print('\t\t' + str(e))
            print()
            #print("Rule {}: {} -> {}, (may be disconnected)".format(str(rule.id), rule.lhs, format_rhs(rule.rhs, show_all=True)))

        # Form tree decomposition.
        # Assume (at most) binary branching
        # For each node tnode \in rule.rhs_tree, assume a list of edges
        # such that every edge in h appears exactly once among all the lists

        t = decompose_graphlet(rule.rhs)
        for v in t.nodes():
            # We need the edges in each bag to be ordered
            t.node[v]['edges'] = list(t.node[v]['edges'])
        rule.rhs_tree = t
        if verbose >= 3:
            print("  tree decomposition:", t.edges())
            for v in t.nodes():
                print("    bag {}".format(v))
                print("      nodes:", " ".join(map(str, t.node[v]['nodes'])))
                print("      edges:", " ".join('-'.join(map(str, e)) for e in t.node[v]['edges']))

    chart = Chart()

    # Axioms
    if verbose >= 3:
        print("axioms:")
    for rule in g:
        for tnode in rule.rhs_tree.nodes():
            if len(rule.rhs_tree.successors(tnode)) == 0:
                item = Item(rule, tnode, 0, Mapping(rule.rhs, h))
                chart.add(item, label="Leaf")

    while len(chart.agenda) > 0:
        trigger = chart.get()
        if trigger == Goal(): continue
        tnode = trigger.tnode
        rule = trigger.rule
        if verbose >= 3:
            print("trigger:", trigger)

        if trigger.dot < len(trigger.edges):
            # There are still edges left to process. Choose the next one, redge.
            redge = trigger.edges[trigger.dot]

            if isinstance(hypergraphs.edge(rule.rhs, redge)['label'], Nonterminal):
                # If redge is labeled with a nonterminal,
                # search for possible rewrites
                lhs = rule.rhs_signature(redge)
                for rewrite in chart.lhs_index[lhs]:
                    if verbose >= 3:
                        print("  rewrite:", rewrite)
                    newmap = trigger.map.copy()
                    try:
                        newmap.add_rewrite(redge, rewrite.rule, rewrite.map)
                    except UnificationFailure:
                        pass
                    else:
                        newitem = Item(rule, tnode, trigger.dot + 1, newmap)
                        chart.add(newitem, ants=(trigger, rewrite),
                                  label="Complete", weight=rewrite.rule.weight)

            else:
                # If redge is labeled with a terminal,
                # search for possible matches with edges in h, hedge,
                for hedge in hypergraphs.edges(h):  # to do: more general
                    # and try to add redge->hedge to trigger.map
                    newmap = trigger.map.copy()
                    try:
                        newmap.add_edge(redge, hedge)
                    except UnificationFailure:
                        pass
                    else:
                        newitem = Item(rule, tnode, trigger.dot + 1, newmap)
                        chart.add(newitem, ants=(trigger,), label="Shift")

        elif tnode != rule.rhs_tree.graph['root']:
            # No more edges in tnode left to process; move to parent
            [tparent] = rule.rhs_tree.predecessors(tnode)
            tchildren = rule.rhs_tree.successors(tparent)
            if len(tchildren) == 1:
                # only child
                newmap = trigger.map.copy()
                try:
                    newmap.set_domain(rule.rhs_tree.node[tparent]['nodes'])
                except UnificationFailure:
                    pass
                else:
                    newitem = Item(rule, tparent, 0, newmap)
                    chart.add(newitem, ants=(trigger,), label="Unary")

            elif len(tchildren) == 2:
                # find sister
                tchildren.remove(tnode)
                (tsister,) = tchildren

                for sister in chart.tnode_index[rule, tsister]:
                    if verbose >= 3:
                        print("  sister:", sister)
                    newmap = trigger.map.copy()
                    try:
                        newmap.merge(sister.map)
                        newmap.set_domain(rule.rhs_tree.node[tparent]['nodes'])
                    except UnificationFailure:
                        pass
                    else:
                        newitem = Item(rule, tparent, 0, newmap)
                        chart.add(newitem, ants=(trigger, sister), label="Binary")
            else:
                raise ParserError("tree decomposition not binary branching")

        else:
            # root of rule rhs: look for items to rewrite
            lhs = rule.lhs_signature()
            for rewritee in chart.edge_index[lhs]:
                if verbose >= 3:
                    print("  rewritee:", rewritee)
                oedge = rewritee.edges[rewritee.dot]
                newmap = rewritee.map.copy()
                try:
                    newmap.add_rewrite(oedge, trigger.rule, trigger.map)
                except UnificationFailure:
                    pass
                else:
                    newitem = Item(rewritee.rule, rewritee.tnode, rewritee.dot + 1, newmap)
                    chart.add(newitem, ants=(rewritee, trigger),
                              label="Complete", weight=rule.weight)

            # and check if we're done
            if trigger.map.hspan.full() and len(external_nodes(rule.rhs)) == 0 and rule.lhs in starts:
                chart.add(Goal(), ants=(trigger,), weight=rule.weight, label="Goal")

    return chart.chart


if __name__ == "__main__":
    import sys
    import argparse
    import amr

    parser = argparse.ArgumentParser()
    # parser.add_argument('grammars', type=str, metavar='grammar', nargs='+', help='file(s) containing grammar rules')
    parser.add_argument('-s', '--start', dest='start', type=str, default='Truth', metavar='nonterminal',
                        help='start symbol')
    args = parser.parse_args()

    frules = []
    erules = []
    start = Nonterminal(args.start)

    for f in range(1, 11):

        print()
        print('**** File #' + str(f) + '****')

        for ri, line in enumerate(open('tests/grammar' + str(f))):
            lhs, frhs, erhs, weight = line.split("|||")
            lhs = Nonterminal(lhs.strip())

            frule = Rule(lhs, parse_rhs(frhs), id=ri, weight=weight)
            frules.append(frule)

            erule = Rule(lhs, parse_rhs(erhs), id=ri)
            erules.append(erule)

        for ri, line in enumerate(open('tests/input' + str(f))):
            h = amr.parse_amr(line)

            if 1 <= verbose < 3:
                sys.stderr.write("Input graph: {}\n".format(amr.format_amr(h)))

            forest = parse(frules, [start], h)

            if forest:
                sys.stderr.write("Items: %s\n" % len(forest))
                if verbose >= 1:
                    sys.stderr.write("Output graph: ")
                print(amr.format_amr(derive(viterbi(forest), erules)))

            else:
                if verbose >= 1:
                    sys.stderr.write("No derivations\n")
                print("")
