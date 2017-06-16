import collections, itertools
from graph import *
from grammar import *

verbose = 4


def mark_tree(node, mark):
    children = [e.tails[0] for e in node.outedges]
    label = "*{0}*".format(node.label) if node is mark else node.label
    if len(children) == 0:
        return label
    else:
        return "({0} {1})".format(label, ' '.join(mark_tree(child, mark) for child in children))


class UnificationFailure(Exception):
    pass


class Subgraph(object):
    """Represents a connected edge-induced subgraph H' of a connected graph H."""

    def __init__(self, marker=False, exts=None):
        self.boundary = {}
        self.marker = marker

    @staticmethod
    def singleton(edge):
        """Creates a Subgraph with a single edge and no external nodes."""
        g = Subgraph()
        for node in edge.nodes():
            g.boundary[node] = {edge}
            g.marker = g.marker or node.marker
        return g

    def copy(self):
        g = Subgraph()
        g.boundary = dict((node, edges.copy()) for (node, edges) in self.boundary.iteritems())
        g.marker = self.marker
        return g

    def __eq__(self, other):
        return self.__handle__() == other.__handle__()

    def __ne__(self, other):
        return not self == other

    def __hash__(self, other):
        return hash(self.__handle__())

    def __handle__(self):
        return (self.marker, frozenset((node, frozenset(edges)) for node, edges in self.boundary.iteritems()))

    def __str__(self):
        return '{{{0}}}'.format(','.join(
            "{0}{{{1}}}".format(node, ','.join(str(edge) for edge in edges)) for node, edges in
            self.boundary.iteritems()))

    def empty(self):
        return len(self.boundary) == 0 and not self.marker

    def full(self):
        if not self.marker: return False
        for node in self.boundary:
            if len(self.boundary[node]) < len(node.outedges) + len(node.inedges):
                return False
        return True

    def contains_node(self, node, lastedge):
        # To do: lastedge should not have to be passed as argument
        if node in self.boundary:
            return True
        dist_min = None
        for bnode in self.boundary:
            dist, edge = lastedge[node, bnode]
            if dist_min is None or dist < dist_min:
                dist_min, edge_min, node_min = dist, edge, node
        return edge_min in self.boundary[node_min]

    def disjoint(self, other):
        for node in self.boundary:
            if node in other.boundary:
                if len(self.boundary[node] & other.boundary[node]) > 0:
                    return False
            elif other.contains_node(node):
                return False
        for node in other.boundary:
            if node not in self.boundary and self.contains_node(node):
                return False
        return True

    def merge(self, other):
        """Merge with another subgraph.
           To ensure that the resulting subgraph is connected,
           require that the new boundary has at least one node in common with ours."""
        if self.marker and other.marker:
            if all(not node.marker for node in set(self.boundary) & set(other.boundary)):
                raise UnificationFailure("subgraphs must be disjoint")

        for node, edges in other.boundary.iteritems():
            if node in self.boundary and self.boundary[node].intersection(edges):
                raise UnificationFailure("subgraphs must be disjoint")
            if node not in self.boundary:
                self.boundary[node] = set()
            self.boundary[node].update(edges)
        self.marker = self.marker or other.marker

    def forget_node(self, node):
        """Forget about a node. But this is only possible if all the node's edges have been added.
           Otherwise, we lose information."""
        if len(self.boundary[node]) != len(node.outedges) + len(node.inedges):
            raise UnificationFailure("can't forget a node until all its edges are recognized")
        del self.boundary[node]

    def cutset(self):
        for node, edges in self.boundary.iteritems():
            for nedge in node.inedges + node.outedges:
                if nedge not in edges:
                    yield nedge


class Item(Node):
    def __init__(self, rule, tnode, dot, map, ants):
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
        Node.__init__(self, "Item")
        self.rule = rule
        self.tnode = tnode
        self.dot = dot
        self.map = map
        self.outedges = [ants]

    def __handle__(self):
        return (self.rule, self.tnode, self.dot, self.map.__handle__())

    def __eq__(self, other):
        return isinstance(other, Item) and self.__handle__() == other.__handle__()

    def __ne__(self, other):
        return not (isinstance(other, Item) and self.__handle__() == other.__handle__())

    def __hash__(self):
        return hash(self.__handle__())

    def __str__(self):
        return "[{rule},{tree},<{before}*{after}>,{map}]".format(
            rule=self.rule,
            tree=mark_tree(self.rule.rhs_tree.root, self.tnode),
            before=','.join(map(str, self.tnode.hedges[:self.dot])),
            after=','.join(map(str, self.tnode.hedges[self.dot:])),
            map=self.map
        )


class Goal(Node):
    def __init__(self, ants=None):
        Node.__init__(self, 'Goal')
        if ants:
            self.outedges = [ants]

    def __eq__(self, other):
        return isinstance(other, Goal)

    def __ne__(self, other):
        return not isinstance(other, Goal)

    def __hash__(self):
        return hash("Goal")


class Mapping(object):
    """Represents a bijection between a subgraph of R and a subgraph of H."""

    def __init__(self):
        self.rspan = Subgraph()  # R'
        self.hspan = Subgraph()  # H'
        self.nodemap = {}  # node of R' -> node of H'

    def copy(self):
        newmap = Mapping()
        newmap.nodemap = self.nodemap.copy()
        newmap.rspan = self.rspan.copy()
        newmap.hspan = self.hspan.copy()
        return newmap

    def __str__(self):
        s = ','.join("{0}{{{1}}}->{2}{{{3}}}".format(
            rnode,
            ','.join(str(edge) for edge in self.rspan.boundary[rnode]),
            hnode,
            ','.join(str(edge) for edge in self.hspan.boundary[hnode]))
                     for rnode, hnode in self.nodemap.iteritems())
        return "{{{0}}}".format(s)

    def __handle__(self):
        return (self.rspan.__handle__(),
                self.hspan.__handle__(),
                frozenset(self.nodemap.iteritems()))

    def __eq__(self, other):
        return isinstance(other, Item) and self.__handle__() == other.__handle__()

    def __ne__(self, other):
        return not self == other

    def __hash__(self):
        return hash(self.__handle__())

    def add(self, rnode, hnode):
        if rnode.label != hnode.label:
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
        if redge.label != hedge.label:
            raise UnificationFailure()

        self.add(redge.head, hedge.head)
        for rtail, htail in itertools.izip(redge.tails, hedge.tails):
            self.add(rtail, htail)

        self.rspan.merge(Subgraph.singleton(redge))
        self.hspan.merge(Subgraph.singleton(hedge))

    def add_rewrite(self, redge, subrule, submap):
        if redge.label != subrule.lhs:
            raise UnificationFailure()
        if len(redge.tails) != len(subrule.rhs.exts):
            raise UnificationFailure()

        if len(list(subrule.rhs.root.edges())) == 0:
            # Special case for when subrule.rhs is just a node with no edges.
            # In this case, redge.head is mapped to a node but subrule.rhs.root is not.
            # So we need to check that the node labels match, but don't need to update self.nodemap.

            if redge.head.label != subrule.rhs.root.label:
                raise UnificationFailure()
            #assert redge.head in self.nodemap
        else:
            self.add(redge.head, submap.nodemap[subrule.rhs.root])
        for rtail, stail in itertools.izip(redge.tails, subrule.rhs.exts):
            self.add(rtail, submap.nodemap[stail])

        self.rspan.merge(Subgraph.singleton(redge))
        self.hspan.merge(submap.hspan)

    def merge(self, other):
        for rnode in other.nodemap:
            self.add(rnode, other.nodemap[rnode])

        self.rspan.merge(other.rspan)
        self.hspan.merge(other.hspan)


class Chart(object):
    def __init__(self):
        self.chart = {}
        self.tnode_index = collections.defaultdict(list)
        self.lhs_index = collections.defaultdict(list)
        self.edge_index = collections.defaultdict(list)
        self.agenda = {}
        self.indent_level = 0

    def add(self, item):
        if verbose >= 3:
            print " " * self.indent_level + "add: " + str(item)
        if item in self.chart:
            olditem = self.chart[item]
            olditem.outedges.extend(item.outedges)
            if verbose >= 3:
                print " " * self.indent_level + "  already in chart"
        elif item in self.agenda:
            olditem = self.agenda[item]
            olditem.outedges.extend(item.outedges)
            if verbose >= 3:
                print " " * self.indent_level + "  already in agenda"
        else:
            self.agenda[item] = item

    def get(self):
        key, item = self.agenda.popitem()
        assert key not in self.chart
        self.chart[key] = item

        if isinstance(item, Goal):
            return item

        # index for completed tree nodes
        if item.dot == len(item.tnode.hedges):
            self.tnode_index[item.tnode].append(item)

            # index for completed rhs's
            if item.tnode is item.rule.rhs_tree.root:
                lhs = item.rule.lhs_signature()
                self.lhs_index[lhs].append(item)

        else:
            redge = item.tnode.hedges[item.dot]
            if isinstance(redge.label, Nonterminal):
                lhs = item.rule.rhs_signature(redge)
                self.edge_index[lhs].append(item)

        return item

    def __contains__(self, item):
        return item in self.chart

    def __getitem__(self, item):
        return self.chart[item]


class ParserError(Exception):
    pass


def parse(g, starts, h):
    h.root.marker = True
    chart = Chart()
    # paths = g.all_pairs_shortest_paths()

    edgelabels = set()
    for edge in h.dfs_edges():
        if not isinstance(edge.label, Nonterminal):
            edgelabels.add(edge.label)
        edgelabels.add('F') #add the fake label

    # Preprocess grammar
    g_filtered = []
    for rule in g:
        if verbose >= 3:
            print "Preprocessing rule:", rule

        discard_rule = False
        for edge in rule.rhs.dfs_edges():
            if not isinstance(edge.label, Nonterminal) and edge.label not in edgelabels:
                discard_rule = True
                break
        if discard_rule:
            continue

        # Form tree decomposition
        rule.rhs_tree = rule.rhs.tree_decomposition()
        #TW - I dont know what I'm doing here
        #def remove_fake_edges(node):
        #    good_hedges = []
        #    for h in node.hedges:
        #        if h.label != 'F':
        #            good_hedges.append( h )
        #        else:
        #            print 'removed', h.label
        #    node.hedges = good_hedges
        #    for n in node.outedges:
        #        remove_fake_edges(n.tails[0])
        #remove_fake_edges(rule.rhs_tree.root)

        if verbose >= 3:
            print "Tree decomposition:", rule.rhs_tree

        # Assume (at most) binary branching
        # For each node tnode \in rule.rhs_tree, assume a list tnode.hedges
        # such that every edge in h appears exactly once among all the lists

        g_filtered.append(rule)
    g = g_filtered
    # print "Filtered rules:", len(g)

    # Axioms
    if verbose >= 3:
        print "axioms:"
    chart.indent_level = 2
    for rule in g:
        for tnode in rule.rhs_tree.frontier():
            item = Item(rule, tnode, 0, Mapping(), Edge('Axiom'))
            chart.add(item)

    while len(chart.agenda) > 0:
        trigger = chart.get()
        if trigger == Goal(): continue
        rule = trigger.rule
        tnode = trigger.tnode
        if verbose >= 3:
            print "trigger:", trigger
        chart.indent_level = 2

        if trigger.dot < len(tnode.hedges):
            # There are still edges left to process. Choose the next one, redge.
            redge = tnode.hedges[trigger.dot]

            if isinstance(redge.label, Nonterminal):
                # If redge is labeled with a nonterminal,
                # search for possible rewrites
                lhs = rule.rhs_signature(redge)
                for rewrite in chart.lhs_index[lhs]:
                    if verbose >= 3:
                        print "  rewrite:", rewrite
                    newmap = trigger.map.copy()
                    try:
                        newmap.add_rewrite(redge, rewrite.rule, rewrite.map)
                    except UnificationFailure:
                        pass
                    else:
                        newitem = Item(rule, tnode, trigger.dot + 1, newmap,
                                       Edge('Complete[%s]' % rewrite.rule.id, [trigger, rewrite],
                                            weight=rewrite.rule.weight))
                        chart.add(newitem)

            else:
                # If redge is labeled with a terminal,
                # search for possible matches with edges in h, hedge,
                hedges = h.dfs_edges()
                for hedge in hedges:
                    # and try to add redge->hedge to trigger.map
                    newmap = trigger.map.copy()
                    try:
                        newmap.add_edge(redge, hedge)
                    except UnificationFailure:
                        pass
                    else:
                        newitem = Item(rule, tnode, trigger.dot + 1, newmap, Edge('Shift[%s]' % redge.label, [trigger]))
                        chart.add(newitem)

        elif tnode is not rule.rhs_tree.root:
            # No more edges in tnode left to process; move to parent
            tparent = tnode.inedges[0].head
            if len(tparent.outedges) == 1:
                # only child
                newmap = trigger.map.copy()
                try:
                    newmap.set_domain(tparent.hnodes)
                except UnificationFailure:
                    pass
                else:
                    newitem = Item(rule, tparent, 0, newmap, Edge('Tree', [trigger]))
                    chart.add(newitem)

            elif len(tparent.outedges) == 2:
                # find sister
                tchildren = [edge.tails[0] for edge in tparent.outedges]
                tchildren.remove(tnode)
                (tsister,) = tchildren

                for sister in chart.tnode_index[tsister]:
                    if verbose >= 3:
                        print "  sister:", sister
                    newmap = trigger.map.copy()
                    try:
                        newmap.merge(sister.map)
                        newmap.set_domain(tparent.hnodes)
                    except UnificationFailure:
                        pass
                    else:
                        newitem = Item(rule, tparent, 0, newmap, Edge('Tree', [trigger, sister]))  # order?
                        chart.add(newitem)
            else:
                raise ParserError("tree decomposition not binary branching")

        else:
            # root of rule rhs: look for items to rewrite
            lhs = rule.lhs_signature()
            for rewritee in chart.edge_index[lhs]:
                if verbose >= 3:
                    print "  rewritee:", rewritee
                oedge = rewritee.tnode.hedges[rewritee.dot]
                newmap = rewritee.map.copy()
                try:
                    newmap.add_rewrite(oedge, trigger.rule, trigger.map)
                except UnificationFailure:
                    pass
                else:
                    newitem = Item(rewritee.rule, rewritee.tnode, rewritee.dot + 1, newmap,
                                   Edge('Complete[%s]' % trigger.rule.id, [rewritee, trigger], weight=rule.weight))
                    chart.add(newitem)

            # and check if we're done
            if trigger.map.hspan.full() and len(rule.rhs.exts) == 0 and rule.lhs in starts:
                chart.add(Goal(Edge('Goal', tails=[trigger], weight=rule.weight)))

    sys.stderr.write("%d items\n" % len(chart.chart))
    if Goal() in chart:
        print 'success'
        return Graph(chart[Goal()])
    else:
        print 'fail'
        return None


def product(args):
    result = bigfloat.bigfloat(1.)
    for arg in args:
        result *= arg
    return result


def derive(derivation):
    def visit(node, indent=0):
        assert (len(node.outedges) == 1)

        edge = node.outedges[0]

        node = node.original

        if isinstance(node, Item) and node.dot == len(node.tnode.hedges) and node.tnode is node.rule.rhs_tree.root:
            print '  ' * indent + str(node)
            indent += 1

        if isinstance(node, Goal):
            return visit(edge.tails[0], indent)

        if edge.label.startswith('Complete'):
            aitem, pitem = edge.tails
            nonterminals = visit(aitem, indent)
            aitem = aitem.original
            x = aitem.tnode.hedges[aitem.dot].label
            nonterminals[id(x)] = visit(pitem, indent)
        else:
            nonterminals = {}
            for child in edge.tails:
                nonterminals.update(visit(child, indent))

        if isinstance(node, Item) and node.dot == len(node.tnode.hedges) and node.tnode is node.rule.rhs_tree.root:
            return subst(node.rule.erhs, nonterminals)
        else:
            return nonterminals

    x = visit(derivation.root)
    return x

if __name__ == "__main__":
    import sys
    import argparse

    parser = argparse.ArgumentParser()
    parser.add_argument('-s', '--start', dest='start', type=str, default='0', metavar='nonterminal', help='start symbol')
    parser.add_argument('-k', dest='k', type=int, default=1, metavar='n', help='number of hypotheses to output')
    args = parser.parse_args()

    g = []

    for ri, line in enumerate(open('grammar5')):
        fields = line.split("|||")
        lhs, rhs, erhs = fields[:3]
        if len(fields) == 4:
            weight = float(fields[3])
        else:
            weight = 1.
        r = Rule(lhs=Nonterminal(lhs.strip()),
                 rhs=rhs,
                 erhs=erhs,
                 weight=weight)
        r.id = ri
        g.append(r)

    s = Nonterminal(args.start)

    if verbose >= 1:
        print "Start symbol: {0}\n".format(s)
        print "Input grammar:"
        for r in g:
            print str(r)

    print
    print

    for line in open('input5'):
        h = amr_to_graph(line)

        if verbose >= 1:
            print "Input graph:"
            print h.to_amr()

        forest = parse(g, [s], h)

        if forest:
            if args.k == 1:
                if verbose >= 1:
                    sys.stderr.write("Output graph:\n")
                print derive(forest.viterbi())
            else:
                nbest = NBest(forest)
                for i in xrange(args.k):
                    try:
                        print derive(nbest[i])
                    except IndexError:
                        break
        else:
            if verbose >= 1:
                sys.stderr.write("No derivations\n")
            print ""
