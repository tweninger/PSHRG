import collections
import heapq
import itertools
import random

import bigfloat
import treewidth

PSEUDOROOT = 'multi-sentence'


class Graph(object):
    """
    This data structure does triple duty. It is used for:
    - semantic graphs
    - tree decompositions
    - derivation forests
    """

    def __init__(self, arg):
        if isinstance(arg, Node):
            self.root = arg
        elif type(arg) in [str, unicode]:
            self.root = amr_to_graph(arg).root
        else:
            raise ValueError("can't initialize Graph from type {0}".format(type(arg)))

        self.update()

    def update(self):
        """Call this method after the graph structure has been modified"""
        self._compute_inedges()

    def _compute_inedges(self):
        # Add upward pointers to Nodes and Edges.
        # The reason we don't do this at the time that they are constructed
        # is to allow the structure to be modified afterwards.
        # However, after the Graph is constructed, please don't modify the structure
        for node in self.dfs():
            node.inedges = []

        for node in self.dfs():
            for edge in node.outedges:
                edge.head = node
                for child in edge.tails:
                    child.inedges.append(edge)

    def copy(self, memo=None):
        if memo is None: memo = {}
        if id(self) not in memo:
            memo[id(self)] = Graph(self.root.copy(memo))
        return memo[id(self)]

    def __str__(self):
        return self.to_amr()

    def to_amr(self, node_to_str=None, edge_to_str=None):
        count = collections.Counter()

        def visit(node):
            count[node] += 1

            if count[node] > 1:
                return node.var

            # Format node label
            if node_to_str:
                label = node_to_str(node)
            # elif " " in node.label:
            #    label = '"%s"' % node.label
            else:
                label = str(node.label)
            if node.var:
                label = "{0} / {1}".format(node.var, label)

            if node.outedges:
                edgestrings = []

                for ei, edge in enumerate(node.outedges):
                    if edge_to_str:
                        edgestrings.append(":{0}".format(edge_to_str(edge)))
                    elif edge.label:
                        edgestrings.append(":{0}".format(edge.label))
                    elif ei > 0:
                        # it's ok if the first edge has no explicit label
                        edgestrings.append(":")
                    edgestrings.extend([visit(child) for child in edge.tails])
                s = "({0} {1})".format(label, " ".join(edgestrings))
            else:
                if node.var:  # parens are obligatory in this case
                    s = "({0})".format(label)
                else:
                    s = label
            return s

        return visit(self.root)

    def to_dot(self):
        # assign name to each node
        name = {}
        for node in self.dfs():
            if node.var:
                s = "%s / %s" % (node.var, node.label)
                assert s not in name
                name[node] = s
            elif node.label not in name:
                name[node] = node.label
            else:
                name[node] = "%s_%s" % (node.label, len(name))

        result = []
        result.append("digraph G {\n")
        for node in self.dfs():
            if node.label == PSEUDOROOT: continue
            for edge in node.outedges:
                if len(edge.tails) > 1:
                    raise ValueError("hypergraphs not allowed")
                (tail,) = edge.tails
                result.append('  "%s" -> "%s" [label="%s"];\n' % (
                name[node].replace('"', '\\"'), name[tail].replace('"', '\\"'), edge.label.replace('"', '\\"')))
        result.append("}\n")
        return "".join(result)

    def undirected_graph(self):
        """Return an adjacency list of the graph, viewed as an undirected graph"""
        graph = collections.defaultdict(set)
        for node in self.dfs():
            if node.label == PSEUDOROOT: continue
            graph.setdefault(node, set())
            for edge in node.outedges:
                treewidth.make_clique(graph, [node] + edge.tails)
        return graph

    def directed_graph(self):
        """Return an adjacency list of the graph, viewed as an directed graph"""
        graph = collections.defaultdict(set)
        for node in self.dfs():
            if node.label == PSEUDOROOT: continue
            graph.setdefault(node, set())
            for edge in node.outedges:
                for tail in edge.tails:
                    graph[node].add(tail)
        return graph

    def tree_decomposition(self):
        graph = self.undirected_graph()
        tree = treewidth.quickbb(graph)
        return tree

    def dfs(self):
        memo = set()
        result = []

        def visit(node):
            if node in memo:
                return
            memo.add(node)
            result.append(node)
            for edge in node.outedges:
                for child in edge.tails:
                    visit(child)

        visit(self.root)
        return result

    def dfs_edges(self):
        for node in self.dfs():
            for edge in node.outedges:
                yield edge

    def scc(self):
        """Tarjan's algorithm"""
        order = {}
        lowlink = {}
        stack = []
        components = []

        def visit(v):
            i = len(order)
            order[v] = i
            lowlink[v] = i
            stack.append(v)

            for edge in v.outedges:
                for tail in edge.tails:
                    if tail not in order:
                        visit(tail)
                        lowlink[v] = min(lowlink[v], lowlink[tail])
                    elif tail in stack:
                        lowlink[v] = min(lowlink[v], order[tail])

            if lowlink[v] == order[v]:
                vi = stack.index(v)
                component = set(stack[vi:])
                del stack[vi:]
                components.append(component)

        for v in self.dfs():
            if v not in order:
                visit(v)

        return components

    def frontier(self):
        return [node for node in self.dfs() if len(node.outedges) == 0]

    def viterbi_edges(self):
        """return a dict of Node -> (probability, Edge)"""
        memo = {}

        def visit(node):
            if node in memo:
                p, _ = memo[node]
                return p
            # We put a zero probability into the memo already
            # in case one of our descendants points back to self.
            # This will cause the descendant not to choose self.
            memo[node] = pmax, emax = (0., None)
            for edge in node.outedges:
                p = bigfloat.bigfloat(edge.weight)
                for child in edge.tails:
                    p *= visit(child)
                if emax is None or p > pmax:
                    pmax, emax = p, edge

            memo[node] = pmax, emax
            return pmax

        visit(self.root)

        return memo

    def construct(self, edges):
        def visit(node):
            edge = edges[node]
            newedge = Edge(edge.label,
                           tails=[visit(tail) for tail in edge.tails],
                           weight=edge.weight)
            newnode = Node(node.label, outedges=[newedge])
            newnode.original = node
            return newnode

        return Graph(visit(self.root))

    def viterbi(self):
        edges = {node: edge for (node, (_, edge)) in self.viterbi_edges().items()}
        return self.construct(edges)

    def inside(self):
        memo = {}

        def visit(node):
            if node in memo:
                p = memo[node]
                return p
            memo[node] = psum = 0.
            for edge in node.outedges:
                p = bigfloat.bigfloat(edge.weight)
                for child in edge.tails:
                    p *= visit(child)
                psum += p

            memo[node] = psum
            return psum

        visit(self.root)
        return memo

    def sample(self, inside):
        edges = {}
        for node in self.dfs():
            ps = []
            # Recompute the edge inside weights because we threw them away before
            for edge in node.outedges:
                p = bigfloat.bigfloat(edge.weight)
                for child in edge.tails:
                    p *= inside[child]
                ps.append((p / inside[node], edge))
            r = random.random()
            psum = 0.
            for p, edge in ps:
                psum += p
                if psum > r:
                    edges[node] = edge
                    break
            else:
                assert False
        return self.construct(edges)

    def all_pairs_shortest_paths(self):
        """Returns a dictionary paths, where paths[u,v] is a pair of
        the shortest path from u to v and the last edge along that path."""
        paths = {}
        g = self.undirected_graph()
        for u in g:
            paths[u, u] = (0, None)
            for edge in u.outedges:
                for v in edge.tails:
                    paths[u, v] = (1, edge)
        for w in g:
            for u in g:
                for v in g:
                    if paths[u, v][0] > paths[u, w][0] + paths[w, v][0]:
                        paths[u, v] = (paths[u, w][0] + paths[w, v][0], paths[w, v][1])
        return paths


def amr_to_graph(s, start=0, return_end=False):
    def scan_space(i):
        while s[i].isspace():
            i += 1
        return i

    def scan_label(i):
        j = i
        if s[j] == '"':
            j += 1
            while s[j] != '"':
                j += 1
            j += 1
        else:
            # while not s[j].isspace() and s[j] != ')':
            while not s[j].isspace() and s[j] != ')' and s[j] not in "./:":
                j += 1
        return s[i:j], j

    def scan_edge(i):
        i = scan_space(i)

        if s[i] == ')':
            return None, i

        else:
            if s[i] == ':':
                label, i = scan_label(i + 1)
            else:
                label = 'E'
            tails = []
            while True:
                tail, i = _scan_node(i)
                if tail is None:
                    break
                else:
                    tails.append(tail)
            return Edge(label=label, tails=tails), i

    def _scan_node(i):
        i = scan_space(i)

        if s[i] in [')', ':']:
            return None, i

        elif s[i] == '(':
            i = scan_space(i + 1)
            label, i = scan_label(i)

            # look ahead for a /
            memoize = False
            i = scan_space(i)
            # if s[i] == '/':
            if s[i] in '/.':
                var = label
                i = scan_space(i + 1)
                label, i = scan_label(i)
                memoize = True

            edges = []
            while True:
                edge, i = scan_edge(i)
                if edge is None:
                    assert s[i] == ')'
                    i += 1
                    break
                else:
                    edges.append(edge)
            node = Node(label=label, outedges=edges)
            if memoize:
                node.var = var
                memo[var] = node
            return node, i

        else:
            label, i = scan_label(i)

            # need for Bolinas format:
            memoize = False
            i = scan_space(i)
            # if s[i] == '/':
            if s[i] == '.':
                var = label
                i = scan_space(i + 1)
                label, i = scan_label(i)
                memoize = True

            node = Node(label=label)

            # need for Bolinas format:
            if memoize:
                node.var = var
                memo[var] = node

            return node, i

    def resolve(node):
        if node.outedges:
            for edge in node.outedges:
                edge.tails = [resolve(tail) for tail in edge.tails]
            return node
        else:
            if len(node.outedges) == 0 and node.var is None and node.label in memo:
                return memo[node.label]
            else:
                return node

    def scan_node(s, start=0, return_end=False):
        root, end = _scan_node(start)
        if root:
            resolve(root)

        if return_end:
            return root, end
        else:
            return root

    memo = {}

    i = start
    while i < len(s) and s[i].isspace():
        i += 1
    if i == len(s):
        g = None
    else:
        root, i = scan_node(s, i, True)
        g = Graph(root)

    if return_end:
        return g, i
    else:
        return g




class Node(object):
    def __init__(self, label='E', outedges=None):
        self.label = label
        self.var = None
        self.inedges = []
        self.outedges = outedges or []
        self.marker = False

    def copy(self, memo=None):
        if memo is None: memo = {}
        if id(self) not in memo:
            memo[id(self)] = Node(self.label, [edge.copy(memo) for edge in self.outedges])
        return memo[id(self)]

    def __str__(self):
        if self.var:
            return "{0} / {1}".format(self.var, self.label)
        else:
            return str(self.label)

    def edges(self):
        for edge in self.inedges:
            yield edge
        for edge in self.outedges:
            yield edge


class Edge(object):
    def __init__(self, label='E', tails=None, weight=1.):
        self.label = label
        self.head = None
        self.tails = tails or []
        self.weight = weight

    def copy(self, memo=None):
        if memo is None: memo = {}
        if id(self) not in memo:
            memo[id(self)] = Edge(self.label, [tail.copy(memo) for tail in self.tails], self.weight)
        return memo[id(self)]

    def __str__(self):
        return str(self.label)

    def nodes(self):
        yield self.head
        for tail in self.tails:
            yield tail


class NBestInfo(object):
    """Information about a Node that is needed for n-best computation"""

    def __init__(self, node, viterbi):
        self.nbest = []  # of (viterbi, edge, tailranks)
        self.cands = []  # priority queue of (viterbi, edge, tailranks)
        self.index = set()  # of (edge, tailranks)
        for edge in node.outedges:
            zeros = (0,) * len(edge.tails)
            p = bigfloat.bigfloat(edge.weight)
            for tail in edge.tails:
                tail_viterbi, _ = viterbi[tail]
                p *= tail_viterbi
            self.cands.append((-p, edge, zeros))
            self.index.add((edge, zeros))
        heapq.heapify(self.cands)
        (p, edge, ranks) = heapq.heappop(self.cands)
        self.nbest.append((p, edge, ranks))


class NBest(object):
    def __init__(self, graph):
        self.graph = graph
        self.nbinfos = {}
        viterbi_edges = graph.viterbi_edges()
        for node in graph.dfs():
            self.nbinfos[node] = NBestInfo(node, viterbi_edges)

    def compute_nbest(self, node, n):
        nb = self.nbinfos[node]

        while len(nb.nbest) < n:
            # Extend the candidate pool
            p, edge, ranks = nb.nbest[-1]
            for tail_i in xrange(len(edge.tails)):
                tail, rank = edge.tails[tail_i], ranks[tail_i]

                if self.compute_nbest(tail, rank + 2) >= rank + 2:
                    tail_nb = self.nbinfos[tail]
                    nextranks = list(ranks)
                    nextranks[tail_i] += 1
                    nextranks = tuple(nextranks)
                    if (edge, nextranks) not in nb.index:
                        nextp = p / tail_nb.nbest[rank][0] * tail_nb.nbest[rank + 1][0]
                        heapq.heappush(nb.cands, (nextp, edge, nextranks))
                        nb.index.add((edge, nextranks))

            if len(nb.cands) > 0:
                # Get the next best and add it to the list
                (p, edge, ranks) = heapq.heappop(nb.cands)
                nb.nbest.append((p, edge, ranks))
            else:
                break

        return len(nb.nbest)

    def __getitem__(self, i):
        self.compute_nbest(self.graph.root, i + 1)
        return Graph(self._getitem_helper(self.graph.root, i))

    def _getitem_helper(self, node, i):
        nb = self.nbinfos[node]
        p, edge, ranks = nb.nbest[i]

        newtails = []
        for tail, rank in itertools.izip(edge.tails, ranks):
            newtails.append(self._getitem_helper(tail, rank))

        newedge = Edge(edge.label, tails=newtails, weight=edge.weight)
        newnode = Node(node.label, outedges=[newedge])
        newnode.original = node
        return newnode
