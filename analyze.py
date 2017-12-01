from __future__ import division

import graph
import re
import collections

def unreverse_edges(g):
    if g.root.label == 'multi-sentence':
        roots = [edge.tails[0] for edge in g.root.outedges]
    else:
        roots = [g.root]

    for node in g.dfs():
        edges = []
        for edge in node.outedges:
            reverse = False
            m = re.match(r"(.*)-of$", edge.label)
            if m:
                reverse = True
                newlabel = m.group(1)
            """elif edge.label in ["purpose"] and not re.match(r".*-\d+^", node.label):
                reverse = True
                newlabel = edge.label + '-of'"""
            if reverse:
                (root,) = edge.tails
                root.outedges.append(graph.Edge(newlabel, [node]))
                roots.append(root)
            else:
                edges.append(edge)
        node.outedges = edges

    dummy = graph.Graph(graph.Node('dummy', [graph.Edge('dummy', [root]) for root in roots]))
    components = dummy.scc()
    cindex = {}
    for ci, component in enumerate(components):
        for node in component:
            cindex[node] = ci

    reachable = set()
    for node in dummy.dfs():
        if node is dummy:
            reachable.add(cindex[node])
            continue
        for edge in node.outedges:
            for tail in edge.tails:
                if cindex[node] != cindex[tail]:
                    reachable.add(cindex[tail])

    roots = [component.pop() for ci, component in enumerate(components) if ci not in reachable]

    if len(roots) > 1:
        edges = []
        for ri, root in enumerate(roots):
            edges.append(graph.Edge('snt{0}'.format(ri+1), [root]))
        g.root = graph.Node('multi-sentence', edges)
    else:
        g.root = roots[0]

    g.update()

def has_cycle(g):
    components = g.scc()
    for component in components:
        if len(component) > 1:
            return component
        else:
            # look for self-loop
            (node,) = component
            for edge in node.outedges:
                if node in edge.tails:
                    return [node]
    return None

def count_levels(g):
    stack = []
    def visit(node):
        stack.append(node)
        l = (0, [])
        for edge in node.outedges:
            for tail in edge.tails:
                l = max(l, visit(tail))
        # do not count inedges from multi-sentence
        if len([edge for edge in node.inedges if edge.head.label != "multi-sentence"]) > 1:
            depth, nodes = l
            l = depth+1, [node]+nodes
        stack.pop()
        return l
    depth, nodes = visit(g.root)
    return nodes

if __name__ == "__main__":
    import fileinput, sys, re, itertools
    lines = []
    amr_id = None
    for line in fileinput.input():
        if line.lstrip().startswith("#"):
            m = re.search(r"::id (\S+)", line)
            if m:
                amr_id = m.group(1)
        else:
            lines.append((amr_id, line))

    l_histogram = collections.Counter()
    tw_histogram = collections.Counter()
    degree_histogram = collections.Counter()
    for amr_id, group in itertools.groupby(lines, lambda (a, g): a):
        s = "".join(g for (a, g) in group)
        i = 0
        while i < len(s):
            try:
                g, i = graph.amr_to_graph(s, start=i, return_end=True)
            except:
                sys.stderr.write("error reading graph at line %s\n" % (len(s[:i].split("\n"))))
                raise
            if not g:
                break

            print 'id:', amr_id
            print '  original graph:  ', g
            unreverse_edges(g)
            print '  unreversed graph:', g
            cycle = has_cycle(g)
            if cycle:
                print "  cycle: %s" % (', '.join([str(node.var) for node in cycle]))

            else:
                nodes = count_levels(g)
                if len(nodes) > 0:
                    print "  reentrancies nested %s deep: %s" % (len(nodes), ', '.join([str(node.var) for node in nodes]))
                l_histogram[len(nodes)] += 1

            t = g.tree_decomposition()
            tw = max(len(node)-1 for node in t)
            print "  treewidth = %s" % tw
            tw_histogram[tw] += 1
            if False:
                print "edges:"
                for node in g.dfs():
                    if node.label == graph.PSEUDOROOT: continue
                    for edge in node.outedges:
                        print id(node), id(edge.tails[0])
                print "END"
                print g.to_dot()

            # count degree
            max_degree = None
            for node in g.dfs():
                if node.label == graph.PSEUDOROOT: continue
                degree = len(node.inedges) + len(node.outedges)
                #if degree == 0: continue
                degree_histogram[degree] += 1
                max_degree = max(max_degree, degree)
            print "  max degree", max_degree

    print "nested reentrancies:"
    for depth in sorted(l_histogram):
        print "%s deep\t%s AMRs" % (depth, l_histogram[depth])

    print "treewidth:"
    n = sum(c for (tw,c) in tw_histogram.iteritems())
    cumul = 0
    for tw in sorted(tw_histogram):
        cumul += tw_histogram[tw]
        print "%s\t%s\t%s" % (tw, tw_histogram[tw], cumul)
    print "average %s" % (sum(tw*c for (tw,c) in tw_histogram.iteritems()) / n)

    print "degree:"
    n = sum(c for (d,c) in degree_histogram.iteritems())
    print "degree\tnodes\tprobability"
    for degree in sorted(degree_histogram):
        print "%s\t%s\t%s" % (degree, degree_histogram[degree], degree_histogram[degree]/n)
    print "average %s" % (sum(d*c for (d,c) in degree_histogram.iteritems()) / n)
