import networkx
import collections
import hypergraphs


class ParseError(Exception):
    pass


class QuotedString(str):
    pass


class Node(str):
    pass


def format_sexp(x):
    if isinstance(x, list):
        return "({})".format(" ".join(map(format_sexp, x)))
    else:
        s = str(x)
        if isinstance(x, QuotedString) or any(c.isspace() or c in '()"\\' for c in s):
            return '"{}"'.format(s.replace('\\', '\\\\').replace('"', r'\"'))
        else:
            return s


def parse_sexp(s):
    def skip_space():
        while len(s) > 0 and s[0].isspace():
            s.popleft()

    def parse_atom():
        if len(s) == 0:
            raise ParseError("unexpected end of expression")
        atom = []
        if s[0] == '"':
            s.popleft()
            escape = False
            while len(s) > 0:
                c = s.popleft()
                if escape:
                    atom.append(c)
                    escape = False
                elif c == '\\':
                    escape = True
                elif c == '"':
                    break
                else:
                    atom.append(c)
            else:
                raise ParseError("unexpected end of expression in middle of string")
            if len(s) > 0 and not s[0].isspace() and s[0] != ')':
                raise ParseError("unexpected stuff after close quote")
            return QuotedString(''.join(atom))
        else:
            while len(s) > 0 and not s[0].isspace() and s[0] != ')':
                atom.append(s.popleft())
            return ''.join(atom)

    def parse_start():
        if len(s) > 0 and s[0] == '(':
            xs = []
            s.popleft()  # (
            skip_space()
            while len(s) > 0 and s[0] != ')':
                xs.append(parse_start())
                skip_space()
            s.popleft()  # )
            return xs
        else:
            return parse_atom()

    s = collections.deque(s)
    skip_space()
    result = parse_start()
    skip_space()
    if len(s) > 0:
        raise ParseError("extra stuff after expression {}".format(result))
    return result


def format_amr(g, show_all=False):
    visited = set()

    def visit(v):
        if v in visited:
            return v
        visited.add(v)
        cdr = []
        assert not isinstance(v, hypergraphs.Hyperedge)
        if 'label' in g.node[v]:
            if isinstance(v, Node) and not show_all:
                car = g.node[v]['label']
            else:
                car = v
                cdr.extend(['/', g.node[v]['label']])
        else:
            # used for printing trees
            car = v

        for e in hypergraphs.edges(g, v, 0):
            if hypergraphs.edge(g, e).get('label', None) is not None:
                cdr.append(':{}'.format(hypergraphs.edge(g, e)['label']))
            for child in e[1:]:
                cdr.append(visit(child))
        if cdr:
            return [car] + cdr
        else:
            return car

    if 'root' in g.graph:
        root = g.graph['root']
    else:
        raise ValueError("graph must have a root")
    return format_sexp(visit(root))


def parse_amr(s):
    """Convert an AMR (as a str) into a NetworkX directed graph."""
    expr = parse_sexp(s)
    g = networkx.DiGraph()
    vars = {}
    anon = set()

    def visit(expr):
        if isinstance(expr, list):
            # Read parent node
            if len(expr) >= 3 and not isinstance(expr[1], QuotedString) and expr[1] == '/':
                node = expr[0]
                label = expr[2]
                expr = expr[3:]
                if node in vars:
                    raise ParseError("duplicate variables ({})".format(node))
                vars[node] = label
            else:
                node = Node("_{}".format(len(anon)))
                anon.add(node)
                label = expr[0]
                expr = expr[1:]
                i = 1
            g.add_node(node, label=label)

            # Read child nodes
            edges = []
            for x in expr:
                if isinstance(x, str) and not isinstance(x, QuotedString) and x.startswith(':'):
                    edges.append([x[1:]])
                else:
                    if len(edges) == 0:
                        edges.append([None])
                    edges[-1].append(visit(x))

            # for [label, *nodes] in edges: # python3
            for ln in edges:
                label = ln[0]
                nodes = ln[1:]
                if label:
                    attrs = {'label': label}
                else:
                    attrs = {'label': None}
                if len(nodes) == 1:
                    g.add_edge(node, nodes[0], **attrs)
                else:
                    hypergraphs.add_hyperedge(g, [node] + nodes, **attrs)

            return node

        # Leaf node
        elif isinstance(expr, str):
            if expr in vars:
                node = expr
            else:
                node = Node("_{}".format(len(anon)))
                anon.add(node)
                g.add_node(node, label=expr)
            return node

        else:
            raise TypeError()

    root = visit(expr)
    g.graph['root'] = root
    return g


if __name__ == "__main__":
    import sys

    for s in sys.stdin:
        print(s.rstrip())
        g = parse_amr(s)
        print(format_amr(g))

