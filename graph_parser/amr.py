import networkx
import collections
import hypergraphs


class ParseError(Exception):
    pass


class QuotedString(str):
    pass


class Node(object):
    pass


def format_sexp(x):
    if isinstance(x, list):
        return "({})".format(" ".join(map(format_sexp, x)))
    elif isinstance(x, str):
        if any(c.isspace() or c in '()"\\' for c in x):
            return '"{}"'.format(x.replace('\\', '\\\\').replace('"', r'\"'))
        else:
            return x
    else:
        raise TypeError("unexpected {}".format(type(x)))


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


def format_amr(g, hyper=False):
    visited = set()

    def visit(v):
        if v in visited:
            return v
        visited.add(v)
        if len(g.edges(v)) == 0 and isinstance(v, Node):
            return g.node[v]['label']
        xs = []
        assert not isinstance(v, hypergraphs.Hyperedge)
        if isinstance(v, Node):
            xs.append(g.node[v]['label'])
        else:
            xs.extend([v, '/', g.node[v]['label']])
        if hyper:
            for e in hypergraphs.get_hyperedges(g, v):
                if 'label' in g.node[e]:
                    xs.append(':{}'.format(g.node[e]['label']))
                for child in g.neighbors(e):
                    if child == v: continue
                    xs.append(visit(child))
        else:
            for (v, child) in g.edges(v):
                if 'label' in g[v][child]:
                    xs.append(':{}'.format(g[v][child]['label']))
                xs.append(visit(child))
        return xs

    return format_sexp(visit(g.graph['root']))


def parse_amr(s, hyper=False):
    """Convert an AMR (as a str) into a NetworkX directed graph."""
    expr = parse_sexp(s)
    g = networkx.DiGraph()
    vars = {}

    def visit(expr):
        if isinstance(expr, list):
            # Read parent node
            if len(expr) >= 3 and not isinstance(expr[1], QuotedString) and expr[1] == '/':
                node = expr[0]
                label = expr[2]
                expr = expr[3:]
                if node in vars:
                    raise ParseError("duplicate variables")
                vars[node] = label
            else:
                node = Node()
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

            for [label, heads] in edges:
                if label:
                    attrs = {'label': label}
                else:
                    attrs = {}
                if hyper:
                    hypergraphs.add_hyperedge(g, [node], heads, **attrs)
                else:
                    if len(heads) != 1:
                        raise ValueError("edge with {} heads (use hyper=True)".format(len(heads)))
                    g.add_edge(node, heads[0], **attrs)

            return node

        # Leaf node
        elif isinstance(expr, str):
            if expr in vars:
                node = expr
            else:
                node = Node()
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
        g = parse_amr(s, hyper=True)
        print(format_amr(g, hyper=True))
