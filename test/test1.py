# This should be the same as grammar1 and input1.

import networkx
import parser
import hypergraphs
import amr
import grammar


if __name__ == "__main__":
    frules = []
    erules = []

    # Rule 1
    lhs = grammar.Nonterminal("Truth")

    frhs = networkx.DiGraph(root="i1")
    frhs.add_node("i1", label="instance")
    frhs.add_node("want", label="want")
    frhs.add_edge("i1", "want", label="id")
    frhs.add_node("x", label="instance")
    frhs.add_edge("i1", "x", label="agent")
    hypergraphs.add_hyperedge(frhs, ("x",), label=grammar.Nonterminal("Entity"), link=0)
    frhs.add_node("i2", label="instance")
    frhs.add_edge("i1", "i2", label="theme")
    hypergraphs.add_hyperedge(frhs, ("i2", "x"), label=grammar.Nonterminal("Truth"), link=1)
    frules.append(grammar.Rule(lhs, frhs, id=0))

    erhs = networkx.DiGraph(root="0")
    erhs.add_node("0", label="S")
    erhs.add_node("1", label="NP")
    erhs.add_node("2", label="VP")
    hypergraphs.add_hyperedge(erhs, ("0", "1", "2"))
    hypergraphs.add_hyperedge(erhs, ("1",), label=grammar.Nonterminal("Entity"), link=0)
    erhs.add_node("21", label="VBP")
    erhs.add_node("22", label="SBAR")
    hypergraphs.add_hyperedge(erhs, ("2", "21", "22"))
    erhs.add_node("211", label="want")
    hypergraphs.add_hyperedge(erhs, ("21", "211"))
    hypergraphs.add_hyperedge(erhs, ("22",), label=grammar.Nonterminal("Truth"), link=1)
    erules.append(grammar.Rule(lhs, erhs, id=0))

    # Rule 2
    lhs = grammar.Nonterminal("Truth")

    frhs = networkx.DiGraph(root="i1")
    frhs.add_node("i1", label="instance", external=0)
    frhs.add_node("see", label="see")
    frhs.add_edge("i1", "see", label="id")
    frhs.add_node("i2", label="instance", external=1)
    frhs.add_edge("i1", "i2", label="agent")
    frules.append(grammar.Rule(lhs, frhs, id=1))

    erhs = networkx.DiGraph(root="0")
    erhs.add_node("0", label="SBAR", external=0)
    erhs.add_node("1", label="TO")
    erhs.add_node("2", label="S")
    hypergraphs.add_hyperedge(erhs, ("0", "1", "2"))
    erhs.add_node("11", label="to")
    erhs.add_edge("1", "11")
    erhs.add_node("21", label="VP")
    erhs.add_edge("2", "21")
    erhs.add_node("211", label="VB")
    erhs.add_edge("21", "211")
    erhs.add_node("2111", label="see")
    erhs.add_edge("211", "2111")
    erules.append(grammar.Rule(lhs, erhs, id=1))

    lhs = grammar.Nonterminal("Entity")

    frhs = networkx.DiGraph(root="i1")
    frhs.add_node("i1", label="instance", external=0)
    frhs.add_node("i", label="i")
    frhs.add_edge("i1", "i", label="id")
    frules.append(grammar.Rule(lhs, frhs, id=2))

    erhs = networkx.DiGraph(root="0")
    erhs.add_node("0", label="NP", external=0)
    erhs.add_node("1", label="PRP")
    erhs.add_edge("0", "1")
    erhs.add_node("11", label="I")
    erhs.add_edge("1", "11")
    erules.append(grammar.Rule(lhs, erhs, id=2))

    g = networkx.DiGraph(root="i1")
    g.add_node("i1", label="instance")
    g.add_node("want", label="want")
    g.add_edge("i1", "want", label="id")
    g.add_node("x", label="instance")
    g.add_edge("i1", "x", label="agent")
    g.add_node("i", label="i")
    g.add_edge("x", "i", label="id")
    g.add_node("i2", label="instance")
    g.add_edge("i1", "i2", label="theme")
    g.add_node("see", label="see")
    g.add_edge("i2", "see", label="id")
    g.add_edge("i2", "x", label="agent")

    forest = parser.parse(frules, [grammar.Nonterminal("Truth")], g)
    print(amr.format_amr(grammar.derive(parser.viterbi(forest), erules)))
