#!/usr/bin/env python

import collections, itertools, random
from graph import *
from grammar import *

verbose = 1

def sample(rules):
    sumweight = sum(rule.weight for rule in rules)
    p = random.uniform(0., sumweight)
    q = 0.
    for rule in rules:
        q += rule.weight
        if q >= p:
            return rule

if __name__ == "__main__":
    import sys
    import argparse

    parser = argparse.ArgumentParser()
    parser.add_argument('grammars', type=str, metavar='grammar', nargs='+', help='file containing grammar rules')
    parser.add_argument('-s', '--start', dest='start', type=str, default='Truth', metavar='nonterminal', help='start symbol')
    parser.add_argument('-k', dest='k', type=int, default=1, metavar='n', help='number of hypotheses to output')
    args = parser.parse_args()

    s = Nonterminal(args.start)

    g = []
    lhs_index = collections.defaultdict(list)
    start_rules = []
    for grammarfile in args.grammars:
        for line in open(grammarfile):
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
            g.append(r)
            lhs_index[r.lhs_signature()].append(r)
            if r.lhs == s and len(r.rhs.exts) == 0:
                start_rules.append(r)

    if verbose >= 1:
        sys.stderr.write("Start symbol: {0}\n".format(s))
        sys.stderr.write("Input grammar:\n")
        for r in g:
            sys.stderr.write(str(r) + "\n")

    for i in xrange(args.k):
        r = sample(start_rules)
        stack = [(r, edge) for edge in r.rhs_index.itervalues() if isinstance(edge.label, Nonterminal)]
        h = r.rhs
        while len(stack) > 0:
            r, edge = stack.pop()
            rewrite = sample(lhs_index[r.rhs_signature(edge)])
            h = subst(h, {id(edge.label) : rewrite})
        print h

