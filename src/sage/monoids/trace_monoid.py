# ***************************************************************************************************
#  Copyright (C) 2019      Pavlo Tokariev (Kharkiv National Universiy) <pavlo.tokariev at google mail service>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
# ***************************************************************************************************

"""
Trace monoids
"""

from __future__ import print_function

import copy
from collections import OrderedDict
from itertools import repeat, chain, product, combinations_with_replacement

from sage.misc.cachefunc import cached_method

from sage.graphs.digraph import DiGraph
from sage.graphs.graph import Graph
from sage.monoids.free_monoid import FreeMonoid
from sage.monoids.free_monoid_element import FreeMonoidElement
from sage.rings.integer import Integer
from sage.rings.integer_ring import ZZ
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.power_series_ring import PowerSeriesRing
from sage.sets.set import Set
from sage.structure.parent import Set_generic


class TraceMonoidElement(FreeMonoidElement):
    def _dependence_stack(self):
        independence = self.parent().independence
        generators_set = sorted(e[0] for e in self._element_list)
        stacks = OrderedDict(sorted((g, []) for g in generators_set))
        for element in reversed(self._element_list):
            generator, amount = element
            stacks[generator].extend(repeat(True, amount))
            for other_gen in generators_set:
                if other_gen == generator:
                    continue
                if (generator, other_gen) not in independence:
                    stacks[other_gen].extend(repeat(False, amount))
        return generators_set, stacks

    @cached_method
    def lexic_norm_form(self, alg="sort"):
        if alg == "sort":
            return self._sort_lex_nform()
        elif alg == "stack":
            return self._stack_lex_nform()
        else:
            raise ValueError("Unknown lexicographic form algorithm `{}`.".format(alg))

    def _sort_lex_nform(self):
        elements = copy.copy(self._element_list)
        independence = self.parent().independence

        for i in range(len(elements)):
            for j in range(i, -1, -1):
                if j > 0 and elements[j - 1][0] > elements[i][0] and \
                        (elements[i][0], elements[j - 1][0]) in independence:
                    continue
                if j == i:
                    break
                moved, elements = elements[i], elements[:i] + elements[i + 1:]
                elements.insert(j, moved)
                break

        return self.parent(elements)

    def _stack_lex_nform(self):
        monoid = self.parent()
        if not self._element_list:
            return self
        generators_set, stacks = self._dependence_stack()
        independence = monoid.independence

        elements = []
        while True:
            empty_stacks = []
            for generator, g_stack in stacks.items():
                if g_stack:
                    empty_stacks.append(False)
                    if g_stack[-1]:
                        g_stack.pop()
                        elements.append(generator)
                        for other_gen in generators_set:
                            if other_gen != generator and (generator, other_gen) not in independence:
                                stacks[other_gen].pop()
                        break
                else:
                    empty_stacks.append(True)

            if all(empty_stacks):
                break

        return monoid([(e, 1) for e in elements])

    @cached_method
    def foata_norm_form(self):
        monoid = self.parent()
        if not self._element_list:
            return FoataNormalForm(monoid, [])

        generators_set, stacks = self._dependence_stack()
        independence = monoid.independence

        steps = []
        while True:
            empty_stacks = []
            step = []
            for generator, g_stack in stacks.items():
                if g_stack:
                    if g_stack[-1]:
                        g_stack.pop()
                        step.append(generator)
                    empty_stacks.append(False)
                else:
                    empty_stacks.append(True)

            if all(empty_stacks):
                break

            for g in step:
                for other_gen in generators_set:
                    if other_gen != g and (g, other_gen) not in independence:
                        stacks[other_gen].pop()

            if step:
                steps.append(step)

        steps = (monoid(list((v, 1) for v in step)) for step in steps)
        return FoataNormalForm(monoid, steps)

    def _graph_labels(self, elements, labeled=True):
        f = self.parent().monoid_generators()
        labels = {}

        for i, e in enumerate(elements):
            if labeled:
                e = f[e]
            labels[i] = (i, e)

        return labels

    def _plain_elements(self):
        return list(chain.from_iterable(repeat(e, times) for e, times in self._element_list))

    @cached_method
    def dependency_graph(self, labeled=True):
        elements = self._plain_elements()
        independence = self.parent().independence
        graph = {}

        for i, e in enumerate(elements):
            edges = []
            for v in graph:
                if (e, elements[v]) not in independence:
                    edges.append((v, i))
            graph[i] = []
            for v1, v2 in edges:
                graph[v1].append(v2)

        g = DiGraph(graph)
        g.relabel(self._graph_labels(elements, labeled=labeled))
        return g

    @cached_method
    def hasse_diagram(self, labeled=True):
        d = self.dependency_graph(labeled=labeled)
        h = d.copy()

        for e1 in d.edges():
            for e2 in d.edges():
                if e1[1] == e2[0]:
                    h.delete_edge((e1[0], e2[1]))

        return h

    def _richcmp_(self, other, op):
        return super(TraceMonoidElement, self.lexic_norm_form())._richcmp_(other.lexic_norm_form(), op)


class FoataNormalForm(TraceMonoidElement):
    def __init__(self, monoid, steps):
        self._steps = tuple(steps)
        elements = list(chain.from_iterable(map(lambda x: x._element_list, self._steps)))
        super(TraceMonoidElement, self).__init__(monoid, elements)

    @property
    def steps(self):
        return self._steps

    def _repr_(self):
        return "".join("({})".format(step) for step in self.steps)

    def _latex_(self):
        return "".join("\\({}\\)".format(step) for step in self.steps)


class TraceMonoid(FreeMonoid):
    Element = TraceMonoidElement

    def __init__(self, n=None, names=None, I=None):
        if not n and not names:
            n = 0
        if names:
            n = len(names)

        FreeMonoid.__init__(self, n, names)

        if I is None:
            I = Set()
        if names and len(I) > 0:
            el = next(iter(I[0]))[0]
            if isinstance(el, str):
                f = self.monoid_generators()
                reversed_family = {str(f[k]): k for k in f.keys()}
                I = ((reversed_family[e1], reversed_family[e2]) for e1, e2 in I)
        if not isinstance(I, Set_generic):
            I = Set(I)

        self.independence = I

    @cached_method
    def _named_set_without_duplicates(self):
        f = self.monoid_generators()
        return list((f[v1], f[v2]) for v1, v2 in set(map(frozenset, self.independence)))

    @property
    @cached_method
    def dependence(self):
        return Set(
            pair for pair in product(range(self.ngens()), repeat=2)
            if pair not in self.independence
        )

    @cached_method
    def dependence_graph(self):
        f = self.monoid_generators()
        return Graph([
            (f[v1], f[v2]) for v1, v2 in combinations_with_replacement(range(self.ngens()), 2)
            if (v1, v2) not in self.independence
        ], loops=True)

    @cached_method
    def independence_graph(self):
        return Graph(self._named_set_without_duplicates())

    @cached_method
    def dependence_polynomial(self, t=None):
        if t is None:
            R = PolynomialRing(ZZ, 't')
            t = R.gen()
        clique_seq = self.independence_graph().clique_polynomial().coefficients()
        return Integer(1) / sum(((-1) ** i) * coeff * (t ** i) for i, coeff in enumerate(clique_seq))

    @cached_method
    def growth_series(self):
        pass

    @cached_method
    def number_of_words(self, length):
        psr = PowerSeriesRing(ZZ, default_prec=length + 1)
        return psr(self.dependence_polynomial()).coefficients()[length]

    @cached_method
    def words(self, length):
        if length < 0:
            raise ValueError("Bad length of words. Expected zero or positive number.")
        if length == 0:
            return [self(1)]
        if length == 1:
            return list(self.gens())

        return [
            word * self.gen(suffix) for word in self.words(length - 1)
            for suffix in range(self.ngens())
            if not ((word._element_list[-1][0], suffix) in self.independence and
            word._element_list[-1][0] > suffix)
        ]

    def solve_equation(self, left, right):
        pass

    def _repr_(self):
        f = self.monoid_generators()
        return "Trace monoid on {!s} generators {!s} over independence relation {!r}." \
            .format(self.ngens(), self.gens(), Set((f[v1], f[v2]) for v1, v2 in self.independence))

    def _latex_(self):
        return "<{} | {}>".format(
            repr(self.gens())[1:-1],
            ",".join(
                "{0}{1}={1}{0}".format(v1, v2)
                for v1, v2 in self._named_set_without_duplicates()
            )
        )
