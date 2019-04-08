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
from itertools import chain, repeat

from sage.monoids.free_monoid import FreeMonoid
from sage.monoids.free_monoid_element import FreeMonoidElement
from sage.sets.set import Set
from sage.structure.parent import Set_generic


class TraceMonoidElement(FreeMonoidElement):
    def lexic_norm_form(self):
        result = self.parent(1)
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
        result._element_list = self.collect_sequence(elements)
        return result

    @staticmethod
    def collect_sequence(elements):
        collector = -1
        new_elements = []
        for e in elements:
            if collector != -1 and new_elements[collector][0] == e[0]:
                new_elements[collector] = (e[0], new_elements[collector][1] + e[1])
            else:
                new_elements.append(e)
                collector = len(new_elements) - 1
        return new_elements

    def foata_norm_form(self):
        if not self._element_list:
            return FoataNormalForm([], self.parent())

        generators_set = OrderedDict(sorted((e[0], None) for e in self._element_list))
        stacks = OrderedDict(sorted((g, []) for g in generators_set))
        independence = self.parent().independence

        for element in reversed(self._element_list):
            generator, amount = element
            stacks[generator].extend(repeat(True, amount))
            for other_gen in generators_set.keys():
                if other_gen == generator:
                    continue
                if (generator, other_gen) not in independence:
                    stacks[other_gen].extend(repeat(False, amount))

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
                for other_gen in generators_set.keys():
                    if other_gen != g and (g, other_gen) not in independence:
                        stacks[other_gen].pop()

            if step:
                steps.append(tuple(step))

        return FoataNormalForm(steps, self.parent())

    def dependency_graph(self):
        pass

    def hasse_graph(self):
        pass

    def _richcmp_(self, other, op):
        return super(TraceMonoidElement, self)._richcmp_(other.lexic_norm_form(), op)


class TraceMonoid(FreeMonoid):
    Element = TraceMonoidElement

    def __init__(self, n, names=None, I=None):
        FreeMonoid.__init__(self, n, names)
        if I is None:
            I = Set()
        if names and len(I) > 0:
            el = I[0][0]
            if isinstance(el, str):
                f = self.monoid_generators()
                reversed_family = {str(f[k]): k for k in f.keys()}
                I = ((reversed_family[e1], reversed_family[e2]) for e1, e2 in I)
        if not isinstance(I, Set_generic):
            I = Set(I)
        self.independence = I

    def growth_polynomial(self):
        pass

    def solve_equation(self, left, right):
        pass

    def _repr_(self):
        return "Trace monoid on {} generators {} over independence relation {}." \
            .format(self.ngens(), self.gens(), self.independence)

    def _latex_(self):
        return "<{} | {}>".format(repr(self.gens())[1:-1], self.independence)


class FoataNormalForm(TraceMonoidElement):
    def __init__(self, steps, monoid):
        self._steps = tuple(steps)
        elements = self.collect_sequence((g, 1) for g in chain.from_iterable(self._steps))
        super(TraceMonoidElement, self).__init__(monoid, elements)

    def _repr_(self):
        f = self.parent().monoid_generators()
        return "".join("({})".format("".join(str(f[elem]) for elem in step)) for step in self._steps)

    def _latex_(self):
        f = self.parent().monoid_generators()
        return "".join("\\({}\\)".format("".join(str(f[elem]) for elem in step)) for step in self._steps)
