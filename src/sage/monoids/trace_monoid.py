"""
Trace monoids
"""

from __future__ import print_function

# ***************************************************************************************************
#  Copyright (C) 2019      Pavlo Tokariev (Kharkiv National Universiy) <pavlo.tokariev at google mail service>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
# ***************************************************************************************************
import copy
from itertools import chain

from sage.monoids.free_monoid import FreeMonoid
from sage.monoids.free_monoid_element import FreeMonoidElement
from sage.sets.set import Set
from sage.structure.parent import Set_generic


class TraceMonoidElement(FreeMonoidElement):
    def lexicographic(self):
        result = self.parent(1)
        elements = copy.copy(self._element_list)
        for i in range(len(elements)):
            for j in range(i, -1, -1):
                if j > 0 and elements[j - 1][0] > elements[i][0] and \
                        (elements[i][0], elements[j - 1][0]) in self.parent().independence:
                    continue
                if j == i:
                    break
                moved, elements = elements[i], elements[:i] + elements[i + 1:]
                elements.insert(j, moved)
                break
        collector = -1
        new_elements = []
        for e in elements:
            if collector != -1 and new_elements[collector][0] == e[0]:
                new_elements[collector] = (e[0], new_elements[collector][1] + e[1])
            else:
                new_elements.append(e)
                collector = len(new_elements) - 1
        result._element_list = new_elements
        return result

    def foata(self):
        pass

    def dependency_graph(self):
        pass

    def hasse_graph(self):
        pass

    def _richcmp_(self, other, op):
        return super(TraceMonoidElement, self)._richcmp_(other.lexicographic(), op)


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


class FoataNormalForm:
    def __init__(self, steps, monoid):
        self._steps = steps
        self._parent = monoid

    def to_trace(self):
        return self._parent(chain.from_iterable(self._steps))

    def _repr_(self):
        f = self._parent.monoid_generators()
        return "".join("({})".format("".join(f[number_point] for number_point in step)) for step in self._steps)

    def _latex_(self):
        f = self._parent.monoid_generators()
        return "".join("\\({}\\)".format("".join(f[number_point] for number_point in step)) for step in self._steps)
