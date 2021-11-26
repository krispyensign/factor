import unittest

from sympy import pprint  # type: nolint
from core import *


def hadamard_evaluate(f: Add) -> Add:
    return f.xreplace({
        i**3: -1,
        j**3: -1,
        k**3: 1,

        i**2: 1,
        j**2: -1,
        k**2: -1,

        i: -1,
        j: 1,
        k: -1,
    })


def condense_terms(f: Add) -> Add:
    return f.xreplace({
        d[0]/4 + d[1]/4 + d[2]/4 + d[3]/4: e[0],
        d[0]/4 - d[1]/4 + d[2]/4 - d[3]/4: e[1],
        d[0]/4 + d[1]/4 - d[2]/4 - d[3]/4: e[2],
        d[0]/4 - d[1]/4 - d[2]/4 + d[3]/4: e[3],
    })


class TestTransforms(unittest.TestCase):
    def test_prove_transform(self):
        source = Matrix([[c[ii] for ii in range(4)]])
        target = Matrix([[c[ii] for ii in range(4)]])

        encoded_source = transform(source, x)

        evaluated = Matrix([[hadamard_evaluate(encoded_source.subs({
            x: ii,
        }).expand()) for ii in range(4)]])

        self.assertTrue(evaluated.equals(target))

    def test_prove_i_powers_reduce(self):
        f: Add = i**create_generalized_shift(x)

        source = Matrix([[condense_terms(hadamard_evaluate(f.subs({
            x: ii
        })).subs({
            (-1): i,
        })) for ii in range(4)]])

        target = Matrix([[i**e[ii] for ii in range(4)]])

        encoded_source = transform(source, x)

        evaluated = Matrix([[hadamard_evaluate(encoded_source.subs({
            x: ii,
        }).expand()).subs({
            (-1): i,
        }) for ii in range(4)]])

        self.assertTrue(evaluated.equals(target))


if __name__ == '__main__':
    unittest.main()
