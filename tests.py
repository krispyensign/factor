import unittest

from sympy import pprint, Integer  # type: nolint
from core import *


class TestTransforms(unittest.TestCase):
    def test_prove_transform(self):
        # prove transform
        source = transform(Matrix([[c[ii] for ii in range(4)]]), x)

        # evaluate 0 .. 4 for all cases
        evaluated = Matrix([[hadamard_evaluate(source.subs({
            x: ii,
        }).expand()) for ii in range(4)]])

        # provide expected result
        target = Matrix([[c[ii] for ii in range(4)]])

        self.assertTrue(evaluated.equals(target))

    def test_prove_condense_terms(self):
        # provide function to be reduced
        f: Add = i**create_generalized_shift(x)

        # prove condensed terms of a function before a transform still gives original values
        source = transform(Matrix([[condense_terms(hadamard_evaluate(f.subs({
            x: ii
        }))) for ii in range(4)]]), x)

        # evaluate 0 .. 4 for all cases
        evaluated = Matrix([[hadamard_evaluate(source.subs({
            x: ii,
        }).expand()) for ii in range(4)]])

        # provide expected results for all cases
        target = Matrix([[(-1)**e[ii] for ii in range(4)]])

        self.assertTrue(evaluated.equals(target))

    def test_prove_encode(self):
        # prove encoded function is equivalent to manually evaluating function with a power
        source = encode(a[0], create_generalized_shift(x), x, i)

        # evaluate 0 .. 4 for all cases
        evaluated = Matrix([[hadamard_evaluate(source.subs({
            x: ii,
        })) for ii in range(4)]])

        # provide expected results 0 .. 4 for all cases with no encoding
        target = Matrix([[condense_terms(hadamard_evaluate((i**(a[0]*x)).subs({
            x: create_generalized_shift(x)
        }).subs({
            x: ii
        }))) for ii in range(4)]])

        self.assertTrue(evaluated.equals(target))


if __name__ == '__main__':
    unittest.main()
