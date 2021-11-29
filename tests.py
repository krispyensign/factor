import unittest

from core import *

class TestTransforms(unittest.TestCase):
    def test_prove_walsh_reduction_i(self):
        # prove that i**(2*x) == 1
        source = Matrix(([[i(2*ii) for ii in range(4)]]))
        target = Matrix(([[1 for ii in range(4)]]))
        self.assertTrue(source.equals(target))

    def test_prove_walsh_reduction_j(self):
        # prove that j**(2*x) == i**x
        source = Matrix(([[j(2*ii) for ii in range(4)]]))
        target = Matrix(([[i(ii) for ii in range(4)]]))
        self.assertTrue(source.equals(target))

    def test_prove_walsh_reduction_k(self):
        # prove that k**(2*x) == i**x
        source = Matrix(([[k(2*ii) for ii in range(4)]]))
        target = Matrix(([[i(ii) for ii in range(4)]]))
        self.assertTrue(source.equals(target))

    def test_prove_transform(self):
        # prove the transform
        source = hadamard_transform(Matrix([[c[ii] for ii in range(4)]]), x)

        # evaluate 0 .. 4 for all cases
        evaluated = Matrix([[(source.subs({
            x: ii,
        }).expand()) for ii in range(4)]])

        # provide expected result
        target = Matrix([[c[ii] for ii in range(4)]])
        self.assertTrue(evaluated.equals(target))

    def test_prove_condense_terms(self):
        # provide function to be reduced
        f: Add = create_generalized_shift(x)

        # prove condensed terms of a function before a transform still gives original values
        source = hadamard_transform(Matrix([[condense_terms_d((i(f.subs({
            x: ii
        })))) for ii in range(4)]]), x)

        # evaluate 0 .. 4 for all cases
        evaluated = Matrix([[(source.subs({
            x: ii,
        }).expand()) for ii in range(4)]])

        # provide expected results for all cases
        target = condense_terms_d(Matrix([[i(f.subs({x: ii})) for ii in range(4)]]))

        self.assertTrue(evaluated.equals(target))

    def test_prove_encode(self):
        # prove encoded function is equivalent to unencoded function
        source = encode(a[0], create_generalized_shift(x), x, i)

        # evaluate 0 .. 4 for all cases
        evaluated = Matrix([[(source.subs({
            x: ii,
        })) for ii in range(4)]])

        # provide expected results 0 .. 4 for all cases with no encoding
        target = Matrix([[condense_terms_d(((i(a[0]*x)).subs({
            x: create_generalized_shift(x)
        }).subs({
            x: ii
        }))) for ii in range(4)]])

        self.assertTrue(evaluated.equals(target))


if __name__ == '__main__':
    unittest.main()
