import unittest

from core import *

class TestTransforms(unittest.TestCase):
    def test_prove_walsh_reduction_w1(self):
        # prove that i**(2*x) == 1
        source = Matrix(([[w1(2*n) for n in range(4)]]))
        target = Matrix(([[1 for n in range(4)]]))
        self.assertTrue(source.equals(target))

    def test_prove_walsh_reduction_w2(self):
        # prove that j**(2*x) == i**x
        source = Matrix(([[w2(2*n) for n in range(4)]]))
        target = Matrix(([[w1(n) for n in range(4)]]))
        self.assertTrue(source.equals(target))

    def test_prove_walsh_reduction_w3(self):
        # prove that k**(2*x) == i**x
        source = Matrix(([[w2(2*n) for n in range(4)]]))
        target = Matrix(([[w1(n) for n in range(4)]]))
        self.assertTrue(source.equals(target))

    def test_prove_transform(self):
        # prove the transform
        source = hadamard_transform(Matrix([[c[n] for n in range(4)]]), x)

        # evaluate 0 .. 4 for all cases
        evaluated = Matrix([[(source.subs({x: n}).expand()) for n in range(4)]])

        # provide expected result
        target = Matrix([[c[n] for n in range(4)]])
        self.assertTrue(evaluated.equals(target))

    def test_prove_condense_terms(self):
        # provide function to be reduced
        f: Add = create_generalized_shift(x)

        # prove condensed terms of a function before a transform still gives original values
        source = hadamard_transform(Matrix([[condense_terms_d((w1(f.subs({
            x: n
        })))) for n in range(4)]]), x)

        # evaluate 0 .. 4 for all cases
        evaluated = Matrix([[(source.subs({x: n}).expand()) for n in range(4)]])

        # provide expected results for all cases
        target = condense_terms_d(Matrix([[w1(f.subs({x: n})) for n in range(4)]]))

        self.assertTrue(evaluated.equals(target))

    def test_prove_encode(self):
        # prove encoded function is equivalent to unencoded function
        source = encode(a[0], create_generalized_shift(x), x, w1)

        # evaluate 0 .. 4 for all cases
        evaluated = Matrix([[(source.subs({x: n,})) for n in range(4)]])

        # provide expected results 0 .. 4 for all cases with no encoding
        target = Matrix([[condense_terms_d(((w1(a[0]*x)).subs({
            x: create_generalized_shift(x),
        }).subs({
            x: n,
        }))) for n in range(4)]])

        self.assertTrue(evaluated.equals(target))


if __name__ == '__main__':
    unittest.main()
