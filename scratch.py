from math import fmod
from os import sep
from typing import Tuple
from sympy import (   # type: ignore
    symbols,
    Symbol,
    I,
    Matrix,
    Add,
    pprint,
    Mul,
    Rational,
)

from functor import Functor
from core import create_generalized_polynomial, create_generalized_shift, shift_polynomial 
from utils import matrix_print, sep_print

if __name__ == "__main__":
    x, y, j, k, i = symbols('x, y, j, k, i')
    d: list[Symbol] = symbols('d0, d1, d2, d3')
    e: list[Symbol] = symbols('e0, e1, e2, e3')

    f = create_generalized_polynomial()
    shift = create_generalized_shift(y)
    g = shift_polynomial(f, x, y, shift)*16
    # sep_print()
    # pprint(shift)
    pprint(g)
    sep_print()
