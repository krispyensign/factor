from math import fmod
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
from core import core, build_shift_any, core_shift_smooth, encode
from utils import matrix_print, sep_print

if __name__ == "__main__":
    x: Symbol = symbols('x')
    y: Symbol = symbols('y')
    f = core()
    shift = build_shift_any(f, y)
    g = core_shift_smooth(f, x, y, shift)
    sep_print()
    pprint(shift)
    sep_print()
    pprint(g)
    sep_print()
