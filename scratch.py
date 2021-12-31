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
    sqrt,
)
from core import hadamard_transform, w1

from functor import Functor
from utils import matrix_print, sep_print

def trans(f):
    af = f.coeff(x**2)
    bf = f.coeff(x)
    cf = f.coeff(x, n=0)
    df = bf**2 - 4*af*cf
    return (-x**2 + df).expand()

if __name__ == "__main__":
    x, y, t = symbols("x,y,t")
    # 3*x**2 + 8*x*y + 8*x + 5*y - 20802006     x=-6819    y=2175

    f = 3*x**2 + 8*x*y + 8*x + 5*y - 20802006
    # pprint(trans(f))

    pprint(trans(3*x**2/2 + 8*x*y + 7*x/2 + y - Rational(20802009/2)))
    pprint(trans(3*x**2/2 + 8*x*y + 7*x + 3*y - Rational(20802005/2)))
    pprint(trans(3*x**2/2 + 8*x*y + 15*x/2 + y - 10401004))
    pprint(trans(3*x**2/2 + 8*x*y + 11*x + 3*y - 10401001 ))


    sep_print()

    pprint(trans(3*x**2/4 + 8*x*y + 15*x/4 + y - 5200502))
    pprint(trans(3*x**2/4 + 8*x*y + 11*x/2 + 3*y - Rational(10401001/2)))
    pprint(trans(3*x**2/4 + 8*x*y + 31*x/4 + y - Rational(10401003/2)))
    pprint(trans(3*x**2/4 + 8*x*y + 19*x/2 + 3*y - 5200499))