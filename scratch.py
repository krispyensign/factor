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

def transx(f):
    af = f.coeff(y**2)
    bf = f.coeff(y)
    cf = f.coeff(y, n=0)
    df = bf**2 - 4*af*cf
    return (-y**2 + df).expand()

def transy(f):
    af = f.coeff(x**2)
    bf = f.coeff(x)
    cf = f.coeff(x, n=0)
    df = bf**2 - 4*af*cf
    return (-x**2 + df).expand()

if __name__ == "__main__":
    x, y, t = symbols("x,y,t")
    pprint(hadamard_transform(Matrix([[0, 0, 1, 1]]), x))