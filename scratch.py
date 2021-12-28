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
from core import hadamard_transform, w1

from functor import Functor
from utils import matrix_print, sep_print

if __name__ == "__main__":
    x, y = symbols("x,y")
    fn =  Functor(3*x**2/4 + 4*x*y - x*w1(x) - 3*x*w1(y)/4 + 27*x/4 + 4*y**2 
        - 2*y*w1(x) - 3*y*w1(y)/2 + 14*y + 3*w1(x)*w1(y)/8 - 7*w1(x)/2 - 21*w1(y)/8 - Rational(83207989/4))
    # [0 1 2 3] + [0 1 0 1] => 0 2 2 
    fn = Functor(
        fn.f
        .subs({x: x + 1})
        .subs({y: y + (1 - w1(x)) / 2})
        .subs({x: x + 1})
        .xreplace({w1(x + 2): w1(x), w1(x + 1): -w1(x)})
    )
    pprint(fn.f)
    # 
    m = fn.gen_matrix(2,4)
    matrix_print(m)