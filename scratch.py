from functor import Functor
from sympy import (
    Mod,
    symbols,
    print_maple_code,
    pprint,
    Add,
    Integer,
    Symbol,
	I,
	Rational
)

from typing import Tuple

from utils import matrix_print, sep_print

if __name__ == "__main__":
	x, y = symbols('x,y')
	g = (-1)**(-(-1)**x/2)
	h = I*(-1)**(x+1)
	print([g.subs(x, i) for i in range(4)])
	print([h.subs(x, i) for i in range(4)])