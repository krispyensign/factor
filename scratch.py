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
	f =(-1)**x*x + 5*(-1)**x*y/2 + 11*(-1)**x/4 + (-1)**y*y/4 + (-1)**y/8 + x**2 + 5*x*y + 11*x/2 + 21*y**2/4 + 51*y/4 + + Rational(49/8)
	fn = Functor(f)
	fn.print()
	fn1 = Functor(fn.f.subs({x: 2*x, y: 2*y}))
	print_maple_code(fn1.smooth())
	fn2 = Functor(fn.f.subs({x: 2*x + 1, y: 2*y}))
	print_maple_code(fn2.smooth())
	fn3 = Functor(fn.f.subs({x: 2*x, y: 2*y + 1}))
	print_maple_code(fn3.smooth())
	fn4 = Functor(fn.f.subs({x: 2*x + 1, y: 2*y + 1}))
	print_maple_code(fn4.smooth())
	print(20**2 - 4*4*21)
	g = 2*x - (1 - (-1)**x) / 2 + 2
	print([g.subs(x, i) for i in range(4)])