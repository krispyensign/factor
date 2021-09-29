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
	Rational,
	radsimp,
	sqrt
)

from typing import Tuple

from utils import matrix_print, sep_print

if __name__ == "__main__":
	x, y = symbols('x,y')
	m = (1 - (-1)**x)/2
	f = (x - m)/2
	m2 = m.subs(x, f)
	g = (-1)**x / 4 + x / 2 - Rational(1/4)

	# 1, I  2, -1  3, -I  4, 1
	# 3 , 4 , 3 , 4 
    # 3 + 3x = 3, 2, 5, 0
	h = I**((-1)**x / 2)
	j = sqrt(I)*( -I*(1-(-1)**x)/2 + (1-(-1)**(x+1))/2 )
	pprint(j)
	print([radsimp(h.subs(x, i)) for i in range(4)])
	print([radsimp(j.subs(x, i)) for i in range(4)])

	k = -(-1)**x*(-1)**y/8 - 3*(-1)**x*x/4 - (-1)**x*y/2 - 5*(-1)**x/8 - 13*(-1)**(2*y)/32 - (-1)**y*x/16 + (-1)**y*y/8 + (-1)**y/32 + 3*(-1)**(-y - 1)*x/16 + (-1)**(-y - 1)*y/8 + 5*(-1)**(-y - 1)/32 + 15*x**2/4 + 7*x*y + 29*x/4 + 3*y**2 + 13*y/2 - Rational(545/8) - (-1)**(-y)*(-1)**(-y - 1)/32 + (-1)**(-x)*(-1)**y/8 + (-1)**(-x)*(-1)**(-y - 1)/8 - 3*(-1)**(-x)*x/4 - (-1)**(-x)*y/2 - 5*(-1)**(-x)/8
	matrix_print([[Mod(k.subs(x, i).subs(y, j), 2) for i in range(4)] for j in range(4)])
	l = k.subs(y, y + (1-(-1)**y)/2 + x).subs(x, x+y)
	matrix_print([[Mod(l.subs(x, i).subs(y, j), 2) for i in range(4)] for j in range(4)])
	# pprint(l)