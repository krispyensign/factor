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

    # 1, I  2, -1  3, -I  4, 1
    # 3 , 4 , 3 , 4
    # 3 + 3x = 3, 2, 5, 0
    # h = I**((-1)**x / 2)
    # j = sqrt(I)*(-I*(1-(-1)**x)/2 + (1-(-1)**(x+1))/2)
    # pprint(j.expand())
    # print([radsimp(h.subs(x, i)) for i in range(4)])
    # print([radsimp(j.subs(x, i)) for i in range(4)])
    # sep_print()

    # k2 = (1 - (j * I**x * sqrt(I) * -I)) / 2
    # print([k2.subs(x, i) for i in range(4)])
    # sep_print()

    # l2 = (k2
    #      .expand()
    #      .subs(I*I**(x), I**(x+1))
    #      .subs((-1)**x * I**x, I**(3*x))
    #      .expand()
    #      .subs((-1)**x * I * I**x, I**(3*x+1))
    #      .subs(I**x * I, I**(x+1)))
    # pprint(l2)
    # print([l2.subs(x, i) for i in range(8)])
    # sep_print()

    # m = (1 - (-1)**x)/2
    # f1 = (x - m)/2
    # m2 = m.subs(x, f1)
    # f2 = (x - 2*l2 - m)/4
    # pprint(f2)
    # print([f2.subs(x, i) for i in range(8)])
    # sep_print()

    # m3 = m.subs(x, f2)
    # pprint(m3)
    # sep_print()

    # h = I**((-1)**x / 4)
    # j = sqrt(I)*(-I*(1-(-1)**x)/2 + (1-(-1)**(x+1))/2)
    # pprint(j.expand())
    # print([radsimp(h.subs(x, i)) for i in range(4)])
    # print([radsimp(j.subs(x, i)) for i in range(4)])
    # sep_print()

    fn = Functor(-(-1)**x*x/2 - 5*(-1)**x/8 + 2*x*y + 5*x/4 + 5*y/2 - Rational(34887/8))
    fn.print()
    fn = Functor(fn.f.subs(x, x + (1 - (-1)**y)/2))
    fn.print()
    fn = Functor(fn.f.subs(x, x + (1 - (-1)**y)/2))
    fn.print()



    # 16 3  10 8723, x is odd
    # 16 7  18 8717, x is odd
    # 16 11 10 8718, x is even
    # 16 15 18 8716, x is even