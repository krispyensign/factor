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
    x: Symbol
    y: Symbol
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
    # print([l2.subs(x, i) + 1 for i in range(8)])
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

    # fn = Functor(5*(-1)**x*(-1)**y/4 - 5*(-1)**x*x/4 - 45*(-1)**x/16 + (-1)**y*x/2 - 2*(-1)**y*y + 2*x*y + 9*x/8 + 9*y/2 - Rational(34867/16))
    # fn.print()
    
    # fn0 = Functor(fn.f * 4)
    # matrix_print(fn0.gen_matrix(m=8)
    # fn0.print()

    fn = Functor(-(-1)**x*(-1)**y*x - (-1)**x*(-1)**y*y/4 - 5*(-1)**x*(-1)**y/8 + (-1)**x*y/2 + 7*(-1)**x/8 + (-1)**y*x/2 - 3*(-1)**y*y/4 - 3*(-1)**y/4 + 2*x*y + 2*x + y**2/4 + 3*y/2 - Rational(2179/2))
    # fn.print()
    m1 = (1 - (-1)**(x + 1) * (-1)**(y + 1))/2
    m2 = (1 - (-1)**x * (-1)**(y + 1))/2
    m3 = (1 - (-1)**(x + 1) * (-1)**y)/2
    m4 = (1 - (-1)**x * (-1)**y)/2

    fn1 = Functor(fn.f.subs({x: 2*x, y: 2*y})) # self.x + (1 - (-1)**self.y) / 2
    s1 = fn1.lift(True)[1]
    fn2 = Functor(fn.f.subs({x: 2*x + 1, y: 2*y})) # self.x + (1 - (-1)**self.y) / 2
    s2 = fn2.lift(True)[1]
    fn3 = Functor(fn.f.subs({x: 2*x, y: 2*y + 1})) # self.x + (1 - (-1)**self.y) / 2
    s3 = fn3.lift(True)[1]
    fn4 = Functor(fn.f.subs({x: 2*x + 1, y: 2*y + 1})) # self.x + (1 - (-1)**self.y) / 2
    s4 = fn4.lift(True)[1]

    matrix_print(fn.gen_matrix(m=8))