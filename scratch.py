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
    sqrt,
    Matrix,
)

from typing import Tuple

from utils import matrix_print, sep_print

if __name__ == "__main__":
    x: Symbol
    y: Symbol
    x, y, i, j, k = symbols('x,y,j,k,i')

    def comp_k(xx):
        return [1, 1, -1, -1][xx % 4]

    def comp_j(xx):
        return [1, -1, -1, 1][xx % 4]

    def comp_i(xx):
        return [1, -1, 1, -1][xx % 4]


    g1 = 1
    g2 = (-1)**x

    # print([f.subs({
    #     k: comp_k(n),
    #     j: comp_j(n),
    #     i: comp_i(n),
    # }) for n in range(4)])

    # kf = I**x - ((1 - (-1)**x)/2)*(I**x)
    # kf += kf.subs({x: x + 1})
    # kf = kf.expand().xreplace({
    #     (-1)**x: I**(2*x),
    #     I * I**(3*x): I**(3*x + 1)
    # })
    # pprint(kf.expand())
    iff = (-1)**x
    pprint(iff)
    print([iff.subs({x: n}) for n in range(4)])
    sep_print()

    kf = I**(3*x) / 2 - I**(3*x + 1) / 2 + I**x/2 + I**(x+1)/2
    pprint(kf)
    print([kf.subs({x: n}) for n in range(4)])
    sep_print()

    jf = kf.subs({x: x + 3}).subs({
        I**(x + 4):  I**x,
        I**(3*x+9):  I**(3*x + 1),
        I**(3*x+10): I**(3*x + 2),
    })
    pprint(jf)
    print([jf.subs({x: n}) for n in range(4)])
    sep_print()

    Ident = Matrix([
        [1,  1,  1,  1],
        [1, -1,  1, -1],
        [1,  1, -1, -1],
        [1, -1, -1,  1],
    ])
    pprint(Ident)
    sep_print()

    M1 = Matrix([
        [1, iff, jf, kf]
    ])
    # pprint(M1)

    M2 = Matrix([
        [2, 3, 1, 2]
    ])
    pprint(M2)

    M3 = M2 * Ident
    pprint(M3)
    # 8 -2  2 0 = 8
    # 8  2  2 0 = 12
    # 8 -2 -2 0 = 4
    # 8  2 -2 0 = 8
    f = (M3[0] + M3[1]*iff + M3[2]*jf + M3[3]*kf) / 4
    pprint(f)
    sep_print()

    print(M3[0])
    print([(M3[1] * iff).subs({x: n}) for n in range(4)])
    print([(M3[2] * jf).subs({x: n}) for n in range(4)])
    print([(M3[3] * kf).subs({x: n}) for n in range(4)])
    sep_print()

    print([n for n in range(4)])
    print([f.subs({x: n}) for n in range(4)])
    print([I**f.subs({x: n}) for n in range(4)])
    print([I**(2*f.subs({x: n})) for n in range(4)])
    print([I**(3*f.subs({x: n})) for n in range(4)])