from math import fmod
from functor import Functor
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

from typing import Tuple

from utils import matrix_print, sep_print

def encode(A: Matrix) -> Add | Mul:
    x: Symbol
    x = symbols('x')
    # setup walsh functions
    ii = I**(2*x)
    kk = I**(3*x) / 2 - I**(3*x + 1) / 2 + I**x / 2 + I**(x + 1) / 2
    jj = kk.subs({x: x + 3}).subs({
        I**(x + 4):  I**x,
        I**(3*x + 9):  I**(3*x + 1),
        I**(3*x + 10): I**(3*x + 2),
    })

    # perform hadamard transform
    Ident: Matrix = Matrix([
        [1,  1,  1,  1],
        [1, -1,  1, -1],
        [1,  1, -1, -1],
        [1, -1, -1,  1],
    ])

    B: Matrix = (A * Ident)
    
    # convert to function
    return (B[0] + B[1]*ii + B[2]*jj + B[3]*kk) / 4

if __name__ == "__main__":
    x: Symbol
    y: Symbol
    a: Symbol
    b: Symbol
    c: Symbol
    d: Symbol
    e: Symbol
    f: Symbol
    g: Symbol
    h: Symbol


    x, y = symbols('x, y')
    f = -(-1)**x*(-1)**y*x/4 - (-1)**x*x/4 + (-1)**x*y/2 - (-1)**x/8 + 3*(-1)**y*x/4 + (-1)**y*y/2 + (-1)**y/4 + 5*x**2/4 + 3*x*y + 5*x/4 + y**2 + 3*y/2 - Rational(4185/8)
    fn = Functor(f)
    # 2 2 2 4
    s = encode(Matrix([[0, 2, 2, 0]])).expand().subs({
        I * I**(3*x):           I**(3*x + 1),
        I * I**(2*x):           I**(2*x + 1),
        I * I**x:               I**(x + 1),
        I**x * I**(2*x + 1):    I**(3*x + 1),
    })
    pprint(s)
    print(s)
    sep_print()


    print([(-I**(-2*I**(4*x))).subs({x: i}) for i in range(4)])
    print([(-I**(-2*I**(2*x))).subs({x: i}) for i in range(4)])

    print([[(-I**(-2*I**(2*x) + 2*y + 2)).subs({x: i, y: j}) for i in range(4)] for j in range(4)])
    print([[(I**(2*y + 2)).subs({x: i, y: j}) for i in range(4)] for j in range(4)])

    print([[I**(-I**(2*y) + 4*y + 3).subs({x: i, y: j}) for i in range(4)] for j in range(4)])
    print([[(I**(2*y + 2)).subs({x: i, y: j}) for i in range(4)] for j in range(4)])

    sep_print()
    print([[I**(-I**(3*x) - I**x + I**(x + 1) - I**(3*x + 1) + 2*y + 4).subs({x: i, y: j}) for i in range(4)] for j in range(4)])
    print([[I**(-I**(3*x) - I**x + I**(x + 1) - I**(3*x + 1) + 2*y + 2).subs({x: i, y: j}) for i in range(4)] for j in range(4)])
    sep_print()
    print([[I**(-I**(2*y + 2) + 2*x + 2*y + 1).subs({x: i, y: j}) for i in range(4)] for j in range(4)])
    print([[I**(2*x + 2).subs({x: i, y: j}) for i in range(4)] for j in range(4)])
    sep_print()
    print([[I**(-I**(2*x) + 4*x + 3).subs({x: i, y: j}) for i in range(4)] for j in range(4)])
    print([[I**(2*x + 2).subs({x: i, y: j}) for i in range(4)] for j in range(4)])
    sep_print()
    print([[I**(I**(2*x) + 4*x + 3).subs({x: i, y: j}) for i in range(4)] for j in range(4)])
    print([[I**(2*x).subs({x: i, y: j}) for i in range(4)] for j in range(4)])
    sep_print()
    print([[I**(I**(2*x) + 4*x + 1).subs({x: i, y: j}) for i in range(4)] for j in range(4)])
    print([[I**(2*x + 2).subs({x: i, y: j}) for i in range(4)] for j in range(4)])
    sep_print()
    print([[I**(I**(2*y) + 2*x + 4*y - 1).subs({x: i, y: j}) for i in range(4)] for j in range(4)])
    print([[I**(2*x + 2*y).subs({x: i, y: j}) for i in range(4)] for j in range(4)])
    sep_print()
    print([[I**(I**(2*y) + 2*x + 4*y + 1).subs({x: i, y: j}) for i in range(4)] for j in range(4)])
    print([[I**(2*x + 2*y + 2).subs({x: i, y: j}) for i in range(4)] for j in range(4)])
    sep_print()
    print([[I**(-2*I**(2*x)).subs({x: i, y: j}) for i in range(4)] for j in range(4)])
    sep_print()
    print([[I*I**(-I**(2*y)).subs({x: i, y: j}) for i in range(4)] for j in range(4)])
    print([[(I**(2*y)).subs({x: i, y: j}) for i in range(4)] for j in range(4)])
    sep_print()
    print([[I*I**(-I**(2*y)).subs({x: i, y: j}) for i in range(4)] for j in range(4)])
    print([[(I**(2*y)).subs({x: i, y: j}) for i in range(4)] for j in range(4)])
    sep_print()
    print([[I*I**(I**(2*y)).subs({x: i, y: j}) for i in range(4)] for j in range(4)])
    print([[(I**(2*y + 2)).subs({x: i, y: j}) for i in range(4)] for j in range(4)])


    # A = [[2, 2, 2, 0]]
    # print(A)
    # s = encode(Matrix(A)).expand().subs({
    #     I * I**(3*x):           I**(3*x + 1),
    #     I * I**(2*x):           I**(2*x + 1),
    #     I * I**x:               I**(x + 1),
    #     I**x * I**(2*x + 1):    I**(3*x + 1),
    # })
    # pprint(s)
    # print(s)
    # sep_print()

    # fntest = Functor((5*x**2 + 12*x*y + 10*x + 4*y**2 + 9*y - 519).subs({
    #     x: x + y,
    # }).subs({
    #     x: 2*x + 1,
    # }).expand() / 2)
    # fntest.print()

    # f1 = 5*I**(32*y)/32 + 3*I**(24*y)/8 - 3*I**(20*y)/4 + 10*x**2 + 48*x*y + 10*x + 32*y**2 + 21*y - Rational(2009/32)
    # print(f1.subs({
    #     I**(32*y): 1,
    #     I**(24*y): 1,
    #     I**(20*y): 1,
    # }).expand())
    # f2 = 5*I**(32*y)/32 + 3*I**(24*y)/8 + 3*I**(20*y)/4 + 10*x**2 + 48*x*y + 43*x + 32*y**2 + 81*y - Rational(809/32)
    # print(f2.subs({
    #     I**(32*y): 1,
    #     I**(24*y): 1,
    #     I**(20*y): 1,
    # }).expand())
    # f3 = 5*I**(32*y)/32 + 3*I**(24*y)/8 - 3*I**(20*y)/4 + 10*x**2 + 48*x*y + 33*x + 32*y**2 + 57*y - Rational(1369/32)
    # print(f3.subs({
    #     I**(32*y): 1,
    #     I**(24*y): 1,
    #     I**(20*y): 1,
    # }).expand())
    # f4 = 5*I**(32*y)/32 + 3*I**(24*y)/8 + 3*I**(20*y)/4 + 10*x**2 + 48*x*y + 44*x + 32*y**2 + 77*y - Rational(841/32)
    # print(f4.subs({
    #     I**(32*y): 1,
    #     I**(24*y): 1,
    #     I**(20*y): 1,
    # }).expand())

    # a = symbols('a0, a1, a2, a3')
    # b = symbols('b0, b1, b2, b3')
    # c = symbols('c0, c1, c2, c3')
    # d = symbols('d0, d1, d2, d3')
    # fn = encode(Matrix([[a[0], a[1], a[2], a[3]]]))
    # fn0 = Rational(1/4) * fn.subs({
    #     a[0]: 2,
    #     a[1]: 2,
    #     a[2]: 2,
    #     a[3]: 0,
    # })
    # pprint(fn0)
    # print(fn0)
    # pprint(fn)
    # sep_print()

    # fn2 = fn.subs({
    #     a[0] + a[1] + a[2] + a[3]:  b[0],
    # }).xreplace({
    #     a[0] - a[1] + a[2] - a[3]:  b[1],
    # }).xreplace({
    #     a[0] + a[1] - a[2] - a[3]:  b[2],
    # }).xreplace({
    #     a[0] - a[1] - a[2] + a[3]:  b[3],
    # }).xreplace({
    #     (-1)**x:        I**(2*x)
    # }).subs({
    #     I * I**(3*x):   I**(3*x + 1),
    #     I * I**x:       I**(x + 1),
    # }).xreplace({
    #     b[0]: c[0] + I*d[0],
    #     b[1]: c[1] + I*d[1],
    #     b[2]: c[2] + I*d[2],
    #     b[3]: c[3] + I*d[3],
    # }).expand().subs({
    #     I * I**(3*x):           I**(3*x + 1),
    #     I * I**(2*x):           I**(2*x + 1),
    #     I * I**x:               I**(x + 1),
    # }).subs({
    #     I**x * I**(2*x + 1):    I**(3*x + 1),
    # }).subs({
    #     I**(3*x)*c[2] / 2 + I**(3*x)*c[3] / 2 - I**(3*x)*d[2] / 2 + I**(3*x)*d[3] / 2:
    #         I**(3*x) / 2 * (c[2] + c[3] - d[2] +d[3]),
    #     I**x*c[2]/2 + I**x*c[3]/2 + I**x*d[2]/2 - I**x*d[3]/2:
    #         I**x/2*(c[2] + c[3] + d[2] - d[3]),
    #     -I**(x + 1)*c[2]/2 + I**(x + 1)*c[3]/2 + I**(x + 1)*d[2]/2 + I**(x + 1)*d[3]/2:
    #         I**(x + 1)/2 * (-c[2] + c[3] + d[2] + d[3]),
    #     I**(3*x + 1)*c[2]/2 - I**(3*x + 1)*c[3]/2 + I**(3*x + 1)*d[2]/2 + I**(3*x + 1)*d[3]/2:
    #         I**(3*x + 1) / 2 *(c[2] - c[3] + d[2] + d[3]),
    # })
    # print(fn2)
    # pprint(fn2)
    # sep_print()

    # f = f.expand().xreplace({
    #     (-1)**x:            I**(2*x),
    # }).subs({
    #     I * I**(3*x):       I**(3*x + 1),
    #     I * I**x:           I**(x + 1),
    # })
    # pprint(f)
    # sep_print()

    # fI1 = f.subs({
    #     a:  I**a,
    #     b:  I**b,
    #     c:  I**c,
    #     d:  I**d,
    # }).subs({
    #     I**a * I**(3*x):        I**(3*x + a),
    #     I**a * I**(2*x):        I**(2*x + a),
    #     I**a * I**x:            I**(x + a),
    #     I**b * I**(2*x):        I**(2*x + b),
    #     I**b * I**(x + 1):      I**(x + b + 1),
    #     I**b * I**(3*x + 1):    I**(3*x + b + 1),
    #     I**c * I**(3*x):        I**(3*x + c),
    #     I**c * I**(2*x):        I**(2*x + c),
    #     I**c * I**x:            I**(x + c),
    #     I**d * I**(2*x):        I**(2*x + d),
    #     I**d * I**(x + 1):      I**(x + d + 1),
    #     I**d * I**(3*x + 1):    I**(3*x + d + 1),
    # }).xreplace({
    #     I**x * I**(a + 2*x):    I**(3*x + a),
    # }).subs({
    #     I**x * I**(c + 2*x):    I**(3*x + c),
    # }).subs({
    #     I**(a + x) - I**(b + x + 1) - I**(c + x) + I**(d + x + 1): I**x*(I**a - I**(b + 1) - I**c + I**(d + 1)),
    # })
    # pprint(fI1)
    # sep_print()

    # fI2 = fI1.subs({
    #     a: 2*a,
    #     b: 2*b,
    #     c: 2*c,
    #     d: 2*d,
    # })
    # pprint(fI2)
    # sep_print()
    
    # fI3 = fI1.subs({
    #     a: 3*a,
    #     b: 3*b,
    #     c: 3*c,
    #     d: 3*d,
    # })
    # pprint(fI3)
    # sep_print()
