from functor import Functor
from sympy import (
    symbols,
    Symbol,
    I,
    Matrix,
    Add,
    pprint,
    Mul
)

from typing import Tuple

from utils import matrix_print, sep_print

def encode(A: Matrix) -> Add | Mul:
    x: Symbol
    y: Symbol
    x, y = symbols('x, y')
    # setup walsh functions
    ii = (-1)**x
    kk = I**(3*x) / 2 - I**(3*x + 1) / 2 + I**x / 2 + I**(x + 1) / 2
    jj = kk.subs({x: x + 3}).subs({
        I**(x + 4):  I**x,
        I**(3*x + 9):  I**(3*x + 1),
        I**(3*x + 10): I**(3*x + 2),
    })

    # perform hadamard transform
    B: Matrix = (A * Matrix([
        [1,  1,  1,  1],
        [1, -1,  1, -1],
        [1,  1, -1, -1],
        [1, -1, -1,  1],
    ])).multiply_elementwise(Matrix([
        [1, ii, jj, kk]
    ]))

    # convert to function
    return (B[0] + B[1] + B[2] + B[3]).expand().xreplace({
        (-1)**x: I**(2*x),
    }).subs({
        I * I**(3*x): I**(3*x + 1),
    })

if __name__ == "__main__":
    x: Symbol
    y: Symbol
    a: Symbol
    b: Symbol
    c: Symbol
    d: Symbol

    x, y, a, b, c, d = symbols('x, y, a, b, c, d')

    f = encode(Matrix([[a, b, c, d]]))
    pprint(f)
    sep_print()
    fI1 = encode(Matrix([[I**a, I**b, I**c, I**d]]))
    pprint(fI1)
    sep_print()
    fI2 = encode(Matrix([[I**(2*a), I**(2*b), I**(2*c), I**(2*d)]]))
    pprint(fI2)
    sep_print()
    fI3 = encode(Matrix([[I**(3*a), I**(3*b), I**(3*c), I**(3*d)]]))
    fI3 = fI3.subs({
        I**(3*a) * I**(3*x):        I**(3*a + 3*x),
        I**(3*a) * I**(2*x):        I**(3*a + 2*x),
        I**(3*a) * I**x:            I**(3*a + x),
        I**(3*b) * I**(2*x):        I**(3*b + 2*x),
        I * I**(3*b) * I**(x):      I**(3*b + x + 1),
        I**(3*b) * I**(3*x + 1):    I**(3*b + 3*x + 1),
        I**(3*c) * I**(3*x):        I**(3*c + 3*x),
        I**(3*c) * I**(2*x):        I**(3*c + 2*x),
        I**(3*c) * I**x:            I**(3*c + x),
        I**(3*d) * I**(2*x):        I**(3*d + 2*x),
        I * I**(3*d) * I**x:        I**(3*d + x + 1),
        I**(3*d) * I**(3*x + 1):    I**(3*d + 3*x + 1),
    }).xreplace({
        
    })
    pprint(fI3)
    sep_print()

    print([(fI1).subs({x: n}) for n in range(4)])
    print([(fI2).subs({x: n}) for n in range(4)])
    print([(fI3).subs({x: n}) for n in range(4)])
    sep_print()
