from sympy import Symbol, symbols, I, Matrix, Add, Mul, Rational  # type: ignore


def core() -> Add:
    # define some symbols
    x: Symbol
    y: Symbol
    x, y = symbols('x, y')
    n: list[Symbol] = symbols(','.join([f"n{i}" for i in range(12)]))
    a: list[Symbol] = symbols(','.join([f"a{i}" for i in range(12)]))
    b: list[Symbol] = symbols(','.join([f"b{i}" for i in range(12)]))

    # define the core function
    return (n[0]*x**2 + n[1]*x*y + n[2]*y**2 +

            n[3]*x + n[4]*x*I**(x*a[0] + b[0]) +
            n[5]*x*I**(a[1]*x + b[1])*I**(a[2]*y + b[2]) + n[6]*x*I**(a[3]*y + b[3]) +

            n[7]*y + n[8]*y*I**(x*a[4] + b[4]) +
            n[9]*y*I**(a[5]*x + b[5])*I**(a[6]*y + b[6]) + n[10]*y*I**(a[7]*y + b[7]) +

            n[11] + n[12]*I**(x*a[8] + b[8]) +
            n[13]*I**(a[9]*x + b[9])*I**(a[10]*y + b[10]) + n[14]*y*I**(a[11]*y + b[11]))


def encode(A: Matrix, w: Symbol) -> Add | Mul:
    # perform hadamard transform
    B: Matrix = (A * Matrix([
        [1,  1,  1,  1],
        [1, -1,  1, -1],
        [1,  1, -1, -1],
        [1, -1, -1,  1],
    ]))

    # convert to function
    return Rational(1/4)*(
        B[0] +
        B[1]*I**(2*w) +
        B[2]*(I**w/2 + I**(w + 3)/2 + I**(3*w + 1)/2 - I**(3*w + 2)/2) +
        B[3]*(I**(3*w)/2 + I**w/2 + I**(w + 1)/2 - I**(3*w + 1)/2)
    )


def build_shift_any(f: Add, is_x: bool = True) -> Add:
    w: Symbol
    v: Symbol
    if is_x is True:
        w = symbols('x')
        v = symbols('y')
    else:
        w = symbols('y')
        v = symbols('x')

    c: list[Symbol] = symbols('c0, c1, c2, c3')
    d: list[Symbol] = symbols('d0, d1, d2, d3')
    e: list[Symbol] = symbols('e0, e1, e2, e3')
    g: list[Symbol] = symbols('g0, g1, g2, g3')

    fn = encode(Matrix([[c[0], c[1], c[2], c[3]]]), w)

    fn2 = fn.subs({
        c[0] + c[1] + c[2] + c[3]:  d[0],
    }).xreplace({
        c[0] - c[1] + c[2] - c[3]:  d[1],
    }).xreplace({
        c[0] + c[1] - c[2] - c[3]:  d[2],
    }).xreplace({
        c[0] - c[1] - c[2] + c[3]:  d[3],
    }).expand()
