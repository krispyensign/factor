from sympy import (  # type: ignore
    Symbol,
    symbols,
    Matrix,
    Add,
    Mul,
    Rational,
    Function,
    Mod
)


class i(Function):
    """Walsh[1] function"""
    @classmethod
    def eval(cls, n) -> int | Function:
        if n.is_Integer:
            match Mod(n, 4):
                case 0: return 1
                case 1: return -1
                case 2: return 1
                case 3: return -1


class j(Function):
    """Walsh[2] function"""
    @classmethod
    def eval(cls, n) -> int | Function:
        if n.is_Integer:
            match Mod(n, 4):
                case 0: return 1
                case 1: return 1
                case 2: return -1
                case 3: return -1


class k(Function):
    """Walsh[3] function"""
    @classmethod
    def eval(cls, n) -> int | Function:
        if n.is_Integer:
            match Mod(n, 4):
                case 0: return 1
                case 1: return -1
                case 2: return -1
                case 3: return 1


# define some global symbols
x: Symbol = symbols('x')
y: Symbol = symbols('y')
n: list[Symbol] = symbols(','.join([f"n{ii}" for ii in range(29)]))
a: list[Symbol] = symbols(','.join([f"a{ii}" for ii in range(18)]))
b: list[Symbol] = symbols(','.join([f"b{ii}" for ii in range(18)]))
c: list[Symbol] = symbols('c0, c1, c2, c3')
d: list[Symbol] = symbols('d0, d1, d2, d3')
e: list[Symbol] = symbols('e0, e1, e2, e3')


def condense_terms_d(f: Add) -> Add:
    return f.subs({
        d[0]/4 + d[1]/4 + d[2]/4 + d[3]/4: e[0]/4,
        d[0]/4 - d[1]/4 + d[2]/4 - d[3]/4: e[1]/4,
        d[0]/4 + d[1]/4 - d[2]/4 - d[3]/4: e[2]/4,
        d[0]/4 - d[1]/4 - d[2]/4 + d[3]/4: e[3]/4,
    })


def condense_terms_c(f: Add) -> Add:
    return f.subs({
        c[0] + c[1] + c[2] + c[3]: d[0],
        c[0] - c[1] + c[2] - c[3]: d[1],
        c[0] + c[1] - c[2] - c[3]: d[2],
        c[0] - c[1] - c[2] + c[3]: d[3],
    })


def walsh_reduction(f: Add) -> Add:
    # perform reduction of walsh function args
    return f.expand().subs({
        i(2*y): 1,
        i(2*x): 1,
        j(2*x): i(x),
        j(2*y): i(y),
        k(2*x): i(x),
        k(2*y): i(y),
    })


def hadamard_transform(A: Matrix, v: Symbol) -> Add | Mul:
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
        B[1]*i(v) +
        B[2]*j(v) +
        B[3]*k(v)
    )


def create_generalized_polynomial() -> Add:
    # define the core function
    return (
        n[0]*x**2 +
        n[1]*x*y +
        n[2]*y**2 +

        x*(
            n[3] +

            n[4]*i(a[0]*x) +
            n[5]*i(b[0]*y) +
            n[6]*i(a[1]*x + b[1]*y) +

            n[6]*j(a[2]*x) +
            n[7]*j(b[2]*y) +
            n[8]*j(a[3]*x + b[3]*y) +

            n[6]*k(a[4]*x) +
            n[7]*k(b[4]*y) +
            n[8]*k(a[5]*x + b[5]*y)
        ) +

        y*(
            n[9] +

            n[10]*i(a[6]*x) +
            n[11]*i(b[6]*y) +
            n[12]*i(a[7]*x + b[7]*y) +

            n[13]*j(a[8]*x) +
            n[14]*j(b[8]*y) +
            n[15]*j(a[9]*x + b[9]*y) +

            n[16]*k(a[10]*x) +
            n[17]*k(b[10]*y) +
            n[18]*k(a[11]*x + b[11]*y)
        ) +

        (
            n[19] +

            n[20]*i(a[12]*x) +
            n[21]*i(b[12]*y) +
            n[22]*i(a[13]*x + b[13]*y) +

            n[23]*j(a[14]*x) +
            n[24]*j(b[14]*y) +
            n[25]*j(a[15]*x + b[15]*y) +

            n[26]*k(a[16]*x) +
            n[27]*k(b[16]*y) +
            n[28]*k(a[17]*x + b[17]*y)
        )
    )


def create_generalized_shift(v: Symbol) -> Add:
    return condense_terms_c(hadamard_transform(Matrix([[c[ii] for ii in range(4)]]), v)*4)/4


def encode(coeff: Symbol, shift: Add, v: Symbol, walsh: Function) -> Add:
    return condense_terms_d(hadamard_transform(Matrix([[walsh(coeff*shift.subs({v: ii})) for ii in range(4)]]), v))


def shift_polynomial(f: Add, v: Symbol, w: Symbol, shift: Add) -> Add:
    # define a local temp symbol
    q: Symbol = symbols('q')

    # introduce q to be incrementally substituted with shift
    g: Add = f.subs({v: v + q}).expand()

    # encode everything to reduce to simpler form
    for s in [a, b]:
        for ii in range(18):
            # substitute with encoding
            g = g.xreplace({
                i(s[ii]*q): encode(s[ii], shift, w, i),
                j(s[ii]*q): encode(s[ii], shift, w, j),
                k(s[ii]*q): encode(s[ii], shift, w, k),
            })

    return walsh_reduction(g.subs({
        q: shift,
    }).expand())
