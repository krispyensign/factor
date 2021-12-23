from sympy import (  # type: ignore
    Symbol,
    symbols,
    Matrix,
    Add,
    Mul,
    Rational,
    Function,
    Mod,
    Expr,
    pprint,
)

# define some global symbols
x: Symbol = symbols('x')
y: Symbol = symbols('y')
a: list[Symbol] = symbols(','.join([f"a{n}" for n in range(18)]))
b: list[Symbol] = symbols(','.join([f"b{n}" for n in range(18)]))
c: list[Symbol] = symbols('c0, c1, c2, c3')
d: list[Symbol] = symbols('d0, d1, d2, d3')
e: list[Symbol] = symbols('e0, e1, e2, e3')


class w1(Function):
    """Walsh[1] function"""
    @classmethod
    def eval(cls, n: Expr) -> int | Function:
        if n.is_Symbol:
            return

        elif n.is_Integer:
            match Mod(n, 2):
                case 0: return 1
                case 1: return -1
        
        elif n == 2*x + w1(x)/2 + Rational(1/2): # Zi_expr_1
            return -w1(x)
        elif n == 2*y + w1(y)/2 + Rational(1/2): # Zi_expr_1
            return -w1(y)
        elif n == x + y: # Zi_add_l
            return w1(x)*w1(y)
        
        elif n in [2*x, 4*x, 6*x, 2*y, 4*y, 6*y]:
            return 1
        elif n in [2*x + 1, 2*y + 1]:
            return -1
        elif n in [2*x + 2, 2*y + 2]:
            return 1
        elif n in [x - w1(y) + Rational(1), #Zi_expr_2
                   2*x - w1(x)/2 + Rational(1/2), # Zi_expr_3
                   2*x + w1(x)/2 - Rational(1/2)]: # Zi_expr_5
            return w1(x)
        elif n in [y - w1(x) + Rational(1), #Zi_expr_2
                   2*y - w1(y)/2 + Rational(1/2), # Zi_expr_3
                   2*y + w1(y)/2 - Rational(1/2)]: # Zi_expr_5
            return w1(y)
        elif n in [x + w1(y)/2 + Rational(1/2), #Zi_expr_4
                   y + w1(x)/2 + Rational(1/2), #Zi_expr_4
                   x + y + 1]: #zi_add_l
            return -w1(x)*w1(y)


class w2(Function):
    """Walsh[2] function"""
    @classmethod
    def eval(cls, n: int | Expr) -> int | Function:
        if n.is_Integer:
            match Mod(n, 4):
                case 0: return 1
                case 1: return 1
                case 2: return -1
                case 3: return -1


class w3(Function):
    """Walsh[3] function"""
    @classmethod
    def eval(cls, n: int | Expr) -> int | Function:
        if n.is_Integer:
            match Mod(n, 4):
                case 0: return 1
                case 1: return -1
                case 2: return -1
                case 3: return 1


def condense_terms_d(f: Add) -> Add:
    return f.subs({
        d[0]/4 + d[1]/4 + d[2]/4 + d[3]/4: e[0],
        d[0]/4 - d[1]/4 + d[2]/4 - d[3]/4: e[1],
        d[0]/4 + d[1]/4 - d[2]/4 - d[3]/4: e[2],
        d[0]/4 - d[1]/4 - d[2]/4 + d[3]/4: e[3],
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
        w1(x)**2: 1,
        w2(x)**2: 1,
        w3(x)**2: 1,

        w1(y)**2: 1,
        w2(y)**2: 1,
        w3(y)**2: 1,

        w2(2*x): w1(x),
        w3(2*x): w1(x),

        w2(2*y): w1(y),
        w3(2*y): w1(y),
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
        B[1]*w1(v) +
        B[2]*w2(v) +
        B[3]*w3(v)
    )


def create_generalized_shift(v: Symbol) -> Add:
    return condense_terms_c(hadamard_transform(Matrix([[c[n] for n in range(4)]]), v)*4)/4


def encode(coeff: Symbol, shift: Add, v: Symbol, walsh: Function) -> Add:
    return condense_terms_d(
        hadamard_transform(
            Matrix([[walsh(coeff*shift.subs({v: n})) for n in range(4)]]), v)
    )


def shift_polynomial(f: Add, v: Symbol, w: Symbol, shift: Add) -> Add:
    # define a local temp symbol
    q: Symbol = symbols('q')

    # introduce q to be incrementally substituted with shift
    g: Add = f.subs({v: v + q}).expand()

    # TODO: add more replacers for encoding.
    # encode everything to reduce to simpler form
    for s in [a, b]:
        for n in range(18):
            # substitute with encoding
            g = g.xreplace({
                w1(s[n]*q): encode(s[n], shift, w, w1),
                w2(s[n]*q): encode(s[n], shift, w, w2),
                w3(s[n]*q): encode(s[n], shift, w, w3),
            })

    return walsh_reduction(g.subs({
        q: shift,
    }).expand())
