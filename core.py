from sympy import Symbol, symbols, I, Matrix, Add, Mul, Rational  # type: ignore

# define some global symbols
x: Symbol
y: Symbol
x, y = symbols('x, y')
i, j, k = symbols('i, j, k')
n: list[Symbol] = symbols(','.join([f"n{ii}" for ii in range(29)]))
a: list[Symbol] = symbols(','.join([f"a{ii}" for ii in range(18)]))
b: list[Symbol] = symbols(','.join([f"b{ii}" for ii in range(18)]))
c: list[Symbol] = symbols('c0, c1, c2, c3')
d: list[Symbol] = symbols('d0, d1, d2, d3')
e: list[Symbol] = symbols('e0, e1, e2, e3')


def core() -> Add:
    # define the core function
    return (
        n[0]*x**2 +
        n[1]*x*y +
        n[2]*y**2 +

        x*(
            n[3] +

            n[4]*i**(a[0]*x) +
            n[5]*i**(b[0]*y) +
            n[6]*i**(a[1]*x + b[1]*y) +

            n[6]*j**(a[2]*x) +
            n[7]*j**(b[2]*y) +
            n[8]*j**(a[3]*x + b[3]*y) +

            n[6]*k**(a[4]*x) +
            n[7]*k**(b[4]*y) +
            n[8]*k**(a[5]*x + b[5]*y)
        ) +

        y*(
            n[9] +

            n[10]*i**(a[6]*x) +
            n[11]*i**(b[6]*y) +
            n[12]*i**(a[7]*x + b[7]*y) +

            n[13]*j**(a[8]*x) +
            n[14]*j**(b[8]*y) +
            n[15]*j**(a[9]*x + b[9]*y) +

            n[16]*k**(a[10]*x) +
            n[17]*k**(b[10]*y) +
            n[18]*k**(a[11]*x + b[11]*y)
        ) +

        (
            n[19] +

            n[20]*i**(a[12]*x) +
            n[21]*i**(b[12]*y) +
            n[22]*i**(a[13]*x + b[13]*y) +

            n[23]*j**(a[14]*x) +
            n[24]*j**(b[14]*y) +
            n[25]*j**(a[15]*x + b[15]*y) +

            n[26]*k**(a[16]*x) +
            n[27]*k**(b[16]*y) +
            n[28]*k**(a[17]*x + b[17]*y)
        )
    )


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
        B[1]*i**w +
        B[2]*j**w +
        B[3]*k**w
    )


def build_shift_any(f: Add, w: Symbol) -> Add:
    return encode(Matrix([[c[0], c[1], c[2], c[3]]]), w).subs({
        c[0]/4 + c[1]/4 + c[2]/4 + c[3]/4:  d[0]/4,
        c[0] - c[1] + c[2] - c[3]:  d[1],
        c[0] + c[1] - c[2] - c[3]:  d[2],
        c[0] - c[1] - c[2] + c[3]:  d[3],
    })


def encode_smooth(r: Symbol, shift: Add, v: Symbol, base: Symbol) -> Add:
    return encode(Matrix([[base**(r*shift.subs({v: ii})) for ii in range(4)]]), v).subs({
        # smooth powers to reduce climbing powers and for better grouping
        i**2: 1,
        j**2: -1,
        k**2: -1,

        i**3: -1,
        j**3: -1,
        k**3: 1,

        i: i,
        j: 1,
        k: i,
    }).xreplace({
        # group values and introduce e[n]
        d[0]/4 + d[1]/4 + d[2]/4 + d[3]/4: e[0],
        d[0]/4 - d[1]/4 + d[2]/4 - d[3]/4: e[1],
        d[0]/4 + d[1]/4 - d[2]/4 - d[3]/4: e[2],
        d[0]/4 - d[1]/4 - d[2]/4 + d[3]/4: e[3],
        d[0]/4 + i*d[1]/4 + d[2]/4 + i*d[3]/4: e[1],
    })


def core_shift_smooth(f: Add, w: Symbol, v: Symbol, shift: Add):
    # define a local temp symbol
    q: Symbol = symbols('q')

    # introduce q
    g: Add = f.subs({w: w + q}).expand()

    # encode everything to reduce climbing powers
    for ii in range(18):
        # encode and smooth
        u = encode_smooth(a[ii], shift, v, i)

        # substitute
        g = g.xreplace({
            i**(a[ii]*q): u
        }).expand()

        # encode and smooth
        u = encode_smooth(a[ii], shift, v, j)

        # substitute
        g = g.xreplace({
            j**(a[ii]*q): u
        }).expand()

        # encode and smooth
        u = encode_smooth(a[ii], shift, v, k)

        # substitute
        g = g.xreplace({
            k**(a[ii]*q): u
        }).expand()

        # encode and smooth
        u = encode_smooth(b[ii], shift, v, i)

        # substitute
        g = g.xreplace({
            i**(b[ii]*q): u
        }).expand()

        # encode and smooth
        u = encode_smooth(b[ii], shift, v, j)

        # substitute
        g = g.xreplace({
            j**(b[ii]*q): u
        }).expand()

        # encode and smooth
        u = encode_smooth(b[ii], shift, v, k)

        # substitute
        g = g.xreplace({
            k**(b[ii]*q): u
        }).expand()

    return g.subs({
        q: shift,
    }).xreplace({
        # group values and introduce e[n]
        d[0]/4 + d[1]/4 + d[2]/4 + d[3]/4: e[0],
        d[0]/4 - d[1]/4 + d[2]/4 - d[3]/4: e[1],
        d[0]/4 + d[1]/4 - d[2]/4 - d[3]/4: e[2],
        d[0]/4 - d[1]/4 - d[2]/4 + d[3]/4: e[3],
        d[0]/4 + i*d[1]/4 + d[2]/4 + i*d[3]/4: e[1],
    }).expand().subs({
        # smooth more powers
        i**(2*y): 1,
        i**(2*x): 1,
        j**(2*x): i**x,
        j**(2*y): i**y,
        k**(2*x): i**x,
        k**(2*y): i**y,
    })
