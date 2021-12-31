from math import gcd
from sympy import symbols, I, Rational, pprint # type: ignore
from functor import Functor
from utils import matrix_print
from core import w1

if __name__ == "__main__":
    # initialize everything
    N = 54547 * 24407
    x, y = symbols('x,y')
    f = x**2 - y**2 - N
    fn = Functor(f)
    # fn = Functor(4*x**2 + 2*x*w1(x) + 4*x*w1(y) + 4*x - y**2 + w1(x)*w1(y) + w1(x) + 2*w1(y) + Rational(9/4))
    # fn = Functor(-x**2 + 16*y**2 + 16*y + 1331328633)
    # fn = Functor(-x**2 + 64*y**2  + 32*y + 1331328633)
    # 3*x**2 + 8*x*y + 8*x + 5*y - 20802006     -6819    2175
    # 3*x**2 + 8*x*y + 15*x + 7*y - 20801999    3050    -293
    # 3*x**2 + 8*x*y + 7*x + y - 20802009       -3051   291
    # 3*x**2 + 8*x*y + 14*x + 3*y - 20802005    6818    -2177

    # 16*x**2 + 16*x*y + 11*x + 3*y**2 + 5*y - 20802008     -292    -1884
    # 16*x**2 + 16*x*y + 21*x + 3*y**2 + 10*y - 20802003    2175    -1884
    # 16*x**2 + 16*x*y + 27*x + 3*y**2 + 12*y - 20801999    -2176   1883
    # 16*x**2 + 16*x*y + 37*x + 3*y**2 + 17*y - 20801989    291     1883
    bits = 0
    rotation = False
    matchFailure = False

    # loop through the constructions
    for i in range(16):
        # print some stats
        print("Iteration: " + str(i))
        print("Bits reduced: " + str(bits))
        print("Sqrt N bits: " + str(len(bin(int(N**(1/2))))))
        fn.print(print_full=True)
        if bits >= len(bin(int(N**(1/2)))):
            break

        # perform the lift and record what happened
        try:
            function, is_reduced, is_rotated, _ = fn.lift(rotation)
            if is_rotated is True:
                rotation = not rotation

        except:
            matchFailure = True
            break

        # if a reduction occurred then record it
        if is_reduced is True:
            bits += 1

        # create a new functor object based on the constructed function
        fn = Functor(function)

    print("Bits reduced: " + str(bits))
    # fn.print(print_full=True)
    fn.print(print_full=False)
    matrix_print(fn.gen_matrix(m=8))
    if matchFailure == True:
        print("Failed to match.")
