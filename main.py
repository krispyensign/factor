from sympy.core import symbols # type: ignore
from functor import Functor
from utils import matrix_print

if __name__ == "__main__":
    # initialize everything
    N = 313 * 107
    # N = 313 * 107
    # N = 313 * 223
    # N = 91
    fn = Functor(N)
    bits = 0
    rotation = False
    matchFailure = False

    # loop through the constructions
    for i in range(13):
        # print some stats
        print("Iteration: " + str(i))
        print("Bits reduced: " + str(bits))
        print("Sqrt N bits: " + str(len(bin(int(N**(1/2))))))
        fn.print()
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
    fn.print()
    matrix_print(fn.gen_matrix(m=8))
    if matchFailure == True:
        print("Failed to match.")
