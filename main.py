from functor import Functor
from utils import matrix_print
from sympy import print_maple_code, symbols

if __name__ == "__main__":
    # initialize everything
    N = 43*107
    fn = Functor(N)
    bits = 0
    rotate_x = False

    # loop through the constructions
    for i in range(18):
        # print some stats
        print("Iteration: " + str(i))
        print("Bits reduced: " + str(bits))
        if 2**bits > N//2:
            break

        fn.print()

        # perform the lift and record what happened
        function, is_reduced, is_rotated = fn.lift(rotate_x=rotate_x)

        # flip the rotation bit if the function was rotated.  allows for even distribution
        if is_rotated:
            rotate_x = not rotate_x

        # if a reduction occurred then record it
        if is_reduced is True:
            bits += 1

        # create a new functor object based on the constructed function
        fn = Functor(function)

    print("Bits reduced: " + str(bits))
    fn.print()
    matrix_print(fn.gen_matrix(m=8))
