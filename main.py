from functor import Functor
from utils import matrix_print

if __name__ == "__main__":
    # initialize everything
    N = 313 * 223
    fn = Functor(N)
    bits = 0

    # loop through the constructions
    for i in range(19):
        # print some stats
        print("Iteration: " + str(i))
        print("Bits reduced: " + str(bits))
        print("Sqrt N bits: " + str(len(bin(int(N**(1/2))))))
        if bits >= len(bin(int(N**(1/2)))):
            break

        fn.print()

        # perform the lift and record what happened
        function, is_reduced = fn.lift()

        # if a reduction occurred then record it
        if is_reduced is True:
            bits += 1

        # create a new functor object based on the constructed function
        fn = Functor(function)

    print("Bits reduced: " + str(bits))
    fn.print()
    matrix_print(fn.gen_matrix(m=8))
