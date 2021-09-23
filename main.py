from functor import Functor
from utils import matrix_print

if __name__ == "__main__":
    fn = Functor(43*107)
    bits = 0
    rotate_x = False
    for i in range(15):
        # print some stats
        print("Iteration: " + str(i))
        print("Bits reduced: " + str(bits))
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
    matrix_print(fn.gen_matrix(m=4))
