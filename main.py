from functor import Functor
from utils import matrix_print

if __name__ == "__main__":
    fn = Functor(43*107)
    bits = 0
    rotate_x = False
    for i in range(15):
        print("Iteration: " + str(i))
        print("Bits reduced: " + str(bits))
        fn.print()
        f, r, is_rotated = fn.lift(rotate_x=rotate_x)
        if is_rotated:
            rotate_x = not rotate_x
        if r is True:
            bits += 1
        fn = Functor(f)

    print("Bits reduced: " + str(bits))
    fn.print()
    matrix_print(fn.gen_matrix(m=4))
