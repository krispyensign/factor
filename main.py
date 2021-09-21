from functor import Functor


if __name__ == "__main__":
    fn = Functor(91)
    bits = 0
    for i in range(9):
        f, r = fn.lift()
        if r is True:
            bits += 1
        fn = Functor(f)

    print("Bits reduced: " + str(bits))
    fn.print()
