from functor import Functor


if __name__ == "__main__":
    fn = Functor(91)
    for i in range(4):
        f = fn.lift()
        fn = Functor(f)

    fn.finalize()
