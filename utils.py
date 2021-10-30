from sympy import Integer # type: ignore


def sep_print():
    print('='*40)


def matrix_print(m: list[list[Integer]]):
    print("\n")
    for row in m:
        print(row)
    print("\n")
