from sympy import (
    Mod,
    symbols,
    pprint,
    Add,
    Integer,
    Symbol,
    I,
    Rational,
    roots
)

from typing import Tuple

from utils import matrix_print, sep_print


class Functor:
    x: Symbol
    y: Symbol
    f: Add

    def __init__(self, z) -> None:
        self.x, self.y = symbols('x y')
        if type(z) == int:
            self.f = self.x * self.y - z
        else:
            self.f = z
            self.f = self.smooth()

    def print(self) -> None:
        # print and pretty print the main function
        pprint(self.f)
        print(self.f)

        # print the 4 sub functions
        pprint(Functor(self.f.subs({self.x: 2*self.x, self.y: 2*self.y})).f)
        pprint(
            Functor(self.f.subs({self.x: 2*self.x + 1, self.y: 2*self.y})).f)
        pprint(
            Functor(self.f.subs({self.x: 2*self.x, self.y: 2*self.y + 1})).f)
        pprint(
            Functor(self.f.subs({self.x: 2*self.x + 1, self.y: 2*self.y + 1})).f)

        # print the matrix
        matrix_print(self.gen_matrix())

        # print the separator
        sep_print()

    def gen_matrix(self, n=2, m=4) -> list[list[Integer]]:
        # generate the m x m (default = 4 x 4) binary matrix
        return [[Integer(Mod(self.f, n).subs({self.x: i, self.y: j})) for i in range(m)] for j in range(m)]

    def lift(self, flip_rotation: bool) -> Tuple[Add, bool, bool, dict[Symbol, Add]]:
        # perform pattern match to get the subexpression and various flags
        do_division, sub_expression, is_rotated = self.matcher(
            self.gen_matrix(), flip_rotation)

        # pretty print the sub expression
        pprint(sub_expression)

        # create a new function with the sub expression and smooth it for faster processing
        f = Functor(self.f.subs(sub_expression)).f

        # if the sub expression is 2*x + w or 2*y + w then divide by two
        if do_division is True:
            f /= 2

        return f, do_division, is_rotated, sub_expression

    def smooth(self) -> Add:
        # replace complicated exponents with simpler isomorphic exponents over the integers
        return (self.f
                .expand()
                .subs((-1)**(2*self.y), 1)
                .subs((-1)**(2*self.x), 1)
                .subs((-1)**(3*self.y), (-1)**self.y)
                .subs((-1)**(3*self.x), (-1)**self.x)
                .subs((-1)**((-1)**self.x), -1)
                .subs((-1)**((-1)**self.y), -1)
                .subs((-1)**(-(-1)**self.x/2), I*(-1)**(self.x + 1))
                .subs((-1)**(-(-1)**self.y/2), I*(-1)**(self.y + 1))
                .subs((-1)**(self.y + 1), -1*(-1)**(self.y))
                .subs((-1)**(self.y - 1), -1*(-1)**(self.y))
                .subs((-1)**(self.x + 1), -1*(-1)**(self.x))
                .subs((-1)**(self.x - 1), -1*(-1)**(self.x))
                .subs((-1)**(-self.y + 1), -1*(-1)**(self.y))
                .subs((-1)**(-self.y - 1), -1*(-1)**(self.y))
                .subs((-1)**(-self.x + 1), -1*(-1)**(self.x))
                .subs((-1)**(-self.x - 1), -1*(-1)**(self.x))
                .subs((-1)**(-self.x), (-1)**(self.x))
                .subs((-1)**(-self.y), (-1)**(self.y)))

    def matcher(
        self,
        m: list[list[Integer]],
        flip_rotation: bool,
    ) -> Tuple[bool, dict[Symbol, Add], bool]:
        # setup rotation

        rotator = {self.x: self.x + self.y}
        if flip_rotation is True:
            rotator = {self.y: self.x + self.y}

        # match simple subexpressions
        if m == [[1, 0, 1, 0],
                 [1, 0, 1, 0],
                 [1, 0, 1, 0],
                 [1, 0, 1, 0]]:
            return True, {self.x: 2*self.x + 1}, False

        elif m == [[0, 1, 0, 1],
                   [0, 1, 0, 1],
                   [0, 1, 0, 1],
                   [0, 1, 0, 1]]:
            return True, {self.x: 2*self.x}, False

        elif m == [[0, 0, 0, 0],
                   [1, 1, 1, 1],
                   [0, 0, 0, 0],
                   [1, 1, 1, 1]]:
            return True, {self.y: 2*self.y}, False

        elif m == [[1, 1, 1, 1],
                   [0, 0, 0, 0],
                   [1, 1, 1, 1],
                   [0, 0, 0, 0]]:
            return True, {self.y: 2*self.y + 1}, False

        elif m == [[1, 1, 1, 1],
                   [1, 0, 1, 0],
                   [1, 1, 1, 1],
                   [1, 0, 1, 0]]:
            return True, {self.x: 2*self.x + 1, self.y: 2*self.y + 1}, False

        # match complex subexpressions
        elif m == [[0, 0, 1, 1],
                   [0, 0, 1, 1],
                   [0, 0, 1, 1],
                   [0, 0, 1, 1]]:
            return True, {self.x: 2*self.x - (1 - (-1)**self.x) / 2}, False

        elif m == [[1, 0, 0, 1],
                   [1, 0, 0, 1],
                   [1, 0, 0, 1],
                   [1, 0, 0, 1]]:
            return True, {self.x: 2*self.x - (1 - (-1)**self.x) / 2 + 1}, False

        elif m == [[1, 1, 0, 0],
                   [1, 1, 0, 0],
                   [1, 1, 0, 0],
                   [1, 1, 0, 0]]:
            return True, {self.x: 2*self.x - (1 - (-1)**self.x) / 2 + 2}, False

        elif m == [[0, 1, 1, 0],
                   [0, 1, 1, 0],
                   [0, 1, 1, 0],
                   [0, 1, 1, 0]]:
            return True, {self.x: 2*self.x + (1 - (-1)**self.x) / 2}, False

        elif m == [[0, 0, 0, 0],
                   [0, 0, 0, 0],
                   [1, 1, 1, 1],
                   [1, 1, 1, 1]]:
            return True, {self.y: 2*self.y - (1 - (-1)**self.y) / 2}, False

        elif m == [[1, 1, 1, 1],
                   [0, 0, 0, 0],
                   [0, 0, 0, 0],
                   [1, 1, 1, 1]]:
            return True, {self.y: 2*self.y - (1 - (-1)**self.y) / 2 + 1}, False

        elif m == [[1, 1, 1, 1],
                   [1, 1, 1, 1],
                   [0, 0, 0, 0],
                   [0, 0, 0, 0]]:
            return True, {self.y: 2*self.y - (1 - (-1)**self.y) / 2 + 2}, False

        elif m == [[0, 0, 0, 0],
                   [1, 1, 1, 1],
                   [1, 1, 1, 1],
                   [0, 0, 0, 0]]:
            return True, {self.y: 2*self.y + (1 - (-1)**self.y) / 2}, False

        # match rotations
        elif m in [[[0, 0, 1, 1],
                    [0, 0, 1, 1],
                    [1, 1, 0, 0],
                    [1, 1, 0, 0]],

                   [[1, 0, 0, 1],
                    [1, 0, 0, 1],
                    [0, 1, 1, 0],
                    [0, 1, 1, 0]],

                   [[1, 1, 0, 0],
                    [1, 1, 0, 0],
                    [0, 0, 1, 1],
                    [0, 0, 1, 1]],

                   [[0, 1, 1, 0],
                    [0, 1, 1, 0],
                    [1, 0, 0, 1],
                    [1, 0, 0, 1]],


                   [[1, 0, 0, 1],
                    [0, 1, 1, 0],
                    [0, 1, 1, 0],
                    [1, 0, 0, 1]],

                   [[0, 0, 1, 1],
                    [1, 1, 0, 0],
                    [1, 1, 0, 0],
                    [0, 0, 1, 1]],

                   [[0, 1, 1, 0],
                    [1, 0, 0, 1],
                    [1, 0, 0, 1],
                    [0, 1, 1, 0]],

                   [[1, 1, 0, 0],
                    [0, 0, 1, 1],
                    [0, 0, 1, 1],
                    [1, 1, 0, 0]],

                   [[0, 0, 1, 1],
                    [1, 0, 0, 1],
                    [1, 1, 0, 0],
                    [0, 1, 1, 0]],

                   [[1, 0, 0, 1],
                    [1, 1, 0, 0],
                    [0, 1, 1, 0],
                    [0, 0, 1, 1]],

                   [[1, 1, 0, 0],
                    [0, 1, 1, 0],
                    [0, 0, 1, 1],
                    [1, 0, 0, 1]],

                   [[0, 1, 1, 0],
                    [0, 0, 1, 1],
                    [1, 0, 0, 1],
                    [1, 1, 0, 0]],

                   [[1, 0, 0, 1],
                    [0, 0, 1, 1],
                    [0, 1, 1, 0],
                    [1, 1, 0, 0]]]:
            return False, rotator, True

        # match shifting
        elif m in [[[1, 1, 0, 0],
                    [1, 0, 0, 1],
                    [1, 1, 0, 0],
                    [1, 0, 0, 1]],

                   [[0, 0, 1, 1],
                    [0, 1, 1, 0],
                    [0, 0, 1, 1],
                    [0, 1, 1, 0]]]:
            return False, {self.x: self.x + (1 - (-1)**(self.y + 1)) / 2}, False

        elif m in [[[1, 1, 0, 0],
                    [0, 0, 1, 1],
                    [1, 1, 0, 0],
                    [0, 0, 1, 1]],

                   [[0, 0, 1, 1],
                    [1, 1, 0, 0],
                    [0, 0, 1, 1],
                    [1, 1, 0, 0]],

                   [[1, 0, 0, 1],
                    [0, 1, 1, 0],
                    [1, 0, 0, 1],
                    [0, 1, 1, 0]],

                   [[0, 1, 1, 0],
                    [1, 0, 0, 1],
                    [0, 1, 1, 0],
                    [1, 0, 0, 1]]]:
            return False, {self.x: self.x + 1 - (-1)**self.y}, False

        elif m in [[[1, 1, 1, 1],
                    [1, 0, 1, 0],
                    [0, 0, 0, 0],
                    [0, 1, 0, 1]],

                   [[0, 0, 0, 0],
                    [0, 1, 0, 1],
                    [1, 1, 1, 1],
                    [1, 0, 1, 0]],

                   [[0, 1, 0, 1],
                    [1, 1, 1, 1],
                    [1, 0, 1, 0],
                    [0, 0, 0, 0]],

                   [[1, 0, 1, 0],
                    [0, 0, 0, 0],
                    [0, 1, 0, 1],
                    [1, 1, 1, 1]]]:
            return False, {self.y: self.y + (1 - (-1)**(self.x + 1)) / 2}, False

        elif m in [[[1, 1, 1, 1],
                    [0, 1, 0, 1],
                    [0, 0, 0, 0],
                    [1, 0, 1, 0]],

                   [[0, 0, 0, 0],
                    [1, 0, 1, 0],
                    [1, 1, 1, 1],
                    [0, 1, 0, 1]],

                   [[0, 1, 0, 1],
                    [0, 0, 0, 0],
                    [1, 0, 1, 0],
                    [1, 1, 1, 1]],

                   [[1, 0, 1, 0],
                    [1, 1, 1, 1],
                    [0, 1, 0, 1],
                    [0, 0, 0, 0]]]:
            return False, {self.y: self.y + (1 - (-1)**self.x) / 2}, False

        elif m in [[[1, 0, 1, 0],
                    [0, 1, 0, 1],
                    [1, 0, 1, 0],
                    [0, 1, 0, 1]],

                   [[0, 1, 0, 1],
                    [1, 0, 1, 0],
                    [0, 1, 0, 1],
                    [1, 0, 1, 0]],

                   [[0, 1, 1, 0],
                    [0, 0, 1, 1],
                    [0, 1, 1, 0],
                    [0, 0, 1, 1]],

                   [[1, 0, 0, 1],
                    [1, 1, 0, 0],
                    [1, 0, 0, 1],
                    [1, 1, 0, 0]],

                   [[0, 0, 1, 1],
                    [1, 0, 0, 1],
                    [0, 0, 1, 1],
                    [1, 0, 0, 1]]]:
            return False, {self.x: self.x + (1 - (-1)**self.y) / 2}, False

        elif m in [[[0, 1, 0, 1],
                    [0, 1, 0, 1],
                    [1, 0, 1, 0],
                    [1, 0, 1, 0]],

                   [[0, 1, 0, 1],
                    [1, 0, 1, 0],
                    [1, 0, 1, 0],
                    [0, 1, 0, 1]],

                   [[1, 0, 1, 0],
                    [1, 0, 1, 0],
                    [0, 1, 0, 1],
                    [0, 1, 0, 1]],

                   [[1, 0, 1, 0],
                    [0, 1, 0, 1],
                    [0, 1, 0, 1],
                    [1, 0, 1, 0]]]:
            return False, {self.y: self.y + 1 - (-1)**self.x}, False

        else:
            raise BaseException("Invalid pattern")
