from sympy import (
    Mod,
    symbols,
    print_maple_code,
    pprint,
    Add,
    Integer,
    Symbol,
    I
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

    def print(self):
        fn1 = Functor(self.f.subs({self.x: 2*self.x, self.y: 2*self.y}))
        print(fn1.smooth())
        fn2 = Functor(self.f.subs({self.x: 2*self.x + 1, self.y: 2*self.y}))
        print(fn2.smooth())
        fn3 = Functor(self.f.subs({self.x: 2*self.x, self.y: 2*self.y + 1}))
        print(fn3.smooth())
        fn4 = Functor(self.f.subs({self.x: 2*self.x + 1, self.y: 2*self.y + 1}))
        print(fn4.smooth())
        print(self.f)
        pprint(self.f)
        print(self.f)
        matrix_print(self.gen_matrix())
        sep_print()

    def gen_matrix(self, m=4) -> list[list[Integer]]:
        return [[Integer(Mod(self.f, 2).subs({self.x: i, self.y: j})) for i in range(m)] for j in range(m)]

    def lift(self, rotate_x: bool) -> Tuple[Add, bool, bool]:
        do_division, sub_expression, is_rotated = self.matcher(
            self.gen_matrix(), rotate_x=rotate_x)
        pprint(sub_expression)

        f = Functor(self.f.subs(sub_expression)).smooth()
        if do_division is True:
            f /= 2

        return f, do_division, is_rotated

    def smooth(self) -> Add:
        return (self.f
                .subs((-1)**((-1)**self.x/2),  I*(-1)**self.x)
                # 0, 3, 4, 7, ... => 1 -1 1 -1
                .subs((-1)**(2*self.y + (1 - (-1)**self.y)/2), (-1)**self.y)
                # 0, 3, 4, 7, ... => 1 -1 1 -1
                .subs((-1)**(2*self.x + (1 - (-1)**self.x)/2), (-1)**self.x)

                # 0, 1, 4, 5, ... => 1 -1 1 -1
                .subs((-1)**(2*self.y - (1 - (-1)**self.y)/2), (-1)**self.y)
                # 0, 1, 4, 5, ... => 1 -1 1 -1
                .subs((-1)**(2*self.x - (1 - (-1)**self.x)/2), (-1)**self.x)

                # 1, 2, 5, 6, ... => -1 1 -1 1
                .subs((-1)**(2*self.x - (1 - (-1)**self.x)/2 + 1), (-1)**(self.x + 1))
                .subs((-1)**(2*self.y - (1 - (-1)**self.y)/2 + 1), (-1)**(self.y + 1))

                # 2, 3, 6, 7, ... => 1 -1 1 -1
                .subs((-1)**(2*self.y - (1 - (-1)**self.y)/2 + 2), (-1)**self.y)
                .subs((-1)**(2*self.x - (1 - (-1)**self.x)/2 + 2), (-1)**self.x)

                .subs((-1)**(self.x - (1 - (-1)**self.y) / 2), (-1)**(self.x + self.y))
                .subs((-1)**(self.y - (1 - (-1)**self.x) / 2), (-1)**(self.x + self.y))
                .subs((-1)**(self.x + (1 - (-1)**self.y) / 2), (-1)**(self.x + self.y))
                .subs((-1)**(self.y + (1 - (-1)**self.x) / 2), (-1)**(self.x + self.y))

                .expand()

                .subs((-1)**(2*self.y), 1)
                .subs((-1)**(2*self.x), 1)
                .subs((-1)**(3*self.y), (-1)**self.y)
                .subs((-1)**(3*self.x), (-1)**self.x)
                .subs((-1)**((-1)**self.x), -1)
                .subs((-1)**((-1)**self.y), -1))

    def matcher(
        self,
        m: list[list[Integer]],
        rotate_x: bool
    ) -> Tuple[bool, dict[Symbol, Add], bool]:

        # setup rotation, rotate different direction than last time
        rotator: dict[Symbol, Add]
        if rotate_x is True:
            rotator = {self.x: self.x + self.y}
        else:
            rotator = {self.y: self.x + self.y}

        if m == [[1, 0, 1, 0], [1, 0, 1, 0], [1, 0, 1, 0], [1, 0, 1, 0]]:
            return True, {self.x: 2*self.x + 1}, False

        elif m == [[0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1], [0, 1, 0, 1]]:
            return True, {self.x: 2*self.x}, False

        elif m == [[1, 1, 1, 1], [1, 0, 1, 0], [1, 1, 1, 1], [1, 0, 1, 0]]:
            return True, {self.x: 2*self.x + 1, self.y: 2*self.y + 1}, False

        elif m == [[1, 0, 1, 0], [0, 1, 0, 1], [1, 0, 1, 0], [0, 1, 0, 1]]:
            return False, {self.x: self.x + (1 - (-1)**self.y) / 2}, False
        elif m == [[0, 1, 0, 1], [1, 0, 1, 0], [0, 1, 0, 1], [1, 0, 1, 0]]:
            return False, {self.x: self.x + (1 - (-1)**self.y) / 2}, False

        elif m == [[1, 1, 0, 0], [1, 0, 0, 1], [1, 1, 0, 0], [1, 0, 0, 1]]:
            return False, {self.x: self.x - (1 - (-1)**self.y) / 2}, False

        elif m == [[1, 1, 1, 1], [1, 0, 1, 0], [0, 0, 0, 0], [0, 1, 0, 1]]:
            return False, {self.y: self.y - (1 - (-1)**self.x) / 2}, False
        elif m == [[1, 1, 1, 1], [0, 1, 0, 1], [0, 0, 0, 0], [1, 0, 1, 0]]:
            return False, {self.y: self.y - (1 - (-1)**self.x) / 2}, False

        elif m == [[0, 1, 1, 0], [0, 0, 1, 1], [0, 1, 1, 0], [0, 0, 1, 1]]:
            return False, {self.x: self.x + (1 - (-1)**self.y) / 2}, False

        elif m == [[1, 1, 0, 0], [0, 0, 1, 1], [1, 1, 0, 0], [0, 0, 1, 1]]:
            return False, {self.x: self.x + 1 - (-1)**(self.y + 1)}, False
        elif m == [[0, 0, 1, 1], [1, 1, 0, 0], [0, 0, 1, 1], [1, 1, 0, 0]]:
            return False, {self.x: self.x + 1 - (-1)**(self.y + 1)}, False

        elif m == [[1, 0, 0, 1], [0, 1, 1, 0], [1, 0, 0, 1], [0, 1, 1, 0]]:
            return False, {self.x: self.x + 1 - (-1)**self.y}, False

        elif m == [[0, 1, 0, 1], [0, 1, 0, 1], [1, 0, 1, 0], [1, 0, 1, 0]]:
            return False, {self.y: self.y + 1 - (-1)**self.x}, False
        elif m == [[0, 1, 0, 1], [1, 0, 1, 0], [1, 0, 1, 0], [0, 1, 0, 1]]:
            return False, {self.y: self.y + 1 - (-1)**self.x}, False
        elif m == [[1, 0, 1, 0], [0, 1, 0, 1], [0, 1, 0, 1], [1, 0, 1, 0]]:
            return False, {self.y: self.y + 1 - (-1)**self.x}, False

        elif m == [[0, 0, 1, 1], [1, 1, 0, 0], [1, 1, 0, 0], [0, 0, 1, 1]]:
            return False, {self.x: self.x - 1}, False
        
        elif m == [[0, 1, 1, 0], [0, 0, 1, 1], [0, 0, 1, 1], [1, 0, 0, 1]]:
            return False, {self.x: self.x - (1-(-1)**self.x)/2 + self.y + 1}, False

        elif m == [[0, 0, 0, 0], [1, 1, 1, 1], [1, 1, 1, 1], [0, 0, 0, 0]]:
            return True, {self.y: 2*self.y + (1 - (-1)**self.y) / 2}, False

        elif m == [[0, 1, 1, 0], [0, 1, 1, 0], [0, 1, 1, 0], [0, 1, 1, 0]]:
            return True, {self.x: 2*self.x + (1 - (-1)**self.x) / 2}, False

        elif m == [[0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1], [0, 0, 1, 1]]:
            return True, {self.x: 2*self.x - (1 - (-1)**self.x) / 2}, False

        elif m == [[0, 0, 0, 0], [0, 0, 0, 0], [1, 1, 1, 1], [1, 1, 1, 1]]:
            return True, {self.y: 2*self.y - (1 - (-1)**self.y) / 2}, False

        elif m == [[1, 0, 0, 1], [1, 0, 0, 1], [1, 0, 0, 1], [1, 0, 0, 1]]:
            return True, {self.x: 2*self.x - (1 - (-1)**self.x) / 2 + 1}, False

        elif m == [[1, 1, 1, 1], [0, 0, 0, 0], [0, 0, 0, 0], [1, 1, 1, 1]]:
            return True, {self.y: 2*self.y - (1 - (-1)**self.y) / 2 + 1}, False

        elif m == [[1, 1, 0, 0], [1, 1, 0, 0], [1, 1, 0, 0], [1, 1, 0, 0]]:
            return True, {self.x: 2*self.x - (1 - (-1)**self.x) / 2 + 2}, False

        elif m == [[1, 1, 1, 1], [1, 1, 1, 1], [0, 0, 0, 0], [0, 0, 0, 0]]:
            return True, {self.y: 2*self.y - (1 - (-1)**self.y) / 2 + 2}, False

        elif m == [[1, 0, 0, 1], [0, 1, 1, 0], [0, 1, 1, 0], [1, 0, 0, 1]]:
            return False, rotator, True
        elif m == [[1, 1, 0, 0], [1, 1, 0, 0], [0, 0, 1, 1], [0, 0, 1, 1]]:
            return False, rotator, True
        # elif m == [[0, 0, 1, 1], [0, 1, 1, 0], [1, 1, 0, 0], [1, 0, 0, 1]]:
        #     return False, rotator, True
        elif m == [[0, 1, 1, 0], [1, 0, 0, 1], [1, 0, 0, 1], [0, 1, 1, 0]]:
            return False, rotator, True
        # elif m == [[1, 0, 0, 1], [0, 0, 1, 1], [0, 1, 1, 0], [1, 1, 0, 0]]:
        #     return False, rotator, True
        # elif m == [[0, 1, 1, 0], [1, 0, 1, 0], [1, 0, 0, 1], [0, 1, 0, 1]]:
        #     return False, rotator, False

        else:
            raise BaseException("Invalid pattern")
