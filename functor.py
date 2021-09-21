from sympy import (
    Mod,
    symbols,
    print_maple_code,
    pprint,
    Add,
    Integer,
    Symbol
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
        print_maple_code(self.f)
        pprint(self.f)
        matrix_print(self.gen_matrix())
        sep_print()

    def gen_matrix(self) -> list[list[Integer]]:
        return [[Mod(self.f, 2).subs({self.x: i, self.y: j}) for i in range(4)] for j in range(4)]

    def lift(self) -> Tuple[Add, bool]:
        do_division, sub_expression = self.matcher(self.gen_matrix())

        f = Functor(self.f.subs(sub_expression)).smooth()
        if do_division is True:
            f /= 2

        return f, do_division

    def smooth(self) -> Add:
        return (self.f
                .subs((-1)**(2*self.y + (1 - (-1)**self.y)/2), (-1)**self.y)
                .subs((-1)**(2*self.x + (1 - (-1)**self.x)/2), (-1)**self.x)
                .subs((-1)**(2*self.y - (1 - (-1)**self.y)/2 + 2), (-1)**self.x)
                .subs((-1)**(2*self.x - (1 - (-1)**self.x)/2 + 2), (-1)**self.x)
                .subs((-1)**(self.x - (1 - (-1)**self.y) / 2), (-1)**(self.x + self.y))
                .subs((-1)**(self.y - (1 - (-1)**self.x) / 2), (-1)**(self.x + self.y))
                .expand()
                .subs((-1)**(2*self.y), 1)
                .subs((-1)**(2*self.x), 1)
                .subs((-1)**(3*self.y), (-1)**self.y)
                .subs((-1)**(3*self.x), (-1)**self.x)
                .subs((-1)**((-1)**self.x), -1)
                .subs((-1)**((-1)**self.y), -1))

    def matcher(self, m: list[list[Integer]]) -> Tuple[bool, dict[Symbol, Add]]:
        if m == [[1, 1, 1, 1], [1, 0, 1, 0], [1, 1, 1, 1], [1, 0, 1, 0]]:
            return True, {self.x: 2*self.x + 1, self.y: 2*self.y + 1}
        elif m == [[1, 0, 1, 0], [0, 1, 0, 1], [1, 0, 1, 0], [0, 1, 0, 1]]:
            return False, {self.x: self.x + (1 - (-1)**self.y) / 2}
        elif m == [[1, 0, 1, 0], [1, 0, 1, 0], [1, 0, 1, 0], [1, 0, 1, 0]]:
            return True, {self.x: 2*self.x + 1}
        elif m == [[0, 1, 0, 1], [1, 0, 1, 0], [1, 0, 1, 0], [0, 1, 0, 1]]:
            return False, {self.y: self.y + 1 - (-1)**self.x}
        elif m == [[0, 0, 0, 0], [1, 1, 1, 1], [1, 1, 1, 1], [0, 0, 0, 0]]:
            return True, {self.y: 2*self.y + (1 - (-1)**self.y)/2}
        elif m == [[1, 1, 0, 0], [1, 1, 0, 0], [0, 0, 1, 1], [0, 0, 1, 1]]:
            return False, {self.x: self.x + self.y}
        elif m == [[1, 1, 0, 0], [1, 0, 0, 1], [1, 1, 0, 0], [1, 0, 0, 1]]:
            return False, {self.x: self.x - (1 - (-1)**self.y) / 2}
        elif m == [[1, 1, 0, 0], [1, 1, 0, 0], [1, 1, 0, 0], [1, 1, 0, 0]]:
            return True, {self.x: 2*self.x - (1 - (-1)**self.x)/2 + 2}
        elif m == [[1, 1, 0, 0], [0, 0, 1, 1], [1, 1, 0, 0], [0, 0, 1, 1]]:
            return False, {self.x: self.x + 1 - (-1)**(self.y + 1)}
        else:
            raise "Invalid pattern"
