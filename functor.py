import sympy
from sympy.core.add import Add
from sympy.core.numbers import Integer
from typing import Tuple

from sympy.core.symbol import Symbol


def sep_print():
    print('='*40)


def matrix_print(m: list[list[Integer]]):
    print("\n")
    for row in m:
        print(row)
    print("\n")


class Functor:
	x: Symbol
	y: Symbol
	f: Add

	def __init__(self, z) -> None:
		self.x, self.y = sympy.symbols('x y')
		if type(z) == int:
			self.f = self.x * self.y - z
		else:
			self.f = z

	def gen_matrix(self) -> list[list[Integer]]:
		return [[sympy.Mod(self.f, 2).subs({self.x: i, self.y: j}) for i in range(4)] for j in range(4)]

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
		else:
			raise "Invalid pattern"

	def smooth(self) -> Add:
		return (self.f
				.expand()
				.subs((-1)**(2*self.y), 1)
				.subs((-1)**(2*self.x), 1)
				.subs((-1)**((-1)**self.x), -1)
				.subs((-1)**((-1)**self.y), -1))

	def lift(self) -> Add:
		sep_print()
		sympy.pprint(self.f)
		m = self.gen_matrix()
		matrix_print(m)

		do_division, sub_expression = self.matcher(m)

		f = Functor(self.f.subs(sub_expression)).smooth()
		if do_division is True:
			f /= 2

		return f

	def finalize(self):
		sep_print()
		sympy.pprint(self.f)
		matrix_print(self.gen_matrix())
		sympy.print_maple_code(self.f)
		sep_print()
