from os import sync
import sympy
from sympy.core import symbol
from sympy.core.numbers import Integer
from sympy.testing.runtests import SymPyTestResults
from typing import Tuple


def genMatrix(x: sympy.Symbol, y: sympy.Symbol, f: sympy.Add, m: int) -> list[list[Integer]]:
	return [[sympy.Mod(f, m).subs({x: i, y: j}) for i in range(4)] for j in range(4)]


def matrixPrint(m: list[list[Integer]]):
	[print(row) for row in m]


def kernel_matcher(
	x: sympy.Symbol,
	y: sympy.Symbol,
	m: list[list[Integer]]
) -> Tuple[bool, dict[sympy.Symbol, sympy.Add]]:
	if m == [[1, 1, 1, 1], [1, 0, 1, 0], [1, 1, 1, 1], [1, 0, 1, 0]]:
		return True, {x: 2*x + 1, y: 2*y + 1}
	elif m == [[1, 0, 1, 0], [0, 1, 0, 1], [1, 0, 1, 0], [0, 1, 0, 1]]:
		return False, {x: x + (1 - (-1)**y) / 2}
	elif m == [[1, 0, 1, 0], [1, 0, 1, 0], [1, 0, 1, 0], [1, 0, 1, 0]]:
		return True, {x: 2*x + 1}
	elif m == [[0, 1, 0, 1], [1, 0, 1, 0], [1, 0, 1, 0], [0, 1, 0, 1]]:
		return False, {y: y + 1 - (-1)**x}
	else:
		raise "Invalid pattern"


def core_substitution(
	x: sympy.Symbol,
	y: sympy.Symbol,
	f: sympy.Add
) -> sympy.Add:
	return (
		f
		.expand()
		.subs((-1)**(2*y), 1)
		.subs((-1)**(2*x), 1)
		.subs((-1)**((-1)**x), -1)
		.subs((-1)**((-1)**y), -1)
	)


def process_function(
	x: sympy.Symbol,
	y: sympy.Symbol,
	f: sympy.Add
) -> Tuple[sympy.Add, list[list[Integer]]]:
	sympy.pprint(f)
	m = genMatrix(x, y, f, 2)
	matrixPrint(m)

	do_division, sub_expression = kernel_matcher(x, y, m)

	f = core_substitution(x, y, f.subs(sub_expression))
	if do_division is True:
		f /= 2

	return f, m


if __name__ == "__main__":
	N = 91
	x, y = sympy.symbols('x y')
	f: sympy.Add = x*y - N

	for i in range(4):
		print('==============================')
		f, m = process_function(x, y, f)

	print('==============================')
	sympy.pprint(f)
	print("\n")
	m = genMatrix(x, y, f, 2)
	matrixPrint(m)
	print("\n")
	sympy.print_maple_code(f)
	print("\n")
	print(type(f))
	print(type(m))
	print('==============================')
