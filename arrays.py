from itertools import count

from z3 import *
from common import check_formulas, Solver_test_files


def array_to_euf(formulas):
    """
    Устраняет массивы из формул: `select` от `store` раскрывается через `If`, а выборка
    из базового массива заменяется применением свежей неинтерпретированной функции.
    """
    select_functions = {}  # номер терма-массива -> функция выбора
    array_constants = {}   # номер терма-массива -> свежая константа
    memo = {}
    counter = count()

    def select_function(array):
        key = array.get_id()
        if key not in select_functions:
            sort = array.sort()
            name = f"__select_{next(counter)}"
            select_functions[key] = Function(name, sort.domain(), sort.range())
        return select_functions[key]

    def array_constant(array):
        key = array.get_id()
        if key not in array_constants:
            array_constants[key] = FreshConst(array.sort(), "__array")
        return array_constants[key]

    def read(array, index):
        """Значение `select(array, index)` с учётом аксиом read-over-write"""
        if is_store(array):
            return If(index == go(array.arg(1)),
                      go(array.arg(2)),
                      read(array.arg(0), index))
        if is_app_of(array, Z3_OP_ITE) and is_array(array):
            return If(go(array.arg(0)),
                      read(array.arg(1), index),
                      read(array.arg(2), index))
        base = go(array)
        return select_function(base)(index)

    def go(term):
        key = term.get_id()
        if key in memo:
            return memo[key]

        if is_select(term):
            result = read(term.arg(0), go(term.arg(1)))
        elif is_app(term) and term.num_args() > 0:
            result = term.decl()(*[go(c) for c in term.children()])
        else:
            result = term

        if is_array(result):
            result = array_constant(result)

        memo[key] = result
        return result

    return [go(formula) for formula in formulas]


def rewrite(e, f):
    """Применяет `f` ко всем подтермам `e` снизу вверх: сначала к аргументам, затем к терму с уже переписанными аргументами"""
    memo = {}

    def go(t):
        if t.get_id() not in memo:
            if is_app(t) and t.num_args() > 0:
                memo[t.get_id()] = f(t.decl()(*[go(c) for c in t.children()]))
            else:
                memo[t.get_id()] = f(t)
        return memo[t.get_id()]

    return go(e)


def subterms(formulas):
    seen, result = set(), []

    def go(t):
        if t.get_id() not in seen:
            seen.add(t.get_id())
            result.append(t)
            for c in t.children():
                go(c)

    for f in formulas:
        go(f)
    return result


class ArrayToEufSolver:
    def __init__(self):
        self.formulas = []

    def add(self, *formulas):
        self.formulas += formulas

    def check(self):
        result = list(array_to_euf(self.formulas))
        arrays = [t for t in subterms(result) if is_array(t)]
        assert not arrays, f"В результате остались массивы: {arrays[0]}"
        solver = Solver()
        solver.add(result)
        return solver.check()


def array_to_euf_test_lecture():
    S = DeclareSort('S')
    A = Array('A', S, S)
    x, y, z, v, w, x1, x2, v1, v2 = Consts('x y z v w x1 x2 v1 v2', S)
    check_formulas(ArrayToEufSolver, [x == y, x != z, Select(Store(Store(A, x, v), z, w), y) != v], unsat)
    check_formulas(ArrayToEufSolver, [Select(A, x) == Select(A, y), x != y], sat)
    check_formulas(ArrayToEufSolver, [A[A[A[x]]] == x, A[A[A[A[A[x]]]]] == x, A[x] != x], unsat)
    check_formulas(ArrayToEufSolver, [x1 == y, x1 != x2, Select(A, y) == v1,
                                      Select(Store(Store(A, x1, v1), x2, v2), y) != Select(A, y)], unsat)


def array_to_euf_test_bool():
    S = DeclareSort('S')
    A = Array('A', S, S)
    x, y, v, w = Consts('x y v w', S)
    check_formulas(ArrayToEufSolver, [Implies(Select(Store(A, x, v), y) == v, x == y), Select(A, y) == v, x != y], unsat)
    check_formulas(ArrayToEufSolver, [Or(Select(Store(A, x, v), y) != v, x != y), x == y], unsat)
    check_formulas(ArrayToEufSolver, [Or(Select(Store(A, x, w), y) == v, x == y), Select(A, y) == v], sat)


def array_to_euf_tests():
    array_to_euf_test_lecture()
    array_to_euf_test_bool()
    Solver_test_files(ArrayToEufSolver, list, "QF_AX")


if __name__ == "__main__":
    array_to_euf_tests()
    print("OK")
