from z3 import *
from common import check_formulas, Solver_test_file


def is_bool_connective(f):
    return (is_and(f) or is_or(f) or is_not(f) or is_implies(f) or is_app_of(f, Z3_OP_XOR)
            or ((is_eq(f) or is_distinct(f)) and is_bool(f.arg(0)))
            or (is_app_of(f, Z3_OP_ITE) and is_bool(f)))


class DPLL_T_Solver:
    """
    Реализуйте DPLL(T) решатель. Вы можете только:
    - использовать готовый пропозициональный решатель `self.prop_solver`
    - создавать решатели теории при помощи конструктора `self.theory_solver`
    Другие решатели создавать и использовать запрещено.

    Решатель теории `T = self.theory_solver()` умеет:
    - `T.add(*literals)` — добавить литералы (атомы теории или их отрицания)
    - `T.check()` — вернуть `sat` или `unsat`
    - `T.unsat_core()` — после `unsat` вернуть обоснование: невыполнимое подмножество добавленных литералов

    Абстракция T2B и обратное отображение B2T уже написаны.
    """
    def __init__(self, prop_solver, theory_solver):
        self.prop_solver = prop_solver
        self.theory_solver = theory_solver
        self.atoms = {}  # номер атома теории -> (атом, булева переменная)

    def T2B(self, f):
        """Заменяет каждый атом теории в формуле `f` на соответствующую ему булеву переменную"""
        self._collect_atoms(f)
        pairs = list(self.atoms.values())
        return substitute(f, *pairs) if pairs else f

    def B2T(self, model):
        """Список литералов теории, которые истинны в модели `model` пропозиционального решателя"""
        return [atom if is_true(model.eval(p, model_completion=True)) else Not(atom)
                for atom, p in self.atoms.values()]

    def _collect_atoms(self, f):
        if is_bool_connective(f):
            for c in f.children():
                self._collect_atoms(c)
        elif not (is_true(f) or is_false(f)) and f.get_id() not in self.atoms:
            self.atoms[f.get_id()] = (f, FreshBool())

    def add(self, *fs):
        for f in fs:
            self.prop_solver.add(self.T2B(f))

    def check(self):
        while True:
            prop_result = self.prop_solver.check()
            if prop_result != sat:
                return prop_result

            model = self.prop_solver.model()
            theory = self.theory_solver()
            theory.add(*self.B2T(model))
            theory_result = theory.check()
            if theory_result == sat:
                return sat
            if theory_result != unsat:
                return theory_result

            blocking = []
            for literal in theory.unsat_core():
                atom = literal.arg(0) if is_not(literal) else literal
                variable = self.atoms[atom.get_id()][1]
                blocking.append(variable if is_not(literal) else Not(variable))
            if not blocking:
                return unsat
            self.prop_solver.add(Or(*blocking))


class TheorySolver:
    def __init__(self):
        self.solver = Solver()
        self.solver.set(unsat_core=True)
        self.ps = dict()

    def add(self, *args):
        for arg in args:
            assert not (is_and(arg) or is_or(arg)), f"Theory solver obtained {arg}, which is not a literal"
        for arg in args:
            p = FreshBool()
            self.solver.assert_and_track(arg, p)
            self.ps[p] = arg

    def check(self):
        return self.solver.check()

    def model(self):
        return self.solver.model()

    def unsat_core(self):
        core = self.solver.unsat_core()
        return [self.ps[v] for v in core]


def check_dpll_t(theory_solver, formulas, expected):
    check_formulas(lambda: DPLL_T_Solver(SolverFor("QF_FD"), theory_solver), formulas, expected)


def DPLL_T_Solver_test_lecture(theory_solver):
    x, y = Ints('x y')
    check_dpll_t(theory_solver, [x > 3, Or(x < 0, x < y), Or(y < 0, y <= x)], unsat)


def DPLL_T_Solver_test_sat(theory_solver):
    x, y = Ints('x y')
    check_dpll_t(theory_solver, [x > 3, Or(x < 0, x < y), Or(y < 0, y <= x, y == x + 5)], sat)
    check_dpll_t(theory_solver, [Or(x < 0, x > 10), Or(y < 0, y > 10), x + y == 5], sat)


def DPLL_T_Solver_test_bool(theory_solver):
    x = Int('x')
    b = Bool('b')
    check_dpll_t(theory_solver, [Or(b, x > 0), Implies(b, x < -5), x > -3, x < 1], unsat)
    check_dpll_t(theory_solver, [Or(b, x > 0), Implies(b, x < -5), x > -10, x < 1], sat)


def DPLL_T_Solver_test_combined(theory_solver):
    Z = IntSort()
    f = Function('f', Z, Z)
    x, y = Ints('x y')
    A = Array('A', Z, Z)
    check_dpll_t(theory_solver, [x + 2 == y, f(Store(A, x, 3)[y - 2]) != f(y - x + 1)], unsat)


def DPLL_T_Solver_tests():
    DPLL_T_Solver_test_lecture(TheorySolver)
    DPLL_T_Solver_test_sat(TheorySolver)
    DPLL_T_Solver_test_bool(TheorySolver)
    DPLL_T_Solver_test_combined(TheorySolver)
    for n in range(2, 6):
        Solver_test_file(lambda: DPLL_T_Solver(SolverFor("QF_FD"), TheorySolver), list,
                         f"QF_UF/eq_diamond/eq_diamond{n}.smt2")


if __name__ == "__main__":
    DPLL_T_Solver_tests()
    print("OK")
