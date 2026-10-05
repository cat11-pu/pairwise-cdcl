"""Acceptance tests for the cdcl solver core.

Run them from the project root with:

    python3 -m unittest discover -s tests -v
"""

import itertools
import unittest

from cdcl import SAT, UNSAT, Solver, solve_cnf


def vars_of(clauses):
    """Highest variable number used by the formula."""
    highest = 0
    for clause in clauses:
        for lit in clause:
            highest = max(highest, abs(lit))
    return highest


def model_satisfies(clauses, model):
    """True when every clause has at least one literal that is true."""
    for clause in clauses:
        if not any((lit > 0) == model[abs(lit)] for lit in clause):
            return False
    return True


def brute_force(clauses):
    """Enumerate the whole assignment space.  Returns a model or None."""
    num_vars = vars_of(clauses)
    for bits in itertools.product((False, True), repeat=num_vars):
        model = {var + 1: bits[var] for var in range(num_vars)}
        if model_satisfies(clauses, model):
            return model
    return None


def pigeonhole(pigeons, holes):
    """CNF of the pigeonhole principle; pigeon p sits in hole h iff (p-1)*holes+h."""
    clauses = []
    for pigeon in range(1, pigeons + 1):
        clauses.append([(pigeon - 1) * holes + hole for hole in range(1, holes + 1)])
    for hole in range(1, holes + 1):
        for first in range(1, pigeons + 1):
            for second in range(first + 1, pigeons + 1):
                clauses.append([-((first - 1) * holes + hole), -((second - 1) * holes + hole)])
    return clauses


class SatisfiableTest(unittest.TestCase):
    def test_unique_model_is_reported(self):
        clauses = [[1, 2], [-1, 2], [1, -2]]
        status, model = solve_cnf(clauses)
        self.assertEqual(status, SAT)
        self.assertIsNotNone(model)
        self.assertEqual(sorted(model), [1, 2])
        self.assertTrue(model_satisfies(clauses, model))
        self.assertEqual(model, {1: True, 2: True})

    def test_unit_chain_forces_all_variables(self):
        clauses = [[1], [-1, 2], [-2, 3], [-3, 4]]
        status, model = solve_cnf(clauses)
        self.assertEqual(status, SAT)
        self.assertTrue(model_satisfies(clauses, model))
        self.assertEqual(model, {1: True, 2: True, 3: True, 4: True})

    def test_duplicate_literals_keep_the_semantics(self):
        clauses = [[1, 1], [-1, 2, 2], [-2, -2, 3]]
        status, model = solve_cnf(clauses)
        self.assertEqual(status, SAT)
        self.assertTrue(model_satisfies(clauses, model))
        self.assertEqual(model, {1: True, 2: True, 3: True})

    def test_verdict_and_model_agree_with_enumeration(self):
        formulas = [
            [[1, 2], [2, 3], [-1, -3]],
            [[1, 2], [1, -2], [-1, 2]],
            [[1, 2, 3], [-1, 2], [-2, 3], [-3, 1]],
            [[1], [2], [-1, -2]],
            [[-1, 2], [1, -2], [-1, -2], [1, 2]],
            [[-3, 4, 1], [-2, -3], [-2, 4], [2, 3, 1], [-1, -4, -2]],
            [[5, 4, -2], [5, 1, 4], [-1, -5, 2], [3, -2, -4], [-2, -5, 4], [-2, -4, -1]],
        ]
        for clauses in formulas:
            expected = brute_force(clauses)
            status, model = solve_cnf(clauses)
            if expected is None:
                self.assertEqual(status, UNSAT, "wrong verdict for %r" % (clauses,))
            else:
                self.assertEqual(status, SAT, "wrong verdict for %r" % (clauses,))
                self.assertTrue(
                    model_satisfies(clauses, model),
                    "model %r violates %r" % (model, clauses),
                )


class UnsatisfiableTest(unittest.TestCase):
    def test_contradictory_units(self):
        clauses = [[1], [-1]]
        status, model = solve_cnf(clauses)
        self.assertEqual(status, UNSAT)
        self.assertIsNone(model)
        self.assertIsNone(brute_force(clauses))

    def test_empty_clause_is_unsatisfiable(self):
        self.assertEqual(solve_cnf([[]])[0], UNSAT)
        self.assertEqual(solve_cnf([[1, 2], []])[0], UNSAT)
        solver = Solver()
        solver.add_clause([1])
        solver.add_clause([])
        self.assertEqual(solver.solve(), UNSAT)

    def test_all_combinations_blocked(self):
        clauses = [[1, 2], [1, -2], [-1, 2], [-1, -2]]
        status, _ = solve_cnf(clauses)
        self.assertEqual(status, UNSAT)
        self.assertIsNone(brute_force(clauses))
        relaxed = [[1, 2], [1, -2], [-1, 2]]
        status, model = solve_cnf(relaxed)
        self.assertEqual(status, SAT)
        self.assertTrue(model_satisfies(relaxed, model))

    def test_pigeonhole_three_into_two(self):
        three_into_two = pigeonhole(3, 2)
        self.assertEqual(solve_cnf(three_into_two)[0], UNSAT)
        self.assertIsNone(brute_force(three_into_two))
        four_into_three = pigeonhole(4, 3)
        self.assertEqual(solve_cnf(four_into_three)[0], UNSAT)
        self.assertIsNone(brute_force(four_into_three))
        two_into_two = pigeonhole(2, 2)
        status, model = solve_cnf(two_into_two)
        self.assertEqual(status, SAT)
        self.assertTrue(model_satisfies(two_into_two, model))


class InputValidationTest(unittest.TestCase):
    def test_invalid_literals_are_rejected(self):
        solver = Solver()
        with self.assertRaises(ValueError):
            solver.add_clause([0])
        with self.assertRaises(ValueError):
            solver.add_clause([1, 0, 2])
        with self.assertRaises(TypeError):
            solver.add_clause([1.5])
        with self.assertRaises(TypeError):
            solver.add_clause(["1"])
        solver.add_clause([1])
        solver.add_clause([-1, 2])
        solver.add_clause([-2])
        self.assertEqual(solver.solve(), UNSAT)


if __name__ == "__main__":
    unittest.main()
