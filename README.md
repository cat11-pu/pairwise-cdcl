# pairwise-cdcl

A small CDCL SAT solver core written with the Python standard library only.
There is nothing to install and no third party dependency.

A CNF formula is a list of clauses and a clause is a list of nonzero integers.
The literal x means that variable x is true, the literal -x means that variable
x is false, variables are numbered from 1 upwards.

## What is inside

* `cdcl/core.py` - the solver: two watched literals per clause with unit
  propagation over the trail, first-UIP conflict analysis, non-chronological
  backtracking to the assertion level, phase saving for the branching
  heuristic, restarts with a growing conflict threshold and periodic
  simplification of the clause database.
* `tests/test_core.py` - the acceptance tests for the solver.

## Public interface

```python
from cdcl import SAT, UNSAT, Solver, solve_cnf

status, model = solve_cnf([[1, 2], [-1, 2]])    # SAT / UNSAT, model or None
```

* `Solver(num_vars=0, max_conflicts=20000)` with `add_clause(clause)`,
  `solve()` and `model()`.
* `solve()` returns `SAT`, `UNSAT`, or `UNKNOWN` when the conflict budget given
  by `max_conflicts` ran out.
* `model()` maps every variable of the formula to a bool.
* A clause that is a bad literal is rejected: `ValueError` for the literal 0,
  `TypeError` for anything that is not an integer.

## Running the tests

From the project root:

    python3 -m unittest discover -s tests -v

All of the tests have to pass.
