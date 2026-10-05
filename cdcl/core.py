"""CDCL SAT solver core (standard library only).

A CNF formula is a list of clauses and a clause is a list of nonzero
integers.  The literal x means that variable x is true, the literal -x means
that variable x is false.  Variables are numbered from 1 upwards.

The solver keeps the usual CDCL machinery:

* two watched literals per clause and unit propagation over the trail,
* first-UIP conflict analysis,
* non-chronological backtracking to the assertion level,
* phase saving for the branching heuristic,
* restarts with a growing conflict threshold,
* periodic simplification of the clause database.
"""

SAT = "SAT"
UNSAT = "UNSAT"
UNKNOWN = "UNKNOWN"

LIT_UNDEF = 0
LIT_TRUE = 1
LIT_FALSE = -1


class Clause:
    """A clause.  The two watched literals are kept at index 0 and index 1."""

    __slots__ = ("lits",)

    def __init__(self, lits):
        self.lits = list(lits)

    def __len__(self):
        return len(self.lits)

    def __repr__(self):
        return "Clause(%s)" % (", ".join(str(lit) for lit in self.lits),)


class Solver:
    """A CDCL SAT solver."""

    def __init__(self, num_vars=0, max_conflicts=20000):
        self.num_vars = num_vars
        self.max_conflicts = max_conflicts

        self.clauses = []
        self.watches = {}
        self.assign = {}
        self.level = {}
        self.reason = {}
        self.phase = {}
        self.activity = {}
        self.trail = []
        self.trail_lim = []
        self.qhead = 0

        self.ok = True
        self.conflicts = 0
        self.conflicts_since_restart = 0
        self.restart_limit = 8
        self.simplify_limit = 6
        self.var_inc = 1.0
        self.var_decay = 0.95

    # ------------------------------------------------------------------
    # trail and assignment
    # ------------------------------------------------------------------
    def decision_level(self):
        """Number of decisions made so far."""
        return len(self.trail_lim)

    def new_decision_level(self):
        self.trail_lim.append(len(self.trail))

    def lit_value(self, lit):
        """LIT_TRUE, LIT_FALSE or LIT_UNDEF for the given literal."""
        value = self.assign.get(abs(lit), 0)
        if value == 0:
            return LIT_UNDEF
        return LIT_TRUE if (value > 0) == (lit > 0) else LIT_FALSE

    def all_variables_assigned(self):
        return len(self.assign) >= self.num_vars

    def enqueue(self, lit, reason=None):
        """Assign lit to true.  Returns False if this contradicts the trail."""
        var = abs(lit)
        value = LIT_TRUE if lit > 0 else LIT_FALSE
        current = self.assign.get(var, 0)
        if current == value:
            return True
        self.assign[var] = value
        self.level[var] = self.decision_level()
        self.reason[var] = reason
        self.phase[var] = value
        self.trail.append(lit)
        return True

    def cancel_until(self, level):
        """Undo every assignment made above the given decision level."""
        if self.decision_level() <= level:
            return
        boundary = self.trail_lim[level]
        while len(self.trail) > boundary:
            lit = self.trail.pop()
            var = abs(lit)
            del self.assign[var]
            del self.level[var]
            self.reason.pop(var, None)
        del self.trail_lim[level:]
        self.qhead = len(self.trail)

    # ------------------------------------------------------------------
    # clause database
    # ------------------------------------------------------------------
    def add_clause(self, lits):
        """Add a clause to the formula under construction."""
        clause = []
        for lit in lits:
            if not isinstance(lit, int):
                raise TypeError("literal must be an integer, got %r" % (lit,))
            if lit == 0:
                raise ValueError("literal 0 is not a valid literal")
            var = abs(lit)
            if var > self.num_vars:
                self.num_vars = var
            self.activity.setdefault(var, 0.0)
            clause.append(lit)
        if not clause:
            return
        if len(clause) == 1:
            if not self.enqueue(clause[0], None):
                self.ok = False
            self.qhead = len(self.trail)
            return
        new_clause = Clause(clause)
        self.clauses.append(new_clause)
        self.attach_clause(new_clause)

    def attach_clause(self, clause):
        """Watch the two literals stored at index 0 and index 1."""
        self.watches.setdefault(clause.lits[0], []).append(clause)
        self.watches.setdefault(clause.lits[1], []).append(clause)

    def detach_clause(self, clause):
        """Stop watching a clause."""
        for lit in (clause.lits[0], clause.lits[1]):
            watchers = self.watches.get(lit)
            if not watchers:
                continue
            for index, watched in enumerate(watchers):
                if watched is clause:
                    watchers.pop(index)
                    break

    # ------------------------------------------------------------------
    # propagation
    # ------------------------------------------------------------------
    def propagate(self):
        """Propagate all pending assignments.

        Returns the clause that became falsified, or None.
        """
        while self.qhead < len(self.trail):
            lit = self.trail[self.qhead]
            self.qhead += 1
            false_lit = -lit
            watchers = self.watches.setdefault(false_lit, [])
            index = 0
            while index < len(watchers):
                clause = watchers[index]
                index += 1
                lits = clause.lits
                if lits[0] == false_lit:
                    lits[0], lits[1] = lits[1], false_lit
                elif lits[1] != false_lit:
                    watchers.pop(index - 1)
                    index -= 1
                    continue
                if self.lit_value(lits[0]) == LIT_TRUE:
                    continue
                moved = False
                for other in range(2, len(lits)):
                    if self.lit_value(lits[other]) != LIT_FALSE:
                        lits[1], lits[other] = lits[other], false_lit
                        self.watches[false_lit].append(clause)
                        watchers.pop(index - 1)
                        index -= 1
                        moved = True
                        break
                if moved:
                    continue
                if self.lit_value(lits[0]) == LIT_FALSE:
                    return clause
                if not self.enqueue(lits[0], clause):
                    return clause
        return None

    # ------------------------------------------------------------------
    # conflict analysis
    # ------------------------------------------------------------------
    def analyze(self, conflict):
        """First-UIP conflict analysis.

        Returns the learned clause, whose first literal is the asserting
        literal, together with the level to backjump to.
        """
        learnt = [None]
        seen = set()
        counter = 0
        index = len(self.trail) - 1
        clause = conflict
        resolved = None
        while True:
            for lit in clause.lits:
                if resolved is not None and abs(lit) == abs(resolved):
                    continue
                var = abs(lit)
                if var in seen:
                    continue
                level = self.level.get(var, 0)
                if level == 0:
                    continue
                seen.add(var)
                self.bump_activity(var)
                if level == self.decision_level():
                    counter += 1
                else:
                    learnt.append(lit)
            while index >= 0 and abs(self.trail[index]) not in seen:
                index -= 1
            if index < 0:
                raise RuntimeError("conflict analysis: nothing left to resolve")
            resolved = self.trail[index]
            index -= 1
            seen.discard(abs(resolved))
            counter -= 1
            if counter == 0:
                break
            reason = self.reason.get(abs(resolved))
            if reason is None:
                raise RuntimeError("conflict analysis: reached a decision")
            clause = reason
        learnt[0] = resolved
        return learnt, self.backtrack_level(learnt)

    def backtrack_level(self, learnt):
        """Level to return to after learning the clause."""
        if len(learnt) == 1:
            return 0
        return max(self.level[abs(lit)] for lit in learnt)

    def bump_activity(self, var):
        self.activity[var] = self.activity.get(var, 0.0) + self.var_inc

    # ------------------------------------------------------------------
    # heuristics
    # ------------------------------------------------------------------
    def pick_branch_lit(self):
        """Literal of the unassigned variable with the highest activity."""
        best = None
        best_activity = -1.0
        for var in range(1, self.num_vars + 1):
            if var in self.assign:
                continue
            activity = self.activity.get(var, 0.0)
            if activity > best_activity:
                best_activity = activity
                best = var
        if best is None:
            raise RuntimeError("no unassigned variable left")
        return best if self.phase.get(best, LIT_TRUE) > 0 else -best

    def should_simplify(self):
        return self.conflicts >= self.simplify_limit

    def should_restart(self):
        return self.conflicts_since_restart >= self.restart_limit

    def restart(self):
        """Drop every decision and continue from level 0."""
        self.cancel_until(0)
        self.conflicts_since_restart = 0
        self.restart_limit = self.restart_limit * 3 // 2 + 4

    def simplify(self):
        """Drop the clauses that can never be used again."""
        kept = []
        for clause in self.clauses:
            if self.satisfied_clause(clause):
                self.detach_clause(clause)
                continue
            kept.append(clause)
        self.clauses = kept

    def satisfied_clause(self, clause):
        """True when the clause is satisfied by the current assignment."""
        for lit in clause.lits:
            if self.lit_value(lit) == LIT_TRUE:
                return True
        return False

    # ------------------------------------------------------------------
    # search
    # ------------------------------------------------------------------
    def solve(self):
        """Search for a model.

        Returns SAT, UNSAT, or UNKNOWN when the conflict budget ran out.
        """
        if not self.ok:
            return UNSAT
        while True:
            if self.all_variables_assigned():
                return SAT
            conflict = self.propagate()
            if conflict is None:
                self.new_decision_level()
                self.enqueue(self.pick_branch_lit(), None)
                continue
            if self.decision_level() == 0:
                return UNSAT
            self.conflicts += 1
            self.conflicts_since_restart += 1
            self.var_inc /= self.var_decay
            if self.conflicts >= self.max_conflicts:
                return UNKNOWN
            if self.should_simplify():
                self.simplify()
                self.simplify_limit += 16
            learnt, level = self.analyze(conflict)
            self.cancel_until(level)
            if len(learnt) == 1:
                if not self.enqueue(learnt[0], None):
                    return UNSAT
            else:
                clause = Clause(learnt)
                self.clauses.append(clause)
                self.attach_clause(clause)
                if not self.enqueue(learnt[0], clause):
                    return UNSAT
            if self.should_restart():
                self.restart()

    def model(self):
        """The assignment found by the last solve() call, as var -> bool."""
        return {var: self.assign[var] > 0 for var in range(1, self.num_vars + 1)}


def solve_cnf(clauses, num_vars=0, max_conflicts=20000):
    """Solve a CNF formula given as a list of clauses.

    Returns (status, model); the model is None unless the status is SAT.
    """
    solver = Solver(num_vars=num_vars, max_conflicts=max_conflicts)
    for clause in clauses:
        solver.add_clause(clause)
    status = solver.solve()
    return status, (solver.model() if status == SAT else None)
