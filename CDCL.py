# This script implements a basic CDCL (Conflict-Driven Clause Learning) SAT solver.
# It takes as input a CNF formula in DIMACS format and tries to determine whether it's satisfiable (SAT) or unsatisfiable (UNSAT).

import sys
import random
from pprint import pprint
from dataclasses import dataclass
from typing import List, Set, Tuple, Optional, Iterator

# Represents a single literal, e.g., x or ¬x
@dataclass(frozen=True)
class Literal:
    variable: int
    negation: bool

    def __repr__(self):
        return '¬' + str(self.variable) if self.negation else str(self.variable)

    def neg(self) -> 'Literal':
        """Return the negation of this literal."""
        return Literal(self.variable, not self.negation)

# Represents a disjunction of literals (a single clause)
@dataclass
class Clause:
    literals: List[Literal]

    def __repr__(self):
        return ' ∨ '.join(map(str, self.literals))

    def __iter__(self) -> Iterator[Literal]:
        return iter(self.literals)

    def __len__(self):
        return len(self.literals)

# Represents a conjunction of clauses (the full formula)
@dataclass
class Formula:
    clauses: List[Clause]
    __variables: Set[int]

    def __init__(self, clauses: List[Clause]):
        """Initialize formula and remove duplicate literals from clauses."""
        self.clauses = []
        self.__variables = set()
        for clause in clauses:
            self.clauses.append(Clause(list(set(clause))))  # remove duplicate literals in a clause
            for lit in clause:
                self.__variables.add(lit.variable)

    def variables(self) -> Set[int]:
        """Return the set of variables contained in this formula."""
        return self.__variables

    def __repr__(self):
        return ' ∧ '.join(f'({clause})' for clause in self.clauses)

    def __iter__(self) -> Iterator[Clause]:
        return iter(self.clauses)

    def __len__(self):
        return len(self.clauses)

# Represents an assignment of a variable along with its decision level and the clause that led to it (if any)
@dataclass
class Assignment:
    value: bool
    antecedent: Optional[Clause]
    dl: int  # decision level

# Dictionary-like structure to store assignments with decision levels
class Assignments(dict):
    def __init__(self):
        super().__init__()
        self.dl = 0  # current decision level

    def value(self, literal: Literal) -> bool:
        """Evaluate the value of a literal given current assignments."""
        return not self[literal.variable].value if literal.negation else self[literal.variable].value

    def assign(self, variable: int, value: bool, antecedent: Optional[Clause]):
        """Assign a value to a variable with optional antecedent clause."""
        self[variable] = Assignment(value, antecedent, self.dl)

    def unassign(self, variable: int):
        self.pop(variable)

    def satisfy(self, formula: Formula) -> bool:
        """Check whether the current assignments satisfy the formula."""
        for clause in formula:
            if True not in [self.value(lit) for lit in clause]:
                return False
        return True

# Performs unit propagation: automatically assigns values to unit clauses
def unit_propagation(formula: Formula, assignments: Assignments) -> Tuple[str, Optional[Clause]]:
    finish = False
    while not finish:
        finish = True
        for clause in formula:
            status = clause_status(clause, assignments)
            if status in ('unresolved', 'satisfied'):
                continue
            elif status == 'unit':
                literal = next(lit for lit in clause if lit.variable not in assignments)
                var = literal.variable
                val = not literal.negation
                assignments.assign(var, val, antecedent=clause)
                finish = False
            else:
                # Clause is unsatisfied — conflict detected
                return ('conflict', clause)
    return ('unresolved', None)

# Determines the status of a clause under the current assignments
def clause_status(clause: Clause, assignments: Assignments) -> str:
    values = [assignments.value(lit) if lit.variable in assignments else None for lit in clause]
    if True in values:
        return 'satisfied'
    elif values.count(False) == len(values):
        return 'unsatisfied'
    elif values.count(False) == len(values) - 1:
        return 'unit'
    else:
        return 'unresolved'

# Resolves two clauses on a particular variable
def resolve(a: Clause, b: Clause, x: int) -> Clause:
    result = set(a.literals + b.literals) - {Literal(x, True), Literal(x, False)}
    return Clause(list(result))

# Analyzes a conflict and returns the backtrack level and the learned clause
def conflict_analysis(clause: Clause, assignments: Assignments) -> Tuple[int, Clause]:
    if assignments.dl == 0:
        return (-1, None)  # Cannot backtrack further

    literals = [lit for lit in clause if assignments[lit.variable].dl == assignments.dl]
    while len(literals) != 1:
        literals = filter(lambda lit: assignments[lit.variable].antecedent is not None, literals)
        literal = next(literals)
        antecedent = assignments[literal.variable].antecedent
        clause = resolve(clause, antecedent, literal.variable)
        literals = [lit for lit in clause if assignments[lit.variable].dl == assignments.dl]

    decision_levels = sorted(set(assignments[lit.variable].dl for lit in clause))
    return (0 if len(decision_levels) <= 1 else decision_levels[-2], clause)

# Unassign all variables with decision level higher than `b`
def backtrack(assignments: Assignments, b: int):
    to_remove = [var for var, assignment in assignments.items() if assignment.dl > b]
    for var in to_remove:
        assignments.pop(var)

# Check if all variables in the formula have been assigned
def all_variables_assigned(formula: Formula, assignments: Assignments) -> bool:
    return len(formula.variables()) == len(assignments)

# Randomly choose an unassigned variable and assign a random value
def pick_branching_variable(formula: Formula, assignments: Assignments) -> Tuple[int, bool]:
    unassigned_vars = [var for var in formula.variables() if var not in assignments]
    var = random.choice(unassigned_vars)
    val = random.choice([True, False])
    return (var, val)

# Add a newly learned clause to the formula
def add_learnt_clause(formula: Formula, clause: Clause):
    formula.clauses.append(clause)

# Main CDCL solving loop
def cdcl_solve(formula: Formula) -> Optional[Assignments]:
    assignments = Assignments()
    reason, clause = unit_propagation(formula, assignments)
    if reason == 'conflict':
        return None  # Formula is UNSAT

    while not all_variables_assigned(formula, assignments):
        var, val = pick_branching_variable(formula, assignments)
        assignments.dl += 1
        assignments.assign(var, val, antecedent=None)

        while True:
            reason, clause = unit_propagation(formula, assignments)
            if reason != 'conflict':
                break

            b, learnt_clause = conflict_analysis(clause, assignments)
            if b < 0:
                return None  # Backtrack impossible, UNSAT
            add_learnt_clause(formula, learnt_clause)
            backtrack(assignments, b)
            assignments.dl = b

    return assignments

# Parse a CNF formula from a string in DIMACS format
def parse_dimacs_cnf(content: str) -> Formula:
    clauses = []
    for line in content.splitlines():
        if len(line) == 0 or line[0] in ("c", "%"):  # Skip comments
            continue
        tokens = line.split()
        for tok in tokens:
            try:
                lit = int(tok)
                if lit == 0:
                    clauses.append(Clause([]))  # New clause
                else:
                    var = abs(lit)
                    neg = lit < 0
                    if not clauses or len(clauses[-1].literals) == 0:
                        clauses.append(Clause([Literal(var, neg)]))
                    else:
                        clauses[-1].literals.append(Literal(var, neg))
            except ValueError:
                continue
    return Formula(clauses)

# Main program entry point
if __name__ == '__main__':
    random.seed(5201314)  # Fixed seed for reproducibility
    if len(sys.argv) != 2:
        print('Provide one DIMACS cnf filename as argument.')
        sys.exit(1)

    dimacs_cnf = open(sys.argv[1]).read()
    formulas = parse_dimacs_cnf(dimacs_cnf)

    for i, formula in enumerate(formulas, 1):
        print(f"Solving formula {i}: {formula}")
        result = cdcl_solve(formula)
        if result:
            assert result.satisfy(formula)
            print(f"Formula {i} is SAT with assignments:")
            assignments = {var: assignment.value for var, assignment in result.items()}
            pprint(assignments)
        else:
            print(f"Formula {i} is UNSAT.")
