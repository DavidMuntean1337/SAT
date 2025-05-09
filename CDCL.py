import sys
import random
from pprint import pprint
from dataclasses import dataclass
from typing import List, Set, Tuple, Optional, Iterator

@dataclass(frozen=True)
class Literal:
    variable: int
    negation: bool

    def __repr__(self):
        if self.negation:
            return '¬' + str(self.variable)
        else:
            return str(self.variable)

    def neg(self) -> 'Literal':
        """Return the negation of this literal."""
        return Literal(self.variable, not self.negation)

@dataclass
class Clause:
    literals: List[Literal]

    def __repr__(self):
        return ' ∨ '.join(map(str, self.literals))

    def __iter__(self) -> Iterator[Literal]:
        return iter(self.literals)

    def __len__(self):
        return len(self.literals)

@dataclass
class Formula:
    clauses: List[Clause]
    __variables: Set[int]

    def __init__(self, clauses: List[Clause]):
        """Remove duplicate literals in clauses."""
        self.clauses = []
        self.__variables = set()
        for clause in clauses:
            self.clauses.append(Clause(list(set(clause))))
            for lit in clause:
                var = lit.variable
                self.__variables.add(var)

    def variables(self) -> Set[int]:
        """Return the set of variables contained in this formula."""
        return self.__variables

    def __repr__(self):
        return ' ∧ '.join(f'({clause})' for clause in self.clauses)

    def __iter__(self) -> Iterator[Clause]:
        return iter(self.clauses)

    def __len__(self):
        return len(self.clauses)

@dataclass
class Assignment:
    value: bool
    antecedent: Optional[Clause]
    dl: int  # decision level

class Assignments(dict):
    """Stores the current assignments of variables and their decision level."""
    def __init__(self):
        super().__init__()
        self.dl = 0

    def value(self, literal: Literal) -> bool:
        """Return the value of the literal with respect to the current assignments."""
        if literal.negation:
            return not self[literal.variable].value
        else:
            return self[literal.variable].value

    def assign(self, variable: int, value: bool, antecedent: Optional[Clause]):
        self[variable] = Assignment(value, antecedent, self.dl)

    def unassign(self, variable: int):
        self.pop(variable)

    def satisfy(self, formula: Formula) -> bool:
        """Check whether the assignments actually satisfy the formula."""
        for clause in formula:
            if True not in [self.value(lit) for lit in clause]:
                return False
        return True

def unit_propagation(formula: Formula, assignments: Assignments) -> Tuple[str, Optional[Clause]]:
    finish = False
    while not finish:
        finish = True
        for clause in formula:
            status = clause_status(clause, assignments)
            if status == 'unresolved' or status == 'satisfied':
                continue
            elif status == 'unit':
                literal = next(literal for literal in clause if literal.variable not in assignments)
                var = literal.variable
                val = not literal.negation
                assignments.assign(var, val, antecedent=clause)
                finish = False
            else:
                return ('conflict', clause)
    return ('unresolved', None)

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

def resolve(a: Clause, b: Clause, x: int) -> Clause:
    result = set(a.literals + b.literals) - {Literal(x, True), Literal(x, False)}
    result = list(result)
    return Clause(result)

def conflict_analysis(clause: Clause, assignments: Assignments) -> Tuple[int, Clause]:
    if assignments.dl == 0:
        return (-1, None)
    literals = [literal for literal in clause if assignments[literal.variable].dl == assignments.dl]
    while len(literals) != 1:
        literals = filter(lambda lit: assignments[lit.variable].antecedent is not None, literals)
        literal = next(literals)
        antecedent = assignments[literal.variable].antecedent
        clause = resolve(clause, antecedent, literal.variable)
        literals = [literal for literal in clause if assignments[literal.variable].dl == assignments.dl]
    decision_levels = sorted(set(assignments[literal.variable].dl for literal in clause))
    if len(decision_levels) <= 1:
        return 0, clause
    else:
        return decision_levels[-2], clause

def backtrack(assignments: Assignments, b: int):
    to_remove = [var for var, assignment in assignments.items() if assignment.dl > b]
    for var in to_remove:
        assignments.pop(var)

def all_variables_assigned(formula: Formula, assignments: Assignments) -> bool:
    return len(formula.variables()) == len(assignments)

def pick_branching_variable(formula: Formula, assignments: Assignments) -> Tuple[int, bool]:
    unassigned_vars = [var for var in formula.variables() if var not in assignments]
    var = random.choice(unassigned_vars)
    val = random.choice([True, False])
    return (var, val)

def add_learnt_clause(formula: Formula, clause: Clause):
    formula.clauses.append(clause)

def cdcl_solve(formula: Formula) -> Optional[Assignments]:
    assignments = Assignments()
    reason, clause = unit_propagation(formula, assignments)
    if reason == 'conflict':
        return None

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
                return None
            add_learnt_clause(formula, learnt_clause)
            backtrack(assignments, b)
            assignments.dl = b

    return assignments

def parse_dimacs_cnf(content: str) -> Formula:
    clauses = []
    for line in content.splitlines():
        # Skip comments and empty lines
        if len(line) == 0 or line[0] in ("c", "%"):
            continue
        tokens = line.split()
        for tok in tokens:
            try:
                lit = int(tok)
                if lit == 0:
                    # Start a new clause when we encounter '0'
                    clauses.append(Clause([]))
                else:
                    var = abs(lit)
                    neg = lit < 0
                    if not clauses or len(clauses[-1].literals) == 0:
                        clauses.append(Clause([Literal(var, neg)]))
                    else:
                        clauses[-1].literals.append(Literal(var, neg))
            except ValueError:
                # Ignore any non-integer tokens (such as comments)
                continue

    return Formula(clauses)

if __name__ == '__main__':
    random.seed(5201314)
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
