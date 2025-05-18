def dpll(clauses, assignment={}):
    # Inner function: Applies unit propagation (simplifies the formula when there's a unit clause)
    def unit_propagate(clauses, assignment):
        changed = True
        while changed:
            changed = False
            for clause in clauses:
                if len(clause) == 1:  # Found a unit clause
                    lit = clause[0]
                    var = abs(lit)
                    val = lit > 0
                    if var in assignment:
                        if assignment[var] != val:
                            return None, None  # Conflict detected
                    else:
                        assignment[var] = val
                        clauses = simplify(clauses, var, val)
                        changed = True
                    break
        return clauses, assignment

    # Inner function: Simplifies the formula by removing satisfied clauses and false literals
    def simplify(clauses, var, val):
        new_clauses = []
        for clause in clauses:
            # If the clause is already satisfied, skip it
            if (val and var in clause) or (not val and -var in clause):
                continue
            # Remove the negated literal from the clause
            new_clause = [l for l in clause if l != var and l != -var]
            if new_clause:
                new_clauses.append(new_clause)
        return new_clauses

    # Step 1: Apply unit propagation
    clauses, assignment = unit_propagate(clauses, assignment.copy())
    if clauses is None:  # Conflict encountered
        return False
    if not clauses:  # All clauses satisfied
        return True

    # Step 2: Choose an unassigned variable and recurse
    for clause in clauses:
        for literal in clause:
            var = abs(literal)
            if var not in assignment:
                for val in [True, False]:
                    new_assignment = assignment.copy()
                    new_assignment[var] = val
                    simplified_clauses = simplify(clauses, var, val)
                    if dpll(simplified_clauses, new_assignment):
                        return True
                return False
    return True  # Should never get here under normal CNF input

# Parses a CNF formula in DIMACS format
def parse_dimacs_cnf(content: str):
    clauses = []
    for line in content.splitlines():
        if len(line) == 0 or line[0] in ("c", "%"):  # Skip comments
            continue
        tokens = line.split()
        clause = []
        for tok in tokens:
            try:
                lit = int(tok)
                if lit == 0:
                    clauses.append(clause)  # End of clause
                    clause = []
                else:
                    clause.append(lit)
            except ValueError:
                continue  # Ignore invalid tokens
    if clause:
        clauses.append(clause)  # Append last clause if not closed by 0
    return clauses

# Main block: reads a CNF file and runs the DPLL SAT solver
if __name__ == "__main__":
    # Open and read the DIMACS CNF file
    with open("file.cnf", "r") as file:
        dimacs_cnf = file.read()

    # Parse the CNF into clause list
    clauses = parse_dimacs_cnf(dimacs_cnf)

    print("🔹 DPLL")
    result = dpll(clauses)
    print(f"The formula is: {'SATISFIABLE' if result else 'UNSATISFIABLE'}")
