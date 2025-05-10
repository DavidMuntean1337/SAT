from itertools import combinations

# Reprezentare clauză: set de intregi. e: {1, -2} == (A ∨ ¬B)

def resolve(ci, cj):
    resolvents = []
    for lit in ci:
        if -lit in cj:
            new_clause = (ci | cj) - {lit, -lit}
            resolvents.append(frozenset(new_clause))
    return resolvents

def pl_resolution(clauses):
    clauses = set(frozenset(c) for c in clauses)
    new = set()
    while True:
        pairs = combinations(clauses, 2)
        for (ci, cj) in pairs:
            resolvents = resolve(ci, cj)
            for r in resolvents:
                if not r:
                    return True  # Empty clause => satisfiable
                new.add(r)
        if new.issubset(clauses):
            return False  # No progress => not satisfiable
        clauses.update(new)

def parse_dimacs_cnf(content: str):
    clauses = []
    for line in content.splitlines():
        # Skip comments and empty lines
        if len(line) == 0 or line[0] in ("c", "%"):
            continue
        tokens = line.split()
        clause = []
        for tok in tokens:
            try:
                lit = int(tok)
                if lit == 0:
                    # End of the clause, add it to the list
                    clauses.append(clause)
                    clause = []  # Start a new clause
                else:
                    clause.append(lit)
            except ValueError:
                # Ignore non-integer tokens (such as comments)
                continue
    if clause:
        clauses.append(clause)  # Add the last clause if there is one
    return clauses

# Main function to process DIMACS CNF file
if __name__ == "__main__":
    # Open the DIMACS CNF file and read its content
    with open("file.cnf", "r") as file:
        dimacs_cnf = file.read()

    # Split the content into different formulas based on "p cnf" header
    formulas = dimacs_cnf.split('p cnf')  # Split by the header of each formula
    formulas = [f"p cnf{formula}" for formula in formulas if formula.strip()]  # Re-add the header part

    for i, formula in enumerate(formulas, 1):
        print(f"\n🔹 Rezoluție pentru formula {i}:")
        clauses = parse_dimacs_cnf(formula)
        result = pl_resolution(clauses)
        print(f"Formula este: {'SATISFIABILĂ' if result else 'NESATISFIABILĂ'}")
