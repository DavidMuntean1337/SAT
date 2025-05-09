def dpll(clauses, assignment={}):
    def unit_propagate(clauses, assignment):
        changed = True
        while changed:
            changed = False
            for clause in clauses:  # Iterezi peste toate clauzele
                if len(clause) == 1:  # Clauză unitară găsită
                    lit = clause[0]
                    var = abs(lit)
                    val = lit > 0
                    if var in assignment:
                        if assignment[var] != val:
                            return None, None  # Conflict detectat
                    else:
                        assignment[var] = val
                        clauses = simplify(clauses, var, val)
                        changed = True
                    break
        return clauses, assignment

    def simplify(clauses, var, val):
        new_clauses = []
        for clause in clauses:  # Iterezi peste toate clauzele
            if (val and var in clause) or (not val and -var in clause):
                continue  # Sari peste clauzele satisfăcute
            new_clause = [l for l in clause if l != var and l != -var]
            if new_clause:  # Adaugă clauza doar dacă nu e goală
                new_clauses.append(new_clause)
        return new_clauses

    clauses, assignment = unit_propagate(clauses, assignment.copy())
    if clauses is None:
        return False
    if not clauses:
        return True

    for clause in clauses:  # Iterezi peste toate clauzele
        for literal in clause:  # Iterezi peste literele din fiecare clauză
            var = abs(literal)
            if var not in assignment:
                for val in [True, False]:
                    new_assignment = assignment.copy()
                    new_assignment[var] = val
                    simplified_clauses = simplify(clauses, var, val)
                    if dpll(simplified_clauses, new_assignment):
                        return True
                return False
    return True

def parse_dimacs_cnf(content: str):
    clauses = []
    for line in content.splitlines():
        if len(line) == 0 or line[0] in ("c", "%"):  # Sari peste comentarii
            continue
        tokens = line.split()
        clause = []
        for tok in tokens:
            try:
                lit = int(tok)
                if lit == 0:
                    clauses.append(clause)  # Adaugă clauza
                    clause = []  # Începe o nouă clauză
                else:
                    clause.append(lit)
            except ValueError:
                continue  # Ignoră tokenii neintregeri (comentarii)
    if clause:
        clauses.append(clause)  # Adaugă ultima clauză dacă mai există
    return clauses

# Funcția principală pentru procesarea fișierului DIMACS CNF
if __name__ == "__main__":
    # Deschide fișierul DIMACS CNF și citește conținutul
    with open("file.cnf", "r") as file:
        dimacs_cnf = file.read()

    # Parsează conținutul CNF
    clauses = parse_dimacs_cnf(dimacs_cnf)
    
    print("🔹 DPLL")
    result = dpll(clauses)
    print(f"Formula este: {'SATISFIABILĂ' if result else 'NESATISFIABILĂ'}")
