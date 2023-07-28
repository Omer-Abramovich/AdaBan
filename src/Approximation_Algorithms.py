from math import comb
import random
import time

from DNF import DNF


def random_subset(s):
    return {x for x in s if random.choice((True, False))}


def monte_carlo(dnf: DNF):
    start = time.time()
    n = dnf.variable_count
    variables = dnf.variables
    criticals_dict = {var: 0 for var in variables}
    for i in range(n * 50):
        assignment = random_subset(variables)
        if dnf.is_assignment_satisfied(assignment):
            for var in assignment:
                assignment.remove(var)
                if not dnf.is_assignment_satisfied(assignment):
                    criticals_dict[var] += 1
                assignment.add(var)
        mid = time.time()
        if mid - start > 3600:
            proportion = (2 ** n) // i
            results = {var: int(criticals_dict[var] * proportion) for var in variables}
            return {"status": "Failed", "results": results}
    proportion = (2 ** n) / (n * 50)
    results = {var: int(criticals_dict[var] * proportion) for var in variables}
    return {"results": results}


def monte_carlo_single_var(dnf: DNF, var):
    start = time.time()
    n = dnf.variable_count - 1
    variables = dnf.variables.copy()
    variables.remove(var)
    criticals = 0
    results = []
    for i in range(1, n * 1000 + 1):
        assignment = random_subset(variables)
        assignment.add(var)
        if dnf.is_assignment_satisfied(assignment):
            assignment.remove(var)
            if not dnf.is_assignment_satisfied(assignment):
                criticals += 1
        mid = time.time()
        if mid - start > 7200:
            break

        if i % 10 == 0:
            mid = time.time()
            proportion = (2 ** n)
            print(i / (n * 1000))
            value = (criticals / i) * proportion
            results.append((mid - start, value))
    return {"var": var, "results": results}


def cnf_proxy(dnf):
    dnf_var_count = dnf.variable_count
    cnf, map = dnf_to_number_cnf(dnf.dnf)
    vs = {}
    for clause in cnf:
        clause = [int(v) for v in clause if abs(int(v)) <= dnf_var_count]
        n_pos = 0
        n_neg = 0
        for v in clause:
            if v > 0:
                n_pos += 1
            else:
                n_neg += 1
        for v in clause:
            is_pos = v > 0
            v = abs(v)
            if v not in vs:
                vs[v] = 0
            vs[v] += (1 if is_pos else -1) / (len(clause) * comb(len(clause) - 1, n_neg if is_pos else n_neg - 1))
    s = sum(vs.values())
    reverse_map = {v: k for k, v in map.items()}

    return {"values": {reverse_map[x[0]]: x[1] / s for x in vs.items()}}


def flatter(lst):
    x = []
    for i in lst:
        abs_lst = [abs(j) for j in i]
        x.extend(abs_lst)

    return x


def tseitin(dnf):
    maxi = max(flatter(dnf))
    next_num = maxi + 1

    ans = []
    for i in dnf:
        ans.append([-1 * i[j] for j in range(len(i))] + [next_num])
        for j in i:
            ans.append([j, -1 * next_num])
        next_num += 1

    for i in range(maxi + 1, next_num):
        ans.append([-1 * i, next_num])
    final_clause = [i for i in range(maxi + 1, next_num)]
    final_clause.append(-1 * next_num)
    ans.append(final_clause)
    ans.append([next_num])

    return ans


def dnf_to_number_cnf(dnf):
    number_dnf, num_map = map_to_numbers(dnf)
    cnf = tseitin(number_dnf)
    print(cnf)
    return cnf, num_map


def map_to_numbers(dnf):
    name_number_map = {}
    current_num = 1
    for clause in dnf:
        for fact in clause:
            if fact in name_number_map:
                continue
            else:
                name_number_map[fact] = current_num
                current_num += 1
    new_dnf = []
    for clause in dnf:
        new_dnf.append([name_number_map[fact] for fact in clause])

    print(new_dnf)
    return new_dnf, name_number_map
