import itertools
import time

from DNF import DNF
from Expansion import Expansion


def calculate_banzhaf(dnf):
    return Expansion(dnf).calculate_banzahf()


def calculate_shapley(dnf):
    return Expansion(dnf).calculate_shapley()


def ADABAN(dnf, epsilon=0.1, timeout=3600):
    start = time.time()
    expansion = Expansion(dnf)
    bounds_dict = dict()
    relevant_facts = list(expansion.dtree.variables.copy())
    expansion.perform_hierarchical_expansion()
    depth = 1

    while len(relevant_facts) > 0:
        fact = relevant_facts[0]
        upper_bound = expansion.dtree.upper_bound_critical_assignments_fact(fact)
        mid_time = time.time()
        if mid_time - start > timeout:
            return {"status": "Failed", "depth": depth, "remaining facts": len(relevant_facts)}
        lower_bound = expansion.dtree.lower_bound_critical_assignments_fact(fact)
        bounds_dict[fact] = (lower_bound, upper_bound)
        try:
            if upper_bound / lower_bound - 1 <= epsilon:
                relevant_facts.remove(fact)
            else:
                expansion.expand_once()
                expansion.perform_hierarchical_expansion()
                depth += 1
        except Exception:
            if upper_bound // max(lower_bound, 1) - 1 <= epsilon:
                relevant_facts.remove(fact)
            else:
                expansion.expand_once()
                expansion.perform_hierarchical_expansion()
                depth += 1
        mid_time = time.time()
        if mid_time - start > timeout:
            return {"status": "Failed", "depth": depth, "remaining facts": len(relevant_facts)}

    return {"values": bounds_dict}


def Adaban_single_var(dnf: DNF, var):
    start = time.time()
    expansion = Expansion(dnf)
    results = []
    res0_l = expansion.dtree.lower_bound_critical_assignments_fact(var)
    res0_u = expansion.dtree.upper_bound_critical_assignments_fact(var)
    print(res0_u)
    print(res0_l)
    mid = time.time()
    results.append((mid - start, (res0_u + res0_l) // 2))
    should_continue = True if res0_u != res0_l else False

    while should_continue:
        expansion.perform_hierarchical_expansion()
        upper_bound = expansion.dtree.upper_bound_critical_assignments_fact(var)
        lower_bound = expansion.dtree.lower_bound_critical_assignments_fact(var)
        print(upper_bound)
        print(lower_bound)
        mid = time.time()
        results.append((mid - start, (upper_bound + lower_bound) // 2))

        expansion.expand_once()
        should_continue = True if upper_bound != lower_bound else False

    return {"var": var, "results": results}


def get_top_k_approximation(dnf, k=10, expansion=None, timeout=3600):
    if dnf.variable_count <= k or dnf.clause_count() == 1:
        return {"preprocessing_time": 0, "preprocessing_depth": 0, "bounds_time": 0, "calculation_depth": 0,
                "relevant_facts": list(dnf.variables)}
    expansion = expansion if expansion is not None else Expansion(dnf)
    bounds_dict = dict()
    start = time.time()
    relevant_facts = expansion.dtree.variables
    chained = list(itertools.chain(*dnf.dnf))
    count_dict = {f: chained.count(f) for f in relevant_facts}

    facts_in_all = [f for f in relevant_facts if chained.count(f) == len(dnf.dnf)]

    if len(facts_in_all) >= k:
        return {"preprocessing_time": 0, "preprocessing_depth": 0, "bounds_time": 0, "calculation_depth": 0,
                "relevant_facts": facts_in_all}

    count_dict = {f: count_dict[f] for f in list(count_dict.keys()) if count_dict[f] != len(dnf.dnf)}
    v1 = max(count_dict, key=count_dict.get)
    v2 = min(count_dict, key=count_dict.get)
    if count_dict[v1] == 1:
        return {"preprocessing_time": 0, "preprocessing_depth": 0, "bounds_time": 0, "calculation_depth": 0,
                "relevant_facts": list(dnf.variables)}

    i = 0
    while True:
        upper_v1 = expansion.dtree.upper_bound_satisfying_assignments_without_fact(v1)
        lower_v2 = expansion.dtree.lower_bound_satisfying_assignments_without_fact(v2)
        if upper_v1 < lower_v2:
            preprocessing_depth = i
            break
        else:
            can_expand = expansion.expand_once()
            if not can_expand:
                preprocessing_depth = i
                break
            i += 1
            mid_time = time.time()
            if mid_time - start > timeout:
                return {"status": "Failed", "depth": i, "relevant_facts": len(relevant_facts)}
    end = time.time()
    preprocessing_time = end - start
    relevant_facts_results = []

    start = time.time()
    while True:
        for j, fact in enumerate(relevant_facts):
            mid_time = time.time()
            if mid_time - start > timeout:
                return {"status": "Failed", "depth": i, "remaining facts": len(relevant_facts)}
            lower_bound = expansion.dtree.lower_bound_satisfying_assignments_without_fact(fact)
            upper_bound = expansion.dtree.upper_bound_satisfying_assignments_without_fact(fact)
            bounds_dict[fact] = (lower_bound, upper_bound)
            if bounds_dict[fact][0] > bounds_dict[fact][1]:
                print(f"fact - {fact}, lower - {bounds_dict[(fact, 0)]}, upper - {bounds_dict[(fact, 1)]}")
                assert False

        relevant_facts = find_relevant_facts(bounds_dict, relevant_facts, k)
        relevant_facts_results.append(len(relevant_facts))
        if len(relevant_facts) <= k:
            calculation_depth = i
            break
        can_expand = expansion.expand_once()
        mid_time = time.time()
        if mid_time - start > timeout:
            return {"status": "Failed", "depth": i + preprocessing_depth, "relevant_facts": len(relevant_facts)}

        if not can_expand:
            calculation_depth = i
            break
        i += 1
    end = time.time()
    bounds_time = end - start
    return {"preprocessing_time": preprocessing_time, "preprocessing_depth": preprocessing_depth,
            "bounds_time": bounds_time, "calculation_depth": calculation_depth, "relevant_facts": relevant_facts,
            "relevant_over_time": relevant_facts_results}


"""AdaBan without hierarchical expansion optimization"""


def get_epsilon_bounds(dnf, epsilon, expansion=None, timeout=3600):
    start = time.time()
    expansion = expansion if expansion is not None else Expansion(dnf)
    bounds_dict = dict()
    relevant_facts = list(expansion.dtree.variables.copy())
    depth = 0

    while len(relevant_facts) > 0:
        fact = relevant_facts[0]
        upper_bound = expansion.dtree.upper_bound_critical_assignments_fact(fact)
        mid_time = time.time()
        if mid_time - start > timeout:
            return {"status": "Failed", "depth": depth, "remaining facts": len(relevant_facts)}
        lower_bound = expansion.dtree.lower_bound_critical_assignments_fact(fact)
        bounds_dict[fact] = (lower_bound, upper_bound)
        # print(bounds_dict[fact])
        try:
            if upper_bound / lower_bound - 1 <= epsilon:
                relevant_facts.remove(fact)
            else:
                expansion.expand_once()
                depth += 1
                # print(f"depth = {depth}")
        except Exception:
            if upper_bound // max(lower_bound, 1) - 1 <= epsilon:
                relevant_facts.remove(fact)
            else:
                expansion.expand_once()
                depth += 1
        mid_time = time.time()
        if mid_time - start > timeout:
            return {"status": "Failed", "depth": depth, "remaining facts": len(relevant_facts)}

    return {"values": bounds_dict}


def find_relevant_facts(bounds_dict, facts, k):
    relevant_facts = []
    facts = list(facts)
    for fact1 in facts:
        smaller_than_count = 0
        for fact2 in facts:
            if fact1 != fact2 and bounds_dict[fact2][1] <= bounds_dict[fact1][0]:
                smaller_than_count += 1
        if smaller_than_count < k:
            relevant_facts.append(fact1)

    return relevant_facts
