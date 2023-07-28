from itertools import chain
import math
from collections import Counter
from Helper_functions import *
from decimal import Decimal, getcontext


class I_DNF:
    def __init__(self, formula: list):
        self.variables = set(item for sublist in formula for item in sublist)
        self.variable_count = len(self.variables)
        clause_times_size = len([x for clause in formula for x in clause])
        if self.variable_count != clause_times_size:
            print("Error - iDNF is not an idnf")
            print(self.variable_count)
            print(clause_times_size)
            print(formula)
            assert False

        self.idnf = formula

    def get_variable_count(self):
        return self.variable_count

    def satisfying_assignments(self):
        getcontext().prec = 100
        unsatisfied_fraction = Decimal(1)
        clause_size_pows = [Decimal(2) ** len(clause) for clause in self.idnf]

        for i, clause in enumerate(self.idnf):
            unsatisfied_fraction *= (clause_size_pows[i] - 1) / clause_size_pows[i]

        satisfied_faction = Decimal(1) - unsatisfied_fraction
        total_number_of_assignments = Decimal(2) ** self.variable_count
        result = int(total_number_of_assignments * satisfied_faction)
        return result

    def satisfying_assignments_with_fact(self, fact):
        getcontext().prec = 60
        unsatisfied_fraction = Decimal(1)
        clause_size_pows = [Decimal(2) ** len(clause) for clause in self.idnf]

        for i, clause in enumerate(self.idnf):
            if fact in clause and len(clause) == 1:
                return 2 ** (self.variable_count - 1)

            unsatisfied_fraction *= ((clause_size_pows[i] - 1) / clause_size_pows[i]) if fact not in clause else (
                    ((clause_size_pows[i] / 2) - 1) / (clause_size_pows[i] / 2))

        satisfied_faction = Decimal(1) - unsatisfied_fraction
        total_number_of_assignments = Decimal(2) ** self.variable_count
        result = int(total_number_of_assignments * satisfied_faction)
        return result

    def satisfying_assignments_without_fact(self, fact):
        getcontext().prec = 100
        unsatisfied_fraction = Decimal(1)
        clause_size_pows = [Decimal(2) ** len(clause) for clause in self.idnf]

        for i, clause in enumerate(self.idnf):
            unsatisfied_fraction *= ((clause_size_pows[i] - 1) / clause_size_pows[i]) if fact not in clause else 1

        satisfied_faction = Decimal(1) - unsatisfied_fraction
        total_number_of_assignments = Decimal(2) ** (self.variable_count - (1 if fact in self.variables else 0))
        result = int(total_number_of_assignments * satisfied_faction)
        return result

    def unsatisfying_assignments(self):
        getcontext().prec = 60
        unsatisfied_fraction = Decimal(1)
        clause_size_pows = [Decimal(2) ** len(clause) for clause in self.idnf]

        for i, clause in enumerate(self.idnf):
            unsatisfied_fraction *= (clause_size_pows[i] - 1) / clause_size_pows[i]

        total_number_of_assignments = Decimal(2) ** self.variable_count
        result = int(total_number_of_assignments * unsatisfied_fraction)
        return result

    def satisfying_assignments_by_size(self):
        current_satisfying_assignments = [0]
        current_unsatisfying_assignments = [1]
        for clause in self.idnf:
            clause_satisfying_assignments = ([0] * len(clause)) + [1]
            clause_unsatisfying_assignments = [math.comb(len(clause), i) for i in range(len(clause))]
            total_assignments = add_lists(current_satisfying_assignments, current_unsatisfying_assignments)

            current_satisfying_assignments = add_lists(convolve(total_assignments, clause_satisfying_assignments),
                                                       convolve(clause_unsatisfying_assignments,
                                                                current_satisfying_assignments))
            current_unsatisfying_assignments = convolve(clause_unsatisfying_assignments,
                                                        current_unsatisfying_assignments)

        return current_satisfying_assignments

    def satisfying_assignments_by_size_without_fact(self, fact):
        current_satisfying_assignments = [0]
        current_unsatisfying_assignments = [1]
        for clause in self.idnf:
            clause_size = len(clause) if fact not in clause else len(clause) - 1
            clause_satisfying_assignments = (([0] * (len(clause) if fact not in clause else len(clause) - 1)) + [
                1]) if fact not in clause else [0]
            clause_unsatisfying_assignments = [math.comb(clause_size, i) for i in
                                               range(clause_size if fact not in clause else (clause_size + 1))]
            total_assignments = add_lists(current_satisfying_assignments, current_unsatisfying_assignments)

            current_satisfying_assignments = add_lists(convolve(total_assignments, clause_satisfying_assignments),
                                                       convolve(clause_unsatisfying_assignments,
                                                                current_satisfying_assignments))
            current_unsatisfying_assignments = convolve(clause_unsatisfying_assignments,
                                                        current_unsatisfying_assignments)

        return current_satisfying_assignments


class DNF:
    def __init__(self, formula: list):
        self.dnf = formula
        self.model_count = -1
        self.variables = self.__get_variables__()
        self.variable_count = len(self.variables)
        self.lower_bound_idnf: I_DNF = None
        self.upper_bound_idnf: I_DNF = None
        self.current_lower_bound = None
        self.current_upper_bound = None

    def __get_variables__(self):
        self.variables = set(item for sublist in self.dnf for item in sublist)
        return self.variables

    def clause_count(self):
        return len(self.dnf)

    def is_assignment_satisfied(self, assignment):
        return any(all(fact in assignment for fact in clause) for clause in self.dnf)

    def satisfying_assignments(self):
        all_assignments = powerset(self.variables)
        for clause in self.dnf:
            assignment_to_remove = []
            for assignment in all_assignments:
                should_remove = True
                for fact in clause:
                    if fact not in assignment:
                        should_remove = False
                        break
                if should_remove:
                    assignment_to_remove.append(assignment)
            for assignment in assignment_to_remove:
                all_assignments.remove(assignment)

        satisfying_assignments = (2 ** len(self.variables)) - len(all_assignments)
        return satisfying_assignments

    def unsatisfying_assignments(self):
        if len(self.dnf) == 1:
            return (2 ** len(self.dnf[0])) - 1

        all_assignments = powerset(self.variables)
        for clause in self.dnf:
            assignment_to_remove = []
            for assignment in all_assignments:
                should_remove = True
                for fact in clause:
                    if fact not in assignment:
                        should_remove = False
                        break
                if should_remove:
                    assignment_to_remove.append(assignment)
            for assignment in assignment_to_remove:
                all_assignments.remove(assignment)

        return len(all_assignments)

    def __create_lower_bound_idnf__(self):
        if self.lower_bound_idnf is not None:
            return self.lower_bound_idnf

        idnf = []
        current_variables = set()

        for clause in self.dnf:
            add_clause = True
            for fact in clause:
                if fact in current_variables:
                    add_clause = False
                    break
            if add_clause:
                idnf.append(clause.copy())
                for fact in clause:
                    current_variables.add(fact)

        self.lower_bound_idnf = I_DNF(idnf)
        return self.lower_bound_idnf

    def __create_upper_bound_idnf__(self):
        if self.upper_bound_idnf is not None:
            return self.upper_bound_idnf

        idnf = []
        current_variables = set()

        for clause in self.dnf:
            clause_copy = clause.copy()
            for fact in clause:
                if fact in current_variables and len(clause_copy) > 1:
                    clause_copy.remove(fact)
            idnf.append(clause_copy)
            for fact in clause_copy:
                current_variables.add(fact)

        variables_to_remove = set()
        for clause in idnf:
            if len(clause) == 1:
                variables_to_remove.add(clause[0])

        for clause in idnf:
            to_remove = []
            for fact in clause:
                if fact in variables_to_remove:
                    to_remove.append(fact)
            for fact in to_remove:
                clause.remove(fact)

        idnf = [lst for lst in idnf if lst]

        for variable in variables_to_remove:
            idnf.append([variable])

        self.upper_bound_idnf = I_DNF(idnf)
        return self.upper_bound_idnf

    def satisfying_assignments_fact(self, fact):
        variables_copy = self.variables.copy()
        variables_copy.remove(fact)

        clauses = [[var for var in sub_list if var != fact] for sub_list in self.dnf]
        if any(len(clause) == 0 for clause in clauses):
            return 2 ** len(variables_copy)

        all_assignments = powerset(variables_copy)
        for clause in clauses:
            assignment_to_remove = []
            for assignment in all_assignments:
                should_remove = True
                for fact in clause:
                    if fact not in assignment:
                        should_remove = False
                        break
                if should_remove:
                    assignment_to_remove.append(assignment)
            for assignment in assignment_to_remove:
                all_assignments.remove(assignment)

        satisfying_assignments = (2 ** len(variables_copy)) - len(all_assignments)
        return satisfying_assignments

    def satisfying_assignments_without_fact(self, fact):
        variables_copy = self.variables.copy()
        variables_copy.remove(fact)

        clauses = [clause for clause in self.dnf if fact not in clause]
        if len(clauses) == 0:
            return 0

        all_assignments = powerset(variables_copy)
        for clause in clauses:
            assignment_to_remove = []
            for assignment in all_assignments:
                should_remove = True
                for fact in clause:
                    if fact not in assignment:
                        should_remove = False
                        break
                if should_remove:
                    assignment_to_remove.append(assignment)
            for assignment in assignment_to_remove:
                all_assignments.remove(assignment)

        satisfying_assignments = (2 ** len(variables_copy)) - len(all_assignments)
        return satisfying_assignments

    def critical_assignments_for_fact(self, fact):
        if fact not in self.variables:
            return 0

        satisfied_assignment_with_fact = self.satisfying_assignments_fact(fact)
        satisfied_assignment_without_fact = self.satisfying_assignments_without_fact(fact)

        return satisfied_assignment_with_fact - satisfied_assignment_without_fact

    """Assignments by size - Shapley"""

    def satisfying_assignments_by_size(self) -> list:
        if self.clause_count() == 1:
            res = ([0] * len(self.dnf[0])) + [1]
            return res

        all_assignments = powerset(self.variables)
        for clause in self.dnf:
            assignment_to_remove = []
            for assignment in all_assignments:
                should_remove = True
                for fact in clause:
                    if fact not in assignment:
                        should_remove = False
                        break
                if should_remove:
                    assignment_to_remove.append(assignment)
            for assignment in assignment_to_remove:
                all_assignments.remove(assignment)

        sizes = [len(assignment) for assignment in all_assignments]
        variable_count = len(self.variables)
        counts = [0] * (variable_count + 1)
        for size in sizes:
            counts[size] += 1

        variable_count = len(self.variables)
        return [math.comb(variable_count, i) - counts[i] for i in range(variable_count + 1)]

    def satisfying_assignments_by_size_with_fact(self, fact):
        dnf_with_fact = DNF([[var for var in sub_list if var != fact] for sub_list in self.dnf])
        if any(len(clause) == 0 for clause in dnf_with_fact.dnf):
            res = [math.comb(self.variable_count - 1, i) for i in range(self.variable_count)]
            return res
        else:
            return dnf_with_fact.satisfying_assignments_by_size()

    def satisfying_assignments_by_size_without_fact(self, fact):
        if fact not in self.variables:
            return self.satisfying_assignments_by_size()

        vars_copy = self.variables.copy()
        vars_copy.remove(fact)

        all_assignments = powerset(vars_copy)
        for clause in self.dnf:
            assignment_to_remove = []
            for assignment in all_assignments:
                should_remove = True
                for fact in clause:
                    if fact not in assignment:
                        should_remove = False
                        break
                if should_remove:
                    assignment_to_remove.append(assignment)
            for assignment in assignment_to_remove:
                all_assignments.remove(assignment)

        sizes = [len(assignment) for assignment in all_assignments]
        variable_count = len(vars_copy)
        counts = [0] * (variable_count + 1)
        for size in sizes:
            counts[size] += 1
        return [math.comb(variable_count, i) - counts[i] for i in range(variable_count + 1)]

    def critical_assignments_by_size_fact(self, fact):
        if fact not in self.variables:
            return [0]

        if self.clause_count() == 1:
            res = ([0] * (self.variable_count - 1)) if self.variable_count > 1 else []
            res.append(1)
            return res

        satisfied_assignments_with_fact = self.satisfying_assignments_by_size_with_fact(fact)
        satisfied_assignments_without_fact = self.satisfying_assignments_by_size_without_fact(fact)

        return sub_lists(satisfied_assignments_with_fact, satisfied_assignments_without_fact)

    """critical assignments lower and upper bound"""

    def get_lower_bound(self):
        if self.current_lower_bound is not None:
            return self.current_lower_bound

        if len(self.dnf) == 1:
            return 1

        self.__create_lower_bound_idnf__()

        self.current_lower_bound = max(int(self.lower_bound_idnf.satisfying_assignments() *
                                           (2 ** (self.variable_count - self.lower_bound_idnf.variable_count))), 0)

        return self.current_lower_bound

    def get_upper_bound(self):
        if self.current_upper_bound is not None:
            return self.current_upper_bound

        if len(self.dnf) == 1:
            return 1

        my_upper_bound = math.prod(
            (1 - Decimal(1) / Decimal(2) ** len(c))
            for c in self.dnf
        )

        my_upper_bound = int((1 - Decimal(my_upper_bound)) * (1 << self.variable_count))

        return min(1 << self.variable_count, my_upper_bound)

    def unsatisfying_assignments_lower_bound(self):
        if len(self.dnf) == 1:
            return (2 ** len(self.dnf[0])) - 1

        if self.upper_bound_idnf is not None:
            return self.upper_bound_idnf.unsatisfying_assignments()

        self.__create_upper_bound_idnf__()

        return int(self.upper_bound_idnf.unsatisfying_assignments() *
                   (2 ** (self.variable_count - self.upper_bound_idnf.variable_count)))

    def unsatisfying_assignments_upper_bound(self):
        if len(self.dnf) == 1:
            return (2 ** len(self.dnf[0])) - 1

        if self.lower_bound_idnf is not None:
            return self.lower_bound_idnf.unsatisfying_assignments()
        self.__create_lower_bound_idnf__()
        return int(self.lower_bound_idnf.unsatisfying_assignments() * (
                2 ** (self.variable_count - self.lower_bound_idnf.variable_count)))

    def __create_positive_dnf_fact(self, fact):
        positive_dnf = [[var for var in clause if var != fact] for clause in self.dnf]
        positive_dnf_sets = [set(clause) for clause in positive_dnf]
        positive_dnf = [l for l, s in zip(positive_dnf, positive_dnf_sets) if
                        not any(s > other for other in positive_dnf_sets)]
        positive_dnf = DNF(positive_dnf)
        return positive_dnf

    def __create_negative_dnf_fact(self, fact):
        negative_dnf = DNF([clause for clause in self.dnf if fact not in clause])
        return negative_dnf

    def lower_bound_critical_assignments_fact(self, fact):
        if len(self.dnf) == 1:
            return 1
        positive_dnf = self.__create_positive_dnf_fact(fact)
        negative_dnf = self.__create_negative_dnf_fact(fact)

        positive_lost_vars = len(self.variables) - positive_dnf.variable_count - 1
        negative_lost_vars = len(self.variables) - negative_dnf.variable_count - 1

        return max(
            1,
            positive_dnf.get_lower_bound() * (1 << positive_lost_vars) - negative_dnf.get_upper_bound() * (
                    1 << negative_lost_vars)
        )

    def upper_bound_critical_assignments_fact(self, fact):
        if len(self.dnf) == 1:
            return 1
        positive_dnf = self.__create_positive_dnf_fact(fact)
        negative_dnf = self.__create_negative_dnf_fact(fact)

        positive_lost_vars = len(self.variables) - positive_dnf.variable_count - 1
        negative_lost_vars = len(self.variables) - negative_dnf.variable_count - 1

        return min(pow(2, self.variable_count - 1),
                   max(positive_dnf.get_upper_bound() * pow(2,
                                                            positive_lost_vars) - negative_dnf.get_lower_bound() * pow(
                       2,
                       negative_lost_vars), 1))

    def lower_bound_satisfying_assignments_without_fact(self, fact):
        if fact not in self.variables:
            return self.get_lower_bound()
        if len(self.dnf) == 1:
            return 0

        self.__create_lower_bound_idnf__()

        return max(int(self.lower_bound_idnf.satisfying_assignments_without_fact(fact) *
                       (2 ** (self.variable_count - self.lower_bound_idnf.variable_count - (
                           1 if fact not in self.lower_bound_idnf.variables else 0)))), 0)

    def upper_bound_satisfying_assignments_without_fact(self, fact):
        if fact not in self.variables:
            return self.get_upper_bound()

        if len(self.dnf) == 1:
            return 0

        my_upper_bound = math.prod(
            (1 - Decimal(1) / Decimal(2) ** len(c)) if fact not in c else 1
            for c in self.dnf
        )

        my_upper_bound = int((1 - Decimal(my_upper_bound)) * (1 << (self.variable_count - 1)))

        return min((1 << (self.variable_count - 1)), my_upper_bound)

    """ Bounds by size - Shapley"""

    def lower_bound_satisfying_assignments_by_size(self):
        self.__create_lower_bound_idnf__()
        assignments_by_size = self.lower_bound_idnf.satisfying_assignments_by_size()
        lost_vars = len(self.variables) - self.lower_bound_idnf.variable_count
        lost_vars_assignments_array = [math.comb(lost_vars, i) for i in range(lost_vars + 1)]
        return convolve(assignments_by_size, lost_vars_assignments_array)

    def upper_bound_satisfying_assignments_by_size(self):
        self.__create_upper_bound_idnf__()
        assignments_by_size = self.upper_bound_idnf.satisfying_assignments_by_size()
        lost_vars = len(self.variables) - self.upper_bound_idnf.variable_count
        lost_vars_assignments_array = [math.comb(lost_vars, i) for i in range(lost_vars + 1)]
        return convolve(assignments_by_size, lost_vars_assignments_array)

    def lower_bound_satisfying_assignments_by_size_without_fact(self, fact):
        self.__create_lower_bound_idnf__()
        assignments_by_size = self.lower_bound_idnf.satisfying_assignments_by_size_without_fact(fact)
        lost_vars = (len(self.variables) - self.lower_bound_idnf.variable_count) - (
            1 if fact in self.variables and fact not in self.lower_bound_idnf.variables else 0)
        lost_vars_assignments_array = [math.comb(lost_vars, i) for i in range(lost_vars + 1)]
        return convolve(assignments_by_size, lost_vars_assignments_array)

    def upper_bound_satisfying_assignments_by_size_without_fact(self, fact):
        self.__create_upper_bound_idnf__()
        assignments_by_size = self.upper_bound_idnf.satisfying_assignments_by_size_without_fact(fact)
        lost_vars = (len(self.variables) - self.upper_bound_idnf.variable_count) - (
            1 if fact in self.variables and fact not in self.upper_bound_idnf.variables else 0)
        lost_vars_assignments_array = [math.comb(lost_vars, i) for i in range(lost_vars + 1)]
        return convolve(assignments_by_size, lost_vars_assignments_array)

    def lower_bound_critical_assignments_by_size_fact(self, fact):
        positive_dnf = self.__create_positive_dnf_fact(fact)

        negative_dnf = self.__create_negative_dnf_fact(fact)

        positive_dnf_assignments_by_size_lower_bound = positive_dnf.lower_bound_satisfying_assignments_by_size() \
            if positive_dnf.dnf \
            else [1]
        negative_dnf_assignments_by_size_upper_bound = negative_dnf.upper_bound_satisfying_assignments_by_size() \
            if negative_dnf.dnf \
            else [0]

        positive_lost_vars = len(self.variables) - positive_dnf.variable_count - 1
        positive_lost_vars_assignments_array = [math.comb(positive_lost_vars, i) for i in range(positive_lost_vars + 1)]
        negative_lost_vars = len(self.variables) - negative_dnf.variable_count - 1
        negative_lost_vars_assignments_array = [math.comb(negative_lost_vars, i) for i in range(negative_lost_vars + 1)]

        positive_dnf_assignments_by_size_lower_bound = convolve(positive_dnf_assignments_by_size_lower_bound,
                                                                positive_lost_vars_assignments_array)
        negative_dnf_assignments_by_size_upper_bound = convolve(negative_dnf_assignments_by_size_upper_bound,
                                                                negative_lost_vars_assignments_array)

        critical_assignments_by_size = sub_lists(positive_dnf_assignments_by_size_lower_bound,
                                                 negative_dnf_assignments_by_size_upper_bound)

        return critical_assignments_by_size

    def upper_bound_critical_assignments_by_size_fact(self, fact):
        positive_dnf = self.__create_positive_dnf_fact(fact)

        negative_dnf = self.__create_negative_dnf_fact(fact)

        positive_dnf_assignments_by_size_upper_bound = positive_dnf.upper_bound_satisfying_assignments_by_size() \
            if positive_dnf.dnf \
            else [1]
        negative_dnf_assignments_by_size_lower_bound = negative_dnf.lower_bound_satisfying_assignments_by_size() \
            if negative_dnf.dnf \
            else [0]

        positive_lost_vars = len(self.variables) - positive_dnf.variable_count - 1
        positive_lost_vars_assignments_array = [math.comb(positive_lost_vars, i) for i in range(positive_lost_vars + 1)]
        negative_lost_vars = len(self.variables) - negative_dnf.variable_count - 1
        negative_lost_vars_assignments_array = [math.comb(negative_lost_vars, i) for i in range(negative_lost_vars + 1)]

        positive_dnf_assignments_by_size_upper_bound = convolve(positive_dnf_assignments_by_size_upper_bound,
                                                                positive_lost_vars_assignments_array)
        negative_dnf_assignments_by_size_lower_bound = convolve(negative_dnf_assignments_by_size_lower_bound,
                                                                negative_lost_vars_assignments_array)

        critical_assignments_by_size = sub_lists(positive_dnf_assignments_by_size_upper_bound,
                                                 negative_dnf_assignments_by_size_lower_bound)

        return critical_assignments_by_size

    """
    Expansion
    """

    def __try_to_find_independent_or(self) -> (bool, list, list):
        clauses = self.dnf.copy()
        variable_set_left, variable_set_right = set(), set()
        variable_set_left = variable_set_left.union(set(clauses[0]))
        left_dnf, right_dnf = [], []

        while len(clauses) > 0:
            tmp_variable_set = set(clauses[0])
            tmp_clauses = []
            added_counter = -1
            while added_counter != 0:
                added_counter = 0
                for clause in clauses:
                    if any(variable in tmp_variable_set for variable in clause):
                        added_counter += 1
                        tmp_variable_set = tmp_variable_set.union(set(clause))
                        tmp_clauses.append(clause)
                        clauses.remove(clause)

            if len(tmp_clauses) + len(left_dnf) <= (len(self.dnf) / 2):
                left_dnf.extend(tmp_clauses)
                variable_set_left = variable_set_left.union(tmp_variable_set)
            else:
                right_dnf.extend(tmp_clauses)
                variable_set_right = variable_set_right.union(tmp_variable_set)

        return len(right_dnf) < len(self.dnf), left_dnf, right_dnf

    def __try_to_find_independent_and(self) -> (bool, list, list):
        left_dnf = list(set(self.dnf[0]).intersection(*self.dnf[1:]))
        if len(left_dnf) > 0:
            success = True
            right_dnf = [[var for var in sub_list if var not in left_dnf] for sub_list in self.dnf]
            right_dnf = [lst for lst in right_dnf if lst != []]

        else:
            success = False
            right_dnf = []

        return success, [left_dnf], right_dnf

    def __find_exclusive_or(self) -> (list, list):
        counter_obj = Counter(chain.from_iterable(self.dnf))
        variable_to_remove = counter_obj.most_common(1)[0][0]

        left_dnf = [clause for clause in self.dnf if variable_to_remove not in clause]
        right_dnf = [[var for var in sub_list if var != variable_to_remove] for sub_list in self.dnf]
        right_dnf = [lst for lst in right_dnf if lst != []]

        right_dnf_sets = [set(clause) for clause in right_dnf]
        right_dnf = [l for l, s in zip(right_dnf, right_dnf_sets) if not any(s > other for other in right_dnf_sets)]

        return left_dnf, right_dnf, variable_to_remove

    def expand(self):
        from DTree import Dtree, DTREE_GATE

        if self.clause_count() <= 1:
            return Dtree(self, DTREE_GATE.Empty_Gate), False

        # Finding independent or:
        succeeded, left_branch, right_branch = self.__try_to_find_independent_or()
        if succeeded:
            return Dtree(
                (Dtree(DNF(left_branch), DTREE_GATE.Empty_Gate), Dtree(DNF(right_branch), DTREE_GATE.Empty_Gate)),
                DTREE_GATE.Independent_Or), True

        # Finding independent And
        succeeded, left_branch, right_branch = self.__try_to_find_independent_and()
        if succeeded:
            return Dtree(
                (Dtree(DNF(left_branch), DTREE_GATE.Empty_Gate), Dtree(DNF(right_branch), DTREE_GATE.Empty_Gate)),
                DTREE_GATE.Independent_And), True

        left_branch, right_branch, removed_variable = self.__find_exclusive_or()
        return Dtree(
            (Dtree(DNF(left_branch), DTREE_GATE.Empty_Gate), Dtree(DNF(right_branch), DTREE_GATE.Empty_Gate)),
            DTREE_GATE.Exclusive_Or, hidden_variable=removed_variable), True

    def hierarchical_expand(self):
        from DTree import Dtree, DTREE_GATE

        if self.clause_count() <= 1:
            return Dtree(self, DTREE_GATE.Empty_Gate), False, False

        # Finding independent or:
        succeeded, left_branch, right_branch = self.__try_to_find_independent_or()
        if succeeded:
            left_branch, can_expand_hierarchically_l, can_expand_in_general_l = DNF(left_branch).hierarchical_expand()
            right_branch, can_expand_hierarchically_r, can_expand_in_general_r = DNF(right_branch).hierarchical_expand()
            return Dtree(
                (left_branch, right_branch),
                DTREE_GATE.Independent_Or), True, can_expand_in_general_l or can_expand_in_general_r

        # Finding independent And
        succeeded, left_branch, right_branch = self.__try_to_find_independent_and()
        if succeeded:
            left_branch, can_expand_hierarchically_l, can_expand_in_general_l = DNF(left_branch).hierarchical_expand()
            right_branch, can_expand_hierarchically_r, can_expand_in_general_r = DNF(right_branch).hierarchical_expand()

            return Dtree(
                (left_branch, right_branch),
                DTREE_GATE.Independent_And), True, can_expand_in_general_l or can_expand_in_general_r

        return Dtree(self, DTREE_GATE.Empty_Gate), False, True
