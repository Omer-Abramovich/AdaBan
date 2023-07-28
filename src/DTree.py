import math
from enum import Enum
from Helper_functions import *
from DNF import DNF


class DTREE_GATE(Enum):
    Independent_Or = 1
    Independent_And = 2
    Exclusive_Or = 3
    Empty_Gate = 4


class Dtree:
    """
    initialization
    """

    def __init__(self, dtrees, gate: DTREE_GATE, hidden_variable=None):
        self.dnf: DNF = None
        self.dtree1: Dtree = None
        self.dtree2: Dtree = None
        if gate is None or gate == DTREE_GATE.Empty_Gate:
            self.dnf = dtrees
            self.size = 1
        else:
            self.dtree1, self.dtree2 = dtrees
            self.size = self.dtree1.size + self.dtree2.size
        self.gate: DTREE_GATE = gate

        self.hidden_variable = hidden_variable

        self.current_lower_bound = None
        self.current_upper_bound = None
        self.prev_lower_bound = None
        self.prev_upper_bound = None
        self.current_satisfying_assignments = None
        self.current_unsatisfying_assignments = None
        self.current_satisfying_assignments_by_size = None

        self.current_lower_bound_by_size = None
        self.current_upper_bound_by_size = None

        self.can_expand = False if (gate is None or gate == DTREE_GATE.Empty_Gate and len(self.dnf.dnf) <= 1) else True

        self.variables = self.__get_variables__()
        self.variable_count = len(self.variables)
        self.lower_bound_dict = {}
        self.upper_bound_dict = {}
        self.stop_bounds_calculation = False

    def __get_variables__(self):
        if self.dnf:
            return self.dnf.variables
        else:
            if self.hidden_variable is not None:
                return set(self.dtree1.variables.union(self.dtree2.variables).union({self.hidden_variable}))
            else:
                return set(self.dtree1.variables.union(self.dtree2.variables))

    """
    Calculate total number of satisfying assignments
    """

    def satisfying_assignments(self):
        if self.current_satisfying_assignments is not None:
            return self.current_satisfying_assignments

        if self.gate is None or self.gate == DTREE_GATE.Empty_Gate:
            self.current_satisfying_assignments = self.dnf.satisfying_assignments()
            return self.current_satisfying_assignments

        dtree1_assignments = self.dtree1.satisfying_assignments()
        dtree2_assignments = self.dtree2.satisfying_assignments()

        if self.gate == DTREE_GATE.Independent_Or:
            return dtree1_assignments * (2 ** self.dtree2.variable_count) + \
                   dtree2_assignments * (2 ** self.dtree1.variable_count) - \
                   dtree1_assignments * dtree2_assignments

        elif self.gate == DTREE_GATE.Independent_And:
            return dtree1_assignments * dtree2_assignments

        elif self.gate == DTREE_GATE.Exclusive_Or:
            variables1 = self.dtree1.variables
            variables2 = self.dtree2.variables

            unique_variables1 = len([x for x in variables1 if x not in variables2])
            unique_variables2 = len([x for x in variables2 if x not in variables1])

            return dtree1_assignments * (2 ** unique_variables2) + dtree2_assignments * (2 ** unique_variables1)

        else:
            print("Error - false gate")
            return -1

    """
    Calculate total number of unsatisfying assignments
    """

    def unsatisfying_assignments(self):
        if self.current_unsatisfying_assignments is not None:
            return self.current_unsatisfying_assignments

        if self.gate is None or self.gate == DTREE_GATE.Empty_Gate:
            self.current_unsatisfying_assignments = self.dnf.unsatisfying_assignments()
            return self.current_unsatisfying_assignments

        dtree1_unsatisfied_assignments = self.dtree1.unsatisfying_assignments()
        dtree2_unsatisfied_assignments = self.dtree2.unsatisfying_assignments()

        if self.gate == DTREE_GATE.Independent_Or:
            return dtree1_unsatisfied_assignments * dtree2_unsatisfied_assignments

        elif self.gate == DTREE_GATE.Independent_And:
            return (dtree1_unsatisfied_assignments * (2 ** self.dtree2.variable_count)) + (
                    dtree2_unsatisfied_assignments * self.dtree1.satisfying_assignments())

        elif self.gate == DTREE_GATE.Exclusive_Or:
            variables1 = self.dtree1.variables
            variables2 = self.dtree2.variables

            unique_variables1 = len([x for x in variables1 if x not in variables2])
            unique_variables2 = len([x for x in variables2 if x not in variables1])

            return dtree1_unsatisfied_assignments * (2 ** unique_variables2) + dtree2_unsatisfied_assignments * (
                    2 ** unique_variables1)

        else:
            print("Error - false gate")
            return -1

    """
    Calculate lower and upper bounds on the number of un/satisfying assignments
    """

    def lower_bound_satisfying_assignments(self):
        if self.current_lower_bound is not None:
            return self.current_lower_bound

        if self.gate is None or self.gate == DTREE_GATE.Empty_Gate:
            res = self.dnf.get_lower_bound()

        elif self.gate == DTREE_GATE.Independent_Or:
            res = self.dtree1.lower_bound_satisfying_assignments() * (2 ** self.dtree2.variable_count) + \
                  self.dtree2.lower_bound_satisfying_assignments() * (2 ** self.dtree1.variable_count) - \
                  self.dtree1.lower_bound_satisfying_assignments() * self.dtree2.lower_bound_satisfying_assignments()
            # self.dtree1.upper_bound_satisfying_assignments() * self.dtree2.upper_bound_satisfying_assignments()

        elif self.gate == DTREE_GATE.Independent_And:
            res = self.dtree1.lower_bound_satisfying_assignments() * self.dtree2.lower_bound_satisfying_assignments()

        elif self.gate == DTREE_GATE.Exclusive_Or:
            variables1 = self.dtree1.variables
            variables2 = self.dtree2.variables

            unique_variables1 = len([x for x in variables1 if x not in variables2])
            unique_variables2 = len([x for x in variables2 if x not in variables1])

            res = self.dtree1.lower_bound_satisfying_assignments() * (
                    2 ** unique_variables2) + self.dtree2.lower_bound_satisfying_assignments() * (
                          2 ** unique_variables1)

        else:
            print("Error - false gate")
            return -1

        self.current_lower_bound = max(res, 0) if self.prev_lower_bound is None \
            else max(self.prev_lower_bound, res)

        return self.current_lower_bound

    def upper_bound_satisfying_assignments(self):
        if self.current_upper_bound is not None:
            return self.current_upper_bound

        if self.gate is None or self.gate == DTREE_GATE.Empty_Gate:
            res = self.dnf.get_upper_bound()

        elif self.gate == DTREE_GATE.Independent_Or:
            res = self.dtree1.upper_bound_satisfying_assignments() * (2 ** self.dtree2.variable_count) + \
                  self.dtree2.upper_bound_satisfying_assignments() * (2 ** self.dtree1.variable_count) - \
                  self.dtree1.upper_bound_satisfying_assignments() * self.dtree2.upper_bound_satisfying_assignments()

        elif self.gate == DTREE_GATE.Independent_And:
            res = self.dtree1.upper_bound_satisfying_assignments() * self.dtree2.upper_bound_satisfying_assignments()

        elif self.gate == DTREE_GATE.Exclusive_Or:
            variables1 = self.dtree1.variables
            variables2 = self.dtree2.variables

            unique_variables1 = len([x for x in variables1 if x not in variables2])
            unique_variables2 = len([x for x in variables2 if x not in variables1])

            res = self.dtree1.upper_bound_satisfying_assignments() * (
                    2 ** unique_variables2) + self.dtree2.upper_bound_satisfying_assignments() * (
                          2 ** unique_variables1)

        else:
            print("Error - false gate")
            return -1

        self.current_upper_bound = min(res, (2 ** self.variable_count)) if self.prev_upper_bound is None else min(
            res, self.prev_upper_bound)

        return self.current_upper_bound

    def lower_bound_unsatisfying_assignments(self):
        if self.gate is None or self.gate == DTREE_GATE.Empty_Gate:
            res = self.dnf.unsatisfying_assignments_lower_bound()

        elif self.gate == DTREE_GATE.Independent_Or:
            res = self.dtree1.lower_bound_unsatisfying_assignments() * self.dtree2.lower_bound_unsatisfying_assignments()

        elif self.gate == DTREE_GATE.Independent_And:
            res = (self.dtree1.lower_bound_unsatisfying_assignments() * (2 ** self.dtree2.variable_count)) + (
                    self.dtree2.lower_bound_unsatisfying_assignments() * self.dtree1.lower_bound_satisfying_assignments())

        elif self.gate == DTREE_GATE.Exclusive_Or:
            variables1 = self.dtree1.variables
            variables2 = self.dtree2.variables

            unique_variables1 = len([x for x in variables1 if x not in variables2])
            unique_variables2 = len([x for x in variables2 if x not in variables1])

            res = self.dtree1.lower_bound_unsatisfying_assignments() * (
                    2 ** unique_variables2) + self.dtree2.lower_bound_unsatisfying_assignments() * (
                          2 ** unique_variables1)

        else:
            print("Error - false gate")
            return -1

        return res

    def upper_bound_unsatisfying_assignments(self):
        if self.gate is None or self.gate == DTREE_GATE.Empty_Gate:
            res = self.dnf.unsatisfying_assignments_upper_bound()

        elif self.gate == DTREE_GATE.Independent_Or:
            res = self.dtree1.upper_bound_unsatisfying_assignments() * self.dtree2.upper_bound_unsatisfying_assignments()

        elif self.gate == DTREE_GATE.Independent_And:
            res = (self.dtree1.upper_bound_unsatisfying_assignments() * (2 ** self.dtree2.variable_count)) + (
                    self.dtree2.upper_bound_unsatisfying_assignments() * self.dtree1.upper_bound_satisfying_assignments())

        elif self.gate == DTREE_GATE.Exclusive_Or:
            variables1 = self.dtree1.variables
            variables2 = self.dtree2.variables

            unique_variables1 = len([x for x in variables1 if x not in variables2])
            unique_variables2 = len([x for x in variables2 if x not in variables1])

            res = self.dtree1.upper_bound_unsatisfying_assignments() * (
                    2 ** unique_variables2) + self.dtree2.upper_bound_unsatisfying_assignments() * (
                          2 ** unique_variables1)

        else:
            print("Error - false gate")
            return -1

        return res

    """
    calculate satisfying assignments with fact
    """

    def satisfying_assignments_with_fact(self, fact):
        if fact not in self.variables:
            return self.satisfying_assignments()

        if self.gate is None or self.gate == DTREE_GATE.Empty_Gate:
            return self.dnf.satisfying_assignments_fact(fact)

        if self.gate == DTREE_GATE.Independent_Or:
            if fact in self.dtree1.variables:
                dtree1_assignments = self.dtree1.satisfying_assignments_with_fact(fact)
                dtree2_assignments = self.dtree2.satisfying_assignments()
                return dtree1_assignments * (2 ** self.dtree2.variable_count) + dtree2_assignments * (
                        2 ** (self.dtree1.variable_count - 1)) - dtree1_assignments * dtree2_assignments
            else:
                dtree1_assignments = self.dtree1.satisfying_assignments()
                dtree2_assignments = self.dtree2.satisfying_assignments_with_fact(fact)
                return dtree1_assignments * (2 ** (self.dtree2.variable_count - 1)) + dtree2_assignments * (
                        2 ** self.dtree1.variable_count) - dtree1_assignments * dtree2_assignments

        elif self.gate == DTREE_GATE.Independent_And:
            if fact in self.dtree1.variables:
                dtree1_assignments = self.dtree1.satisfying_assignments_with_fact(fact)
                dtree2_assignments = self.dtree2.satisfying_assignments()
            else:
                dtree1_assignments = self.dtree1.satisfying_assignments()
                dtree2_assignments = self.dtree2.satisfying_assignments_with_fact(fact)

            return dtree1_assignments * dtree2_assignments

        elif self.gate == DTREE_GATE.Exclusive_Or:

            variables1 = self.dtree1.variables
            variables2 = self.dtree2.variables

            unique_variables1 = len([x for x in variables1 if x not in variables2 and x != fact])
            unique_variables2 = len([x for x in variables2 if x not in variables1 and x != fact])
            if self.hidden_variable == fact:
                dtree1_assignments = self.dtree1.satisfying_assignments()
                return dtree1_assignments * (2 ** unique_variables2)
            else:
                dtree1_assignments = self.dtree1.satisfying_assignments_with_fact(fact)
                dtree2_assignments = self.dtree2.satisfying_assignments_with_fact(fact)
                return dtree1_assignments * (2 ** unique_variables2) + dtree2_assignments * (2 ** unique_variables1)

        else:
            print("Error - false gate")
            return -1

    def satisfying_assignments_without_fact(self, fact):
        if fact not in self.variables:
            return self.satisfying_assignments()

        if self.gate is None or self.gate == DTREE_GATE.Empty_Gate:
            return self.dnf.satisfying_assignments_without_fact(fact)

        if self.gate == DTREE_GATE.Independent_Or:
            if fact in self.dtree1.variables:
                dtree1_assignments = self.dtree1.satisfying_assignments_without_fact(fact)
                dtree2_assignments = self.dtree2.satisfying_assignments()
                return dtree1_assignments * (2 ** self.dtree2.variable_count) + dtree2_assignments * (
                            2 ** (self.dtree1.variable_count - 1)) - dtree1_assignments * dtree2_assignments
            else:
                dtree1_assignments = self.dtree1.satisfying_assignments()
                dtree2_assignments = self.dtree2.satisfying_assignments_without_fact(fact)
                return dtree1_assignments * (2 ** (self.dtree2.variable_count - 1)) + dtree2_assignments * (
                            2 ** self.dtree1.variable_count) - dtree1_assignments * dtree2_assignments

        elif self.gate == DTREE_GATE.Independent_And:
            if fact in self.dtree1.variables:
                dtree1_assignments = self.dtree1.satisfying_assignments_without_fact(fact)
                dtree2_assignments = self.dtree2.satisfying_assignments()
            else:
                dtree1_assignments = self.dtree1.satisfying_assignments()
                dtree2_assignments = self.dtree2.satisfying_assignments_without_fact(fact)

            return dtree1_assignments * dtree2_assignments

        elif self.gate == DTREE_GATE.Exclusive_Or:

            variables1 = self.dtree1.variables
            variables2 = self.dtree2.variables

            unique_variables1 = len([x for x in variables1 if x not in variables2 and x != fact])
            unique_variables2 = len([x for x in variables2 if x not in variables1 and x != fact])

            if self.hidden_variable == fact:
                dtree2_assignments = self.dtree1.satisfying_assignments()
                return dtree2_assignments * (2 ** unique_variables1)
            else:
                dtree1_assignments = self.dtree1.satisfying_assignments_without_fact(fact)
                dtree2_assignments = self.dtree2.satisfying_assignments_without_fact(fact)
                return dtree1_assignments * (2 ** unique_variables2) + dtree2_assignments * (2 ** unique_variables1)

        else:
            print("Error - false gate")
            return -1

    """
    calculate bounds on satisfying assignments with/out fact
    """

    def lower_bound_satisfying_assignments_with_fact(self, fact):
        if fact not in self.variables:
            return self.lower_bound_satisfying_assignments()

        if self.gate is None or self.gate == DTREE_GATE.Empty_Gate:
            return self.dnf.satisfying_assignments_fact(fact)  # TODO lower bound

        if self.gate == DTREE_GATE.Independent_Or:
            if fact in self.dtree1.variables:
                dtree1_assignments = self.dtree1.lower_bound_satisfying_assignments_with_fact(fact)
                dtree2_assignments = self.dtree2.lower_bound_satisfying_assignments()
                return dtree1_assignments * (2 ** self.dtree2.variable_count) + dtree2_assignments * (
                        2 ** (self.dtree1.variable_count - 1)) - dtree1_assignments * dtree2_assignments
            else:
                dtree1_assignments = self.dtree1.lower_bound_satisfying_assignments()
                dtree2_assignments = self.lower_bound_satisfying_assignments_with_fact(fact)
                return dtree1_assignments * (2 ** (self.dtree2.variable_count - 1)) + dtree2_assignments * (
                        2 ** self.dtree1.variable_count) - dtree1_assignments * dtree2_assignments

        elif self.gate == DTREE_GATE.Independent_And:
            if fact in self.dtree1.variables:
                dtree1_assignments = self.dtree1.lower_bound_satisfying_assignments_with_fact(fact)
                dtree2_assignments = self.dtree2.lower_bound_satisfying_assignments()
            else:
                dtree1_assignments = self.dtree1.lower_bound_satisfying_assignments()
                dtree2_assignments = self.dtree2.lower_bound_satisfying_assignments_with_fact(fact)

            return dtree1_assignments * dtree2_assignments

        elif self.gate == DTREE_GATE.Exclusive_Or:

            variables1 = self.dtree1.variables
            variables2 = self.dtree2.variables

            unique_variables1 = len([x for x in variables1 if x not in variables2 and x != fact])
            unique_variables2 = len([x for x in variables2 if x not in variables1 and x != fact])
            if self.hidden_variable == fact:
                dtree1_assignments = self.dtree1.lower_bound_satisfying_assignments()
                return dtree1_assignments * (2 ** unique_variables2)
            else:
                dtree1_assignments = self.dtree1.lower_bound_satisfying_assignments_with_fact(fact)
                dtree2_assignments = self.dtree2.lower_bound_satisfying_assignments_with_fact(fact)
                return dtree1_assignments * (2 ** unique_variables2) + dtree2_assignments * (2 ** unique_variables1)

        else:
            print("Error - false gate")
            return -1

    def upper_bound_satisfying_assignments_with_fact(self, fact):
        if fact not in self.variables:
            return self.upper_bound_satisfying_assignments()

        if self.gate is None or self.gate == DTREE_GATE.Empty_Gate:
            return self.dnf.satisfying_assignments_fact(fact)  # TODO upper bound

        if self.gate == DTREE_GATE.Independent_Or:
            if fact in self.dtree1.variables:
                dtree1_assignments = self.dtree1.upper_bound_satisfying_assignments_with_fact(fact)
                dtree2_assignments = self.dtree2.upper_bound_satisfying_assignments()
                return dtree1_assignments * (2 ** self.dtree2.variable_count) + dtree2_assignments * (
                            2 ** (self.dtree1.variable_count - 1)) - dtree1_assignments * dtree2_assignments
            else:
                dtree1_assignments = self.dtree1.upper_bound_satisfying_assignments()
                dtree2_assignments = self.upper_bound_satisfying_assignments_with_fact(fact)
                return dtree1_assignments * (2 ** (self.dtree2.variable_count - 1)) + dtree2_assignments * (
                            2 ** self.dtree1.variable_count) - dtree1_assignments * dtree2_assignments

        elif self.gate == DTREE_GATE.Independent_And:
            if fact in self.dtree1.variables:
                dtree1_assignments = self.dtree1.upper_bound_satisfying_assignments_with_fact(fact)
                dtree2_assignments = self.dtree2.upper_bound_satisfying_assignments()
            else:
                dtree1_assignments = self.dtree1.upper_bound_satisfying_assignments()
                dtree2_assignments = self.dtree2.upper_bound_satisfying_assignments_with_fact(fact)

            return dtree1_assignments * dtree2_assignments

        elif self.gate == DTREE_GATE.Exclusive_Or:

            variables1 = self.dtree1.variables
            variables2 = self.dtree2.variables

            unique_variables1 = len([x for x in variables1 if x not in variables2 and x != fact])
            unique_variables2 = len([x for x in variables2 if x not in variables1 and x != fact])
            if self.hidden_variable == fact:
                dtree1_assignments = self.dtree1.upper_bound_satisfying_assignments()
                return dtree1_assignments * (2 ** unique_variables2)
            else:
                dtree1_assignments = self.dtree1.upper_bound_satisfying_assignments_with_fact(fact)
                dtree2_assignments = self.dtree2.upper_bound_satisfying_assignments_with_fact(fact)
                return dtree1_assignments * (2 ** unique_variables2) + dtree2_assignments * (2 ** unique_variables1)

        else:
            print("Error - false gate")
            return -1

    def lower_bound_satisfying_assignments_without_fact(self, fact):
        if fact not in self.variables:
            return self.lower_bound_satisfying_assignments()

        if self.gate is None or self.gate == DTREE_GATE.Empty_Gate:
            return self.dnf.lower_bound_satisfying_assignments_without_fact(fact)

        if self.gate == DTREE_GATE.Independent_Or:
            if fact in self.dtree1.variables:
                dtree1_assignments = self.dtree1.lower_bound_satisfying_assignments_without_fact(fact)
                dtree2_assignments = self.dtree2.lower_bound_satisfying_assignments()
                return dtree1_assignments * (2 ** self.dtree2.variable_count) + dtree2_assignments * (
                            2 ** (self.dtree1.variable_count - 1)) - dtree1_assignments * dtree2_assignments
            else:
                dtree1_assignments = self.dtree1.lower_bound_satisfying_assignments()
                dtree2_assignments = self.dtree2.lower_bound_satisfying_assignments_without_fact(fact)
                return dtree1_assignments * (2 ** (self.dtree2.variable_count - 1)) + dtree2_assignments * (
                            2 ** self.dtree1.variable_count) - dtree1_assignments * dtree2_assignments

        elif self.gate == DTREE_GATE.Independent_And:
            if fact in self.dtree1.variables:
                dtree1_assignments = self.dtree1.lower_bound_satisfying_assignments_without_fact(fact)
                dtree2_assignments = self.dtree2.lower_bound_satisfying_assignments()
            else:
                dtree1_assignments = self.dtree1.lower_bound_satisfying_assignments()
                dtree2_assignments = self.dtree2.lower_bound_satisfying_assignments_without_fact(fact)

            return dtree1_assignments * dtree2_assignments

        elif self.gate == DTREE_GATE.Exclusive_Or:

            variables1 = self.dtree1.variables
            variables2 = self.dtree2.variables

            unique_variables1 = len([x for x in variables1 if x not in variables2 and x != fact])
            unique_variables2 = len([x for x in variables2 if x not in variables1 and x != fact])
            if self.hidden_variable == fact:
                dtree1_assignments = self.dtree1.lower_bound_satisfying_assignments_without_fact(fact)
                return dtree1_assignments * (2 ** unique_variables2)
            else:
                dtree1_assignments = self.dtree1.lower_bound_satisfying_assignments_without_fact(fact)
                dtree2_assignments = self.dtree2.lower_bound_satisfying_assignments_without_fact(fact)
                return dtree1_assignments * (2 ** unique_variables2) + dtree2_assignments * (2 ** unique_variables1)

        else:
            print("Error - false gate")
            return -1

    def upper_bound_satisfying_assignments_without_fact(self, fact):
        if fact not in self.variables:
            return self.upper_bound_satisfying_assignments()

        if self.gate is None or self.gate == DTREE_GATE.Empty_Gate:
            return self.dnf.upper_bound_satisfying_assignments_without_fact(fact)

        if self.gate == DTREE_GATE.Independent_Or:
            if fact in self.dtree1.variables:
                dtree1_assignments = self.dtree1.upper_bound_satisfying_assignments_without_fact(fact)
                dtree2_assignments = self.dtree2.upper_bound_satisfying_assignments()
                return dtree1_assignments * (2 ** self.dtree2.variable_count) + dtree2_assignments * (
                            2 ** (self.dtree1.variable_count - 1)) - dtree1_assignments * dtree2_assignments
            else:
                dtree1_assignments = self.dtree1.upper_bound_satisfying_assignments()
                dtree2_assignments = self.dtree2.upper_bound_satisfying_assignments_without_fact(fact)
                return dtree1_assignments * (2 ** (self.dtree2.variable_count - 1)) + dtree2_assignments * (
                            2 ** self.dtree1.variable_count) - dtree1_assignments * dtree2_assignments

        elif self.gate == DTREE_GATE.Independent_And:
            if fact in self.dtree1.variables:
                dtree1_assignments = self.dtree1.upper_bound_satisfying_assignments_without_fact(fact)
                dtree2_assignments = self.dtree2.upper_bound_satisfying_assignments()
            else:
                dtree1_assignments = self.dtree1.upper_bound_satisfying_assignments()
                dtree2_assignments = self.dtree2.upper_bound_satisfying_assignments_without_fact(fact)

            return dtree1_assignments * dtree2_assignments

        elif self.gate == DTREE_GATE.Exclusive_Or:

            variables1 = self.dtree1.variables
            variables2 = self.dtree2.variables

            unique_variables1 = len([x for x in variables1 if x not in variables2 and x != fact])
            unique_variables2 = len([x for x in variables2 if x not in variables1 and x != fact])
            if self.hidden_variable == fact:
                dtree1_assignments = self.dtree1.upper_bound_satisfying_assignments()
                return dtree1_assignments * (2 ** unique_variables2)
            else:
                dtree1_assignments = self.dtree1.upper_bound_satisfying_assignments_without_fact(fact)
                dtree2_assignments = self.dtree2.upper_bound_satisfying_assignments_without_fact(fact)
                return dtree1_assignments * (2 ** unique_variables2) + dtree2_assignments * (2 ** unique_variables1)

        else:
            print("Error - false gate")
            return -1

    """
    calculate critical assignments for fact - Banzhaf
    """

    def critical_assignments_fact(self, fact):
        if fact not in self.variables:
            return 0

        if self.gate is None or self.gate == DTREE_GATE.Empty_Gate:
            return self.dnf.critical_assignments_for_fact(fact)

        if self.gate == DTREE_GATE.Independent_Or:
            if fact in self.dtree1.variables:
                return self.dtree1.critical_assignments_fact(fact) * (
                        (2 ** self.dtree2.variable_count) - self.dtree2.satisfying_assignments())
            else:
                return self.dtree2.critical_assignments_fact(fact) * (
                        (2 ** self.dtree1.variable_count) - self.dtree1.satisfying_assignments())

        elif self.gate == DTREE_GATE.Independent_And:
            if fact in self.dtree1.variables:
                return self.dtree1.critical_assignments_fact(fact) * self.dtree2.satisfying_assignments()
            else:
                return self.dtree2.critical_assignments_fact(fact) * self.dtree1.satisfying_assignments()

        elif self.gate == DTREE_GATE.Exclusive_Or:
            variables1 = self.dtree1.variables
            variables2 = self.dtree2.variables
            unique_variables1 = len([x for x in variables1 if x not in variables2])
            unique_variables2 = len([x for x in variables2 if x not in variables1])

            if self.hidden_variable == fact:
                return self.dtree2.satisfying_assignments() * (
                        2 ** unique_variables1) - self.dtree1.satisfying_assignments() * (2 ** unique_variables2)
            else:
                return self.dtree1.critical_assignments_fact(fact) * (
                        2 ** unique_variables2) + self.dtree2.critical_assignments_fact(fact) * (
                               2 ** unique_variables1)

        else:
            print("Error - false gate")
            return -1

    def lower_bound_critical_assignments_fact(self, fact):
        if fact not in self.variables:
            return 0

        if self.stop_bounds_calculation and fact in self.lower_bound_dict:
            return self.lower_bound_dict[fact]

        if self.gate is None or self.gate == DTREE_GATE.Empty_Gate:
            if not self.can_expand:
                self.stop_bounds_calculation = True
            if fact in self.lower_bound_dict:
                return self.lower_bound_dict[fact]
            else:
                res = self.dnf.lower_bound_critical_assignments_fact(fact)
                self.lower_bound_dict[fact] = res
                return res

        if self.gate == DTREE_GATE.Independent_Or:
            if fact in self.dtree1.variables:
                res = self.dtree1.lower_bound_critical_assignments_fact(fact) * (
                        (2 ** self.dtree2.variable_count) - self.dtree2.upper_bound_satisfying_assignments())
            else:
                res = self.dtree2.lower_bound_critical_assignments_fact(fact) * (
                        (2 ** self.dtree1.variable_count) - self.dtree1.upper_bound_satisfying_assignments())

        elif self.gate == DTREE_GATE.Independent_And:
            if fact in self.dtree1.variables:
                res = self.dtree1.lower_bound_critical_assignments_fact(
                    fact) * self.dtree2.lower_bound_satisfying_assignments()
            else:
                res = self.dtree2.lower_bound_critical_assignments_fact(
                    fact) * self.dtree1.lower_bound_satisfying_assignments()

        elif self.gate == DTREE_GATE.Exclusive_Or:
            variables1 = self.dtree1.variables
            variables2 = self.dtree2.variables
            unique_variables1 = len([x for x in variables1 if x not in variables2])
            unique_variables2 = len([x for x in variables2 if x not in variables1])

            if self.hidden_variable == fact:
                res = self.dtree2.lower_bound_satisfying_assignments() * (
                        2 ** unique_variables1) - self.dtree1.upper_bound_satisfying_assignments() * (
                              2 ** unique_variables2)
            else:
                res = self.dtree1.lower_bound_critical_assignments_fact(fact) * (
                        2 ** unique_variables2) + self.dtree2.lower_bound_critical_assignments_fact(fact) * (
                              2 ** unique_variables1)

        else:
            print("Error - false gate")
            return -1

        self.lower_bound_dict[fact] = max(res, 0) if fact not in self.lower_bound_dict else max(
            self.lower_bound_dict[fact], res)
        if not self.can_expand:
            self.stop_bounds_calculation = False
        return self.lower_bound_dict[fact]

    def upper_bound_critical_assignments_fact(self, fact):
        if fact not in self.variables:
            return 0

        if self.stop_bounds_calculation and fact in self.upper_bound_dict:
            return self.upper_bound_dict[fact]

        if self.gate is None or self.gate == DTREE_GATE.Empty_Gate:
            if not self.can_expand:
                self.stop_bounds_calculation = True

            res = self.dnf.upper_bound_critical_assignments_fact(fact)
            self.upper_bound_dict[fact] = res
            return res

        if self.gate == DTREE_GATE.Independent_Or:
            if fact in self.dtree1.variables:
                res = self.dtree1.upper_bound_critical_assignments_fact(fact) * (
                        (2 ** self.dtree2.variable_count) - self.dtree2.lower_bound_satisfying_assignments())
            else:
                res = self.dtree2.upper_bound_critical_assignments_fact(fact) * (
                        (2 ** self.dtree1.variable_count) - self.dtree1.lower_bound_satisfying_assignments())

        elif self.gate == DTREE_GATE.Independent_And:
            if fact in self.dtree1.variables:
                res = self.dtree1.upper_bound_critical_assignments_fact(
                    fact) * self.dtree2.upper_bound_satisfying_assignments()
            else:
                res = self.dtree2.upper_bound_critical_assignments_fact(
                    fact) * self.dtree1.upper_bound_satisfying_assignments()

        elif self.gate == DTREE_GATE.Exclusive_Or:
            variables1 = self.dtree1.variables
            variables2 = self.dtree2.variables
            unique_variables1 = len([x for x in variables1 if x not in variables2])
            unique_variables2 = len([x for x in variables2 if x not in variables1])

            if self.hidden_variable == fact:
                res = self.dtree2.upper_bound_satisfying_assignments() * (
                        2 ** unique_variables1) - self.dtree1.lower_bound_satisfying_assignments() * (
                              2 ** unique_variables2)
            else:
                res = self.dtree1.upper_bound_critical_assignments_fact(fact) * (
                        2 ** unique_variables2) + self.dtree2.upper_bound_critical_assignments_fact(fact) * (
                              2 ** unique_variables1)

        else:
            print("Error - false gate")
            return -1

        self.upper_bound_dict[fact] = min(res, 2 ** self.variable_count) if fact not in self.upper_bound_dict else min(
            self.upper_bound_dict[fact], res)
        if not self.can_expand:
            self.stop_bounds_calculation = True
        return self.upper_bound_dict[fact]

    """
    Shapley related calculations - assignments by size
    """

    def satisfying_assignments_by_size(self) -> list:
        if self.current_satisfying_assignments_by_size is not None:
            return self.current_satisfying_assignments_by_size

        if self.gate is None or self.gate == DTREE_GATE.Empty_Gate:
            result = self.dnf.satisfying_assignments_by_size()
            self.current_satisfying_assignments_by_size = result
            return result

        dtree1_assignments_by_size = self.dtree1.satisfying_assignments_by_size()
        dtree2_assignments_by_size = self.dtree2.satisfying_assignments_by_size()

        if self.gate == DTREE_GATE.Independent_Or:
            l_branch_assignments = dtree1_assignments_by_size
            r_branch_assignments = dtree2_assignments_by_size
            l_branch_vars = self.dtree1.variable_count
            r_branch_vars = self.dtree2.variable_count
            l_branch_total_assignments = [math.comb(l_branch_vars, i) for i in range(l_branch_vars + 1)]
            r_branch_total_assignments = [math.comb(r_branch_vars, i) for i in range(r_branch_vars + 1)]

            result = sub_lists(add_lists(convolve(l_branch_assignments, r_branch_total_assignments),
                                         convolve(r_branch_assignments, l_branch_total_assignments)),
                               convolve(l_branch_assignments, r_branch_assignments))

        elif self.gate == DTREE_GATE.Independent_And:
            l_branch_assignments = dtree1_assignments_by_size
            r_branch_assignments = dtree2_assignments_by_size
            result = convolve(l_branch_assignments, r_branch_assignments)

        elif self.gate == DTREE_GATE.Exclusive_Or:
            variables1 = self.dtree1.variables
            variables2 = self.dtree2.variables

            unique_variables1 = len([x for x in variables1 if x not in variables2])
            unique_variables2 = len([x for x in variables2 if x not in variables1])

            unique_variables1_by_size = [math.comb(unique_variables1, i) for i in range(unique_variables1 + 1)]
            unique_variables2_by_size = [math.comb(unique_variables2, i) for i in range(unique_variables2 + 1)]

            l_branch_assignments = dtree1_assignments_by_size
            r_branch_assignments = convolve(dtree2_assignments_by_size, [0, 1])

            result = add_lists(convolve(l_branch_assignments, unique_variables2_by_size),
                               convolve(r_branch_assignments, unique_variables1_by_size))

        else:
            print("Error - false gate")
            return [None]

        self.current_satisfying_assignments_by_size = result
        return result

    def critical_assignments_by_size_fact(self, fact):
        if fact not in self.variables:
            return [0]

        if self.gate is None or self.gate == DTREE_GATE.Empty_Gate:
            return self.dnf.critical_assignments_by_size_fact(fact)

        dtree1_critical_assignments_by_size = self.dtree1.critical_assignments_by_size_fact(fact)
        dtree2_critical_assignments_by_size = self.dtree2.critical_assignments_by_size_fact(fact)

        if self.gate == DTREE_GATE.Independent_Or:
            if fact in self.dtree1.variables:
                r_branch_vars = self.dtree2.variable_count
                r_branch_unsatisfied_assignments = sub_lists(
                    [math.comb(r_branch_vars, i) for i in range(r_branch_vars + 1)],
                    self.dtree2.satisfying_assignments_by_size())
                return convolve(dtree1_critical_assignments_by_size, r_branch_unsatisfied_assignments)
            else:
                l_branch_vars = self.dtree1.variable_count
                l_branch_unsatisfied_assignments = sub_lists(
                    [math.comb(l_branch_vars, i) for i in range(l_branch_vars + 1)],
                    self.dtree1.satisfying_assignments_by_size())
                return convolve(dtree2_critical_assignments_by_size, l_branch_unsatisfied_assignments)

        elif self.gate == DTREE_GATE.Independent_And:
            if fact in self.dtree1.variables:
                l_branch_assignments = dtree1_critical_assignments_by_size
                r_branch_assignments = self.dtree2.satisfying_assignments_by_size()
            else:
                l_branch_assignments = self.dtree1.satisfying_assignments_by_size()
                r_branch_assignments = dtree2_critical_assignments_by_size

            return convolve(l_branch_assignments, r_branch_assignments)

        elif self.gate == DTREE_GATE.Exclusive_Or:
            if fact == self.hidden_variable:
                lost_vars1 = self.variable_count - self.dtree1.variable_count - 1
                lost_vars2 = self.variable_count - self.dtree2.variable_count - 1
                lost_vars1_assignments_array = self.__create_lost_variables_assignments__(lost_vars1)
                lost_vars2_assignments_array = self.__create_lost_variables_assignments__(lost_vars2)
                dtree1_assignments_by_size = self.dtree1.satisfying_assignments_by_size()
                dtree2_assignments_by_size = self.dtree2.satisfying_assignments_by_size()
                dtree1_real_assignments_by_size = convolve(dtree1_assignments_by_size, lost_vars1_assignments_array)
                dtree2_real_assignments_by_size = convolve(dtree2_assignments_by_size, lost_vars2_assignments_array)
                return sub_lists(dtree2_real_assignments_by_size, dtree1_real_assignments_by_size)
            else:
                variables1 = self.dtree1.variables
                variables2 = self.dtree2.variables

                unique_variables1 = len([x for x in variables1 if x not in variables2])
                unique_variables2 = len([x for x in variables2 if x not in variables1])

                unique_variables1_by_size = [math.comb(unique_variables1, i) for i in range(unique_variables1 + 1)]
                unique_variables2_by_size = [math.comb(unique_variables2, i) for i in range(unique_variables2 + 1)]
                l_branch_assignments = dtree1_critical_assignments_by_size
                r_branch_assignments = convolve(dtree2_critical_assignments_by_size, [0, 1])

                result = add_lists(convolve(l_branch_assignments, unique_variables2_by_size),
                                   convolve(r_branch_assignments, unique_variables1_by_size))

                return result

        else:
            print("Error - false gate")
            return -1

    def lower_bound_satisfying_assignments_by_size(self) -> list:
        if self.current_lower_bound_by_size is not None:
            return self.current_lower_bound_by_size

        if self.gate is None or self.gate == DTREE_GATE.Empty_Gate:
            result = self.dnf.lower_bound_satisfying_assignments_by_size()

        elif self.gate == DTREE_GATE.Independent_Or:
            l_branch_vars = self.dtree1.variable_count
            r_branch_vars = self.dtree2.variable_count
            l_branch_total_assignments = [math.comb(l_branch_vars, i) for i in range(l_branch_vars + 1)]
            r_branch_total_assignments = [math.comb(r_branch_vars, i) for i in range(r_branch_vars + 1)]

            result = sub_lists(add_lists(
                convolve(self.dtree1.lower_bound_satisfying_assignments_by_size(), r_branch_total_assignments),
                convolve(self.dtree2.lower_bound_satisfying_assignments_by_size(), l_branch_total_assignments)),
                convolve(self.dtree1.lower_bound_satisfying_assignments_by_size(),
                         self.dtree2.lower_bound_satisfying_assignments_by_size()))

        elif self.gate == DTREE_GATE.Independent_And:
            result = convolve(self.dtree1.lower_bound_satisfying_assignments_by_size(),
                              self.dtree2.lower_bound_satisfying_assignments_by_size())

        elif self.gate == DTREE_GATE.Exclusive_Or:
            variables1 = self.dtree1.variables
            variables2 = self.dtree2.variables

            unique_variables1 = len([x for x in variables1 if x not in variables2])
            unique_variables2 = len([x for x in variables2 if x not in variables1])

            unique_variables1_by_size = [math.comb(unique_variables1, i) for i in range(unique_variables1 + 1)]
            unique_variables2_by_size = [math.comb(unique_variables2, i) for i in range(unique_variables2 + 1)]

            l_branch_assignments = self.dtree1.lower_bound_satisfying_assignments_by_size()
            r_branch_assignments = convolve(self.dtree2.lower_bound_satisfying_assignments_by_size(), [0, 1])

            result = add_lists(convolve(l_branch_assignments, unique_variables2_by_size),
                               convolve(r_branch_assignments, unique_variables1_by_size))

        else:
            print("Error - false gate")
            return [None]

        self.current_lower_bound_by_size = result
        return result

    def upper_bound_satisfying_assignments_by_size(self) -> list:
        if self.current_upper_bound_by_size is not None:
            return self.current_upper_bound_by_size

        if self.gate is None or self.gate == DTREE_GATE.Empty_Gate:
            result = self.dnf.upper_bound_satisfying_assignments_by_size()

        elif self.gate == DTREE_GATE.Independent_Or:
            l_branch_vars = self.dtree1.variable_count
            r_branch_vars = self.dtree2.variable_count
            l_branch_total_assignments = [math.comb(l_branch_vars, i) for i in range(l_branch_vars + 1)]
            r_branch_total_assignments = [math.comb(r_branch_vars, i) for i in range(r_branch_vars + 1)]

            result = sub_lists(add_lists(
                convolve(self.dtree1.upper_bound_satisfying_assignments_by_size(), r_branch_total_assignments),
                convolve(self.dtree2.upper_bound_satisfying_assignments_by_size(), l_branch_total_assignments)),
                convolve(self.dtree1.upper_bound_satisfying_assignments_by_size(),
                         self.dtree2.upper_bound_satisfying_assignments_by_size()))

        elif self.gate == DTREE_GATE.Independent_And:
            result = convolve(self.dtree1.upper_bound_satisfying_assignments_by_size(),
                              self.dtree2.upper_bound_satisfying_assignments_by_size())

        elif self.gate == DTREE_GATE.Exclusive_Or:
            variables1 = self.dtree1.variables
            variables2 = self.dtree2.variables

            unique_variables1 = len([x for x in variables1 if x not in variables2])
            unique_variables2 = len([x for x in variables2 if x not in variables1])

            unique_variables1_by_size = [math.comb(unique_variables1, i) for i in range(unique_variables1 + 1)]
            unique_variables2_by_size = [math.comb(unique_variables2, i) for i in range(unique_variables2 + 1)]

            l_branch_assignments = self.dtree1.upper_bound_satisfying_assignments_by_size()
            r_branch_assignments = convolve(self.dtree2.upper_bound_satisfying_assignments_by_size(), [0, 1])

            result = add_lists(convolve(l_branch_assignments, unique_variables2_by_size),
                               convolve(r_branch_assignments, unique_variables1_by_size))

        else:
            print("Error - false gate")
            return [None]

        self.current_upper_bound_by_size = result
        return result

    def lower_bound_critical_assignments_by_size_fact(self, fact):
        if fact not in self.variables:
            return [0]

        if self.gate is None or self.gate == DTREE_GATE.Empty_Gate:
            return self.dnf.lower_bound_critical_assignments_by_size_fact(fact)

        if self.gate == DTREE_GATE.Independent_Or:
            if fact in self.dtree1.variables:
                r_branch_vars = self.dtree2.variable_count
                r_branch_unsatisfied_assignments = sub_lists(
                    [math.comb(r_branch_vars, i) for i in range(r_branch_vars + 1)],
                    self.dtree2.upper_bound_satisfying_assignments_by_size())
                return convolve(self.dtree1.lower_bound_critical_assignments_by_size_fact(fact),
                                r_branch_unsatisfied_assignments)
            else:
                l_branch_vars = self.dtree1.variable_count
                l_branch_unsatisfied_assignments = sub_lists(
                    [math.comb(l_branch_vars, i) for i in range(l_branch_vars + 1)],
                    self.dtree1.upper_bound_satisfying_assignments_by_size())
                return convolve(self.dtree2.lower_bound_critical_assignments_by_size_fact(fact),
                                l_branch_unsatisfied_assignments)

        elif self.gate == DTREE_GATE.Independent_And:
            if fact in self.dtree1.variables:
                l_branch_assignments = self.dtree1.lower_bound_critical_assignments_by_size_fact(fact)
                r_branch_assignments = self.dtree2.lower_bound_satisfying_assignments_by_size()
            else:
                l_branch_assignments = self.dtree1.lower_bound_satisfying_assignments_by_size()
                r_branch_assignments = self.dtree2.lower_bound_critical_assignments_by_size_fact(fact)

            return convolve(l_branch_assignments, r_branch_assignments)

        elif self.gate == DTREE_GATE.Exclusive_Or:
            if fact == self.hidden_variable:
                lost_vars1 = self.variable_count - self.dtree1.variable_count - 1
                lost_vars2 = self.variable_count - self.dtree2.variable_count - 1
                lost_vars1_assignments_array = self.__create_lost_variables_assignments__(lost_vars1)
                lost_vars2_assignments_array = self.__create_lost_variables_assignments__(lost_vars2)
                dtree1_assignments_by_size = self.dtree1.upper_bound_satisfying_assignments_by_size()
                dtree2_assignments_by_size = self.dtree2.lower_bound_satisfying_assignments_by_size()
                dtree1_real_assignments_by_size = convolve(dtree1_assignments_by_size, lost_vars1_assignments_array)
                dtree2_real_assignments_by_size = convolve(dtree2_assignments_by_size, lost_vars2_assignments_array)
                return sub_lists(dtree2_real_assignments_by_size, dtree1_real_assignments_by_size)
            else:
                variables1 = self.dtree1.variables
                variables2 = self.dtree2.variables

                unique_variables1 = len([x for x in variables1 if x not in variables2])
                unique_variables2 = len([x for x in variables2 if x not in variables1])

                unique_variables1_by_size = [math.comb(unique_variables1, i) for i in range(unique_variables1 + 1)]
                unique_variables2_by_size = [math.comb(unique_variables2, i) for i in range(unique_variables2 + 1)]
                l_branch_assignments = self.dtree1.lower_bound_critical_assignments_by_size_fact(fact)
                r_branch_assignments = convolve(self.dtree2.lower_bound_critical_assignments_by_size_fact(fact), [0, 1])

                result = add_lists(convolve(l_branch_assignments, unique_variables2_by_size),
                                   convolve(r_branch_assignments, unique_variables1_by_size))

                return result

        else:
            print("Error - false gate")
            return -1

    def upper_bound_critical_assignments_by_size_fact(self, fact):
        if fact not in self.variables:
            return [0]

        if self.gate is None or self.gate == DTREE_GATE.Empty_Gate:
            return self.dnf.upper_bound_critical_assignments_by_size_fact(fact)

        if self.gate == DTREE_GATE.Independent_Or:
            if fact in self.dtree1.variables:
                r_branch_vars = self.dtree2.variable_count
                r_branch_unsatisfied_assignments = sub_lists(
                    [math.comb(r_branch_vars, i) for i in range(r_branch_vars + 1)],
                    self.dtree2.lower_bound_satisfying_assignments_by_size())
                return convolve(self.dtree1.upper_bound_critical_assignments_by_size_fact(fact),
                                r_branch_unsatisfied_assignments)
            else:
                l_branch_vars = self.dtree1.variable_count
                l_branch_unsatisfied_assignments = sub_lists(
                    [math.comb(l_branch_vars, i) for i in range(l_branch_vars + 1)],
                    self.dtree1.lower_bound_satisfying_assignments_by_size())
                return convolve(self.dtree2.upper_bound_critical_assignments_by_size_fact(fact),
                                l_branch_unsatisfied_assignments)

        elif self.gate == DTREE_GATE.Independent_And:
            if fact in self.dtree1.variables:
                l_branch_assignments = self.dtree1.upper_bound_critical_assignments_by_size_fact(fact)
                r_branch_assignments = self.dtree2.upper_bound_satisfying_assignments_by_size()
            else:
                l_branch_assignments = self.dtree1.upper_bound_satisfying_assignments_by_size()
                r_branch_assignments = self.dtree2.upper_bound_critical_assignments_by_size_fact(fact)

            return convolve(l_branch_assignments, r_branch_assignments)

        elif self.gate == DTREE_GATE.Exclusive_Or:
            if fact == self.hidden_variable:
                lost_vars1 = self.variable_count - self.dtree1.variable_count - 1
                lost_vars2 = self.variable_count - self.dtree2.variable_count - 1
                lost_vars1_assignments_array = self.__create_lost_variables_assignments__(lost_vars1)
                lost_vars2_assignments_array = self.__create_lost_variables_assignments__(lost_vars2)
                dtree1_assignments_by_size = self.dtree1.lower_bound_satisfying_assignments_by_size()
                dtree2_assignments_by_size = self.dtree2.upper_bound_satisfying_assignments_by_size()
                dtree1_real_assignments_by_size = convolve(dtree1_assignments_by_size, lost_vars1_assignments_array)
                dtree2_real_assignments_by_size = convolve(dtree2_assignments_by_size, lost_vars2_assignments_array)
                return sub_lists(dtree2_real_assignments_by_size, dtree1_real_assignments_by_size)
            else:
                variables1 = self.dtree1.variables
                variables2 = self.dtree2.variables

                unique_variables1 = len([x for x in variables1 if x not in variables2])
                unique_variables2 = len([x for x in variables2 if x not in variables1])

                unique_variables1_by_size = [math.comb(unique_variables1, i) for i in range(unique_variables1 + 1)]
                unique_variables2_by_size = [math.comb(unique_variables2, i) for i in range(unique_variables2 + 1)]
                l_branch_assignments = self.dtree1.upper_bound_critical_assignments_by_size_fact(fact)
                r_branch_assignments = convolve(self.dtree2.upper_bound_critical_assignments_by_size_fact(fact), [0, 1])

                result = add_lists(convolve(l_branch_assignments, unique_variables2_by_size),
                                   convolve(r_branch_assignments, unique_variables1_by_size))

                return result

        else:
            print("Error - false gate")
            return -1

    def lower_bound_satisfying_assignments_by_size_without_fact(self, fact):
        if fact not in self.variables:
            return self.lower_bound_satisfying_assignments_by_size()

        if self.gate is None or self.gate == DTREE_GATE.Empty_Gate:
            return self.dnf.lower_bound_satisfying_assignments_by_size_without_fact(fact)

        if self.gate == DTREE_GATE.Independent_Or:
            if fact in self.dtree1.variables:
                dtree1_assignments = self.dtree1.lower_bound_satisfying_assignments_by_size_without_fact(fact)
                dtree2_assignments = self.dtree2.lower_bound_satisfying_assignments_by_size()

                return sub_lists(add_lists(convolve(dtree1_assignments, self.__create_lost_variables_assignments__(
                    self.dtree2.variable_count)),
                                           convolve(dtree2_assignments, self.__create_lost_variables_assignments__(
                                               self.dtree1.variable_count - 1))),
                                 convolve(dtree1_assignments, dtree2_assignments))
            else:
                dtree1_assignments = self.dtree1.lower_bound_satisfying_assignments_by_size()
                dtree2_assignments = self.dtree2.lower_bound_satisfying_assignments_by_size_without_fact(fact)

                return sub_lists(add_lists(convolve(dtree1_assignments, self.__create_lost_variables_assignments__(
                    self.dtree2.variable_count - 1)),
                                           convolve(dtree2_assignments, self.__create_lost_variables_assignments__(
                                               self.dtree1.variable_count))),
                                 convolve(dtree1_assignments, dtree2_assignments))

        elif self.gate == DTREE_GATE.Independent_And:
            if fact in self.dtree1.variables:
                dtree1_assignments = self.dtree1.lower_bound_satisfying_assignments_by_size_without_fact(fact)
                dtree2_assignments = self.dtree2.lower_bound_satisfying_assignments_by_size()
            else:
                dtree1_assignments = self.dtree1.lower_bound_satisfying_assignments_by_size()
                dtree2_assignments = self.dtree2.lower_bound_satisfying_assignments_by_size_without_fact(fact)

            return convolve(dtree1_assignments, dtree2_assignments)

        elif self.gate == DTREE_GATE.Exclusive_Or:

            variables1 = self.dtree1.variables
            variables2 = self.dtree2.variables

            unique_variables1 = len([x for x in variables1 if x not in variables2 and x != fact])
            unique_variables2 = len([x for x in variables2 if x not in variables1 and x != fact])
            if self.hidden_variable == fact:
                dtree1_assignments = self.dtree1.lower_bound_satisfying_assignments_by_size_without_fact(fact)
                return convolve(dtree1_assignments, self.__create_lost_variables_assignments__(unique_variables2))
            else:
                dtree1_assignments = self.dtree1.lower_bound_satisfying_assignments_by_size_without_fact(fact)
                dtree2_assignments = convolve(self.dtree2.lower_bound_satisfying_assignments_by_size_without_fact(fact),
                                              [0, 1])
                return add_lists(
                    convolve(dtree1_assignments, self.__create_lost_variables_assignments__(unique_variables2)),
                    convolve(dtree2_assignments, self.__create_lost_variables_assignments__(unique_variables1)))

        else:
            print("Error - false gate")
            return -1

    def upper_bound_satisfying_assignments_by_size_without_fact(self, fact):
        if fact not in self.variables:
            return self.upper_bound_satisfying_assignments_by_size()

        if self.gate is None or self.gate == DTREE_GATE.Empty_Gate:
            return self.dnf.upper_bound_satisfying_assignments_by_size_without_fact(fact)

        if self.gate == DTREE_GATE.Independent_Or:
            if fact in self.dtree1.variables:
                dtree1_assignments = self.dtree1.upper_bound_satisfying_assignments_by_size_without_fact(fact)
                dtree2_assignments = self.dtree2.upper_bound_satisfying_assignments_by_size()
                return sub_lists(add_lists(convolve(dtree1_assignments, self.__create_lost_variables_assignments__(
                    self.dtree2.variable_count)),
                                           convolve(dtree2_assignments, self.__create_lost_variables_assignments__(
                                               self.dtree1.variable_count - 1))),
                                 convolve(dtree1_assignments, dtree2_assignments))
            else:
                dtree1_assignments = self.dtree1.upper_bound_satisfying_assignments_by_size()
                dtree2_assignments = self.dtree2.upper_bound_satisfying_assignments_by_size_without_fact(fact)
                return sub_lists(add_lists(convolve(dtree1_assignments, self.__create_lost_variables_assignments__(
                    self.dtree2.variable_count - 1)),
                                           convolve(dtree2_assignments, self.__create_lost_variables_assignments__(
                                               self.dtree1.variable_count))),
                                 convolve(dtree1_assignments, dtree2_assignments))

        elif self.gate == DTREE_GATE.Independent_And:
            if fact in self.dtree1.variables:
                dtree1_assignments = self.dtree1.upper_bound_satisfying_assignments_by_size_without_fact(fact)
                dtree2_assignments = self.dtree2.upper_bound_satisfying_assignments_by_size()
            else:
                dtree1_assignments = self.dtree1.upper_bound_satisfying_assignments_by_size()
                dtree2_assignments = self.dtree2.upper_bound_satisfying_assignments_by_size_without_fact(fact)

            return convolve(dtree1_assignments, dtree2_assignments)

        elif self.gate == DTREE_GATE.Exclusive_Or:

            variables1 = self.dtree1.variables
            variables2 = self.dtree2.variables

            unique_variables1 = len([x for x in variables1 if x not in variables2 and x != fact])
            unique_variables2 = len([x for x in variables2 if x not in variables1 and x != fact])
            if self.hidden_variable == fact:
                dtree1_assignments = self.dtree1.upper_bound_satisfying_assignments_by_size_without_fact(fact)
                return convolve(dtree1_assignments, self.__create_lost_variables_assignments__(unique_variables2))
            else:
                dtree1_assignments = self.dtree1.upper_bound_satisfying_assignments_by_size_without_fact(fact)
                dtree2_assignments = convolve(self.dtree2.upper_bound_satisfying_assignments_by_size_without_fact(fact),
                                              [0, 1])
                return add_lists(
                    convolve(dtree1_assignments, self.__create_lost_variables_assignments__(unique_variables2)),
                    convolve(dtree2_assignments, self.__create_lost_variables_assignments__(unique_variables1)))

        else:
            print("Error - false gate")
            return -1

    """
    expansion
    """

    def expand(self):

        if not self.can_expand:
            return False

        if self.gate == DTREE_GATE.Empty_Gate or self.gate is None:
            expended_tree, succeeded = self.dnf.expand()
            if not succeeded:
                self.can_expand = False
                return False
            else:
                self.gate = expended_tree.gate
                self.dtree1 = expended_tree.dtree1
                self.dtree2 = expended_tree.dtree2
                self.dnf = None
                self.current_lower_bound = None
                self.current_upper_bound = None
                self.current_upper_bound_by_size = None
                self.current_lower_bound_by_size = None
                self.hidden_variable = expended_tree.hidden_variable
                self.size = 3
                return True
        else:
            succeeded1 = self.dtree1.expand()
            succeeded2 = self.dtree2.expand()

            self.size = self.dtree1.size + self.dtree2.size + 1
            self.can_expand = succeeded1 or succeeded2
            if succeeded1 or succeeded2:
                self.prev_lower_bound = self.current_lower_bound
                self.prev_upper_bound = self.current_upper_bound
                self.current_lower_bound = None
                self.current_upper_bound = None
                self.current_upper_bound_by_size = None
                self.current_lower_bound_by_size = None
            return succeeded1 or succeeded2

    def hierarchical_expand(self):
        if not self.can_expand:
            return False, False

        if self.gate == DTREE_GATE.Empty_Gate or self.gate is None:
            expended_tree, succeeded, general_can_expand = self.dnf.hierarchical_expand()
            if not general_can_expand:
                self.can_expand = False
            if not succeeded:
                return False, general_can_expand
            else:
                self.gate = expended_tree.gate
                self.dtree1 = expended_tree.dtree1
                self.dtree2 = expended_tree.dtree2
                self.dnf = None
                self.current_lower_bound = None
                self.current_upper_bound = None
                self.lower_bound_dict = {}
                self.upper_bound_dict = {}
                self.current_upper_bound_by_size = None
                self.current_lower_bound_by_size = None
                self.hidden_variable = expended_tree.hidden_variable
                self.size = 3
                return True, general_can_expand
        else:
            succeeded1, general_can_expand1 = self.dtree1.hierarchical_expand()
            succeeded2, general_can_expand2 = self.dtree2.hierarchical_expand()

            self.size = self.dtree1.size + self.dtree2.size + 1
            if succeeded1 or succeeded2:
                self.prev_lower_bound = self.current_lower_bound
                self.prev_upper_bound = self.current_upper_bound
                self.current_lower_bound = None
                self.current_upper_bound = None
                self.lower_bound_dict = {}
                self.upper_bound_dict = {}
                self.current_upper_bound_by_size = None
                self.current_lower_bound_by_size = None
                self.can_expand = general_can_expand1 or general_can_expand2
            return succeeded1 or succeeded2, self.can_expand

    @staticmethod
    def __create_lost_variables_assignments__(lost_vars):
        return [math.comb(lost_vars, i) for i in range(lost_vars + 1)]

    """
    power indices calculations
    """

    def calculate_shapley_for_fact(self, fact):
        var_count = self.variable_count
        assignments_by_size = [int(i) for i in self.critical_assignments_by_size_fact(fact)]

        coefficients = [(int(math.factorial(i)) * int(math.factorial(var_count - i - 1))) for i in range(var_count)]
        shapley_value = sum([int(assignments_by_size[i]) * int(coefficients[i]) for i in
                             range(min(len(assignments_by_size), len(coefficients)))]) / math.factorial(var_count)

        return shapley_value

    def calculate_lower_bound_shapley_fact(self, fact):
        var_count = self.variable_count
        assignments_by_size = [max(int(i), 0) for i in self.lower_bound_critical_assignments_by_size_fact(fact)]

        coefficients = [(int(math.factorial(i)) * int(math.factorial(var_count - i - 1))) for i in range(var_count)]
        shapley_value = sum([int(assignments_by_size[i]) * int(coefficients[i]) for i in
                             range(min(len(assignments_by_size), len(coefficients)))]) / math.factorial(var_count)
        return shapley_value

    def calculate_upper_bound_shapley_fact(self, fact):
        var_count = self.variable_count
        assignments_by_size = [max(int(i), 0) for i in self.upper_bound_critical_assignments_by_size_fact(fact)]

        coefficients = [(int(math.factorial(i)) * int(math.factorial(var_count - i - 1))) for i in range(var_count)]
        shapley_value = sum([int(assignments_by_size[i]) * int(coefficients[i]) for i in
                             range(min(len(assignments_by_size), len(coefficients)))]) / math.factorial(var_count)
        return shapley_value

    def calculate_shapley_dict(self):
        if self.gate == DTREE_GATE.Empty_Gate:
            return self.dnf.calculate_shapley_dict

        elif self.gate == DTREE_GATE.Independent_Or:
            return 2
        return 2  # TODO

    def calculate_slow_banzhaf(self, fact):
        critical_assignments_by_size = self.critical_assignments_by_size_fact(fact)
        return sum(critical_assignments_by_size)

    def calculate_shapley_lower_bound(self, facts):
        var_count = self.variable_count
        coefficients = [(int(math.factorial(i)) * int(math.factorial(var_count - i - 1))) for i in range(var_count)]
        results = {}
        for fact in facts:
            assignments_by_size = [max(int(i), 0) for i in
                                   self.lower_bound_satisfying_assignments_by_size_without_fact(fact)]
            results[fact] = sum(mul_lists(assignments_by_size, coefficients))
        return results

    def calculate_shapley_upper_bound(self, facts):
        var_count = self.variable_count
        coefficients = [(int(math.factorial(i)) * int(math.factorial(var_count - i - 1))) for i in range(var_count)]
        results = {}
        for fact in facts:
            assignments_by_size = [max(int(i), 0) for i in
                                   self.upper_bound_satisfying_assignments_by_size_without_fact(fact)]
            results[fact] = sum(mul_lists(assignments_by_size, coefficients))
        return results
