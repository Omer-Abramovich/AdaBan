import pydot
import time
import math
from DTree import Dtree, DTREE_GATE


class Expansion:
    def __init__(self, dnf):
        self.dtree = Dtree(dnf, DTREE_GATE.Empty_Gate)
        self.size = 1
        self.graph = pydot.Dot(graph_type='graph')

    def expand_once(self):
        expended = self.dtree.expand()
        return expended

    def perform_expansion(self, limit=1000, timeout=3600):
        start = time.time()
        expanding = True
        depth = 0
        while expanding and depth < limit:
            expanding = self.expand_once()
            if time.time() - start > timeout:
                return -1 * depth
            depth += 1

        return depth

    def perform_hierarchical_expansion(self):
        depth = self.dtree.hierarchical_expand()
        return depth

    def calculate_banzahf(self):
        if self.dtree.variable_count == 0:
            return {"expansion_time": 0, "calculation_time": 0, "depth": 0, "banzhaf_values": {}}
        start = time.time()
        depth = self.perform_expansion()
        if depth < 0:
            return {"expansion_time": -1, "calculation_time": 0, "depth": -1 * depth, "banzhaf_values": {}}
        end = time.time()
        expansion_time = end - start
        banzhaf_vals = {}
        start = time.time()
        for fact in self.dtree.variables:
            banzhaf_vals[fact] = self.dtree.critical_assignments_fact(fact)
            mid = time.time()
            if mid - start > 1200:
                return {"expansion_time": expansion_time, "calculation_time": "Failed", "depth": depth,
                        "banzhaf_values": banzhaf_vals}
        end = time.time()
        calc_time = end - start
        return {"expansion_time": expansion_time, "calculation_time": calc_time, "depth": depth,
                "banzhaf_values": banzhaf_vals}

    def calculate_shapley(self):
        if self.dtree.variable_count == 0:
            return {"expansion_time": 0, "calculation_time": 0, "depth": 0, "shapley_values": {}}
        start = time.time()
        depth = self.perform_expansion()
        end = time.time()
        expansion_time = end - start
        shapley_vals = {}
        start = time.time()
        coefficients = [(int(math.factorial(i)) * int(math.factorial(self.dtree.variable_count - i - 1))) for i in
                        range(self.dtree.variable_count)]
        for fact in self.dtree.variables:
            assignments_by_size = [int(i) for i in self.dtree.critical_assignments_by_size_fact(fact)]
            shapley_vals[fact] = sum([int(assignments_by_size[i]) * int(coefficients[i]) for i in
                                      range(min(len(assignments_by_size), len(coefficients)))]) / math.factorial(
                self.dtree.variable_count)
        end = time.time()
        calc_time = end - start
        return {"expansion_time": expansion_time, "calculation_time": calc_time, "depth": depth,
                "shapley_values": shapley_vals}

    def __add_dtree(self, dtree, parent_node, name_suffix):
        node_name = parent_node.get_name() + name_suffix
        if dtree.gate == DTREE_GATE.Empty_Gate:
            node_label = str(dtree.dnf.dnf)
        else:
            node_label = self.__string_for_gate(dtree.gate)

        node = pydot.Node(name=node_name, label=node_label)
        self.graph.add_node(node)
        self.graph.add_edge(pydot.Edge(parent_node, node))

        if dtree.gate != DTREE_GATE.Empty_Gate:
            self.__add_dtree(dtree.dtree1, node, "l")
            self.__add_dtree(dtree.dtree2, node, "r")

    @staticmethod
    def __string_for_gate(gate: DTREE_GATE):
        if gate == DTREE_GATE.Independent_Or:
            return r"$OR$"
        elif gate == DTREE_GATE.Independent_And:
            return r"$AND$"
        elif gate == DTREE_GATE.Exclusive_Or:
            return r"$X$"

    def create_tree_visualisation(self):
        root_node = pydot.Node(name="R", label=self.__string_for_gate(self.dtree.gate))
        self.graph.add_node(root_node)
        self.__add_dtree(self.dtree.dtree1, root_node, "l")
        self.__add_dtree(self.dtree.dtree2, root_node, "r")

        self.graph.write_png("test.png")
