"""
Implementation of a DPLL solver, based on on code from
https://github.com/sgomber/CDCL-SAT, where the backjumping and clause learning
features have been disabled.
"""

import time
from collections import OrderedDict

class Statistics:
    """
    Class used to store the various statistics measuerd while solving
    the SAT problem and defines method to print the statistics.
    """

    def __init__(self):
        """
        Constructor for the Statistics class.
        """

        # Input file in which the problem is stored
        self._input_file = ""

        # Result of the SAT solver (SAT or UNSAT)
        self._result = ""

        # Path of the output statistics file used to store
        # the statistics for the solved problem
        self._output_statistics_file = ""

        # Path of the output assignment file which stores the satisfying assignment
        # if the problem is satisfied, it is empty if the problem is UNSAT
        self._output_assignment_file = ""

        # Number of variables in the problem
        self._num_vars = 0

        # Original number of clauses present in the problem
        self._num_orig_clauses = 0

        # Number of original clauses stored
        # (The unary clauses are not stored and are directly used
        # to get the assignment)
        self._num_clauses = 0

        # Number of clauses learned by the solver
        # during the conflict analysis
        self._num_learned_clauses = 0

        # Number of decisions made by the solver
        self._num_decisions = 0

        # Number of implications made by the
        # solver (These are assignments which are
        # not decided but are implied from the decisions)
        self._num_implications = 0

        # Time at which the solver starts solving the problem
        self._start_time = 0

        # Time at which the solver is done reading the problem
        self._read_time = 0

        # Time at which the solver has completed solving the problem
        self._complete_time = 0

        # Time which the solver spend while performing BCP
        self._bcp_time = 0

        # Time which the solver spend while deciding (in _decide method)
        self._decide_time = 0

        # Time which the solver spend while analyzing the conflicts
        self._analyze_time = 0

        # Time which the solver spend while backtracking
        self._backtrack_time = 0

        # Number of restarts
        self._restarts = 0

    def print_stats(self):
        '''
        Method to print the statistics.
        '''

        # Print the stored statistics with appropriate labels
        print("=========================== STATISTICS ===============================")
        print("Solving formula from file: ",self._input_file)
        print("Vars:{}, Clauses:{} Stored Clauses:{}".format(str(self._num_vars),str(self._num_orig_clauses),str(self._num_clauses)))
        print("Input Reading Time: ",self._read_time - self._start_time)
        print("-------------------------------")
        print("Restarts: ",self._restarts)
        print("Learned clauses: ",self._num_learned_clauses)
        print("Decisions made: ",self._num_decisions)
        print("Implications made: ",self._num_implications)
        print("Time taken: ",self._complete_time-self._start_time)
        print("----------- Time breakup ----------------------")
        print("BCP Time: ",self._bcp_time)
        print("Decide Time: ",self._decide_time)
        print("Conflict Analyze Time: ",self._analyze_time)
        print("Backtrack Time: ",self._backtrack_time)
        print("-------------------------------")
        print("RESULT: ",self._result)
        print("Statistics stored in file: ",self._output_statistics_file)

        # Check if the result of the problem is
        # SAT and if it is, then show the
        # assignement file name
        if self._result == "SAT":
            print("Satisfying Assignment stored in file: ",self._output_assignment_file)
        print("======================================================================")


class AssignedNode:
    """
    Class used to store the information about the variables being assigned.

    Public Attributes:
        var: variable that is assigned
        value: value assigned to the variable (True/False)
        level: decision level at which the variable is assigned
        clause: The id of the clause which implies this decision
        index: The index in the assignment stack at which this node is pushed
    """

    def __init__(self,var,value,level,clause):
        '''
        Constructor for the AssignedNode class.

        Arguments:
            var: variable that is assigned
            value: value assigned to the variable (True/False)
            level: decision level at which the variable is assigned
            clause: The id of the clause which implies this decision

        Return:
            initialized AssignedNode object
        '''

        # Variable that is assigned
        self.var = var

        # Value assigned to the variable (True/False)
        self.value = value

        # Level at which the variable is assigned
        self.level = level

        # The index of the clause which implies the variable var
        # If var is decided, this is set to None
        self.clause = clause

        # Index at which a node is placed in the assignment stack
        # Initially it is -1 when node is created and has to be
        # updated when pushed in assignment_stack.
        self.index = -1

    def __str__(self):
        '''
        Method to get the string representation of the AssignedNode object.

        Return:
            a string that has the information about this node
        '''

        return_string = ""

        # return_string += f"Var: {self.var} "
        # return_string += f"Val: {self.value} "
        # return_string += f"Lev: {self.level} "
        # return_string += f"Cls: {self.clause} "
        # return_string += f"Ind: {self.index} "

        lit = self.var
        if not self.value:
            lit = -1 * self.var
        return_string += str(lit).ljust(5)

        return_string += f"\x1b[37m(level: {self.level})\x1b[0m".ljust(10)

        return return_string


class DPLLSolver:
    """
    Class to store the data structures that are maintained while solving the SAT problem.
    It also stores the statistics of the solved problem and the methods that are used to solve the
    SAT problem.

    Public Attributes:
        stats: The statistics object that has the statistics of the solved SAT problem

    Public Methods:
        solve(filename): Takes as argument the filename which has the problem instance in the DIMACS CNF format
        and solves it
    """

    def __init__(self, verbose=True):

        self._num_clauses = 0
        self._num_vars = 0
        self._level = 0
        self._clauses = []
        self._clauses_watched_by_l = {}
        self._literals_watching_c = {}
        self._variable_to_assignment_nodes = {}
        self._assignment_stack = []

        self._verbose = verbose

        self._decider = "ORDERED"
        self._restarter = None
        self.stats = Statistics()


    def _is_negative_literal(self,literal):
        return literal > self._num_vars

    def _get_var_from_literal(self, literal):
        if self._is_negative_literal(literal):
            return literal - self._num_vars
        return literal

    def _get_posneg_var_from_literal(self, literal):
        if self._is_negative_literal(literal):
            return -1 * (literal - self._num_vars)
        return literal


    def _add_clause(self, clause):

        clause = clause[:-1]
        clause = list(OrderedDict.fromkeys(clause))

        if len(clause)==1:
            lit = clause[0]
            value_to_set = True
            if lit[0]=='-':
                value_to_set = False
                var = int(lit[1:])
            else:
                var = int(lit)

            if var not in self._variable_to_assignment_nodes:
                self.stats._num_implications += 1
                node = AssignedNode(var, value_to_set, 0, None)
                self._variable_to_assignment_nodes[var] = node
                self._assignment_stack.append(node)
                node.index = len(self._assignment_stack)-1

                if self._verbose:
                    print("* UP: ".ljust(15), end="")
                    print(node)

                    current_assignment = []
                    for node in self._assignment_stack.copy():
                        if node.value:
                            current_assignment.append(node.var)
                        else:
                            current_assignment.append(-1*node.var)
                    print(f"\x1b[37m  Current assignment: {current_assignment}\x1b[0m")
            else:
                node = self._variable_to_assignment_nodes[var]
                if node.value != value_to_set:
                    self.stats._result = "UNSAT"
                    return 0

            return 1

        clause_with_literals = []

        for lit in clause:
            if lit[0]=='-':
                var = int(lit[1:])
                clause_with_literals.append(var+self._num_vars)
            else:
                var = int(lit)
                clause_with_literals.append(var)

        clause_id = self._num_clauses

        self._clauses.append(clause_with_literals)
        self._num_clauses += 1

        watch_literal1 = clause_with_literals[0]
        watch_literal2 = clause_with_literals[1]

        self._literals_watching_c[clause_id] = [watch_literal1, watch_literal2]

        self._clauses_watched_by_l.setdefault(
            watch_literal1,
            []
        ).append(clause_id)
        self._clauses_watched_by_l.setdefault(
            watch_literal2,
            []
        ).append(clause_id)

        return 1


    def _read_dimacs_cnf_file(self,cnf_filename):

        with open(cnf_filename, "r") as cnf_file:

            for line in cnf_file.readlines():
                line = line.rstrip()
                line = line.split()

                first_word = line[0]

                if first_word == "c":
                    continue

                if first_word == "p":
                    self._num_vars = int(line[2])

                    self.stats._num_orig_clauses = int(line[3])

                else:
                    ret = self._add_clause(line)
                    if ret == 0:
                        break

    def _decide(self):

        if self._decider == "ORDERED":
            var = -1
            for x in range(1, self._num_vars+1):
                if x not in self._variable_to_assignment_nodes:
                    var = x
                    break

            value_to_set = True

        # -1 indicates that the queue is empty
        if var == -1:
            return -1

        self._level += 1

        new_node = AssignedNode(var, value_to_set, self._level, None)
        self._variable_to_assignment_nodes[var] = new_node
        self._assignment_stack.append(new_node)
        new_node.index = len(self._assignment_stack)-1

        self.stats._num_decisions += 1

        if self._verbose:
            print("> Decision: ".ljust(15),end="")
            print(new_node)

            current_assignment = []
            for node in self._assignment_stack.copy():
                if node.value:
                    current_assignment.append(node.var)
                else:
                    current_assignment.append(-1*node.var)
            print(f"\x1b[37m  Current assignment: {current_assignment}\x1b[0m")

        return var


    def _boolean_constraint_propogation(self,is_first_time):
        '''
        Main method that makes all the implications.

        There are two main cases. When it is run for the first time (if is_first_time is True), we can have many
        decisions already made due to the implications by unary clauses and so we have to traverse through all and
        make further implications. So, we start at the 0th index in the assignment list. If is_first_time is False,
        it means that we only have to take the last made decision into account and make the implications and so we
        start from the last node in the assignment stack.

        The implied decisions are pushed into the stack until no more implications can be made and "NO_CONFLICT"
        is returned, or a conflict is detected and in that case "CONFLICT" is returned. If the number of conflicts
        reach a certain limit set by the restart heuristic, then the method returns "RESTART" and restarts the
        solver.

        Parameters:
            is_first_time: Boolean which is set to True when this method is run initially and False for all
            other invocations

        Return:
            "CONFLICT" or "NO_CONFLICT" depending on whether a conflict arised while making the
            implications or not. Returns "RESTART" depending on the number of conflicts encountered
            and the restart strategy used by the solver (if any)
        '''

        last_assignment_pointer = len(self._assignment_stack)-1

        if is_first_time:
            last_assignment_pointer = 0

        while last_assignment_pointer < len(self._assignment_stack):
            last_assigned_node = self._assignment_stack[last_assignment_pointer]
            if last_assigned_node.value:
                literal_that_is_falsed = last_assigned_node.var + self._num_vars
            else:
                literal_that_is_falsed = last_assigned_node.var

            itr = 0

            clauses_watched_by_falsed_literal = \
                self._clauses_watched_by_l.setdefault(
                    literal_that_is_falsed,
                    []
                ).copy()

            clauses_watched_by_falsed_literal.reverse()

            while itr < len(clauses_watched_by_falsed_literal):
                clause_id = clauses_watched_by_falsed_literal[itr]
                watch_list_of_clause = self._literals_watching_c[clause_id]

                other_watch_literal = watch_list_of_clause[0]
                if other_watch_literal == literal_that_is_falsed:
                    other_watch_literal = watch_list_of_clause[1]

                other_watch_var = self._get_var_from_literal(
                    other_watch_literal
                )
                is_negative_other = self._is_negative_literal(
                    other_watch_literal
                )

                if other_watch_var in self._variable_to_assignment_nodes:
                    value_assgned = self._variable_to_assignment_nodes[
                        other_watch_var
                    ].value
                    if (is_negative_other and not value_assgned) or \
                            (not is_negative_other and value_assgned):
                        itr += 1
                        continue

                new_literal_to_watch = -1
                clause = self._clauses[clause_id]

                for lit in clause:
                    if lit not in watch_list_of_clause:
                        var_of_lit = self._get_var_from_literal(lit)

                        if var_of_lit not in self._variable_to_assignment_nodes:
                            new_literal_to_watch = lit
                            break

                        node = self._variable_to_assignment_nodes[
                            var_of_lit
                        ]
                        is_negative = self._is_negative_literal(lit)
                        if (is_negative and not node.value) or \
                                (not is_negative and node.value):
                            new_literal_to_watch = lit
                            break

                if new_literal_to_watch != -1:
                    self._literals_watching_c[clause_id].remove(
                        literal_that_is_falsed
                    )
                    self._literals_watching_c[clause_id].append(
                        new_literal_to_watch
                    )

                    self._clauses_watched_by_l.setdefault(
                        literal_that_is_falsed,
                        []
                    ).remove(clause_id)
                    self._clauses_watched_by_l.setdefault(
                        new_literal_to_watch,
                        []
                    ).append(clause_id)

                else:
                    if other_watch_var not in self._variable_to_assignment_nodes:
                        value_to_set = not is_negative_other

                        assign_var_node = AssignedNode(
                            other_watch_var,
                            value_to_set,
                            self._level,
                            clause_id
                        )
                        self._variable_to_assignment_nodes[
                            other_watch_var
                        ] = assign_var_node

                        self._assignment_stack.append(assign_var_node)
                        assign_var_node.index = len(self._assignment_stack) - 1

                        self.stats._num_implications += 1

                        if self._verbose:
                            print("* UP: ".ljust(15), end="")
                            print(assign_var_node)

                            current_assignment = []
                            for node in self._assignment_stack.copy():
                                if node.value:
                                    current_assignment.append(node.var)
                                else:
                                    current_assignment.append(-1*node.var)
                            print(f"\x1b[37m  Current assignment: {current_assignment}\x1b[0m")
                    else:

                        conflict_node = AssignedNode(
                            None,
                            None,
                            self._level,
                            clause_id
                        )
                        self._assignment_stack.append(conflict_node)

                        conflict_node.index = len(self._assignment_stack)-1

                        # if self._verbose:
                        #     print("CONFLICT")

                        return "CONFLICT"

                itr += 1

            last_assignment_pointer += 1

        return "NO_CONFLICT"


    def _resolve(self, clause1, clause2, var):
        full_clause = clause1 + clause2
        full_clause = list(OrderedDict.fromkeys(full_clause))
        full_clause.remove(var)
        full_clause.remove(var + self._num_vars)
        return full_clause


    def _is_asserting_clause(self,clause,level):
        counter = 0
        maxi = -1
        cand = -1

        for lit in clause:
            var = self._get_var_from_literal(lit)
            node = self._variable_to_assignment_nodes[var]

            if node.level == level:
                counter += 1

                if node.index > maxi:
                    maxi = node.index
                    cand = node

        return counter == 1, cand


    def _get_backtrack_level(self, conflict_clause, conflict_level):
        maximum_level_before_conflict_level = -1

        literal_at_conflict_level = -1

        for lit in conflict_clause:
            var = self._get_var_from_literal(lit)
            assigned_node = self._variable_to_assignment_nodes[var]

            if assigned_node.level == conflict_level:
                literal_at_conflict_level = lit
            else:
                if assigned_node.level > maximum_level_before_conflict_level:
                    maximum_level_before_conflict_level = assigned_node.level

        return maximum_level_before_conflict_level, literal_at_conflict_level


    def _find_backtrack(self):
        '''
        Method that is called when a conflict occurs during the
        Boolean Constrain Propogation (BCP). It analyzes the conflict,
        generates the valid conflict clause (as discussed above) and adds
        it to the clause database. It then returns the backtrack level
        and the assignment node implied by the conflict clause that will be used
        for implications once the solver backtracks (described below in the algorithm).

        Parameters:
            None

        Return:
            the level to which the solver should jump back and
            the assignement node implied by the conflict clause
        '''

        assigment_stack_pointer = len(self._assignment_stack)-1

        conflict_node = self._assignment_stack[assigment_stack_pointer]
        conflict_level = conflict_node.level

        if conflict_level == 0:
            return -1, None

        backtrack_level = conflict_level - 1

        backtrack_node = None
        while True:
            assigment_stack_pointer -= 1
            if assigment_stack_pointer < 0:
                break
            node = self._assignment_stack[assigment_stack_pointer]
            if node.level == conflict_level:
                backtrack_node = node
            else:
                break

        node_to_add = AssignedNode(
            backtrack_node.var,
            not backtrack_node.value,
            backtrack_level,
            None
        )

        self._assignment_stack.pop()

        if self._verbose:
            print("= \x1b[31mCONFLICT!\x1b[0m")
            print("\x1b[34m< Backtracking to level " + \
                f"{backtrack_level}\x1b[0m")
            print("* Propagated: ".ljust(15), end="")
            print(node_to_add)

            # current_assignment = []
            # for node in self._assignment_stack.copy():
            #     if node.value:
            #         current_assignment.append(node.var)
            #     else:
            #         current_assignment.append(-1*node.var)
            # print(f"\x1b[37m  Current assignment: {current_assignment}\x1b[0m")

        return backtrack_level, node_to_add

        # print(f"assignment_stack: {[(node.var, node.value, node.level) for node in self._assignment_stack.copy()]}")

        assigment_stack_pointer = len(self._assignment_stack)-1

        conflict_node = self._assignment_stack[assigment_stack_pointer]
        conflict_level = conflict_node.level
        conflict_clause = self._clauses[conflict_node.clause]

        self._assignment_stack.pop()



        while True:
            is_asserting, prev_assigned_node = \
                self._is_asserting_clause(conflict_clause, conflict_level)

            if is_asserting:
                break

            clause = self._clauses[prev_assigned_node.clause]
            var = prev_assigned_node.var
            conflict_clause = self._resolve(conflict_clause, clause, var)

        if self._verbose:
            print(
                "= \x1b[31mCONFLICT!\x1b[0m Learned clause:\x1b[34m",
                [self._get_posneg_var_from_literal(lit) for lit in conflict_clause],
                "\x1b[0m"
            )

        if len(conflict_clause) > 1:
            self.stats._num_learned_clauses += 1
            clause_id = self._num_clauses

            self._num_clauses += 1
            self._clauses.append(conflict_clause)

            self._clauses_watched_by_l.setdefault(
                conflict_clause[0],
                []
            ).append(clause_id)
            self._clauses_watched_by_l.setdefault(
                conflict_clause[1],
                []
            ).append(clause_id)

            self._literals_watching_c[clause_id] = [
                conflict_clause[0],
                conflict_clause[1]
            ]

            backtrack_level, conflict_level_literal = \
                self._get_backtrack_level(conflict_clause,conflict_level)

            conflict_level_var = self._get_var_from_literal(
                conflict_level_literal
            )

            is_negative_conflict_lit = \
                self._is_negative_literal(conflict_level_literal)

            value_to_set = True
            if is_negative_conflict_lit:
                value_to_set = False

            node = AssignedNode(
                conflict_level_var,
                value_to_set,
                backtrack_level,
                clause_id
            )

            if self._verbose:
                print(f"\x1b[37m< Backjumping to level " + \
                    f"{backtrack_level}\x1b[0m")
                propagated_lit = (-1 if is_negative_conflict_lit else 1) * \
                    conflict_level_var
                print("* UP: ".ljust(15), end="")
                print(node)

                current_assignment = []
                for node in self._assignment_stack.copy():
                    if node.value:
                        current_assignment.append(node.var)
                    else:
                        current_assignment.append(-1*node.var)
                print(f"\x1b[37m  Current assignment: {current_assignment}\x1b[0m")

            return backtrack_level, node

        else:
            literal = conflict_clause[0]
            var = self._get_var_from_literal(literal)
            is_negative_literal = self._is_negative_literal(literal)

            assigned_node = self._variable_to_assignment_nodes[var]

            backtrack_level = 0

            value_to_set = True
            if is_negative_literal:
                value_to_set = False

            node = AssignedNode(
                var,
                value_to_set,
                backtrack_level,
                None
            )

            return backtrack_level, node


    def _backtrack(self, backtrack_level, node_to_add):
        self._level = backtrack_level

        itr = len(self._assignment_stack)-1
        while True:
            if itr < 0:
                break
            if self._assignment_stack[itr].level <= backtrack_level:
                break
            else:
                del self._variable_to_assignment_nodes[
                    self._assignment_stack[itr].var
                ]

                node = self._assignment_stack.pop(itr)

                del node
                itr -= 1

        if node_to_add:
            self._variable_to_assignment_nodes[node_to_add.var] = node_to_add

            self._assignment_stack.append(node_to_add)
            node_to_add.index = len(self._assignment_stack)-1

            self.stats._num_implications += 1

        if self._verbose:
            current_assignment = []
            for node in self._assignment_stack.copy():
                if node.value:
                    current_assignment.append(node.var)
                else:
                    current_assignment.append(-1*node.var)
            print(f"\x1b[37m  Current assignment: {current_assignment}\x1b[0m")


    def solve(self, cnf_filename):

        self.stats._input_file = cnf_filename
        self.stats._start_time = time.time()

        self._read_dimacs_cnf_file(cnf_filename)

        self.stats._read_time = time.time()

        self.stats._num_vars = self._num_vars
        self.stats._num_clauses = self._num_clauses

        if self.stats._result == "UNSAT":
            self.stats._complete_time = time.time()

        else:
            first_time = True
            while True:
                while True:

                    temp = time.time()
                    result = self._boolean_constraint_propogation(first_time)
                    self.stats._bcp_time += time.time()-temp

                    if result == "NO_CONFLICT":
                        break

                    first_time = False

                    temp = time.time()
                    backtrack_level, node_to_add = self._find_backtrack()
                    self.stats._analyze_time += time.time()-temp

                    if backtrack_level == -1:
                        print("\x1b[91mUNSAT\x1b[0m")
                        self.stats._result = "UNSAT"
                        self.stats._complete_time = time.time()
                        break

                    temp = time.time()
                    self._backtrack(backtrack_level, node_to_add)
                    self.stats._backtrack_time += time.time() - temp

                if self.stats._result == "UNSAT":
                    break

                first_time = False
                temp = time.time()
                var_decided = self._decide()
                self.stats._decide_time += time.time()-temp

                if var_decided == -1:
                    print("\x1b[32mSAT\x1b[0m")
                    self.stats._result = "SAT"
                    self.stats._complete_time = time.time()
                    break
