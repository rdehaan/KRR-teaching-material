import clingo
from clingox.reify import reify_program # pylint: disable=E0401

def preprocess_program(program):
    """
    Returns the ASP program in preprocessed form as a string.
    """
    # pylint: disable=R0912,R0914,R0915

    # Reify the program
    reified_symbols = reify_program(
        program,
        calculate_sccs=False,
    )
    reified_program = "".join([
        f"{symbol}.\n"
        for symbol in reified_symbols
    ])

    # Load and ground the reified program
    control = clingo.Control() # pylint: disable=E1101
    control.add("base", [], reified_program)
    control.ground([("base", [])])

    # Find and yield answer sets
    control.configuration.solve.models = 1

    # Initialize data structures to reconstruct the program
    atom_tuples = {}
    literal_tuples = {}
    weighted_literal_tuples = {}
    literal_to_output = {}
    atom_to_output = {}
    rules = []
    show_program = "#show.\n"
    preprocessed_program = ""

    # Find the single answer set, and parse it into our data structures
    with control.solve(yield_=True) as handle:
        for model in handle:
            for atom in model.symbols(atoms=True):
                if atom.name == "atom_tuple" and len(atom.arguments) == 1:
                    tuple_no = atom.arguments[0].number
                    if tuple_no not in atom_tuples:
                        atom_tuples[tuple_no] = []
                elif atom.name == "atom_tuple" and len(atom.arguments) == 2:
                    tuple_no = atom.arguments[0].number
                    argument = atom.arguments[1].number
                    if tuple_no not in atom_tuples:
                        atom_tuples[tuple_no] = []
                    atom_tuples[tuple_no].append(argument)
                elif atom.name == "literal_tuple" and len(atom.arguments) == 1:
                    tuple_no = atom.arguments[0].number
                    if tuple_no not in literal_tuples:
                        literal_tuples[tuple_no] = []
                elif atom.name == "literal_tuple" and len(atom.arguments) == 2:
                    tuple_no = atom.arguments[0].number
                    argument = atom.arguments[1].number
                    if tuple_no not in literal_tuples:
                        literal_tuples[tuple_no] = []
                    literal_tuples[tuple_no].append(argument)
                elif atom.name == "weighted_literal_tuple" and len(atom.arguments) == 1:
                    tuple_no = atom.arguments[0].number
                    if tuple_no not in weighted_literal_tuples:
                        weighted_literal_tuples[tuple_no] = []
                elif atom.name == "weighted_literal_tuple" and len(atom.arguments) == 3:
                    tuple_no = atom.arguments[0].number
                    argument = atom.arguments[1].number
                    weight = atom.arguments[2].number
                    if tuple_no not in weighted_literal_tuples:
                        weighted_literal_tuples[tuple_no] = []
                    weighted_literal_tuples[tuple_no].append((argument, weight))
                elif atom.name == "output":
                    output_name = str(atom.arguments[0])
                    output_literal = atom.arguments[1].number
                    literal_to_output[output_literal] = output_name
                    if output_literal == 0:
                        preprocessed_program += f"{output_name}.\n"
                    show_program += f"#show {output_name} : {output_name}.\n"
                elif atom.name == "rule":
                    head_type = atom.arguments[0].name
                    head_no = atom.arguments[0].arguments[0].number
                    body_type = atom.arguments[1].name
                    body_no = [arg.number for arg in atom.arguments[1].arguments]
                    rules.append((head_type, head_no, body_type, body_no))

    for literal, output in literal_to_output.items():
        if len(literal_tuples[literal]) == 1:
            atom = literal_tuples[literal][0]
            atom_to_output[atom] = output

    def display_atom(atom):
        if atom in atom_to_output:
            return atom_to_output[atom]
        return f"a{atom}"

    def display_literal(literal):
        if literal < 0:
            return f"not {display_atom(-1*literal)}"
        return display_atom(literal)

    def display_weighted_literal(literal, weight):
        return f"{weight},{display_literal(literal)}:{display_literal(literal)}"

    # Go through the rules, and write them out into valid ASP syntax
    for head_type, head_no, body_type, body_no in rules:
        if head_type == "disjunction":
            head_repr = " ; ".join([
                display_atom(atom)
                for atom in atom_tuples[head_no]
            ])
        elif head_type == "choice":
            head_repr = " ; ".join([
                display_atom(atom)
                for atom in atom_tuples[head_no]
            ])
            head_repr = f"{{ {head_repr} }}"
        if body_type == "normal":
            body_repr = ", ".join([
                display_literal(literal)
                for literal in literal_tuples[body_no[0]]
            ])
        elif body_type == "sum":
            body_repr = "; ".join([
                display_weighted_literal(wlit[0], wlit[1])
                for wlit in weighted_literal_tuples[body_no[0]]
            ])
            body_repr = f"#sum {{ {body_repr} }} >= {body_no[1]}"
        if head_repr == "":
            rule_repr = f":- {body_repr}."
        elif body_repr == "":
            rule_repr = f"{head_repr}."
        else:
            rule_repr = f"{head_repr} :- {body_repr}."
        preprocessed_program += f"{rule_repr}\n"

    # Add #show statements
    preprocessed_program += show_program

    return preprocessed_program


def answer_sets(
    program,
    num_models=0,
):
    """
    Iterate over the answer sets of a program,
    in the form of lists of atoms.
    """
    # pylint: disable=no-member

    # Load and ground reified program, together with meta programs
    control = clingo.Control([
        '--project',
        '--warn=none',
    ])
    control.add("base", [], program)
    control.ground([("base", [])])

    control.configuration.solve.models = num_models

    with control.solve(yield_=True) as handle:
        for answer_set in handle:
            atoms = list(answer_set.symbols(shown=True))
            answer_set_str = [
                str(atom) for atom in atoms
            ]
            answer_set_str.sort()
            yield answer_set_str


def print_answer_sets(
    program,
    num_models=0,
):
    """
    Print the answer sets of a program.
    """
    for i, supp_model in enumerate(answer_sets(
        program,
        num_models,
    ), start=1):
        print(f"#{i}:")
        print(f"- Answer set: {{ {', '.join(supp_model)} }}")
        print()


def supported_models(
    program,
    num_models=0,
):
    """
    Iterate over the supported models of a program,
    in the form of lists of atoms.
    """
    # pylint: disable=no-member

    reified_symbols = reify_program(
        program,
        calculate_sccs=False,
    )
    reified_program = "".join([
        f"{symbol}.\n"
        for symbol in reified_symbols
    ])

    meta_program = """
        conjunction(B) :- literal_tuple(B),
            not not hold(L) : literal_tuple(B, L), L > 0;
                not hold(L) : literal_tuple(B,-L), L > 0.

        body(normal(B)) :- rule(_,normal(B)), conjunction(B).
        body(sum(B,G))  :- rule(_,sum(B,G)),
            #sum { W,L : not not hold(L), weighted_literal_tuple(B, L,W), L > 0 ;
                   W,L :     not hold(L), weighted_literal_tuple(B,-L,W), L > 0 } >= G.

          hold(A) : atom_tuple(H,A)   :- rule(disjunction(H),B), body(B).
        { hold(A) : atom_tuple(H,A) } :- rule(     choice(H),B), body(B).

        #show.
        #show model(T) : output(T,B), conjunction(B).
    """

    # Load and ground reified program, together with meta programs
    control = clingo.Control([
        '--project',
        '--warn=none',
    ])
    control.add("base", [], reified_program)
    control.add("base", [], meta_program)
    control.ground([("base", [])])

    control.configuration.solve.models = num_models

    with control.solve(yield_=True) as handle:
        for answer_set in handle:
            atoms = list(answer_set.symbols(shown=True))
            supp_model = [
                str(atom.arguments[0]) for atom in atoms
                if atom.name == "model"
            ]
            supp_model.sort()
            yield supp_model


def print_supported_models(
    program,
    num_models=0,
):
    """
    Print the supported models of a program.
    """
    for i, supp_model in enumerate(supported_models(
        program,
        num_models,
    ), start=1):
        print(f"#{i}:")
        print(f"- Supported model: {{ {', '.join(supp_model)} }}")
        print()


def unfounded_sets(
    program,
    num_models=0,
):
    """
    Iterate over the supported models of a program
    that include an unfounded set,
    in the form of pairs of lists of atoms.
    """
    # pylint: disable=no-member

    reified_symbols = reify_program(
        program,
        calculate_sccs=False,
    )
    reified_program = "".join([
        f"{symbol}.\n"
        for symbol in reified_symbols
    ])

    meta_program = """
        %%% FIRST, SELECT A SUPPORTED MODEL
        conjunction(B) :- literal_tuple(B),
            not not hold(L) : literal_tuple(B, L), L > 0;
                not hold(L) : literal_tuple(B,-L), L > 0.

        body(normal(B)) :- rule(_,normal(B)), conjunction(B).
        body(sum(B,G))  :- rule(_,sum(B,G)),
            #sum { W,L : not not hold(L), weighted_literal_tuple(B, L,W), L > 0 ;
                   W,L :     not hold(L), weighted_literal_tuple(B,-L,W), L > 0 } >= G.

          hold(A) : atom_tuple(H,A)   :- rule(disjunction(H),B), body(B).
        { hold(A) : atom_tuple(H,A) } :- rule(     choice(H),B), body(B).

        #show.
        #show model(T) : output(T,B), conjunction(B).

        %%% THEN, REQUIRE THAT IT CONTAINS A NON-EMPTY UNFOUNDED SET

        % Generate non-empty unfounded set
        1 { unfounded(A) : hold(A) }.

        % Check all rules, distinguishing several cases
        % Case 1: no unfounded atoms in the head
        unfounded_check(rule(disjunction(H),B)) :-
            rule(disjunction(H),B),
            not unfounded(A) : atom_tuple(H,A).
        unfounded_check(rule(choice(H),B)) :-
            rule(choice(H),B),
            not unfounded(A) : atom_tuple(H,A).

        % Case 2: normal body is falsified (possibly by excluding U)
        unfounded_check(rule(H,normal(B))) :-
            rule(H,normal(B)),
            not conjunction(B).
        unfounded_check(rule(H,normal(B))) :-
            rule(H,normal(B)),
            literal_tuple(B,L), unfounded(L).

        % Case 3: sum body is falsified by excluding U
        unfounded_check(rule(H,sum(B,G))) :-
            rule(H,sum(B,G)),
            #sum { W,L : hold(L), not unfounded(L),
                         weighted_literal_tuple(B, L,W), L > 0 ;
                   W,L : not hold(L),
                         weighted_literal_tuple(B,-L,W), L > 0 } < G.

        % Case 4: some atom in disjunctive head not in U is made true
        unfounded_check(rule(disjunction(H),normal(B))) :-
            rule(disjunction(H),normal(B)),
            atom_tuple(H,A), not unfounded(A), hold(A).

        % Check must pass for all rules
        :- rule(H,B), not unfounded_check(rule(H,B)).

        %#show unfounded/1.
        #show unfounded(T) : output(T,B), literal_tuple(B,L), unfounded(L).
    """

    # Load and ground reified program, together with meta programs
    control = clingo.Control([
        '--project',
        '--warn=none',
    ])
    control.add("base", [], reified_program)
    control.add("base", [], meta_program)
    control.ground([("base", [])])

    control.configuration.solve.models = num_models

    with control.solve(yield_=True) as handle:
        for answer_set in handle:
            atoms = list(answer_set.symbols(shown=True))
            supp_model = [
                str(atom.arguments[0]) for atom in atoms
                if atom.name == "model"
            ]
            supp_model.sort()
            unfounded_set = [
                str(atom.arguments[0]) for atom in atoms
                if atom.name == "unfounded"
            ]
            unfounded_set.sort()
            yield supp_model, unfounded_set


def print_unfounded_sets(
    program,
    num_models=0,
):
    """
    Print each pair of a supported model of a program
    and an unfounded set that is included in the model.
    """
    for i, (supp_model, unfounded_set) in enumerate(unfounded_sets(
        program,
        num_models,
    ), start=1):
        print(f"#{i}:")
        print(f"- Supported model: {{ {', '.join(supp_model)} }}")
        print(f"- Unfounded set: {{ {', '.join(unfounded_set)} }}")
        print()
