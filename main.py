from typing import List, Union, Optional, Generic, TypeVar, Tuple, Dict, Iterator
from enum import Enum, auto
from dataclasses import dataclass
import re


@dataclass
class Implication:
    left: 'Formula'
    right: 'Formula'

@dataclass
class Atom:
    name: Optional[str] = None

@dataclass
class Negation:
    statement: 'Formula'

Formula = Union[Implication, Atom, Negation]

@dataclass
class Theorem:
    atoms: List[Atom]
    lines: List['Line']
    name: Optional[str] = None

@dataclass
class ApplyTheorem:
    theorem: Theorem
    parameters: Tuple[Formula, ...]

@dataclass
class ModusPonens:
    line1: 'Formula'
    line2: 'Formula'

Reason = Union[ApplyTheorem, ModusPonens]

R = TypeVar('R', bound=Reason)

@dataclass
class Line(Generic[R]):
    formula: Formula
    reason: R


axiom_assertion = Theorem([], [], name='axiom assertion') # special "theorem" that asserts an axiom is true
assumption_assertion = Theorem([], [], name='assumption assertion') # special theorem so that I can add the assumptions to the list of lines, make applying modus ponens easier

@dataclass
class Deduction:
    atoms: List[Atom]
    assumptions: List[Formula]
    lines: List[Line]
    name: Optional[str] = None

def remove_duplicate_lines(deduction: Deduction) -> Deduction:
    #TODO
    return deduction

def find_modus_ponens(line: Line[ModusPonens], lines: List[Line]) -> Tuple[Line, Line, int]:
    line1 = line.reason.line1
    line2 = line.reason.line2
    line1_no = None
    line2_no = None
    for i, ll in enumerate(lines):
        if ll.formula == line1:
            line1_no = i
        if ll.formula == line2:
            line2_no = i
    if line1_no is None or line2_no is None:
        raise ValueError("Invalid deduction")
    return lines[line1_no], lines[line2_no], max(line1_no, line2_no)

def print_formula_no_sub(formula: Formula, variables_lookup: Dict[int, str]) -> str:
    if isinstance(formula, Implication):
        return f"({print_formula_no_sub(formula.left, variables_lookup)} -> {print_formula_no_sub(formula.right, variables_lookup)})"
    if isinstance(formula, Atom):
        return variables_lookup.get(id(formula), f'(name={Atom.name})')
    if isinstance(formula, Negation):
        return f"!{print_formula_no_sub(formula.statement, variables_lookup)}"

    raise ValueError("Invalid formula")

def print_formula(formula: Formula, variables_lookup: Dict[int, str]) -> str:
    if id(formula) in variables_lookup:
        return variables_lookup[id(formula)]
    if isinstance(formula, Implication):
        return f"({print_formula(formula.left, variables_lookup)} -> {print_formula(formula.right, variables_lookup)})"
    if isinstance(formula, Atom):
        return variables_lookup.get(id(formula), f'(name={Atom.name})')
    if isinstance(formula, Negation):
        return f"!{print_formula(formula.statement, variables_lookup)}"


class Parser:
    def __init__(self, formula: str):
        self.tokens: List[str] = self.tokenize(formula)
        self.pos: int = 0

    def tokenize(self, formula: str) -> List[str]:
        """ Tokenizes the input formula into meaningful components. """
        token_pattern = r'->|!|\(|\)|[A-Za-z][A-Za-z0-9_]*'
        tokens = re.findall(token_pattern, formula)
        remaining = re.sub(token_pattern, '', formula)
        if remaining.strip():
            raise ValueError("Invalid characters in formula")
        return tokens

    def peek(self) -> Optional[str]:
        """ Returns the current token without consuming it. """
        return self.tokens[self.pos] if self.pos < len(self.tokens) else None

    def consume(self) -> str:
        """ Consumes and returns the current token, moving to the next. """
        if self.pos >= len(self.tokens):
            raise ValueError("Unexpected end of input")
        token = self.tokens[self.pos]
        self.pos += 1
        return token

    def parse(self) -> Formula:
        tree = self.parse_implication()
        if self.peek() is not None:
            raise ValueError(f"Unexpected token at position {self.pos}: {self.peek()}")
        return tree

    def parse_implication(self) -> Formula:
        """ Parses implications with lower precedence than negation. """
        left = self.parse_negation()
        while self.peek() == "->":
            self.consume()
            right = self.parse_implication()
            left = Implication(left, right)
        return left

    def parse_negation(self) -> Formula:
        """ Parses negations, which have higher precedence than implications. """
        if self.peek() == "!":
            self.consume()
            return Negation(self.parse_negation())
        return self.parse_primary()

    def parse_primary(self) -> Formula:
        """ Parses atomic formulas and parenthesized expressions. """
        if self.peek() == "(":
            self.consume()
            expr = self.parse_implication()
            assert self.consume() == ")", "Mismatched parentheses"
            return expr
        return self.parse_atom()

    def parse_atom(self) -> Formula:
        """ Parses atomic propositions. """
        token = self.consume()
        assert re.match(r"^[A-Za-z][A-Za-z0-9_]*$", token), f"Invalid atom name: {token}"
        return Atom(token)

def parse_formula(formula: str, variables: Dict[str, Formula]) -> Formula:
    """ Wrapper function for parsing a formula string into a tree. """
    parser = Parser(formula)
    
    tree = parser.parse()
    # traverse the tree and replace the atoms with the given substitution
    def substitute(formula: Formula, variables: Dict[str, Formula]) -> Formula:
        if isinstance(formula, Atom) and formula.name in variables:
            return variables[formula.name]
        elif isinstance(formula, Implication):
            return Implication(substitute(formula.left, variables), substitute(formula.right, variables))
        elif isinstance(formula, Negation):
            return Negation(substitute(formula.statement, variables))
        return formula

    return substitute(tree, variables)

def theorem_printer(theorem: Theorem, variables: Dict[str, Formula]):
    counter = 1
    lookup_table: Dict[int, str] = {}
    for name, formula in variables.items():
        lookup_table[id(formula)] = name
    for line in theorem.lines:
        formula_str = print_formula_no_sub(line.formula, lookup_table)
        if id(line.formula) in lookup_table:
            formula_name = lookup_table[id(line.formula)]
        else:
            formula_name = f"t{counter}"
            counter += 1
            lookup_table[id(line.formula)] = formula_name
        if isinstance(line.reason, ApplyTheorem):
            parameter_names = []
            for parameter in line.reason.parameters:
                if id(parameter) in lookup_table:
                    parameter_names.append(lookup_table[id(parameter)])
                else:
                    parameter_names.append(print_formula(parameter, lookup_table))
            theorem_name = line.reason.theorem.name
            yield f"|- {formula_str} [apply {theorem_name}({', '.join(parameter_names)})] ==> {formula_name}"
        elif isinstance(line.reason, ModusPonens):
            line1 = line.reason.line1
            line2 = line.reason.line2
            line1_name = lookup_table[id(line1)] # if it is not in the lookup table, something had gone wrong before
            line2_name = lookup_table[id(line2)]
            yield f"|- {formula_str} [modus_ponens {line1_name} {line2_name}] ==> {formula_name}"

def deduction_theorem_algorithm_step(deduction: Deduction, self_implication: Theorem, A1: Theorem, A2: Theorem) -> Deduction: # self_implication is the theorem that (q -> q)
    # TODO: make this more efficient
    A = deduction.assumptions[-1]
    B = deduction.lines[-1]
    if A == B.formula:
        new_line = Line(parse_formula('A -> A', {'A': A}), ApplyTheorem(self_implication, (A,)))
        return Deduction(deduction.atoms, deduction.assumptions[:-1], deduction.lines[:len(deduction.assumptions)-1] + deduction.lines[len(deduction.assumptions):-1] + [new_line])

    if isinstance(B.reason, ApplyTheorem):
        line1 = Line(parse_formula('B -> (A -> B)', {'A': A, 'B': B.formula}), ApplyTheorem(A1, (A, B.formula)))
        line2 = Line(parse_formula('A -> B', {'A': A, 'B': B.formula}), ModusPonens(line1.formula, B.formula))
        # since we did not use the assumption, we remove it from the list of Lines as well
        return Deduction(deduction.atoms, deduction.assumptions[:-1], deduction.lines[:len(deduction.assumptions)-1] + deduction.lines[len(deduction.assumptions):-1] + [line1, line2])
    if isinstance(B.reason, ModusPonens):
        CB, C, line_no = find_modus_ponens(B, deduction.lines)

        AC_theorem = deduction_theorem_algorithm(Deduction(deduction.atoms, deduction.assumptions, deduction.lines[:line_no] + [C]), self_implication, A1, A2)
        AC = AC_theorem.lines[-1]
        ACB_theorem = deduction_theorem_algorithm(Deduction(deduction.atoms, deduction.assumptions, deduction.lines[:line_no] + [CB]), self_implication, A1, A2)
        ACB = ACB_theorem.lines[-1]
        line1 = Line(parse_formula('(ACB) -> ((AC) -> (A -> B))', {'ACB': ACB.formula, 'A': A, 'B': B.formula, 'AC': AC.formula}), ApplyTheorem(A2, (A, C.formula, B.formula)))
        line2 = Line(parse_formula('(A -> C) -> (A -> B)', {'A': A, 'B': B.formula, 'C': C.formula}), ModusPonens(line1.formula, ACB.formula))
        line3 = Line(parse_formula('A -> B', {'A': A, 'B': B.formula}), ModusPonens(line2.formula, AC.formula))
        return Deduction(deduction.atoms, deduction.assumptions[:-1], deduction.lines[:len(deduction.assumptions)-1] + deduction.lines[len(deduction.assumptions):-1] + AC_theorem.lines + ACB_theorem.lines + [line1, line2, line3])

    raise ValueError("Invalid deduction")

def deduction_theorem_algorithm(deduction: Deduction, self_implication: Theorem, A1: Theorem, A2: Theorem) -> Theorem:
    while deduction.assumptions:
        deduction = deduction_theorem_algorithm_step(deduction, self_implication, A1, A2)
        remove_duplicate_lines(deduction)

    return Theorem(deduction.atoms, deduction.lines)

def parse_line(line: str, variables: Dict[str, Formula], theorems: Dict[str, Theorem]) -> Line:
    # TODO: add debug information
    match = re.match(r'\|- ([A-Za-z0-9_()!-> ]+?) \[(.+)\](?: ==> ([A-Za-z0-9_]+))?', line)
    if not match:
        raise ValueError(f"Invalid line format: {line}")
    
    formula_str, reason_str, line_name = match.groups()

    formula = parse_formula(formula_str, variables)
    reason = parse_reason(reason_str, variables, theorems)
    parsed_line = Line(formula, reason)
    if line_name is not None:
        variables[line_name] = formula
    return parsed_line

def parse_reason(reason_str: str, variables: Dict[str, Formula], theorems: Dict[str, Theorem]) -> Reason:
    if reason_str.startswith('apply '):
        match = re.match(r'^\s*apply ([A-Za-z][A-Za-z0-9_]*?)\((.*?)\)\s*$', reason_str)
        if not match:
            raise ValueError(f"Invalid apply theorem format: {reason_str}")
        theorem_name, variables_str = match.groups()
        theorem = theorems[theorem_name]
        parameters = []
        for s in variables_str.split(','):
            parameters.append(parse_formula(s, variables))
        # check that the number of variables is correct
        if len(parameters) != len(theorem.atoms):
            raise ValueError(f"Invalid number of variables for theorem {theorem_name}")
        reason: Reason = ApplyTheorem(theorem, tuple(parameters))
    elif reason_str.startswith('modus_ponens '):
        match = re.match(r'\s*modus_ponens ([A-Za-z0-9_]+)\s+([A-Za-z0-9_]+)\s*', reason_str)
        if not match:
            raise ValueError(f"Invalid modus ponens format: {reason_str}")
        line1_name, line2_name = match.groups()
        reason = ModusPonens(variables[line1_name], variables[line2_name])
    elif reason_str.strip() == 'axiom':
        reason = ApplyTheorem(axiom_assertion, ())
    else:
        raise ValueError(f"Unknown reason: {reason_str}")
    return reason


def parse_name(line):
    match = re.match(r'^\s*name\s+([A-Za-z0-9_]+)\s*$', line)
    if not match:
        raise ValueError(f"Invalid name format: {line}")
    (name, ) = match.groups()
    return name
def parse_atom(line):
    match = re.match(r'^\s*var\s+([A-Za-z][A-Za-z0-9_]*)\s*$', line)
    if not match:
        raise ValueError(f"Invalid atoms format: {line}")
    (atom_name, ) = match.groups()
    return atom_name, Atom(atom_name)
def parse_assumption(line, variables):
    match = re.match(r'^\s*assume\s+([A-Za-z0-9_()!-> ]+?)(?: ==> ([A-Za-z0-9_]+))?\s*$', line)
    if not match:
        raise ValueError(f"Invalid assumption format: {line}")
    if not match:
        raise ValueError(f"Invalid line format: {line}")
    
    formula_str, line_name = match.groups()
    formula = parse_formula(formula_str, variables)

    if line_name is not None:
        variables[line_name] = formula
    
    assumption = parse_formula(formula_str, variables)
    return assumption

def parse_deduction_file(lines, theorems: Dict[str, Theorem]):
    variables: Dict[str, Atom] = {}
    class Expected(Enum):
        NAME = auto()
        ATOMS = auto()
        ASSUMPTION = auto()
        LINE = auto()
    expected = Expected.NAME

    def parse_line_inner(line):
        return parse_line(line, variables, theorems)
    
    name = None
    deduction = Deduction([], [], [])
    for line in lines:
        line = line.strip()
        if not line:
            continue
        if expected == Expected.NAME and not line.startswith('name'):
            if name is None:
                raise ValueError(f"Expected name, got: {line}")
            expected = Expected.ATOMS
        if expected == Expected.ATOMS and not line.startswith('var'):
            expected = Expected.ASSUMPTION
        if expected == Expected.ASSUMPTION and not line.startswith('assume'):
            expected = Expected.LINE
        if expected == Expected.LINE and not line.startswith('|-'):
            raise ValueError(f"Expected line starting with |-: {line}")
        
        if expected == Expected.NAME and line.startswith('name'):
            name = parse_name(line)
            deduction = Deduction([], [], [], name=name)
        elif expected == Expected.NAME:
            raise ValueError(f"Expected name or var, got: {line}")
        elif expected == Expected.ATOMS and line.startswith('var'):
            atom_name, atom = parse_atom(line)
            variables[atom_name] = atom
            deduction.atoms.append(atom)
        elif expected == Expected.ATOMS:
            raise ValueError(f"Expected var or assume, got: {line}")
        elif expected == Expected.ASSUMPTION and line.startswith('assume'):
            assumption = parse_assumption(line, variables)
            deduction.assumptions.append(assumption)
            deduction.lines.append(Line(assumption, ApplyTheorem(assumption_assertion, ())))
        elif expected == Expected.ASSUMPTION:
            raise ValueError(f"Expected assume or |-, got: {line}")
        elif expected == Expected.LINE and line.startswith('|-'):
            line = parse_line_inner(line)
            deduction.lines.append(line)
        elif expected == Expected.LINE:
            raise ValueError(f"Expected line starting with |-, got: {line}")
        else:
            raise ValueError(f"Invalid state: {expected}")
    return deduction, variables



theorems: Dict[str, Theorem] = {}

with open('lib/A1.txt', 'r', encoding='utf-8') as f:
    deduction, variables = parse_deduction_file(f, theorems)
    theorems[deduction.name] = deduction

with open('lib/A2.txt', 'r', encoding='utf-8') as f:
    deduction, variables = parse_deduction_file(f, theorems)
    theorems[deduction.name] = deduction

with open('lib/A3.txt', 'r', encoding='utf-8') as f:
    deduction, variables = parse_deduction_file(f, theorems)
    theorems[deduction.name] = deduction


with open('lib/self-implication.txt', 'r', encoding='utf-8') as f:
    deduction, variables = parse_deduction_file(f, theorems)
    theorems[deduction.name] = deduction

with open('lib/a-not-everything.txt', 'r', encoding='utf-8') as f:
    deduction, variables = parse_deduction_file(f, theorems)
    theorems[deduction.name] = deduction
    result = deduction_theorem_algorithm(deduction, theorems['self_implication'], theorems['A1'], theorems['A2'])
    for line in theorem_printer(result, variables):
        print(line)