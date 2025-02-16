from typing import List, Union, Optional, Generic, TypeVar, Tuple, Dict
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
    variables: Tuple[Formula, ...]

@dataclass
class ModusPonens:
    line1: 'Line'
    line2: 'Line'

Reason = Union[ApplyTheorem, ModusPonens]

R = TypeVar('R', bound=Reason)

@dataclass
class Line(Generic[R]):
    formula: Formula
    reason: R


axiom_assertion = Theorem([], [], name='axiom assertion') # special "theorem" that asserts an axiom is true

@dataclass
class Deduction:
    atoms: List[Atom]
    assumptions: List[Formula]
    lines: List[Line]
    name: Optional[str] = None

def remove_duplicate_lines(deduction: Deduction) -> Deduction:
    lines = []
    lines_set = set()
    for line in deduction.lines:
        if line.formula not in lines_set:
            lines.append(line)
            lines_set.add(line.formula)
    return Deduction(deduction.atoms, deduction.assumptions, lines)

def find_modus_ponens(line: Line[ModusPonens], lines: List[Line]) -> Tuple[Line, Line, int]:
    line1 = line.reason.line1
    line2 = line.reason.line2
    line1_no = lines.index(line1)
    line2_no = lines.index(line2)
    return line1, line2, max(line1_no, line2_no)


def print_formula(formula: Formula) -> str:
    if isinstance(formula, Implication):
        return f"({print_formula(formula.left)} -> {print_formula(formula.right)})"
    if isinstance(formula, Atom):
        return formula.name or 'anonymous'
    if isinstance(formula, Negation):
        return f"!{print_formula(formula.statement)}"

    raise ValueError("Invalid formula")

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

def parse_formula(formula: str, subsititon: Dict[str, Formula]) -> Formula:
    """ Wrapper function for parsing a formula string into a tree. """
    parser = Parser(formula)
    
    tree = parser.parse()
    # traverse the tree and replace the atoms with the given substitution
    def substitute(formula: Formula, substitution: Dict[str, Formula]) -> Formula:
        if isinstance(formula, Atom) and formula.name in substitution:
            return substitution[formula.name]
        elif isinstance(formula, Implication):
            return Implication(substitute(formula.left, substitution), substitute(formula.right, substitution))
        elif isinstance(formula, Negation):
            return Negation(substitute(formula.statement, substitution))
        return formula

    return substitute(tree, subsititon)
    


def deduction_theorem_algorithm_step(deduction: Deduction, self_implication: Theorem, A1: Theorem, A2: Theorem) -> Deduction: # self_implication is the theorem that (q -> q)
    # TODO: make this more efficient
    A = deduction.assumptions[-1]
    B = deduction.lines[-1]
    if type(B) == Line[ApplyTheorem]:
        line1 = Line(parse_formula('B -> (A -> B)', {'A': A, 'B': B.formula}), ApplyTheorem(A1, (A, B.formula)))
        line2 = Line(parse_formula('A -> B', {'A': A, 'B': B.formula}), ModusPonens(line1, B))
        return Deduction(deduction.atoms, deduction.assumptions[:-1], deduction.lines + [line1, line2])
    if A == B:
        new_line = Line(parse_formula('A -> A', {'A': A}), ApplyTheorem(self_implication, (A,)))
        return Deduction(deduction.atoms, deduction.assumptions[:-1], deduction.lines + [new_line])
    if isinstance(B.reason, ModusPonens):
        C, CB, line_no = find_modus_ponens(B, deduction.lines)
        AC_theorem = deduction_theorem_algorithm(Deduction(deduction.atoms, deduction.assumptions, deduction.lines[:line_no] + [C]), self_implication, A1, A2)
        AC = AC_theorem.lines[-1]
        ACB_theorem = deduction_theorem_algorithm(Deduction(deduction.atoms, deduction.assumptions, deduction.lines[:line_no] + [CB]), self_implication, A1, A2)
        ACB = ACB_theorem.lines[-1]
        line1 = Line(parse_formula('(A -> CB) -> ((A -> C) -> (A -> B))', {'A': A, 'B': B.formula, 'C': C.formula, 'CB': CB.formula}), ApplyTheorem(A2, (A, C.formula, B.formula)))
        line2 = Line(parse_formula('(A -> C) -> (A -> B)', {'A': A, 'B': B.formula, 'C': C.formula}), ModusPonens(line1, ACB))
        line3 = Line(parse_formula('A -> B', {'A': A, 'B': B.formula}), ModusPonens(line2, AC))
        return Deduction(deduction.atoms, deduction.assumptions[:-1], deduction.lines + AC_theorem.lines + ACB_theorem.lines + [line1, line2, line3])

    raise ValueError("Invalid deduction")

def deduction_theorem_algorithm(deduction: Deduction, self_implication: Theorem, A1: Theorem, A2: Theorem) -> Theorem:
    while deduction.assumptions:
        deduction = deduction_theorem_algorithm_step(deduction, self_implication, A1, A2)
        remove_duplicate_lines(deduction)

    return Theorem(deduction.atoms, deduction.lines)

theorems: Dict[str, Theorem] = {}

lines_ns: Dict[str, Line] = {}

def parse_line(line: str, substitions: Dict[str, Formula]) -> Line:
    # TODO: add debug information
    match = re.match(r'\|- ([A-Za-z0-9_()!-> ]+?) \[(.+)\](?: ==> ([A-Za-z0-9_]+))?', line)
    if not match:
        raise ValueError(f"Invalid line format: {line}")
    
    formula_str, reason_str, line_name = match.groups()
    if line_name is None:
        line_name = None
    
    formula = parse_formula(formula_str, substitions)
    if reason_str.startswith('apply '):
        match = re.match(r'apply ([A-Za-z][A-Za-z0-9_]*?)\((.*?)\)', reason_str)
        if not match:
            raise ValueError(f"Invalid apply theorem format: {reason_str}")
        theorem_name, variables_str = match.groups()
        theorem = theorems[theorem_name]
        variables = []
        for s in variables_str.split(', '):
            if s in substitions:
                variables.append(substitions[s])
            else:
                raise ValueError(f"Unknown variable: {s}")
        # check that the number of variables is correct
        if len(variables) != len(theorem.atoms):
            raise ValueError(f"Invalid number of variables for theorem {theorem_name}")
        reason: Reason = ApplyTheorem(theorem, tuple(variables))
    elif reason_str.startswith('modus_ponens '):
        match = re.match(r'modus_ponens ([A-Za-z0-9_]+), ([A-Za-z0-9_]+)', reason_str)
        if not match:
            raise ValueError(f"Invalid modus ponens format: {reason_str}")
        line1_name, line2_name = match.groups()
        reason = ModusPonens(lines_ns[line1_name], lines_ns[line2_name])
    elif reason_str.strip == 'axiom':
        reason = ApplyTheorem(axiom_assertion, ())
    else:
        raise ValueError(f"Unknown reason: {reason_str}")
    
    parsed_line = Line(formula, reason)
    if line_name is not None:
        substitions[line_name] = parsed_line.formula
    return parsed_line
    
def parse_name(line):
    match = re.match(r'^\s*name\s*=\s*([A-Za-z0-9_]+)\s*$', line)
    if not match:
        raise ValueError(f"Invalid name format: {line}")
    name = match.group(1).strip()
    return Theorem([], [], name=name)
def parse_atom(line):
    match = re.match(r'^\s*var\s+([A-Za-z][A-Za-z0-9_]*)\s*$', line)
    if not match:
        raise ValueError(f"Invalid atoms format: {line}")
    (atom_name, ) = match.group()
    return atom_name, Atom(atom_name)
def parse_assumption(line, variables):
    match = re.match(r'^\s*([A-Za-z0-9_()!-> ]+?) (?: ==> ([A-Za-z0-9_]+))?\s*$', line)
    if not match:
        raise ValueError(f"Invalid assumption format: {line}")
    if not match:
        raise ValueError(f"Invalid line format: {line}")
    
    formula_str, line_name = match.groups()
    if line_name is None:
        line_name = None
    
    assumption = parse_formula(formula_str, variables)
    return assumption

def parse_deduction_file(lines):
    variables = {}
    class Expected(Enum):
        NAME = auto()
        ATOMS = auto()
        ASSUMPTION = auto()
        LINE = auto()
    expected = Expected.NAME

    def parse_line_inner(line):
        return parse_line(line, variables)
    
    for line in lines:
        line = line.strip()
        if not line:
            continue
        if expected == Expected.NAME and not line.startswith('name'):
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
        elif expected == Expected.ATOMS:
            raise ValueError(f"Expected var or assume, got: {line}")
        elif expected == Expected.ASSUMPTION and line.startswith('assume'):
            assumption = parse_assumption(line, variables)
            deduction.assumptions.append(assumption)
        elif expected == Expected.ASSUMPTION:
            raise ValueError(f"Expected assume or |-, got: {line}")
        elif expected == Expected.LINE and line.startswith('|-'):
            line = parse_line_inner(line)
            deduction.lines.append(line)
        elif expected == Expected.LINE:
            raise ValueError(f"Expected line starting with |-, got: {line}")
        else:
            raise ValueError(f"Invalid state: {expected}")
    
            
