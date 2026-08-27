#!/usr/bin/env python3
"""Small formula parser for MVP arithmetic expressions."""

import re
from typing import List, Optional, Tuple, Dict, Any


class ASTNode:
    """Base class for AST nodes"""
    pass


class Num(ASTNode):
    """Numeric literal node"""
    def __init__(self, value: int, is_float: bool = False):
        self.value = value
        self.is_float = is_float

    def __repr__(self):
        return "Num(" + str(self.value) + ")"


class Var(ASTNode):
    """Variable node"""
    def __init__(self, name: str):
        self.name = name

    def __repr__(self):
        return "Var('" + self.name + "')"


class Neg(ASTNode):
    """Unary negation node"""
    def __init__(self, expr: ASTNode):
        self.expr = expr

    def __repr__(self):
        return "Neg(" + str(self.expr) + ")"


class BinOp(ASTNode):
    """Binary operation node"""
    def __init__(self, left: ASTNode, op: str, right: ASTNode):
        self.left = left
        self.op = op
        self.right = right

    def __repr__(self):
        return "BinOp(" + str(self.left) + ", '" + self.op + "', " + str(self.right) + ")"


class Eq(ASTNode):
    """Equality node"""
    def __init__(self, left: ASTNode, right: ASTNode):
        self.left = left
        self.right = right

    def __repr__(self):
        return "Eq(" + str(self.left) + ", " + str(self.right) + ")"


class Ne(ASTNode):
    """Inequality/Not-equal node"""
    def __init__(self, left: ASTNode, right: ASTNode):
        self.left = left
        self.right = right

    def __repr__(self):
        return "Ne(" + str(self.left) + ", " + str(self.right) + ")"


class Lt(ASTNode):
    """Less-than node"""
    def __init__(self, left: ASTNode, right: ASTNode):
        self.left = left
        self.right = right

    def __repr__(self):
        return "Lt(" + str(self.left) + ", " + str(self.right) + ")"


class Le(ASTNode):
    """Less-or-equal node"""
    def __init__(self, left: ASTNode, right: ASTNode):
        self.left = left
        self.right = right

    def __repr__(self):
        return "Le(" + str(self.left) + ", " + str(self.right) + ")"


class Gt(ASTNode):
    """Greater-than node"""
    def __init__(self, left: ASTNode, right: ASTNode):
        self.left = left
        self.right = right

    def __repr__(self):
        return "Gt(" + str(self.left) + ", " + str(self.right) + ")"


class Ge(ASTNode):
    """Greater-or-equal node"""
    def __init__(self, left: ASTNode, right: ASTNode):
        self.left = left
        self.right = right

    def __repr__(self):
        return "Ge(" + str(self.left) + ", " + str(self.right) + ")"


class Forall(ASTNode):
    """Forall quantifier node"""
    def __init__(self, var: str, body: ASTNode):
        self.var = var
        self.body = body

    def __repr__(self):
        return "Forall('" + self.var + "', " + str(self.body) + ")"


class Exists(ASTNode):
    """Exists quantifier node"""
    def __init__(self, var: str, body: ASTNode):
        self.var = var
        self.body = body

    def __repr__(self):
        return "Exists('" + self.var + "', " + str(self.body) + ")"


class Imp(ASTNode):
    """Implication node"""
    def __init__(self, left: ASTNode, right: ASTNode):
        self.left = left  # antecedent
        self.right = right  # consequent

    def __repr__(self):
        return "Imp(" + str(self.left) + ", " + str(self.right) + ")"


def normalize_implicit_multiplication_expression(expr: str) -> str:
    """Normalize implicit multiplication in a raw expression string.
    
    Handles cases like:
    - '2a' -> '2 * a' (number followed by variable)
    - 'ab' -> 'a * b' (two single-letter variables)
    - 'a2' -> 'a * 2' (variable followed by number)
    - '2ab' -> '2 * a * b' (number followed by chain of variables)
    - '3xyz' -> '3 * x * y * z' (number followed by multi-letter chain)
    - '(a+b)2' -> '(a+b) * 2' (paren followed by number)
    - '(a+b)(c+d)' -> '(a+b) * (c+d)' (paren followed by paren)
    - '2(a+b)' -> '2 * (a+b)' (number followed by paren)
    - 'a(b+c)' -> 'a * (b+c)' (variable followed by paren)
    """
    result = expr
    
    # Replace ** with ^ for power
    result = result.replace('**', '^')
    
    # Handle ) followed by various tokens
    result = re.sub(r'\)(\d)', r') * \1', result)
    result = re.sub(r'\)([a-zA-Z])', r') * \1', result)
    result = re.sub(r'\)\(', r') * (', result)
    
    # Handle letter or digit followed by (
    result = re.sub(r'([a-zA-Z])\(', r'\1 * (', result)
    result = re.sub(r'(\d)\(', r'\1 * (', result)
    
    # Handle number followed by multi-letter lowercase chain: "3xyz" -> "3 * x * y * z"
    def _split_chain(match):
        num = match.group(1)
        letters = match.group(2)
        return num + ' * ' + ' * '.join(letters)
    result = re.sub(r'(\d+)([a-z]{2,})(?![a-zA-Z])', _split_chain, result)
    
    # Pattern: number followed by single variable (e.g., "2a", "3x")
    changed = True
    while changed:
        changed = False
        new_result = re.sub(r'(\d)([a-zA-Z])', r'\1 * \2', result)
        if new_result != result:
            changed = True
        result = new_result
    
    # Pattern: variable followed by number (e.g., "a2", "xb")
    changed = True
    while changed:
        changed = False
        new_result = re.sub(r'([a-zA-Z])(\d)(?!\w)', r'\1 * \2', result)
        if new_result != result:
            changed = True
        result = new_result
    
    # Pattern: single lowercase letter followed by single lowercase letter
    # (e.g., "ab" -> "a * b", but not "Nat" -> "N * a * t")
    changed = True
    while changed:
        changed = False
        new_result = re.sub(r'(?<![a-zA-Z])([a-z])([a-z])(?![a-zA-Z])', r'\1 * \2', result)
        if new_result != result:
            changed = True
        result = new_result
    
    return result


def tokenize(expression: str) -> List[str]:
    """Tokenize a mathematical expression string into tokens."""
    # First, normalize implicit multiplication in the raw string
    expr = normalize_implicit_multiplication_expression(expression)
    
    # Now replace LaTeX-like tokens
    replacements = [
        (r'\\cdot', '*'),
        (r'\\le', '<='),
        (r'\\ge', '>='),
        (r'\\neq', '!='),
    ]
    
    for pattern, replacement in replacements:
        expr = re.sub(pattern, replacement, expr)
    
    # Token pattern: numbers, variables, operators, parentheses
    token_pattern = r'''
        \d+                  # integers
        | [a-zA-Z_]\w*(?:\.[a-zA-Z_]\w*)*   # variables/identifiers (dotted like Nat.succ)
        | [+\-*/^=!<>]       # operators
        | \(|\)              # parentheses
        | <=|>=|!=           # multi-char operators
    '''
    
    tokens = re.findall(token_pattern, expr, re.VERBOSE)
    return tokens


def normalize_implicit_multiplication(tokens: List[str]) -> List[str]:
    """Normalize implicit multiplication like '2ab' -> '2 * a * b'."""
    normalized = []
    i = 0
    while i < len(tokens):
        token = tokens[i]
        normalized.append(token)
        
        # Check if next token should be multiplied implicitly
        if i + 1 < len(tokens):
            next_token = tokens[i + 1]
            should_multiply = False
            
            if token == ')':
                if next_token.isdigit() or next_token.isalpha() or next_token == '(':
                    should_multiply = True
            elif token.isdigit():
                if next_token.isalpha() or next_token == '(':
                    should_multiply = True
            elif token.startswith('-') and token[1:].isdigit():
                if next_token.isalpha() or next_token == '(':
                    should_multiply = True
            elif token.isalpha() or (token.startswith('_') and token[1:].isalpha()):
                if next_token.isalpha() or next_token.isdigit() or next_token == '(':
                    should_multiply = True
            
            if should_multiply:
                normalized.append('*')
        
        i += 1
    
    return normalized


def parse_expression(tokens: List[str], pos: int = 0) -> Tuple[Optional[Any], int]:
    """Parse an expression from tokens.
    
    Grammar:
    expression := term (('+' | '-') term)*
    term := factor (('*' | '/') factor)*
    factor := primary ('^' primary)?
    primary := number | variable | '(' expression ')' | '-' primary
    """
    
    # Parse term
    left, pos = parse_term(tokens, pos)
    
    # Handle + and -
    while pos < len(tokens) and tokens[pos] in ('+', '-'):
        op = tokens[pos]
        pos += 1
        right, pos = parse_term(tokens, pos)
        left = BinOp(left, op, right)
    
    return left, pos


def parse_term(tokens: List[str], pos: int = 0) -> Tuple[Optional[Any], int]:
    """Parse a term (handles * and /)."""
    
    # Parse factor
    left, pos = parse_factor(tokens, pos)
    
    # Handle * and /
    while pos < len(tokens) and tokens[pos] in ('*', '/'):
        op = tokens[pos]
        pos += 1
        right, pos = parse_factor(tokens, pos)
        left = BinOp(left, op, right)
    
    return left, pos


def parse_factor(tokens: List[str], pos: int = 0) -> Tuple[Optional[Any], int]:
    """Parse a factor (handles ^)."""
    
    # Parse primary
    primary, pos = parse_primary(tokens, pos)
    
    # Handle ^ (power)
    while pos < len(tokens) and tokens[pos] == '^':
        pos += 1
        right, pos = parse_primary(tokens, pos)
        primary = BinOp(primary, '^', right)
    
    return primary, pos


def parse_primary(tokens: List[str], pos: int = 0) -> Tuple[Optional[Any], int]:
    """Parse a primary expression."""
    
    if pos >= len(tokens):
        return None, pos
    
    token = tokens[pos]
    
    # Parenthesized expression
    if token == '(':
        pos += 1  # skip '('
        inner_expr, pos = parse_expression(tokens, pos)
        if pos < len(tokens) and tokens[pos] == ')':
            pos += 1  # skip ')'
            return inner_expr, pos
        return None, pos
    
    # Number
    elif token.isdigit() or (token.startswith('-') and token[1:].isdigit()):
        value = int(token)
        return Num(value), pos + 1
    
    # Variable/identifier (including dotted like Nat.succ)
    elif token[0].isalpha() and all(c.isalnum() or c in '_.-' for c in token):
        var_name = token
        return Var(var_name), pos + 1
    
    # Unary negation
    elif token == '-':
        if pos + 1 < len(tokens):
            # Check if next token is a number or variable
            next_token = tokens[pos + 1]
            if (next_token.isdigit() or (next_token.startswith('-') and next_token[1:].isdigit()) or
                (next_token.isalpha() or (next_token.startswith('_') and next_token[1:].isalpha())) or
                next_token == '('):
                # Parse the operand and negate it
                expr, pos = parse_primary(tokens, pos + 1)
                if expr is not None:
                    return Neg(expr), pos
    
    return None, pos + 1


def parse_equation(expression: str) -> Tuple[Optional[Any], Optional[List[str]]]:
    """Parse a mathematical equation/inequality expression.
    
    Returns:
        (parsed node, list of free variable names)
    """
    # Tokenize
    tokens = tokenize(expression)
    tokens = normalize_implicit_multiplication(tokens)
    
    # Find the relation operator position
    normalized = expression.strip()
    
    # Try to find relation operator in order of priority: !=, >=, <=, <, >
    # Note: = is checked last since >= and <= contain =
    rel_op = None
    rel_patterns = ['!=', '>=', '<=', '<', '>']
    
    for op in rel_patterns:
        # Escape for regex
        escaped_op = re.escape(op)
        match = re.search(escaped_op, normalized)
        if match:
            rel_op = op
            # Split at this operator position
            left_text = normalized[:match.start()].strip()
            right_text = normalized[match.end():].strip()
            break
    
    # Check for = as relation operator (last priority, after checking >=, <=, etc.)
    if rel_op is None:
        match = re.search(r'(?<![<>=!])=', normalized)
        if match and match.group(0) == '=':
            rel_op = '='
            left_text = normalized[:match.start()].strip()
            right_text = normalized[match.end():].strip()
    
    if rel_op is None:
        # No relation operator found - parse as just an expression
        left, pos = parse_expression(tokens)
        free_vars = extract_free_variables(left)
        return None, free_vars
    
    # Parse left side
    left_tokens = tokenize(left_text)
    left_tokens = normalize_implicit_multiplication(left_tokens)
    left, _ = parse_expression(left_tokens)
    
    # Parse right side
    right_tokens = tokenize(right_text)
    right_tokens = normalize_implicit_multiplication(right_tokens)
    right, _ = parse_expression(right_tokens)
    
    # Extract free variables
    left_vars = extract_free_variables(left)
    right_vars = extract_free_variables(right)
    free_vars = sorted(list(set(left_vars + right_vars)))
    
    # Create equation node
    eq = Eq(left, right)
    
    return eq, free_vars


def extract_free_variables(node) -> List[str]:
    """Extract free variable names from an AST node."""
    vars_set = set()
    
    if node is None:
        return []
    
    def _extract(n):
        if isinstance(n, Var):
            vars_set.add(n.name)
        elif isinstance(n, BinOp):
            _extract(n.left)
            _extract(n.right)
        elif isinstance(n, Neg):
            _extract(n.expr)
        elif isinstance(n, Eq):
            _extract(n.left)
            _extract(n.right)
        elif isinstance(n, Ne):
            _extract(n.left)
            _extract(n.right)
        elif isinstance(n, Lt):
            _extract(n.left)
            _extract(n.right)
        elif isinstance(n, Le):
            _extract(n.left)
            _extract(n.right)
        elif isinstance(n, Gt):
            _extract(n.left)
            _extract(n.right)
        elif isinstance(n, Ge):
            _extract(n.left)
            _extract(n.right)
    
    _extract(node)
    
    # Return sorted list for deterministic output
    return sorted(list(vars_set))


def parse(input_string: str) -> Dict[str, Any]:
    """Parse a mathematical statement and return structured information.
    
    Returns dict with:
        - 'type': 'equation', 'inequality', or 'expression'
        - 'left': left side AST or None
        - 'right': right side AST or None
        - 'relation': relation operator or None
        - 'free_variables': list of free variable names
        - 'normalized': normalized expression string
    """
    eq, free_vars = parse_equation(input_string)
    
    result = {
        'type': 'expression',
        'left': None,
        'right': None,
        'relation': None,
        'free_variables': free_vars,
        'normalized': input_string.strip(),
    }
    
    if eq is not None:
        result['type'] = 'equation'
        result['left'] = eq.left
        result['right'] = eq.right
        result['relation'] = 'Eq'
    else:
        # Check for inequality types
        normalized = input_string.strip()
        for op in ['!=', '>=', '<=', '<', '>']:
            if op in normalized:
                result['type'] = 'inequality'
                result['relation'] = op
                break
    
    return result


# Test the parser
if __name__ == "__main__":
    test_cases = [
        "0 = 0",
        "x + 0 = x",
        "(a+b)^2 = a^2 + 2ab + b^2",
        "-1 + 1 = 0",
        "x < x + 1",
        "Nat.succ 0 = 1",
    ]
    
    for test in test_cases:
        result = parse(test)
        print(f"Input: {test!r}")
        print(f"  Type: {result['type']}")
        print(f"  Free vars: {result['free_variables']}")
        print(f"  Relation: {result['relation']}")
        print(f"  Normalized: {result['normalized']}")
        print()