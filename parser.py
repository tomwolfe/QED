#!/usr/bin/env python3
"""Small formula parser for MVP arithmetic expressions."""

import re
from typing import List, Optional, Tuple, Dict, Any

# Matches the left-hand side of an ODE of the form d<var>/dt = <rhs>.
# Captures the differentiated variable name (group 1) and the right-hand
# side expression (group 2). Whitespace around tokens is tolerated.
_ODE_RE = re.compile(r"^\s*d\s*([A-Za-z_]\w*)\s*/\s*dt\s*=\s*(.*)$", re.DOTALL)


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


class ODE(ASTNode):
    """Ordinary differential equation node: d<var>/dt = <rhs>.

    Represents a time derivative statement where ``var`` is the name of the
    differentiated quantity (e.g. ``A_gut``) and ``rhs`` is the AST of the
    right-hand side expression. This is the canonical form produced when
    parsing perfusion-limited PBPK ODEs such as ``dA_gut/dt = -ka * A_gut``.
    """

    def __init__(self, var: str, rhs: ASTNode):
        self.var = var
        self.rhs = rhs

    def __repr__(self):
        return "ODE('" + self.var + "', " + str(self.rhs) + ")"


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
    
    # Create relation node based on operator
    rel_nodes = {
        '=': Eq,
        '!=': Ne,
        '<': Lt,
        '<=': Le,
        '>': Gt,
        '>=': Ge,
    }
    node_cls = rel_nodes.get(rel_op, Eq)
    eq = node_cls(left, right)
    
    return eq, free_vars


def parse_ode(expression: str) -> Tuple[Optional[Any], Optional[List[str]]]:
    """Parse an ordinary differential equation of the form ``d<var>/dt = <rhs>``.

    Returns:
        (ODE node, list of free variable names in the RHS) when the input
        matches the ODE pattern, otherwise ``(None, None)``.

    The differentiated variable name (e.g. ``A_gut``) is recorded verbatim as
    ``ode.var``; the right-hand side is parsed into an AST suitable for Lean
    translation via the standard expression parser.
    """
    if expression is None:
        return None, None

    normalized = expression.strip()
    match = _ODE_RE.match(normalized)
    if not match:
        return None, None

    var = match.group(1)
    rhs_text = match.group(2).strip()

    if not rhs_text:
        return None, None

    rhs_tokens = tokenize(rhs_text)
    rhs_tokens = normalize_implicit_multiplication(rhs_tokens)
    rhs, _ = parse_expression(rhs_tokens)

    if rhs is None:
        return None, None

    free_vars = extract_free_variables(rhs)
    return ODE(var, rhs), free_vars


def is_ode(expression: str) -> bool:
    """Return True if ``expression`` is an ODE of the form d<var>/dt = <rhs>."""
    return _ODE_RE.match((expression or "").strip()) is not None


def involves_derivative(expression: str) -> bool:
    """Return True if ``expression`` mentions a time-derivative / rate-of-change
    term such as ``dX/dt`` or ``dA_liver/dt`` anywhere in the string.

    This is used by the agentic pipeline to recognize formal-ODE inputs (not
    just the canonical ``d<var>/dt = <rhs>`` head form) so it can prioritize
    Mathlib tactics that handle derivatives, division and algebraic structure
    in the right-hand side (``dsimp``, ``field_simp``, ``ring``).
    """
    if is_ode(expression):
        return True
    normalized = (expression or "").strip()
    # Match d<ident>/d<ident> anywhere (e.g. dA_liver/dt, dC/dt, dState/dx).
    return re.search(r'\bd[A-Za-z_]\w*/d[A-Za-z_]\w*', normalized) is not None


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


def contains_op(node, op: str) -> bool:
    """Recursively check if any BinOp in the AST uses the given operator."""
    if node is None:
        return False
    if isinstance(node, BinOp):
        if node.op == op:
            return True
        return contains_op(node.left, op) or contains_op(node.right, op)
    if isinstance(node, Neg):
        return contains_op(node.expr, op)
    if isinstance(node, (Eq, Ne, Lt, Le, Gt, Ge)):
        return contains_op(node.left, op) or contains_op(node.right, op)
    return False


def is_inequality(node) -> bool:
    """Return True if the node is a comparison (Ne, Lt, Le, Gt, Ge)."""
    return isinstance(node, (Ne, Lt, Le, Gt, Ge))


def has_numeric_ops(node) -> bool:
    """Check for + or * operators in the AST tree."""
    if node is None:
        return False
    if isinstance(node, BinOp):
        if node.op in ('+', '*'):
            return True
        return has_numeric_ops(node.left) or has_numeric_ops(node.right)
    if isinstance(node, Neg):
        return has_numeric_ops(node.expr)
    if isinstance(node, (Eq, Ne, Lt, Le, Gt, Ge)):
        return has_numeric_ops(node.left) or has_numeric_ops(node.right)
    return False


def has_polynomial_structure(node) -> bool:
    """Check for ^ operators (detects polynomial/algebraic expressions)."""
    if node is None:
        return False
    if isinstance(node, BinOp):
        if node.op == '^':
            return True
        return has_polynomial_structure(node.left) or has_polynomial_structure(node.right)
    if isinstance(node, Neg):
        return has_polynomial_structure(node.expr)
    if isinstance(node, (Eq, Ne, Lt, Le, Gt, Ge)):
        return has_polynomial_structure(node.left) or has_polynomial_structure(node.right)
    return False


def find_division_variables(node) -> set:
    """Find variable names that appear in division denominators.

    Returns the set of variable names whose right-hand side of a ``/`` node
    is not a numeric literal (i.e. symbolic division).  Used by the agentic
    pipeline to generate positivity hypotheses for field-theoretic theorems.
    """
    if node is None:
        return set()
    result: set = set()
    if isinstance(node, BinOp):
        if node.op == '/' and not isinstance(node.right, Num):
            _collect_vars(node.right, result)
        result |= find_division_variables(node.left)
        result |= find_division_variables(node.right)
    elif isinstance(node, Neg):
        result |= find_division_variables(node.expr)
    elif isinstance(node, (Eq, Ne, Lt, Le, Gt, Ge)):
        result |= find_division_variables(node.left)
        result |= find_division_variables(node.right)
    return result


def _collect_vars(node, result: set) -> None:
    """Collect all Var names from an AST node into *result*."""
    if node is None:
        return
    if isinstance(node, Var):
        result.add(node.name)
    elif isinstance(node, BinOp):
        _collect_vars(node.left, result)
        _collect_vars(node.right, result)
    elif isinstance(node, Neg):
        _collect_vars(node.expr, result)


def has_rational_structure(node) -> bool:
    """Detect division over symbolic (non-numeric) variables.

    Returns True when the AST contains a ``/`` operator whose right operand
    is *not* a pure numeric literal – i.e. the division is symbolic and
    therefore lives in a field (``ℝ``) rather than ``ℕ`` or ``ℤ``.

    This is used by the agentic pipeline to decide whether the expression
    requires ``Real`` typing and Mathlib's ``field_simp``/``ring`` tactics.
    """
    if node is None:
        return False
    if isinstance(node, BinOp):
        if node.op == '/':
            # Right operand that is not a numeric literal => symbolic division
            if not isinstance(node.right, Num):
                return True
        return has_rational_structure(node.left) or has_rational_structure(node.right)
    if isinstance(node, Neg):
        return has_rational_structure(node.expr)
    if isinstance(node, (Eq, Ne, Lt, Le, Gt, Ge)):
        return has_rational_structure(node.left) or has_rational_structure(node.right)
    return False


def parse(input_string: str) -> Dict[str, Any]:
    """Parse a mathematical statement and return structured information.
    
    Returns dict with:
        - 'type': 'equation', 'inequality', 'ode', or 'expression'
        - 'left': left side AST or None
        - 'right': right side AST or None
        - 'relation': relation operator or None
        - 'ode': ODE node when the input is an ODE, else None
        - 'free_variables': list of free variable names
        - 'normalized': normalized expression string
    """
    eq, free_vars = parse_equation(input_string)

    result = {
        'type': 'expression',
        'left': None,
        'right': None,
        'relation': None,
        'ode': None,
        'free_variables': free_vars,
        'normalized': input_string.strip(),
    }

    if eq is not None:
        result['left'] = eq.left
        result['right'] = eq.right
        if isinstance(eq, Eq):
            result['type'] = 'equation'
            result['relation'] = '='
        else:
            result['type'] = 'inequality'
            rel_map = {Ne: '!=', Lt: '<', Le: '<=', Gt: '>', Ge: '>='}
            result['relation'] = rel_map.get(type(eq), '=')
    else:
        # Check for inequality types
        normalized = input_string.strip()
        for op in ['!=', '>=', '<=', '<', '>']:
            if op in normalized:
                result['type'] = 'inequality'
                result['relation'] = op
                break

    # ODE detection takes precedence for d<var>/dt = <rhs> statements.
    ode, ode_vars = parse_ode(input_string)
    if ode is not None:
        result['type'] = 'ode'
        result['ode'] = ode
        result['free_variables'] = ode_vars
        result['relation'] = '='
    
    return result


def ast_to_latex(node) -> str:
    """Convert an AST node back to a canonical LaTeX-like string."""
    if node is None:
        return ''
    if isinstance(node, Num):
        return str(node.value)
    if isinstance(node, Var):
        return node.name
    if isinstance(node, Neg):
        inner = ast_to_latex(node.expr)
        return f'-{inner}'
    if isinstance(node, BinOp):
        left = ast_to_latex(node.left)
        right = ast_to_latex(node.right)
        if node.op == '^':
            return f'{left}^{{{right}}}'
        return f'{left} {node.op} {right}'
    if isinstance(node, Eq):
        return f'{ast_to_latex(node.left)} = {ast_to_latex(node.right)}'
    if isinstance(node, Ne):
        return f'{ast_to_latex(node.left)} != {ast_to_latex(node.right)}'
    if isinstance(node, Lt):
        return f'{ast_to_latex(node.left)} < {ast_to_latex(node.right)}'
    if isinstance(node, Le):
        return f'{ast_to_latex(node.left)} <= {ast_to_latex(node.right)}'
    if isinstance(node, Gt):
        return f'{ast_to_latex(node.left)} > {ast_to_latex(node.right)}'
    if isinstance(node, Ge):
        return f'{ast_to_latex(node.left)} >= {ast_to_latex(node.right)}'
    if isinstance(node, ODE):
        return f'd{node.var}/dt = {ast_to_latex(node.rhs)}'
    return ''


def _is_identity(node: Eq) -> bool:
    """Return True if the Eq node represents a structural identity (left == right)."""
    if not isinstance(node, Eq):
        return False
    return ast_to_latex(node.left) == ast_to_latex(node.right)


def _is_numeric_only(node: ASTNode) -> bool:
    """Return True if the AST contains only numeric literals and operators (no variables)."""
    if isinstance(node, Num):
        return True
    if isinstance(node, Neg):
        return _is_numeric_only(node.expr)
    if isinstance(node, BinOp):
        return _is_numeric_only(node.left) and _is_numeric_only(node.right)
    if isinstance(node, Var):
        return False
    return False


def is_numeric_equality(latex: str) -> bool:
    """Return True if the expression is a closed numeric equality (no free variables).

    Both sides must reduce to concrete integers/floats so that ``decide``/``simp``
    can prove the equality without assuming any variables. This is the class of
    lemmas the PBPK bridge emits (e.g. ``-6 + 9 + -13 + 4 + 6 + 0 = 0``).
    """
    eq, free_vars = parse_equation(latex)
    if eq is None or not isinstance(eq, Eq):
        return False
    if free_vars:
        return False
    return _is_numeric_only(eq.left) and _is_numeric_only(eq.right)


def statement_kind(latex: str) -> str:
    """Classify a LaTeX statement as 'identity', 'equality', 'inequality', or 'other'.

    - 'identity':    Eq node where both sides are structurally identical (e.g. x = x)
    - 'equality':    Eq node where sides differ (e.g. x + 1 = 2)
    - 'inequality':  Ne, Lt, Le, Gt, or Ge node
    - 'other':       unparseable or bare expression with no relation operator
    """
    eq, _ = parse_equation(latex)
    if eq is None:
        return 'other'
    if isinstance(eq, Eq):
        if _is_identity(eq):
            return 'identity'
        return 'equality'
    if isinstance(eq, (Ne, Lt, Le, Gt, Ge)):
        return 'inequality'
    return 'other'


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