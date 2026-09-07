"""Small formula parser for MVP arithmetic expressions."""
import re
from typing import List, Optional, Tuple, Dict, Any, cast
_ODE_RE = re.compile('^\\s*d\\s*([A-Za-z_]\\w*)\\s*/\\s*dt\\s*=\\s*(.*)$', re.DOTALL)

class ASTNode:
    """Base class for AST nodes"""
    pass

class Num(ASTNode):
    """Numeric literal node"""

    def __init__(self, value: int, is_float: bool=False) -> None:
        self.value = value
        self.is_float = is_float

    def __repr__(self) -> str:
        return 'Num(' + str(self.value) + ')'

class Var(ASTNode):
    """Variable node"""

    def __init__(self, name: str) -> None:
        self.name = name

    def __repr__(self) -> str:
        return "Var('" + self.name + "')"

class Neg(ASTNode):
    """Unary negation node"""

    def __init__(self, expr: ASTNode) -> None:
        self.expr = expr

    def __repr__(self) -> str:
        return 'Neg(' + str(self.expr) + ')'

class BinOp(ASTNode):
    """Binary operation node"""

    def __init__(self, left: ASTNode, op: str, right: ASTNode) -> None:
        self.left = left
        self.op = op
        self.right = right

    def __repr__(self) -> str:
        return 'BinOp(' + str(self.left) + ", '" + self.op + "', " + str(self.right) + ')'

class Eq(ASTNode):
    """Equality node"""

    def __init__(self, left: ASTNode, right: ASTNode) -> None:
        self.left = left
        self.right = right

    def __repr__(self) -> str:
        return 'Eq(' + str(self.left) + ', ' + str(self.right) + ')'

class Ne(ASTNode):
    """Inequality/Not-equal node"""

    def __init__(self, left: ASTNode, right: ASTNode) -> None:
        self.left = left
        self.right = right

    def __repr__(self) -> str:
        return 'Ne(' + str(self.left) + ', ' + str(self.right) + ')'

class Lt(ASTNode):
    """Less-than node"""

    def __init__(self, left: ASTNode, right: ASTNode) -> None:
        self.left = left
        self.right = right

    def __repr__(self) -> str:
        return 'Lt(' + str(self.left) + ', ' + str(self.right) + ')'

class Le(ASTNode):
    """Less-or-equal node"""

    def __init__(self, left: ASTNode, right: ASTNode) -> None:
        self.left = left
        self.right = right

    def __repr__(self) -> str:
        return 'Le(' + str(self.left) + ', ' + str(self.right) + ')'

class Gt(ASTNode):
    """Greater-than node"""

    def __init__(self, left: ASTNode, right: ASTNode) -> None:
        self.left = left
        self.right = right

    def __repr__(self) -> str:
        return 'Gt(' + str(self.left) + ', ' + str(self.right) + ')'

class Ge(ASTNode):
    """Greater-or-equal node"""

    def __init__(self, left: ASTNode, right: ASTNode) -> None:
        self.left = left
        self.right = right

    def __repr__(self) -> str:
        return 'Ge(' + str(self.left) + ', ' + str(self.right) + ')'

class ODE(ASTNode):
    """Ordinary differential equation node: d<var>/dt = <rhs>.

    Represents a time derivative statement where ``var`` is the name of the
    differentiated quantity (e.g. ``A_gut``) and ``rhs`` is the AST of the
    right-hand side expression. This is the canonical form produced when
    parsing perfusion-limited PBPK ODEs such as ``dA_gut/dt = -ka * A_gut``.
    """

    def __init__(self, var: str, rhs: ASTNode) -> None:
        self.var = var
        self.rhs = rhs

    def __repr__(self) -> str:
        return "ODE('" + self.var + "', " + str(self.rhs) + ')'

class Forall(ASTNode):
    """Forall quantifier node"""

    def __init__(self, var: str, body: ASTNode) -> None:
        self.var = var
        self.body = body

    def __repr__(self) -> str:
        return "Forall('" + self.var + "', " + str(self.body) + ')'

class Exists(ASTNode):
    """Exists quantifier node"""

    def __init__(self, var: str, body: ASTNode) -> None:
        self.var = var
        self.body = body

    def __repr__(self) -> str:
        return "Exists('" + self.var + "', " + str(self.body) + ')'

class Imp(ASTNode):
    """Implication node"""

    def __init__(self, left: ASTNode, right: ASTNode) -> None:
        self.left = left
        self.right = right

    def __repr__(self) -> str:
        return 'Imp(' + str(self.left) + ', ' + str(self.right) + ')'

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
    result = result.replace('**', '^')
    result = re.sub('\\)(\\d)', ') * \\1', result)
    result = re.sub('\\)([a-zA-Z])', ') * \\1', result)
    result = re.sub('\\)\\(', ') * (', result)
    result = re.sub('([a-zA-Z])\\(', '\\1 * (', result)
    result = re.sub('(\\d)\\(', '\\1 * (', result)

    def _split_chain(match: 're.Match[str]') -> str:
        num = match.group(1)
        letters = match.group(2)
        return num + ' * ' + ' * '.join(letters)
    result = re.sub('(\\d+)([a-z]{2,})(?![a-zA-Z])', _split_chain, result)
    changed = True
    while changed:
        changed = False
        new_result = re.sub('(\\d)([a-zA-Z])', '\\1 * \\2', result)
        if new_result != result:
            changed = True
        result = new_result
    changed = True
    while changed:
        changed = False
        new_result = re.sub('([a-zA-Z])(\\d)(?!\\w)', '\\1 * \\2', result)
        if new_result != result:
            changed = True
        result = new_result
    changed = True
    while changed:
        changed = False
        new_result = re.sub('(?<![a-zA-Z])([a-z])([a-z])(?![a-zA-Z])', '\\1 * \\2', result)
        if new_result != result:
            changed = True
        result = new_result
    return result

def tokenize(expression: str) -> List[str]:
    """Tokenize a mathematical expression string into tokens."""
    expr = normalize_implicit_multiplication_expression(expression)
    replacements = [('\\\\cdot', '*'), ('\\\\le', '<='), ('\\\\ge', '>='), ('\\\\neq', '!=')]
    for pattern, replacement in replacements:
        expr = re.sub(pattern, replacement, expr)
    token_pattern = '\n        \\d+                  # integers\n        | [a-zA-Z_]\\w*(?:\\.[a-zA-Z_]\\w*)*   # variables/identifiers (dotted like Nat.succ)\n        | [+\\-*/^=!<>]       # operators\n        | \\(|\\)              # parentheses\n        | <=|>=|!=           # multi-char operators\n    '
    tokens = re.findall(token_pattern, expr, re.VERBOSE)
    return tokens

def normalize_implicit_multiplication(tokens: List[str]) -> List[str]:
    """Normalize implicit multiplication like '2ab' -> '2 * a * b'."""
    normalized = []
    i = 0
    while i < len(tokens):
        token = tokens[i]
        normalized.append(token)
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

def parse_expression(tokens: List[str], pos: int=0) -> Tuple[Optional[ASTNode], int]:
    """Parse an expression from tokens.
    
    Grammar:
    expression := term (('+' | '-') term)*
    term := factor (('*' | '/') factor)*
    factor := primary ('^' primary)?
    primary := number | variable | '(' expression ')' | '-' primary
    """
    left, pos = parse_term(tokens, pos)
    while pos < len(tokens) and tokens[pos] in ('+', '-'):
        op = tokens[pos]
        pos += 1
        right, pos = parse_term(tokens, pos)
        left = BinOp(cast(ASTNode, left), op, cast(ASTNode, right))
    return (left, pos)

def parse_term(tokens: List[str], pos: int=0) -> Tuple[Optional[ASTNode], int]:
    """Parse a term (handles * and /)."""
    left, pos = parse_factor(tokens, pos)
    while pos < len(tokens) and tokens[pos] in ('*', '/'):
        op = tokens[pos]
        pos += 1
        right, pos = parse_factor(tokens, pos)
        left = BinOp(cast(ASTNode, left), op, cast(ASTNode, right))
    return (left, pos)

def parse_factor(tokens: List[str], pos: int=0) -> Tuple[Optional[ASTNode], int]:
    """Parse a factor (handles ^)."""
    primary, pos = parse_primary(tokens, pos)
    while pos < len(tokens) and tokens[pos] == '^':
        pos += 1
        right, pos = parse_primary(tokens, pos)
        primary = BinOp(cast(ASTNode, primary), '^', cast(ASTNode, right))
    return (primary, pos)

def parse_primary(tokens: List[str], pos: int=0) -> Tuple[Optional[ASTNode], int]:
    """Parse a primary expression."""
    if pos >= len(tokens):
        return (None, pos)
    token = tokens[pos]
    if token == '(':
        pos += 1
        inner_expr, pos = parse_expression(tokens, pos)
        if pos < len(tokens) and tokens[pos] == ')':
            pos += 1
            return (inner_expr, pos)
        return (None, pos)
    elif token.isdigit() or (token.startswith('-') and token[1:].isdigit()):
        value = int(token)
        return (Num(value), pos + 1)
    elif token[0].isalpha() and all((c.isalnum() or c in '_.-' for c in token)):
        var_name = token
        return (Var(var_name), pos + 1)
    elif token == '-':
        if pos + 1 < len(tokens):
            next_token = tokens[pos + 1]
            if next_token.isdigit() or (next_token.startswith('-') and next_token[1:].isdigit()) or (next_token.isalpha() or (next_token.startswith('_') and next_token[1:].isalpha())) or (next_token == '('):
                expr, pos = parse_primary(tokens, pos + 1)
                if expr is not None:
                    return (Neg(expr), pos)
    return (None, pos + 1)

def parse_equation(expression: str) -> Tuple[Optional[ASTNode], Optional[List[str]]]:
    """Parse a mathematical equation/inequality expression.
    
    Returns:
        (parsed node, list of free variable names)
    """
    tokens = tokenize(expression)
    tokens = normalize_implicit_multiplication(tokens)
    normalized = expression.strip()
    rel_op = None
    rel_patterns = ['!=', '>=', '<=', '<', '>']
    for op in rel_patterns:
        escaped_op = re.escape(op)
        match = re.search(escaped_op, normalized)
        if match:
            rel_op = op
            left_text = normalized[:match.start()].strip()
            right_text = normalized[match.end():].strip()
            break
    if rel_op is None:
        match = re.search('(?<![<>=!])=', normalized)
        if match and match.group(0) == '=':
            rel_op = '='
            left_text = normalized[:match.start()].strip()
            right_text = normalized[match.end():].strip()
    if rel_op is None:
        left, pos = parse_expression(tokens)
        free_vars = extract_free_variables(left)
        return (None, free_vars)
    left_tokens = tokenize(left_text)
    left_tokens = normalize_implicit_multiplication(left_tokens)
    left, _ = parse_expression(left_tokens)
    right_tokens = tokenize(right_text)
    right_tokens = normalize_implicit_multiplication(right_tokens)
    right, _ = parse_expression(right_tokens)
    left_vars = extract_free_variables(left)
    right_vars = extract_free_variables(right)
    free_vars = sorted(list(set(left_vars + right_vars)))
    rel_nodes = {'=': Eq, '!=': Ne, '<': Lt, '<=': Le, '>': Gt, '>=': Ge}
    node_cls = rel_nodes.get(rel_op, Eq)
    eq = node_cls(cast(ASTNode, left), cast(ASTNode, right))
    return (eq, free_vars)

def parse_ode(expression: str) -> Tuple[Optional[ODE], Optional[List[str]]]:
    """Parse an ordinary differential equation of the form ``d<var>/dt = <rhs>``.

    Returns:
        (ODE node, list of free variable names in the RHS) when the input
        matches the ODE pattern, otherwise ``(None, None)``.

    The differentiated variable name (e.g. ``A_gut``) is recorded verbatim as
    ``ode.var``; the right-hand side is parsed into an AST suitable for Lean
    translation via the standard expression parser.
    """
    if expression is None:
        return (None, None)
    normalized = expression.strip()
    match = _ODE_RE.match(normalized)
    if not match:
        return (None, None)
    var = match.group(1)
    rhs_text = match.group(2).strip()
    if not rhs_text:
        return (None, None)
    rhs_tokens = tokenize(rhs_text)
    rhs_tokens = normalize_implicit_multiplication(rhs_tokens)
    rhs, _ = parse_expression(rhs_tokens)
    if rhs is None:
        return (None, None)
    free_vars = extract_free_variables(rhs)
    return (ODE(var, rhs), free_vars)

def is_ode(expression: str) -> bool:
    """Return True if ``expression`` is an ODE of the form d<var>/dt = <rhs>."""
    return _ODE_RE.match((expression or '').strip()) is not None

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
    normalized = (expression or '').strip()
    return re.search('\\bd[A-Za-z_]\\w*/d[A-Za-z_]\\w*', normalized) is not None

def extract_free_variables(node: Optional[ASTNode]) -> List[str]:
    """Extract free variable names from an AST node."""
    vars_set: set[str] = set()
    if node is None:
        return []

    def _extract(n: Optional[ASTNode]) -> None:
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
    return sorted(list(vars_set))

def contains_op(node: Optional[ASTNode], op: str) -> bool:
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

def is_inequality(node: Optional[ASTNode]) -> bool:
    """Return True if the node is a comparison (Ne, Lt, Le, Gt, Ge)."""
    return isinstance(node, (Ne, Lt, Le, Gt, Ge))

def has_numeric_ops(node: Optional[ASTNode]) -> bool:
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

def has_polynomial_structure(node: Optional[ASTNode]) -> bool:
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

def find_division_variables(node: Optional[ASTNode]) -> set[str]:
    """Find variable names that appear in division denominators.

    Returns the set of variable names whose right-hand side of a ``/`` node
    is not a numeric literal (i.e. symbolic division).  Used by the agentic
    pipeline to generate positivity hypotheses for field-theoretic theorems.
    """
    if node is None:
        return set()
    result: set[str] = set()
    if isinstance(node, BinOp):
        if node.op == '/' and (not isinstance(node.right, Num)):
            _collect_vars(node.right, result)
        result |= find_division_variables(node.left)
        result |= find_division_variables(node.right)
    elif isinstance(node, Neg):
        result |= find_division_variables(node.expr)
    elif isinstance(node, (Eq, Ne, Lt, Le, Gt, Ge)):
        result |= find_division_variables(node.left)
        result |= find_division_variables(node.right)
    return result

def _collect_vars(node: Optional[ASTNode], result: set[str]) -> None:
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

def has_rational_structure(node: Optional[ASTNode]) -> bool:
    """Detect division over symbolic (non-numeric) variables.

    Returns True when the AST contains a ``/`` operator whose right operand
    is *not* a pure numeric literal – i.e. the division is symbolic and
    therefore lives in a field (``ℝ``) rather than ``ℕ`` or ``ℤ``.

    Also detects Michaelis-Menten patterns: ``Vmax * C / (Km + C)`` where
    the denominator is a sum containing a symbolic variable.  This is the
    canonical enzyme-kinetics form that requires ``Real`` typing and
    Mathlib's ``field_simp``/``ring`` tactics.

    This is used by the agentic pipeline to decide whether the expression
    requires ``Real`` typing and Mathlib's ``field_simp``/``ring`` tactics.
    """
    if node is None:
        return False
    if isinstance(node, BinOp):
        if node.op == '/':
            if not isinstance(node.right, Num):
                return True
        if node.op == '*' and isinstance(node.right, BinOp) and (node.right.op == '/'):
            inner_div = node.right
            if not isinstance(inner_div.right, Num):
                return True
        return has_rational_structure(node.left) or has_rational_structure(node.right)
    if isinstance(node, Neg):
        return has_rational_structure(node.expr)
    if isinstance(node, (Eq, Ne, Lt, Le, Gt, Ge)):
        return has_rational_structure(node.left) or has_rational_structure(node.right)
    return False

def extract_positivity_hypotheses(node: Optional[ASTNode]) -> List[str]:
    """Recursively find all variables in division denominators.

    Returns a list of Lean hypothesis strings of the form
    ``[(hKm : 0 < Km), (hC : 0 < C), ...]`` for every variable that
    appears in the denominator of a ``/`` node (including nested sums
    like ``Km + C`` in Michaelis-Menten denominators).

    These positivity hypotheses are required by Mathlib's ``field_simp``
    to simplify divisions safely over ``ℝ``.

    Examples
    --------
    >>> node, _ = parse_equation("Vmax * C / (Km + C)")
    >>> extract_positivity_hypotheses(node)
    ['(hC : 0 < C)', '(hKm : 0 < Km)']
    """
    if node is None:
        return []
    div_vars = find_division_variables(node)
    return [f'(h{v} : 0 < {v})' for v in sorted(div_vars)]

def has_compartmental_structure(node: Optional[ASTNode]) -> bool:
    """Detect PBPK compartmental flow patterns in the AST.

    Returns True when the expression contains the characteristic perfusion-
    limited compartment structure ``Q * (C_p - C_tissue / Kp)`` where a
    flow rate ``Q`` multiplies a concentration gradient involving division
    by a tissue partition coefficient ``Kp``.

    This is used by the agentic pipeline to classify VeriTrial PBPK
    mass-conservation lemmas and route them through the Real-typed
    parametric proof path.
    """
    if node is None:
        return False

    def _walk(n: Optional[ASTNode]) -> bool:
        if n is None:
            return False
        if isinstance(n, BinOp) and n.op == '*':
            rhs = n.right
            if isinstance(rhs, BinOp) and rhs.op in ('-', '+'):
                if isinstance(rhs.right, BinOp) and rhs.right.op == '/':
                    if not isinstance(rhs.right.right, Num):
                        return True
        if isinstance(n, BinOp):
            return _walk(n.left) or _walk(n.right)
        if isinstance(n, Neg):
            return _walk(n.expr)
        if isinstance(n, (Eq, Ne, Lt, Le, Gt, Ge)):
            return _walk(n.left) or _walk(n.right)
        return False
    return _walk(node)

def is_metzler_positivity(node: Optional[ASTNode]) -> bool:
    """Jacobian off-diagonal positivity: ``Q / (V * Kp) > 0`` or ``Q / Kp > 0``.

    Returns True when the node is a strict inequality (Gt/Lt, either
    orientation) whose positive side is a division of ``Q`` by a ``Kp``
    (optionally via ``V * Kp``) term.
    """
    if node is None:
        return False
    if isinstance(node, Gt):
        lhs, rhs = (node.left, node.right)
    elif isinstance(node, Lt):
        lhs, rhs = (node.right, node.left)
    else:
        return False
    if not (isinstance(rhs, Num) and rhs.value == 0):
        return False
    if not (isinstance(lhs, BinOp) and lhs.op == '/'):
        return False
    num_vars: set[str] = set()
    _collect_vars(lhs.left, num_vars)
    den_vars: set[str] = set()
    _collect_vars(lhs.right, den_vars)
    if 'Q' not in num_vars:
        return False
    return 'Kp' in den_vars

def is_discrete_step_conservation(node: Optional[ASTNode]) -> bool:
    """Discrete-step conservation: ``sum(y_i + dt * f_i) = sum(y_i) + dt * sum(f_i)``.

    Structural check on the LaTeX round-trip: an Eq whose left mentions
    ``dt`` and whose right mentions both ``dt`` and ``sum`` (or the
    per-index sum pattern ``y_i``/``f_i``).
    """
    if not isinstance(node, Eq):
        return False
    latex = ast_to_latex(node)
    if '=' not in latex:
        return False
    left, right = latex.split('=', 1)

    def has_dt(s: str) -> bool:
        return 'dt' in s or 'd * t' in s
    if not has_dt(left):
        return False
    if not has_dt(right):
        return False
    return 'sum' in latex or ('y_i' in latex and 'f_i' in latex)

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
    result: Dict[str, Any] = {'type': 'expression', 'left': None, 'right': None, 'relation': None, 'ode': None, 'free_variables': free_vars, 'normalized': input_string.strip()}
    if eq is not None:
        assert isinstance(eq, (Eq, Ne, Lt, Le, Gt, Ge))
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
        normalized = input_string.strip()
        for op in ['!=', '>=', '<=', '<', '>']:
            if op in normalized:
                result['type'] = 'inequality'
                result['relation'] = op
                break
    ode, ode_vars = parse_ode(input_string)
    if ode is not None:
        result['type'] = 'ode'
        result['ode'] = ode
        result['free_variables'] = ode_vars
        result['relation'] = '='
    return result

def ast_to_latex(node: Optional[ASTNode]) -> str:
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

def _is_identity(node: ASTNode) -> bool:
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
if __name__ == '__main__':
    test_cases = ['0 = 0', 'x + 0 = x', '(a+b)^2 = a^2 + 2ab + b^2', '-1 + 1 = 0', 'x < x + 1', 'Nat.succ 0 = 1']
    for test in test_cases:
        result = parse(test)
        print(f'Input: {test!r}')
        print(f"  Type: {result['type']}")
        print(f"  Free vars: {result['free_variables']}")
        print(f"  Relation: {result['relation']}")
        print(f"  Normalized: {result['normalized']}")
        print()