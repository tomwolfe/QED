#!/usr/bin/env python3
"""
Lean 4 Agentic Pipeline - Core implementation.
Converts constrained mathematical statements into verified Lean 4 code using iterative tactic search.
"""

import re
import sys
import os
import json
import subprocess
import tempfile
from dataclasses import dataclass, field
from fractions import Fraction
from pathlib import Path
from typing import List, Optional, Sequence, Tuple, Dict, Any
from parser import (
    parse_equation,
    parse_expression,
    tokenize,
    normalize_implicit_multiplication,
    normalize_implicit_multiplication_expression,
    contains_op,
    is_inequality,
    has_numeric_ops,
    has_polynomial_structure,
    has_rational_structure,
    find_division_variables,
    is_ode,
    involves_derivative,
    canonical_form,
    extract_free_variables,
    has_numeric_literal,
    is_derivative,
    is_positivity,
    is_discrete_step_conservation,
    is_nonneg_product,
    _collect_vars,
    _is_identity,
    _is_numeric_only,
    ASTNode,
    BinOp,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Neg,
    Num,
)


def _collect_division_numerator_vars(node: object, result: set[str]) -> None:
    """Collect variable names from the numerator of division expressions.

    ``find_division_variables`` only collects denominator variables, but
    Mathlib's ``positivity`` tactic also needs the numerator to be positive
    (e.g. ``E / F > 0`` requires ``E > 0`` and ``F > 0``).  This
    function walks the AST and adds numerator variables from ``/`` nodes
    to *result* in-place.
    """
    if node is None:
        return
    if isinstance(node, BinOp):
        if node.op == '/':
            _collect_vars(node.left, result)
        _collect_division_numerator_vars(node.left, result)
        _collect_division_numerator_vars(node.right, result)
    elif isinstance(node, Neg):
        _collect_division_numerator_vars(node.expr, result)
    elif isinstance(node, (Eq, Ne, Lt, Le, Gt, Ge)):
        _collect_division_numerator_vars(node.left, result)
        _collect_division_numerator_vars(node.right, result)


# ---------------------------------------------------------------------------
# Context-aware type selection.
#
# The type a statement must be read at is the JOIN of the requirements its
# AST imposes, over the lattice Nat < Int < Rat < Real.  A statement that
# mixes constructs (a division AND a negation, say) is read at the strongest
# type any of its parts needs -- not at the first type that happens to
# match.
#
# The requirements are read off the AST rather than off the text: a text
# heuristic cannot tell a negative LITERAL from a binary subtraction, nor a
# numeric denominator from a symbolic one, and both differences change the
# claim the statement makes.
# ---------------------------------------------------------------------------

_TYPE_LATTICE: Tuple[str, ...] = ('Nat', 'Int', 'Rat', 'Real')

# The weakest type that can support each requirement.
_TYPE_REQUIREMENTS: Dict[str, str] = {
    'NEGATIVE': 'Int',     # a negated term: Nat has no negation
    'SUBTRACTION': 'Int',  # Nat subtraction truncates, so it changes the claim
    'RATIONAL': 'Rat',     # division by a numeric literal
    'FIELD': 'Real',       # division by a symbolic denominator
    'ORDERED': 'Real',     # an ordered claim over a product or a ratio
    'ODE': 'Real',         # rate-of-change notation
}


def _join_types(types: List[str]) -> str:
    """The weakest type in the lattice that satisfies every type in *types*."""
    strongest = 'Nat'
    for candidate in types:
        if candidate not in _TYPE_LATTICE:
            continue
        if _TYPE_LATTICE.index(candidate) > _TYPE_LATTICE.index(strongest):
            strongest = candidate
    return strongest


def _split_relation(expression: str) -> Optional[Tuple[str, str, str]]:
    """Split a statement at its top-level relation operator.

    Returns ``(left, right, operator)`` -- the two sides with the text they
    were written with, so ascribing them does not change the statement, and
    the operator itself so an ascribed statement keeps its RELATION (a
    ``!=`` must not come back as an ``=``) -- or None when the statement has
    no top-level relation.
    """
    depth = 0
    i = 0
    n = len(expression)
    while i < n:
        ch = expression[i]
        if ch == '(':
            depth += 1
        elif ch == ')':
            depth -= 1
        elif depth == 0:
            two = expression[i:i + 2]
            if two in ('!=', '<=', '>='):
                return expression[:i].strip(), expression[i + 2:].strip(), two
            if ch in ('=', '<', '>', '≠'):
                return expression[:i].strip(), expression[i + 1:].strip(), ch
        i += 1
    return None


def _ascribe_sides(lean_expression: str, lean_type: str) -> Optional[str]:
    """The statement with BOTH sides of its relation ascribed at *lean_type*.

    Returns None when the statement has no top-level relation: there is
    nothing to ascribe then, and the statement is elaborated as written.
    The relation itself is preserved, so a ``!=`` does not come back as an
    ``=``.
    """
    sides = _split_relation(lean_expression)
    if sides is None:
        return None
    lhs, rhs, operator = sides
    return f"({lhs} : {lean_type}) {operator} ({rhs} : {lean_type})"


# The exact value of a closed numeric term, and the value the SAME term has
# under ℕ arithmetic.  Both are needed to decide whether a statement may be
# read at ℕ at all: ℕ truncates its division and saturates its subtraction,
# so a statement can be TRUE at ℕ and FALSE at ℚ.
#
# The exact reading is rational arithmetic (``fractions.Fraction``); the ℕ
# reading mirrors Lean: ``Nat.div`` truncates towards zero and ``Nat.sub``
# saturates at zero.
#
# The exponent is bounded so that a term like ``9 ^ 999999999`` cannot turn a
# type decision into an arbitrary computation: an exponent that large is
# simply not evaluated, and a statement that needs it is not read at ℕ.
_MAX_EVAL_EXPONENT = 64


def _exact_term_value(node: Optional[ASTNode]) -> Optional[Fraction]:
    """The EXACT rational value of a closed numeric term, or None.

    None means "cannot be evaluated exactly": the term is not closed (it
    contains a variable), it divides by zero, it is not an exact number, or
    its exponent is not a small natural number.
    """
    if isinstance(node, Num):
        if node.is_float:
            return None
        return Fraction(node.value)
    if isinstance(node, Neg):
        inner = _exact_term_value(node.expr)
        return None if inner is None else -inner
    if isinstance(node, BinOp):
        left = _exact_term_value(node.left)
        right = _exact_term_value(node.right)
        if left is None or right is None:
            return None
        if node.op == '+':
            return left + right
        if node.op == '-':
            return left - right
        if node.op == '*':
            return left * right
        if node.op == '/':
            if right == 0:
                return None
            return left / right
        if node.op == '^':
            if (right.denominator != 1 or right < 0
                    or right > _MAX_EVAL_EXPONENT):
                return None
            return left ** int(right)
    return None


def _nat_term_value(node: Optional[ASTNode]) -> Optional[int]:
    """The value of a closed numeric term under ℕ arithmetic, or None.

    Lean's ℕ arithmetic truncates its division and saturates its subtraction
    at zero; a term that needs a signed value (a negation) has no ℕ reading
    at all.
    """
    if isinstance(node, Num):
        if node.is_float or node.value < 0:
            return None
        return node.value
    if isinstance(node, Neg):
        # ℕ has no negation: the term has no ℕ reading.
        return None
    if isinstance(node, BinOp):
        left = _nat_term_value(node.left)
        right = _nat_term_value(node.right)
        if left is None or right is None:
            return None
        if node.op == '+':
            return left + right
        if node.op == '-':
            return max(left - right, 0)
        if node.op == '*':
            return left * right
        if node.op == '/':
            return 0 if right == 0 else left // right
        if node.op == '^':
            if right > _MAX_EVAL_EXPONENT:
                return None
            return left ** right
    return None


# The relation operators, by AST node type.
_RELATION_OPERATORS: Dict[type, str] = {
    Eq: '=', Ne: '!=', Lt: '<', Le: '<=', Gt: '>', Ge: '>=',
}


def _compare(operator: str, left: Any, right: Any) -> Optional[bool]:
    """The truth of ``left operator right``, or None when it is unknown."""
    if operator == '=':
        return left == right
    if operator == '!=':
        return left != right
    if operator == '<':
        return left < right
    if operator == '<=':
        return left <= right
    if operator == '>':
        return left > right
    if operator == '>=':
        return left >= right
    return None


def _reading_is_faithful(node: Optional[ASTNode]) -> bool:
    """True when the ℕ reading of a closed statement says the SAME thing as
    its exact (ℚ) reading.

    A statement may only be read at ℕ when the reading does not change the
    claim: ℕ truncates its division and saturates its subtraction, so
    ``5 / 2 = 2`` is TRUE at ℕ and FALSE at ℚ, while ``4 / 2 = 2`` is true
    at both.  A statement that cannot be evaluated exactly (it is open, or
    it divides by zero) has no verdict here, and is not faithful.
    """
    if not isinstance(node, (Eq, Ne, Lt, Le, Gt, Ge)):
        return False
    exact_left = _exact_term_value(node.left)
    exact_right = _exact_term_value(node.right)
    nat_left = _nat_term_value(node.left)
    nat_right = _nat_term_value(node.right)
    if (exact_left is None or exact_right is None
            or nat_left is None or nat_right is None):
        return False
    operator = _RELATION_OPERATORS[type(node)]
    exact_truth = _compare(operator, exact_left, exact_right)
    nat_truth = _compare(operator, nat_left, nat_right)
    return exact_truth is not None and exact_truth == nat_truth


# ---------------------------------------------------------------------------
# Rendering the statement as Lean.
#
# The input language is not Lean: implicit multiplication (``2ab``) and the
# LaTeX-like macros (``\frac``, ``\le``, ``a^{2}``) are part of it, and
# Lean has none of them.  Interpolating the user's text into the theorem
# therefore handed Lean a statement it cannot even parse -- the pipeline
# accepted the input, then failed on a statement the user never wrote.
#
# The rendering keeps the shape the PARSER read: it uses the same
# normalization, so the term Lean receives is the term that was parsed.
# Two adjustments are Lean-specific:
#
#   * a QUALIFIED name followed by an operand is an APPLICATION
#     (``Nat.succ 0``), not a product: Lean has no ``Nat.succ * 0``;
#   * ``!=`` is not a Lean operator -- Lean spells it ``≠``.
# ---------------------------------------------------------------------------

# A Lean name, possibly qualified (``Nat.succ``).
_LEAN_NAME = r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*'

# Two operands separated by whitespace, with no operator between them.
# The parser reads that adjacency as a product, so Lean has to see one too.
_LEAN_ADJACENCY_RE = re.compile(
    r'(?P<left>' + _LEAN_NAME + r'|\d+|\))'
    r'(?P<space>\s+)'
    r'(?P<right>' + _LEAN_NAME + r'|\d+|\()'
)


def _lean_adjacency(match: 're.Match[str]') -> str:
    """Render one adjacent pair of operands as Lean.

    A qualified name applied to an operand is an APPLICATION in Lean, so
    ``Nat.succ 0`` stays as it is; every other adjacency is a product.

    The left operand must also really START where the match starts: the
    regex can find the tail of a name (``lpha`` in ``\\alpha``), and a
    LaTeX control word is not an operand at all.  Both are left alone, so
    an unsupported macro stays unsupported instead of being mangled.
    """
    left = match.group('left')
    if left != ')':
        before = match.string[:match.start()]
        if before and (before[-1].isalnum() or before[-1] in '_\\'):
            return match.group(0)
    if '.' in left:
        return match.group(0)
    return f'{left} * {match.group("right")}'


def to_lean_expression(expression: str) -> str:
    """Render *expression* as a Lean term.

    The result is the statement the USER wrote, in Lean's vocabulary: the
    same structure the parser read, with the implicit products made
    explicit and the LaTeX-like macros expanded.
    """
    text = normalize_implicit_multiplication_expression(expression)
    text = _LEAN_ADJACENCY_RE.sub(_lean_adjacency, text)
    # Lean has no `!=` operator; `≠` is how it spells "not equal".
    return text.replace('!=', '≠')


# ---------------------------------------------------------------------------
# Tactic policy.
#
# The tactic a statement gets is decided from its AST, never from its TEXT.
# A text heuristic cannot tell a derivative from an ordinary ratio, a
# numeral from an identifier that happens to contain digits, or a
# polynomial identity from a goal that merely mentions "ring" -- and each
# of those mistakes hands the prover a tactic that cannot close the goal.
#
# The policy has three parts:
#
#   * a SHAPE: the facts about a statement that are read off its AST
#     (identity? field division? polynomial? ordered? closed numeric?);
#   * a PLAN: the tactic CHAINS the shape makes worth trying, in order;
#   * a COMPOSER: a chain is built from ATOMIC STEPS, so a combination
#     like "field_simp; ring" is DERIVED from the statement instead of
#     being pasted in as a literal.
# ---------------------------------------------------------------------------

# The atomic steps a candidate chain is built from.  A chain is rendered by
# joining its steps with "; ", so "field_simp; ring" is COMPOSED from two
# steps rather than written as one literal.
_TACTIC_STEPS: Dict[str, str] = {
    'intros': 'intros',
    'intro': 'intro',
    'dsimp': 'dsimp',
    'field_simp': 'field_simp',
    'ring': 'ring',
    'ring_nf': 'ring_nf',
    'linarith': 'linarith',
    'positivity': 'positivity',
    'norm_num': 'norm_num',
    'decide': 'decide',
    'omega': 'omega',
    'simp': 'simp',
    'simp_mul_div': 'simp [mul_sub, mul_div_assoc]',
    'rfl': 'rfl',
    'refl': 'refl',
    'assumption': 'assumption',
}


def compose_tactic(steps: Sequence[str]) -> str:
    """Render a chain of atomic steps as ONE Lean tactic block.

    ``compose_tactic(['field_simp', 'ring'])`` is ``'field_simp; ring'``: the
    combination is derived from the steps, not pasted in as a literal.
    """
    return '; '.join(_TACTIC_STEPS.get(step, step) for step in steps)


@dataclass
class StatementShape:
    """The facts about a statement that the tactic policy decides on.

    Every field is read off the statement's AST.  ``node`` is None when the
    statement could not be parsed at all; the policy then assumes the
    weakest facts (no division, no power, no numerals), which keeps the
    selection fail-safe rather than arbitrary.
    """

    node: Optional[ASTNode] = None
    free_vars: List[str] = field(default_factory=list)
    is_derivative: bool = False
    is_identity: bool = False
    is_closed_numeric: bool = False
    has_division: bool = False
    has_field_division: bool = False
    has_power: bool = False
    has_numeral: bool = False
    has_numeric_ops: bool = False
    is_inequality: bool = False
    is_strict: bool = False
    is_positivity_claim: bool = False
    is_metzler_positivity: bool = False
    is_step_conservation: bool = False
    is_boundary_flow: bool = False


@dataclass
class GoalState:
    """What the prover knows about the goal it has to close.

    The goal itself is only ONE part of the state: the local hypotheses
    decide whether the goal is already in the context, and the ambient
    type decides whether it is a decidable proposition.
    """

    text: str = ''
    node: Optional[ASTNode] = None
    shape: StatementShape = field(default_factory=StatementShape)
    hypotheses: List[str] = field(default_factory=list)
    expected_type: str = ''


def _is_positivity_claim(node: Optional[ASTNode]) -> bool:
    """A comparison of a product or a ratio against zero.

    ``k * x > 0`` is a claim about the SIGNS OF THE FACTORS, which is what
    ``positivity`` discharges.  A bare ``x > 0`` is not: there the
    non-negativity would be the conclusion itself.
    """
    if not isinstance(node, (Lt, Le, Gt, Ge)):
        return False
    for side, other in ((node.left, node.right), (node.right, node.left)):
        if isinstance(side, Num) and side.value == 0:
            return contains_op(other, '*') or contains_op(other, '/')
    return False


def _shape_from_node(node: Optional[ASTNode]) -> StatementShape:
    """Read the policy's facts about *node* off its AST."""
    shape = StatementShape(node=node)
    if node is None:
        return shape
    shape.free_vars = extract_free_variables(node)
    shape.is_derivative = is_derivative(node)
    shape.has_division = contains_op(node, '/')
    shape.has_field_division = has_rational_structure(node)
    shape.has_power = has_polynomial_structure(node)
    shape.has_numeral = has_numeric_literal(node)
    shape.has_numeric_ops = has_numeric_ops(node)
    shape.is_inequality = is_inequality(node)
    shape.is_strict = isinstance(node, (Lt, Gt))
    shape.is_identity = isinstance(node, Eq) and _is_identity(node)
    shape.is_closed_numeric = (
        isinstance(node, Eq)
        and not shape.free_vars
        and _is_numeric_only(node.left)
        and _is_numeric_only(node.right)
    )
    shape.is_positivity_claim = _is_positivity_claim(node)
    shape.is_metzler_positivity = is_positivity(node)
    shape.is_step_conservation = is_discrete_step_conservation(node)
    shape.is_boundary_flow = is_nonneg_product(node)
    return shape


def _plan_for_shape(shape: StatementShape) -> List[List[str]]:
    """The tactic chains *shape* makes worth trying, most specific first.

    Each chain is a list of ATOMIC STEP NAMES; the caller renders it with
    :func:`compose_tactic`.  The order is the policy: the most specific
    shape gets the most specific chain, and the generic tactics are only
    appended as a fallback by the caller.
    """
    # A closed numeric equality: ``simp``/``decide`` discharge it without
    # assuming anything, and they are a stronger credibility signal than
    # ``rfl``.
    if shape.is_closed_numeric:
        return [['simp'], ['decide'], ['norm_num'], ['ring']]
    # A rate-of-change statement: ``dsimp`` normalizes the derivative head,
    # ``field_simp`` clears the divisions, ``ring`` closes the identity.
    if shape.is_derivative:
        return [
            ['intros', 'dsimp', 'field_simp', 'ring'],
            ['intros', 'field_simp', 'ring'],
            ['dsimp'], ['field_simp'], ['ring_nf'], ['simp'],
            ['norm_num'], ['decide'],
        ]
    # A reflexive statement: both sides are structurally equal.
    if shape.is_identity:
        return [['rfl'], ['simp'], ['refl']]
    # A Jacobian off-diagonal (Metzler) positivity claim.
    if shape.is_metzler_positivity:
        return [
            ['intros', 'positivity'], ['positivity'],
            ['intros', 'field_simp', 'ring'],
        ]
    # A discrete-step conservation claim.
    if shape.is_step_conservation:
        return [
            ['intros', 'field_simp', 'ring'], ['field_simp'],
            ['ring'], ['intros', 'positivity'],
        ]
    # A boundary inflow non-negativity claim: (E / F) * A >= 0.
    if shape.is_boundary_flow:
        return [
            ['intros', 'positivity'],
            ['intros', 'field_simp', 'linarith'],
            ['intros', 'field_simp', 'ring'],
            ['positivity'], ['linarith'],
        ]
    # A strict inequality over a division: a positivity claim about the
    # ratio, discharged by ``positivity`` over the positivity hypotheses.
    if shape.is_strict and shape.has_division:
        return [
            ['intros', 'positivity'],
            ['intros', 'field_simp', 'positivity'],
            ['positivity'],
        ]
    # A field statement: the division is symbolic, so the divisions have to
    # be cleared before any polynomial tactic applies.
    if shape.has_field_division:
        return [
            ['intros', 'positivity'],
            ['intros', 'field_simp', 'ring'],
            ['intros', 'dsimp', 'field_simp', 'ring'],
            ['intros', 'simp_mul_div', 'ring'],
            ['intro'], ['dsimp'], ['field_simp'], ['simp_mul_div'],
            ['ring_nf'], ['linarith'], ['simp'], ['norm_num'],
        ]
    # A division over an exact numeric denominator.
    if shape.has_division:
        return [
            ['intros', 'positivity'],
            ['intros', 'field_simp', 'ring'],
            ['field_simp'], ['ring'], ['norm_num'], ['simp'],
        ]
    # An ordered claim.
    if shape.is_inequality:
        return [
            ['intros', 'positivity'],
            ['intros', 'linarith'],
            ['linarith'], ['omega'], ['simp'], ['norm_num'],
        ]
    # A polynomial identity.
    if shape.has_power:
        return [['ring'], ['simp'], ['linarith'], ['norm_num']]
    # Anything else.
    return [['rfl'], ['simp'], ['norm_num'], ['decide'], ['ring']]


class LeanAgenticPipeline:
    """
    Pipeline that converts mathematical statements to verified Lean 4 proofs.
    
    Uses iterative tactic search with strict verification: success requires
    the final Lean file to compile without `sorry` placeholders.
    """
    
    # The outputs a run produces: the audit trail and the verified
    # Lean artefact.  Both are written by ``run()`` -- the PUBLIC entry
    # point -- so the CLI and a programmatic caller get the same files.
    TRACE_FILE = "traces.json"
    ARTIFACT_FILE = "output.lean"

    def __init__(self, use_mathlib: bool = True, lean_path: Optional[str] = None,
                 adapter: Optional[Any] = None,
                 lean_compile_timeout: int = 180,
                 trace_path: Optional[str] = None,
                 artifact_path: Optional[str] = None):
        """
        Initialize the pipeline.
        
        Args:
            use_mathlib: Whether to use Mathlib tactics
            lean_path: Path to lean executable (or None to search PATH)
            adapter: Optional agent adapter for agentic repair (must have send(prompt, session) method)
            lean_compile_timeout: Seconds allowed for one Lean invocation.
                The default is sized for a COLD Mathlib cache: a clean room or
                a fresh `.lake` has to import Mathlib from source, which is
                far slower than a warm build. A budget tuned to a warm cache
                makes correctness depend on machine speed.
            trace_path: Where to write the audit trail (default ``traces.json``).
            artifact_path: Where to write the verified Lean source
                (default ``output.lean``).
        """
        self.lean_compile_timeout = lean_compile_timeout
        self.trace_path = trace_path or self.TRACE_FILE
        self.artifact_path = artifact_path or self.ARTIFACT_FILE
        self.lean_path = lean_path or self._find_lean()
        # Detect Lake environment for hermetic Mathlib builds
        self._lake_root = self._find_lake_root()
        self._lake_env_lean = self._build_lake_env_lean_cmd()
        # Auto-detect Mathlib availability
        self.use_mathlib = use_mathlib and self._check_mathlib_available()
        self.adapter = adapter
        self.tactic_candidates = [
            'rfl', 'simp', 'norm_num', 'decide', 'ring', 
            'linarith', 'omega', 'field_simp', 'dsimp', 'intro',
            'positivity',
        ]
    
    def _find_lean(self) -> Optional[str]:
        """Find lean executable in PATH."""
        env = os.environ.copy()
        env["PATH"] = str(Path.home() / ".elan" / "bin") + ":" + env.get("PATH", "")
        
        try:
            result = subprocess.run(
                ["which", "lean"],
                capture_output=True,
                text=True,
                env=env,
                timeout=5
            )
            if result.returncode == 0:
                lean_path = result.stdout.strip()
                # Verify lean is actually usable (not just a stub that downloads)
                # Check if toolchain directory exists
                toolchain_dir = Path.home() / ".elan" / "toolchains"
                if toolchain_dir.exists():
                    # Check if there's at least one toolchain installed
                    toolchains = [d for d in toolchain_dir.iterdir() if d.is_dir() and not d.name.endswith('.lock')]
                    if toolchains:
                        return lean_path
                return None
        except Exception:
            pass
        return None
    
    def _find_lake_root(self) -> Optional[Path]:
        """Walk up from CWD to find a directory containing lakefile.lean."""
        d = Path.cwd()
        while d != d.parent:
            if (d / "lakefile.lean").exists():
                return d
            d = d.parent
        if (d / "lakefile.lean").exists():
            return d
        return None
    
    def _build_lake_env_lean_cmd(self) -> Optional[List[str]]:
        """If a Lake root is detected, return the command prefix for
        invoking Lean directly (bypassing ``lake env``).

        NOTE: ``lake env`` SIGTRAP-crashes under some Lake/Lean version
        combinations even though the toolchain's ``lean`` is healthy, so
        we invoke the elan-shimmed ``lean`` directly (it resolves the
        pinned toolchain via the lake root's ``lean-toolchain`` file) and
        supply ``LEAN_PATH`` explicitly via :meth:`_compile_env`.
        """
        if self._lake_root is None:
            return None
        elan_bin = str(Path.home() / ".elan" / "bin")
        lean_bin = os.path.join(elan_bin, "lean")
        if not os.path.isfile(lean_bin):
            return None
        return [lean_bin]

    def _compile_env(self) -> dict:
        """Environment for Lean invocations: explicit LEAN_PATH over the
        Lake root's olean roots (project + all dependency packages)."""
        env = os.environ.copy()
        if self._lake_root is not None:
            parts = [str(self._lake_root / ".lake" / "build" / "lib" / "lean")]
            pkgs = self._lake_root / ".lake" / "packages"
            if pkgs.is_dir():
                for pkg in sorted(pkgs.iterdir()):
                    cand = pkg / ".lake" / "build" / "lib" / "lean"
                    if cand.is_dir():
                        parts.append(str(cand))
            prev = env.get("LEAN_PATH", "")
            env["LEAN_PATH"] = os.pathsep.join(parts) + (os.pathsep + prev if prev else "")
        return env
    
    def _compile_lean_cmd(self, lean_file: str) -> List[str]:
        """Return the full command list to compile *lean_file*.

        When a Lake root with ``lakefile.lean`` is detected, invoke the
        elan-shimmed ``lean`` directly (bypassing crash-prone ``lake env``)
        with ``LEAN_PATH`` from :meth:`_compile_env`.  Otherwise fall back
        to the bare ``lean`` executable.
        """
        if self._lake_env_lean is not None:
            return self._lake_env_lean + [lean_file]
        return [self.lean_path or 'lean', lean_file]
    
    def _check_mathlib_available(self) -> bool:
        """Check if Mathlib is available in the Lean environment."""
        if not self.lean_path:
            return False
        
        env = os.environ.copy()
        env["PATH"] = str(Path.home() / ".elan" / "bin") + ":" + env.get("PATH", "")
        
        try:
            # Create a temporary file to test Mathlib import
            import tempfile
            with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', delete=False) as f:
                f.write("import Mathlib.Tactic\n")
                temp_path = f.name
            
            # Prefer `lake env lean` when a lakefile is present, so Mathlib
            # imports resolve through the hermetic Lake build graph.
            compile_cmd = self._compile_lean_cmd(temp_path)
            
            try:
                env = self._compile_env()
                result = subprocess.run(
                    compile_cmd,
                    capture_output=True,
                    text=True,
                    timeout=60,
                    env=env
                )
                return result.returncode == 0
            except Exception:
                return False
            finally:
                try:
                    os.unlink(temp_path)
                except Exception:
                    pass
        except Exception:
            return False
    
    def validate_input(self, latex_input: str) -> Tuple[bool, str]:
        """
        Validate mathematical input.
        
        Returns:
            (is_valid, error_message)
        """
        if not latex_input or not latex_input.strip():
            return False, "Empty input"
        
        # Basic validation - reject obviously non-mathematical input
        if re.match(r'^[a-zA-Z\s]+$', latex_input.strip()) and not re.search(r'[=<>!]', latex_input):
            return False, "Non-mathematical input"
        
        # Try to parse
        try:
            eq, free_vars = parse_equation(latex_input)
            if eq is None and not free_vars:
                return False, "Could not parse mathematical expression"
        except Exception as e:
            return False, f"Parse error: {str(e)}"
        
        return True, ""
    
    def _parse_statement(self, expression: str) -> Optional[ASTNode]:
        """The AST of a statement, or None when it cannot be parsed."""
        eq, _ = parse_equation(expression)
        if eq is not None:
            return eq
        tokens = tokenize(expression)
        tokens = normalize_implicit_multiplication(tokens)
        node, _ = parse_expression(tokens)
        return node

    def _type_requirements(self, expression: str) -> set[str]:
        """The type requirements the statement's AST imposes.

        Returns a subset of the keys of :data:`_TYPE_REQUIREMENTS`.  A
        statement that cannot be parsed imposes none, which keeps the
        selection fail-safe: it falls back to Nat, the weakest type.
        """
        # ODE / rate-of-change notation lives on ℝ.
        if is_ode(expression) or involves_derivative(expression):
            return {'ODE'}
        node = self._parse_statement(expression)
        if node is None:
            return set()
        requirements: set[str] = set()
        self._collect_type_requirements(node, requirements)
        return requirements

    @classmethod
    def _collect_type_requirements(
        cls,
        node: Optional[ASTNode],
        requirements: set[str],
    ) -> None:
        """Collect the type requirements of *node* into *requirements*."""
        if node is None:
            return
        if isinstance(node, Neg):
            # A negation needs a signed type: ℕ has no negation.
            requirements.add('NEGATIVE')
            cls._collect_type_requirements(node.expr, requirements)
            return
        if isinstance(node, BinOp):
            if node.op == '-':
                # ℕ subtraction TRUNCATES, so at ℕ the statement would be a
                # different claim from the one that was written.
                requirements.add('SUBTRACTION')
            elif node.op == '/':
                if _is_numeric_only(node.right):
                    # An exact numeric ratio: rational arithmetic.
                    requirements.add('RATIONAL')
                else:
                    # A symbolic denominator: the division is a field
                    # operation, so the statement lives on ℝ.
                    requirements.add('FIELD')
            cls._collect_type_requirements(node.left, requirements)
            cls._collect_type_requirements(node.right, requirements)
            return
        if isinstance(node, (Eq, Ne, Lt, Le, Gt, Ge)):
            if isinstance(node, (Lt, Le, Gt, Ge)):
                cls._collect_ordered_requirement(node.left, node.right, requirements)
            cls._collect_type_requirements(node.left, requirements)
            cls._collect_type_requirements(node.right, requirements)

    @staticmethod
    def _collect_ordered_requirement(
        left: Optional[ASTNode],
        right: Optional[ASTNode],
        requirements: set[str],
    ) -> None:
        """An ordered claim over a product or a ratio needs an ordered field.

        A bare comparison (``x > 0``) is left alone: a positivity hypothesis
        for it would be the conclusion, so the pipeline must not invent one.
        A comparison whose non-zero side is a product or a ratio
        (``k * x > 0``) is a positivity claim about the factors, and
        ``positivity`` needs ℝ to discharge it.
        """
        for side in (left, right):
            if isinstance(side, Num):
                continue
            if contains_op(side, '*') or contains_op(side, '/'):
                requirements.add('ORDERED')

    def _suggest_type(self, expression: str) -> str:
        """
        Suggest appropriate type based on expression content.

        The type is the join of the requirements the statement's AST imposes
        (see :meth:`_type_requirements`), so a statement that mixes
        constructs is read at the strongest type any of its parts needs.

        Returns:
            Type string: 'Nat', 'Int', 'Rat', or 'Real'
        """
        requirements = self._type_requirements(expression)
        return _join_types([
            _TYPE_REQUIREMENTS[name]
            for name in requirements
            if name in _TYPE_REQUIREMENTS
        ])

    def _get_var_type(self, variables: List[str], expression: str) -> str:
        """
        Get type for variables based on expression context.

        Args:
            variables: List of variable names
            expression: Full expression string

        Returns:
            Type string for variables
        """
        ideal = self._suggest_type(expression)
        if variables:
            # An OPEN statement carries its type in the variable
            # declarations, so the ideal type is used as-is.
            return ideal
        # A CLOSED statement has no declaration to carry its type: the type
        # can only be pinned by ascribing it inside the statement, and only
        # a type the environment can evaluate may be used.  Core ``Rat`` is
        # a computable rational that ``decide``/``simp`` cannot evaluate
        # (Mathlib's ``Rat`` = ℚ can, via ``norm_num``/``ring``), so without
        # Mathlib a closed rational statement keeps Lean's default ℕ.
        #
        # That fallback is only HONEST when ℕ says the same thing the exact
        # reading says: ℕ truncates its division, so ``5 / 2 = 2`` is true at
        # ℕ and false at ℚ, and reading it at ℕ would report a false claim
        # as verified.  When the two readings disagree the statement keeps
        # its rational type, and the run fails closed instead of proving a
        # different statement.
        if ideal == 'Rat' and not getattr(self, 'use_mathlib', False):
            if _reading_is_faithful(self._parse_statement(expression)):
                return 'Nat'
            return 'Rat'
        return ideal
    
    def check_for_sorry(self, lean_source: str, compiler_output: str) -> Tuple[bool, str]:
        """
        Check if output contains sorry or sorryAx.
        
        Uses word-boundary matching to avoid false positives from identifiers
        containing "sorry" as a substring.
        
        Args:
            lean_source: The Lean source code
            compiler_output: Compiler stdout/stderr
            
        Returns:
            (has_sorry, reason)
        """
        # Check source for sorry or sorryAx (word boundary match)
        # Check fully-qualified patterns first to get specific reason
        if re.search(r'\bLean\.Elab\.Tactic\.sorry\b', lean_source):
            return True, "Lean source contains 'Lean.Elab.Tactic.sorry'"
        if re.search(r'\bTactic\.sorry\b', lean_source):
            return True, "Lean source contains 'Tactic.sorry'"
        if re.search(r'\bsorryAx\b', lean_source):
            return True, "Lean source contains 'sorryAx'"
        if re.search(r'\bsorry\b', lean_source):
            return True, "Lean source contains 'sorry'"
        
        # Check compiler output for sorry or sorryAx (word boundary match)
        if re.search(r'\bsorryAx\b', compiler_output):
            return True, "Compiler output mentions 'sorryAx'"
        
        # Check for Lean 4 warning patterns indicating sorry usage.
        #
        # Lean 4.33 reports a sorry proof as
        #     warning: declaration uses `sorry`
        # -- the token is BACKTICK-quoted, so the literal substring
        # "uses sorry" never appears and a detector written for the bare
        # form matches nothing. Those detectors were therefore dead code:
        # only the generic catch-all below could ever fire, and the precise
        # reasons they were written to produce were unreachable.
        #
        # Match the quoted AND the bare form so the specific detectors are
        # live again; the generic catch-all stays as the backstop.
        if re.search(r'declaration uses\s+[`\'"]?sorry\b', compiler_output):
            return True, "Compiler output indicates declaration uses sorry"
        if re.search(r'warning:.*uses\s+[`\'"]?sorry\b', compiler_output):
            return True, "Compiler output warning indicates sorry usage"
        if re.search(r'uses\s+sorryAx\b', compiler_output):
            return True, "Compiler output indicates uses sorryAx"
        
        if re.search(r'\bsorry\b', compiler_output):
            return True, "Compiler output mentions 'sorry'"
        
        return False, ""
    
    # The name the pipeline gives the theorem it proves. The axioms report is
    # bound to the declaration that was actually checked, so this is the
    # preferred target; a file that names its theorem differently is checked
    # against its own declaration instead.
    GOAL_THEOREM_NAME = "qed_goal"

    @staticmethod
    def _declared_theorem_names(lean_source: str) -> List[str]:
        """Names of the theorems/lemmas declared in *lean_source*.

        Used to bind the axioms check to the declaration that is really in
        the file, instead of assuming a fixed name. Attributes and the
        standard modifiers are tolerated so that a decorated declaration is
        still recognised.
        """
        return re.findall(
            r'^[ \t]*(?:@\[[^\]]*\][ \t]*)*'
            r'(?:(?:private|protected|noncomputable|unsafe|partial)[ \t]+)*'
            r'(?:theorem|lemma)[ \t]+([A-Za-z_][A-Za-z0-9_\'.]*)',
            lean_source,
            re.MULTILINE,
        )

    def _verify_no_sorry_axioms(self, temp_path: str) -> Tuple[bool, str]:
        """
        Verify that a compiled theorem doesn't use sorry axioms.
        
        Runs `#print axioms theorem_name` to check the axiom set.
        
        The check FAILS CLOSED. A file that does not compile, or a file whose
        axioms report is not produced, yields "not clean" -- never "clean".
        The previous version never looked at the compiler's exit code and
        never required the report to exist, so it certified files it had
        not actually inspected: a file with a syntax error came back
        "clean", and a file whose theorem was not named ``qed_goal`` came
        back "clean" because ``#print axioms qed_goal`` errored out and
        nothing was left to grep. Absence of evidence was being read as
        evidence of innocence, which is the one thing a no-sorry gate must
        never do.
        
        Args:
            temp_path: Path to the temporary .lean file
            
        Returns:
            (is_clean, reason) - is_clean is True if no sorry axioms found
        """
        verify_path = temp_path + ".verify.lean"
        try:
            with open(temp_path, 'r') as f:
                original_content = f.read()

            # Bind the report to the declaration that is really in the file.
            names = self._declared_theorem_names(original_content)
            if not names:
                return False, (
                    "Axiom verification failed (fail-closed): the file "
                    "declares no theorem, so no axiom set could be checked"
                )
            target = (
                self.GOAL_THEOREM_NAME
                if self.GOAL_THEOREM_NAME in names
                else names[0]
            )

            verify_code = original_content + f"\n#print axioms {target}\n"
            with open(verify_path, 'w') as f:
                f.write(verify_code)
            
            result = subprocess.run(
                self._compile_lean_cmd(verify_path),
                capture_output=True,
                text=True,
                timeout=self.lean_compile_timeout,
                env=self._compile_env()
            )
            
            output = result.stdout + result.stderr

            # A verify file that did not compile tells us NOTHING about the
            # axiom set, so it cannot be reported as clean.
            if result.returncode != 0:
                return False, (
                    "Axiom verification failed (fail-closed): the axioms "
                    f"check did not compile (exit {result.returncode})"
                )

            # The axioms report is the structured evidence we asked for.
            # Parse it instead of grepping the whole output, so the verdict
            # is about THIS theorem's axiom set.
            depends = re.search(
                r"'%s' depends on axioms:\s*\[([^\]]*)\]" % re.escape(target),
                output,
            )
            if depends:
                axioms = [
                    a.strip() for a in depends.group(1).split(',') if a.strip()
                ]
                sorry_axioms = [a for a in axioms if re.search(r'\bsorry', a)]
                if sorry_axioms:
                    return False, (
                        "#print axioms shows sorry ("
                        + ", ".join(sorry_axioms) + ")"
                    )
                # Belt and braces: a sorry mention anywhere in the output
                # (e.g. a warning about a different declaration in the same
                # file) is a leak, whatever this theorem's axiom list says.
                if re.search(r'\bsorry\b', output):
                    return False, "#print axioms shows sorry"
                return True, ""

            if re.search(
                r"'%s' does not depend on any axioms" % re.escape(target),
                output,
            ):
                if re.search(r'\bsorry\b', output):
                    return False, "#print axioms shows sorry"
                return True, ""

            # No report for the target: the check learned nothing, so it
            # cannot certify anything.
            return False, (
                "Axiom verification failed (fail-closed): no axioms report "
                f"for '{target}' was produced"
            )
            
        except Exception as e:
            return False, f"Axiom verification failed (fail-closed): {e}"
        finally:
            try:
                os.unlink(verify_path)
            except Exception:
                pass

    def _source_on_disk_is_clean(self, temp_path: str) -> Tuple[bool, str]:
        """Re-read the compiled file and confirm it still has no sorry.

        The in-memory string that was handed to the compiler is not proof of
        what is on disk. The file is the artefact a reviewer will re-check
        and re-compile, so the gate has to be evaluated on the file itself.

        Fails closed: a file that cannot be read is not a file that has been
        shown to be sorry-free.
        """
        try:
            with open(temp_path, 'r') as f:
                disk_source = f.read()
        except Exception as e:
            return False, (
                f"Post-compilation source re-read failed (fail-closed): {e}"
            )
        return self.check_for_sorry(disk_source, '')

    @staticmethod
    def _parse_lean_goal(stderr: str) -> Optional[str]:
        """Extract the proof goal after the turnstile (⊢) from Lean 4 compiler stderr.

        Returns the goal text (without the ⊢ prefix) or None if no goal is found.
        Delegates to :meth:`_extract_goal_context` so the call site and the
        adapter prompt always agree on what "the goal" is -- including goals
        that Lean's pretty-printer wrapped onto several lines.
        """
        goal, _hyps = LeanAgenticPipeline._extract_goal_context(stderr)
        return goal

    @staticmethod
    def _extract_goal_context(error_output: str) -> Tuple[Optional[str], List[str]]:
        """Extract the *exact* unsolved goal and its local hypotheses.

        Lean's "unsolved goals" block is the ground truth about what is left to
        prove:

            error: unsolved goals
            context:
            hq : 0 < Q
            hv : 0 < V
            ⊢ Q / V > 0

        Reconstructing the goal from the theorem statement instead (as the
        adapter prompt used to) loses every hypothesis, so the adapter is
        asked to close a goal it cannot possibly see. Reading the block
        verbatim gives the model exactly the context Lean has.

        Returns ``(goal, hypotheses)``; ``goal`` is None when no ``⊢`` is
        present. The goal may be multi-line (Lean's pretty-printer wraps long
        goals onto indented continuation lines), so the whole block is kept.
        """
        if not error_output:
            return None, []

        lines = error_output.splitlines()
        # Prefer the LAST goal: a theorem is compiled statement-then-goal, and
        # earlier ⊢ occurrences belong to the declaration header.
        idx = None
        for i, line in enumerate(lines):
            if "⊢" in line:
                idx = i
        if idx is None:
            return None, []

        first = lines[idx].split("⊢", 1)[1].strip()
        goal_parts = [first] if first else []
        for line in lines[idx + 1:]:
            # A goal continuation is an indented, non-empty line. Anything
            # else starts the next compiler message and ends the goal.
            if not line.strip():
                break
            if not line[:1].isspace():
                break
            if "⊢" in line or line.lstrip().startswith("error"):
                break
            # Keep the line's own indentation: in a wrapped Lean goal the
            # break position is part of how the term parses, and re-indenting
            # it would hand the adapter a differently-shaped goal.
            goal_parts.append(line.rstrip())
        goal = "\n".join(goal_parts).strip() or None

        # Hypotheses: the `context:` block immediately preceding the goal.
        hyps: List[str] = []
        for line in reversed(lines[:idx]):
            stripped = line.strip()
            if not stripped:
                if hyps:
                    break
                continue
            if stripped.lower().startswith("context:"):
                break
            m = re.match(r"^[A-Za-z_][A-Za-z0-9_'.]*\s*:\s*(.+)$", stripped)
            if m and hyps is not None:
                hyps.append(stripped)
                continue
            break
        hyps.reverse()
        return goal, hyps

    def _construct_repair_prompt(
        self,
        goal: str,
        lean_code: str,
        error_output: str,
        expression: str,
    ) -> str:
        """Build an agentic repair prompt from the parsed goal and error context.

        The exact goal Lean reported -- together with its local hypotheses -- is
        what the adapter is asked to close. ``goal`` is only a fallback for when
        the stderr carried no parsable goal block; the real one is recovered
        from ``error_output`` so the model sees the hypotheses the static
        candidates (ring / positivity / field_simp) were actually given.
        """
        exact_goal, hyps = self._extract_goal_context(error_output)
        goal_text = exact_goal or goal
        lines = [
            "You are a Lean 4 proof assistant. The following theorem failed to compile.",
            "",
            f"Theorem expression: {expression}",
            "",
            "Current Lean code:",
            f"```lean\n{lean_code}\n```",
            "",
            "Compiler error (relevant excerpt):",
            f"```\n{error_output[:2000]}\n```",
            "",
        ]
        if hyps:
            lines.append("Local hypotheses in scope:")
            lines.extend(f"  {h}" for h in hyps)
            lines.append("")
        lines.append("The EXACT goal Lean reported as unsolved (close this, verbatim):")
        lines.append(f"⊢ {goal_text}")
        lines.append("")
        lines.append(
            "The deterministic candidates (ring, positivity, field_simp, simp, "
            "linarith) have all FAILED on this goal. Do not repeat them verbatim. "
            "Respond with a SINGLE valid Lean tactic or tactic sequence that "
            "closes the goal above. Output ONLY the tactic text, no explanation. "
            "Examples: `nlinarith [sq_nonneg (x - y)]`, `field_simp` then `ring`, "
            "`exact sub_nonneg.mpr h1`, `positivity`, `simp [h, Nat.add_comm]`."
        )
        return "\n".join(lines)

    @staticmethod
    def _parse_adapter_tactic(response_text: str) -> Optional[str]:
        """Extract a Lean tactic from an adapter response.

        Looks for text inside ```lean ... ``` blocks, or falls back to the
        first non-empty line that looks like a tactic (no period at end,
        contains lowercase letters or known tactic keywords).
        """
        # Try fenced code block first
        fenced = re.search(r'```(?:lean)?\s*\n?(.+?)\n?```', response_text, re.DOTALL)
        if fenced:
            candidate = fenced.group(1).strip()
            if candidate:
                return candidate
        # Fall back: first non-empty line that is not a sentence
        for line in response_text.strip().splitlines():
            line = line.strip()
            if not line:
                continue
            # Skip lines that look like prose (start with capital, end with period)
            if line[0].isupper() and line.endswith('.'):
                continue
            return line
        return None

    def _with_fallbacks(self, candidates: List[str]) -> List[str]:
        """Append the generic tactics that every statement may need.

        The order of the policy is preserved: a fallback never displaces a
        candidate the shape asked for, it only fills in what is missing.
        """
        for tactic in self.tactic_candidates:
            if tactic not in candidates:
                candidates.append(tactic)
        return candidates

    def get_tactic_candidates(self, expression: str) -> List[str]:
        """
        Get ordered tactic candidates for *expression*.

        The order is derived from the statement's AST: the statement is
        parsed once into a :class:`StatementShape`, the shape decides which
        tactic CHAINS are worth trying, and each chain is rendered from
        atomic steps (:func:`compose_tactic`).  Nothing here inspects the
        text of the statement, so a goal that merely mentions a tactic
        cannot capture the policy.

        Args:
            expression: Mathematical expression

        Returns:
            Ordered list of tactic candidates
        """
        shape = _shape_from_node(self._parse_statement(expression))
        plan = _plan_for_shape(shape)
        candidates = [compose_tactic(chain) for chain in plan]
        return self._with_fallbacks(candidates)

    @staticmethod
    def _strip_turnstile(goal: str) -> str:
        """The goal text without Lean's turnstile prefix."""
        text = (goal or '').strip()
        if text.startswith('⊢'):
            text = text[1:].strip()
        return text

    @staticmethod
    def _local_hypotheses(error_info: Dict[str, Any]) -> List[str]:
        """The local hypotheses the prover has in scope, if any.

        They may be handed over directly (``hypotheses``) or come with the
        compiler output Lean reported (``error_output``/``stderr``).
        """
        hypotheses = error_info.get('hypotheses')
        if isinstance(hypotheses, str):
            hypotheses = [hypotheses]
        if isinstance(hypotheses, (list, tuple)):
            found = [h for h in hypotheses if isinstance(h, str) and h.strip()]
            if found:
                return found
        for key in ('error_output', 'stderr', 'compiler_output'):
            output = error_info.get(key)
            if isinstance(output, str) and output:
                _goal, context = LeanAgenticPipeline._extract_goal_context(output)
                if context:
                    return context
        return []

    def _goal_state(self, error_info: Dict[str, Any]) -> 'GoalState':
        """What the prover knows about the goal it has to close."""
        goal_text = self._strip_turnstile(error_info.get('goal', ''))
        node = self._parse_statement(goal_text)
        return GoalState(
            text=goal_text,
            node=node,
            shape=_shape_from_node(node),
            hypotheses=self._local_hypotheses(error_info),
            expected_type=error_info.get('expected_type', '') or '',
        )

    @staticmethod
    def _goal_in_context(state: 'GoalState') -> bool:
        """True when the goal is exactly one of the local hypotheses.

        Then the goal is already proved: ``assumption`` closes it.
        """
        if state.node is None or not state.hypotheses:
            return False
        goal_form = canonical_form(state.node)
        for hypothesis in state.hypotheses:
            _name, separator, proposition = hypothesis.partition(':')
            if not separator:
                proposition = hypothesis
            proposition = proposition.strip()
            if not proposition:
                continue
            node, _ = parse_equation(proposition)
            if node is not None and canonical_form(node) == goal_form:
                return True
        return False

    def _tactic_for_goal_state(self, state: 'GoalState') -> str:
        """The tactic that fits the goal state.

        The order is load-bearing and is not obvious from the branches
        alone:

          * the FIELD branch comes before the polynomial branch, because a
            goal that mixes a power with a division is a field identity --
            ``ring`` cannot clear the division;
          * the ORDERED branch comes before the Bool branch, because a
            comparison is proved by ``linarith`` whatever the ambient type
            is, while the Bool branch is about a decidable proposition.
        """
        shape = state.shape
        # The goal is already in the context.
        if self._goal_in_context(state):
            return 'assumption'
        # A reflexive goal.
        if shape.is_identity:
            return 'rfl'
        # A positivity claim about the factors of a product or a ratio.
        if shape.is_positivity_claim:
            return 'positivity'
        # A field identity: the divisions have to be cleared before any
        # polynomial tactic applies.
        if shape.is_derivative or shape.has_division:
            return 'field_simp'
        # An ordered claim.
        if shape.is_inequality:
            return 'linarith'
        # A Bool-typed goal is a decidable proposition.
        if 'Bool' in state.expected_type:
            return 'decide'
        # Polynomial algebra.
        if shape.has_power:
            return 'ring'
        # Concrete numerals.
        if shape.has_numeral and shape.has_numeric_ops:
            return 'norm_num'
        # Plain algebraic structure (+ or * without ^).
        if shape.has_numeric_ops:
            return 'ring'
        # Nothing to go on.
        return 'simp'

    def select_tactic(self, error_info: Dict[str, Any]) -> str:
        """
        Select a tactic from the goal state.

        The decision is read off the goal's AST and the local hypotheses,
        never off the goal TEXT: a text heuristic cannot tell a derivative
        from an ordinary ratio, a numeral from an identifier that happens
        to contain digits, or a polynomial identity from a goal that merely
        mentions "ring".

        Args:
            error_info: Dictionary with error details.  Recognised keys:
                ``goal`` (with or without the turnstile), ``expected_type``,
                ``hypotheses`` (a list of ``name : proposition`` strings) and
                ``error_output``/``stderr`` (the compiler output the
                hypotheses can be read from).

        Returns:
            Selected tactic
        """
        return self._tactic_for_goal_state(self._goal_state(error_info))
    
    def generate_lean_code(self, expression: str, free_vars: Optional[List[str]] = None) -> str:
        """
        Generate Lean 4 theorem code from mathematical expression.
        
        Args:
            expression: Mathematical expression
            free_vars: List of free variables (defaults to none)
            
        Returns:
            Lean 4 code string
        """
        if free_vars is None:
            free_vars = []

        # The term Lean receives is the term the USER wrote: the input
        # language carries implicit products and LaTeX-like macros that Lean
        # does not understand, so the text is rendered before it is
        # interpolated into the theorem.
        lean_expression = to_lean_expression(expression)

        # Determine type
        var_type = self._get_var_type(free_vars, expression)
        
        # Filter out known Lean identifiers from free variables
        lean_keywords = {'Nat', 'Int', 'Rat', 'Real', 'Bool', 'True', 'False', 'Nat.succ', 'Nat.zero'}
        filtered_vars = [v for v in free_vars if v not in lean_keywords and not v.startswith('Nat.')]
        
        # Build imports and theorem header
        if var_type == 'Real':
            # Real-typed theorems live in ℝ, whose canonical instances are
            # already `Field ℝ` and `LinearOrderedField ℝ`.  An explicit
            # `[Field ℝ]` binder would SHADOW those instances and block
            # ring/field_simp, so none is emitted.
            # `Mathlib.Data.Real.Basic` is the canonical module name. The old
            # `Mathlib.Basic.*.Basic` module it replaces does not exist at the
            # pinned mathlib version (the leftover .olean from the old
            # toolchain is unreadable there), so the rename is required, not
            # cosmetic. One correct import, no fallback chain.
            imports = "import Mathlib.Tactic\nimport Mathlib.Data.Real.Basic\n\n"

            # For parametric field identities (free vars + symbolic division),
            # emit universal quantification with positivity hypotheses for
            # variables that appear in division denominators AND numerators
            # (positivity requires all variables in a ratio to be positive).
            eq_node, _ = parse_equation(expression)
            div_vars = find_division_variables(eq_node) if eq_node else set()
            # Also collect numerator variables from division nodes for
            # positivity (E / F > 0 needs both E > 0 and F > 0).
            if eq_node:
                _collect_division_numerator_vars(eq_node, div_vars)
            hyp_vars = sorted(div_vars & set(filtered_vars)) if div_vars else []

            # For strict inequalities (Gt/Lt) with no division variables,
            # generate strict positivity hypotheses for ALL variables.
            # E.g. k * x > 0 needs (hk : 0 < k) (hx : 0 < x).
            if not hyp_vars and isinstance(eq_node, (Gt, Lt)) and eq_node is not None:
                all_expr_vars: set[str] = set()
                _collect_vars(eq_node, all_expr_vars)
                hyp_vars = sorted(all_expr_vars & set(filtered_vars))

            # For Ge/Le inequalities (>= 0 / <= 0), collect non-division
            # variables that need non-strict positivity (0 ≤ A).  These are
            # state variables bounded below by zero but not in denominators.
            nonstrict_hyp_vars: list[str] = []
            if isinstance(eq_node, (Ge, Le)) and eq_node is not None:
                all_expr_vars_ge: set[str] = set()
                _collect_vars(eq_node, all_expr_vars_ge)
                nonstrict_hyp_vars = sorted(
                    (all_expr_vars_ge - div_vars) & set(filtered_vars)
                )

            # The positivity hypotheses are emitted for a goal that
            # `positivity` can discharge over ℝ (a LinearOrderedField, which
            # plain `ℝ` variables already are), so no extra instance binder
            # is needed.  A goal with no hypothesis at all keeps the plain
            # `ℝ` type.

            if filtered_vars:
                params = ' '.join([f'({v} : ℝ)' for v in filtered_vars])
                strict_hyps = ' '.join([f'(h{v} : 0 < {v})' for v in hyp_vars])
                nonstrict_hyps = ' '.join([f'(hn{v} : 0 ≤ {v})' for v in nonstrict_hyp_vars])
                all_hyps = ' '.join(h for h in [strict_hyps, nonstrict_hyps] if h)
                if all_hyps:
                    theorem = (
                        f"theorem qed_goal {params} {all_hyps} "
                        f": {lean_expression} := by\n"
                    )
                else:
                    theorem = f"theorem qed_goal {params} : {lean_expression} := by\n"
            else:
                # A CLOSED statement has no declaration to carry its type:
                # Lean elaborates the numerals at ℕ, where the division
                # TRUNCATES, so the statement Lean would check would not be
                # the statement that was written (`2 * (1 / 2) < 1` is true
                # at ℕ and false at ℝ).  Ascribing BOTH sides of the
                # relation pins the whole statement at the type that was
                # inferred.
                ascribed = _ascribe_sides(lean_expression, 'ℝ')
                if ascribed is None:
                    theorem = f"theorem qed_goal : {lean_expression} := by\n"
                else:
                    theorem = f"theorem qed_goal : {ascribed} := by\n"
        else:
            # Build theorem statement
            if filtered_vars:
                # An OPEN statement carries its type in the variable
                # declarations, so Lean elaborates it at that type.
                params = ' '.join([f'({v} : {var_type})' for v in filtered_vars])
                theorem = f"theorem qed_goal {params} : {lean_expression} := by\n"
            else:
                # A CLOSED statement has no declaration to carry its type:
                # Lean elaborates the numerals at ℕ, where subtraction and
                # division TRUNCATE, so the statement Lean would check would
                # not be the statement that was written (`1 - 2 = 0` is true
                # at ℕ and false at ℤ).  Ascribing BOTH sides of the relation
                # pins the whole statement at the type that was inferred.
                ascribed = None
                if var_type in ('Int', 'Rat') and self._type_requirements(expression):
                    ascribed = _ascribe_sides(lean_expression, var_type)
                if ascribed is None:
                    theorem = f"theorem qed_goal : {lean_expression} := by\n"
                else:
                    # The relation is preserved: ascribing the two sides
                    # must not turn a `!=` into an `=`.
                    theorem = f"theorem qed_goal : {ascribed} := by\n"
            imports = ""

        # Add imports if using Mathlib (non-Real types)
        if self.use_mathlib and var_type != 'Real':
            imports = "import Mathlib.Tactic\n\n"
        
        return imports + theorem
    
    def execute_tactic_loop(self, expression: str, max_iterations: int = 15) -> Dict[str, Any]:
        """
        Execute tactic search loop to find a working proof.
        
        Args:
            expression: Mathematical expression
            max_iterations: Maximum number of tactic attempts
            
        Returns:
            Dictionary with results
        """
        # Validate input
        is_valid, error_msg = self.validate_input(expression)
        if not is_valid:
            return {
                'success': False,
                'error': error_msg,
                'lean_code': None,
                'attempts': []
            }
        
        # Check if Lean is available
        if not self.lean_path:
            return {
                'success': False,
                'error': 'Lean compiler not found. Install elan and run: elan default leanprover/lean4:stable',
                'lean_code': None,
                'attempts': []
            }
        
        # Parse expression
        eq, free_vars = parse_equation(expression)

        # Generate base Lean code
        base_code = self.generate_lean_code(expression, free_vars or [])
        
        # Get tactic candidates
        candidates = self.get_tactic_candidates(expression)
        
        attempts = []
        for i, tactic in enumerate(candidates[:max_iterations]):
            # Generate complete Lean code with tactic
            lean_code = base_code + f"  {tactic}\n"
            
            # Write to temporary file
            with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', delete=False) as f:
                f.write(lean_code)
                temp_path = f.name
            
            try:
                # Compile – prefer `lake env lean` when a lakefile is present
                result = subprocess.run(
                    self._compile_lean_cmd(temp_path),
                    capture_output=True,
                    text=True,
                    timeout=self.lean_compile_timeout,
                    env=self._compile_env()
                )
                
                # Check for sorry
                has_sorry, sorry_reason = self.check_for_sorry(lean_code, result.stdout + result.stderr)
                
                attempt = {
                    'iteration': i,
                    'tactic': tactic,
                    'exit_code': result.returncode,
                    'has_sorry': has_sorry,
                    'sorry_reason': sorry_reason,
                    'stdout': result.stdout[:500],
                    'stderr': result.stderr[:500]
                }
                attempts.append(attempt)
                
                # Success if compiled without sorry
                if result.returncode == 0 and not has_sorry:
                    # Post-compilation re-read: the gate is evaluated on the
                    # FILE, not only on the string that was handed to the
                    # compiler. The file is what a reviewer re-checks, so a
                    # file that carries a sorry must not be reported as
                    # verified even when the compiled source was clean.
                    disk_sorry, disk_reason = self._source_on_disk_is_clean(temp_path)
                    if disk_sorry:
                        attempt['has_sorry'] = True
                        attempt['sorry_reason'] = f"Post-compilation source re-read: {disk_reason}"
                        continue
                    
                    # Additional verification: check axioms if compilation succeeded
                    axioms_clean, axioms_reason = self._verify_no_sorry_axioms(temp_path)
                    
                    if axioms_clean:
                        return {
                            'success': True,
                            'lean_code': lean_code,
                            'tactic': tactic,
                            'attempts': attempts,
                            'verification': {
                                'source_check': 'passed',
                                'compiler_check': 'passed',
                                'axioms_check': 'passed'
                            }
                        }
                    else:
                        # Axioms check failed - this is a sorry leak
                        attempt['has_sorry'] = True
                        attempt['sorry_reason'] = axioms_reason
                        continue
                
            except subprocess.TimeoutExpired:
                attempts.append({
                    'iteration': i,
                    'tactic': tactic,
                    'exit_code': -1,
                    'has_sorry': False,
                    'sorry_reason': '',
                    'stdout': '',
                    'stderr': 'Timeout'
                })
            except Exception as e:
                attempts.append({
                    'iteration': i,
                    'tactic': tactic,
                    'exit_code': -1,
                    'has_sorry': False,
                    'sorry_reason': '',
                    'stdout': '',
                    'stderr': str(e)
                })
            finally:
                # Cleanup
                try:
                    os.unlink(temp_path)
                except Exception:
                    pass

        # --- Agentic repair: after static candidates exhaust, use adapter ---
        if self.adapter is not None:
            # Collect the last error output that contains a goal
            last_goal: Optional[str] = None
            last_error: str = ""
            for att in reversed(attempts):
                combined = att.get('stdout', '') + '\n' + att.get('stderr', '')
                goal = self._parse_lean_goal(combined)
                if goal is not None:
                    last_goal = goal
                    last_error = combined
                    break

            if last_goal is not None:
                for repair_idx in range(3):
                    prompt = self._construct_repair_prompt(
                        last_goal, base_code, last_error, expression,
                    )
                    try:
                        session = type('obj', (object,), {
                            'session_id': f'qed-repair-{repair_idx}',
                            'project_dir': os.getcwd(),
                        })()
                        state = self.adapter.send(prompt, session)
                        response_text = getattr(state, 'logs', '') or ''
                        tactic = self._parse_adapter_tactic(response_text)
                        if tactic is None:
                            continue

                        lean_code = base_code + f"  {tactic}\n"
                        with tempfile.NamedTemporaryFile(
                            mode='w', suffix='.lean', delete=False,
                        ) as f:
                            f.write(lean_code)
                            temp_path = f.name
                        try:
                            result = subprocess.run(
                                self._compile_lean_cmd(temp_path),
                                capture_output=True, text=True,
                                timeout=self.lean_compile_timeout,
                                env=self._compile_env(),
                            )
                            has_sorry, sorry_reason = self.check_for_sorry(
                                lean_code, result.stdout + result.stderr,
                            )
                            attempt = {
                                'iteration': len(attempts) + repair_idx,
                                'tactic': f'[adapter] {tactic}',
                                'exit_code': result.returncode,
                                'has_sorry': has_sorry,
                                'sorry_reason': sorry_reason,
                                'stdout': result.stdout[:500],
                                'stderr': result.stderr[:500],
                            }
                            attempts.append(attempt)
                            if result.returncode == 0 and not has_sorry:
                                # Same gate as the static path: re-read the
                                # file that was actually compiled, so a
                                # sorry-bearing artefact cannot be reported
                                # as verified just because the in-memory
                                # source was clean.
                                disk_sorry, disk_reason = (
                                    self._source_on_disk_is_clean(temp_path)
                                )
                                if disk_sorry:
                                    attempt['has_sorry'] = True
                                    attempt['sorry_reason'] = (
                                        f"Post-compilation source re-read: {disk_reason}"
                                    )
                                    continue
                                axioms_clean, axioms_reason = (
                                    self._verify_no_sorry_axioms(temp_path)
                                )
                                if axioms_clean:
                                    return {
                                        'success': True,
                                        'lean_code': lean_code,
                                        'tactic': f'[adapter] {tactic}',
                                        'attempts': attempts,
                                        'verification': {
                                            'source_check': 'passed',
                                            'compiler_check': 'passed',
                                            'axioms_check': 'passed',
                                        },
                                    }
                                else:
                                    attempt['has_sorry'] = True
                                    attempt['sorry_reason'] = axioms_reason
                        except Exception:
                            pass
                        finally:
                            try:
                                os.unlink(temp_path)
                            except Exception:
                                pass
                    except Exception:
                        continue

        # A Lean invocation that never finished is NOT a refutation. It is an
        # infrastructure failure, and conflating the two is how a verification
        # system starts lying: importing Mathlib from a cold cache routinely
        # takes far longer than a warm build, so a provable goal times out,
        # every tactic is recorded as "did not work", and the pipeline
        # reports "No tactic succeeded" as though the statement were unprovable.
        # That failure is silent (the only trace is stderr='Timeout' buried in
        # attempts) and it is environment-dependent, so it turns a correct
        # suite into a coin flip on a slow or clean-room machine.
        #
        # So: a realistic budget for a cold Mathlib import, and if NO attempt
        # ever got a verdict, say that explicitly rather than implying the
        # mathematics failed.
        verdict_obtained = any(
            a.get('exit_code') != -1 or a.get('stderr') != 'Timeout'
            for a in attempts
        )
        if not verdict_obtained and attempts:
            return {
                'success': False,
                'error': (
                    f'No verdict from the Lean compiler after {len(attempts)} '
                    f'attempts: every attempt hit the {self.lean_compile_timeout}s '
                    f'timeout. This is an environment/timeout failure, NOT a '
                    f'refutation -- the statement was never disproved and may '
                    f'well be provable. Raise lean_compile_timeout or warm the '
                    f'build cache.'
                ),
                'lean_code': base_code,
                'attempts': attempts,
                'infrastructure_failure': True,
            }

        return {
            'success': False,
            'error': f'No tactic succeeded after {len(attempts)} attempts',
            'lean_code': base_code,
            'attempts': attempts
        }
    
    def _execute_with_initial_code(self, initial_code: str, max_iterations: int = 15) -> Dict[str, Any]:
        """
        Execute tactic loop with pre-generated initial code.
        
        The initial code is only a SOURCE for the statement: its proof is
        discarded and the tactic loop searches for a fresh one, so a `sorry`
        in the initial proof never reaches the result -- the file is rebuilt
        from the statement and re-verified by the loop's own gate.
        
        What the method must not do is ECHO a sorry-bearing artefact back as
        though it were a result, so the failure path below refuses to.
        
        Args:
            initial_code: Initial Lean code
            max_iterations: Maximum iterations
            
        Returns:
            Dictionary with results
        """
        # Extract expression from initial code
        match = re.search(r': (.+?) := by', initial_code)
        if not match:
            # Never echo a sorry-bearing artefact back as a result.
            has_sorry, sorry_reason = self.check_for_sorry(initial_code, '')
            if has_sorry:
                return {
                    'success': False,
                    'error': f'Initial code contains a sorry placeholder: {sorry_reason}',
                    'lean_code': '',
                    'attempts': []
                }
            return {
                'success': False,
                'error': 'Could not extract expression from initial code',
                'lean_code': initial_code,
                'attempts': []
            }
        
        expression = match.group(1)
        return self.execute_tactic_loop(expression, max_iterations)
    
    def write_trace(self, result: Dict[str, Any],
                    path: Optional[str] = None) -> bool:
        """Write the audit trail for *result* to the trace file.

        The trace is a REQUIRED output (the README promises it on both
        success and failure), so it is written by ``run()`` -- the public
        entry point -- rather than only by the CLI.  A programmatic caller
        that forgets to write it would otherwise leave the check "was
        traces.json written?" satisfied by whatever file happened to be on
        disk already, which is how a stale trace passes for a fresh one.

        Writing the trace must never turn a VERIFIED proof into a crash:
        an unwritable path is reported in the result (``trace_error``) and
        the run's verdict is left untouched.

        Returns:
            True when the trace was written, False when it could not be.
        """
        target = Path(path or self.trace_path)
        try:
            target.write_text(
                json.dumps(result, indent=2, default=str), encoding='utf-8')
        except (OSError, TypeError, ValueError) as e:
            result['trace_error'] = f"Failed to write {target}: {e}"
            return False
        return True

    def write_artifact(self, result: Dict[str, Any],
                       path: Optional[str] = None) -> bool:
        """Write the VERIFIED Lean source to the artefact file.

        Only a successful run produces an artefact: a failed run must not
        leave a stale proof behind that a reader could mistake for the
        current one.  The bytes written are exactly the source that was
        compiled, so the artefact recompiles on its own.

        Returns:
            True when the artefact was written, False when it could not be
            (or when the run did not succeed).
        """
        if not result.get('success'):
            return False
        source = result.get('lean_code') or ''
        if not source.strip():
            return False
        target = Path(path or self.artifact_path)
        try:
            target.write_text(source, encoding='utf-8')
        except OSError as e:
            result['artifact_error'] = f"Failed to write {target}: {e}"
            return False
        return True

    def run(self, latex_input: str, max_iterations: int = 15) -> Dict[str, Any]:
        """
        Run the full pipeline on mathematical input.

        The audit trail and the verified artefact are written here, not only
        in the CLI: they are the pipeline's outputs, so a programmatic
        caller gets the same files a command-line caller does.

        Args:
            latex_input: Mathematical expression
            max_iterations: Maximum number of tactic attempts
            
        Returns:
            Dictionary with results
        """
        result = self.execute_tactic_loop(latex_input, max_iterations)
        # The artefact first, the trail last: the trail is the record of
        # the run, so it is written once everything else is settled.
        self.write_artifact(result)
        self.write_trace(result)
        return result


def main() -> None:
    """CLI entry point."""
    import argparse as _ap
    ap = _ap.ArgumentParser(description="Lean 4 agentic pipeline")
    ap.add_argument("expression", nargs="?", default=None,
                    help="mathematical expression")
    ap.add_argument("--adapter", default=None,
                    help="adapter name to resolve for agentic repair")
    ap.add_argument("--adapters-config", default=None,
                    help="path to tether config for adapter resolution")
    ap.add_argument("--max-iterations", type=int, default=15,
                    help="iteration limit")
    args = ap.parse_args()

    if not args.expression:
        print("Usage: python3 agentic_pipeline.py <mathematical_expression> [--adapter NAME ...]")
        sys.exit(1)

    expression = args.expression
    adapter = None
    if args.adapter:
        try:
            from tether.adapters import resolve_adapter  # type: ignore
            adapter = resolve_adapter(
                args.adapter,
                config_path=args.adapters_config) if args.adapters_config else resolve_adapter(args.adapter)
        except Exception as e:
            print(f"adapter resolution failed: {e}", file=sys.stderr)
            sys.exit(1)
    pipeline = LeanAgenticPipeline(adapter=adapter)
    
    result = pipeline.run(expression, max_iterations=args.max_iterations)
    # ``run()`` honours ``--max-iterations`` (it is passed straight
    # through) and writes the audit trail to traces.json.

    if result['success']:
        print("✓ Verification Successful! (no sorry)")
        print(f"\nGenerated Lean:\n{result['lean_code']}")
        print(f"\nWinning tactic: {result['tactic']}")
    else:
        print("✗ Verification Failed")
        print(f"Error: {result['error']}")
        attempts = result.get('attempts') or []
        print(f"\nAttempts ({len(attempts)}):")
        for attempt in attempts:
            print(
                f"  [{attempt.get('iteration')}] {attempt.get('tactic')} "
                f"-> exit {attempt.get('exit_code')}"
                + (f" ({attempt.get('sorry_reason')})"
                   if attempt.get('sorry_reason') else "")
            )
        if result.get('infrastructure_failure'):
            print("\nThis was an ENVIRONMENT failure, not a refutation.")

    sys.exit(0 if result['success'] else 1)


if __name__ == "__main__":
    main()
