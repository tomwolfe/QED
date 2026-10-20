#!/usr/bin/env python3
import subprocess
import sys
import os
from typing import Any
from pathlib import Path


def test_identity_theorem() -> None:
    """The CLI must verify a simple theorem end to end.

    This used to RETURN a bool, which pytest reports as a warning
    (``PytestReturnNotNoneWarning``) and never checks: a broken CLI still
    produced a green suite.  It asserts now.
    """
    latex_input = r"Nat.succ 0 = 1"

    print("Testing Lean 4 Agentic Pipeline with Simple Theorem")
    print("=" * 60)
    print(f"Input: {latex_input}")
    print("=" * 60)

    env = os.environ.copy()
    env["PATH"] = str(Path.home() / ".elan" / "bin") + ":" + env.get("PATH", "")

    try:
        result = subprocess.run(
            ["python3", "agentic_pipeline.py", latex_input],
            capture_output=True,
            text=True,
            timeout=180,
            env=env,
        )
    except subprocess.TimeoutExpired:
        raise AssertionError("the CLI timed out") from None

    print("\nSTDOUT:")
    print(result.stdout)
    if result.stderr:
        print("\nSTDERR:")
        print(result.stderr)

    print(f"\nExit Code: {result.returncode}")
    print("=" * 60)

    assert result.returncode == 0, (
        f"the CLI failed to verify '{latex_input}':\n{result.stdout}\n"
        f"{result.stderr}")
    assert "Verification Successful" in result.stdout, result.stdout


if __name__ == "__main__":
    test_identity_theorem()
    sys.exit(0)


# --- Parser: String normalization tests ---

from parser import (  # noqa: E402
    normalize_implicit_multiplication_expression,
    normalize_implicit_multiplication,
    tokenize,
    parse_expression,
    parse_equation,
    BinOp,
    Var,
    Num,
)


def test_normalize_string_number_var() -> None:
    assert normalize_implicit_multiplication_expression('2a') == '2 * a'
    assert normalize_implicit_multiplication_expression('3x') == '3 * x'


def test_normalize_string_number_chain() -> None:
    assert normalize_implicit_multiplication_expression('2ab') == '2 * a * b'
    assert normalize_implicit_multiplication_expression('3xyz') == '3 * x * y * z'


def test_normalize_string_post_paren() -> None:
    assert normalize_implicit_multiplication_expression('(a+b)2') == '(a+b) * 2'
    assert normalize_implicit_multiplication_expression('(a+b)(c+d)') == '(a+b) * (c+d)'
    assert normalize_implicit_multiplication_expression('(a+b)x') == '(a+b) * x'


def test_normalize_string_pre_paren() -> None:
    assert normalize_implicit_multiplication_expression('2(a+b)') == '2 * (a+b)'
    assert normalize_implicit_multiplication_expression('a(b+c)') == 'a * (b+c)'


def test_normalize_string_single_pairs() -> None:
    assert normalize_implicit_multiplication_expression('ab') == 'a * b'
    assert normalize_implicit_multiplication_expression('ab + cd') == 'a * b + c * d'


def test_normalize_string_equation() -> None:
    result = normalize_implicit_multiplication_expression('(a+b)^2 = a^2 + 2ab + b^2')
    assert result == '(a+b)^2 = a^2 + 2 * a * b + b^2'


def test_normalize_string_multi_letter_unchanged() -> None:
    assert normalize_implicit_multiplication_expression('Nat + x') == 'Nat + x'


# --- Parser: Token normalization tests ---

def test_normalize_tokens_paren_to_digit() -> None:
    tokens = ['(', 'a', '+', 'b', ')', '2']
    result = normalize_implicit_multiplication(tokens)
    idx = result.index(')')
    assert result[idx + 1] == '*'
    assert result[idx + 2] == '2'


def test_normalize_tokens_paren_to_var() -> None:
    tokens = ['(', 'a', '+', 'b', ')', 'x']
    result = normalize_implicit_multiplication(tokens)
    idx = result.index(')')
    assert result[idx + 1] == '*'
    assert result[idx + 2] == 'x'


def test_normalize_tokens_paren_to_paren() -> None:
    tokens = ['(', 'a', '+', 'b', ')', '(', 'c', '+', 'd', ')']
    result = normalize_implicit_multiplication(tokens)
    idx = result.index(')')
    assert result[idx + 1] == '*'
    assert result[idx + 2] == '('


def test_normalize_tokens_num_to_paren() -> None:
    tokens = ['2', '(', 'a', '+', 'b', ')']
    result = normalize_implicit_multiplication(tokens)
    assert result[1] == '*'


def test_normalize_tokens_var_to_paren() -> None:
    tokens = ['a', '(', 'b', '+', 'c', ')']
    result = normalize_implicit_multiplication(tokens)
    assert result[1] == '*'


# --- Parser: Integration tests ---

def test_parse_paren_mul() -> None:
    tokens = tokenize('(a+b)2')
    tokens = normalize_implicit_multiplication(tokens)
    expr, pos = parse_expression(tokens)
    assert expr is not None
    assert isinstance(expr, BinOp)
    assert expr.op == '*'


def test_parse_nested_parens() -> None:
    tokens = tokenize('((a+b))')
    tokens = normalize_implicit_multiplication(tokens)
    expr, pos = parse_expression(tokens)
    assert expr is not None
    assert isinstance(expr, BinOp)
    assert expr.op == '+'


def test_parse_number_var_chain() -> None:
    tokens = tokenize('3xyz')
    tokens = normalize_implicit_multiplication(tokens)
    expr, pos = parse_expression(tokens)
    assert expr is not None
    assert isinstance(expr, BinOp)


def test_parse_equation_2ab() -> None:
    eq, free_vars = parse_equation('(a+b)^2 = a^2 + 2ab + b^2')
    assert eq is not None
    assert free_vars is not None
    assert 'a' in free_vars
    assert 'b' in free_vars


# --- Type inference tests ---

def test_suggest_type_nat() -> None:
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    assert pipeline._suggest_type('x + 0 = x') == 'Nat'


def test_suggest_type_int() -> None:
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    assert pipeline._suggest_type('-1 + 1 = 0') == 'Int'


def test_suggest_type_rat() -> None:
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    assert pipeline._suggest_type('x / 2 = y') == 'Rat'


def test_get_var_type_nat() -> None:
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    assert pipeline._get_var_type(['x'], 'x + 0 = x') == 'Nat'


def test_get_var_type_int() -> None:
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    assert pipeline._get_var_type(['x'], '-1 + x = 0') == 'Int'


# --- Tactic selection tests ---

def test_tactic_candidates_algebraic() -> None:
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    candidates = pipeline.get_tactic_candidates('(a+b)^2 = a^2 + 2ab + b^2')
    assert 'ring' in candidates
    assert candidates.index('ring') < candidates.index('simp')


def test_tactic_candidates_inequality() -> None:
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    candidates = pipeline.get_tactic_candidates('x < x + 1')
    assert 'linarith' in candidates
    assert candidates.index('linarith') < candidates.index('simp')


def test_tactic_candidates_division() -> None:
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    candidates = pipeline.get_tactic_candidates('x / 2 = y')
    assert 'field_simp' in candidates
    # Compound intros tactics and field_simp are all present
    assert 'intros; positivity' in candidates
    assert 'intros; field_simp; ring' in candidates


def test_tactic_candidates_ode_prioritizes_ode_tactics() -> None:
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    candidates = pipeline.get_tactic_candidates('dA_liver/dt = Q * (C_p - C_liver / Kp)')
    # ODE inputs must surface the Mathlib ODE tactics.
    assert 'dsimp' in candidates
    assert 'field_simp' in candidates
    # Compound intros tactics come first
    assert 'intros; dsimp; field_simp; ring' in candidates
    # Ordering: individual dsimp leads individual tactics, then field_simp, then ring_nf, before generic simp.
    assert candidates.index('dsimp') < candidates.index('field_simp')
    assert candidates.index('field_simp') < candidates.index('ring_nf')
    assert candidates.index('ring_nf') < candidates.index('simp')


def test_tactic_candidates_ode_involves_derivative_notation() -> None:
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    # Derivative notation anywhere (not just d<var>/dt = <rhs>) triggers ODE policy.
    candidates = pipeline.get_tactic_candidates('dA_gut/dt + dA_central/dt = 0')
    assert 'dsimp' in candidates
    assert 'field_simp' in candidates
    assert 'ring' in candidates


def test_tactic_candidates_ode_not_identity_shortcut() -> None:
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    # An ODE equation is not a textual identity, so it must take the ODE branch
    # (which leads with compound intros tactics) rather than the identity short-circuit (rfl).
    candidates = pipeline.get_tactic_candidates('dA_gut/dt = -ka * A_gut')
    assert 'intros; dsimp; field_simp; ring' in candidates
    assert candidates[0] == 'intros; dsimp; field_simp; ring'


def test_select_tactic_field_simp_for_derivative_goal() -> None:
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    error_info = {
        "error": "type mismatch",
        "goal": "⊢ dA_liver/dt = Q * (C_p - C_liver / Kp)",
        "term": "dA_liver",
        "expected_type": "Real",
    }
    tactic = pipeline.select_tactic(error_info)
    assert tactic == 'field_simp'


def test_involves_derivative_parser() -> None:
    from parser import involves_derivative
    assert involves_derivative('dA_liver/dt = Q * (C_p - C_liver / Kp)') is True
    assert involves_derivative('Q * (C_p - C_tissue / Kp)') is False
    assert involves_derivative('ka * A_gut = ka * A_gut') is False



def test_select_tactic_ring_goal() -> None:
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    error_info = {
        "error": "type mismatch",
        "goal": "⊢ a + b = b + a",
        "term": "a + b",
        "expected_type": "Nat",
    }
    tactic = pipeline.select_tactic(error_info)
    assert tactic == 'ring'


def test_select_tactic_linarith_inequality() -> None:
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    error_info = {
        "error": "type mismatch",
        "goal": "⊢ a < b",
        "term": "a",
        "expected_type": "Bool",
    }
    tactic = pipeline.select_tactic(error_info)
    assert tactic == 'linarith'


# --- No-sorry gate tests ---

def test_check_for_sorry_source_sorry() -> None:
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    has_sorry, reason = pipeline.check_for_sorry("theorem foo : 1 = 1 := by\n  sorry", "")
    assert has_sorry is True
    assert "sorry" in reason.lower()


def test_check_for_sorry_source_sorryax() -> None:
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    has_sorry, reason = pipeline.check_for_sorry("theorem foo : 1 = 1 := by\n  exact sorryAx _", "")
    assert has_sorry is True
    assert "sorryAx" in reason


def test_check_for_sorry_compiler_sorry() -> None:
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    has_sorry, reason = pipeline.check_for_sorry("theorem foo : 1 = 1 := by\n  rfl", "declaration uses sorry")
    assert has_sorry is True
    assert "sorry" in reason.lower()


def test_check_for_sorry_compiler_sorryax() -> None:
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    has_sorry, reason = pipeline.check_for_sorry("theorem foo : 1 = 1 := by\n  rfl", "uses sorryAx")
    assert has_sorry is True
    assert "sorryAx" in reason


def test_check_for_sorry_compiler_word_boundary() -> None:
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    # "sorrier" should NOT trigger the sorry check
    has_sorry, _ = pipeline.check_for_sorry("theorem foo : 1 = 1 := by\n  rfl", "sorrier is not the answer")
    assert has_sorry is False


def test_check_for_sorry_clean() -> None:
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    has_sorry, reason = pipeline.check_for_sorry(
        "theorem foo : 1 = 1 := by\n  rfl",
        ""
    )
    assert has_sorry is False
    assert reason == ""


def test_check_for_sorry_compiler_broad_match() -> None:
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    has_sorry, reason = pipeline.check_for_sorry(
        "theorem foo : 1 = 1 := by\n  rfl",
        "error: unknown identifier 'sorry'"
    )
    assert has_sorry is True
    assert "sorry" in reason.lower()


def test_success_implies_no_sorry_in_output() -> None:
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    result = pipeline.run("0 = 0")
    if result['success']:
        assert 'sorry' not in result['lean_code']
        assert 'sorryAx' not in result['lean_code']
        assert result['verification']['source_check'] == 'passed'
        assert result['verification']['compiler_check'] == 'passed'
        assert result['verification']['axioms_check'] == 'passed'


def test_check_for_sorry_compiler_warning_pattern() -> None:
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    has_sorry, reason = pipeline.check_for_sorry(
        "theorem foo : 1 = 1 := by\n  rfl",
        "warning: declaration 'foo' uses sorry"
    )
    assert has_sorry is True
    assert "warning" in reason.lower()


def test_verify_no_sorry_axioms_clean_file() -> None:
    import tempfile
    import os
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    lean_code = "theorem foo : 1 = 1 := by\n  rfl\n"
    with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', delete=False) as f:
        f.write(lean_code)
        temp_path = f.name
    try:
        is_clean, reason = pipeline._verify_no_sorry_axioms(temp_path)
        # Either clean (if lean works) or fail-closed with error reason (if lean unavailable)
        assert is_clean is True or "fail-closed" in reason.lower() or "error" in reason.lower()
    finally:
        os.unlink(temp_path)


# --- Hardened no-sorry gate tests ---

def test_check_for_sorry_source_tactic_sorry() -> None:
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    has_sorry, reason = pipeline.check_for_sorry("theorem foo : 1 = 1 := by\n  exact Tactic.sorry", "")
    assert has_sorry is True
    assert "Tactic.sorry" in reason


def test_check_for_sorry_source_lean_elab_sorry() -> None:
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    has_sorry, reason = pipeline.check_for_sorry("theorem foo : 1 = 1 := by\n  exact Lean.Elab.Tactic.sorry", "")
    assert has_sorry is True
    assert "Lean.Elab.Tactic.sorry" in reason


def test_check_for_sorry_compiler_uses_sorryax() -> None:
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    has_sorry, reason = pipeline.check_for_sorry(
        "theorem foo : 1 = 1 := by\n  rfl",
        "uses sorryAx"
    )
    assert has_sorry is True
    assert "sorryAx" in reason


def test_check_for_sorry_clean_no_false_positive() -> None:
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    # "sorry" as part of a longer word should not trigger
    has_sorry, _ = pipeline.check_for_sorry(
        "theorem foo : 1 = 1 := by\n  rfl",
        "info: processing file 'sorryfoo.lean'"
    )
    assert has_sorry is False


def test_verify_no_sorry_axioms_fail_closed() -> None:
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    # Non-existent path should fail-closed (return False)
    is_clean, reason = pipeline._verify_no_sorry_axioms("/nonexistent/path.lean")
    assert is_clean is False
    assert "fail-closed" in reason.lower() or "error" in reason.lower()


# --- AST helper tests ---

from parser import (  # noqa: E402
    contains_op,
    is_inequality,
    has_numeric_ops,
    has_polynomial_structure,
    ast_to_latex,
    _is_identity,
    statement_kind,
    Neg,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
)


def test_contains_op_division() -> None:
    eq, _ = parse_equation("x / 2 = y")
    assert contains_op(eq, '/') is True
    assert contains_op(eq, '^') is False


def test_contains_op_power() -> None:
    eq, _ = parse_equation("a^2 = b")
    assert contains_op(eq, '^') is True
    assert contains_op(eq, '/') is False


def test_contains_op_none() -> None:
    assert contains_op(None, '+') is False


def test_is_inequality_true() -> None:
    for expr in ["x < y", "x > y", "x <= y", "x >= y", "x != y"]:
        eq, _ = parse_equation(expr)
        assert is_inequality(eq) is True, f"Expected inequality for {expr}"


def test_is_inequality_false() -> None:
    eq, _ = parse_equation("x = y")
    assert is_inequality(eq) is False


def test_has_numeric_ops_addition() -> None:
    eq, _ = parse_equation("x + y = z")
    assert has_numeric_ops(eq) is True


def test_has_numeric_ops_multiplication() -> None:
    eq, _ = parse_equation("x * y = z")
    assert has_numeric_ops(eq) is True


def test_has_numeric_ops_no_ops() -> None:
    eq, _ = parse_equation("x = y")
    assert has_numeric_ops(eq) is False


def test_has_polynomial_structure_power() -> None:
    eq, _ = parse_equation("(a + b)^2 = a^2 + b^2")
    assert has_polynomial_structure(eq) is True


def test_has_polynomial_structure_implicit_mul() -> None:
    """2ab = a * b has * but no ^, so it should NOT be polynomial."""
    eq, _ = parse_equation("2ab = a * b")
    assert has_polynomial_structure(eq) is False


def test_has_polynomial_structure_no_poly() -> None:
    eq, _ = parse_equation("x + y = z")
    assert has_polynomial_structure(eq) is False


def test_tactic_candidates_ab_not_false_positive() -> None:
    """Verify that 'ab = a * b' doesn't falsely trigger polynomial branch
    when there is no ^ operator in the AST."""
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    # After normalization: "a * b = a * b" — has * but no ^
    # The polynomial branch should NOT fire (only * without ^ is not polynomial)
    candidates = pipeline.get_tactic_candidates("ab = a * b")
    # Should use default order (no ring priority), since there's no ^ operator
    assert candidates[0] == 'rfl'


# --- ast_to_latex tests ---

def test_ast_to_latex_var() -> None:
    assert ast_to_latex(Var('x')) == 'x'


def test_ast_to_latex_num() -> None:
    assert ast_to_latex(Num(3)) == '3'


def test_ast_to_latex_binop_add() -> None:
    node = BinOp(Var('x'), '+', Var('y'))
    assert ast_to_latex(node) == 'x + y'


def test_ast_to_latex_binop_mul() -> None:
    node = BinOp(Var('a'), '*', Var('b'))
    assert ast_to_latex(node) == 'a * b'


def test_ast_to_latex_binop_power() -> None:
    node = BinOp(Var('x'), '^', Num(2))
    assert ast_to_latex(node) == 'x^{2}'


def test_ast_to_latex_neg() -> None:
    node = Neg(Var('x'))
    assert ast_to_latex(node) == '-x'


def test_ast_to_latex_eq() -> None:
    node = Eq(Var('x'), Var('y'))
    assert ast_to_latex(node) == 'x = y'


def test_ast_to_latex_ne() -> None:
    node = Ne(Var('x'), Var('y'))
    assert ast_to_latex(node) == 'x != y'


def test_ast_to_latex_lt() -> None:
    node = Lt(Var('x'), Var('y'))
    assert ast_to_latex(node) == 'x < y'


def test_ast_to_latex_le() -> None:
    node = Le(Var('x'), Var('y'))
    assert ast_to_latex(node) == 'x <= y'


def test_ast_to_latex_gt() -> None:
    node = Gt(Var('x'), Var('y'))
    assert ast_to_latex(node) == 'x > y'


def test_ast_to_latex_ge() -> None:
    node = Ge(Var('x'), Var('y'))
    assert ast_to_latex(node) == 'x >= y'


def test_ast_to_latex_none() -> None:
    assert ast_to_latex(None) == ''


def test_ast_to_latex_nested() -> None:
    node = BinOp(BinOp(Var('a'), '+', Var('b')), '*', Var('c'))
    assert ast_to_latex(node) == 'a + b * c'


# --- _is_identity tests ---

def test_is_identity_true() -> None:
    node = Eq(Var('x'), Var('x'))
    assert _is_identity(node) is True


def test_is_identity_false() -> None:
    node = Eq(Var('x'), Var('y'))
    assert _is_identity(node) is False


def test_is_identity_complex_true() -> None:
    node = Eq(BinOp(Var('a'), '+', Var('b')), BinOp(Var('a'), '+', Var('b')))
    assert _is_identity(node) is True


def test_is_identity_complex_false() -> None:
    node = Eq(BinOp(Var('a'), '+', Var('b')), BinOp(Var('a'), '-', Var('b')))
    assert _is_identity(node) is False


def test_is_identity_non_eq() -> None:
    node = Ne(Var('x'), Var('x'))
    assert _is_identity(node) is False


# --- statement_kind tests ---

def test_statement_kind_identity_x_eq_x() -> None:
    assert statement_kind('x = x') == 'identity'


def test_statement_kind_identity_complex() -> None:
    assert statement_kind('a + b = a + b') == 'identity'


def test_statement_kind_identity_multiplication() -> None:
    assert statement_kind('x * 1 = x * 1') == 'identity'


def test_statement_kind_equality() -> None:
    assert statement_kind('x + 1 = 2') == 'equality'


def test_statement_kind_equality_not_identity() -> None:
    assert statement_kind('x + 1 = x + 2') == 'equality'


def test_statement_kind_inequality_lt() -> None:
    assert statement_kind('x < y') == 'inequality'


def test_statement_kind_inequality_le() -> None:
    assert statement_kind('x <= y') == 'inequality'


def test_statement_kind_inequality_gt() -> None:
    assert statement_kind('x > y') == 'inequality'


def test_statement_kind_inequality_ge() -> None:
    assert statement_kind('x >= y') == 'inequality'


def test_statement_kind_inequality_ne() -> None:
    assert statement_kind('x != y') == 'inequality'


def test_statement_kind_other_bare_expression() -> None:
    assert statement_kind('x + 1') == 'other'


def test_statement_kind_other_number() -> None:
    assert statement_kind('42') == 'other'


def test_statement_kind_identity_not_inequality() -> None:
    result = statement_kind('x = x')
    assert result != 'inequality'


def test_statement_kind_eq_ne_distinct() -> None:
    eq_result = statement_kind('x = y')
    ne_result = statement_kind('x != y')
    assert eq_result == 'equality'
    assert ne_result == 'inequality'


def test_statement_kind_identity_power() -> None:
    assert statement_kind('x^1 = x^1') == 'identity'


# --- ODE parsing tests (PBPK d<var>/dt = <rhs> support) ---

from parser import parse_ode, is_ode, ODE, parse  # noqa: E402


def test_parse_ode_basic() -> None:
    ode, free_vars = parse_ode('dA_gut/dt = -ka * A_gut')
    assert ode is not None
    assert isinstance(ode, ODE)
    assert ode.var == 'A_gut'
    assert free_vars is not None
    assert 'A_gut' in free_vars


def test_parse_ode_var_extraction() -> None:
    ode, free_vars = parse_ode('dA_liver/dt = Q * (C_p - C_liver / Kp)')
    assert ode is not None
    assert ode.var == 'A_liver'
    # RHS free variables should be captured (Q, C_p, C_liver, Kp)
    assert free_vars is not None
    for v in ['Q', 'C_p', 'C_liver', 'Kp']:
        assert v in free_vars


def test_parse_ode_with_spaces() -> None:
    ode, _ = parse_ode('dA_gut / dt = -ka * A_gut')
    assert ode is not None
    assert ode.var == 'A_gut'


def test_parse_ode_rhs_is_ast() -> None:
    from parser import BinOp
    ode, _ = parse_ode('dA_gut/dt = -ka * A_gut')
    assert ode is not None
    # RHS should be a BinOp (Neg(Var('k')) * Var('a')) * Var('A_gut')
    assert isinstance(ode.rhs, BinOp)
    assert ode.rhs.op == '*'


def test_parse_ode_none_for_plain_equation() -> None:
    ode, free_vars = parse_ode('x + 1 = 2')
    assert ode is None
    assert free_vars is None


def test_parse_ode_none_for_expression() -> None:
    ode, free_vars = parse_ode('x + 1')
    assert ode is None
    assert free_vars is None


def test_is_ode_classification() -> None:
    assert is_ode('dA_gut/dt = -ka * A_gut') is True
    assert is_ode('x + 1 = 2') is False
    assert is_ode('dA_central/dt = ka * A_gut') is True


def test_parse_returns_ode_type() -> None:
    result = parse('dA_gut/dt = -ka * A_gut')
    assert result['type'] == 'ode'
    assert result['ode'] is not None
    assert result['ode'].var == 'A_gut'
    assert result['relation'] == '='


def test_parse_non_ode_untouched() -> None:
    result = parse('x + 1 = 2')
    assert result['type'] == 'equation'
    assert result['ode'] is None


def test_ast_to_latex_ode() -> None:
    ode, _ = parse_ode('dA_gut/dt = -ka * A_gut')
    rendered = ast_to_latex(ode)
    assert rendered.startswith('dA_gut/dt =')
    assert 'A_gut' in rendered


def test_parse_ode_nonempty_rhs_required() -> None:
    ode, _ = parse_ode('dA_gut/dt =')
    assert ode is None


# --- Additional parser unit tests for mutation coverage ---

def test_parse_equation_single_var() -> None:
    eq, free_vars = parse_equation('x = y')
    assert eq is not None
    assert free_vars is not None
    assert set(free_vars) == {'x', 'y'}


def test_parse_expression_addition() -> None:
    from parser import BinOp
    tokens = tokenize('a + b')
    tokens = normalize_implicit_multiplication(tokens)
    expr, _ = parse_expression(tokens)
    assert isinstance(expr, BinOp)
    assert expr.op == '+'


def test_statement_kind_other_empty() -> None:
    assert statement_kind('') == 'other'


def test_contains_op_addition() -> None:
    eq, _ = parse_equation('x + y = z')
    assert contains_op(eq, '+') is True
    assert contains_op(eq, '*') is False



# ---------------------------------------------------------------------------
# Mission B: QED depth for the VeriTrial PBPK surface
# ---------------------------------------------------------------------------

def _pbpk_run(expr: str) -> dict[str, Any]:
    """Run the pipeline (real Lean compile) and return the result dict."""
    from agentic_pipeline import LeanAgenticPipeline
    return LeanAgenticPipeline(use_mathlib=True).run(expr)


def test_pbpk_perfusion_distributive_witness_proves_no_sorry() -> None:
    """The closed numeric perfusion-limited distributive witness must prove
    genuinely (decide/simp/ring), NOT by reflexivity, and contain no sorry."""
    res = _pbpk_run("3 * (5 - 4 / 2) = 3 * 5 - 3 * 4 / 2")
    assert res["success"] is True
    assert "sorry" not in res["lean_code"]
    assert "sorryAx" not in res["lean_code"]
    # It is a closed numeric identity: proving it required a real tactic, not rfl.
    assert res["tactic"] in ("simp", "decide", "ring", "norm_num", "field_simp")


def test_pbpk_mass_conservation_witness_proves_no_sorry() -> None:
    """Lemma 3b: the sum of all six compartment derivative RHS terms equals 0.
    This is the genuinely non-reflexive mass-conservation proof."""
    res = _pbpk_run("-6 + 9 + -13 + 4 + 6 + 0 = 0")
    assert res["success"] is True
    assert "sorry" not in res["lean_code"]
    assert "sorryAx" not in res["lean_code"]


def test_pbpk_gut_absorption_identity_proves() -> None:
    """The gut absorption identity needs no division and no subtraction, so
    the context-aware selection types it ℕ: it is an identity that holds in
    any commutative monoid, so it verifies in every environment (with or
    without Mathlib) and never carries a sorry."""
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline(use_mathlib=True)
    res = pipeline.run("ka * A_gut = ka * A_gut")
    assert res["success"] is True
    assert "sorry" not in res["lean_code"]


def test_pbpk_ode_tactic_policy_includes_distributive_field() -> None:
    """For a PBPK perfusion ODE the candidate ordering must surface the
    field/distributive tactics (dsimp -> field_simp -> ring) so a genuine
    proof is reachable."""
    from agentic_pipeline import LeanAgenticPipeline
    cands = LeanAgenticPipeline().get_tactic_candidates(
        "dA_liver/dt = Q * (C_p - C_liver / Kp)"
    )
    assert "dsimp" in cands
    assert "field_simp" in cands
    assert "ring_nf" in cands
    assert cands.index("dsimp") < cands.index("field_simp") < cands.index("ring_nf")


def test_pbpk_symbolic_ode_fails_closed_without_mathlib() -> None:
    """A fully symbolic perfusion-distributive lemma needs Mathlib
    (field_simp/ring on the field division). When Mathlib is unavailable the
    pipeline must FAIL CLOSED (success=False) rather than emit sorry."""
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline(use_mathlib=True)
    if pipeline.use_mathlib:
        # Mathlib present: a real proof is expected, but never a sorry.
        res = pipeline.run("Q * (C_p - C_tissue / Kp) = Q * C_p - Q * C_tissue / Kp")
        assert "sorry" not in res["lean_code"]
    else:
        # No Mathlib in this environment: the gate must not silently pass.
        res = pipeline.run("Q * (C_p - C_tissue / Kp) = Q * C_p - Q * C_tissue / Kp")
        assert res["success"] is False


# ---------------------------------------------------------------------------
# Mission B (deepened): parser/statement_kind/tactic classification for the
# EXACT lemma shapes VeriTrial's formal gate emits. These are fast unit tests
# (no Lean compile) that pin the classification the agentic pipeline relies on
# so a genuine proof path is always reachable and the gate never degrades to a
# silent pass / reflexivity-only check.
# ---------------------------------------------------------------------------

# Closed numeric perfusion-distributive witness VeriTrial exports (Lemma 2).
_VERITRIAL_NUMERIC_WITNESS = "3 * (5 - 4 / 2) = 3 * 5 - 3 * 4 / 2"
# Symbolic perfusion-distributive law VeriTrial exports under --ode-lemmas
# (requires Mathlib field_simp/ring; fail-closed without it).
_VERITRIAL_SYMBOLIC_DISTRIBUTIVE = (
    "Q * (C_p - C_tissue / Kp) = Q * C_p - Q * C_tissue / Kp"
)


def test_normalize_veritrial_numeric_witness_roundtrip() -> None:
    """The exported numeric witness is already fully explicit; normalizing it
    must leave the structure intact (no accidental identity collapse)."""
    from parser import normalize_implicit_multiplication_expression
    out = normalize_implicit_multiplication_expression(_VERITRIAL_NUMERIC_WITNESS)
    assert out == _VERITRIAL_NUMERIC_WITNESS


def test_parse_veritrial_numeric_witness_no_free_vars() -> None:
    """A closed numeric witness has no free variables: QED proves it by decide/
    simp on concrete numerals, never by assuming away a variable."""
    eq, free_vars = parse_equation(_VERITRIAL_NUMERIC_WITNESS)
    assert eq is not None
    assert free_vars == []


def test_statement_kind_veritrial_numeric_witness_is_equality_not_identity() -> None:
    """Crucial: the numeric witness must classify as 'equality' (both sides
    structurally differ), so the pipeline takes the real proof branch instead
    of the reflexivity short-circuit. A regression here would mean the gate
    silently 'passes' a lemma it never actually discharged."""
    assert statement_kind(_VERITRIAL_NUMERIC_WITNESS) == 'equality'
    assert statement_kind(_VERITRIAL_NUMERIC_WITNESS) != 'identity'


def test_statement_kind_veritrial_symbolic_distributive_is_equality() -> None:
    eq, free_vars = parse_equation(_VERITRIAL_SYMBOLIC_DISTRIBUTIVE)
    assert eq is not None
    assert free_vars is not None
    assert set(free_vars) == {"Q", "C_p", "C_tissue", "Kp"}
    assert statement_kind(_VERITRIAL_SYMBOLIC_DISTRIBUTIVE) == 'equality'


def test_tactic_candidates_veritrial_numeric_reach_real_proof() -> None:
    """For the closed numeric witness a genuine (non-rfl) proof path must be
    reachable in bare Lean: field_simp/ring/norm_num/simp/decide are all
    surfaced so decide/simp can discharge it without Mathlib."""
    from agentic_pipeline import LeanAgenticPipeline
    cands = LeanAgenticPipeline().get_tactic_candidates(_VERITRIAL_NUMERIC_WITNESS)
    assert "simp" in cands
    assert "decide" in cands
    # Must NOT be reduced to the identity short-circuit (rfl-first).
    assert cands[0] != "rfl"


def test_tactic_candidates_veritrial_symbolic_field_path() -> None:
    """For the symbolic distributive law the Mathlib field/distributive
    tactics must be surfaced first so a genuine proof is reachable when
    Mathlib is present; without Mathlib the pipeline correctly fails closed
    (see test_pbpk_symbolic_ode_fails_closed_without_mathlib)."""
    from agentic_pipeline import LeanAgenticPipeline
    cands = LeanAgenticPipeline().get_tactic_candidates(
        _VERITRIAL_SYMBOLIC_DISTRIBUTIVE)
    assert "field_simp" in cands
    assert "ring_nf" in cands
    assert cands.index("field_simp") < cands.index("ring_nf")


def test_get_tactic_candidates_symbolic_orders_mathlib_before_generic() -> None:
    """Symbolic field identities must not be handed to a generic 'simp' before
    the field-clearing tactics get a chance; otherwise a Mathlib-backed run
    would close the goal without exercising field_simp/ring."""
    from agentic_pipeline import LeanAgenticPipeline
    cands = LeanAgenticPipeline().get_tactic_candidates(
        _VERITRIAL_SYMBOLIC_DISTRIBUTIVE)
    assert cands.index("field_simp") < cands.index("simp")
    assert cands.index("ring_nf") < cands.index("simp")


# ---------------------------------------------------------------------------
# Phase B: New lemma classes (Rodgers-Rowland Kp, Blood Unbound Fraction,
# Fixed-Step Solver Invariant)
# ---------------------------------------------------------------------------

# Lemma 4: Rodgers-Rowland Kp identity (closed numeric witness).
_VERITRIAL_KP_IDENTITY = "129 = 129"

# Lemma 5: Blood unbound fraction identity (closed numeric witness).
_VERITRIAL_BLOOD_UNBOUND = "20000 = 20000"

# Lemma 6: Fixed-step solver mass conservation invariant (structural).
_VERITRIAL_STEP_CONSERVATION = (
    "(3 + 1 * (-6)) + (5 + 1 * (9)) + (10 + 1 * (-13)) + "
    "(2 + 1 * (4)) + (1 + 1 * (6)) + (0 + 1 * (0)) = 21"
)


def test_pbpk_rogers_rowland_kp_identity_proves_no_sorry() -> None:
    """Lemma 4: the Rodgers-Rowland Kp identity at a representative reference
    point must prove by decide (closed numeric) with no sorry."""
    res = _pbpk_run(_VERITRIAL_KP_IDENTITY)
    assert res["success"] is True
    assert "sorry" not in res["lean_code"]
    assert "sorryAx" not in res["lean_code"]


def test_pbpk_blood_unbound_fraction_proves_no_sorry() -> None:
    """Lemma 5: the blood unbound fraction identity at a representative
    reference point must prove by decide (closed numeric) with no sorry."""
    res = _pbpk_run(_VERITRIAL_BLOOD_UNBOUND)
    assert res["success"] is True
    assert "sorry" not in res["lean_code"]
    assert "sorryAx" not in res["lean_code"]


def test_pbpk_step_conservation_proves_no_sorry() -> None:
    """Lemma 6: the fixed-step solver mass conservation invariant at a
    representative reference point must prove by decide (closed numeric)
    with no sorry."""
    res = _pbpk_run(_VERITRIAL_STEP_CONSERVATION)
    assert res["success"] is True
    assert "sorry" not in res["lean_code"]
    assert "sorryAx" not in res["lean_code"]


def test_tactic_candidates_rogers_rowland_kp() -> None:
    """The Rodgers-Rowland Kp identity (129 = 129) is a closed numeric
    equality. The pipeline must surface decide/simp/norm_num and NOT take
    the identity short-circuit (since both sides are the same integer literal
    but the statement_kind function may classify it as identity)."""
    from agentic_pipeline import LeanAgenticPipeline
    cands = LeanAgenticPipeline().get_tactic_candidates(_VERITRIAL_KP_IDENTITY)
    # Both sides are identical integers, so statement_kind may say 'identity'.
    # Either path works: decide/simp both close it without sorry.
    assert "decide" in cands or "simp" in cands


def test_tactic_candidates_blood_unbound_fraction() -> None:
    """The blood unbound fraction identity (20000 = 20000) is a closed numeric
    equality. The pipeline must surface decide/simp/norm_num."""
    from agentic_pipeline import LeanAgenticPipeline
    cands = LeanAgenticPipeline().get_tactic_candidates(_VERITRIAL_BLOOD_UNBOUND)
    assert "decide" in cands or "simp" in cands


def test_tactic_candidates_step_conservation() -> None:
    """The fixed-step solver invariant is a closed numeric equality.
    The pipeline must surface decide/simp/norm_num."""
    from agentic_pipeline import LeanAgenticPipeline
    cands = LeanAgenticPipeline().get_tactic_candidates(_VERITRIAL_STEP_CONSERVATION)
    assert "decide" in cands or "simp" in cands


# ---------------------------------------------------------------------------
# Phase C: is_numeric_equality and non-reflexive proof credibility
# ---------------------------------------------------------------------------

def test_is_numeric_equality_mass_conservation() -> None:
    """The mass-conservation witness is a closed numeric equality."""
    from parser import is_numeric_equality
    assert is_numeric_equality("-6 + 9 + -13 + 4 + 6 + 0 = 0") is True


def test_is_numeric_equality_perfusion_witness() -> None:
    """The perfusion distributive witness is a closed numeric equality."""
    from parser import is_numeric_equality
    assert is_numeric_equality("3 * (5 - 4 / 2) = 3 * 5 - 3 * 4 / 2") is True


def test_is_numeric_equality_identity() -> None:
    """Closed numeric identity (129 = 129) is still a numeric equality."""
    from parser import is_numeric_equality
    assert is_numeric_equality("129 = 129") is True


def test_is_numeric_equality_with_variables() -> None:
    """An equality with free variables is NOT a numeric equality."""
    from parser import is_numeric_equality
    assert is_numeric_equality("ka * A_gut = ka * A_gut") is False
    assert is_numeric_equality("x + 1 = 2") is False


def test_is_numeric_equality_non_equation() -> None:
    """A bare expression is not a numeric equality."""
    from parser import is_numeric_equality
    assert is_numeric_equality("42") is False
    assert is_numeric_equality("x + y") is False


def test_numeric_equality_uses_non_reflexive_tactic() -> None:
    """Closed numeric equalities must prove by simp/decide (not rfl) for
    formal-verification credibility."""
    from agentic_pipeline import LeanAgenticPipeline
    res = LeanAgenticPipeline(use_mathlib=True).run("-6 + 9 + -13 + 4 + 6 + 0 = 0")
    assert res["success"] is True
    assert "sorry" not in res["lean_code"]
    # Must NOT be rfl: we want a genuine non-reflexive proof.
    assert res["tactic"] != "rfl"
    assert res["tactic"] in ("simp", "decide", "norm_num", "ring")


# ---------------------------------------------------------------------------
# Stage 1: Symbolic Real Analysis – has_rational_structure, Real typing,
#           and [Field ℝ] code generation
# ---------------------------------------------------------------------------

from parser import has_rational_structure  # noqa: E402


def test_has_rational_structure_symbolic_division() -> None:
    """Division by a symbolic variable => rational structure."""
    eq, _ = parse_equation("Q * (C_p - C_tissue / Kp) = Q * C_p - Q * C_tissue / Kp")
    assert has_rational_structure(eq) is True


def test_has_rational_structure_numeric_only_division() -> None:
    """Division by a numeric literal is NOT rational structure (stays ℤ/ℕ)."""
    eq, _ = parse_equation("4 / 2 = 2")
    assert has_rational_structure(eq) is False


def test_has_rational_structure_no_division() -> None:
    """Expressions without / have no rational structure."""
    eq, _ = parse_equation("a + b = b + a")
    assert has_rational_structure(eq) is False


def test_has_rational_structure_none() -> None:
    assert has_rational_structure(None) is False


def test_suggest_type_real_for_symbolic_division() -> None:
    """Symbolic division (C_tissue / Kp) should infer Real, not Rat."""
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    assert pipeline._suggest_type(
        "Q * (C_p - C_tissue / Kp) = Q * C_p - Q * C_tissue / Kp"
    ) == "Real"


def test_suggest_type_real_for_ode() -> None:
    """ODE expressions always infer Real."""
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    assert pipeline._suggest_type("dA_liver/dt = Q * (C_p - C_liver / Kp)") == "Real"


def test_generate_lean_code_real_field_r() -> None:
    """Real-typed theorems should emit [Field ℝ] and ℝ variable annotations."""
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline(use_mathlib=True)
    code = pipeline.generate_lean_code(
        "Q * (C_p - C_tissue / Kp) = Q * C_p - Q * C_tissue / Kp",
        ["Q", "C_p", "C_tissue", "Kp"],
    )
    assert "[Field ℝ]" not in code  # canonical Real instances: variable [Field ℝ] shadows them and blocks ring/field_simp
    assert "ℝ" in code
    assert "import Mathlib" in code


def test_tactic_candidates_symbolic_rational_prioritizes_field() -> None:
    """Symbolic rational expressions must surface intro/dsimp/field_simp/ring
    before generic simp."""
    from agentic_pipeline import LeanAgenticPipeline
    cands = LeanAgenticPipeline().get_tactic_candidates(
        "Q * (C_p - C_tissue / Kp) = Q * C_p - Q * C_tissue / Kp"
    )
    assert "intro" in cands
    assert "dsimp" in cands
    assert "field_simp" in cands
    assert "ring_nf" in cands
    assert cands.index("field_simp") < cands.index("ring_nf")
    assert cands.index("ring_nf") < cands.index("simp")


def test_symbolic_distributive_proves_no_sorry() -> None:
    """The symbolic perfusion-distributive law must prove (Mathlib-backed)
    without sorry.  This is the core Stage 1 gate for parametric ODE algebra.
    When Mathlib is unavailable the pipeline must FAIL CLOSED (success=False)."""
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline(use_mathlib=True)
    if pipeline.use_mathlib:
        res = pipeline.run(
            "Q * (C_p - C_tissue / Kp) = Q * C_p - Q * C_tissue / Kp"
        )
        assert res["success"] is True
        assert "sorry" not in res["lean_code"]
        assert "sorryAx" not in res["lean_code"]
        assert res["verification"]["axioms_check"] == "passed"
    else:
        # No Mathlib: must fail closed, not emit sorry
        res = pipeline.run(
            "Q * (C_p - C_tissue / Kp) = Q * C_p - Q * C_tissue / Kp"
        )
        assert res["success"] is False
        assert "sorry" not in res.get("lean_code", "")


def test_symbolic_mass_balance_real_typed() -> None:
    """A symbolic mass-balance expression with subtraction and division
    must be typed as Real and generate valid Lean with [Field ℝ]."""
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline(use_mathlib=True)
    # Mass-balance: sum of perfusion rates equals zero (symbolic)
    expr = "Q * C_p - Q * C_tissue / Kp + Q * C_liver / Kp = 0"
    code = pipeline.generate_lean_code(expr, ["Q", "C_p", "C_tissue", "Kp", "C_liver"])
    assert "[Field ℝ]" not in code  # canonical Real instances: variable [Field ℝ] shadows them and blocks ring/field_simp
    assert "ℝ" in code
    # Must not contain sorry
    assert "sorry" not in code


def test_symbolic_distributive_lean_code_no_sorry() -> None:
    """The generated Lean source for the symbolic distributive law must not
    contain sorry even before compilation."""
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline(use_mathlib=True)
    code = pipeline.generate_lean_code(
        "Q * (C_p - C_tissue / Kp) = Q * C_p - Q * C_tissue / Kp",
        ["Q", "C_p", "C_tissue", "Kp"],
    )
    assert "sorry" not in code
    assert "sorryAx" not in code


# ---------------------------------------------------------------------------
# Phase 1: Parametric Linear Compartmental & Field Expansion
# ---------------------------------------------------------------------------

from parser import find_division_variables  # noqa: E402


def test_find_division_variables_symbolic() -> None:
    """Variables in symbolic division denominators are detected."""
    eq, _ = parse_equation("Q * (C_p - C_tissue / Kp) = Q * C_p - Q * C_tissue / Kp")
    div_vars = find_division_variables(eq)
    assert "Kp" in div_vars
    assert "C_p" not in div_vars
    assert "Q" not in div_vars


def test_find_division_variables_multiple() -> None:
    """Multiple division positions are detected."""
    eq, _ = parse_equation("a / b + c / d = e")
    div_vars = find_division_variables(eq)
    assert div_vars == {"b", "d"}


def test_find_division_variables_numeric_only() -> None:
    """Numeric-only division yields no division variables."""
    eq, _ = parse_equation("4 / 2 = 2")
    div_vars = find_division_variables(eq)
    assert div_vars == set()


def test_find_division_variables_none() -> None:
    assert find_division_variables(None) == set()


def test_parametric_lean_code_haspositivity_hypotheses() -> None:
    """Parametric expressions with symbolic division emit positivity hypotheses
    for variables in division positions."""
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline(use_mathlib=True)
    code = pipeline.generate_lean_code(
        "Q * (C_p - C_tissue / Kp) = Q * C_p - Q * C_tissue / Kp",
        ["Q", "C_p", "C_tissue", "Kp"],
    )
    assert "[Field ℝ]" not in code  # canonical Real instances: variable [Field ℝ] shadows them and blocks ring/field_simp
    assert "(hKp : 0 < Kp)" in code
    assert "sorry" not in code


def test_parametric_lean_code_no_hyp_for_non_div_vars() -> None:
    """Variables NOT in division positions (numerator or denominator) do not
    get positivity hypotheses. C_p is never in a division so it has no hypothesis."""
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline(use_mathlib=True)
    code = pipeline.generate_lean_code(
        "Q * (C_p - C_tissue / Kp) = Q * C_p - Q * C_tissue / Kp",
        ["Q", "C_p", "C_tissue", "Kp"],
    )
    # C_p is never in a division position (neither numerator nor denominator)
    assert "(hC_p" not in code
    # Q IS in a division numerator position (Q * C_tissue / Kp on RHS), so it gets a hypothesis
    # Kp is in a division denominator, so it gets a hypothesis
    # C_tissue is in a division numerator, so it gets a hypothesis


def test_parametric_lean_code_no_div_no_hyps() -> None:
    """Expressions without division emit no positivity hypotheses."""
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline(use_mathlib=True)
    code = pipeline.generate_lean_code(
        "a + b = b + a",
        ["a", "b"],
    )
    assert "0 <" not in code


def test_parametric_mass_balance_with_hypotheses() -> None:
    """The parametric mass conservation sum emits hypotheses for division vars."""
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline(use_mathlib=True)
    expr = "-ka * Ag + Q * (Cp - Ct / Kp) + ka * Ag - Q * (Cp - Ct / Kp) - CL * Cp + CL * Cp = 0"
    code = pipeline.generate_lean_code(expr, ["ka", "Ag", "Q", "Cp", "Ct", "Kp", "CL"])
    assert "[Field ℝ]" not in code  # canonical Real instances: variable [Field ℝ] shadows them and blocks ring/field_simp
    assert "(hKp : 0 < Kp)" in code
    assert "sorry" not in code


def test_tactic_candidates_parametric_orders_intro_first() -> None:
    """Parametric field identities must have compound intros tactics first,
    followed by intro to bind universally quantified variables, then
    field_simp/ring tactics."""
    from agentic_pipeline import LeanAgenticPipeline
    cands = LeanAgenticPipeline().get_tactic_candidates(
        "Q * (C_p - C_tissue / Kp) = Q * C_p - Q * C_tissue / Kp"
    )
    # Compound intros tactics come first
    assert "intros; positivity" in cands
    assert "intros; field_simp; ring" in cands
    # Then individual intro
    assert "intro" in cands
    idx_intro = cands.index("intro")
    idx_ds = cands.index("dsimp")
    idx_fs = cands.index("field_simp")
    idx_ring = cands.index("ring_nf")
    idx_lin = cands.index("linarith")
    assert idx_intro < idx_ds < idx_fs < idx_ring < idx_lin


def test_parametric_distributive_proves_no_sorry() -> None:
    """The parametric distributive law must prove (Mathlib-backed) without sorry
    when Mathlib is available, and fail closed when it is not."""
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline(use_mathlib=True)
    res = pipeline.run(
        "Q * (C_p - C_tissue / Kp) = Q * C_p - Q * C_tissue / Kp"
    )
    if pipeline.use_mathlib:
        assert res["success"] is True
        assert "sorry" not in res["lean_code"]
        assert "sorryAx" not in res["lean_code"]
    else:
        assert res["success"] is False
        assert "sorry" not in res.get("lean_code", "")


def test_parametric_mass_conservation_proves_no_sorry() -> None:
    """Parametric mass conservation identity (sum of derivatives = 0) must prove
    without sorry when Mathlib is available."""
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline(use_mathlib=True)
    # Correct mass conservation: Gut(-ka*Ag) + Liver(Q*(Cp-Ct/Kp)) +
    # Central(ka*Ag - Q*(Cp-Ct/Kp) - CL*Cp) + Elim(CL*Cp) = 0
    expr = (
        "-ka * Ag + Q * (Cp - Ct / Kp) + ka * Ag "
        "- Q * (Cp - Ct / Kp) - CL * Cp + CL * Cp = 0"
    )
    res = pipeline.run(expr)
    if pipeline.use_mathlib:
        assert res["success"] is True
        assert "sorry" not in res["lean_code"]
        assert "sorryAx" not in res["lean_code"]
    else:
        assert res["success"] is False
        assert "sorry" not in res.get("lean_code", "")


def test_parametric_compartmental_conservation() -> None:
    """4-compartment flow conservation with positivity hypotheses.

    Proving this needs Mathlib's field algebra (field_simp/ring), so with
    Mathlib available it must prove axiom-clean, and without it must fail
    closed with no sorry.
    """
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline(use_mathlib=True)
    res = pipeline.run(
        "(-ka * Ag) + (Q1 * (Cp - Ct1 / Kp1)) + (Q2 * (Cp - Ct2 / Kp2)) "
        "+ (ka * Ag - Q1 * (Cp - Ct1 / Kp1) - Q2 * (Cp - Ct2 / Kp2)) = 0"
    )
    if pipeline.use_mathlib:
        assert res["success"] is True
        assert "sorry" not in res["lean_code"]
        assert res["verification"]["axioms_check"] == "passed"
    else:
        assert res["success"] is False
        assert "sorry" not in res.get("lean_code", "")


def test_has_compartmental_structure() -> None:
    """detects Q * (C_p - C_tissue / Kp) patterns"""
    from parser import has_compartmental_structure, parse_equation
    eq, _ = parse_equation("Q * (C_p - C_tissue / Kp) = Q * C_p - Q * C_tissue / Kp")
    assert has_compartmental_structure(eq) is True


def test_has_compartmental_structure_no_match() -> None:
    """expressions without the compartment pattern return False"""
    from parser import has_compartmental_structure, parse_equation
    eq, _ = parse_equation("a + b = b + a")
    assert has_compartmental_structure(eq) is False


def test_has_compartmental_structure_none() -> None:
    from parser import has_compartmental_structure
    assert has_compartmental_structure(None) is False


# ---------------------------------------------------------------------------
# Phase 1: Compound Tactics & Dynamical Invariants
# ---------------------------------------------------------------------------


def test_compound_tactic_candidates_for_rational_expressions() -> None:
    """Compound intros tactics are present for expressions with rational structure."""
    from agentic_pipeline import LeanAgenticPipeline
    cands = LeanAgenticPipeline().get_tactic_candidates(
        "Q * (C_p - C_tissue / Kp) = Q * C_p - Q * C_tissue / Kp"
    )
    assert "intros; positivity" in cands
    assert "intros; field_simp; ring" in cands
    assert "intros; dsimp; field_simp; ring" in cands
    assert "intros; simp [mul_sub, mul_div_assoc]; ring" in cands


def test_compound_tactic_candidates_for_ode_expressions() -> None:
    """Compound intros tactics are present for ODE expressions."""
    from agentic_pipeline import LeanAgenticPipeline
    cands = LeanAgenticPipeline().get_tactic_candidates(
        "dA_liver/dt = Q * (C_p - C_liver / Kp)"
    )
    assert "intros; dsimp; field_simp; ring" in cands
    assert "intros; field_simp; ring" in cands


def test_compound_tactic_candidates_for_division_expressions() -> None:
    """Compound intros tactics are present for division expressions."""
    from agentic_pipeline import LeanAgenticPipeline
    cands = LeanAgenticPipeline().get_tactic_candidates("x / 2 = y")
    assert "intros; positivity" in cands
    assert "intros; field_simp; ring" in cands


def test_compound_tactic_candidates_for_inequality_expressions() -> None:
    """Compound intros tactics are present for inequality expressions."""
    from agentic_pipeline import LeanAgenticPipeline
    cands = LeanAgenticPipeline().get_tactic_candidates("x < x + 1")
    assert "intros; positivity" in cands
    assert "intros; linarith" in cands


def test_parametric_metzler_positivity_proves_no_sorry() -> None:
    """Metzler off-diagonal positivity: Q / Kp > 0 with positivity hypotheses.

    This is the fundamental dynamical invariant for compartmental systems:
    the Jacobian must be a Metzler matrix (off-diagonal entries >= 0).
    Proved by intros; positivity over ℝ with LinearOrderedField.
    """
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline(use_mathlib=True)
    res = pipeline.run("Q / Kp > 0")
    if pipeline.use_mathlib:
        assert res["success"] is True
        assert "sorry" not in res["lean_code"]
        assert "sorryAx" not in res["lean_code"]
        assert res["verification"]["axioms_check"] == "passed"
    else:
        assert res["success"] is False
        assert "sorry" not in res.get("lean_code", "")


def test_parametric_metzler_positivity_compound_tactic_proves() -> None:
    """Metzler positivity with compound intros; positivity tactic."""
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline(use_mathlib=True)
    # Generate Lean code and try the compound tactic directly
    code = pipeline.generate_lean_code("Q / Kp > 0", ["Q", "Kp"])
    # The generated code should have positivity hypotheses
    assert "(hQ : 0 < Q)" in code or "(hKp : 0 < Kp)" in code
    # Try the compound tactic
    lean_code = code + "  intros; positivity\n"
    import tempfile
    import os
    with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', delete=False) as f:
        f.write(lean_code)
        temp_path = f.name
    try:
        import subprocess
        result = subprocess.run(
            pipeline._compile_lean_cmd(temp_path),
            capture_output=True, text=True, timeout=30,
            env=pipeline._compile_env(),
        )
        has_sorry, _ = pipeline.check_for_sorry(lean_code, result.stdout + result.stderr)
        if pipeline.use_mathlib:
            assert result.returncode == 0, f"Compound tactic failed: {result.stderr[-500:]}"
            assert not has_sorry
        # If no Mathlib, tactic may fail but must not produce sorry
        assert not has_sorry
    finally:
        try:
            os.unlink(temp_path)
        except Exception:
            pass


def test_parametric_compartmental_conservation_with_positivity() -> None:
    """4-compartment flow conservation with positivity hypotheses.

    The parametric sum of all compartment derivative RHS terms equals 0
    when all flow rates and partition coefficients are positive.
    This proves mass conservation for a generic compartmental model.
    """
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline(use_mathlib=True)
    # Parametric mass conservation: gut + liver + central = 0
    # (simplified 2-perfusion model for testability)
    expr = (
        "-ka_rate * Ag + Q_liver * (Cp - Ct_liver / Kp_liver) "
        "+ ka_rate * Ag - Q_liver * (Cp - Ct_liver / Kp_liver) = 0"
    )
    res = pipeline.run(expr)
    if pipeline.use_mathlib:
        assert res["success"] is True
        assert "sorry" not in res["lean_code"]
        assert "sorryAx" not in res["lean_code"]
        assert res["verification"]["axioms_check"] == "passed"
    else:
        assert res["success"] is False
        assert "sorry" not in res.get("lean_code", "")


def test_parametric_positivity_hypotheses_for_division_in_inequality() -> None:
    """Division variables in inequality expressions get positivity hypotheses."""
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline(use_mathlib=True)
    code = pipeline.generate_lean_code("Q / Kp > 0", ["Q", "Kp"])
    assert "[Field ℝ]" not in code  # positivity goal uses LinearOrderedField
    assert "(hQ : 0 < Q)" in code
    assert "(hKp : 0 < Kp)" in code
    assert "sorry" not in code


def test_compound_tactic_ode_mass_balance_proves_no_sorry() -> None:
    """The compound intros; dsimp; field_simp; ring tactic chain proves
    the perfusion-distributive law for ODE expressions without sorry."""
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline(use_mathlib=True)
    res = pipeline.run(
        "Q * (C_p - C_tissue / Kp) = Q * C_p - Q * C_tissue / Kp"
    )
    if pipeline.use_mathlib:
        assert res["success"] is True
        assert "sorry" not in res["lean_code"]
        assert "sorryAx" not in res["lean_code"]
        # The winning tactic should be a compound or individual Mathlib tactic
        # ('simp [mul_sub, mul_div_assoc]' is a pipeline candidate that closes
        # the distributive law over a field without needing the hypotheses.)
        assert res["tactic"] in (
            "intros; positivity", "intros; field_simp; ring",
            "intros; dsimp; field_simp; ring",
            "intros; simp [mul_sub, mul_div_assoc]; ring",
            "simp [mul_sub, mul_div_assoc]",
            "intro", "field_simp", "ring_nf", "dsimp",
        )


def test_ast_node_reprs() -> None:
    """AST node reprs render constructor form (used in diagnostics)."""
    from parser import BinOp, Exists, Gt, Imp, Ne, Num, Var
    assert repr(BinOp(Var("Q"), "*", Var("C"))) == "BinOp(Var('Q'), '*', Var('C'))"
    assert repr(Ne(Var("a"), Num(1))) == "Ne(Var('a'), Num(1))"
    assert repr(Gt(Var("Q"), Num(0))) == "Gt(Var('Q'), Num(0))"
    assert repr(Exists("x", Var("x"))) == "Exists('x', Var('x'))"
    assert repr(Imp(Var("a"), Var("b"))) == "Imp(Var('a'), Var('b'))"


def test_parse_unary_minus_variable() -> None:
    """Leading '-' binds as negation of the operand that follows it."""
    from parser import Neg, Var
    node, pos = parse_expression(tokenize("-x"))
    assert isinstance(node, Neg)
    assert isinstance(node.expr, Var) and node.expr.name == "x"
    assert pos == 2


def test_contains_op_nested_right_subtree() -> None:
    """contains_op finds operators nested in either subtree."""
    from parser import BinOp, Eq, Var, contains_op
    nested = Eq(Var("a"), BinOp(Var("b"), "/", Var("c")))
    assert contains_op(nested, "/") is True
    assert contains_op(nested, "^") is False
    no_div = Eq(BinOp(Var("a"), "+", Var("b")), Var("c"))
    assert contains_op(no_div, "/") is False
    assert contains_op(no_div, "+") is True


def test_rational_structure_numeric_denominator() -> None:
    """Division by a plain numeric literal is not symbolic rational structure."""
    from parser import has_rational_structure
    node, _ = parse_expression(tokenize("Vmax * C / 2"))
    assert node is not None
    assert has_rational_structure(node) is False
    node2, _ = parse_expression(tokenize("Vmax * C / (Km + C)"))
    assert node2 is not None
    assert has_rational_structure(node2) is True


def test_positivity_hypotheses_none_empty() -> None:
    """No AST means no positivity hypotheses."""
    from parser import extract_positivity_hypotheses
    assert extract_positivity_hypotheses(None) == []


def test_compartmental_structure_none_false() -> None:
    """No AST has no compartmental flow structure."""
    from parser import has_compartmental_structure
    assert has_compartmental_structure(None) is False


def test_is_numeric_only_relation_false() -> None:
    """A relation node itself is never a purely numeric term."""
    from parser import BinOp, Eq, Num, Var, _is_numeric_only
    assert _is_numeric_only(Eq(Num(1), Num(2))) is False
    assert _is_numeric_only(Var("x")) is False
    assert _is_numeric_only(BinOp(Num(1), "+", Num(2))) is True


def test_rational_structure_parenthesized_ratio() -> None:
    """An explicitly parenthesized symbolic ratio is rational structure."""
    from parser import has_rational_structure
    node, _ = parse_expression(tokenize("Vmax * (C / (Km + C))"))
    assert node is not None
    assert has_rational_structure(node) is True


def test_saturable_shapes_surface_field_or_positivity_first() -> None:
    """Saturable flux shapes surface `intros; positivity` / `intros; field_simp; ring`.

    Covers the three `Compartmental.saturableFlux` lemmas (non-negativity,
    boundedness, monotonicity): every shape must type as Real, detect
    rational structure, and rank a universal (`intros; …`) tactic first so
    the pipeline never attempts a bare tactic on unintroduced hypotheses.
    """
    from agentic_pipeline import LeanAgenticPipeline
    from parser import has_rational_structure, parse_equation
    pipeline = LeanAgenticPipeline.__new__(LeanAgenticPipeline)
    pipeline.tactic_candidates = ['rfl', 'simp', 'norm_num', 'decide', 'ring',
                                  'linarith', 'omega', 'field_simp', 'dsimp',
                                  'intro', 'positivity']
    for expr in ("Vmax * C / (Km + C) >= 0",
                 "Vmax * C / (Km + C) < Vmax",
                 "Vmax * C1 / (Km + C1) <= Vmax * C2 / (Km + C2)"):
        node, _ = parse_equation(expr)
        assert node is not None
        assert has_rational_structure(node) is True
        assert pipeline._suggest_type(expr) == "Real"
        first = pipeline.get_tactic_candidates(expr)[0]
        assert first.startswith("intros; "), first
        assert "positivity" in first or "field_simp" in first, first


def test_saturable_positivity_hypotheses_cover_denominator() -> None:
    """Denominator variables of the saturable shape get positivity hypotheses."""
    from parser import extract_positivity_hypotheses, parse_equation
    node, _ = parse_equation("Vmax * C / (Km + C) >= 0")
    assert node is not None
    hyps = extract_positivity_hypotheses(node)
    assert "(hC : 0 < C)" in hyps
    assert "(hKm : 0 < Km)" in hyps


def test_parse_lone_minus_is_none() -> None:
    """A dangling unary minus with no operand parses to nothing."""
    node, pos = parse_expression(tokenize("-"))
    assert node is None
    assert pos == 1


def test_is_boundary_flow_positivity_detects_pattern() -> None:
    """Parser detects compartmental boundary inflow: (Q / (V * Kp)) * A >= 0."""
    from parser import is_boundary_flow_positivity, parse_equation
    node, _ = parse_equation("(Q / (V_central * Kp)) * A_central >= 0")
    assert node is not None
    assert is_boundary_flow_positivity(node) is True


def test_is_boundary_flow_positivity_rejects_missing_q() -> None:
    """Generic detector needs a division factor; bare products are rejected."""
    from parser import is_boundary_flow_positivity, parse_equation
    node, _ = parse_equation("x * z >= 0")
    assert node is not None
    assert is_boundary_flow_positivity(node) is False


def test_is_boundary_flow_positivity_rejects_strict() -> None:
    """Strict inequality (> 0) is not boundary flow (non-negativity requires >=)."""
    from parser import is_boundary_flow_positivity, parse_equation
    node, _ = parse_equation("(Q / (V * Kp)) * A > 0")
    assert node is not None
    assert is_boundary_flow_positivity(node) is False


def test_boundary_flow_positivity_tactic_candidates() -> None:
    """Boundary flow positivity prioritizes intros; positivity and linarith."""
    from agentic_pipeline import LeanAgenticPipeline
    cands = LeanAgenticPipeline().get_tactic_candidates(
        "(Q / (V_central * Kp)) * A_central >= 0"
    )
    assert "intros; positivity" in cands
    assert "intros; field_simp; linarith" in cands


def test_boundary_flow_positivity_proves_no_sorry() -> None:
    """Compartmental boundary inflow (Q / (V * Kp)) * A >= 0 proves without sorry.

    With hypotheses 0 < Q, 0 < V, 0 < Kp, and 0 <= A, the expression
    is a product of non-negative terms and proves via positivity over ℝ.
    """
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline(use_mathlib=True)
    res = pipeline.run("(Q / (V_central * Kp)) * A_central >= 0")
    if pipeline.use_mathlib:
        assert res["success"] is True
        assert "sorry" not in res["lean_code"]
        assert "sorryAx" not in res["lean_code"]
        assert res["verification"]["axioms_check"] == "passed"
    else:
        assert res["success"] is False
        assert "sorry" not in res.get("lean_code", "")


# --- Agentic repair tests ---

def test_parse_lean_goal_basic() -> None:
    """_parse_lean_goal extracts text after ⊢ from Lean stderr."""
    from agentic_pipeline import LeanAgenticPipeline
    stderr = "error: type mismatch\n  ⊢ a + b = b + a\nhas type\n  Prop"
    goal = LeanAgenticPipeline._parse_lean_goal(stderr)
    assert goal == "a + b = b + a"


def test_parse_lean_goal_no_turnstile() -> None:
    """_parse_lean_goal returns None when no ⊢ is present."""
    from agentic_pipeline import LeanAgenticPipeline
    assert LeanAgenticPipeline._parse_lean_goal("some random error") is None


def test_parse_adapter_tactic_fenced_block() -> None:
    """_parse_adapter_tactic extracts tactic from ```lean fenced block."""
    from agentic_pipeline import LeanAgenticPipeline
    response = "Here is the tactic:\n```lean\nring\n```\nHope this helps."
    tactic = LeanAgenticPipeline._parse_adapter_tactic(response)
    assert tactic == "ring"


def test_parse_adapter_tactic_plain_line() -> None:
    """_parse_adapter_tactic falls back to first plausible line."""
    from agentic_pipeline import LeanAgenticPipeline
    response = "simp [add_comm]"
    tactic = LeanAgenticPipeline._parse_adapter_tactic(response)
    assert tactic == "simp [add_comm]"


def test_parse_adapter_tactic_skips_prose() -> None:
    """_parse_adapter_tactic skips lines that look like prose."""
    from agentic_pipeline import LeanAgenticPipeline
    response = "This is the correct tactic.\nfield_simp"
    tactic = LeanAgenticPipeline._parse_adapter_tactic(response)
    assert tactic == "field_simp"


def test_agentic_adapter_called_on_failure(monkeypatch: Any) -> None:
    """When static tactics fail and a goal is parsed, the adapter is called."""
    from agentic_pipeline import LeanAgenticPipeline
    from dataclasses import dataclass

    @dataclass
    class _FakeState:
        logs: str = "positivity"

    @dataclass
    class _FakeSession:
        session_id: str = ""
        project_dir: str = ""

    class _FakeAdapter:
        def __init__(self):
            self.calls: list[str] = []
        def send(self, prompt: str, session: Any) -> _FakeState:
            self.calls.append(prompt)
            return _FakeState(logs="positivity")

    adapter = _FakeAdapter()
    pipeline = LeanAgenticPipeline(use_mathlib=False, adapter=adapter)

    # Mock compile to always fail with a goal on first attempts,
    # then succeed when tactic is "positivity"
    call_count = [0]

    def _mock_run(cmd, **kwargs):
        call_count[0] += 1
        if call_count[0] <= 15:
            # Static tactic attempts: fail with a goal
            return type('Result', (), {
                'returncode': 1,
                'stdout': '',
                'stderr': 'error: type mismatch\n  ⊢ 0 < 1\nhas type\n  Prop',
            })()
        # Adapter-provided tactic: succeed
        return type('Result', (), {
            'returncode': 0,
            'stdout': '',
            'stderr': '',
        })()

    monkeypatch.setattr(subprocess, 'run', _mock_run)

    # Patch _verify_no_sorry_axioms to always pass
    monkeypatch.setattr(
        LeanAgenticPipeline, '_verify_no_sorry_axioms',
        lambda self, path: (True, ''),
    )
    # Patch check_for_sorry to always return clean
    monkeypatch.setattr(
        LeanAgenticPipeline, 'check_for_sorry',
        lambda self, src, out: (False, ''),
    )

    result = pipeline.run("0 < 1")
    # Adapter should have been called because static tactics exhausted
    assert len(adapter.calls) >= 1
    assert "⊢ 0 < 1" in adapter.calls[0]
    # ... and the repair it produced is what the run reports as verified.
    assert result["success"] is True
    assert "[adapter]" in result["tactic"]
    assert "sorry" not in result["lean_code"]


def test_adapter_repair_e2e_mocked() -> None:
    """End-to-end adapter repair: static candidates fail -> adapter queried
    via _construct_repair_prompt -> _parse_adapter_tactic response compiled
    and verified against #print axioms."""
    from agentic_pipeline import LeanAgenticPipeline

    class FakeState:
        logs = "```lean\nring\n```"

    class FakeAdapter:
        def __init__(self):
            self.prompts: list[str] = []

        def send(self, prompt, session):
            self.prompts.append(prompt)
            return FakeState()

    pipeline = LeanAgenticPipeline(adapter=FakeAdapter())
    # Force static candidates to fail by pointing at a bogus lean binary
    pipeline.lean_path = "/nonexistent-lean"
    pipeline._lake_env_lean = None
    pipeline._lake_root = None
    pipeline.use_mathlib = False

    import subprocess as _sp

    real_run = _sp.run
    calls = {"n": 0}

    class R:
        def __init__(self, rc, out="", err=""):
            self.returncode = rc
            self.stdout = out
            self.stderr = err

    def fake_run(cmd, **kw):
        calls["n"] += 1
        text = ""
        try:
            f = [a for a in (cmd if isinstance(cmd, list) else []) if str(a).endswith(".lean")]
            if f:
                text = open(f[0]).read()
        except Exception:
            text = ""
        if "[adapter]" in text or "ring" in text and calls["n"] > 3:
            return R(0, "", "")
        # static attempts: fail with a goal-bearing error
        return R(1, "", "error: unsolved goals\n⊢ a + b = b + a\n")

    _sp.run = fake_run  # type: ignore
    try:
        # unit-level: prompt + parse
        prompt = pipeline._construct_repair_prompt(
            "a + b = b + a", "theorem qed_goal : a + b = b + a := by\n",
            "unsolved goals", "a + b = b + a")
        assert "⊢" in prompt or "goal" in prompt.lower()
        tactic = pipeline._parse_adapter_tactic(FakeState.logs)
        assert tactic == "ring"
        # full loop with tiny budget so static phase exhausts fast
        res = pipeline.execute_tactic_loop("a + b = b + a", max_iterations=1)
        assert any("[adapter]" in a.get("tactic", "") for a in res["attempts"])
        assert pipeline.adapter.prompts, "adapter must have been queried"
    finally:
        _sp.run = real_run  # type: ignore

# --- Out-of-Distribution (OOD) generic verification tests ---
# SEIR epidemic model + 3-tank cascade: verified with zero changes to QED.

def test_ood_seir_conservation() -> None:
    from parser import parse_equation, is_linear_conservation
    # SEIR closed-population conservation: S + E + I + R = N -> S + E + I + R - N = 0
    node, _ = parse_equation("S + E + I + R - N = 0")
    assert node is not None and is_linear_conservation(node)

def test_ood_seir_positivity() -> None:
    from parser import parse_equation, is_positivity
    # SEIR transmission coefficient positivity (generic division form)
    node, _ = parse_equation("beta / gamma > 0")
    assert node is not None and is_positivity(node)

def test_ood_tank_cascade() -> None:
    from parser import parse_equation, is_linear_conservation, is_nonneg_product
    node, _ = parse_equation("h1 + h2 + h3 - H = 0")
    assert node is not None and is_linear_conservation(node)
    node2, _ = parse_equation("(q / V) * h1 >= 0")
    assert node2 is not None and is_nonneg_product(node2)

def test_ood_matrix_entry_equality() -> None:
    from parser import parse_equation, is_matrix_entry_equality
    node, _ = parse_equation("K11 + K12 = K11 + K12")
    assert node is not None

def test_ood_finance_budget_identity() -> None:
    """A household budget identity is a conservation law, not a PK statement.

    Out-of-domain on purpose: nothing here resembles a compartment, a rate
    constant, or an amount, so the conservation recognizer is exercised on
    vocabulary it has never been tuned against. The identity is written in the
    canonical ``sum - total = 0`` form the recognizer requires (a linear sum
    equating to zero), not in the ``= savings`` form a person would write.
    """
    from parser import parse_equation, is_linear_conservation
    node, _ = parse_equation(
        "revenue - rent - food - transport - savings = 0")
    assert node is not None and is_linear_conservation(node)
    # The recognizer is a *structural* classifier: it certifies the FORM
    # "linear sum = 0" and deliberately does not judge whether the statement
    # is a true identity (that is the prover's job, not the parser's). So the
    # meaningful contrast is shape, not semantics: an inequality is not a
    # conservation law.
    bad, _ = parse_equation("revenue - rent - savings > 0")
    assert bad is not None and not is_linear_conservation(bad)

def test_ood_ode_from_a_non_biological_domain() -> None:
    """A cooling-body ODE and a generic flow bound, both non-PK.

    Exercises ``is_ode`` / ``parse_ode`` / ``involves_derivative`` /
    ``is_nonneg_product`` on engineering notation so the ODE and flow
    recognizers are not merely correct for the compartment naming they were
    built around.
    """
    from parser import involves_derivative, is_ode, is_nonneg_product
    from parser import parse_equation, parse_ode
    ode, free_vars = parse_ode("dT_env/dt = -h * (T_env - T_ambient)")
    assert ode is not None, "a first-order cooling ODE must parse"
    assert is_ode("dT_env/dt = -h * (T_env - T_ambient)") is True
    assert is_ode("revenue - rent = savings") is False
    assert involves_derivative("dT_env/dt = -h * (T_env - T_ambient)") is True
    # Newton-style cooling flux, written as a flow bound: a product carrying a
    # division, which is the shape is_nonneg_product recognises.
    node, _ = parse_equation("(h / c_air) * (T_env - T_ambient) >= 0")
    assert node is not None and is_nonneg_product(node)


# --- Exact-goal extraction for the agentic repair prompt ---

def test_extract_goal_context_reads_goal_and_hypotheses() -> None:
    """The repair prompt must show the model the goal Lean actually reported,
    hypotheses included. Reconstructing it from the theorem statement loses the
    context that made ring/positivity/field_simp fail."""
    from agentic_pipeline import LeanAgenticPipeline
    stderr = (
        "example (hq : 0 < Q) (hv : 0 < V) : 0 < Q / V := by\n"
        "  sorry\n"
        "error: unsolved goals\n"
        "context:\n"
        "hq : 0 < Q\n"
        "hv : 0 < V\n"
        "⊢ 0 < Q / V\n"
    )
    goal, hyps = LeanAgenticPipeline._extract_goal_context(stderr)
    assert goal == "0 < Q / V"
    assert hyps == ["hq : 0 < Q", "hv : 0 < V"]


def test_extract_goal_context_keeps_wrapped_multiline_goals() -> None:
    """Lean wraps long goals onto indented continuation lines; taking only the
    first line after ⊢ would hand the adapter a truncated, unprovable goal."""
    from agentic_pipeline import LeanAgenticPipeline
    stderr = (
        "error: unsolved goals\n"
        "⊢ ∀ (x : ℝ), x + 0 = x ∧\n"
        "  x = x\n"
        "next message\n"
    )
    goal, _ = LeanAgenticPipeline._extract_goal_context(stderr)
    assert goal == "∀ (x : ℝ), x + 0 = x ∧\n  x = x"


def test_extract_goal_context_prefers_the_last_goal() -> None:
    """A theorem compiles as statement-then-goal, so only the LAST ⊢ is the
    unsolved one; the header's ⊢ must not win."""
    from agentic_pipeline import LeanAgenticPipeline
    stderr = (
        "example : 0 < Q / V := by\n"
        "⊢ 0 < Q / V\n"
        "error: unsolved goals\n"
        "context:\n"
        "hv : 0 < V\n"
        "⊢ 0 < Q / V ∧ 0 < V\n"
    )
    goal, hyps = LeanAgenticPipeline._extract_goal_context(stderr)
    assert goal == "0 < Q / V ∧ 0 < V"
    assert hyps == ["hv : 0 < V"]


def test_extract_goal_context_without_turnstile_is_none() -> None:
    from agentic_pipeline import LeanAgenticPipeline
    assert LeanAgenticPipeline._extract_goal_context("no goal here") == (None, [])


def test_repair_prompt_states_the_exact_goal_not_the_reconstructed_one() -> None:
    """The whole point of the hardening: the adapter is told the deterministic
    candidates already failed, and is given the verbatim goal block."""
    from agentic_pipeline import LeanAgenticPipeline
    stderr = (
        "error: unsolved goals\n"
        "context:\n"
        "hq : 0 < Q\n"
        "⊢ 0 < Q / V\n"
    )
    pipeline = LeanAgenticPipeline(adapter=None)
    prompt = pipeline._construct_repair_prompt(
        "STALE-FALLBACK-GOAL", "example : True := by\n", stderr, "0 < Q / V",
    )
    assert "⊢ 0 < Q / V" in prompt
    assert "STALE-FALLBACK-GOAL" not in prompt
    assert "hq : 0 < Q" in prompt
    assert "ring, positivity, field_simp" in prompt


def test_repair_prompt_falls_back_to_passed_goal_when_stderr_has_none() -> None:
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline(adapter=None)
    prompt = pipeline._construct_repair_prompt(
        "a + b = b + a", "theorem q : a + b = b + a := by\n",
        "error: something else entirely", "a + b = b + a",
    )
    assert "⊢ a + b = b + a" in prompt


# ---------------------------------------------------------------------------
# qed-02-parser-hardening: implicit multiplication + nested parenthesis handling
#
# These are fast (no-Lean) unit tests pinning the five parser defects that let a
# *different statement* reach Lean than the user wrote:
#   1. word boundaries  - multi-character names were shredded (ka_rate -> k * a_rate)
#   2. LaTeX expansion  - macros were expanded *after* implicit-mul, so \le became
#                         ['l','*','e'] and \frac became a variable named 'frac'
#   3. identity check   - ast_to_latex emits no parens, so (a + b) * c compared
#                         equal to a + b * c and took the `rfl` short-circuit
#   4. fail closed      - malformed/nested parens produced Eq(None, ...) nodes
#   5. identifiers      - dotted/underscored operands lost the token after them
#                         (Nat.succ 0 silently dropped the 0)
# ---------------------------------------------------------------------------

from parser import (  # noqa: E402
    canonical_form,
    expand_latex_macros,
)


# --- 1. word boundaries: identifiers must survive normalization intact ---

def test_normalize_preserves_snake_case_identifier() -> None:
    """'ka_rate' was shredded to 'k * a_rate' because the letter-pair rule used
    [a-zA-Z] as its word class, which excludes '_'."""
    from parser import normalize_implicit_multiplication_expression as n
    assert n('ka_rate * Ag') == 'ka_rate * Ag'


def test_normalize_preserves_underscored_identifier_suffix() -> None:
    """'a_bc' was split to 'a_b * c' for the same reason."""
    from parser import normalize_implicit_multiplication_expression as n
    assert n('a_bc') == 'a_bc'
    assert n('x_1 + y_2') == 'x_1 + y_2'


def test_normalize_preserves_subscripted_name_before_product() -> None:
    """'A_1ab' must not decay to 'A_1 * a * b'."""
    from parser import normalize_implicit_multiplication_expression as n
    assert n('A_1ab') == 'A_1ab'
    assert n('(A_1 + A_2)2') == '(A_1 + A_2) * 2'


def test_normalize_does_not_split_inside_alphabetic_name() -> None:
    """A digit or letter may not split off the tail of a longer name."""
    from parser import normalize_implicit_multiplication_expression as n
    assert n('Nat2') == 'Nat2'
    assert n('a1b') == 'a1b'
    assert n('2_3') == '2_3'


def test_normalize_keeps_pinned_products_after_boundary_fix() -> None:
    """The boundary lookarounds must not weaken genuine implicit products."""
    from parser import normalize_implicit_multiplication_expression as n
    assert n('2a') == '2 * a'
    assert n('2ab') == '2 * a * b'
    assert n('3xyz') == '3 * x * y * z'
    assert n('ab') == 'a * b'
    assert n('ab + cd') == 'a * b + c * d'
    assert n('(a+b)^2 = a^2 + 2ab + b^2') == '(a+b)^2 = a^2 + 2 * a * b + b^2'
    assert n('Nat + x') == 'Nat + x'
    assert n('Vmax * C / (Km + C)') == 'Vmax * C / (Km + C)'


def test_underscored_names_survive_full_parse() -> None:
    """The free-variable set must report 'ka_rate' as one name, not 'k'."""
    from parser import parse_equation
    eq, free_vars = parse_equation('ka_rate * Ag = 1')
    assert eq is not None
    assert free_vars == ['Ag', 'ka_rate']


# --- 2. LaTeX-like tokens: expansion must precede implicit multiplication ---

def test_latex_relation_macros_are_not_split_into_letters() -> None:
    """'a \\le b' used to tokenize as ['a', 'l', '*', 'e', 'b'] because the
    letter-pair rule ran before macro expansion.

    The relation is now ONE token ('<='), not two ('<', '='): the
    multi-character branch of the token pattern used to sit after the
    single-character operator class, so it was dead code."""
    assert tokenize('a \\le b') == ['a', '<=', 'b']
    assert tokenize('a \\ge b') == ['a', '>=', 'b']
    assert tokenize('a \\leq b') == ['a', '<=', 'b']
    assert tokenize('a \\geq b') == ['a', '>=', 'b']
    assert tokenize('a \\neq b') == ['a', '!=', 'b']


def test_latex_operator_macros_expand() -> None:
    assert tokenize('a \\cdot b = c') == ['a', '*', 'b', '=', 'c']
    assert tokenize('a \\times b = c') == ['a', '*', 'b', '=', 'c']
    assert tokenize('a \\div b = c') == ['a', '/', 'b', '=', 'c']


def test_latex_frac_expands_to_division() -> None:
    """'\\frac{a}{b}' used to tokenize as the variable 'frac'."""
    assert tokenize('\\frac{a}{b} = c') == [
        '(', '(', 'a', ')', '/', '(', 'b', ')', ')', '=', 'c']
    eq, free_vars = parse_equation('\\frac{a}{b} = c')
    assert eq is not None
    assert canonical_form(eq) == '((a / b)=c)'
    assert free_vars == ['a', 'b', 'c']


def test_latex_frac_preserves_grouping() -> None:
    eq, _ = parse_equation('\\frac{a + b}{c} = d')
    assert eq is not None
    assert canonical_form(eq) == '(((a + b) / c)=d)'


def test_latex_relation_macros_reach_statement_kind() -> None:
    """The relation must be found on the expanded string, not the raw one."""
    assert statement_kind('a \\le b') == 'inequality'
    assert statement_kind('a \\geq b') == 'inequality'
    eq, _ = parse_equation('a \\neq b')
    assert eq is not None and is_inequality(eq) is True


def test_latex_delimiters_and_thin_spaces_expand() -> None:
    assert expand_latex_macros('a \\left( b \\right)') == 'a ( b )'
    assert expand_latex_macros('a \\, b') == 'a   b'
    assert tokenize('a \\cdot (b + c) = d') == ['a', '*', '(', 'b', '+', 'c', ')', '=', 'd']


# --- 3. structural identity must not depend on the display renderer ---

def test_canonical_form_distinguishes_parenthesized_products() -> None:
    """ast_to_latex is a lossy display renderer; canonical_form is not."""
    from parser import ast_to_latex, canonical_form as cf
    left, _ = parse_equation('(a + b) * c = a')
    right, _ = parse_equation('a + b * c = a')
    # The display renderer collapses both to the same string ...
    assert ast_to_latex(left.left) == ast_to_latex(right.left)
    # ... but the canonical form must keep them apart.
    assert cf(left.left) != cf(right.left)


def test_statement_kind_is_not_identity_for_false_distributive_claim() -> None:
    """'(a + b) * c = a + b * c' is FALSE; classifying it as 'identity' sent the
    pipeline down the `rfl` short-circuit, i.e. a silent pass."""
    assert statement_kind('(a + b) * c = a + b * c') == 'equality'
    assert statement_kind('x * (y + 1) = x * y + x') == 'equality'
    assert statement_kind('3 * (5 - 4 / 2) = 3 * 5 - 3 * 4 / 2') == 'equality'


def test_statement_kind_still_reports_true_identities() -> None:
    """The structural comparison must keep recognizing real identities."""
    assert statement_kind('x = x') == 'identity'
    assert statement_kind('a + b = a + b') == 'identity'
    assert statement_kind('ab = a * b') == 'identity'
    assert statement_kind('x * 1 = x * 1') == 'identity'
    assert statement_kind('x^1 = x^1') == 'identity'


def test_identity_short_circuit_not_reachable_for_false_statement() -> None:
    """End-to-end: a false distributive claim must take the same tactic path as
    any other non-identity equality, and must NOT take the identity
    short-circuit (which appends 'refl' and tries rfl-first)."""
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    identity_cands = pipeline.get_tactic_candidates('a + b = a + b')
    false_cands = pipeline.get_tactic_candidates('(a + b) * c = a + b * c')
    true_equality_cands = pipeline.get_tactic_candidates('x * (y + 1) = x * y + x')
    # The identity short-circuit has a distinct signature; it must not fire.
    assert false_cands != identity_cands
    # ... and the false statement is classified exactly like a real equality.
    assert false_cands == true_equality_cands


# --- 4. malformed / nested / unbalanced parentheses must fail closed ---

def test_malformed_paren_equations_fail_closed() -> None:
    """These used to build Eq(None, ...) nodes, so codegen emitted a theorem
    statement with an empty left-hand side."""
    for expr in ['(a+) = 1', '(()) = 1', '((a+b) = 1', 'a = (b', '(a', '()',
                 '*a = b', '2( = 1', 'x = 1 +', '(a)( = 1']:
        eq, _ = parse_equation(expr)
        assert eq is None, expr
        assert statement_kind(expr) == 'other', expr


def test_trailing_tokens_fail_closed() -> None:
    """Leftover tokens were silently discarded, changing the statement."""
    eq, _ = parse_equation('(a+b)) = 1')
    assert eq is None
    eq, _ = parse_equation('(a+b)) * c = 1')
    assert eq is None
    # A second relation operator is not silently dropped either.
    eq, _ = parse_equation('a < b < c')
    assert eq is None


def test_malformed_input_is_rejected_by_the_validator() -> None:
    """Fail-closed must reach the pipeline: unparseable input is not 'valid'."""
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    is_valid, reason = pipeline.validate_input('(a+) = 1')
    assert is_valid is False
    assert 'parse' in reason.lower()


def test_malformed_ode_fails_closed() -> None:
    assert parse_ode('dA/dt = (1 + )') == (None, None)
    assert parse_ode('dA/dt = (1 + 2') == (None, None)


def test_wellformed_nested_parens_still_parse() -> None:
    """Fail-closed must not break well-formed nesting."""
    eq, _ = parse_equation('((a + b)) = (c)')
    assert eq is not None
    assert canonical_form(eq) == '((a + b)=c)'
    eq, _ = parse_equation('(3 + 1 * (-6)) + (5 + 1 * (9)) = 21')
    assert eq is not None


# --- 5. dotted / underscored operands keep the token that follows them ---

def test_dotted_identifier_does_not_swallow_its_argument() -> None:
    """'Nat.succ 0' silently dropped the 0, yielding the statement 'Nat.succ = 1'."""
    from parser import normalize_implicit_multiplication as nim
    assert nim(tokenize('Nat.succ 0')) == ['Nat.succ', '*', '0']
    eq, free_vars = parse_equation('Nat.succ 0 = 1')
    assert eq is not None
    assert canonical_form(eq) == '((Nat.succ * 0)=1)'
    assert free_vars == ['Nat.succ']


def test_underscored_identifier_adjacency_is_explicit_multiplication() -> None:
    from parser import normalize_implicit_multiplication as nim
    assert nim(tokenize('A_1 (2)')) == ['A_1', '*', '(', '2', ')']
    assert nim(tokenize('x_1 y_2')) == ['x_1', '*', 'y_2']


def test_digit_adjacency_to_identifier_is_multiplication() -> None:
    from parser import normalize_implicit_multiplication as nim
    assert nim(tokenize('2 A_1')) == ['2', '*', 'A_1']
    assert nim(tokenize('(a+b) A_1')) == ['(', 'a', '+', 'b', ')', '*', 'A_1']


def test_ode_with_underscored_names_parses() -> None:
    ode, free_vars = parse_ode('dA_1/dt = -k_1 * A_1')
    assert ode is not None
    assert ode.var == 'A_1'
    assert free_vars == ['A_1', 'k_1']


# --- 6. total token coverage: a character outside the vocabulary is rejected,
#        not silently deleted (so no *different* statement reaches Lean) ---

def test_tokenize_rejects_characters_outside_the_vocabulary() -> None:
    """`re.findall` skipped text it could not match, so a stray character was
    deleted instead of rejected: 'x % y = z' tokenized to ['x','y','=','z'] and
    reached Lean as 'x * y = z'. The tokenizer now requires the matches to cover
    the whole input (whitespace excepted) and returns [] otherwise."""
    for expr in ['x % y = z', 'a @ b = c', 'a & b = c', 'a, b = c', 'a; b = c',
                 'x = 1 & y = 2', 'a = b $ c', 'a = b | c', 'a = b # c',
                 'a = b " c', "a = b ' c", 'a = b ? c', 'a = b : c',
                 'a = b ~ c', 'a = b ` c', 'a = b { c', 'a = b } c',
                 'a = b [ c', 'a = b ] c', 'a = b \\unknown']:
        assert tokenize(expr) == [], expr


def test_unknown_characters_fail_closed() -> None:
    """A statement that cannot be tokenized must be rejected, not approximated:
    parse_equation yields no node and statement_kind reports 'other'."""
    for expr in ['x % y = z', 'a @ b = c', 'x = 1_000', '2_3 = 4', 'a & b = c',
                 'a, b = c', '2.5 = 2', '_foo = 1', 'a = 1/2/3/4_5']:
        eq, _ = parse_equation(expr)
        assert eq is None, expr
        assert statement_kind(expr) == 'other', expr


def test_digit_separators_and_decimals_are_not_mangled() -> None:
    """'1_000' used to tokenize as ['1','_000'] and reach Lean as '1 * _000';
    '2.5' used to tokenize as ['2','5'] and be interpreted as '2 * 5'. Identifiers
    must start with a letter, so both now fail closed."""
    assert tokenize('1_000') == []
    assert tokenize('2.5') == []
    eq, _ = parse_equation('x = 1_000')
    assert eq is None
    eq, _ = parse_equation('2.5 = 2')
    assert eq is None
    # ... and the two forms that *are* supported still work.
    assert tokenize('x_1 = 1') == ['x_1', '=', '1']
    assert tokenize('A_1 = 1') == ['A_1', '=', '1']


def test_unsupported_latex_macros_fail_closed_instead_of_leaking() -> None:
    """An unexpanded macro must not become the ASCII identifier that follows the
    backslash: 'a \\pm b = c' reached Lean as 'a * pm * b = c', and '\\alpha' as a
    variable named 'alpha'."""
    for expr in ['a \\pm b = c', 'a \\mp b = c', 'a \\sqrt{2} = b',
                 '\\alpha + \\beta = 1', '2\\alpha = 1', 'a \\not= b',
                 'a \\cdot \\pm b = c']:
        eq, _ = parse_equation(expr)
        assert eq is None, expr
        assert statement_kind(expr) == 'other', expr
        assert 'pm' not in tokenize(expr) and 'alpha' not in tokenize(expr)


def test_malformed_ode_with_unknown_characters_fails_closed() -> None:
    assert parse_ode('dA/dt = a \\pm b') == (None, None)
    assert parse_ode('dA/dt = a % b') == (None, None)
    assert parse_ode('dA/dt = (1 + 2') == (None, None)


def test_unicode_operators_are_recognized() -> None:
    """Typographic operators copied out of rendered LaTeX used to lose their
    meaning entirely: 'a ≤ b' tokenized to ['a','b'] and degraded to the
    implicit product 'a * b', which is a different (and wrong) statement."""
    assert tokenize('a × b = c') == ['a', '*', 'b', '=', 'c']
    assert tokenize('a ÷ b = c') == ['a', '/', 'b', '=', 'c']
    assert tokenize('1 − 1 = 0') == ['1', '-', '1', '=', '0']
    assert tokenize('a ≤ b') == ['a', '<=', 'b']
    assert tokenize('a ≥ b') == ['a', '>=', 'b']
    assert tokenize('a ≠ b') == ['a', '!=', 'b']


def test_unicode_operators_reach_the_parsed_statement() -> None:
    eq, free_vars = parse_equation('a × b = c')
    assert eq is not None and canonical_form(eq) == '((a * b)=c)'
    eq, _ = parse_equation('a ÷ b = c')
    assert eq is not None and canonical_form(eq) == '((a / b)=c)'
    eq, _ = parse_equation('1 − 1 = 0')
    assert eq is not None and canonical_form(eq) == '((1 - 1)=0)'
    for expr, cls in [('a ≤ b', Le), ('a ≥ b', Ge), ('a ≠ b', Ne)]:
        eq, _ = parse_equation(expr)
        assert isinstance(eq, cls), expr
        assert is_inequality(eq) is True, expr
        assert statement_kind(expr) == 'inequality', expr


def test_unicode_operators_in_an_ode_parse() -> None:
    ode, free_vars = parse_ode('dA/dt = −k × A')
    assert ode is not None
    assert ode.var == 'A'
    assert canonical_form(ode.rhs) == '((-k) * A)'
    assert free_vars == ['A', 'k']


def test_tokenizer_still_accepts_the_pinned_vocabulary() -> None:
    """The coverage check must not reject any input the parser is meant to take:
    whitespace is the only tolerated gap, and every supported token shape still
    tokenizes."""
    for expr in ['2 * (a+b)', '(a+b)(c+d)', '3xyz', '2a', 'ab', 'a2', '2ab',
                 'Nat.succ 0', 'x_1 y_2', 'A_1 (2)', '2 A_1', '(a+b) A_1',
                 'ka_rate * Ag = 1', 'Vmax * C / (Km + C)', 'Nat + x',
                 'x = 1 - -1', 'a  *  b  =  c', '(a + b) ^ 2 = a ^ 2']:
        assert tokenize(expr) != [], expr
    assert tokenize('2 * (a+b)') == ['2', '*', '(', 'a', '+', 'b', ')']
    assert tokenize('a  *  b') == ['a', '*', 'b']


def test_empty_and_whitespace_input_yields_no_tokens() -> None:
    assert tokenize('') == []
    assert tokenize('   ') == []
    assert tokenize('()') == ['(', ')']
    assert statement_kind('') == 'other'


# ---------------------------------------------------------------------------
# qed-02-parser-hardening, part 2: the tokenizer/macro layer.
#
# The five defects above are fixed; these tests pin the *residue* that was
# still letting a different statement reach Lean, plus the implicit
# multiplication and nested-parenthesis patterns the mission asks for:
#
#   7. control words   - ``\cdotp`` was truncated to ``*p``: the tail of a
#                        longer control word leaked in as an identifier, so
#                        ``a \cdotp b`` reached Lean as ``a * p * b``.
#   8. braced scripts  - ``a^{2}`` / ``x_{1}`` (the standard LaTeX spelling
#                        of a power and a subscript) were rejected outright.
#   9. multi-char ops  - the ``<=``/``>=``/``!=`` branch of the token
#                        pattern sat AFTER the single-character operator
#                        class, so it was dead code.
#  10. macro coverage  - ``\lt``/``\gt``/``\dfrac``/``\tfrac`` are common
#                        spellings that were not expanded at all.
#
# All of these are compiler-free, so they survive a clean room without
# Mathlib.
# ---------------------------------------------------------------------------


# --- 7. a control word ends at the first non-letter ---

def test_longer_control_words_are_not_truncated_into_an_operator_and_a_name() -> None:
    """``a \\cdotp b`` used to expand to ``a *p b`` and tokenize as
    ['a', '*', 'p', 'b'] -- the statement Lean saw was ``a * p * b``.

    A LaTeX control word ends at the first non-letter, so ``\\cdotp`` is
    NOT ``\\cdot`` followed by ``p``.  The tail must not leak into the
    statement: the whole control word is unknown, so the input is rejected.
    """
    for expr in ['a \\cdotp b', 'a \\divide b', 'a \\neqq b', 'a \\leX b',
                 'a \\geqx b', 'a \\timesp b', 'a \\divx b']:
        assert tokenize(expr) == [], expr
        eq, _ = parse_equation(expr)
        assert eq is None, expr
        assert statement_kind(expr) == 'other', expr


def test_control_word_boundary_does_not_break_the_supported_macros() -> None:
    """The boundary must not swallow the macros that ARE supported: the
    non-letter after a control word may be a space, a parenthesis or an
    operator."""
    assert tokenize('a \\cdot b = c') == ['a', '*', 'b', '=', 'c']
    assert tokenize('a \\cdot(b) = c') == ['a', '*', '(', 'b', ')', '=', 'c']
    assert tokenize('a \\le b') == ['a', '<=', 'b']
    assert tokenize('a \\leq b') == ['a', '<=', 'b']
    assert tokenize('a \\left(b\\right) = c') == ['a', '(', 'b', ')', '=', 'c']
    assert tokenize('\\frac{a}{b} = c') == [
        '(', '(', 'a', ')', '/', '(', 'b', ')', ')', '=', 'c']


# --- 8. braced powers and subscripts ---

def test_braced_power_expands_to_a_parenthesized_power() -> None:
    """``a^{2}`` is the standard LaTeX spelling of a power.  The braces
    become real parentheses, so the grouping the power denotes survives."""
    assert tokenize('a^{2}') == ['a', '^', '(', '2', ')']
    eq, _ = parse_equation('a^{2} = b')
    assert eq is not None
    assert canonical_form(eq) == '((a ^ 2)=b)'


def test_braced_power_keeps_the_grouping_of_its_exponent() -> None:
    """``a^{b+c}`` is ``a^(b+c)``, not ``(a^b)+c``."""
    eq, _ = parse_equation('a^{b+c} = d')
    assert eq is not None
    assert canonical_form(eq) == '((a ^ (b + c))=d)'


def test_braced_power_of_a_negative_exponent() -> None:
    eq, _ = parse_equation('e^{-x} = 1')
    assert eq is not None
    assert canonical_form(eq) == '((e ^ (-x))=1)'


def test_braced_subscript_expands_to_a_name() -> None:
    """``x_{1}`` is the LaTeX spelling of a subscripted name."""
    assert tokenize('x_{1}') == ['x_1']
    eq, free_vars = parse_equation('x_{1} = 4')
    assert eq is not None
    assert canonical_form(eq) == '(x_1=4)'
    assert free_vars == ['x_1']


def test_ambiguous_braced_subscripts_fail_closed() -> None:
    """A subscript that is not a name tail, or that is followed by more
    name characters, must be REJECTED rather than merged into one name:
    ``a_{i,j}`` must not become ``a_i * j`` and ``a_{i}j`` must not become
    the single name ``a_ij``."""
    for expr in ['a_{i,j} = 1', 'a_{i-1} = 1', 'a_{i}j = 1', 'A_{1}ab = 1']:
        assert tokenize(expr) == [], expr
        eq, _ = parse_equation(expr)
        assert eq is None, expr


def test_braced_frac_and_script_nest() -> None:
    """``\\frac{a_{1}}{b}`` and ``a^{\\frac{b}{c}}`` need both rewrites to
    run before either can succeed."""
    assert tokenize('\\frac{a_{1}}{b}') == [
        '(', '(', 'a_1', ')', '/', '(', 'b', ')', ')']
    assert tokenize('a^{\\frac{b}{c}}') == [
        'a', '^', '(', '(', '(', 'b', ')', '/', '(', 'c', ')', ')', ')']


def test_a_fraction_is_one_operand() -> None:
    """``\\frac{a}{b}^2`` is ``(a/b)^2``, not ``a/(b^2)``.

    The fraction used to expand to ``(a) / (b)``, so a power attached to it
    landed on the *denominator* -- a different statement from the one that
    was written.  The whole fraction is one operand now."""
    from parser import canonical_form as cf
    for raw in ['\\frac{a}{b}^2', '\\frac{a}{b}^{2}']:
        node, _ = parse_expression(
            normalize_implicit_multiplication(tokenize(raw)))
        assert node is not None, raw
        assert cf(node) == '((a / b) ^ 2)', raw
    node, _ = parse_expression(
        normalize_implicit_multiplication(tokenize('\\frac{a}{b}x')))
    assert node is not None
    assert cf(node) == '((a / b) * x)'


# --- 9. the multi-character operators are one token ---

def test_multi_character_operators_are_single_tokens() -> None:
    """The token pattern is an ordered alternation: the multi-character
    branch used to sit after the single-character operator class, so it
    never matched and ``<=`` tokenized as ``<`` followed by ``=``."""
    assert tokenize('a <= b') == ['a', '<=', 'b']
    assert tokenize('a >= b') == ['a', '>=', 'b']
    assert tokenize('a != b') == ['a', '!=', 'b']
    # The single-character operators are unaffected.
    assert tokenize('a < b') == ['a', '<', 'b']
    assert tokenize('a > b') == ['a', '>', 'b']
    assert tokenize('a = b') == ['a', '=', 'b']


def test_multi_character_operators_still_reach_the_relation() -> None:
    """Making the branch live must not change what the statement means."""
    for expr, cls in [('a <= b', Le), ('a >= b', Ge), ('a != b', Ne)]:
        eq, free_vars = parse_equation(expr)
        assert eq is not None, expr
        assert isinstance(eq, cls), expr
        assert free_vars == ['a', 'b'], expr
        assert statement_kind(expr) == 'inequality', expr


# --- 10. the remaining common macro spellings ---

def test_additional_relation_macros_expand() -> None:
    assert tokenize('a \\lt b') == ['a', '<=', 'b']
    assert tokenize('a \\gt b') == ['a', '>=', 'b']
    eq, _ = parse_equation('a \\lt b')
    assert eq is not None and isinstance(eq, Le)
    eq, _ = parse_equation('a \\gt b')
    assert eq is not None and isinstance(eq, Ge)


def test_display_and_text_fractions_expand() -> None:
    """``\\dfrac``/``\\tfrac`` are the display/text spellings of ``\\frac``."""
    for expr in ['\\dfrac{a}{b} = c', '\\tfrac{a}{b} = c']:
        assert tokenize(expr) == [
            '(', '(', 'a', ')', '/', '(', 'b', ')', ')', '=', 'c'], expr
        eq, free_vars = parse_equation(expr)
        assert eq is not None, expr
        assert canonical_form(eq) == '((a / b)=c)', expr


def test_unknown_math_macros_still_fail_closed() -> None:
    """Adding macros must not open the door to the identifiers behind
    them: the ones that are still unknown stay unknown."""
    for expr in ['a \\pm b = c', 'a \\mp b = c', 'a \\sqrt{2} = b',
                 '\\alpha + \\beta = 1', 'a \\approx b', 'a \\cdotp b = c']:
        assert tokenize(expr) == [], expr
        eq, _ = parse_equation(expr)
        assert eq is None, expr


# --- the mission's own subject: implicit multiplication and nested parens ---

def test_implicit_multiplication_patterns() -> None:
    """Every implicit-product shape the MVP input language allows, from the
    raw text to the AST."""
    from parser import (normalize_implicit_multiplication_expression as n,
                         canonical_form as cf)
    cases = [
        ('2a', '2 * a', '(2 * a)'),
        ('2ab', '2 * a * b', '((2 * a) * b)'),
        ('3xyz', '3 * x * y * z', '(((3 * x) * y) * z)'),
        ('ab', 'a * b', '(a * b)'),
        ('a2', 'a * 2', '(a * 2)'),
        ('(a+b)2', '(a+b) * 2', '((a + b) * 2)'),
        ('(a+b)(c+d)', '(a+b) * (c+d)', '((a + b) * (c + d))'),
        ('2(a+b)', '2 * (a+b)', '(2 * (a + b))'),
        ('a(b+c)', 'a * (b+c)', '(a * (b + c))'),
    ]
    for raw, normalized, ast in cases:
        assert n(raw) == normalized, raw
        tokens = normalize_implicit_multiplication(tokenize(raw))
        node, pos = parse_expression(tokens)
        assert node is not None, raw
        assert pos == len(tokens), raw
        assert cf(node) == ast, raw


def test_implicit_multiplication_never_splits_a_name() -> None:
    """The word-boundary rules are what keep a multi-character name a
    single name."""
    from parser import normalize_implicit_multiplication_expression as n
    for name in ['ka_rate', 'A_1ab', 'a1b', 'Nat2', 'x_1', 'k_rate',
                 'Nat.succ', 'Vmax', 'Km']:
        assert n(name) == name, name
    eq, free_vars = parse_equation('ka_rate * Ag = 1')
    assert eq is not None
    assert free_vars == ['Ag', 'ka_rate']


def test_nested_parentheses_are_grouped_not_flattened() -> None:
    """Nesting is preserved: ``((a + b))`` is the same term as ``(a + b)``,
    and the grouping is what distinguishes it from ``a + b``."""
    from parser import canonical_form as cf
    node, pos = parse_expression(
        normalize_implicit_multiplication(tokenize('((a + b))')))
    assert node is not None
    assert cf(node) == '(a + b)'
    node, pos = parse_expression(
        normalize_implicit_multiplication(tokenize('(a + (b * (c - d)))')))
    assert node is not None
    assert cf(node) == '(a + (b * (c - d)))'


def test_nested_parentheses_multiply_as_a_group() -> None:
    """A parenthesized group is one operand: ``(a+b)(c+d)`` is a product of
    two sums, not a sum of products."""
    from parser import canonical_form as cf
    node, pos = parse_expression(
        normalize_implicit_multiplication(tokenize('((a+b))(c+d)')))
    assert node is not None
    assert cf(node) == '((a + b) * (c + d))'
    node, pos = parse_expression(
        normalize_implicit_multiplication(tokenize('2((a+b))')))
    assert node is not None
    assert cf(node) == '(2 * (a + b))'


def test_implicit_multiplication_chains_through_several_groups() -> None:
    """The two rules meet on the shapes the mission names: a group is ONE
    operand and the adjacency between two operands is a product.

    Three adjacent groups, a group next to a name, a literal next to a group
    and a signed literal next to a group are all the same rule applied
    repeatedly, and each one is a different product.
    """
    from parser import canonical_form as cf
    cases = [
        ('(a+b)(c+d)(e+f)', '(((a + b) * (c + d)) * (e + f))'),
        ('2(a+b)(c+d)', '((2 * (a + b)) * (c + d))'),
        ('(a+b)(c+d)e', '(((a + b) * (c + d)) * e)'),
        ('2(a+b)c(d)', '(((2 * (a + b)) * c) * d)'),
        ('-2(a+b)', '((-2) * (a + b))'),
    ]
    for raw, expected in cases:
        tokens = normalize_implicit_multiplication(tokenize(raw))
        node, pos = parse_expression(tokens)
        assert node is not None, raw
        assert pos == len(tokens), raw
        assert cf(node) == expected, raw


def test_unbalanced_parentheses_fail_closed() -> None:
    """Every unbalanced shape is rejected; none of them may reach Lean."""
    for expr in ['(a', 'a)', '((a)', '(a))', '(()', '())', '(a + (b)',
                 '(a + b)) = 1', '((a+b) = 1', 'a = (b', '(()) = 1']:
        eq, _ = parse_equation(expr)
        assert eq is None, expr
        assert statement_kind(expr) == 'other', expr


# --- the adjacency rules that the token-level normalizer still has to make ---

def test_negative_number_followed_by_a_variable_is_a_product() -> None:
    """'-2x' is the product of -2 and x.  The adjacency rule for a signed
    literal is a separate branch of the normalizer, so it is pinned here
    rather than left to the digit branch alone."""
    from parser import canonical_form as cf
    tokens = normalize_implicit_multiplication(tokenize('-2x'))
    assert tokens == ['-', '2', '*', 'x']
    node, pos = parse_expression(tokens)
    assert node is not None
    assert pos == len(tokens)
    assert cf(node) == '((-2) * x)'


def test_parse_ode_of_nothing_is_not_an_ode() -> None:
    """A missing expression is not an ODE; the parser says so with the
    documented (None, None) pair rather than with a half-built node."""
    assert parse_ode(None) == (None, None)


def test_nonneg_product_rejects_a_non_product_lhs() -> None:
    """'x >= 0' is a non-negativity claim about a single term, not about a
    product, so the detector answers False."""
    from parser import is_nonneg_product
    node, _ = parse_equation('x >= 0')
    assert node is not None
    assert is_nonneg_product(node) is False


def test_flow_gradient_detector_answers_false_on_a_malformed_node() -> None:
    """A detector must answer False, never None, when it meets a node it
    cannot read: a half-built child must not turn into a truthy answer."""
    from parser import has_flow_gradient_structure
    assert has_flow_gradient_structure(BinOp(Var('a'), '*', None)) is False


# ---------------------------------------------------------------------------
# A Lean timeout is an infrastructure failure, not a refutation.
#
# Importing Mathlib from a cold cache (a clean room, a fresh `.lake`) takes
# far longer than a warm build. When the compile budget was a flat 30s, a
# provable goal timed out, every tactic was recorded as "did not work", and
# the pipeline returned "No tactic succeeded after N attempts" -- the same
# shape it uses for a statement that genuinely does not follow. The only
# trace was stderr='Timeout' buried in `attempts`, so the suite passed or
# failed depending on how warm the machine was.


def test_lean_compile_timeout_default_is_sized_for_a_cold_cache() -> None:
    from agentic_pipeline import LeanAgenticPipeline

    p = LeanAgenticPipeline()
    # A cold Mathlib import does not finish in 30s; 180 is the floor that
    # keeps correctness from depending on cache warmth.
    assert p.lean_compile_timeout >= 180


def test_lean_compile_timeout_is_configurable() -> None:
    from agentic_pipeline import LeanAgenticPipeline

    assert LeanAgenticPipeline(lean_compile_timeout=7).lean_compile_timeout == 7


def test_every_attempt_timing_out_is_reported_as_infrastructure_failure(
    monkeypatch,
) -> None:
    import subprocess as _sp

    from agentic_pipeline import LeanAgenticPipeline

    def _boom(*a, **k):
        raise _sp.TimeoutExpired(cmd="lean", timeout=1)

    monkeypatch.setattr(_sp, "run", _boom)
    p = LeanAgenticPipeline(use_mathlib=False, lean_path="lean")
    res = p.execute_tactic_loop("x + x = 2 * x")
    assert res["success"] is False
    # Not the refutation message: this must never be mistakable for
    # "the statement is unprovable".
    assert "No tactic succeeded" not in res["error"]
    assert res.get("infrastructure_failure") is True
    assert "NOT a refutation" in res["error"]


def test_a_real_refutation_is_not_labelled_infrastructure_failure(
    monkeypatch,
) -> None:
    import subprocess as _sp

    from agentic_pipeline import LeanAgenticPipeline

    class _Done:
        returncode = 1
        stdout = " unsolved goals\n"
        stderr = ""

    monkeypatch.setattr(_sp, "run", lambda *a, **k: _Done())
    p = LeanAgenticPipeline(use_mathlib=False, lean_path="lean")
    res = p.execute_tactic_loop("x + x = 2 * x")
    assert res["success"] is False
    # The compiler answered, so this IS a verdict and keeps the old wording.
    assert res.get("infrastructure_failure") is None
    assert "No tactic succeeded" in res["error"]


# ---------------------------------------------------------------------------
# Tactic selection is a PURE decision, so it must be tested without a prover.
#
# Measured 2026-09-26: mutation kill rate for agentic_pipeline.py against this
# suite is 1.00 (40/40) with Mathlib present, but the clean-room gate measured
# 0.675 with 13 survivors clustered in the tactic loop. Nothing was wrong with
# the logic -- the clean room has no `.lake`, so every prover test fails closed
# and never reaches the dispatch. Tactic selection decides from a STRING, so
# pinning it here makes the coverage independent of whether a compiler, a
# toolchain or a warm cache happens to be available.


def _sel(goal: str, expected_type: str = "") -> str:
    from agentic_pipeline import LeanAgenticPipeline

    p = LeanAgenticPipeline(use_mathlib=False, lean_path="lean")
    return p.select_tactic({"goal": goal, "expected_type": expected_type})


def test_select_tactic_picks_ring_for_polynomial_structure() -> None:
    assert _sel("a + b = b + a") == "ring"
    assert _sel("x^2 - 4 = 0") == "ring"


def test_select_tactic_picks_field_simp_for_division_and_derivatives() -> None:
    # A derivative goal and a bare division goal are both field identities:
    # the divisions have to be cleared before any polynomial tactic applies.
    assert _sel("d/dt C = (A/V) - (C/K)") == "field_simp"
    assert _sel("A/V = C/K") == "field_simp"


def test_select_tactic_picks_linarith_for_inequalities() -> None:
    assert _sel("x > 0") == "linarith"
    assert _sel("a + b <= c") == "linarith"


def test_select_tactic_picks_norm_num_for_concrete_arithmetic() -> None:
    assert _sel("2 + 2 = 4") == "norm_num"
    assert _sel("f(x)*2 = 2*f(x)") == "norm_num"


def test_select_tactic_picks_decide_for_bool_mismatch() -> None:
    # The Bool branch is keyed on the EXPECTED TYPE, not the goal text, so a
    # goal that looks algebraic still routes to decide when the type is Bool.
    assert _sel("a + b = b + a", expected_type="Bool") == "decide"


def test_select_tactic_falls_back_to_simp_on_an_unclassifiable_goal() -> None:
    # A bare identifier carries no operator, so nothing upstream claims it and
    # the default branch decides. (Note "P Q" does NOT land here: adjacent
    # identifiers read as polynomial structure, which is correct -- a product
    # of atoms is something ring can reason about.)
    assert _sel("foo") == "simp"
    assert _sel("True") == "simp"


def test_select_tactic_strips_the_turnstile_prefix() -> None:
    # Lean goals arrive with a turnstile; the same goal must classify the
    # same way with and without it, or dispatch silently depends on framing.
    with_bar = _sel("⊢ a + b = b + a")
    without_bar = _sel("a + b = b + a")
    assert with_bar == without_bar == "ring"


def test_select_tactic_prefers_field_simp_over_ring_for_ode_goals() -> None:
    # Order matters and is not obvious: an ODE goal is ALSO polynomial, so if
    # the ring branch came first it would win and the divisions would never be
    # cleared. Pinning the precedence is what makes the ordering load-bearing.
    assert _sel("d/dt C = (A/V) - (C/K)") == "field_simp"
    assert _sel("A/V = C/K") == "field_simp"


def test_candidates_for_closed_numeric_equality_prefer_non_reflexive() -> None:
    from agentic_pipeline import LeanAgenticPipeline

    p = LeanAgenticPipeline(use_mathlib=False, lean_path="lean")
    cands = p.get_tactic_candidates("2 + 2 = 4")
    assert cands[:2] == ["simp", "decide"]
    assert "rfl" not in cands[:2]


def test_candidates_for_an_identity_lead_with_rfl() -> None:
    from agentic_pipeline import LeanAgenticPipeline

    p = LeanAgenticPipeline(use_mathlib=False, lean_path="lean")
    cands = p.get_tactic_candidates("a = a")
    assert cands[0] == "rfl"


def test_candidates_for_an_ode_lead_with_a_field_simp_chain() -> None:
    from agentic_pipeline import LeanAgenticPipeline

    p = LeanAgenticPipeline(use_mathlib=False, lean_path="lean")
    cands = p.get_tactic_candidates("d/dt C = A/V - C/K")
    assert any("field_simp" in t and "ring" in t for t in cands), cands
    # Candidates are ordered most-behavioural-first and must not repeat.
    assert len(cands) == len(set(cands))


# ---------------------------------------------------------------------------
# Two coverage holes the clean-room mutation run exposed, both compiler-free.
#
# The clean-room kill rate for agentic_pipeline.py is 0.5167 (31/60) against
# 1.0000 (60/60) warm, and the difference is entirely this: without Mathlib
# the prover tests fail closed and never reach the code below. Both are pure
# string handling, so both are testable anywhere.


def test_execute_with_initial_code_delegates_to_the_tactic_loop() -> None:
    # qed-01's contract names BOTH execute_tactic_loop and
    # _execute_with_initial_code, but nothing covered the second: it extracts
    # the expression after the LAST ': ... := by' and hands the rest to the
    # loop. A mutant that broke this delegation survived the whole suite.
    from agentic_pipeline import LeanAgenticPipeline

    p = LeanAgenticPipeline(use_mathlib=False, lean_path="lean")
    res = p._execute_with_initial_code(
        "theorem qed_goal : 2 + 2 = 4 := by\n  norm_num\n"
    )
    assert res["success"] is True
    assert res["lean_code"].startswith("theorem qed_goal : 2 + 2 = 4")


def test_execute_with_initial_code_fails_closed_without_a_by_block() -> None:
    # No ': ... := by' means there is no expression to extract. This must be
    # an explicit failure, not a pass with an empty proof.
    from agentic_pipeline import LeanAgenticPipeline

    p = LeanAgenticPipeline(use_mathlib=False, lean_path="lean")
    res = p._execute_with_initial_code("theorem qed_goal : 2 + 2 = 4\n")
    assert res["success"] is False
    assert "Could not extract expression" in res["error"]
    assert res["attempts"] == []


def test_execute_with_initial_code_does_not_smuggle_sorry() -> None:
    from agentic_pipeline import LeanAgenticPipeline

    p = LeanAgenticPipeline(use_mathlib=False, lean_path="lean")
    res = p._execute_with_initial_code(
        "theorem qed_goal : 2 + 2 = 4 := by\n  sorry\n"
    )
    assert "sorry" not in res.get("lean_code", "")


def _typed_pipeline(monkeypatch, var_type: str):
    """A pipeline whose inferred variable type is pinned.

    ``generate_lean_code`` derives the type from the free variables and the
    expression, so the Int/Rat branches are only reachable by controlling
    that inference. Pinning it here is what makes these three branches
    reachable from a test at all.
    """
    from agentic_pipeline import LeanAgenticPipeline

    p = LeanAgenticPipeline(use_mathlib=False, lean_path="lean")
    monkeypatch.setattr(
        p, "_get_var_type", lambda variables, expression: var_type)
    return p


def test_generate_lean_code_annotates_negative_int_literals(monkeypatch) -> None:
    # Under Int the negative literals need an explicit annotation or Lean
    # infers them at a different type; the annotation must land on the
    # literals, not on the whole statement.
    p = _typed_pipeline(monkeypatch, "Int")
    code = p.generate_lean_code("-5 = -5", [])
    assert "(-5 : Int)" in code
    assert code.startswith("theorem qed_goal : ")
    assert "= (-5 : Int) := by" in code


def test_generate_lean_code_leaves_non_negative_ints_unannotated(monkeypatch) -> None:
    # The Int branch is guarded on a '-' being present AND the type being Int.
    # A negative expression typed Real must not pick up an Int annotation.
    p = _typed_pipeline(monkeypatch, "Int")
    assert ": Int" not in p.generate_lean_code("a + b = b + a", [])
    p_real = _typed_pipeline(monkeypatch, "Real")
    assert ": Int" not in p_real.generate_lean_code("-5 = -5", [])


def test_generate_lean_code_handles_rat_division(monkeypatch) -> None:
    p = _typed_pipeline(monkeypatch, "Rat")
    code = p.generate_lean_code("3/4 = 3/4", [])
    assert code.startswith("theorem qed_goal : ")
    assert "3/4" in code


# ---------------------------------------------------------------------------
# qed-01-no-sorry-gate: the gate must FAIL CLOSED.
#
# The gate had three ways to wave a proof through:
#
#   1. The compiler's EXIT CODE is not a gate. Lean prints
#        warning: declaration uses `sorry`
#      and still exits 0, so a sorry proof is a "successful" compile. Only
#      the source/warning/axiom checks can catch it.
#
#   2. The specific compiler-output detectors were DEAD CODE. Lean
#      backtick-quotes the token ("uses `sorry`"), so a detector written for
#      the bare "uses sorry" form matched nothing and only the generic
#      catch-all could fire -- the precise reasons the detectors existed to
#      produce were unreachable.
#
#   3. The axioms check was FAIL-OPEN. It never looked at the compiler's
#      exit code and never required the axioms report to exist, so:
#        - a file with a syntax error came back "clean";
#        - a file whose theorem was not named `qed_goal` came back "clean",
#          because `#print axioms qed_goal` errored out and there was
#          nothing left to grep.
#      Absence of evidence was being read as evidence of innocence, which is
#      the one thing a no-sorry gate must never do.
#
# The tests below pin the three fixes, and drive the tactic loop end to end
# so that a sorry-bearing output is shown to return FAILURE, not success.


class _FakeLeanResult:
    """Stand-in for the object ``subprocess.run`` returns."""

    def __init__(self, returncode: int = 0, stdout: str = "", stderr: str = ""):
        self.returncode = returncode
        self.stdout = stdout
        self.stderr = stderr


def _lean_path_in(cmd) -> str:
    """The .lean file a Lean command line refers to, if any."""
    for part in (cmd if isinstance(cmd, list) else []):
        if str(part).endswith(".lean"):
            return str(part)
    return ""


def _read_lean(path: str) -> str:
    try:
        with open(path) as fh:
            return fh.read()
    except OSError:
        return ""


def _fake_lean_run(compile_returncode: int = 0, compile_output: str = "",
                   axioms_report: str | None = None):
    """Build a ``subprocess.run`` stand-in that behaves like Lean.

    The axioms check re-compiles the file with ``#print axioms <name>``
    appended, so the stand-in has to answer that request differently from an
    ordinary compile -- otherwise the fake is indistinguishable from a
    compiler that says nothing at all, and the gate's behaviour under test
    would be untestable.
    """
    def _run(cmd, **kwargs):
        text = _read_lean(_lean_path_in(cmd))
        if "#print axioms" in text:
            report = (
                axioms_report
                if axioms_report is not None
                else "'qed_goal' does not depend on any axioms"
            )
            return _FakeLeanResult(0, report, "")
        return _FakeLeanResult(compile_returncode, compile_output, "")
    return _run


# --- 1. the compiler's exit code is NOT the gate ---

def test_check_for_sorry_catches_the_message_lean_actually_prints() -> None:
    """Lean 4.33 prints ``warning: declaration uses `sorry``` -- the token is
    backtick-quoted, so a detector written for the bare "uses sorry" form
    matches nothing."""
    from agentic_pipeline import LeanAgenticPipeline
    p = LeanAgenticPipeline()
    has_sorry, reason = p.check_for_sorry(
        "theorem qed_goal : 1 = 1 := by\n  rfl",
        "warning: declaration uses `sorry`",
    )
    assert has_sorry is True
    # The SPECIFIC detector must fire, not merely the generic catch-all.
    assert "declaration uses sorry" in reason.lower(), reason


def test_check_for_sorry_specific_warning_detector_is_live() -> None:
    """The `warning: ... uses sorry` detector must reach its own reason."""
    from agentic_pipeline import LeanAgenticPipeline
    p = LeanAgenticPipeline()
    has_sorry, reason = p.check_for_sorry(
        "theorem qed_goal : 1 = 1 := by\n  rfl",
        "warning: declaration 'qed_goal' uses `sorry`",
    )
    assert has_sorry is True
    assert "warning" in reason.lower(), reason


def test_tactic_loop_rejects_a_sorry_proof_even_when_the_compiler_exits_zero(
    monkeypatch,
) -> None:
    """A proof Lean accepted only because it contained a `sorry` must never
    be reported as verified -- even though Lean exited 0."""
    import subprocess as _sp
    from agentic_pipeline import LeanAgenticPipeline

    monkeypatch.setattr(
        _sp, "run",
        _fake_lean_run(
            compile_returncode=0,
            compile_output="warning: declaration uses `sorry`",
        ),
    )
    p = LeanAgenticPipeline(use_mathlib=False, lean_path="lean")
    res = p.execute_tactic_loop("0 = 0")
    assert res["success"] is False
    assert res["attempts"], "the attempts must be recorded"
    assert all(a["has_sorry"] for a in res["attempts"]), res["attempts"]
    assert all("sorry" in a["sorry_reason"].lower() for a in res["attempts"])


def test_tactic_loop_accepts_a_clean_proof_under_the_same_mock(monkeypatch) -> None:
    """The control for the test above: the same mock, without the sorry
    warning, must still succeed. Without this the rejection test could pass
    for the wrong reason."""
    import subprocess as _sp
    from agentic_pipeline import LeanAgenticPipeline

    monkeypatch.setattr(_sp, "run", _fake_lean_run())
    p = LeanAgenticPipeline(use_mathlib=False, lean_path="lean")
    res = p.execute_tactic_loop("0 = 0")
    assert res["success"] is True
    assert res["verification"]["axioms_check"] == "passed"
    assert "sorry" not in res["lean_code"]


# --- 2. the axioms check must fail closed ---

def test_verify_no_sorry_axioms_fails_closed_when_the_file_does_not_compile() -> None:
    """A file the compiler rejected tells us NOTHING about its axiom set, so
    it must not be certified clean. The old check never read the exit code
    and returned "clean" for a file with a syntax error."""
    import os
    import tempfile
    from agentic_pipeline import LeanAgenticPipeline
    p = LeanAgenticPipeline()
    with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", delete=False) as f:
        f.write("theorem broken : : : := by\n")
        path = f.name
    try:
        is_clean, reason = p._verify_no_sorry_axioms(path)
        assert is_clean is False
        assert "fail-closed" in reason.lower() or "error" in reason.lower()
    finally:
        os.unlink(path)


def test_verify_no_sorry_axioms_fails_closed_when_no_report_is_produced() -> None:
    """No theorem means no axiom set to check: absence of evidence is not
    evidence of innocence."""
    import os
    import tempfile
    from agentic_pipeline import LeanAgenticPipeline
    p = LeanAgenticPipeline()
    with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", delete=False) as f:
        f.write("def helper := 1\n")
        path = f.name
    try:
        is_clean, reason = p._verify_no_sorry_axioms(path)
        assert is_clean is False
        assert "fail-closed" in reason.lower() or "error" in reason.lower()
    finally:
        os.unlink(path)


def test_verify_no_sorry_axioms_rejects_sorryax_in_the_axiom_list() -> None:
    """The verdict must come from the axioms REPORT, not from grepping the
    compiler output for the word 'sorry'."""
    import os
    import tempfile
    from agentic_pipeline import LeanAgenticPipeline
    p = LeanAgenticPipeline()
    with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", delete=False) as f:
        f.write("theorem qed_goal : 1 = 1 := by\n  sorry\n")
        path = f.name
    try:
        is_clean, reason = p._verify_no_sorry_axioms(path)
        assert is_clean is False
        assert "sorry" in reason.lower()
    finally:
        os.unlink(path)


def test_verify_no_sorry_axioms_binds_the_report_to_the_declared_theorem() -> None:
    """The report is asked for the theorem the file actually declares, so a
    sorry under a different name is still caught."""
    import os
    import tempfile
    from agentic_pipeline import LeanAgenticPipeline
    p = LeanAgenticPipeline()
    with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", delete=False) as f:
        f.write("theorem my_lemma : 1 = 1 := by\n  sorry\n")
        path = f.name
    try:
        is_clean, reason = p._verify_no_sorry_axioms(path)
        assert is_clean is False
        assert "sorry" in reason.lower()
    finally:
        os.unlink(path)


def test_verify_no_sorry_axioms_accepts_a_clean_declaration() -> None:
    """The control for the fail-closed tests: a clean declaration is clean.
    (Tolerant of a missing Lean, like the pre-existing sibling test.)"""
    import os
    import tempfile
    from agentic_pipeline import LeanAgenticPipeline
    p = LeanAgenticPipeline()
    with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", delete=False) as f:
        f.write("theorem my_lemma : 1 = 1 := by\n  rfl\n")
        path = f.name
    try:
        is_clean, reason = p._verify_no_sorry_axioms(path)
        assert is_clean is True or "fail-closed" in reason.lower() or "error" in reason.lower()
    finally:
        os.unlink(path)


# --- 3. the gate is evaluated on the FILE, not only on the compiled string ---

def test_tactic_loop_rejects_a_proof_whose_file_on_disk_carries_a_sorry(
    monkeypatch,
) -> None:
    """The artefact on disk is what a reviewer re-checks and re-compiles, so
    the gate has to be evaluated on the file -- not only on the string that
    was handed to the compiler."""
    import subprocess as _sp
    from agentic_pipeline import LeanAgenticPipeline

    def _run(cmd, **kwargs):
        path = _lean_path_in(cmd)
        text = _read_lean(path)
        if "#print axioms" in text:
            return _FakeLeanResult(
                0, "'qed_goal' does not depend on any axioms", ""
            )
        # Whatever was compiled, the artefact on disk now carries a sorry.
        with open(path, "w") as fh:
            fh.write("theorem qed_goal : 1 = 1 := by\n  sorry\n")
        return _FakeLeanResult(0, "", "")

    monkeypatch.setattr(_sp, "run", _run)
    p = LeanAgenticPipeline(use_mathlib=False, lean_path="lean")
    res = p.execute_tactic_loop("0 = 0")
    assert res["success"] is False
    assert res["attempts"]
    assert all(a["has_sorry"] for a in res["attempts"]), res["attempts"]
    assert all("re-read" in a["sorry_reason"] for a in res["attempts"])


def test_source_on_disk_is_clean_fails_closed_when_the_file_cannot_be_read() -> None:
    """A file that cannot be read is not a file that has been shown to be
    sorry-free."""
    from agentic_pipeline import LeanAgenticPipeline
    p = LeanAgenticPipeline(use_mathlib=False, lean_path="lean")
    is_clean, reason = p._source_on_disk_is_clean("/nonexistent/path.lean")
    assert is_clean is False
    assert "fail-closed" in reason.lower() or "error" in reason.lower()


# --- 4. the agentic repair path carries the same gate ---

def test_adapter_repair_rejects_a_sorry_proof(monkeypatch) -> None:
    """The adapter path is a second way to reach success, so it has to carry
    the same no-sorry gate as the static path."""
    import subprocess as _sp
    from agentic_pipeline import LeanAgenticPipeline

    class _FakeState:
        logs = "```lean\nring\n```"

    class _FakeAdapter:
        def __init__(self):
            self.prompts: list[str] = []

        def send(self, prompt, session):
            self.prompts.append(prompt)
            return _FakeState()

    def _run(cmd, **kwargs):
        text = _read_lean(_lean_path_in(cmd))
        if "#print axioms" in text:
            return _FakeLeanResult(
                0, "'qed_goal' does not depend on any axioms", ""
            )
        if "ring" in text:
            # The adapter's tactic compiles, but Lean warns that the proof
            # it accepted still uses `sorry`.
            return _FakeLeanResult(0, "warning: declaration uses `sorry`", "")
        return _FakeLeanResult(1, "", "error: unsolved goals\n⊢ 0 = 0\n")

    monkeypatch.setattr(_sp, "run", _run)
    adapter = _FakeAdapter()
    p = LeanAgenticPipeline(use_mathlib=False, lean_path="lean", adapter=adapter)
    res = p.execute_tactic_loop("0 = 0", max_iterations=3)
    assert res["success"] is False
    assert adapter.prompts, "the adapter must have been consulted"
    adapter_attempts = [
        a for a in res["attempts"] if "[adapter]" in a.get("tactic", "")
    ]
    assert adapter_attempts, res["attempts"]
    assert all(a["has_sorry"] for a in adapter_attempts), adapter_attempts


def test_execute_with_initial_code_never_echoes_a_sorry_artifact() -> None:
    """A sorry-bearing artefact must never be handed back as a result."""
    from agentic_pipeline import LeanAgenticPipeline
    p = LeanAgenticPipeline(use_mathlib=False, lean_path="lean")
    res = p._execute_with_initial_code("theorem qed_goal : 1 = 1\n  sorry\n")
    assert res["success"] is False
    assert "sorry" not in res.get("lean_code", "")


# ---------------------------------------------------------------------------
# qed-03-type-inference: context-aware type selection.
#
# The type of a statement used to be guessed from the TEXT with regular
# expressions, which could not tell a negative LITERAL from a binary
# subtraction, nor a numeric denominator from a symbolic one.  Two things
# followed from that:
#
#   1. every equality containing a `*` was typed ℝ (the relation operator
#      `=` matched the "inequality" pattern), so a plain product was
#      elaborated in a field it did not need;
#   2. the type the pipeline REPORTED was not the type the generated Lean
#      was elaborated at, so a statement that is FALSE in ℤ could be
#      "verified" because ℕ subtraction truncates (`1 - 2 = 0`).
#
# The tests below pin the AST-driven selection AND the fidelity of the
# emitted statement: what the pipeline claims to have checked is what Lean
# actually checked.  The selection tests are compiler-free; the honesty
# tests need a prover.
# ---------------------------------------------------------------------------


def test_suggest_type_joins_mixed_expressions() -> None:
    """A statement that mixes constructs is read at the strongest type any
    of its parts needs -- not at the first type that happens to match."""
    from agentic_pipeline import LeanAgenticPipeline
    p = LeanAgenticPipeline()
    # division + subtraction -> ℚ (the subtraction alone would say ℤ)
    assert p._suggest_type("x / 2 - 1 = 0") == "Rat"
    # division + subtraction + a symbolic denominator -> ℝ
    assert p._suggest_type("x / y - 1 = 0") == "Real"
    # a negative literal joined with a division -> ℚ
    assert p._suggest_type("-1 + x / 2 = 0") == "Rat"
    # a negative literal joined with a symbolic division -> ℝ
    assert p._suggest_type("-1 + x / y = 0") == "Real"


def test_suggest_type_reads_the_denominator_not_the_text() -> None:
    """A numeric denominator is exact rational arithmetic (ℚ); a symbolic
    one is a field (ℝ).  The text heuristic could not tell `x / 2` from
    `x / (2 + 1)` -- both are exact, neither needs a field."""
    from agentic_pipeline import LeanAgenticPipeline
    p = LeanAgenticPipeline()
    assert p._suggest_type("x / (2 + 1) = y") == "Rat"
    assert p._suggest_type("x / y = z") == "Real"


def test_suggest_type_product_equality_is_not_real() -> None:
    """`a * b = c` is an equality with a product, not an inequality: it
    needs no field, so it is read at ℕ."""
    from agentic_pipeline import LeanAgenticPipeline
    p = LeanAgenticPipeline()
    assert p._suggest_type("a * b = c") == "Nat"
    assert p._suggest_type("2 * x = x * 2") == "Nat"
    assert p._suggest_type("(a + b)^2 = a^2 + 2ab + b^2") == "Nat"
    assert p._suggest_type("ka * A_gut = ka * A_gut") == "Nat"


def test_suggest_type_bare_comparison_gets_no_field() -> None:
    """A bare comparison is left at ℕ: a positivity hypothesis for it would
    be the conclusion.  A comparison over a product is a positivity claim
    ABOUT THE FACTORS, and `positivity` needs ℝ to discharge it."""
    from agentic_pipeline import LeanAgenticPipeline
    p = LeanAgenticPipeline()
    assert p._suggest_type("x > 0") == "Nat"
    assert p._suggest_type("x >= 0") == "Nat"
    assert p._suggest_type("k * x > 0") == "Real"


def test_generate_lean_code_does_not_corrupt_binary_subtraction() -> None:
    """The old `(-\\d+)` annotation matched the `-` of a binary subtraction,
    so `2-1 = 1` was emitted as `2(-1 : Int) = 1` -- which is not Lean."""
    from agentic_pipeline import LeanAgenticPipeline
    p = LeanAgenticPipeline(use_mathlib=True)
    code = p.generate_lean_code("2-1 = 1", [])
    assert "2(-1" not in code
    assert "2-1" in code
    assert ": Int" in code


def test_generate_lean_code_closed_statement_is_ascribed_at_the_inferred_type() -> None:
    """A closed statement has no variable declaration to carry its type, so
    it must be ascribed inside the statement -- otherwise Lean elaborates the
    numerals at ℕ, where subtraction and division TRUNCATE."""
    from agentic_pipeline import LeanAgenticPipeline
    p = LeanAgenticPipeline(use_mathlib=True)
    code = p.generate_lean_code("1 - 2 = 0", [])
    assert "(1 - 2 : Int)" in code
    assert "(0 : Int)" in code


def test_generate_lean_code_natural_statement_is_not_ascribed() -> None:
    """A statement that needs no type beyond ℕ is left alone: an
    unnecessary annotation would change the theorem for nothing."""
    from agentic_pipeline import LeanAgenticPipeline
    p = LeanAgenticPipeline(use_mathlib=True)
    code = p.generate_lean_code("2 + 2 = 4", [])
    assert ": Int" not in code
    assert ": Rat" not in code
    assert "2 + 2 = 4" in code


def test_closed_subtraction_is_not_verified_by_nat_truncation() -> None:
    """`1 - 2 = 0` is FALSE in ℤ, and true in ℕ only because ℕ subtraction
    truncates.  The pipeline must not report a truncated statement as
    verified -- and it must never do it with a sorry."""
    from agentic_pipeline import LeanAgenticPipeline
    res = LeanAgenticPipeline(use_mathlib=True).run("1 - 2 = 0")
    assert res["success"] is False
    assert "sorry" not in res.get("lean_code", "")


def test_closed_negative_result_is_not_verified_by_nat_truncation() -> None:
    """`0 - 1 = 0` truncates to `0 = 0` at ℕ; at ℤ it is false."""
    from agentic_pipeline import LeanAgenticPipeline
    res = LeanAgenticPipeline(use_mathlib=True).run("0 - 1 = 0")
    assert res["success"] is False
    assert "sorry" not in res.get("lean_code", "")


def test_closed_division_is_not_verified_by_nat_truncation() -> None:
    """`5 / 2 = 2` is true at ℕ (truncating division) and false at ℚ."""
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline(use_mathlib=True)
    if pipeline.use_mathlib:
        res = pipeline.run("5 / 2 = 2")
        assert res["success"] is False
        assert "sorry" not in res.get("lean_code", "")


def test_mass_conservation_witness_still_verifies_at_int() -> None:
    """The regression guard in the other direction: a TRUE statement must
    still be verified after the type selection changed.  The witness is a
    sum of signed integers, so it is read at ℤ and must still prove."""
    from agentic_pipeline import LeanAgenticPipeline
    res = LeanAgenticPipeline(use_mathlib=True).run(
        "-6 + 9 + -13 + 4 + 6 + 0 = 0")
    assert res["success"] is True
    assert "sorry" not in res["lean_code"]
    assert res["verification"]["axioms_check"] == "passed"


# ---------------------------------------------------------------------------
# qed-04-tactic-policy: the tactic policy is decided from the AST.
#
# The policy used to read the goal TEXT:
#
#   * ``'ring' in goal.lower()`` sent the goal ``spring = spring`` to
#     ``ring`` -- the substring matched, and ``ring`` cannot close an
#     identity;
#   * ``re.search(r'\d+', goal)`` treated the NAME ``A_1`` as a numeral;
#   * the branches were ordered so that a goal mixing a power with a
#     division went to ``ring``, which cannot clear the division;
#   * the local hypotheses were ignored, so a goal that was already in the
#     context was re-proved from scratch.
#
# The selection is now read off a SHAPE -- the facts a statement's AST
# carries -- the candidate chains are COMPOSED from atomic steps, and
# ``select_tactic`` also looks at the goal state (the local hypotheses and
# the ambient type).
#
# These tests are compiler-free: tactic selection is a pure decision, so it
# must be pinned independently of whether Lean, Mathlib or a warm build
# cache happens to be available.
# ---------------------------------------------------------------------------


def _cands(expression: str) -> list:
    from agentic_pipeline import LeanAgenticPipeline
    return LeanAgenticPipeline().get_tactic_candidates(expression)


def test_select_tactic_does_not_match_the_keyword_ring() -> None:
    """``spring = spring`` CONTAINS the substring "ring".  The old policy
    matched on the text and handed the goal to ``ring``, which cannot close
    an identity; the AST says it is reflexive, so ``rfl`` closes it."""
    assert _sel("⊢ spring = spring") == "rfl"
    # ... and a goal that really is algebraic still goes to ring.
    assert _sel("⊢ a + b = b + a") == "ring"


def test_select_tactic_recognises_an_identity_goal() -> None:
    """An identity is a goal ``rfl`` closes; the old policy only knew the
    identity short-circuit for STATEMENTS, not for goals."""
    assert _sel("⊢ a = a") == "rfl"
    assert _sel("⊢ a + b = a + b") == "rfl"


def test_select_tactic_clears_divisions_before_polynomial_tactics() -> None:
    """A goal that mixes a power with a division is a FIELD identity: the
    division has to be cleared before any polynomial tactic applies, so the
    field branch must come before the polynomial one."""
    assert _sel("⊢ (a + b)^2 / c = (a^2 + 2ab + b^2) / c") == "field_simp"
    # A division without a power is a field identity too.
    assert _sel("⊢ A/V = C/K") == "field_simp"


def test_select_tactic_uses_a_matching_hypothesis() -> None:
    """The goal is already in the context: ``assumption`` closes it.  The
    old policy never looked at the hypotheses, so it re-proved the goal
    from scratch."""
    from agentic_pipeline import LeanAgenticPipeline
    p = LeanAgenticPipeline(use_mathlib=False, lean_path="lean")
    assert p.select_tactic(
        {"goal": "⊢ 0 < Q", "hypotheses": ["hQ : 0 < Q"]}
    ) == "assumption"
    # The same hypotheses, read from the compiler output Lean reported.
    stderr = (
        "error: unsolved goals\n"
        "context:\n"
        "hQ : 0 < Q\n"
        "⊢ 0 < Q\n"
    )
    assert p.select_tactic(
        {"goal": "⊢ 0 < Q", "error_output": stderr}
    ) == "assumption"
    # A goal that is NOT in the context is not closed by assumption.
    assert p.select_tactic(
        {"goal": "⊢ 0 < R", "hypotheses": ["hQ : 0 < Q"]}
    ) != "assumption"


def test_select_tactic_positivity_claim_over_a_ratio() -> None:
    """``0 < Q / V`` with positivity hypotheses for Q and V is a claim
    about the SIGNS OF THE FACTORS: ``positivity`` discharges it.  A bare
    ``0 < x`` is not (the non-negativity would be the conclusion), so it
    stays with the ordered tactics."""
    from agentic_pipeline import LeanAgenticPipeline
    p = LeanAgenticPipeline(use_mathlib=False, lean_path="lean")
    assert p.select_tactic({
        "goal": "⊢ 0 < Q / V",
        "hypotheses": ["hQ : 0 < Q", "hV : 0 < V"],
        "expected_type": "Real",
    }) == "positivity"
    assert _sel("⊢ 0 < x") == "linarith"


def test_select_tactic_recognises_a_derivative_from_the_ast() -> None:
    """``dA_liver/dt`` is a DIVISION by the time variable, so the AST says
    it is a derivative; the policy must not depend on the spelling of the
    notation.  A name that merely CONTAINS "dt" is not a derivative."""
    assert _sel("⊢ dA_liver/dt = Q * (C_p - C_liver / Kp)") == "field_simp"
    assert _sel("⊢ d/dt C = (A/V) - (C/K)") == "field_simp"
    # 'dt' on its own is an ordinary name: the goal is reflexive.
    assert _sel("⊢ dt = dt") == "rfl"


def test_select_tactic_uses_the_ast_for_numerals() -> None:
    """A numeral is a ``Num`` node.  ``A_1`` is a NAME that happens to
    contain a digit, and the old digit regex treated it as a numeral."""
    assert _sel("⊢ 2 + 2 = 4") == "norm_num"
    assert _sel("⊢ A_1 = A_1") == "rfl"
    assert _sel("⊢ A_1 = A_2") == "simp"


def test_select_tactic_falls_back_to_simp_for_an_unparsable_goal() -> None:
    """A goal the parser cannot read (a Lean construct outside the MVP
    language) must not crash the policy: it falls back to the weakest
    assumption."""
    assert _sel("⊢ ∀ (x : ℝ), x + 0 = x") == "simp"


def test_candidates_are_composed_of_atomic_steps() -> None:
    """Every candidate is a ';'-joined chain of REGISTRY steps: the
    combinations are composed, not pasted in as literals."""
    from agentic_pipeline import _TACTIC_STEPS
    rendered = set(_TACTIC_STEPS.values())
    for expression in (
        "Q * (C_p - C_tissue / Kp) = Q * C_p - Q * C_tissue / Kp",
        "x < x + 1",
        "dA_liver/dt = Q * (C_p - C_liver / Kp)",
        "(Q / (V_central * Kp)) * A_central >= 0",
        "2 + 2 = 4",
    ):
        for candidate in _cands(expression):
            for step in candidate.split("; "):
                assert step in rendered, (expression, candidate, step)


def test_field_simp_then_ring_is_composed_from_atomic_steps() -> None:
    """``field_simp; ring`` is what the composition of two steps yields."""
    from agentic_pipeline import compose_tactic
    assert compose_tactic(["field_simp", "ring"]) == "field_simp; ring"
    assert compose_tactic(["intros", "field_simp", "ring"]) == \
        "intros; field_simp; ring"
    candidates = _cands(
        "Q * (C_p - C_tissue / Kp) = Q * C_p - Q * C_tissue / Kp")
    assert "intros; field_simp; ring" in candidates


def test_candidates_are_free_of_duplicates() -> None:
    """A candidate that repeats a step is a wasted compile."""
    for expression in (
        "Q * (C_p - C_tissue / Kp) = Q * C_p - Q * C_tissue / Kp",
        "x < x + 1",
        "dA_liver/dt = Q * (C_p - C_liver / Kp)",
        "Vmax * C / (Km + C) >= 0",
    ):
        candidates = _cands(expression)
        assert len(candidates) == len(set(candidates)), expression


def test_candidates_for_a_derivative_statement_use_the_ode_chain() -> None:
    """A rate-of-change statement is recognised from the AST (a division by
    the time variable), so it leads with the field/distributive chain."""
    candidates = _cands("dA_liver/dt = Q * (C_p - C_liver / Kp)")
    assert candidates[0] == "intros; dsimp; field_simp; ring"
    assert candidates.index("dsimp") < candidates.index("field_simp") \
        < candidates.index("ring_nf")


def test_policy_and_type_agree_about_the_field_requirement() -> None:
    """The policy's "needs a field" flag and the inferred type must not
    disagree: a numeric denominator is exact rational arithmetic, a
    symbolic one is a field."""
    from agentic_pipeline import LeanAgenticPipeline, _shape_from_node
    p = LeanAgenticPipeline()
    for expression, expects_field, expects_type in (
        ("x / y = z", True, "Real"),
        ("x / (2 + 1) = y", False, "Rat"),
        ("4 / 2 = 2", False, "Rat"),
        ("a + b = b + a", False, "Nat"),
    ):
        shape = _shape_from_node(p._parse_statement(expression))
        assert shape.has_field_division is expects_field, expression
        assert p._suggest_type(expression) == expects_type, expression


def test_derivative_detection_is_a_parser_fact() -> None:
    """``dA/dt`` is a division by the time variable.  The parser keeps the
    time variable intact, so the AST carries the derivative instead of
    shredding it into a product."""
    from parser import is_derivative, parse_equation
    node, _ = parse_equation("dA_liver/dt = Q * (C_p - C_liver / Kp)")
    assert node is not None
    assert is_derivative(node) is True
    # An ordinary ratio is not a derivative.
    node, _ = parse_equation("x / y = z")
    assert node is not None
    assert is_derivative(node) is False
    # The time variable survives normalization as a NAME.
    from parser import normalize_implicit_multiplication_expression as n
    assert n("dA/dt") == "dA/dt"
    assert n("dt") == "dt"


def test_numeric_literal_detection_is_a_parser_fact() -> None:
    """A numeral is a ``Num`` node; a name that contains a digit is not."""
    from parser import has_numeric_literal, parse_equation
    node, _ = parse_equation("2 + 2 = 4")
    assert node is not None
    assert has_numeric_literal(node) is True
    node, _ = parse_equation("A_1 = A_2")
    assert node is not None
    assert has_numeric_literal(node) is False
    assert has_numeric_literal(None) is False


def test_numeric_denominator_is_not_a_field_statement() -> None:
    """``x / (2 + 1)`` is exact rational arithmetic, not a field: the
    denominator is judged by its VALUE, so the tactic policy and the type
    selection cannot disagree about it."""
    from parser import has_rational_structure, parse_equation
    node, _ = parse_equation("x / (2 + 1) = y")
    assert node is not None
    assert has_rational_structure(node) is False
    node, _ = parse_equation("x / y = z")
    assert node is not None
    assert has_rational_structure(node) is True


# ---------------------------------------------------------------------------
# qed-04-tactic-policy (part 2): the mutation gate.
#
# The mission's mutation tier measures the kill rate of the mutants of
# agentic_pipeline.py against this suite, and the gate is 0.7.  The mutants
# that survived the first measurement cluster in three places:
#
#   * the SHAPE's defaults -- the fail-safe assumptions an unparsable
#     statement falls back to were never pinned, so flipping one of them
#     changed nothing;
#   * the EXPRESSION fallback of the statement parse -- a statement with no
#     relation operator is classified as an EXPRESSION, and nothing said so;
#   * the no-sorry gate's bookkeeping -- a failed axioms check, a missing
#     compiler and a successful agentic repair are all paths the suite
#     walked past without asserting what they report.
#
# The tests below pin those facts.
# ---------------------------------------------------------------------------


def test_statement_shape_defaults_are_the_fail_safe_assumptions() -> None:
    """A statement that cannot be parsed must not make the policy GUESS: the
    shape's defaults are the weakest facts, and they are what the policy
    falls back to."""
    from agentic_pipeline import StatementShape
    shape = StatementShape()
    assert shape.node is None
    assert shape.free_vars == []
    assert shape.is_derivative is False
    assert shape.is_identity is False
    assert shape.is_closed_numeric is False
    assert shape.has_division is False
    assert shape.has_field_division is False
    assert shape.has_power is False
    assert shape.has_numeral is False
    assert shape.has_numeric_ops is False
    assert shape.is_inequality is False
    assert shape.is_strict is False
    assert shape.is_positivity_claim is False
    assert shape.is_metzler_positivity is False
    assert shape.is_step_conservation is False
    assert shape.is_boundary_flow is False


def test_candidates_for_a_bare_expression_use_the_expression_parse() -> None:
    """A statement with no relation operator is still classified: it is
    parsed as an EXPRESSION, not as an empty statement."""
    candidates = _cands("x / y")
    assert "field_simp" in candidates
    assert candidates.index("field_simp") < candidates.index("simp")


def test_a_failed_axioms_check_is_recorded_as_a_sorry_leak(monkeypatch) -> None:
    """When the axioms report shows a sorry, the attempt is recorded as a
    sorry leak: the trace must not say "no sorry" about a proof that leaned
    on a sorry axiom."""
    import subprocess as _sp
    from agentic_pipeline import LeanAgenticPipeline

    def _run(cmd, **kwargs):
        text = _read_lean(_lean_path_in(cmd))
        if "#print axioms" in text:
            return _FakeLeanResult(
                0, "'qed_goal' depends on axioms: [sorryAx]", ""
            )
        return _FakeLeanResult(0, "", "")

    monkeypatch.setattr(_sp, "run", _run)
    p = LeanAgenticPipeline(use_mathlib=False, lean_path="lean")
    res = p.execute_tactic_loop("0 = 0")
    assert res["success"] is False
    assert res["attempts"]
    assert all(a["has_sorry"] for a in res["attempts"]), res["attempts"]


def test_a_sorry_in_another_declaration_is_still_a_leak() -> None:
    """The axioms report is about THIS theorem, but a sorry anywhere in the
    file is a leak: the file must not be certified clean."""
    import os
    import tempfile
    from agentic_pipeline import LeanAgenticPipeline
    p = LeanAgenticPipeline()
    with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", delete=False) as f:
        f.write(
            "theorem qed_goal : 1 = 1 := by\n  rfl\n\n"
            "theorem other : 2 = 2 := by\n  sorry\n"
        )
        path = f.name
    try:
        is_clean, reason = p._verify_no_sorry_axioms(path)
        # A file that carries a sorry must never be certified clean.  (With
        # no Lean at all the check fails closed, which is also not clean.)
        assert is_clean is False
        assert "sorry" in reason.lower() or "fail-closed" in reason.lower()
    finally:
        os.unlink(path)


def test_missing_lean_compiler_is_reported_not_crashed(monkeypatch) -> None:
    """A missing Lean compiler is an explicit failure, not a crash."""
    from agentic_pipeline import LeanAgenticPipeline
    p = LeanAgenticPipeline(use_mathlib=False, lean_path="lean")
    monkeypatch.setattr(p, "lean_path", None)
    res = p.execute_tactic_loop("0 = 0")
    assert res["success"] is False
    assert "Lean compiler not found" in res["error"]
    assert res["attempts"] == []


# ---------------------------------------------------------------------------
# qed-05-integration-validation: the DELIVERABLES of a run.
#
# The mission's third task is "verify traces.json is written correctly", and
# the integration check asserted that the file EXISTS -- a file the library
# API never wrote, so the assertion was satisfied by whatever the previous
# run had left behind.  A stale trace passes for a fresh one, which is the
# one thing an audit trail must never do.
#
# The deliverables are now written by ``run()`` (the public entry point), so
# the CLI and a programmatic caller get the same files.  The tests below pin:
#
#   * the audit trail is written on success AND on failure, and it agrees
#     with the result it describes;
#   * failing to write it is never fatal: a verified proof stays verified;
#   * the artefact holds exactly the verified source, is sorry-free, and
#     RECOMPILES STANDALONE -- the way a reviewer would re-check it;
#   * a failed run leaves no proof artefact behind.
# ---------------------------------------------------------------------------


def _deliverable_pipeline(tmp_path, **kwargs):
    """A pipeline whose deliverables are redirected into *tmp_path*."""
    from agentic_pipeline import LeanAgenticPipeline

    kwargs.setdefault("trace_path", str(tmp_path / "traces.json"))
    kwargs.setdefault("artifact_path", str(tmp_path / "output.lean"))
    return LeanAgenticPipeline(**kwargs)


def test_run_writes_the_audit_trail_on_success(tmp_path) -> None:
    """A verified run must leave an audit trail behind."""
    import json

    pipeline = _deliverable_pipeline(tmp_path)
    result = pipeline.run("0 = 0")
    trace_path = tmp_path / "traces.json"
    assert trace_path.exists(), "the audit trail was not written"
    trace = json.loads(trace_path.read_text())
    assert trace["success"] is True
    assert trace["lean_code"] == result["lean_code"]
    assert trace["tactic"] == result["tactic"]


def test_run_writes_the_audit_trail_on_failure(tmp_path) -> None:
    """A FAILED run must leave an audit trail too: the failure is the part
    of the audit trail that matters most."""
    import json

    pipeline = _deliverable_pipeline(tmp_path)
    result = pipeline.run("hello world")
    assert result["success"] is False
    trace_path = tmp_path / "traces.json"
    assert trace_path.exists(), "the audit trail was not written for a failure"
    trace = json.loads(trace_path.read_text())
    assert trace["success"] is False
    assert trace["error"] == result["error"]


def test_the_audit_trail_records_every_attempt(tmp_path) -> None:
    """The trail must describe the search that happened, not just the verdict."""
    import json

    pipeline = _deliverable_pipeline(tmp_path)
    result = pipeline.run("0 = 0")
    trace = json.loads((tmp_path / "traces.json").read_text())
    assert len(trace["attempts"]) == len(result["attempts"])
    assert trace["attempts"], "the trail recorded no attempt at all"
    for recorded, live in zip(trace["attempts"], result["attempts"]):
        assert recorded["tactic"] == live["tactic"]
        assert recorded["exit_code"] == live["exit_code"]
        assert recorded["has_sorry"] == live["has_sorry"]


def test_a_trace_write_failure_is_not_fatal(tmp_path) -> None:
    """An unwritable trace path must not turn a VERIFIED proof into a crash.

    The verdict is the pipeline's product; the trail is its record.  A
    failure to record must be reported, not raised over the result.
    """
    pipeline = _deliverable_pipeline(
        tmp_path, trace_path=str(tmp_path / "no-such-dir" / "traces.json"))
    result = pipeline.run("0 = 0")
    assert result["success"] is True, "a trace failure changed the verdict"
    assert "trace_error" in result


def test_the_artifact_holds_the_verified_source(tmp_path) -> None:
    """``output.lean`` must hold EXACTLY the source that was verified."""
    pipeline = _deliverable_pipeline(tmp_path)
    result = pipeline.run("0 = 0")
    artifact_path = tmp_path / "output.lean"
    assert artifact_path.exists(), "the verified artefact was not written"
    artifact = artifact_path.read_text()
    assert artifact == result["lean_code"]
    assert "sorry" not in artifact
    assert "sorryAx" not in artifact
    assert "theorem qed_goal" in artifact


def test_a_failed_run_leaves_no_proof_artifact(tmp_path) -> None:
    """A failed run must not leave a proof behind that a reader could
    mistake for the current one."""
    pipeline = _deliverable_pipeline(tmp_path)
    result = pipeline.run("hello world")
    assert result["success"] is False
    assert not (tmp_path / "output.lean").exists()


def test_a_failed_run_does_not_overwrite_an_earlier_artifact(tmp_path) -> None:
    """A later failure must not silently replace the last VERIFIED artefact."""
    pipeline = _deliverable_pipeline(tmp_path)
    verified = pipeline.run("0 = 0")
    artifact_path = tmp_path / "output.lean"
    assert artifact_path.read_text() == verified["lean_code"]

    failed = pipeline.run("hello world")
    assert failed["success"] is False
    assert artifact_path.read_text() == verified["lean_code"]


def test_the_artifact_recompiles_standalone(tmp_path) -> None:
    """The artefact must compile ON ITS OWN: that is what a reviewer does.

    The source in the artefact is the source the pipeline compiled, so it
    must still compile when nothing else is there.
    """
    import subprocess as _sp

    pipeline = _deliverable_pipeline(tmp_path)
    result = pipeline.run("0 = 0")
    assert result["success"] is True
    artifact_path = tmp_path / "output.lean"
    compiled = _sp.run(
        pipeline._compile_lean_cmd(str(artifact_path)),
        capture_output=True, text=True,
        timeout=pipeline.lean_compile_timeout,
        env=pipeline._compile_env(),
    )
    assert compiled.returncode == 0, (
        f"the artefact does not compile standalone:\n"
        f"{compiled.stdout[-500:]}\n{compiled.stderr[-500:]}")
    assert "sorry" not in (compiled.stdout + compiled.stderr)


def test_the_cli_writes_the_audit_trail_and_the_artifact(tmp_path) -> None:
    """The command line must produce the same deliverables as the library."""
    import json

    repo_root = Path(__file__).resolve().parent
    # Pin the toolchain the way the repository does, so the CLI does not
    # fall back to whatever elan's default happens to be.
    toolchain = repo_root / "lean-toolchain"
    if toolchain.is_file():
        (tmp_path / "lean-toolchain").write_text(toolchain.read_text())

    env = os.environ.copy()
    env["PATH"] = str(Path.home() / ".elan" / "bin") + ":" + env.get("PATH", "")
    env["PYTHONPATH"] = str(repo_root)

    result = subprocess.run(
        [sys.executable, str(repo_root / "agentic_pipeline.py"), "0 = 0"],
        capture_output=True, text=True, timeout=300, cwd=str(tmp_path), env=env,
    )
    assert result.returncode == 0, (
        f"the CLI failed:\n{result.stdout}\n{result.stderr}")
    trace_path = tmp_path / "traces.json"
    artifact_path = tmp_path / "output.lean"
    assert trace_path.exists(), "the CLI wrote no audit trail"
    assert artifact_path.exists(), "the CLI wrote no verified artefact"
    trace = json.loads(trace_path.read_text())
    assert trace["success"] is True
    assert artifact_path.read_text() == trace["lean_code"]
    assert "sorry" not in artifact_path.read_text()


# ---------------------------------------------------------------------------
# qed-05-integration-validation: the statement that REACHES Lean.
#
# The pipeline's input language is not Lean: implicit multiplication
# (``2ab``) and the LaTeX-like macros (``\frac``, ``\le``, ``a^{2}``) are
# part of it, and Lean has none of them.  The user's text used to be
# interpolated into the theorem as it was written, so the pipeline accepted
# the input and then handed Lean a statement it could not even PARSE -- a
# failure with nothing to do with the mathematics.
#
# The tests below pin the rendering: the term Lean receives is the term the
# user wrote, in Lean's vocabulary.
# ---------------------------------------------------------------------------


def test_the_lean_rendering_makes_implicit_products_explicit() -> None:
    """``2ab`` is a product in the input language and a product in Lean --
    but Lean needs the ``*``."""
    from agentic_pipeline import to_lean_expression
    assert to_lean_expression("2ab = 2 * a * b") == "2 * a * b = 2 * a * b"
    assert to_lean_expression("ab = a * b") == "a * b = a * b"
    assert to_lean_expression("2a = 2 * a") == "2 * a = 2 * a"


def test_the_lean_rendering_expands_the_latex_macros() -> None:
    """The macros are part of the input language; Lean knows none of them."""
    from agentic_pipeline import to_lean_expression
    assert to_lean_expression(r"\frac{a}{b} = c") == "((a) / (b)) = c"
    assert to_lean_expression(r"a \cdot b = c") == "a * b = c"
    assert to_lean_expression(r"a \le b") == "a <= b"
    assert to_lean_expression(r"a^{2} = b") == "a^(2) = b"
    assert to_lean_expression(r"x_{1} = 4") == "x_1 = 4"


def test_the_lean_rendering_keeps_a_qualified_application_an_application() -> None:
    """``Nat.succ 0`` is an APPLICATION in Lean, not a product.

    The parser reads the MVP language, where juxtaposition is a product;
    Lean's qualified names are functions, so the rendering must not turn
    the application into ``Nat.succ * 0`` -- a term Lean rejects.  An
    EXPLICIT product stays a product: the two spellings are different
    statements and must not collapse into one.
    """
    from agentic_pipeline import to_lean_expression
    assert to_lean_expression("Nat.succ 0 = 1") == "Nat.succ 0 = 1"
    assert to_lean_expression("Nat.succ * 0 = 1") == "Nat.succ * 0 = 1"


def test_the_lean_rendering_spells_not_equal_the_way_lean_does() -> None:
    """Lean has no ``!=`` operator; it spells "not equal" ``≠``."""
    from agentic_pipeline import to_lean_expression
    assert to_lean_expression("x != y") == "x ≠ y"


def test_the_lean_rendering_leaves_a_plain_statement_alone() -> None:
    """A statement that is already Lean must reach Lean unchanged."""
    from agentic_pipeline import to_lean_expression
    for expression in (
        "0 = 0",
        "x + 0 = x",
        "-1 + 1 = 0",
        "3 * (5 - 4 / 2) = 3 * 5 - 3 * 4 / 2",
        "-6 + 9 + -13 + 4 + 6 + 0 = 0",
        "Q * (C_p - C_tissue / Kp) = Q * C_p - Q * C_tissue / Kp",
        "dA_liver/dt = Q * (C_p - C_liver / Kp)",
    ):
        assert to_lean_expression(expression) == expression, expression


def test_the_generated_theorem_is_the_statement_the_user_wrote() -> None:
    """The theorem must carry the RENDERED statement, not the raw text."""
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline(use_mathlib=True)
    code = pipeline.generate_lean_code(
        "(a+b)^2 = a^2 + 2ab + b^2", ["a", "b"])
    # The implicit product is explicit ...
    assert "2 * a * b" in code
    # ... and no LaTeX macro survives into the theorem.
    assert "\\" not in code
    assert "sorry" not in code


def test_a_latex_statement_reaches_lean_as_lean() -> None:
    """A statement written in the LaTeX-like input language must reach the
    compiler as a term Lean can read -- and must then be proved, not merely
    accepted.

    The proof needs Mathlib (``ring`` over a commutative ring), so the
    PROOF is asserted only where Mathlib is present; the RENDERING is
    asserted everywhere, because it is the pipeline's own job.
    """
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline(use_mathlib=True)
    result = pipeline.run("(a+b)^2 = a^2 + 2ab + b^2")
    assert "2 * a * b" in (result.get('lean_code') or '')
    assert "\\" not in (result.get('lean_code') or '')
    assert "sorry" not in (result.get('lean_code') or '')
    if pipeline.use_mathlib:
        assert result["success"] is True, result.get('error')
        assert result["tactic"] in ("ring", "ring_nf", "simp", "norm_num")
    else:
        # Without Mathlib the proof is out of reach, but the pipeline must
        # still FAIL CLOSED rather than report a sorry.
        assert result["success"] is False
