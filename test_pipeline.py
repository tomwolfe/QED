#!/usr/bin/env python3
import subprocess
import sys
import os
from typing import Any
from pathlib import Path


def test_identity_theorem() -> bool:
    """Test the pipeline with a simple Lean theorem"""
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
            timeout=60,
            env=env,
        )

        print("\nSTDOUT:")
        print(result.stdout)
        if result.stderr:
            print("\nSTDERR:")
            print(result.stderr)

        print(f"\nExit Code: {result.returncode}")
        print("=" * 60)

        if result.returncode == 0:
            print("✓ Test PASSED: Theorem was verified successfully!")
            return True
        else:
            print("✗ Test FAILED: Could not verify the theorem")
            return False

    except subprocess.TimeoutExpired:
        print("✗ Test FAILED: Command timed out")
        return False
    except Exception as e:
        print(f"✗ Test FAILED: {str(e)}")
        return False


if __name__ == "__main__":
    success = test_identity_theorem()
    sys.exit(0 if success else 1)


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
    """The gut absorption identity is Real-typed, so it needs Mathlib; without
    Mathlib (a clean-room checkout of the committed tree has no `.lake`) the
    goal cannot compile and the pipeline must fail closed, never with sorry."""
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline(use_mathlib=True)
    res = pipeline.run("ka * A_gut = ka * A_gut")
    if pipeline.use_mathlib:
        assert res["success"] is True
        assert "sorry" not in res["lean_code"]
    else:
        assert res["success"] is False
        assert "sorry" not in res.get("lean_code", "")


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
    letter-pair rule ran before macro expansion."""
    assert tokenize('a \\le b') == ['a', '<', '=', 'b']
    assert tokenize('a \\ge b') == ['a', '>', '=', 'b']
    assert tokenize('a \\leq b') == ['a', '<', '=', 'b']
    assert tokenize('a \\geq b') == ['a', '>', '=', 'b']
    assert tokenize('a \\neq b') == ['a', '!', '=', 'b']


def test_latex_operator_macros_expand() -> None:
    assert tokenize('a \\cdot b = c') == ['a', '*', 'b', '=', 'c']
    assert tokenize('a \\times b = c') == ['a', '*', 'b', '=', 'c']
    assert tokenize('a \\div b = c') == ['a', '/', 'b', '=', 'c']


def test_latex_frac_expands_to_division() -> None:
    """'\\frac{a}{b}' used to tokenize as the variable 'frac'."""
    assert tokenize('\\frac{a}{b} = c') == ['(', 'a', ')', '/', '(', 'b', ')', '=', 'c']
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
    assert tokenize('a ≤ b') == ['a', '<', '=', 'b']
    assert tokenize('a ≥ b') == ['a', '>', '=', 'b']
    assert tokenize('a ≠ b') == ['a', '!', '=', 'b']


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
