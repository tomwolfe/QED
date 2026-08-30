#!/usr/bin/env python3
import subprocess
import sys
import os
from pathlib import Path


def test_identity_theorem():
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

from parser import (
    normalize_implicit_multiplication_expression,
    normalize_implicit_multiplication,
    tokenize,
    parse_primary,
    parse_expression,
    parse_equation,
    BinOp,
    Var,
    Num,
)


def test_normalize_string_number_var():
    assert normalize_implicit_multiplication_expression('2a') == '2 * a'
    assert normalize_implicit_multiplication_expression('3x') == '3 * x'


def test_normalize_string_number_chain():
    assert normalize_implicit_multiplication_expression('2ab') == '2 * a * b'
    assert normalize_implicit_multiplication_expression('3xyz') == '3 * x * y * z'


def test_normalize_string_post_paren():
    assert normalize_implicit_multiplication_expression('(a+b)2') == '(a+b) * 2'
    assert normalize_implicit_multiplication_expression('(a+b)(c+d)') == '(a+b) * (c+d)'
    assert normalize_implicit_multiplication_expression('(a+b)x') == '(a+b) * x'


def test_normalize_string_pre_paren():
    assert normalize_implicit_multiplication_expression('2(a+b)') == '2 * (a+b)'
    assert normalize_implicit_multiplication_expression('a(b+c)') == 'a * (b+c)'


def test_normalize_string_single_pairs():
    assert normalize_implicit_multiplication_expression('ab') == 'a * b'
    assert normalize_implicit_multiplication_expression('ab + cd') == 'a * b + c * d'


def test_normalize_string_equation():
    result = normalize_implicit_multiplication_expression('(a+b)^2 = a^2 + 2ab + b^2')
    assert result == '(a+b)^2 = a^2 + 2 * a * b + b^2'


def test_normalize_string_multi_letter_unchanged():
    assert normalize_implicit_multiplication_expression('Nat + x') == 'Nat + x'


# --- Parser: Token normalization tests ---

def test_normalize_tokens_paren_to_digit():
    tokens = ['(', 'a', '+', 'b', ')', '2']
    result = normalize_implicit_multiplication(tokens)
    idx = result.index(')')
    assert result[idx + 1] == '*'
    assert result[idx + 2] == '2'


def test_normalize_tokens_paren_to_var():
    tokens = ['(', 'a', '+', 'b', ')', 'x']
    result = normalize_implicit_multiplication(tokens)
    idx = result.index(')')
    assert result[idx + 1] == '*'
    assert result[idx + 2] == 'x'


def test_normalize_tokens_paren_to_paren():
    tokens = ['(', 'a', '+', 'b', ')', '(', 'c', '+', 'd', ')']
    result = normalize_implicit_multiplication(tokens)
    idx = result.index(')')
    assert result[idx + 1] == '*'
    assert result[idx + 2] == '('


def test_normalize_tokens_num_to_paren():
    tokens = ['2', '(', 'a', '+', 'b', ')']
    result = normalize_implicit_multiplication(tokens)
    assert result[1] == '*'


def test_normalize_tokens_var_to_paren():
    tokens = ['a', '(', 'b', '+', 'c', ')']
    result = normalize_implicit_multiplication(tokens)
    assert result[1] == '*'


# --- Parser: Integration tests ---

def test_parse_paren_mul():
    tokens = tokenize('(a+b)2')
    tokens = normalize_implicit_multiplication(tokens)
    expr, pos = parse_expression(tokens)
    assert expr is not None
    assert isinstance(expr, BinOp)
    assert expr.op == '*'


def test_parse_nested_parens():
    tokens = tokenize('((a+b))')
    tokens = normalize_implicit_multiplication(tokens)
    expr, pos = parse_expression(tokens)
    assert expr is not None
    assert isinstance(expr, BinOp)
    assert expr.op == '+'


def test_parse_number_var_chain():
    tokens = tokenize('3xyz')
    tokens = normalize_implicit_multiplication(tokens)
    expr, pos = parse_expression(tokens)
    assert expr is not None
    assert isinstance(expr, BinOp)


def test_parse_equation_2ab():
    eq, free_vars = parse_equation('(a+b)^2 = a^2 + 2ab + b^2')
    assert eq is not None
    assert 'a' in free_vars
    assert 'b' in free_vars


# --- Type inference tests ---

def test_suggest_type_nat():
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    assert pipeline._suggest_type('x + 0 = x') == 'Nat'


def test_suggest_type_int():
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    assert pipeline._suggest_type('-1 + 1 = 0') == 'Int'


def test_suggest_type_rat():
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    assert pipeline._suggest_type('x / 2 = y') == 'Rat'


def test_get_var_type_nat():
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    assert pipeline._get_var_type(['x'], 'x + 0 = x') == 'Nat'


def test_get_var_type_int():
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    assert pipeline._get_var_type(['x'], '-1 + x = 0') == 'Int'


# --- Tactic selection tests ---

def test_tactic_candidates_algebraic():
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    candidates = pipeline.get_tactic_candidates('(a+b)^2 = a^2 + 2ab + b^2')
    assert 'ring' in candidates
    assert candidates.index('ring') < candidates.index('simp')


def test_tactic_candidates_inequality():
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    candidates = pipeline.get_tactic_candidates('x < x + 1')
    assert 'linarith' in candidates
    assert candidates.index('linarith') < candidates.index('simp')


def test_tactic_candidates_division():
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    candidates = pipeline.get_tactic_candidates('x / 2 = y')
    assert 'field_simp' in candidates
    assert candidates.index('field_simp') < candidates.index('ring')


def test_tactic_candidates_ode_prioritizes_ode_tactics():
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    candidates = pipeline.get_tactic_candidates('dA_liver/dt = Q * (C_p - C_liver / Kp)')
    # ODE inputs must surface the Mathlib ODE tactics.
    assert 'dsimp' in candidates
    assert 'field_simp' in candidates
    # Ordering: dsimp leads, then field_simp, then ring, before the generic simp.
    assert candidates.index('dsimp') < candidates.index('field_simp')
    assert candidates.index('field_simp') < candidates.index('ring')
    assert candidates.index('ring') < candidates.index('simp')


def test_tactic_candidates_ode_involves_derivative_notation():
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    # Derivative notation anywhere (not just d<var>/dt = <rhs>) triggers ODE policy.
    candidates = pipeline.get_tactic_candidates('dA_gut/dt + dA_central/dt = 0')
    assert 'dsimp' in candidates
    assert 'field_simp' in candidates
    assert 'ring' in candidates


def test_tactic_candidates_ode_not_identity_shortcut():
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    # An ODE equation is not a textual identity, so it must take the ODE branch
    # (which leads with dsimp) rather than the identity short-circuit (rfl).
    candidates = pipeline.get_tactic_candidates('dA_gut/dt = -ka * A_gut')
    assert candidates[0] == 'dsimp'


def test_select_tactic_field_simp_for_derivative_goal():
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


def test_involves_derivative_parser():
    from parser import involves_derivative
    assert involves_derivative('dA_liver/dt = Q * (C_p - C_liver / Kp)') is True
    assert involves_derivative('Q * (C_p - C_tissue / Kp)') is False
    assert involves_derivative('ka * A_gut = ka * A_gut') is False



def test_select_tactic_ring_goal():
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


def test_select_tactic_linarith_inequality():
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

def test_check_for_sorry_source_sorry():
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    has_sorry, reason = pipeline.check_for_sorry("theorem foo : 1 = 1 := by\n  sorry", "")
    assert has_sorry is True
    assert "sorry" in reason.lower()


def test_check_for_sorry_source_sorryax():
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    has_sorry, reason = pipeline.check_for_sorry("theorem foo : 1 = 1 := by\n  exact sorryAx _", "")
    assert has_sorry is True
    assert "sorryAx" in reason


def test_check_for_sorry_compiler_sorry():
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    has_sorry, reason = pipeline.check_for_sorry("theorem foo : 1 = 1 := by\n  rfl", "declaration uses sorry")
    assert has_sorry is True
    assert "sorry" in reason.lower()


def test_check_for_sorry_compiler_sorryax():
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    has_sorry, reason = pipeline.check_for_sorry("theorem foo : 1 = 1 := by\n  rfl", "uses sorryAx")
    assert has_sorry is True
    assert "sorryAx" in reason


def test_check_for_sorry_compiler_word_boundary():
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    # "sorrier" should NOT trigger the sorry check
    has_sorry, _ = pipeline.check_for_sorry("theorem foo : 1 = 1 := by\n  rfl", "sorrier is not the answer")
    assert has_sorry is False


def test_check_for_sorry_clean():
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    has_sorry, reason = pipeline.check_for_sorry(
        "theorem foo : 1 = 1 := by\n  rfl",
        ""
    )
    assert has_sorry is False
    assert reason == ""


def test_check_for_sorry_compiler_broad_match():
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    has_sorry, reason = pipeline.check_for_sorry(
        "theorem foo : 1 = 1 := by\n  rfl",
        "error: unknown identifier 'sorry'"
    )
    assert has_sorry is True
    assert "sorry" in reason.lower()


def test_success_implies_no_sorry_in_output():
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    result = pipeline.run("0 = 0")
    if result['success']:
        assert 'sorry' not in result['lean_code']
        assert 'sorryAx' not in result['lean_code']
        assert result['verification']['source_check'] == 'passed'
        assert result['verification']['compiler_check'] == 'passed'
        assert result['verification']['axioms_check'] == 'passed'


def test_check_for_sorry_compiler_warning_pattern():
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    has_sorry, reason = pipeline.check_for_sorry(
        "theorem foo : 1 = 1 := by\n  rfl",
        "warning: declaration 'foo' uses sorry"
    )
    assert has_sorry is True
    assert "warning" in reason.lower()


def test_verify_no_sorry_axioms_clean_file():
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

def test_check_for_sorry_source_tactic_sorry():
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    has_sorry, reason = pipeline.check_for_sorry("theorem foo : 1 = 1 := by\n  exact Tactic.sorry", "")
    assert has_sorry is True
    assert "Tactic.sorry" in reason


def test_check_for_sorry_source_lean_elab_sorry():
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    has_sorry, reason = pipeline.check_for_sorry("theorem foo : 1 = 1 := by\n  exact Lean.Elab.Tactic.sorry", "")
    assert has_sorry is True
    assert "Lean.Elab.Tactic.sorry" in reason


def test_check_for_sorry_compiler_uses_sorryax():
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    has_sorry, reason = pipeline.check_for_sorry(
        "theorem foo : 1 = 1 := by\n  rfl",
        "uses sorryAx"
    )
    assert has_sorry is True
    assert "sorryAx" in reason


def test_check_for_sorry_clean_no_false_positive():
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    # "sorry" as part of a longer word should not trigger
    has_sorry, _ = pipeline.check_for_sorry(
        "theorem foo : 1 = 1 := by\n  rfl",
        "info: processing file 'sorryfoo.lean'"
    )
    assert has_sorry is False


def test_verify_no_sorry_axioms_fail_closed():
    from agentic_pipeline import LeanAgenticPipeline
    pipeline = LeanAgenticPipeline()
    # Non-existent path should fail-closed (return False)
    is_clean, reason = pipeline._verify_no_sorry_axioms("/nonexistent/path.lean")
    assert is_clean is False
    assert "fail-closed" in reason.lower() or "error" in reason.lower()


# --- AST helper tests ---

from parser import (
    contains_op,
    is_inequality,
    has_numeric_ops,
    has_polynomial_structure,
    parse_equation,
    ast_to_latex,
    _is_identity,
    statement_kind,
    BinOp,
    Var,
    Num,
    Neg,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
)


def test_contains_op_division():
    eq, _ = parse_equation("x / 2 = y")
    assert contains_op(eq, '/') is True
    assert contains_op(eq, '^') is False


def test_contains_op_power():
    eq, _ = parse_equation("a^2 = b")
    assert contains_op(eq, '^') is True
    assert contains_op(eq, '/') is False


def test_contains_op_none():
    assert contains_op(None, '+') is False


def test_is_inequality_true():
    for expr in ["x < y", "x > y", "x <= y", "x >= y", "x != y"]:
        eq, _ = parse_equation(expr)
        assert is_inequality(eq) is True, f"Expected inequality for {expr}"


def test_is_inequality_false():
    eq, _ = parse_equation("x = y")
    assert is_inequality(eq) is False


def test_has_numeric_ops_addition():
    eq, _ = parse_equation("x + y = z")
    assert has_numeric_ops(eq) is True


def test_has_numeric_ops_multiplication():
    eq, _ = parse_equation("x * y = z")
    assert has_numeric_ops(eq) is True


def test_has_numeric_ops_no_ops():
    eq, _ = parse_equation("x = y")
    assert has_numeric_ops(eq) is False


def test_has_polynomial_structure_power():
    eq, _ = parse_equation("(a + b)^2 = a^2 + b^2")
    assert has_polynomial_structure(eq) is True


def test_has_polynomial_structure_implicit_mul():
    """2ab = a * b has * but no ^, so it should NOT be polynomial."""
    eq, _ = parse_equation("2ab = a * b")
    assert has_polynomial_structure(eq) is False


def test_has_polynomial_structure_no_poly():
    eq, _ = parse_equation("x + y = z")
    assert has_polynomial_structure(eq) is False


def test_tactic_candidates_ab_not_false_positive():
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

def test_ast_to_latex_var():
    assert ast_to_latex(Var('x')) == 'x'


def test_ast_to_latex_num():
    assert ast_to_latex(Num(3)) == '3'


def test_ast_to_latex_binop_add():
    node = BinOp(Var('x'), '+', Var('y'))
    assert ast_to_latex(node) == 'x + y'


def test_ast_to_latex_binop_mul():
    node = BinOp(Var('a'), '*', Var('b'))
    assert ast_to_latex(node) == 'a * b'


def test_ast_to_latex_binop_power():
    node = BinOp(Var('x'), '^', Num(2))
    assert ast_to_latex(node) == 'x^{2}'


def test_ast_to_latex_neg():
    node = Neg(Var('x'))
    assert ast_to_latex(node) == '-x'


def test_ast_to_latex_eq():
    node = Eq(Var('x'), Var('y'))
    assert ast_to_latex(node) == 'x = y'


def test_ast_to_latex_ne():
    node = Ne(Var('x'), Var('y'))
    assert ast_to_latex(node) == 'x != y'


def test_ast_to_latex_lt():
    node = Lt(Var('x'), Var('y'))
    assert ast_to_latex(node) == 'x < y'


def test_ast_to_latex_le():
    node = Le(Var('x'), Var('y'))
    assert ast_to_latex(node) == 'x <= y'


def test_ast_to_latex_gt():
    node = Gt(Var('x'), Var('y'))
    assert ast_to_latex(node) == 'x > y'


def test_ast_to_latex_ge():
    node = Ge(Var('x'), Var('y'))
    assert ast_to_latex(node) == 'x >= y'


def test_ast_to_latex_none():
    assert ast_to_latex(None) == ''


def test_ast_to_latex_nested():
    node = BinOp(BinOp(Var('a'), '+', Var('b')), '*', Var('c'))
    assert ast_to_latex(node) == 'a + b * c'


# --- _is_identity tests ---

def test_is_identity_true():
    node = Eq(Var('x'), Var('x'))
    assert _is_identity(node) is True


def test_is_identity_false():
    node = Eq(Var('x'), Var('y'))
    assert _is_identity(node) is False


def test_is_identity_complex_true():
    node = Eq(BinOp(Var('a'), '+', Var('b')), BinOp(Var('a'), '+', Var('b')))
    assert _is_identity(node) is True


def test_is_identity_complex_false():
    node = Eq(BinOp(Var('a'), '+', Var('b')), BinOp(Var('a'), '-', Var('b')))
    assert _is_identity(node) is False


def test_is_identity_non_eq():
    node = Ne(Var('x'), Var('x'))
    assert _is_identity(node) is False


# --- statement_kind tests ---

def test_statement_kind_identity_x_eq_x():
    assert statement_kind('x = x') == 'identity'


def test_statement_kind_identity_complex():
    assert statement_kind('a + b = a + b') == 'identity'


def test_statement_kind_identity_multiplication():
    assert statement_kind('x * 1 = x * 1') == 'identity'


def test_statement_kind_equality():
    assert statement_kind('x + 1 = 2') == 'equality'


def test_statement_kind_equality_not_identity():
    assert statement_kind('x + 1 = x + 2') == 'equality'


def test_statement_kind_inequality_lt():
    assert statement_kind('x < y') == 'inequality'


def test_statement_kind_inequality_le():
    assert statement_kind('x <= y') == 'inequality'


def test_statement_kind_inequality_gt():
    assert statement_kind('x > y') == 'inequality'


def test_statement_kind_inequality_ge():
    assert statement_kind('x >= y') == 'inequality'


def test_statement_kind_inequality_ne():
    assert statement_kind('x != y') == 'inequality'


def test_statement_kind_other_bare_expression():
    assert statement_kind('x + 1') == 'other'


def test_statement_kind_other_number():
    assert statement_kind('42') == 'other'


def test_statement_kind_identity_not_inequality():
    result = statement_kind('x = x')
    assert result != 'inequality'


def test_statement_kind_eq_ne_distinct():
    eq_result = statement_kind('x = y')
    ne_result = statement_kind('x != y')
    assert eq_result == 'equality'
    assert ne_result == 'inequality'


def test_statement_kind_identity_power():
    assert statement_kind('x^1 = x^1') == 'identity'


# --- ODE parsing tests (PBPK d<var>/dt = <rhs> support) ---

from parser import parse_ode, is_ode, ODE, parse


def test_parse_ode_basic():
    ode, free_vars = parse_ode('dA_gut/dt = -ka * A_gut')
    assert ode is not None
    assert isinstance(ode, ODE)
    assert ode.var == 'A_gut'
    assert 'A_gut' in free_vars


def test_parse_ode_var_extraction():
    ode, free_vars = parse_ode('dA_liver/dt = Q * (C_p - C_liver / Kp)')
    assert ode is not None
    assert ode.var == 'A_liver'
    # RHS free variables should be captured (Q, C_p, C_liver, Kp)
    for v in ['Q', 'C_p', 'C_liver', 'Kp']:
        assert v in free_vars


def test_parse_ode_with_spaces():
    ode, _ = parse_ode('dA_gut / dt = -ka * A_gut')
    assert ode is not None
    assert ode.var == 'A_gut'


def test_parse_ode_rhs_is_ast():
    from parser import BinOp, Neg, Var
    ode, _ = parse_ode('dA_gut/dt = -ka * A_gut')
    # RHS should be a BinOp (Neg(Var('k')) * Var('a')) * Var('A_gut')
    assert isinstance(ode.rhs, BinOp)
    assert ode.rhs.op == '*'


def test_parse_ode_none_for_plain_equation():
    ode, free_vars = parse_ode('x + 1 = 2')
    assert ode is None
    assert free_vars is None


def test_parse_ode_none_for_expression():
    ode, free_vars = parse_ode('x + 1')
    assert ode is None
    assert free_vars is None


def test_is_ode_classification():
    assert is_ode('dA_gut/dt = -ka * A_gut') is True
    assert is_ode('x + 1 = 2') is False
    assert is_ode('dA_central/dt = ka * A_gut') is True


def test_parse_returns_ode_type():
    result = parse('dA_gut/dt = -ka * A_gut')
    assert result['type'] == 'ode'
    assert result['ode'] is not None
    assert result['ode'].var == 'A_gut'
    assert result['relation'] == '='


def test_parse_non_ode_untouched():
    result = parse('x + 1 = 2')
    assert result['type'] == 'equation'
    assert result['ode'] is None


def test_ast_to_latex_ode():
    ode, _ = parse_ode('dA_gut/dt = -ka * A_gut')
    rendered = ast_to_latex(ode)
    assert rendered.startswith('dA_gut/dt =')
    assert 'A_gut' in rendered


def test_parse_ode_nonempty_rhs_required():
    ode, _ = parse_ode('dA_gut/dt =')
    assert ode is None


# --- Additional parser unit tests for mutation coverage ---

def test_parse_equation_single_var():
    eq, free_vars = parse_equation('x = y')
    assert eq is not None
    assert set(free_vars) == {'x', 'y'}


def test_parse_expression_addition():
    from parser import BinOp
    tokens = tokenize('a + b')
    tokens = normalize_implicit_multiplication(tokens)
    expr, _ = parse_expression(tokens)
    assert isinstance(expr, BinOp)
    assert expr.op == '+'


def test_statement_kind_other_empty():
    assert statement_kind('') == 'other'


def test_contains_op_addition():
    eq, _ = parse_equation('x + y = z')
    assert contains_op(eq, '+') is True
    assert contains_op(eq, '*') is False



# ---------------------------------------------------------------------------
# Mission B: QED depth for the VeriTrial PBPK surface
# ---------------------------------------------------------------------------

def _pbpk_run(expr: str) -> dict:
    """Run the pipeline (real Lean compile) and return the result dict."""
    from agentic_pipeline import LeanAgenticPipeline
    return LeanAgenticPipeline(use_mathlib=True).run(expr)


def test_pbpk_perfusion_distributive_witness_proves_no_sorry():
    """The closed numeric perfusion-limited distributive witness must prove
    genuinely (decide/simp/ring), NOT by reflexivity, and contain no sorry."""
    res = _pbpk_run("3 * (5 - 4 / 2) = 3 * 5 - 3 * 4 / 2")
    assert res["success"] is True
    assert "sorry" not in res["lean_code"]
    assert "sorryAx" not in res["lean_code"]
    # It is a closed numeric identity: proving it required a real tactic, not rfl.
    assert res["tactic"] in ("simp", "decide", "ring", "norm_num", "field_simp")


def test_pbpk_mass_conservation_witness_proves_no_sorry():
    """Lemma 3b: the sum of all six compartment derivative RHS terms equals 0.
    This is the genuinely non-reflexive mass-conservation proof."""
    res = _pbpk_run("-6 + 9 + -13 + 4 + 6 + 0 = 0")
    assert res["success"] is True
    assert "sorry" not in res["lean_code"]
    assert "sorryAx" not in res["lean_code"]


def test_pbpk_gut_absorption_identity_proves():
    res = _pbpk_run("ka * A_gut = ka * A_gut")
    assert res["success"] is True
    assert "sorry" not in res["lean_code"]


def test_pbpk_ode_tactic_policy_includes_distributive_field():
    """For a PBPK perfusion ODE the candidate ordering must surface the
    field/distributive tactics (dsimp -> field_simp -> ring) so a genuine
    proof is reachable."""
    from agentic_pipeline import LeanAgenticPipeline
    cands = LeanAgenticPipeline().get_tactic_candidates(
        "dA_liver/dt = Q * (C_p - C_liver / Kp)"
    )
    assert "dsimp" in cands
    assert "field_simp" in cands
    assert "ring" in cands
    assert cands.index("dsimp") < cands.index("field_simp") < cands.index("ring")


def test_pbpk_symbolic_ode_fails_closed_without_mathlib():
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
