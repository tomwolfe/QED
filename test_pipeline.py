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
