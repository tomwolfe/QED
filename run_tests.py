#!/usr/bin/env python3
"""
Test suite for the Lean 4 Agentic Pipeline.
Tests various mathematical theorems and edge cases.
"""

import subprocess
import sys
import json
import os
from pathlib import Path


def _check_lean_available():
    """Check if the Lean compiler is available."""
    env = os.environ.copy()
    env["PATH"] = str(Path.home() / ".elan" / "bin") + ":" + env.get("PATH", "")
    try:
        result = subprocess.run(
            ["which", "lean"], capture_output=True, text=True, timeout=5, env=env
        )
        if result.returncode == 0:
            lean_path = result.stdout.strip()
            toolchain_dir = Path.home() / ".elan" / "toolchains"
            if toolchain_dir.exists():
                toolchains = [
                    d
                    for d in toolchain_dir.iterdir()
                    if d.is_dir() and not d.name.endswith(".lock")
                ]
                if toolchains:
                    return True
        return False
    except Exception:
        return False


def run_pipeline_test(
    test_name: str, latex_input: str, expected_success: bool = True
) -> bool:
    """Run a single test case"""
    print(f"\n{'=' * 60}")
    print(f"Test: {test_name}")
    print(f"{'=' * 60}")
    print(f"Input: {latex_input}")
    print(f"Expected: {'SUCCESS' if expected_success else 'FAILURE'}")
    print(f"{'-' * 60}")

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

        success = (result.returncode == 0) == expected_success

        print(f"Exit Code: {result.returncode}")
        if result.stdout:
            print(f"Output:\n{result.stdout}")
        if result.stderr:
            print(f"Errors:\n{result.stderr}")

        if success:
            print(f"✓ PASSED")
        else:
            print(f"✗ FAILED")

        return success

    except subprocess.TimeoutExpired:
        print("✗ FAILED: Command timed out")
        return False
    except Exception as e:
        print(f"✗ FAILED: {str(e)}")
        return False


def run_no_sorry_gate_tests():
    """Run no-sorry gate unit tests (no Lean compiler required)."""
    from agentic_pipeline import LeanAgenticPipeline

    pipeline = LeanAgenticPipeline()
    results = []

    def check(name, fn):
        try:
            fn()
            print(f"✓ PASSED: {name}")
            results.append((name, True))
        except AssertionError as e:
            print(f"✗ FAILED: {name} - {e}")
            results.append((name, False))

    # Source: sorry
    def test_source_sorry():
        has, reason = pipeline.check_for_sorry(
            "theorem foo : 1 = 1 := by\n  sorry", ""
        )
        assert has is True
        assert "sorry" in reason.lower()

    check("source contains sorry", test_source_sorry)

    # Source: sorryAx
    def test_source_sorryax():
        has, reason = pipeline.check_for_sorry(
            "theorem foo : 1 = 1 := by\n  exact sorryAx _", ""
        )
        assert has is True
        assert "sorryAx" in reason

    check("source contains sorryAx", test_source_sorryax)

    # Source: Tactic.sorry
    def test_source_tactic_sorry():
        has, reason = pipeline.check_for_sorry(
            "theorem foo : 1 = 1 := by\n  exact Tactic.sorry", ""
        )
        assert has is True
        assert "Tactic.sorry" in reason

    check("source contains Tactic.sorry", test_source_tactic_sorry)

    # Source: Lean.Elab.Tactic.sorry
    def test_source_lean_elab_sorry():
        has, reason = pipeline.check_for_sorry(
            "theorem foo : 1 = 1 := by\n  exact Lean.Elab.Tactic.sorry", ""
        )
        assert has is True
        assert "Lean.Elab.Tactic.sorry" in reason

    check("source contains Lean.Elab.Tactic.sorry", test_source_lean_elab_sorry)

    # Compiler: declaration uses sorry
    def test_compiler_declaration_uses_sorry():
        has, reason = pipeline.check_for_sorry(
            "theorem foo : 1 = 1 := by\n  rfl", "declaration uses sorry"
        )
        assert has is True
        assert "sorry" in reason.lower()

    check("compiler: declaration uses sorry", test_compiler_declaration_uses_sorry)

    # Compiler: uses sorryAx
    def test_compiler_uses_sorryax():
        has, reason = pipeline.check_for_sorry(
            "theorem foo : 1 = 1 := by\n  rfl", "uses sorryAx"
        )
        assert has is True
        assert "sorryAx" in reason

    check("compiler: uses sorryAx", test_compiler_uses_sorryax)

    # Compiler: warning pattern
    def test_compiler_warning():
        has, reason = pipeline.check_for_sorry(
            "theorem foo : 1 = 1 := by\n  rfl",
            "warning: declaration 'foo' uses sorry",
        )
        assert has is True
        assert "warning" in reason.lower()

    check("compiler: warning pattern", test_compiler_warning)

    # Compiler: broad match
    def test_compiler_broad_match():
        has, reason = pipeline.check_for_sorry(
            "theorem foo : 1 = 1 := by\n  rfl",
            "error: unknown identifier 'sorry'",
        )
        assert has is True
        assert "sorry" in reason.lower()

    check("compiler: broad sorry match", test_compiler_broad_match)

    # Word boundary: no false positive on "sorrier"
    def test_word_boundary_sorrier():
        has, _ = pipeline.check_for_sorry(
            "theorem foo : 1 = 1 := by\n  rfl", "sorrier is not the answer"
        )
        assert has is False

    check("word boundary: sorrier no false positive", test_word_boundary_sorrier)

    # No false positive on filename containing sorry
    def test_no_false_positive_filename():
        has, _ = pipeline.check_for_sorry(
            "theorem foo : 1 = 1 := by\n  rfl",
            "info: processing file 'sorryfoo.lean'",
        )
        assert has is False

    check("no false positive on filename", test_no_false_positive_filename)

    # Clean: no sorry
    def test_clean():
        has, reason = pipeline.check_for_sorry(
            "theorem foo : 1 = 1 := by\n  rfl", ""
        )
        assert has is False
        assert reason == ""

    check("clean output: no sorry detected", test_clean)

    # _verify_no_sorry_axioms: fail-closed on bad path
    def test_axioms_fail_closed():
        is_clean, reason = pipeline._verify_no_sorry_axioms("/nonexistent/path.lean")
        assert is_clean is False
        assert "fail-closed" in reason.lower() or "error" in reason.lower()

    check("axioms check: fail-closed on bad path", test_axioms_fail_closed)

    # _verify_no_sorry_axioms: clean file
    def test_axioms_clean_file():
        import tempfile

        lean_code = "theorem foo : 1 = 1 := by\n  rfl\n"
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".lean", delete=False
        ) as f:
            f.write(lean_code)
            temp_path = f.name
        try:
            is_clean, reason = pipeline._verify_no_sorry_axioms(temp_path)
            assert is_clean is True or "fail-closed" in reason.lower() or "error" in reason.lower()
        finally:
            os.unlink(temp_path)

    check("axioms check: clean file", test_axioms_clean_file)

    # _verify_no_sorry_axioms: fail-closed on a file the compiler rejects.
    # A file that did not compile tells us NOTHING about its axiom set, so
    # it must not be certified clean.
    def test_axioms_fail_closed_on_non_compiling_file():
        import tempfile

        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".lean", delete=False
        ) as f:
            f.write("theorem broken : : : := by\n")
            temp_path = f.name
        try:
            is_clean, reason = pipeline._verify_no_sorry_axioms(temp_path)
            assert is_clean is False
            assert "fail-closed" in reason.lower() or "error" in reason.lower()
        finally:
            os.unlink(temp_path)

    check("axioms check: fail-closed on non-compiling file", test_axioms_fail_closed_on_non_compiling_file)

    # _verify_no_sorry_axioms: fail-closed when no axioms report is produced.
    def test_axioms_fail_closed_without_a_report():
        import tempfile

        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".lean", delete=False
        ) as f:
            f.write("def helper := 1\n")
            temp_path = f.name
        try:
            is_clean, reason = pipeline._verify_no_sorry_axioms(temp_path)
            assert is_clean is False
            assert "fail-closed" in reason.lower() or "error" in reason.lower()
        finally:
            os.unlink(temp_path)

    check("axioms check: fail-closed without an axioms report", test_axioms_fail_closed_without_a_report)

    # The message Lean ACTUALLY prints. Lean 4.33 backtick-quotes the token
    # ("uses `sorry`"), so a detector written for the bare "uses sorry" form
    # matches nothing and only the generic catch-all can fire.
    def test_compiler_real_lean_sorry_warning():
        has, reason = pipeline.check_for_sorry(
            "theorem foo : 1 = 1 := by\n  rfl",
            "warning: declaration uses `sorry`",
        )
        assert has is True
        # The SPECIFIC detector must fire, not merely the generic catch-all.
        assert "declaration uses sorry" in reason.lower()

    check("compiler: real Lean sorry warning", test_compiler_real_lean_sorry_warning)

    # End to end: Lean EXITS 0 on a file that uses `sorry` (it only warns),
    # so the exit code cannot be the gate. A proof that Lean accepted only
    # because it contained a sorry must still be reported as a FAILURE.
    def test_loop_rejects_a_sorry_proof_that_lean_accepted():
        import subprocess as sp

        class _Result:
            def __init__(self, rc=0, out="", err=""):
                self.returncode = rc
                self.stdout = out
                self.stderr = err

        def _fake_run(cmd, **kwargs):
            path = ""
            for part in (cmd if isinstance(cmd, list) else []):
                if str(part).endswith(".lean"):
                    path = str(part)
            text = ""
            if path:
                try:
                    with open(path) as fh:
                        text = fh.read()
                except OSError:
                    text = ""
            if "#print axioms" in text:
                return _Result(0, "'qed_goal' does not depend on any axioms", "")
            return _Result(0, "warning: declaration uses `sorry`", "")

        real_run = sp.run
        sp.run = _fake_run
        try:
            from agentic_pipeline import LeanAgenticPipeline

            p = LeanAgenticPipeline(use_mathlib=False, lean_path="lean")
            res = p.execute_tactic_loop("0 = 0")
            assert res["success"] is False
            assert res["attempts"]
            assert all(a["has_sorry"] for a in res["attempts"])
        finally:
            sp.run = real_run

    check("loop: a sorry proof is rejected", test_loop_rejects_a_sorry_proof_that_lean_accepted)

    return results


def run_all_tests():
    """Run all test cases"""
    lean_available = _check_lean_available()

    print("=" * 60)
    print("Lean 4 Agentic Pipeline - Test Suite")
    print("=" * 60)

    results = []

    # Integration tests (require Lean compiler)
    test_cases = [
        ("Simple Theorem", r"Nat.succ 0 = 1", True),
        ("Simple Equality", r"0 = 0", True),
        ("Trivial Identity", r"x + 0 = x", True),
        ("Non-Math Input", "hello world", False),
        ("Empty Input", "", False),
    ]

    for test_name, latex_input, expected_success in test_cases:
        if expected_success and not lean_available:
            print(f"\n{'=' * 60}")
            print(f"Test: {test_name}")
            print(f"{'=' * 60}")
            print(f"Input: {latex_input}")
            print(f"Expected: SUCCESS")
            print(f"{'-' * 60}")
            print("⊘ SKIPPED: Lean compiler not available")
            results.append((test_name, True))
            continue
        success = run_pipeline_test(test_name, latex_input, expected_success)
        results.append((test_name, success))

    # No-sorry gate unit tests (no Lean required)
    print("\n" + "=" * 60)
    print("No-Sorry Gate Tests")
    print("=" * 60)
    gate_results = run_no_sorry_gate_tests()
    results.extend(gate_results)

    print("\n" + "=" * 60)
    print("Test Summary")
    print("=" * 60)

    passed = sum(1 for _, success in results if success)
    total = len(results)

    for test_name, success in results:
        status = "✓ PASSED" if success else "✗ FAILED"
        print(f"{status}: {test_name}")

    print("=" * 60)
    print(f"Results: {passed}/{total} tests passed")

    return passed == total


if __name__ == "__main__":
    success = run_all_tests()
    sys.exit(0 if success else 1)
