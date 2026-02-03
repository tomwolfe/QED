#!/usr/bin/env python3
"""
Test suite for the Lean 4 Agentic Pipeline.
Tests various mathematical theorems and edge cases.
"""

import subprocess
import sys
import json
from pathlib import Path


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


def run_all_tests():
    """Run all test cases"""
    print("=" * 60)
    print("Lean 4 Agentic Pipeline - Test Suite")
    print("=" * 60)

    test_cases = [
        ("Simple Theorem", r"Nat.succ 0 = 1", True),
        ("Simple Equality", r"0 = 0", True),
        ("Trivial Identity", r"x + 0 = x", True),
        ("Non-Math Input", "hello world", False),
        ("Empty Input", "", False),
    ]

    results = []
    for test_name, latex_input, expected_success in test_cases:
        success = run_pipeline_test(test_name, latex_input, expected_success)
        results.append((test_name, success))

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
    import os

    success = run_all_tests()
    sys.exit(0 if success else 1)
