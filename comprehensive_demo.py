#!/usr/bin/env python3
"""
Comprehensive demonstration of the Lean 4 Agentic Pipeline capabilities.
This script shows the full workflow from input to successful verification.
"""

import subprocess
import sys
import os
from pathlib import Path


def run_test(description, latex_input, expected_success=True):
    """Run a single test case and report results"""
    print(f"\n{'=' * 70}")
    print(f"Test: {description}")
    print(f"{'=' * 70}")
    print(f"Input: {latex_input}")
    print(f"Expected: {'SUCCESS' if expected_success else 'FAILURE'}")
    print("-" * 70)

    env = os.environ.copy()
    env["PATH"] = str(Path.home() / ".elan" / "bin") + ":" + env.get("PATH", "")

    result = subprocess.run(
        ["python3", "agentic_pipeline.py", latex_input],
        capture_output=True,
        text=True,
        timeout=60,
        env=env,
    )

    print(f"Exit Code: {result.returncode}")
    if result.stdout:
        print("Output:")
        print(result.stdout)
    if result.stderr:
        print("Errors:")
        print(result.stderr)

    success = (result.returncode == 0) == expected_success

    if success:
        print(f"✓ PASSED")
    else:
        print(f"✗ FAILED")

    return success


def main():
    """Run comprehensive tests"""
    print("=" * 70)
    print("LEAN 4 AGENTIC PIPELINE - COMPREHENSIVE DEMONSTRATION")
    print("=" * 70)

    test_cases = [
        ("Simple Theorem", "Nat.succ 0 = 1", True),
        ("Simple Equality", "0 = 0", True),
        ("Trivial Identity", "x + 0 = x", True),
        ("Zero Addition", "0 + x = x", True),
        ("Negative Number", "-1 + 1 = 0", True),
        ("Non-Math Input", "hello world", False),
        ("Empty Input", "", False),
    ]

    results = []
    for test_name, latex_input, expected_success in test_cases:
        success = run_test(test_name, latex_input, expected_success)
        results.append((test_name, success))

    print("\n" + "=" * 70)
    print("TEST SUMMARY")
    print("=" * 70)

    passed = sum(1 for _, success in results if success)
    total = len(results)

    for test_name, success in results:
        status = "✓ PASSED" if success else "✗ FAILED"
        print(f"{status}: {test_name}")

    print("=" * 70)
    print(f"Results: {passed}/{total} tests passed")

    if passed == total:
        print("✓ ALL TESTS PASSED - PIPELINE OPERATIONAL")
        return 0
    else:
        print("✗ SOME TESTS FAILED")
        return 1


if __name__ == "__main__":
    sys.exit(main())
