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
