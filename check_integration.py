#!/usr/bin/env python3
"""Integration check: verify pipeline works end-to-end with real Lean compiler."""
import os
import sys
import json
import tempfile

# Ensure elan is on PATH
os.environ["PATH"] = os.path.expanduser("~/.elan/bin") + ":" + os.environ.get("PATH", "")

from agentic_pipeline import LeanAgenticPipeline

def check_case(expression, expect_success=True, expect_type=None):
    """Run one integration case."""
    pipeline = LeanAgenticPipeline()
    result = pipeline.run(expression)
    
    if expect_success:
        assert result['success'], f"Expected success for '{expression}', got: {result.get('error')}"
        # Verify no sorry
        for attempt in result.get('attempts', []):
            assert not attempt.get('has_sorry', False), f"Sorry detected in output for '{expression}'"
    
    # Verify traces.json written
    assert os.path.exists('traces.json'), "traces.json not written"
    with open('traces.json') as f:
        trace = json.load(f)
    assert 'success' in trace, "trace missing success field"
    
    print(f"  OK: {expression}")
    return result

def main():
    print("Running integration checks with real Lean compiler...")
    
    # These should succeed
    check_case("0 = 0")
    check_case("Nat.succ 0 = 1")
    check_case("x + 0 = x")
    check_case("-1 + 1 = 0")
    
    # These should fail validation
    check_case("hello world", expect_success=False)
    check_case("", expect_success=False)
    
    # Verify no-sorry gate
    pipeline = LeanAgenticPipeline()
    has_sorry, _ = pipeline.check_for_sorry("theorem t : 0=0 := by sorry", "")
    assert has_sorry == True, "Should detect sorry"
    has_sorry, _ = pipeline.check_for_sorry("theorem t : 0=0 := by rfl", "")
    assert has_sorry == False, "Should not detect sorry"
    
    print("INTEGRATION OK")

if __name__ == "__main__":
    main()
