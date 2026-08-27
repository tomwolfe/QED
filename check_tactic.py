#!/usr/bin/env python3
"""Helper script for tactic policy tests."""
import sys
from agentic_pipeline import LeanAgenticPipeline

def main():
    if len(sys.argv) < 2:
        print("Usage: python3 check_tactic.py <test_name>")
        sys.exit(1)
    
    test_name = sys.argv[1]
    pipeline = LeanAgenticPipeline()
    
    if test_name == "algebraic":
        candidates = pipeline.get_tactic_candidates("(a+b)^2 = a^2 + 2ab + b^2")
        print(candidates)
        assert "ring" in candidates, f"Expected 'ring' in candidates"
        assert candidates.index("ring") < candidates.index("simp"), f"Expected ring before simp"
    elif test_name == "inequality":
        candidates = pipeline.get_tactic_candidates("x < x + 1")
        print(candidates)
        assert "linarith" in candidates, f"Expected 'linarith' in candidates"
        assert candidates.index("linarith") < candidates.index("simp"), f"Expected linarith before simp"
    elif test_name == "ring_goal":
        error_info = {
            "error": "type mismatch",
            "goal": "⊢ a + b = b + a",
            "term": "a + b",
            "expected_type": "Nat"
        }
        result = pipeline.select_tactic(error_info)
        print(result)
        assert result == "ring", f"Expected 'ring', got '{result}'"
    else:
        print(f"Unknown test: {test_name}")
        sys.exit(1)

if __name__ == "__main__":
    main()
