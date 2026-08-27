#!/usr/bin/env python3
"""Helper script for checking sorry detection."""
import sys
from agentic_pipeline import LeanAgenticPipeline

def main():
    if len(sys.argv) < 2:
        print("Usage: python3 check_sorry.py <true|false>")
        sys.exit(1)
    
    test_sorry = sys.argv[1].lower() == "true"
    
    pipeline = LeanAgenticPipeline()
    
    if test_sorry:
        # Test that sorry is detected
        has_sorry, reason = pipeline.check_for_sorry(
            "theorem t : 0=0 := by sorry",
            ""
        )
        print(has_sorry)
        assert has_sorry == True, f"Expected True, got {has_sorry}"
    else:
        # Test that no sorry is detected
        has_sorry, reason = pipeline.check_for_sorry(
            "theorem t : 0=0 := by rfl",
            ""
        )
        print(has_sorry)
        assert has_sorry == False, f"Expected False, got {has_sorry}"

if __name__ == "__main__":
    main()
