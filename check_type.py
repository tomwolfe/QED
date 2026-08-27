#!/usr/bin/env python3
"""Helper script for type inference tests."""
import sys
from agentic_pipeline import LeanAgenticPipeline

def main():
    if len(sys.argv) < 2:
        print("Usage: python3 check_type.py <test_name>")
        sys.exit(1)
    
    test_name = sys.argv[1]
    pipeline = LeanAgenticPipeline()
    
    if test_name == "int":
        result = pipeline._suggest_type("-1 + 1 = 0")
        print(result)
        assert result == "Int", f"Expected 'Int', got '{result}'"
    elif test_name == "rat":
        result = pipeline._suggest_type("x / 2 = y")
        print(result)
        assert result == "Rat", f"Expected 'Rat', got '{result}'"
    elif test_name == "annotation":
        code = pipeline.generate_lean_code("-1 + 1 = 0", [])
        print(code)
        assert ": Int" in code, f"Expected ': Int' in code"
    else:
        print(f"Unknown test: {test_name}")
        sys.exit(1)

if __name__ == "__main__":
    main()
