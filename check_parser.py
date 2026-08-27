#!/usr/bin/env python3
"""Helper script for parser tests."""
import sys
from parser import normalize_implicit_multiplication_expression

def main():
    if len(sys.argv) < 2:
        print("Usage: python3 check_parser.py <test_name>")
        sys.exit(1)
    
    test_name = sys.argv[1]
    
    if test_name == "pre_paren":
        result = normalize_implicit_multiplication_expression("2(a+b)")
        print(result)
        assert result == "2 * (a+b)", f"Expected '2 * (a+b)', got '{result}'"
    elif test_name == "post_paren":
        result = normalize_implicit_multiplication_expression("(a+b)(c+d)")
        print(result)
        assert result == "(a+b) * (c+d)", f"Expected '(a+b) * (c+d)', got '{result}'"
    elif test_name == "chain":
        result = normalize_implicit_multiplication_expression("3xyz")
        print(result)
        assert result == "3 * x * y * z", f"Expected '3 * x * y * z', got '{result}'"
    else:
        print(f"Unknown test: {test_name}")
        sys.exit(1)

if __name__ == "__main__":
    main()
