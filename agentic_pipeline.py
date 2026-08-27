#!/usr/bin/env python3
"""
Lean 4 Agentic Pipeline - Core implementation.
Converts constrained mathematical statements into verified Lean 4 code using iterative tactic search.
"""

import re
import sys
import os
import json
import subprocess
import tempfile
from pathlib import Path
from typing import List, Optional, Tuple, Dict, Any
from parser import (
    parse_equation,
    extract_free_variables,
    tokenize,
    normalize_implicit_multiplication,
    BinOp,
    Var,
    Num,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
)


class LeanAgenticPipeline:
    """
    Pipeline that converts mathematical statements to verified Lean 4 proofs.
    
    Uses iterative tactic search with strict verification: success requires
    the final Lean file to compile without `sorry` placeholders.
    """
    
    def __init__(self, use_mathlib: bool = True, lean_path: Optional[str] = None):
        """
        Initialize the pipeline.
        
        Args:
            use_mathlib: Whether to use Mathlib tactics
            lean_path: Path to lean executable (or None to search PATH)
        """
        self.use_mathlib = use_mathlib
        self.lean_path = lean_path or self._find_lean()
        self.tactic_candidates = [
            'rfl', 'simp', 'norm_num', 'decide', 'ring', 
            'linarith', 'omega', 'field_simp'
        ]
    
    def _find_lean(self) -> Optional[str]:
        """Find lean executable in PATH."""
        env = os.environ.copy()
        env["PATH"] = str(Path.home() / ".elan" / "bin") + ":" + env.get("PATH", "")
        
        try:
            result = subprocess.run(
                ["which", "lean"],
                capture_output=True,
                text=True,
                env=env,
                timeout=5
            )
            if result.returncode == 0:
                lean_path = result.stdout.strip()
                # Verify lean is actually usable (not just a stub that downloads)
                # Check if toolchain directory exists
                toolchain_dir = Path.home() / ".elan" / "toolchains"
                if toolchain_dir.exists():
                    # Check if there's at least one toolchain installed
                    toolchains = [d for d in toolchain_dir.iterdir() if d.is_dir() and not d.name.endswith('.lock')]
                    if toolchains:
                        return lean_path
                return None
        except:
            pass
        return None
    
    def validate_input(self, latex_input: str) -> Tuple[bool, str]:
        """
        Validate mathematical input.
        
        Returns:
            (is_valid, error_message)
        """
        if not latex_input or not latex_input.strip():
            return False, "Empty input"
        
        # Basic validation - reject obviously non-mathematical input
        if re.match(r'^[a-zA-Z\s]+$', latex_input.strip()) and not re.search(r'[=<>!]', latex_input):
            return False, "Non-mathematical input"
        
        # Try to parse
        try:
            eq, free_vars = parse_equation(latex_input)
            if eq is None and not free_vars:
                return False, "Could not parse mathematical expression"
        except Exception as e:
            return False, f"Parse error: {str(e)}"
        
        return True, ""
    
    def _suggest_type(self, expression: str) -> str:
        """
        Suggest appropriate type based on expression content.
        
        Returns:
            Type string: 'Nat', 'Int', or 'Rat'
        """
        # Check for division -> Rat
        if '/' in expression:
            return 'Rat'
        
        # Check for negative numbers -> Int
        if re.search(r'-\d', expression) or re.search(r'(?<!\w)-\(', expression):
            return 'Int'
        
        # Default to Nat for non-negative
        return 'Nat'
    
    def _get_var_type(self, variables: List[str], expression: str) -> str:
        """
        Get type for variables based on expression context.
        
        Args:
            variables: List of variable names
            expression: Full expression string
            
        Returns:
            Type string for variables
        """
        return self._suggest_type(expression)
    
    def check_for_sorry(self, lean_source: str, compiler_output: str) -> Tuple[bool, str]:
        """
        Check if output contains sorry or sorryAx.
        
        Uses word-boundary matching to avoid false positives from identifiers
        containing "sorry" as a substring.
        
        Args:
            lean_source: The Lean source code
            compiler_output: Compiler stdout/stderr
            
        Returns:
            (has_sorry, reason)
        """
        # Check source for sorry or sorryAx (word boundary match)
        # Check fully-qualified patterns first to get specific reason
        if re.search(r'\bLean\.Elab\.Tactic\.sorry\b', lean_source):
            return True, "Lean source contains 'Lean.Elab.Tactic.sorry'"
        if re.search(r'\bTactic\.sorry\b', lean_source):
            return True, "Lean source contains 'Tactic.sorry'"
        if re.search(r'\bsorryAx\b', lean_source):
            return True, "Lean source contains 'sorryAx'"
        if re.search(r'\bsorry\b', lean_source):
            return True, "Lean source contains 'sorry'"
        
        # Check compiler output for sorry or sorryAx (word boundary match)
        if re.search(r'\bsorryAx\b', compiler_output):
            return True, "Compiler output mentions 'sorryAx'"
        
        # Check for Lean 4 warning patterns indicating sorry usage
        if re.search(r'declaration uses sorry', compiler_output):
            return True, "Compiler output indicates declaration uses sorry"
        if re.search(r'warning:.*uses sorry', compiler_output):
            return True, "Compiler output warning indicates sorry usage"
        if re.search(r'uses sorryAx', compiler_output):
            return True, "Compiler output indicates uses sorryAx"
        
        if re.search(r'\bsorry\b', compiler_output):
            return True, "Compiler output mentions 'sorry'"
        
        return False, ""
    
    def _verify_no_sorry_axioms(self, temp_path: str) -> Tuple[bool, str]:
        """
        Verify that a compiled theorem doesn't use sorry axioms.
        
        Runs `#print axioms theorem_name` to check the axiom set.
        
        Args:
            temp_path: Path to the temporary .lean file
            
        Returns:
            (is_clean, reason) - is_clean is True if no sorry axioms found
        """
        try:
            with open(temp_path, 'r') as f:
                original_content = f.read()
            
            verify_code = original_content + "\n#print axioms qed_goal\n"
            verify_path = temp_path + ".verify.lean"
            with open(verify_path, 'w') as f:
                f.write(verify_code)
            
            result = subprocess.run(
                [self.lean_path or 'lean', verify_path],
                capture_output=True,
                text=True,
                timeout=30,
                env=os.environ.copy()
            )
            
            output = result.stdout + result.stderr
            
            if re.search(r'\bsorry\b', output):
                return False, "#print axioms shows sorry"
            if re.search(r'\bsorryAx\b', output):
                return False, "#print axioms shows sorryAx"
            if re.search(r'declaration uses sorry', output):
                return False, "#print axioms indicates declaration uses sorry"
            if re.search(r'\bTactic\.sorry\b', output):
                return False, "#print axioms shows Tactic.sorry"
            if re.search(r'\bLean\.Elab\.Tactic\.sorry\b', output):
                return False, "#print axioms shows Lean.Elab.Tactic.sorry"
            
            return True, ""
            
        except Exception as e:
            return False, f"Axiom verification failed (fail-closed): {e}"
        finally:
            try:
                os.unlink(verify_path)
            except:
                pass
    
    def get_tactic_candidates(self, expression: str) -> List[str]:
        """
        Get ordered tactic candidates based on expression type.
        
        Args:
            expression: Mathematical expression
            
        Returns:
            Ordered list of tactic candidates
        """
        candidates = []
        
        # Check for division -> field_simp first
        if '/' in expression:
            candidates.extend(['field_simp', 'ring', 'norm_num', 'simp'])
        
        # Check for inequality -> linarith/omega first
        elif re.search(r'[<>]|<=|>=|!=', expression):
            candidates.extend(['linarith', 'omega', 'simp', 'norm_num'])
        
        # Check for polynomial/algebraic -> ring first
        elif re.search(r'\^|[*]|ab|a\^2|b\^2', expression):
            candidates.extend(['ring', 'simp', 'linarith', 'norm_num'])
        
        # Default order
        else:
            candidates.extend(['rfl', 'simp', 'norm_num', 'decide', 'ring'])
        
        # Add remaining tactics
        for tactic in self.tactic_candidates:
            if tactic not in candidates:
                candidates.append(tactic)
        
        return candidates
    
    def select_tactic(self, error_info: Dict[str, Any]) -> str:
        """
        Select tactic based on error information and goal state.
        
        Args:
            error_info: Dictionary with error details
            
        Returns:
            Selected tactic
        """
        goal = error_info.get('goal', '')
        error = error_info.get('error', '')
        expected_type = error_info.get('expected_type', '')
        
        # Check goal for ring patterns
        if re.search(r'[+*^].*=', goal) or 'ring' in goal.lower():
            return 'ring'
        
        # Check for inequality patterns
        if re.search(r'[<>]|<=|>=', goal):
            return 'linarith'
        
        # Check for type mismatch with Bool
        if 'Bool' in expected_type:
            return 'decide'
        
        # Check for numeric normalization
        if re.search(r'\d+', goal) and ('+' in goal or '*' in goal):
            return 'norm_num'
        
        # Default to simp
        return 'simp'
    
    def generate_lean_code(self, expression: str, free_vars: List[str]) -> str:
        """
        Generate Lean 4 theorem code from mathematical expression.
        
        Args:
            expression: Mathematical expression
            free_vars: List of free variables
            
        Returns:
            Lean 4 code string
        """
        # Determine type
        var_type = self._get_var_type(free_vars, expression)
        
        # Build theorem statement
        if free_vars:
            params = ' '.join([f'({v} : {var_type})' for v in free_vars])
            theorem = f"theorem qed_goal {params} : {expression} := by\n"
        else:
            # Add type annotation for negative numbers or division
            if var_type in ('Int', 'Rat'):
                # Annotate the expression with the appropriate type
                if '-' in expression and var_type == 'Int':
                    # For negative numbers, add type annotation
                    annotated_expr = re.sub(r'(-?\d+)', r'(\1 : Int)', expression)
                    theorem = f"theorem qed_goal : {annotated_expr} := by\n"
                elif '/' in expression and var_type == 'Rat':
                    # For division, add type annotation
                    theorem = f"theorem qed_goal : {expression} := by\n"
                else:
                    theorem = f"theorem qed_goal : {expression} := by\n"
            else:
                theorem = f"theorem qed_goal : {expression} := by\n"
        
        # Add imports if using Mathlib
        if self.use_mathlib:
            imports = "import Mathlib.Tactic\n\n"
        else:
            imports = ""
        
        return imports + theorem
    
    def execute_tactic_loop(self, expression: str, max_iterations: int = 15) -> Dict[str, Any]:
        """
        Execute tactic search loop to find a working proof.
        
        Args:
            expression: Mathematical expression
            max_iterations: Maximum number of tactic attempts
            
        Returns:
            Dictionary with results
        """
        # Validate input
        is_valid, error_msg = self.validate_input(expression)
        if not is_valid:
            return {
                'success': False,
                'error': error_msg,
                'lean_code': None,
                'attempts': []
            }
        
        # Check if Lean is available
        if not self.lean_path:
            return {
                'success': False,
                'error': 'Lean compiler not found. Install elan and run: elan default leanprover/lean4:stable',
                'lean_code': None,
                'attempts': []
            }
        
        # Parse expression
        eq, free_vars = parse_equation(expression)
        
        # Generate base Lean code
        base_code = self.generate_lean_code(expression, free_vars)
        
        # Get tactic candidates
        candidates = self.get_tactic_candidates(expression)
        
        attempts = []
        for i, tactic in enumerate(candidates[:max_iterations]):
            # Generate complete Lean code with tactic
            lean_code = base_code + f"  {tactic}\n"
            
            # Write to temporary file
            with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', delete=False) as f:
                f.write(lean_code)
                temp_path = f.name
            
            try:
                # Compile
                result = subprocess.run(
                    [self.lean_path or 'lean', temp_path],
                    capture_output=True,
                    text=True,
                    timeout=30,
                    env=os.environ.copy()
                )
                
                # Check for sorry
                has_sorry, sorry_reason = self.check_for_sorry(lean_code, result.stdout + result.stderr)
                
                attempt = {
                    'iteration': i,
                    'tactic': tactic,
                    'exit_code': result.returncode,
                    'has_sorry': has_sorry,
                    'sorry_reason': sorry_reason,
                    'stdout': result.stdout[:500],
                    'stderr': result.stderr[:500]
                }
                attempts.append(attempt)
                
                # Success if compiled without sorry
                if result.returncode == 0 and not has_sorry:
                    # Post-compilation re-read: verify file on disk still has no sorry
                    try:
                        with open(temp_path, 'r') as f:
                            disk_source = f.read()
                        disk_sorry, disk_reason = self.check_for_sorry(disk_source, '')
                        if disk_sorry:
                            attempt['has_sorry'] = True
                            attempt['sorry_reason'] = f"Post-compilation source re-read: {disk_reason}"
                            continue
                    except Exception:
                        pass
                    
                    # Additional verification: check axioms if compilation succeeded
                    axioms_clean, axioms_reason = self._verify_no_sorry_axioms(temp_path)
                    
                    if axioms_clean:
                        return {
                            'success': True,
                            'lean_code': lean_code,
                            'tactic': tactic,
                            'attempts': attempts,
                            'verification': {
                                'source_check': 'passed',
                                'compiler_check': 'passed',
                                'axioms_check': 'passed'
                            }
                        }
                    else:
                        # Axioms check failed - this is a sorry leak
                        attempt['has_sorry'] = True
                        attempt['sorry_reason'] = axioms_reason
                        continue
                
            except subprocess.TimeoutExpired:
                attempts.append({
                    'iteration': i,
                    'tactic': tactic,
                    'exit_code': -1,
                    'has_sorry': False,
                    'sorry_reason': '',
                    'stdout': '',
                    'stderr': 'Timeout'
                })
            except Exception as e:
                attempts.append({
                    'iteration': i,
                    'tactic': tactic,
                    'exit_code': -1,
                    'has_sorry': False,
                    'sorry_reason': '',
                    'stdout': '',
                    'stderr': str(e)
                })
            finally:
                # Cleanup
                try:
                    os.unlink(temp_path)
                except:
                    pass
        
        return {
            'success': False,
            'error': f'No tactic succeeded after {len(attempts)} attempts',
            'lean_code': base_code,
            'attempts': attempts
        }
    
    def _execute_with_initial_code(self, initial_code: str, max_iterations: int = 15) -> Dict[str, Any]:
        """
        Execute tactic loop with pre-generated initial code.
        
        Args:
            initial_code: Initial Lean code
            max_iterations: Maximum iterations
            
        Returns:
            Dictionary with results
        """
        # Extract expression from initial code
        match = re.search(r': (.+?) := by', initial_code)
        if not match:
            return {
                'success': False,
                'error': 'Could not extract expression from initial code',
                'lean_code': initial_code,
                'attempts': []
            }
        
        expression = match.group(1)
        return self.execute_tactic_loop(expression, max_iterations)
    
    def run(self, latex_input: str) -> Dict[str, Any]:
        """
        Run the full pipeline on mathematical input.
        
        Args:
            latex_input: Mathematical expression
            
        Returns:
            Dictionary with results
        """
        return self.execute_tactic_loop(latex_input)


def main():
    """CLI entry point."""
    if len(sys.argv) < 2:
        print("Usage: python3 agentic_pipeline.py <mathematical_expression>")
        sys.exit(1)
    
    expression = sys.argv[1]
    pipeline = LeanAgenticPipeline()
    
    result = pipeline.run(expression)
    
    if result['success']:
        print("✓ Verification Successful! (no sorry)")
        print(f"\nGenerated Lean:\n{result['lean_code']}")
        print(f"\nWinning tactic: {result['tactic']}")
    else:
        print("✗ Verification Failed")
        print(f"Error: {result['error']}")
    
    # Write traces
    with open('traces.json', 'w') as f:
        json.dump(result, f, indent=2)
    
    sys.exit(0 if result['success'] else 1)


if __name__ == "__main__":
    main()
