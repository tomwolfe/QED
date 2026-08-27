#!/usr/bin/env python3
"""QED: Lean 4 Agentic Pipeline - Converts LaTeX math to verified Lean 4 proofs."""

import argparse
import os
import sys
import json
import re
import subprocess
from pathlib import Path
from typing import List, Dict, Optional, Tuple, Any
import shutil
import tempfile
from datetime import datetime


class LeanAgenticPipeline:
    """Main pipeline that converts LaTeX math statements into verified Lean 4 proofs."""

    def __init__(self, max_iterations: int = 15):
        self.max_iterations = max_iterations
        self.traces: List[Dict] = []
        self.current_iteration = 0
        self.error_count = 0

    def validate_latex(self, latex: str) -> Tuple[bool, str]:
        """Parse and validate LaTeX input - checks for mathematical structure."""
        if not latex or not latex.strip():
            return False, "Empty input"

        # Use parser to check for actual mathematical structure
        try:
            from parser import parse as parse_equation
            parsed = parse_equation(latex)
            # Accept if it's recognized as an equation with proper structure
            if parsed['type'] == 'equation':
                return True, "Valid LaTeX theorem statement"
            # Also accept some basic patterns
            math_keywords = ['0', '1', '2', '3', 'Nat', 'Int', 'Real', 'rat',
                           '+', '-', '*', '/', '^', '=', '<', '>', '<=', '>=']
            has_math = any(kw in latex for kw in math_keywords)
            if has_math and len(latex.strip()) > 3:
                return True, "Valid LaTeX theorem statement"
            return False, "Input doesn't appear to be a mathematical theorem statement"
        except ImportError:
            # Fallback: basic validation
            math_patterns = [
                r"theorem", r"lemma", r"corollary", r"example", r"define",
                r"forall", r"exists", r"->", r"iff", r"implies",
                r"x", r"y", r"z", r"let", r"return", r"have",
                r"\+", r"-", r"\*", r"\^", r"\(", r"\)", r"=",
                r"[a-zA-Z]", r"\\le", r"\\ge", r"\\neq",
            ]
            found = False
            for pattern in math_patterns:
                if re.search(pattern, latex):
                    found = True
                    break
            if not found:
                return False, "Input doesn't appear to be a mathematical theorem statement"
            return True, "Valid LaTeX theorem statement"

    def generate_lean_file(self, latex: str, theorem_name: str) -> str:
        """Generate a Lean 4 file with theorem and sorry placeholder."""
        lean_content = f"""-- {latex}
theorem {theorem_name} : {latex} := by
  sorry"""

        return lean_content

    def check_for_sorry(self, lean_content: str, compiler_output: str) -> Tuple[bool, str]:
        """Check if the Lean content or compiler output contains sorry or sorryAx.
        
        This is the strict no-sorry success criterion.
        """
        # Check if the source code contains sorry
        if "sorry" in lean_content.lower():
            return True, "Final Lean source contains 'sorry'"
        
        # Check if compiler output mentions sorryAx
        if "sorryAx" in compiler_output:
            return True, "Compiler output mentions 'sorryAx'"
        
        # Check if compiler output mentions unimplemented sorry
        if "unimplemented: sorry" in compiler_output.lower():
            return True, "Compiler output mentions unimplemented sorry"
        
        return False, ""

    def get_tactic_candidates(self, latex: str, parsed_info: Dict = None) -> List[str]:
        """Get ordered list of tactic candidates based on the input statement.
        
        Phase 1: Real tactic search loop - selects tactics based on statement type.
        Uses parsed AST info when available for smarter ordering.
        """
        # Default tactic candidates for MVP
        candidates = ["rfl", "simp", "norm_num", "decide", "ring", "linarith", "omega", "field_simp"]
        
        # Check for division - needs field_simp first
        if any(op in latex for op in ["/", "\\frac"]):
            candidates = ["field_simp", "ring", "norm_num", "simp", "linarith", "rfl"]
        
        # Check for inequalities - needs linarith/omega first
        elif any(op in latex for op in ["<", ">", "≤", "≥", "\\le", "\\ge"]):
            candidates = ["linarith", "omega", "simp", "norm_num", "rfl"]
        
        # Polynomial/algebraic expressions - ring first
        elif any(op in latex for op in ["+", "-", "*", "^"]):
            candidates = ["ring", "simp", "linarith", "norm_num", "field_simp", "rfl", "decide"]
        
        # Natural number specific patterns
        if "Nat.succ" in latex or "Nat.zero" in latex:
            candidates = ["rfl", "simp", "omega", "norm_num", "decide"]
        
        # Negative numbers - need Int type
        if any(neg in latex for neg in ["-1", "-2", "-3", "(-"]):
            candidates = ["norm_num", "ring", "simp", "linarith", "rfl"]
        
        # Use parsed info for smarter ordering when available
        if parsed_info is not None:
            free_vars = parsed_info.get('free_variables', [])
            if free_vars:
                # Has variables - simp and ring are more likely to help
                if "ring" in candidates:
                    candidates.remove("ring")
                    candidates.insert(0, "ring")
                if "simp" in candidates:
                    candidates.remove("simp")
                    candidates.insert(1, "simp")
        
        return candidates

    def replace_sorry_with_tactic(self, lean_content: str, tactic: str) -> str:
        """Replace 'sorry' placeholder with the given tactic."""
        # Replace the sorry in the by block with the tactic
        # The sorry is indented with 2 spaces in the by block
        return lean_content.replace("  sorry", f"  {tactic}")

    def parse_latex_to_lean(self, latex: str) -> Dict[str, Any]:
        """Parse LaTeX input and generate Lean code information.
        
        Phase 2/3: Formula parser + Lean code generation.
        Returns dict with lean_code, free_variables, suggested_type, needs_mathlib, imports.
        """
        # Special case: Nat.succ 0 = 1 is a trivial theorem provable with rfl
        if latex.strip() == "Nat.succ 0 = 1":
            return {
                'lean_code': "-- Generated by QED Pipeline\n\n theorem qed_goal : Nat.succ 0 = 1 := by\n  rfl",
                'free_variables': [],
                'suggested_type': 'Nat',
                'needs_mathlib': False,
                'imports': [],
            }
        
        # Parse the equation/inequality using the parser module
        try:
            from parser import parse as parse_equation
        except ImportError:
            # Fallback: basic parsing if parser module not available
            parsed = self._fallback_parse(latex)
            if parsed is None:
                return {
                    'lean_code': "",
                    'free_variables': [],
                    'suggested_type': None,
                    'needs_mathlib': False,
                    'imports': [],
                }
            result = {
                'lean_code': "",
                'free_variables': parsed['free_variables'] if parsed else [],
                'suggested_type': None,
                'needs_mathlib': False,
                'imports': [],
            }
            return result
        
        parsed = parse_equation(latex)
        
        result = {
            'lean_code': "",
            'free_variables': parsed['free_variables'],
            'suggested_type': None,
            'needs_mathlib': False,
            'imports': [],
        }
        
        if parsed['type'] != 'equation':
            # Can't generate Lean code without an equation
            return result
        
        left = parsed['left']
        right = parsed['right']
        relation = parsed['relation']
        
        # Determine if we need Mathlib based on the expression content
        # Check for patterns that require Mathlib tactics
        needs_mathlib = False
        if any(op in latex for op in ["^", "**"]):
            # Power operations need ring or similar
            needs_mathlib = True
        if any(op in latex for op in ["\\cdot", "\\le", "\\ge", "\\neq"]):
            # LaTeX-like tokens might need Mathlib
            needs_mathlib = True
        
        # For MVP, we default to concrete types based on expression content
        suggested_type = self._suggest_type(latex)
        result['suggested_type'] = suggested_type
        
        # Determine if we need Mathlib
        result['needs_mathlib'] = needs_mathlib
        
        # Generate imports if needed
        imports = []
        if needs_mathlib:
            imports.append("import Mathlib.Tactic")
        result['imports'] = imports
        
        # Generate the Lean code
        lean_code_parts = []
        
        # Add imports section if needed
        if imports:
            lean_code_parts.append("import Mathlib.Tactic")
        
        # Add theorem header
        # Build the parameter list from free variables
        var_params = ""
        if result['free_variables']:
            # For MVP, use Int type for variables with arithmetic, Nat otherwise
            var_type = self._get_var_type(result['free_variables'], latex)
            var_params = " " + " ".join([f"({v} : {var_type})" for v in result['free_variables']])
        
        # Determine the theorem statement
        # For simple equalities like "0 = 0", no parameters needed
        # For equations with variables, add parameter declaration
        theorem_stmt = latex
        
        # Build the Lean code
        code = "-- Generated by QED Pipeline\n"
        
        # Add imports section if needed
        if imports:
            code += "import Mathlib.Tactic\n\n"
        
        # Add theorem
        theorem_line = f"theorem qed_goal{var_params} : {theorem_stmt} := by"
        code += theorem_line + "\n"
        
        # Add default tactic - we'll use a default tactic based on the statement type
        tactic = self._select_default_tactic(latex)
        code += f"  {tactic}"
        
        result['lean_code'] = code
        
        return result
    
    def _fallback_parse(self, latex: str) -> Optional[Dict[str, Any]]:
        """Fallback parsing if parser module not available."""
        # Basic parsing: just check for = sign and extract variables
        if "=" not in latex:
            return None
        
        # Simple extraction of variables (letters)
        import re
        variables = re.findall(r'[a-zA-Z]+', latex)
        # Remove common non-variable words
        stop_words = {'the', 'and', 'or', 'but', 'is', 'are', 'was', 'were'}
        variables = [v for v in variables if v not in stop_words]
        
        # Remove duplicates while preserving order
        seen = set()
        unique_vars = []
        for v in variables:
            if v not in seen:
                seen.add(v)
                unique_vars.append(v)
        
        return {
            'type': 'equation',
            'free_variables': unique_vars,
        }
    
    def _suggest_type(self, latex: str) -> Optional[str]:
        """Suggest a Lean type based on the input expression."""
        # Check for patterns that suggest specific types
        if any(neg in latex for neg in ["-1", "-2", "-3", "(-"]):
            # Negative numbers need Int
            return "Int"
        
        if "Nat.succ" in latex:
            return "Nat"
        
        if any(op in latex for op in ["/", "\\frac"]):
            # Division needs Rat or Real
            return "Rat"
        
        # Default to Nat for non-negative integer expressions
        return "Nat"
    
    def _get_var_type(self, free_variables: List[str], latex: str) -> str:
        """Get the type for variables in the theorem."""
        # Use Int if there are negative numbers or subtraction
        if any(neg in latex for neg in ["-1", "-2", "-3", "(-"]):
            return "Int"
        
        # Use Nat for natural number specific patterns
        if "Nat.succ" in latex or "Nat.zero" in latex:
            return "Nat"
        
        if any(op in latex for op in ["/", "\\frac"]):
            return "Rat"
        
        # Default to Nat for non-negative integer expressions
        return "Nat"
    
    def _select_default_tactic(self, latex: str) -> str:
        """Select a default tactic based on the input statement type."""
        # Concrete numeric equality
        if latex.strip() == "0 = 0":
            return "rfl"
        
        if any(op in latex for op in ["+", "-", "*", "^"]):
            # Polynomial/algebraic expressions - try ring first
            return "ring"
        
        if any(op in latex for op in ["<", ">", "≤", "≥"]):
            # Inequalities
            return "linarith"
        
        # Natural number arithmetic
        if "Nat.succ" in latex or "Nat.zero" in latex:
            return "simp"
        
        # Default to simp
        return "simp"
    
    def compile_lean(self, lean_file: Path) -> Tuple[int, str, str]:
        """Compile Lean file and return exit code, stdout, stderr."""
        env = os.environ.copy()
        env["PATH"] = str(Path.home() / ".elan" / "bin") + ":" + env.get("PATH", "")
        
        try:
            result = subprocess.run(
                ["lean", lean_file], capture_output=True, text=True, timeout=30, env=env
            )
            return result.returncode, result.stdout, result.stderr
        except subprocess.TimeoutExpired:
            return -1, "", "Compilation timed out"
        except Exception as e:
            return -1, "", f"Compilation error: {str(e)}"

    def parse_lean_error(self, stderr: str) -> Optional[Dict]:
        """Parse Lean compiler error messages."""
        output = stderr if stderr else ""
        patterns = {
            "line": r"lean[^:]*:(\d+):",
            "file": r'File "(.+)"',
            "error": r"error: (.+)",
            "term": r'term "([^"]+)" has type (.+)',
            "expected": r"but is expected to have type (.+)",
            "goal": r"⊢ (.+)",
            "sorry": r"unimplemented: sorry",
        }
        
        error_info = {"type": "unknown"}
        
        for key, pattern in patterns.items():
            match = re.search(pattern, output, re.MULTILINE | re.IGNORECASE)
            if match:
                if key == "line":
                    error_info["line"] = str(match.group(1))
                elif key == "error":
                    error_info["error"] = match.group(1).strip()
                    error_info["type"] = "error"
                elif key == "term":
                    error_info["term"] = match.group(1).strip()
                elif key == "expected":
                    error_info["expected_type"] = match.group(1).strip()
                elif key == "goal":
                    error_info["goal"] = match.group(1).strip()
        
        return error_info if error_info["type"] != "unknown" else None

    def select_tactic(self, error_info: Dict) -> Optional[str]:
        """Select appropriate tactic based on error information and goal state."""
        if not error_info:
            return None
        
        error_msg = error_info.get("error", "").lower()
        goal = error_info.get("goal", "").lower()
        term = error_info.get("term", "").lower()
        expected = error_info.get("expected_type", "").lower()
        
        # Ring-solvable patterns in goal
        if any(op in goal for op in ["+", "-", "*", "^", "≤", "≥", "<", ">"]):
            if "ring" in error_msg or any(op in term for op in ["+", "-", "*", "^"]):
                return "ring"
        
        # Linear arithmetic patterns
        if (
            "inequality" in error_msg
            or "or" in error_msg
            or any(op in goal for op in ["<", "≤", "≥"])
            or any(kw in goal for kw in ["nat", "int", "linear"])
        ):
            return "linarith"
        
        # Natural number arithmetic - omega handles linear nat/int
        if any(kw in goal for kw in ["nat", "n"]):
            if any(op in goal for op in ["+", "-", "<", "≤"]):
                return "omega"
        
        # Induction patterns
        if "induction" in error_msg or (
            "case" in error_msg and "case" in error_info.get("line", "")
        ):
            return "induction"
        
        # Application patterns
        if "apply" in error_msg and "has type" in error_msg:
            if "forall" in expected or "exists" in expected:
                return "intro"
            return "apply"
        
        # Sorry placeholders
        if "sorry" in error_msg:
            return "exact"
        
        # Equality with arithmetic
        if "eq" in goal or "equal" in goal:
            if any(op in term for op in ["+", "-", "*", "add", "mul"]):
                return "field_simp"
            return "simp"
        
        return "simp"

    def execute_tactic_loop(self, latex: str) -> Tuple[bool, str]:
        """Execute the agentic tactic search loop.
        
        Phase 1: Real tactic search loop that actually tries tactics.
        Each candidate generates a new Lean proof attempt.
        """
        try:
            # Create a temporary directory for this pipeline run
            with tempfile.TemporaryDirectory(prefix="qed_") as temp_dir:
                temp_path = Path(temp_dir)
                theorem_name = "qed_goal"
                lean_file = temp_path / "proof.lean"
                
                # Get ordered list of tactic candidates
                tactic_candidates = self.get_tactic_candidates(latex)
                
                # Phase 1: Try each tactic candidate by compiling
                for tactic_idx, tactic in enumerate(tactic_candidates):
                    # Generate Lean file with this tactic replacing sorry
                    lean_content = f"""-- {latex}
theorem {theorem_name} : {latex} := by
  {tactic}"""
                    
                    lean_file.write_text(lean_content)
                    
                    # Compile and check
                    exit_code, stdout, stderr = self.compile_lean(lean_file)
                    output = stderr if stderr else stdout
                    
                    # Phase 0: Strict no-sorry success criterion
                    # Success requires: exit_code == 0 AND no sorry in source AND no sorryAx in output
                    if exit_code == 0:
                        has_sorry, sorry_reason = self.check_for_sorry(lean_content, output)
                        if not has_sorry:
                            self.traces.append(
                                {
                                    "status": "success",
                                    "iteration": tactic_idx,
                                    "theorems": [theorem_name],
                                    "final_code": lean_content,
                                    "verified_without_sorry": True,
                                    "tactic_used": tactic,
                                }
                            )
                            return (True, lean_content)
                        else:
                            # Compilation succeeded but contains sorry - this is NOT success
                            self.traces.append(
                                {
                                    "iteration": tactic_idx,
                                    "exit_code": exit_code,
                                    "warning": f"Compiled but contains sorry: {sorry_reason}",
                                    "attempted_tactic": tactic,
                                }
                            )
                    else:
                        # Compilation failed - record the attempt
                        error_info = self.parse_lean_error(output)
                        self.traces.append(
                            {
                                "iteration": tactic_idx,
                                "exit_code": exit_code,
                                "error": error_info.get("error", "") if error_info else "Unknown error",
                                "attempted_tactic": tactic,
                                "lean_content": lean_content,
                            }
                        )
                
                # If we get here, all tactic candidates failed
                return False, f"All {len(tactic_candidates)} tactic candidates failed to prove the statement"
        
        except Exception as e:
            return False, f"Pipeline error: {str(e)}"

    def write_trace_file(self, audit_trail: Dict, trace_file: Path = None):
        """Write audit trail to traces.json."""
        if trace_file is None:
            trace_file = Path("traces.json")
        
        # Add metadata to audit trail
        audit_trail["timestamp"] = datetime.now().isoformat()
        audit_trail["trace_file"] = str(trace_file)
        
        try:
            with open(trace_file, "w") as f:
                json.dump(audit_trail, f, indent=2)
        except Exception as e:
            print(f"Warning: Could not write trace file: {e}", file=sys.stderr)

    def run_pipeline(self, latex: str, trace_file: Path = None) -> Dict:
        """Main pipeline execution."""
        self.current_iteration = 0
        self.traces = []

        # Phase 2/3: Parse LaTeX to Lean and generate initial code
        parsed = self.parse_latex_to_lean(latex)
        
        validation_result, validation_msg = self.validate_latex(latex)

        if not validation_result:
            audit_trail = {
                "status": "validation_failed",
                "message": validation_msg,
                "traces": self.traces,
                "original_input": latex,
            }
            self.write_trace_file(audit_trail, trace_file)
            return audit_trail

        # If parse_latex_to_lean generated code, use it as starting point
        # Otherwise fall back to generating code with sorry
        if parsed['lean_code']:
            lean_content = parsed['lean_code']
            # Update traces with parsing information
            self.traces.append(
                {
                    "status": "parsed",
                    "iteration": 0,
                    "parsed_info": {
                        "free_variables": parsed['free_variables'],
                        "suggested_type": parsed['suggested_type'],
                        "needs_mathlib": parsed['needs_mathlib'],
                        "imports": parsed['imports'],
                    },
                }
            )
        else:
            # Fall back to generating code with sorry
            lean_content = self.generate_lean_file(latex, "qed_goal")
            self.traces.append(
                {
                    "status": "generated_with_sorry",
                    "iteration": 0,
                    "initial_code": lean_content,
                }
            )

        success, result = self.execute_tactic_loop(latex) if not parsed['lean_code'] else \
            self._execute_with_initial_code(latex, lean_content)

        audit_trail = {
            "status": "success" if success else "failed",
            "iterations_used": self.current_iteration,
            "max_iterations": self.max_iterations,
            "traces": self.traces,
            "original_input": latex,
        }

        self.write_trace_file(audit_trail, trace_file)
        return audit_trail
    
    def _execute_with_initial_code(self, latex: str, initial_lean_code: str) -> Tuple[bool, str]:
        """Execute tactic loop with pre-generated initial Lean code."""
        try:
            with tempfile.TemporaryDirectory(prefix="qed_") as temp_dir:
                temp_path = Path(temp_dir)
                theorem_name = "qed_goal"
                lean_file = temp_path / "proof.lean"
                
                # Write the initial Lean code
                lean_file.write_text(initial_lean_code)
                
                # Get ordered list of tactic candidates
                tactic_candidates = self.get_tactic_candidates(latex)
                
                # Check if the initial code already has a tactic (not sorry)
                if "sorry" not in initial_lean_code.lower():
                    # Initial code already has a tactic - try to compile it
                    exit_code, stdout, stderr = self.compile_lean(lean_file)
                    output = stderr if stderr else stdout
                    
                    # Phase 0: Strict no-sorry success criterion
                    if exit_code == 0:
                        has_sorry, sorry_reason = self.check_for_sorry(initial_lean_code, output)
                        if not has_sorry:
                            self.traces.append(
                                {
                                    "status": "success",
                                    "iteration": 0,
                                    "theorems": [theorem_name],
                                    "final_code": initial_lean_code,
                                    "verified_without_sorry": True,
                                    "tactic_used": "initial code",
                                }
                            )
                            return (True, initial_lean_code)
                    
                    # If initial code didn't succeed, try additional tactics starting from index 0
                    start_idx = 1  # Skip the first since initial code already tried one
                else:
                    start_idx = 0
                
                # Phase 1: Real tactic search loop
                for tactic_idx, tactic in enumerate(tactic_candidates[start_idx:]):
                    # Generate Lean code with this tactic
                    lean_content = initial_lean_code
                    
                    # Replace sorry or existing tactic with new one
                    if "sorry" in lean_content.lower():
                        lean_content = self.replace_sorry_with_tactic(lean_content, tactic)
                    else:
                        # Code already has a tactic - replace it
                        # Find the by block and replace the tactic
                        lines = lean_content.split('\n')
                        result_lines = []
                        in_by_block = False
                        tactic_replaced = False
                        
                        for line in lines:
                            if 'by' in line and not in_by_block and not line.strip().startswith('--'):
                                in_by_block = True
                                result_lines.append(line)
                                continue
                            
                            if in_by_block:
                                if line.strip() == '' or (line.startswith(' ') and not line.startswith('  ')):
                                    in_by_block = False
                                    result_lines.append(line)
                                    continue
                                elif line.startswith('  ') and not line.startswith('   '):
                                    # Two-space indent - this is a tactic in the by block
                                    if not tactic_replaced:
                                        result_lines.append(f"  {tactic}")
                                        tactic_replaced = True
                                    else:
                                        result_lines.append(line)
                                    continue
                            
                            result_lines.append(line)
                        
                        lean_content = '\n'.join(result_lines)
                    
                    # Write and compile
                    lean_file.write_text(lean_content)
                    
                    # Compile and check
                    exit_code, stdout, stderr = self.compile_lean(lean_file)
                    output = stderr if stderr else stdout
                    
                    # Phase 0: Strict no-sorry success criterion
                    if exit_code == 0:
                        has_sorry, sorry_reason = self.check_for_sorry(lean_content, output)
                        if not has_sorry:
                            self.traces.append(
                                {
                                    "status": "success",
                                    "iteration": start_idx + tactic_idx + 1,
                                    "theorems": [theorem_name],
                                    "final_code": lean_content,
                                    "verified_without_sorry": True,
                                    "tactic_used": tactic,
                                }
                            )
                            return (True, lean_content)
                        else:
                            self.traces.append(
                                {
                                    "iteration": start_idx + tactic_idx + 1,
                                    "exit_code": exit_code,
                                    "warning": f"Compiled but contains sorry: {sorry_reason}",
                                    "attempted_tactic": tactic,
                                }
                            )
                    else:
                        error_info = self.parse_lean_error(output)
                        self.traces.append(
                            {
                                "iteration": start_idx + tactic_idx + 1,
                                "exit_code": exit_code,
                                "error": error_info.get("error", "") if error_info else "Unknown error",
                                "attempted_tactic": tactic,
                                "lean_content": lean_content,
                            }
                        )
                
                return False, f"All {len(tactic_candidates)} tactic candidates failed to prove the statement"
        
        except Exception as e:
            return False, f"Pipeline error: {str(e)}"


def main():
    parser = argparse.ArgumentParser(
        description="QED: Lean 4 Agentic Pipeline - Convert LaTeX math to verified Lean 4 code"
    )
    parser.add_argument("input", help="LaTeX mathematical statement")
    parser.add_argument("--output", help="Output Lean file path", default="output.lean")
    parser.add_argument(
        "--max-iterations",
        type=int,
        help="Maximum tactic search iterations",
        default=15,
    )
    parser.add_argument(
        "--trace-file",
        help="Path to trace file (default: traces.json)",
        default="traces.json",
    )

    args = parser.parse_args()

    pipeline = LeanAgenticPipeline(max_iterations=args.max_iterations)

    result = pipeline.run_pipeline(args.input, Path(args.trace_file))

    if result["status"] == "validation_failed":
        print(f"Validation Failed: {result['message']}", file=sys.stderr)
        print(f"Trace file written to: {args.trace_file}", file=sys.stderr)
        sys.exit(1)

    if result["status"] == "success":
        print("✓ Verification Successful!")
        print(f"Iterations used: {result['iterations_used']}")
        print(f"Output file: {args.output}")
        print(f"Trace file: {args.trace_file}")

        with open(args.output, "w") as f:
            f.write(result["traces"][-1]["final_code"])

        print(f"Code written to {args.output}")
        sys.exit(0)
    else:
        print(
            f"Verification Failed after {result['iterations_used']} iterations",
            file=sys.stderr,
        )
        print(f"Trace file written to: {args.trace_file}", file=sys.stderr)
        print("\nAudit Trail:", file=sys.stderr)
        print(json.dumps(result["traces"], indent=2), file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()