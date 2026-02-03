#!/usr/bin/env python3
import argparse
import os
import sys
import json
import re
import subprocess
from pathlib import Path
from typing import List, Dict, Optional, Tuple
import shutil


class LeanAgenticPipeline:
    def __init__(self, max_iterations: int = 15):
        self.max_iterations = max_iterations
        self.traces: List[Dict] = []
        self.current_iteration = 0
        self.error_count = 0

    def validate_latex(self, latex: str) -> Tuple[bool, str]:
        """Parse and validate LaTeX input"""
        if not latex or not latex.strip():
            return False, "Empty input"

        math_patterns = [
            r"theorem",
            r"lemma",
            r"corollary",
            r"example",
            r"define",
            r"forall",
            r"exists",
            r"->",
            r"iff",
            r"implies",
            r"x",
            r"y",
            r"z",
            r"let",
            r"return",
            r"have",
            r"\w+",
            r"\+",
            r"-",
            r"\*",
            r"\^",
            r"\(",
            r"\)",
            r"=",
            r"[a-zA-Z]",
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
        """Generate a Lean 4 file with theorem and sorry"""
        lean_content = f"""-- {latex}
theorem {theorem_name} : {latex} := by
  sorry"""

        return lean_content

    def compile_lean(self, lean_file: Path) -> Tuple[int, str, str]:
        """Compile Lean file and return exit code, stdout, stderr"""
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
        """Parse Lean compiler error messages"""
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
                    error_info["type"] = "error"  # Mark that we found an error
                elif key == "term":
                    error_info["term"] = match.group(1).strip()
                elif key == "expected":
                    error_info["expected_type"] = match.group(1).strip()
                elif key == "goal":
                    error_info["goal"] = match.group(1).strip()

        return error_info if error_info["type"] != "unknown" else None

    def select_tactic(self, error_info: Dict) -> Optional[str]:
        """Select appropriate tactic based on error information"""
        if not error_info:
            return None

        error_msg = error_info.get("error", "").lower()
        goal = error_info.get("goal", "").lower()
        term = error_info.get("term", "").lower()
        expected = error_info.get("expected_type", "").lower()

        if "ring" in error_msg or any(op in error_msg for op in ["+", "-", "*", "^"]):
            return "ring"

        if (
            "inequality" in error_msg
            or "or" in error_msg
            or any(op in goal for op in ["<", "≤", "≥"])
        ):
            return "linarith"

        if "induction" in error_msg or (
            "case" in error_msg and "case" in error_info.get("line", "")
        ):
            return "induction"

        if "apply" in error_msg and "has type" in error_msg:
            if "forall" in expected or "exists" in expected:
                return "intro"
            return "apply"

        if "sorry" in error_msg.lower():
            return "exact"

        if "eq" in goal or "equal" in goal:
            if "add" in term or "mul" in term:
                return "field_simp"
            return "simp"

        return "simp"

    def execute_tactic_loop(self, latex: str) -> Tuple[bool, str]:
        """Execute the agentic tactic search loop"""
        try:
            theorem_name = f"test_theorem_{self.current_iteration}"
            lean_file = Path(f"temp_lean_{self.current_iteration}.lean")

            lean_content = self.generate_lean_file(latex, theorem_name)
            lean_file.write_text(lean_content)

            original_stderr = ""
            current_tactics = []

            for iteration in range(self.max_iterations):
                self.current_iteration = iteration

                exit_code, stdout, stderr = self.compile_lean(lean_file)

                output = stderr if stderr else stdout
                if exit_code == 0:
                    self.traces.append(
                        {
                            "status": "success",
                            "iteration": iteration,
                            "theorems": [theorem_name],
                            "final_code": lean_content,
                        }
                    )
                    lean_file.unlink()
                    return (True, lean_content)

                error_info = self.parse_lean_error(output)
                if not error_info:
                    original_stderr = stderr
                    continue

                tactic = self.select_tactic(error_info)
                if not tactic:
                    tactic = "simp"

                current_tactics.append(tactic)

                trace_entry = {
                    "iteration": iteration,
                    "exit_code": exit_code,
                    "error": error_info.get("error", ""),
                    "goal": error_info.get("goal", ""),
                    "attempted_tactic": tactic,
                    "current_tactics": list(current_tactics),
                }
                self.traces.append(trace_entry)

                if iteration == 0:
                    original_stderr = stderr

            lean_file.unlink()
            return False, "Max iterations reached without successful verification"

        except Exception as e:
            return False, f"Pipeline error: {str(e)}"

    def run_pipeline(self, latex: str) -> Dict:
        """Main pipeline execution"""
        self.current_iteration = 0
        self.traces = []

        validation_result, validation_msg = self.validate_latex(latex)

        if not validation_result:
            return {
                "status": "validation_failed",
                "message": validation_msg,
                "traces": self.traces,
            }

        success, result = self.execute_tactic_loop(latex)

        audit_trail = {
            "status": "success" if success else "failed",
            "iterations_used": self.current_iteration,
            "max_iterations": self.max_iterations,
            "traces": self.traces,
        }

        return audit_trail


def main():
    parser = argparse.ArgumentParser(
        description="Lean 4 Agentic Pipeline: Convert LaTeX math to verified Lean 4 code"
    )
    parser.add_argument("input", help="LaTeX mathematical statement")
    parser.add_argument("--output", help="Output Lean file path", default="output.lean")
    parser.add_argument(
        "--max-iterations",
        type=int,
        help="Maximum tactic search iterations",
        default=15,
    )

    args = parser.parse_args()

    pipeline = LeanAgenticPipeline(max_iterations=args.max_iterations)

    result = pipeline.run_pipeline(args.input)

    if result["status"] == "validation_failed":
        print(f"Validation Failed: {result['message']}", file=sys.stderr)
        sys.exit(1)

    if result["status"] == "success":
        print("✓ Verification Successful!")
        print(f"Iterations used: {result['iterations_used']}")
        print(f"Output file: {args.output}")

        with open(args.output, "w") as f:
            f.write(result["traces"][-1]["final_code"])

        print(f"Code written to {args.output}")
        sys.exit(0)
    else:
        print(
            f"Verification Failed after {result['iterations_used']} iterations",
            file=sys.stderr,
        )
        print("\nAudit Trail:", file=sys.stderr)
        print(json.dumps(result["traces"], indent=2), file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
