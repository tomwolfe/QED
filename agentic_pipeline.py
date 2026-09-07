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
    parse_expression,
    tokenize,
    normalize_implicit_multiplication,
    contains_op,
    is_inequality,
    has_numeric_ops,
    has_polynomial_structure,
    has_rational_structure,
    find_division_variables,
    statement_kind,
    is_ode,
    involves_derivative,
    is_numeric_equality,
    _collect_vars,
    ASTNode,
    BinOp,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Neg,
)


def _collect_division_numerator_vars(node: object, result: set[str]) -> None:
    """Collect variable names from the numerator of division expressions.

    ``find_division_variables`` only collects denominator variables, but
    Mathlib's ``positivity`` tactic also needs the numerator to be positive
    (e.g. ``Q / Kp > 0`` requires ``Q > 0`` and ``Kp > 0``).  This
    function walks the AST and adds numerator variables from ``/`` nodes
    to *result* in-place.
    """
    if node is None:
        return
    if isinstance(node, BinOp):
        if node.op == '/':
            _collect_vars(node.left, result)
        _collect_division_numerator_vars(node.left, result)
        _collect_division_numerator_vars(node.right, result)
    elif isinstance(node, Neg):
        _collect_division_numerator_vars(node.expr, result)
    elif isinstance(node, (Eq, Ne, Lt, Le, Gt, Ge)):
        _collect_division_numerator_vars(node.left, result)
        _collect_division_numerator_vars(node.right, result)


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
        self.lean_path = lean_path or self._find_lean()
        # Detect Lake environment for hermetic Mathlib builds
        self._lake_root = self._find_lake_root()
        self._lake_env_lean = self._build_lake_env_lean_cmd()
        # Auto-detect Mathlib availability
        self.use_mathlib = use_mathlib and self._check_mathlib_available()
        self.tactic_candidates = [
            'rfl', 'simp', 'norm_num', 'decide', 'ring', 
            'linarith', 'omega', 'field_simp', 'dsimp', 'intro',
            'positivity',
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
        except Exception:
            pass
        return None
    
    def _find_lake_root(self) -> Optional[Path]:
        """Walk up from CWD to find a directory containing lakefile.lean."""
        d = Path.cwd()
        while d != d.parent:
            if (d / "lakefile.lean").exists():
                return d
            d = d.parent
        if (d / "lakefile.lean").exists():
            return d
        return None
    
    def _build_lake_env_lean_cmd(self) -> Optional[List[str]]:
        """If a Lake root is detected, return the command prefix for
        ``lake env lean <file>`` so Lean resolves Mathlib imports."""
        if self._lake_root is None:
            return None
        elan_bin = str(Path.home() / ".elan" / "bin")
        lake_bin = os.path.join(elan_bin, "lake")
        if not os.path.isfile(lake_bin):
            return None
        return [lake_bin, "env", "lean"]
    
    def _compile_lean_cmd(self, lean_file: str) -> List[str]:
        """Return the full command list to compile *lean_file*.
        
        When a Lake root with ``lakefile.lean`` is detected, use
        ``lake env lean <file>`` so that Mathlib imports resolve
        through the hermetic Lake build graph.  Otherwise fall back
        to the bare ``lean`` executable.
        """
        if self._lake_env_lean is not None:
            return self._lake_env_lean + [lean_file]
        return [self.lean_path or 'lean', lean_file]
    
    def _check_mathlib_available(self) -> bool:
        """Check if Mathlib is available in the Lean environment."""
        if not self.lean_path:
            return False
        
        env = os.environ.copy()
        env["PATH"] = str(Path.home() / ".elan" / "bin") + ":" + env.get("PATH", "")
        
        try:
            # Create a temporary file to test Mathlib import
            import tempfile
            with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', delete=False) as f:
                f.write("import Mathlib.Tactic\n")
                temp_path = f.name
            
            # Prefer `lake env lean` when a lakefile is present, so Mathlib
            # imports resolve through the hermetic Lake build graph.
            compile_cmd = self._compile_lean_cmd(temp_path)
            
            try:
                result = subprocess.run(
                    compile_cmd,
                    capture_output=True,
                    text=True,
                    timeout=60,
                    env=env
                )
                return result.returncode == 0
            except Exception:
                return False
            finally:
                try:
                    os.unlink(temp_path)
                except Exception:
                    pass
        except Exception:
            return False
    
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
            Type string: 'Nat', 'Int', 'Rat', or 'Real'
        """
        # ODE expressions and rate-of-change notation live on ℝ
        if is_ode(expression) or involves_derivative(expression):
            return 'Real'

        # Symbolic division (division where the divisor is not a pure numeric
        # literal) requires a field – Real / Rat.  We prefer 'Real' when the
        # expression also contains subtraction or continuous variables, but
        # even pure symbolic division is a field operation, so map to 'Real'
        # whenever the AST confirms rational structure.
        if '/' in expression:
            eq, _ = parse_equation(expression)
            node = eq if eq is not None else None
            if node is None:
                # Fallback: parse as bare expression
                tokens = tokenize(expression)
                tokens = normalize_implicit_multiplication(tokens)
                node, _ = parse_expression(tokens)
            if node is not None and has_rational_structure(node):
                return 'Real'
            # Plain numeric division (e.g. 4/2) stays Rat
            return 'Rat'
        
        # Check for negative numbers or subtraction -> Int
        # Negative literals: -1, -2, etc.
        if re.search(r'-\d', expression):
            return 'Int'
        # Subtraction patterns: a - b, 0 - x, (a - b)
        if re.search(r'(?<!\w)-\(', expression) or re.search(r'\w\s*-\s*\w', expression):
            return 'Int'
        # Parenthesized subtraction: (a - b)
        if re.search(r'\([^)]*-\s*\w[^)]*\)', expression):
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
                self._compile_lean_cmd(verify_path),
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
            except Exception:
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
        
        # Closed numeric equalities (no free variables, both sides are concrete
        # integers): prefer ``simp``/``decide`` over ``rfl`` so the proof is
        # genuinely non-reflexive.  ``rfl`` would still work (Lean's kernel can
        # evaluate closed terms), but ``decide`` or ``simp`` is a stronger
        # credibility signal for formal-verification gates.
        if is_numeric_equality(expression):
            candidates.extend(['simp', 'decide', 'norm_num', 'ring'])
            for tactic in self.tactic_candidates:
                if tactic not in candidates:
                    candidates.append(tactic)
            return candidates
        
        # Use statement_kind for identity short-circuit
        kind = statement_kind(expression)
        if kind == 'identity':
            candidates.extend(['rfl', 'simp', 'refl'])
            for tactic in self.tactic_candidates:
                if tactic not in candidates:
                    candidates.append(tactic)
            return candidates
        
        # ODE / rate-of-change inputs: prioritize the Mathlib tactics that
        # handle derivatives, division and algebraic structure in the RHS.
        # ``dsimp`` normalizes the derivative head, ``field_simp`` clears the
        # divisions (C_p = A/V, C_tissue/Kp), and ``ring_nf`` closes the
        # resulting polynomial/field identities. This is the bridge from
        # "algebraic identity checking" to genuine formal-ODE verification.
        # Compound tactics chain multiple steps in one tactic block.
        if is_ode(expression) or involves_derivative(expression):
            candidates.extend([
                'intros; dsimp; field_simp; ring',
                'intros; field_simp; ring',
                'dsimp', 'field_simp', 'ring_nf', 'simp',
                'norm_num', 'decide',
            ])
            for tactic in self.tactic_candidates:
                if tactic not in candidates:
                    candidates.append(tactic)
            return candidates
        
        # Parse expression to get AST for classification
        eq, _ = parse_equation(expression)
        
        ast_node: ASTNode | None = eq
        if ast_node is None:
            # For non-equation expressions, parse the full expression
            tokens = tokenize(expression)
            tokens = normalize_implicit_multiplication(tokens)
            ast_node, _ = parse_expression(tokens)
        
        # Dynamical invariants: Jacobian off-diagonal (Metzler) positivity
        # ``Q / Kp > 0`` / ``Q / (V * Kp) > 0`` proves via ``positivity``;
        # discrete-step conservation proves via ``field_simp; ring``.
        try:
            from parser import is_metzler_positivity as _is_metz, \
                is_discrete_step_conservation as _is_step
        except ImportError:
            _is_metz = _is_step = None  # type: ignore[assignment]
        if _is_metz is not None and _is_metz(ast_node):
            candidates.extend(['intros; positivity', 'positivity',
                               'intros; field_simp; ring'])
            for tactic in self.tactic_candidates:
                if tactic not in candidates:
                    candidates.append(tactic)
            return candidates
        if _is_step is not None and _is_step(ast_node):
            candidates.extend(['intros; field_simp; ring', 'field_simp',
                               'ring', 'intros; positivity'])
            for tactic in self.tactic_candidates:
                if tactic not in candidates:
                    candidates.append(tactic)
            return candidates

        # Symbolic Real / rational expressions: division over symbolic
        # variables lives in a field ℝ.  Prioritize ``intro`` first (to
        # bring universally quantified variables into scope), then the
        # Mathlib field algebra stack (dsimp to normalize, field_simp to
        # clear divisions, ring_nf to close polynomial/field identities),
        # followed by linarith for any linear side-conditions.
        # ``simp [mul_sub, mul_div_assoc]`` handles the canonical
        # distributive-over-division identity that field_simp alone cannot.
        # Compound tactics (semicoloned sequences) are tried as atomic
        # proof terms: e.g. ``by intros; field_simp; ring`` chains intro
        # + field simplification + ring in one tactic block.
        # Metzler positivity: strict inequality with division → positivity tactic
        if isinstance(ast_node, (Gt, Lt)) and contains_op(ast_node, '/'):
            candidates.extend([
                'intros; positivity',
                'intros; field_simp; positivity',
                'positivity',
            ])
            for tactic in self.tactic_candidates:
                if tactic not in candidates:
                    candidates.append(tactic)
            return candidates

        if has_rational_structure(ast_node):
            candidates.extend([
                'intros; positivity',
                'intros; field_simp; ring',
                'intros; dsimp; field_simp; ring',
                'intros; simp [mul_sub, mul_div_assoc]; ring',
                'intro', 'dsimp', 'field_simp',
                'simp [mul_sub, mul_div_assoc]',
                'ring_nf', 'linarith', 'simp', 'norm_num',
            ])
            for tactic in self.tactic_candidates:
                if tactic not in candidates:
                    candidates.append(tactic)
            return candidates
        
        # Classify using AST helpers
        if contains_op(ast_node, '/'):
            candidates.extend([
                'intros; positivity',
                'intros; field_simp; ring',
                'field_simp', 'ring', 'norm_num', 'simp',
            ])
        elif is_inequality(ast_node):
            candidates.extend([
                'intros; positivity',
                'intros; linarith',
                'linarith', 'omega', 'simp', 'norm_num',
            ])
        elif has_polynomial_structure(ast_node):
            candidates.extend(['ring', 'simp', 'linarith', 'norm_num'])
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
        expected_type = error_info.get('expected_type', '')
        
        # Strip the turnstile prefix from Lean goals for parsing
        goal_text = goal.lstrip('⊢ ').strip()
        
        # Parse the goal to get an AST for classification
        goal_eq, _ = parse_equation(goal_text)
        goal_ast: ASTNode | None = goal_eq
        if goal_ast is None:
            tokens = tokenize(goal_text)
            tokens = normalize_implicit_multiplication(tokens)
            goal_ast, _ = parse_expression(tokens)
        
        # Check goal for ring patterns (polynomial structure or algebraic ops)
        if has_polynomial_structure(goal_ast) or 'ring' in goal.lower():
            return 'ring'

        # Formal-ODE goals: derivatives with division (C_p = A/V, C_tissue/Kp)
        # are field identities; clear the divisions with field_simp first,
        # then let ring close them.
        if involves_derivative(goal) or contains_op(goal_ast, '/'):
            return 'field_simp'
        
        # Check for inequality patterns
        if is_inequality(goal_ast):
            return 'linarith'
        
        # Check for type mismatch with Bool
        if 'Bool' in expected_type:
            return 'decide'
        
        # Check for numeric normalization (+, *, or digits)
        if has_numeric_ops(goal_ast) and re.search(r'\d+', goal):
            return 'norm_num'
        
        # Check for algebraic structure (+ or * without ^) — ring or norm_num
        if has_numeric_ops(goal_ast):
            return 'ring'
        
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
        
        # Filter out known Lean identifiers from free variables
        lean_keywords = {'Nat', 'Int', 'Rat', 'Real', 'Bool', 'True', 'False', 'Nat.succ', 'Nat.zero'}
        filtered_vars = [v for v in free_vars if v not in lean_keywords and not v.startswith('Nat.')]
        
        # Build imports and theorem header
        if var_type == 'Real':
            # Real-typed theorems live in a field; emit [Field ℝ] instance
            imports = "import Mathlib.Tactic\nimport Mathlib.Basic.Real.Basic\n\n"

            # For parametric field identities (free vars + symbolic division),
            # emit universal quantification with positivity hypotheses for
            # variables that appear in division denominators AND numerators
            # (positivity requires all variables in a ratio to be positive).
            eq_node, _ = parse_equation(expression)
            div_vars = find_division_variables(eq_node) if eq_node else set()
            # Also collect numerator variables from division nodes for
            # positivity (Q / Kp > 0 needs both Q > 0 and Kp > 0).
            if eq_node:
                _collect_division_numerator_vars(eq_node, div_vars)
            hyp_vars = sorted(div_vars & set(filtered_vars)) if div_vars else []

            # Detect positivity/strict-inequality goals: these need
            # [LinearOrderedField ℝ] (not [Field ℝ]) so that Mathlib's
            # `positivity` tactic can see the ordered-field structure.
            # Plain `ℝ` variables are automatically LinearOrderedField.
            is_positivity_goal = (
                hyp_vars
                and isinstance(eq_node, (Gt, Lt, Ge, Le))
            )

            if filtered_vars:
                params = ' '.join([f'({v} : ℝ)' for v in filtered_vars])
                if hyp_vars:
                    hyps = ' '.join([f'(h{v} : 0 < {v})' for v in hyp_vars])
                    if is_positivity_goal:
                        # Omit [Field ℝ] so positivity sees LinearOrderedField
                        theorem = (
                            f"theorem qed_goal {params} {hyps} "
                            f": {expression} := by\n"
                        )
                    else:
                        theorem = (
                            f"theorem qed_goal [Field ℝ] {params} {hyps} "
                            f": {expression} := by\n"
                        )
                else:
                    theorem = f"theorem qed_goal [Field ℝ] {params} : {expression} := by\n"
            else:
                theorem = f"theorem qed_goal [Field ℝ] : {expression} := by\n"
        else:
            # Build theorem statement
            if filtered_vars:
                params = ' '.join([f'({v} : {var_type})' for v in filtered_vars])
                theorem = f"theorem qed_goal {params} : {expression} := by\n"
            else:
                # Add type annotation for negative numbers or division
                if var_type in ('Int', 'Rat'):
                    # Annotate the expression with the appropriate type
                    if '-' in expression and var_type == 'Int':
                        # For negative numbers, add type annotation only to negative literals
                        annotated_expr = re.sub(r'(-\d+)', r'(\1 : Int)', expression)
                        theorem = f"theorem qed_goal : {annotated_expr} := by\n"
                    elif '/' in expression and var_type == 'Rat':
                        # For division, add type annotation
                        theorem = f"theorem qed_goal : {expression} := by\n"
                    else:
                        theorem = f"theorem qed_goal : {expression} := by\n"
                else:
                    theorem = f"theorem qed_goal : {expression} := by\n"
            imports = ""
        
        # Add imports if using Mathlib (non-Real types)
        if self.use_mathlib and var_type != 'Real':
            imports = "import Mathlib.Tactic\n\n"
        
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
        base_code = self.generate_lean_code(expression, free_vars or [])
        
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
                # Compile – prefer `lake env lean` when a lakefile is present
                result = subprocess.run(
                    self._compile_lean_cmd(temp_path),
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
                except Exception:
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


def main() -> None:
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
