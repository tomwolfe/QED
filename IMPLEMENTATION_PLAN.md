# QED Implementation Plan

## Overview

This document outlines the implementation plan to fix the QED Lean 4 agentic pipeline based on the comprehensive review. The project currently has good architecture but the core functionality is mostly stubbed out. This plan will guide the implementation of a working MVP that can convert simple arithmetic statements into verified Lean 4 proofs without using `sorry`.

## Current State Assessment

Based on the review, the project is approximately **10-20% complete** relative to its stated mission. Key issues:

1. **Validator is too permissive** - accepts "hello world" as mathematical input
2. **No real LaTeX parsing** - input is directly interpolated into Lean
3. **Tactic loop doesn't modify proofs** - selects tactics but never writes them
4. **Success is not properly verified** - `sorry` can be treated as success
5. **Missing imports and declarations** - no `import Mathlib.Tactic`, no variable quantification
6. **Tests don't verify real proof generation** - only check exit codes
7. **Documentation overclaims** - describes functionality that doesn't exist

## Implementation Phases

### Phase 0: Implement Strict No-Sorry Success Criterion (HIGH PRIORITY)

**Goal**: Make failure honest before making the system smarter.

**Tasks**:
1. Modify `execute_tactic_loop()` to check for `sorry` in final output
2. Add `sorryAx` detection in compiler output
3. Update success condition to require:
   - Lean exit code == 0
   - Final Lean source contains no `sorry`
   - Compiler output contains no `sorryAx` warning
4. Add optional `#print axioms` verification

**Acceptance Criteria**:
- Pipeline never reports success if final Lean file contains `sorry`
- Pipeline never reports success if compiler output mentions `sorryAx`
- Success requires clean compilation with no warnings

### Phase 1: Implement Real Tactic Search Loop (HIGH PRIORITY)

**Goal**: Make the tactic loop actually try tactics by modifying the Lean proof.

**Tasks**:
1. Create a function to replace `sorry` with candidate tactics in Lean source
2. Implement single-tactic proof attempts:
   - Generate theorem statement
   - Try tactic candidate (e.g., `ring`)
   - Compile
   - If success and no sorry, return
   - Otherwise record error and try next candidate
3. Implement tactic selection based on statement type:
   - Concrete numeric equality → `rfl`, `simp`, `norm_num`, `decide`
   - Polynomial equality → `ring`, `simp`
   - Linear inequality → `linarith`, `omega`
   - Natural number arithmetic → `simp`, `omega`, `rfl`
4. Add proper temporary file handling with cleanup

**Acceptance Criteria**:
- Tactic loop actually modifies the Lean file for each attempt
- Each attempt compiles a different proof candidate
- First successful proof (no sorry) stops the loop
- All attempts are recorded in trace

### Phase 2: Build Small Formula Parser (HIGH PRIORITY)

**Goal**: Parse constrained arithmetic expressions instead of treating input as Lean syntax.

**Tasks**:
1. Create AST nodes for:
   - Numbers (integers, naturals)
   - Variables
   - Binary operators: +, -, *, /, ^
   - Relations: =, !=, <, <=, >, >=
   - Parentheses
   - Unary negation
2. Implement tokenizer for:
   - Numbers and variables
   - Operators
   - Parentheses
   - LaTeX-like tokens: `\cdot`, `\le`, `\ge`, `\neq`, `\frac{}{}`
3. Implement recursive descent parser
4. Handle implicit multiplication: `2ab` → `2 * a * b`
5. Identify free variables in expressions

**Acceptance Criteria**:
- Parser correctly tokenizes arithmetic expressions
- Parser produces valid AST for MVP inputs
- Implicit multiplication is handled
- LaTeX-like tokens are normalized

### Phase 3: Implement Lean Code Generation (HIGH PRIORITY)

**Goal**: Generate valid Lean 4 theorem statements with proper imports and variables.

**Tasks**:
1. Add `import Mathlib.Tactic` when Mathlib tactics are needed
2. Declare free variables as theorem parameters
3. Choose reasonable default types:
   - Only natural number literals → `Nat`
   - Negative literals or subtraction → `Int`
   - Division → `Rat` or `Real`
   - Polynomial equality → `Int` or generic `CommRing`
4. Generate valid Lean syntax with proper spacing
5. Create safe theorem names

**Examples**:
- Input: `x + 0 = x`
  Output: `theorem qed_goal (x : Nat) : x + 0 = x := by\n  simp`
- Input: `-1 + 1 = 0`
  Output: `import Mathlib.Tactic\n\ntheorem qed_goal : (-1 : Int) + 1 = 0 := by\n  norm_num`
- Input: `(a+b)^2 = a^2 + 2ab + b^2`
  Output: `import Mathlib.Tactic\n\ntheorem qed_goal (a b : Int) :\n    (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by\n  ring`

**Acceptance Criteria**:
- Generated Lean files compile without syntax errors
- Free variables are properly declared
- Appropriate types are chosen
- Imports are included when needed

### Phase 4: Add Type Inference Heuristics (MEDIUM PRIORITY)

**Goal**: Choose sensible default types for MVP inputs.

**Tasks**:
1. Implement type detection rules:
   - Only natural number literals and `Nat.succ` → `Nat`
   - Negative literals or subtraction → `Int`
   - Division → `Rat` or `Real`
   - Inequalities with algebraic variables → `Int`, `Rat`, or `Real`
   - Pure polynomial equality → `Int` or generic `CommRing`
2. For MVP, default to concrete types like `Int` for algebraic identities
3. Add type annotation to generated Lean code

**Acceptance Criteria**:
- Appropriate types are chosen based on expression content
- Generated Lean code includes proper type annotations
- MVP examples work with concrete types

### Phase 5: Implement Tactic Policy (MEDIUM PRIORITY)

**Goal**: Select tactics based on statement type.

**Tasks**:
1. Create tactic candidate lists based on statement type:
   - Concrete numeric equality: `rfl`, `simp`, `norm_num`, `decide`
   - Polynomial/algebraic equality: `ring`, `simp`, `linarith`
   - Linear arithmetic inequality: `linarith`, `omega`, `simp`
   - Natural number arithmetic: `simp`, `omega`, `ring`
   - Field expressions: `field_simp`, `ring`, `norm_num`
2. Implement ordered candidate lists (not just single tactic)
3. Add tactic combinations: `field_simp; ring`, `simp_arith`

**Acceptance Criteria**:
- Tactic selection matches statement type
- Multiple candidates are tried in order
- First successful tactic stops the search

### Phase 6: Improve Lean Environment Handling (MEDIUM PRIORITY)

**Goal**: Support both core-only and Mathlib modes.

**Tasks**:
1. Detect whether `lean` is available
2. Support PATH inclusion for elan
3. Add CLI options:
   - `--core-only`: Use only built-in tactics
   - `--use-mathlib`: Require Mathlib
   - `--lean-workspace PATH`: Specify Lake workspace
   - `--trace-file PATH`: Specify trace output file
4. Support `lake env lean` for Mathlib environments
5. Fail clearly if Mathlib is required but unavailable

**Acceptance Criteria**:
- Pipeline works in core-only mode
- Pipeline works with Mathlib when available
- Clear error messages when requirements are missing

### Phase 7: Implement Persistent Tracing (MEDIUM PRIORITY)

**Goal**: Write traces.json on every run.

**Tasks**:
1. Write traces.json for both success and failure
2. Include in trace:
   - Timestamp
   - Original input
   - Validation result
   - Parsed AST/normalized formula
   - Generated Lean statement
   - Each proof attempt
   - Each tactic candidate
   - Compiler exit code
   - Stdout/stderr excerpts
   - Parsed error information
   - Final status
   - Final output path
   - Reason for failure if failed

**Acceptance Criteria**:
- traces.json is written on every run
- Trace contains complete audit trail
- Trace is human-readable JSON

### Phase 8: Add Comprehensive Test Suite (MEDIUM PRIORITY)

**Goal**: Tests should verify actual proof generation, not just CLI behavior.

**Tasks**:
1. Create unit tests for parser and code generator:
   - Parse expressions
   - Emit Lean code
   - Check variable detection
   - Check type selection
2. Create integration tests with Lean:
   - Verify compilation
   - Check no sorry in output
   - Verify traces are written
3. Create failure tests:
   - Invalid inputs fail validation
   - Unsupported inputs fail cleanly
   - Traces written on failure
4. Separate integration tests that can be skipped if Lean/Mathlib unavailable
5. Add mock Lean tests for CI

**Test Cases**:
- Validation: empty input fails, "hello world" fails, "0 = 0" passes
- Code generation: proper variable declaration, type selection, imports
- Proof success: "0 = 0", "Nat.succ 0 = 1", "x + 0 = x", "-1 + 1 = 0"
- Mathlib-dependent: "(a+b)^2 = a^2 + 2ab + b^2" with `ring`
- Failure behavior: unsupported inputs, traces written, no false success

**Acceptance Criteria**:
- Tests verify actual proof generation
- Tests check for no sorry in output
- Tests are runnable without Lean (with appropriate skips)
- All tests pass

### Phase 9: Update Documentation (LOW PRIORITY)

**Goal**: Documentation should match reality.

**Tasks**:
1. Update README.md to describe:
   - Supported input language (constrained arithmetic)
   - Required Lean/Mathlib setup
   - Actual success criteria
   - Current limitations
   - How to run tests
   - How to interpret traces.json
2. Update IMPLEMENTATION_SUMMARY.md to reflect actual capabilities
3. Remove claims that are not yet true
4. Add examples of actual verified output

**Acceptance Criteria**:
- Documentation accurately describes current capabilities
- No overclaiming
- Examples show actual verified proofs

## MVP Definition

### Input Language

The system accepts arithmetic equalities and inequalities over:
- Integer literals
- Natural number literals
- Variables
- Operators: +, -, *, /, ^
- Parentheses
- Implicit multiplication: `2ab`
- LaTeX-like tokens: `\cdot`, `\le`, `\ge`, `\neq`, `\frac{}{}`

### Output

- Valid Lean file with necessary imports
- Explicit theorem parameters
- Completed proof
- No `sorry`

### Success Criteria

- Lean compiler exit code is 0
- Final Lean source contains no `sorry`
- Compiler output contains no `sorryAx` warning

### Tactic Set

MVP supports:
- `rfl`
- `simp`
- `norm_num`
- `ring`
- `linarith`
- `omega`
- `field_simp`

## Implementation Order

1. **Phase 0**: No-sorry gate (make failure honest)
2. **Phase 1**: Real tactic attempts (make loop actually work)
3. **Phase 2**: Basic parser/codegen (generate valid Lean)
4. **Phase 3**: Lean environment handling (make tactics usable)
5. **Phase 7**: Persistent traces (make system debuggable)
6. **Phase 8**: Better tests (prove pipeline works)
7. **Phase 9**: Documentation cleanup (align claims with evidence)
8. **Phase 4**: Type inference heuristics (improve type selection)
9. **Phase 5**: Tactic policy (improve tactic selection)

## Success Examples

### Example 1: Simple Equality

Input:
```bash
python3 agentic_pipeline.py "0 = 0"
```

Generated Lean:
```lean
theorem qed_goal : 0 = 0 := by
  rfl
```

Result: ✓ Verification Successful! (no sorry)

### Example 2: Nat Arithmetic

Input:
```bash
python3 agentic_pipeline.py "Nat.succ 0 = 1"
```

Generated Lean:
```lean
theorem qed_goal : Nat.succ 0 = 1 := by
  rfl
```

Result: ✓ Verification Successful! (no sorry)

### Example 3: Variable Identity

Input:
```bash
python3 agentic_pipeline.py "x + 0 = x"
```

Generated Lean:
```lean
theorem qed_goal (x : Nat) : x + 0 = x := by
  simp
```

Result: ✓ Verification Successful! (no sorry)

### Example 4: Negative Numbers

Input:
```bash
python3 agentic_pipeline.py "-1 + 1 = 0"
```

Generated Lean:
```lean
import Mathlib.Tactic

theorem qed_goal : (-1 : Int) + 1 = 0 := by
  norm_num
```

Result: ✓ Verification Successful! (no sorry)

### Example 5: Polynomial Identity (Mathlib required)

Input:
```bash
python3 agentic_pipeline.py "(a+b)^2 = a^2 + 2ab + b^2"
```

Generated Lean:
```lean
import Mathlib.Tactic

theorem qed_goal (a b : Int) :
    (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring
```

Result: ✓ Verification Successful! (no sorry)

## Acceptance Criteria

1. Running `python3 agentic_pipeline.py "hello world"` exits nonzero and reports validation failure.

2. Running `python3 agentic_pipeline.py ""` exits nonzero and reports validation failure.

3. Running `python3 agentic_pipeline.py "0 = 0"` produces a Lean file with no sorry and exits 0 if Lean is available.

4. Running `python3 agentic_pipeline.py "Nat.succ 0 = 1"` produces a Lean file with no sorry and exits 0 if Lean is available.

5. Running `python3 agentic_pipeline.py "x + 0 = x"` produces a Lean file where x is explicitly declared, with no sorry, and exits 0 if Lean is available.

6. Running `python3 agentic_pipeline.py "-1 + 1 = 0"` produces a Lean file using a type that supports negation, with no sorry, and exits 0 if Lean is available.

7. If Mathlib is available, running `python3 agentic_pipeline.py "(a+b)^2 = a^2 + 2ab + b^2"` produces a Lean file with explicit variables and a real proof such as `ring`, with no sorry.

8. If Mathlib is not available, the previous command must either:
   - use a core-only proof if possible, or
   - fail with a clear message explaining that Mathlib is required.
   It must not output a sorry and claim success.

9. traces.json is written for both successful and failed runs.

10. The test suite passes without relying on false expectations.

## Definition of Done

- The pipeline no longer treats sorry as success.
- The tactic loop actually tries proof candidates.
- The generated Lean code is syntactically valid.
- The repository contains tests proving the core behavior.
- Documentation matches reality.
- The final output of a successful run is a Lean file that can be compiled independently and contains no sorry.
