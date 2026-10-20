# Lean 4 Agentic Pipeline - Implementation Summary

## Mission Status: HARDENED MVP IMPLEMENTED ✓

### System Overview
A CLI-based agentic pipeline that converts constrained mathematical statements (in a LaTeX-like syntax) into verified Lean 4 code using iterative tactic search. The pipeline enforces strict verification: success requires the final Lean file to compile without `sorry` placeholders.

### Key Features Implemented

1. **Input Validation** ✓
   - Regex-based parsing of LaTeX mathematical statements
   - Rejects ambiguous or non-mathematical input (e.g., "hello world", empty input)
   - Accepts MVP inputs: "0 = 0", "Nat.succ 0 = 1", "x + 0 = x", "(a+b)^2 = a^2 + 2ab + b^2", "-1 + 1 = 0", "x < x + 1"

2. **Lean 4 Integration** ✓
   - Direct compilation of generated Lean files
   - Proper PATH configuration for elan toolchain
   - Support for Lean 4 via elan
   - Graceful handling when Lean is not installed

3. **Agentic Tactic Search** ✓
   - Automatic tactic ordering based on parsed AST structure
   - Supported tactics: rfl, simp, norm_num, decide, ring, linarith, omega, field_simp
   - Max 15 iterations to prevent token spiraling
   - **Critical**: Each tactic attempt actually modifies the Lean proof; success requires no `sorry` in final output

4. **Error Capture & Handling** ✓
   - Captures both stdout and stderr from Lean compiler
   - Checks exit code and detects `sorry`/`sorryAx` in compiler output
   - Records detailed attempt history for audit trail

5. **Strict No-Sorry Success Criterion** ✓ (Hardened via Tether Mission qed-01)
   - Pipeline never reports success if final Lean file contains `sorry`
   - Pipeline never reports success if compiler output mentions `sorryAx`
   - Comprehensive pattern matching for `Tactic.sorry`, `Lean.Elab.Tactic.sorry`
   - Post-compilation source re-read verification
   - Fail-closed axiom verification when Lean is unavailable
   - Success requires: Lean exit code == 0 AND no `sorry` in source AND no `sorryAx` in compiler output

6. **Audit Trail** ✓
   - Detailed JSON logging of all attempts
   - Tracks iterations, exit codes, sorry reasons, and selected tactics
   - Writes `traces.json` on both success and failure

7. **Formula Parser (Hardened)** ✓ (Hardened via Tether Mission qed-02)
   - Recursive descent parser for MVP arithmetic expressions
   - Parses binary operators: +, -, *, /, ^
   - Parses relations: =, !=, <, <=, >, >=
   - Supports nested parentheses via recursive descent
   - Normalizes implicit multiplication: "2ab" -> "2 * a * b", "3xyz" -> "3 * x * y * z"
   - Handles paren-adjacent multiplication: "(a+b)2", "2(a+b)", "(a+b)(c+d)"
   - Keeps multi-character names intact: "ka_rate", "A_1ab", "Nat.succ" are one name
   - Supports LaTeX-like tokens: \cdot, \times, \div, \le, \leq, \lt, \ge, \geq, \gt,
     \neq, \ne, \frac, \dfrac, \tfrac, \left/\right, braced powers/subscripts ("a^{2}", "x_{1}")
   - Fails closed on anything outside that vocabulary: a stray character, an unknown macro
     ("\pm", "\alpha") or a malformed parenthesis is rejected, never approximated
   - Handles dotted identifiers like `Nat.succ`
   - Identifies free variables in expressions
   - Produces intermediate AST representation

8. **Lean Code Generation** ✓ (Hardened via Tether Mission qed-03)
   - Generates valid Lean 4 theorem statements
   - Adds `import Mathlib.Tactic` when Mathlib tactics are needed
   - Declares free variables as theorem parameters
   - Chooses type-appropriate defaults from the statement's AST (see 10)
   - Generates valid Lean syntax with proper spacing
   - Ascribes the type of a closed statement inside the statement, so Lean
     elaborates it at the type the pipeline inferred

9. **Tactic Policy (AST-Aware)** ✓ (Hardened via Tether Mission qed-04)
   - Tactic candidates selected based on parsed AST structure (not keyword-based)
   - Uses helper functions: `contains_op()`, `is_inequality()`, `has_polynomial_structure()`
   - Division expressions -> field_simp first
   - Inequality expressions -> linarith/omega first
   - Polynomial/algebraic expressions -> ring first
   - Identity statements (both sides structurally equal) short-circuit to rfl/simp
   - Otherwise defaults to: rfl, simp, norm_num, decide, ring, then remaining candidates
   - Selection is purely AST-driven; there is no special-casing for variable presence or sign

10. **Type Inference (Context-Aware)** ✓ (Hardened via Tether Mission qed-03)
    - The type is the JOIN of the requirements the statement's AST imposes,
      over the lattice Nat < Int < Rat < Real: a statement that mixes a
      division with a negation is read at the strongest type any of its
      parts needs
    - The requirements are read off the AST, not off the text: a negative
      LITERAL, a binary subtraction, a numeric denominator and a symbolic
      denominator are four different things, and the text heuristics could
      not tell them apart
    - _suggest_type returns the joined type; _get_var_type returns the type
      to EMIT (open statements carry it in the variable declarations, closed
      statements get it ascribed inside the statement)
    - Proper type selection prevents Lean type mismatch errors, and stops
      the pipeline from "verifying" a statement that is false in the type
      it claimed (Nat subtraction and division truncate)

### Test Results (comprehensive unit tests passing)

**Parser Hardening Tests** ✓
- "2ab" normalized correctly to "2 * a * b" ✓
- "3xyz" normalized correctly to "3 * x * y * z" ✓
- "(a+b)2" handled as "(a+b) * 2" ✓
- "(a+b)(c+d)" handled as "(a+b) * (c+d)" ✓
- "2(a+b)" handled as "2 * (a+b)" ✓
- "ab + cd" handled as "a * b + c * d" ✓
- Nested parens parsed correctly ✓
- Dotted identifiers (Nat.succ) handled correctly ✓

**Type Inference Tests** ✓
- "x + 0 = x" suggests type "Nat" ✓
- "-1 + 1 = 0" suggests type "Int" ✓
- "x / 2 = y" suggests type "Rat" ✓
- "a * b = c" suggests type "Nat" (a product equality needs no field) ✓
- "x / (2 + 1) = y" suggests type "Rat" (a numeric denominator is exact) ✓
- "x / y = z" suggests type "Real" (a symbolic denominator is a field) ✓
- Mixed statements join their requirements ("x / 2 - 1 = 0" is "Rat") ✓
- Proper type annotations generated ✓
- A closed statement is ascribed at the inferred type, so Lean elaborates it
  there: "1 - 2 = 0" is no longer "verified" by Nat truncation ✓

**Tactic Selection Tests** ✓
- Algebraic expressions get ring as first candidate ✓
- Inequality expressions get linarith as first candidate ✓
- Division expressions get field_simp as first candidate ✓
- Goal-based tactic selection works for ring patterns ✓
- Goal-based tactic selection works for inequality patterns ✓
- AST-based classification works correctly ✓

**Sorry Detection Tests** ✓
- Source contains sorry ✓
- Source contains sorryAx ✓
- Source contains Tactic.sorry ✓
- Source contains Lean.Elab.Tactic.sorry ✓
- Compiler: declaration uses sorry ✓
- Compiler: uses sorryAx ✓
- Word boundary: sorrier no false positive ✓
- Axiom verification fail-closed ✓

### Technical Implementation

#### File Structure:
```
.
├── agentic_pipeline.py    # Main pipeline with intelligent tactic selection
├── parser.py              # Hardened recursive descent parser
├── test_pipeline.py          # comprehensive unit tests
├── run_tests.py           # End-to-end test suite
├── check_sorry.py         # Helper script for sorry detection verification
├── check_parser.py        # Helper script for parser verification
├── check_type.py          # Helper script for type inference verification
├── check_tactic.py        # Helper script for tactic selection verification
├── missions/              # Tether mission files
│   ├── qed-01-no-sorry-gate.yaml
│   ├── qed-02-parser-hardening.yaml
│   ├── qed-03-type-inference.yaml
│   ├── qed-04-tactic-policy.yaml
│   ├── qed-05-integration-validation.yaml
│   └── qed-unit-tests-pass.yaml
├── README.md              # Documentation
├── IMPLEMENTATION_SUMMARY.md  # This file
├── LICENSE                # MIT License
├── tether.yaml            # Tether orchestration config
└── traces.json            # Generated audit trail
```

#### Success Criteria (Strict):
```text
Lean compiler exit code == 0
AND final Lean source contains no "sorry"
AND compiler output contains no "sorryAx"
```

#### Supported Inputs:
- "0 = 0" (trivial equality)
- "Nat.succ 0 = 1" (natural number successor)
- "x + 0 = x" (variable identity)
- "-1 + 1 = 0" (negative numbers with Int type)
- "(a+b)^2 = a^2 + 2ab + b^2" (polynomial identity, needs Mathlib)
- "x < x + 1" (inequality)
- "x / 2 = y" (division with Rat type)

#### Supported Tactics:
- rfl (reflexivity)
- simp (simplification)
- norm_num (normalization of number literals)
- decide (decision procedure)
- ring (algebraic simplifications)
- linarith (linear arithmetic)
- omega (quantifier elimination)
- field_simp (field simplification)

### Known Limitations
- Requires Mathlib4 for some tactics (ring, linarith, omega)
- Limited to constrained arithmetic expressions (not arbitrary LaTeX)
- The parser accepts the LaTeX-like vocabulary above, but the Lean code generator
  interpolates the statement *as written*: a statement that uses LaTeX-only
  syntax (`\le`, `\frac`, `a^{2}`) parses, and is then rejected by the Lean
  compiler. Write the statement in Lean-compatible syntax to have it proved.
- Type inference is heuristic-based, not full typeclass synthesis
- Lean 4 toolchain must be available via elan
- Complex proofs requiring deep tactic sequences may need manual intervention

### Tether Missions Executed
The following Tether missions were executed to harden the pipeline:

1. **qed-unit-tests-pass**: Verified all unit tests pass and pipeline handles missing Lean gracefully
2. **qed-01-no-sorry-gate**: Hardened sorry detection with comprehensive patterns and fail-closed axiom verification
3. **qed-02-parser-hardening**: Hardened the parser: dotted identifiers, unary negation before
   parentheses, word-boundary rules that keep multi-character names intact, LaTeX macro expansion
   (control words end at the first non-letter, so a longer control word can never leak its tail
   into the statement), braced powers/subscripts, and a fail-closed tokenizer
4. **qed-03-type-inference**: Verified type inference and proper type annotations
5. **qed-04-tactic-policy**: Refactored tactic selection to use AST-based classification
6. **qed-05-integration-validation**: End-to-end verification with real Lean 4 compiler (v4.0.0) - all 18 end-to-end tests pass

### Conclusion
The Lean 4 Agentic Pipeline has been hardened from an MVP to a more robust implementation. Key improvements:
- Parser now correctly handles implicit multiplication chains, paren-adjacent operations, nested parentheses, and dotted identifiers
- Type inference produces context-appropriate types (Nat/Int/Rat) instead of defaulting to Int
- Tactic selection uses parsed AST structure for smarter ordering (not keyword-based)
- Sorry detection has been hardened with comprehensive patterns and fail-closed axiom verification
- comprehensive unit tests verify all improvements
- Pipeline gracefully handles missing Lean compiler
- End-to-end integration verified with real Lean 4 compiler: 0=0, Nat.succ 0=1, x+0=x, -1+1=0 all verify without sorry
- Mathlib auto-detection: falls back to core-only tactics when Mathlib is unavailable

### qed-00-toolchain-consistency

Three separate things, recorded narrowly and empirically.

**1. The toolchain pin (`v4.34.0-rc2` -> `v4.33.0`).**
`lean-toolchain` is `leanprover/lean4:v4.33.0` and `lakefile.lean` requires mathlib at
the matching tag `v4.33.0`. The pin is deliberate: the `v4.34.0-rc2` `lake` binary
SIGTRAPs (exit 133) on arm64 Darwin 27 for *every* invocation, so nothing runs
under it. At the pinned `v4.33.0`, `lake --version` exits 0 normally. mathlib
follows the toolchain so the pair is known-good together.

**2. The import rename -- this was the actual defect.**
`generate_lean_code` emitted a Real-typed header importing
`Mathlib.Basic.Real.Basic`. That module does not exist at mathlib `v4.33.0`
(there is no `Mathlib/Basic/Real/Basic.lean` in the pinned source tree), so every
generated Real theorem failed to compile:

```text
error: failed to read file '.../Mathlib/Basic/Real/Basic.olean', incompatible header
```

The header now imports `Mathlib.Data.Real.Basic`, the canonical module, which does
exist at `v4.33.0`. One correct import -- no version probe, no fallback chain. No
other import was touched: `Mathlib.Tactic` (the Mathlib-availability probe and the
non-Real path) is unchanged, and no other import was found missing at `v4.33.0`.

**3. Stale build artifact (cleanup, not the fix).**
A `Mathlib/Basic/Real/Basic.olean` tree dated Sep 5 remained under `.lake/` from the
old toolchain; it was untracked and gitignored. It was removed as cleanup only. The
rename is the fix: the 10 previously-failing tests went green with that stale tree
still on disk, and `lake build` afterwards did not attempt to rebuild it (those
modules do not exist in the pinned source).

**Empirical pytest counts** (`python3 -m pytest test_pipeline.py -q`, same machine):

| | Result |
|---|---|
| Before | 10 failed, 248 passed |
| After | 258 passed |

The 10 that flipped were the parametric/Real-typed goals, all of which had been
failing on `incompatible header` rather than on the mathematics. No test was
skipped, xfailed, relaxed or deleted, and no `sorry` was introduced. `run_tests.py`
remains 18/18.

**4. `generate_lean_code(expression, free_vars=None)`.**
`free_vars` is now optional and defaults to `None`, normalised to `[]`. Every
existing caller (`execute_tactic_loop`, `test_pipeline.py`, `check_type.py`) already
passed it explicitly, so no call site or generated theorem changed; this only makes
`generate_lean_code(expr)` a valid one-argument call. It does not affect the type
inference, which already derives the variable type from the expression alone.
