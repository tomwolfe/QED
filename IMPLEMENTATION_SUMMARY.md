# Lean 4 Agentic Pipeline - Implementation Summary

## Mission Status: HARDENED MVP + DOCS-TRUTH AUDIT ✓

### System Overview
A CLI-based agentic pipeline that converts constrained mathematical statements (in a LaTeX-like syntax) into verified Lean 4 code using iterative tactic search. The pipeline enforces strict verification: success requires the final Lean file to compile without `sorry` placeholders.

### Key Features Implemented

1. **Input Validation** ✓
   - Regex screen for obviously non-mathematical text, then a recursive-descent parse of the statement
   - Rejects ambiguous or non-mathematical input (e.g., "hello world", empty input)
   - Accepts MVP inputs: "0 = 0", "Nat.succ 0 = 1", "x + 0 = x", "(a+b)^2 = a^2 + 2ab + b^2", "-1 + 1 = 0", "x < x + 1" (see *Supported Inputs*)

2. **Lean 4 Integration** ✓
   - Direct compilation of generated Lean files
   - Proper PATH configuration for elan toolchain
   - Version pinned by `lean-toolchain` (`leanprover/lean4:v4.34.0-rc2`); elan downloads it on first use
   - When a `lakefile.lean` is found, compiles via the elan-shimmed `lean` with an explicit `LEAN_PATH` over the Lake olean roots (bypasses crash-prone `lake env`)
   - Graceful handling when Lean is not installed

3. **Agentic Tactic Search** ✓
   - Automatic tactic ordering based on parsed AST structure (see feature 9)
   - Base tactic pool: rfl, simp, norm_num, decide, ring, linarith, omega, field_simp, dsimp, intro, positivity
   - AST classification also proposes refl, ring_nf, `simp [mul_sub, mul_div_assoc]`, and compound semicolon chains (e.g. `intros; field_simp; ring`) tried as a single proof block
   - Max 15 iterations by default to prevent token spiraling; the budget is configurable per run with `--max-iterations N`
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
   - Fail-closed axiom verification: `#print axioms qed_goal` is run on every candidate proof, and any failure (unreadable file, crashed compiler, timeout) is reported as not-clean
   - Success requires all three gates: Lean exit code == 0 AND no `sorry`/`sorryAx` in the source and compiler output (including a post-compilation re-read from disk) AND `#print axioms qed_goal` reports no sorry axiom

6. **Audit Trail** ✓
   - Detailed JSON logging of all attempts
   - Tracks iterations, exit codes, sorry reasons, and selected tactics
   - Writes `traces.json` on both success and failure; the CLI also prints the attempt list to stdout on failure

7. **Formula Parser (Hardened)** ✓ (Hardened via Tether Mission qed-02)
   - Recursive descent parser for MVP arithmetic expressions
   - Parses binary operators: +, -, *, /, ^
   - Parses relations: =, !=, <, <=, >, >=
   - Supports nested parentheses via recursive descent
   - Normalizes implicit multiplication: "2ab" -> "2 * a * b", "3xyz" -> "3 * x * y * z" (the normalized form is what gets emitted — see *Supported Inputs*)
   - Handles paren-adjacent multiplication: "(a+b)2", "2(a+b)", "(a+b)(c+d)"
   - Expands LaTeX-like tokens before parsing: `\frac{a}{b}` -> `(a) / (b)`, `\cdot`/`\times` -> `*`, `\div` -> `/`, `\le`/`\leq` -> `<=`, `\ge`/`\geq` -> `>=`, `\neq`/`\ne` -> `!=`
   - Recognizes the Unicode equivalents `×`, `÷`, `≤`, `≥`, `≠`, `−`
   - Fails closed on unsupported macros instead of leaking them into the generated Lean code
   - Handles dotted identifiers like `Nat.succ`
   - Recognizes ODEs of the form `d<var>/dt = <rhs>` (`is_ode`, `parse_ode` -> `ODE` node) and derivative notation anywhere (`involves_derivative`)
   - Identifies free variables in expressions
   - Produces intermediate AST representation

8. **Lean Code Generation** ✓ (Hardened via Tether Mission qed-03)
   - Normalizes the statement before emitting it: implicit multiplication, LaTeX macros, and the ASCII non-strict relations (`<=` -> `≤`, `>=` -> `≥`, `!=` -> `≠`) are rewritten to their Lean spellings, so `2ab`, `\cdot` and `0<=1` all reach Lean as valid code. The relation rewrite is unconditional — a Lean identifier cannot contain `=`, `<` or `>`, so every occurrence is an infix operator — and it is a no-op on canonical input
   - Exempts rate-of-change notation: `dA/dt = Q / V` is emitted as written, never expanded to `dA/d * t` (which would change the meaning and leave `t` undeclared). Normalization therefore stays local to code generation, because `is_ode` / `involves_derivative` classify the *raw* input
   - Generates valid Lean 4 theorem statements
   - Adds `import Mathlib.Tactic` when Mathlib tactics are needed (for `Nat`/`Int`/`Rat` statements)
   - Emits `import Mathlib.Tactic` + `import Mathlib.Basic.Real.Basic` and positivity hypotheses for `Real` statements, so Mathlib's ordered-field tactics apply
   - Declares free variables as theorem parameters
   - Chooses type-appropriate defaults: `Real` for ODEs, derivatives, and division over symbolic variables; `Rat` for division by a pure numeric literal; `Int` for negative literals and subtraction; `Nat` otherwise
   - Generates valid Lean syntax with proper spacing
   - Adds explicit type annotations for negative integer literals (e.g. `(-1 : Int)`). Division gets no extra annotation: rational literals are already inferred, so a `Rat` annotation would be redundant

9. **Tactic Policy (AST-Aware)** ✓ (Hardened via Tether Mission qed-04)
   - Tactic candidates selected based on parsed AST structure (not keyword-based), first matching rule wins
   - Closed numeric equality (`is_numeric_equality`) -> `simp`, `decide`, `norm_num`, `ring`; deliberately *not* `rfl`, so the proof is non-reflexive
   - Structurally identical sides (`statement_kind == 'identity'`) -> `rfl`, `simp`, `refl`
   - ODE / derivative notation (`is_ode`, `involves_derivative`) -> `intros; dsimp; field_simp; ring`, then the field-simplification and normalization stack
   - Dynamical invariants -> `positivity` for Metzler / Jacobian off-diagonal entries (`is_positivity`) and boundary inflow non-negativity (`is_nonneg_product`); `field_simp; ring` for discrete-step conservation (`is_discrete_step_conservation`)
   - Strict inequality containing `/` -> `positivity` (needs the ordered-field structure)
   - Rational structure over symbolic variables (`has_rational_structure`) -> `positivity`, then `field_simp`, `ring_nf`, and `simp [mul_sub, mul_div_assoc]`
   - Any `/` (`contains_op`) -> `field_simp` chain
   - Inequality expressions (`is_inequality`) -> `intros; positivity`, `intros; linarith`, then `linarith`, `omega`
   - Polynomial/algebraic expressions (`has_polynomial_structure`) -> `ring`
   - Otherwise defaults to: rfl, simp, norm_num, decide, ring, then remaining candidates
   - Selection is purely AST-driven; there is no special-casing for variable presence or sign
   - `select_tactic(error_info)` is a separate single-tactic picker for a goal supplied directly: `ring` for polynomial structure, `field_simp` for division/derivative goals, `linarith` for inequalities, `decide` for `Bool` mismatches, `norm_num` for concrete arithmetic, else `simp`

10. **Type Inference (Improved)** ✓
    - `_suggest_type` returns `Real` for ODEs/derivatives and for division whose AST has rational structure, `Rat` for division by a pure numeric literal, `Int` for negative literals and subtraction patterns, and `Nat` otherwise
    - `_get_var_type` applies the statement-level type to every declared variable
    - For `Real` theorems, positivity hypotheses are generated: strict inequalities get `(hv : 0 < v)` for every variable, `≥ 0` / `≤ 0` goals get `(hnv : 0 ≤ v)`, and variables inside a division get the strict form (numerator and denominator both, since `positivity` needs both)
    - Proper type selection prevents Lean type mismatch errors

11. **Agentic Repair (optional)** ✓
    - `--adapter NAME` (with optional `--adapters-config PATH`) resolves a Tether adapter via `tether.adapters.resolve_adapter` for proof repair
    - Once the static candidates are exhausted, the pipeline asks the agent for a tactic, built from Lean's *actual* `unsolved goals` block: the verbatim goal after `⊢` plus its local hypotheses
    - Up to 3 repair rounds; each proposed tactic is compiled and put through the same strict no-`sorry` gate as a static attempt
    - `_parse_adapter_tactic` extracts the tactic from a fenced `lean` block, falling back to the first non-prose line

12. **Timeout Honesty** ✓
    - Each Lean invocation gets `lean_compile_timeout` seconds (default 180, sized for a cold Mathlib import). It is a constructor argument, not a CLI flag, so the "raise `lean_compile_timeout`" advice in the error message applies to library callers
    - A timeout is recorded as an attempt but is **not** treated as a refutation
    - If no attempt ever obtained a verdict, the result carries `infrastructure_failure: true` and says so, instead of reporting "No tactic succeeded"

### Test Results

`python3 -m pytest test_pipeline.py -v` -> **262 passed**.
`python3 run_tests.py` runs 18 checks: 5 end-to-end pipeline invocations (the 3 success
cases are skipped when Lean is absent) and 13 no-sorry-gate checks that need no compiler.

**Parser Hardening Tests** ✓
- "2ab" normalized correctly to "2 * a * b" ✓
- "3xyz" normalized correctly to "3 * x * y * z" ✓
- "(a+b)2" handled as "(a+b) * 2" ✓
- "(a+b)(c+d)" handled as "(a+b) * (c+d)" ✓
- "2(a+b)" handled as "2 * (a+b)" ✓
- "ab + cd" handled as "a * b + c * d" ✓
- Nested parens parsed correctly ✓
- Dotted identifiers (Nat.succ) handled correctly ✓
- LaTeX macros (`\frac`, `\cdot`, `\le`, ...) expanded; unsupported macros fail closed ✓
- Unicode operators (`×`, `÷`, `≤`, `≥`, `≠`, `−`) recognized ✓

**Type Inference Tests** ✓
- "x + 0 = x" suggests type "Nat" ✓
- "-1 + 1 = 0" suggests type "Int" ✓
- "x / 2 = y" suggests type "Rat" (numeric divisor) ✓
- Proper type annotations generated ✓

**Tactic Selection Tests** ✓
- Algebraic expressions lead with ring ✓
- Inequality expressions lead with `intros; positivity`, then `intros; linarith` / `linarith` ✓
- Division expressions lead with `intros; positivity`, then `intros; field_simp; ring` / `field_simp` ✓
- Closed numeric equalities lead with a non-reflexive tactic (simp/decide) ✓
- Identities lead with rfl ✓
- ODE inputs lead with the `intros; dsimp; field_simp; ring` chain ✓
- Goal-based tactic selection works for ring, inequality, field_simp and norm_num patterns ✓
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

**Timeout Tests** ✓
- Cold-cache default timeout and configurability ✓
- All-attempts-timed-out reported as `infrastructure_failure` ✓
- A real refutation is not mislabelled an infrastructure failure ✓

**Statement-Normalization Tests** ✓
- Implicit multiplication is emitted normalized (`2ab` -> `2 * a * b`), not verbatim ✓
- LaTeX macros are expanded before emission (`\cdot`, `\frac`) ✓
- ASCII non-strict relations become Unicode, including digit-adjacent (`0<=1` -> `0≤1`, `2>=x` -> `2≥x`) ✓
- `=` and dotted identifiers are left untouched by the relation rewrite ✓
- ODE notation is exempt: `dA/dt = Q / V` is emitted as written, never as `dA/d * t` ✓
- ODE inputs still route to the `intros; dsimp; field_simp; ring` chain ✓

### Technical Implementation

#### File Structure:
```
.
├── agentic_pipeline.py    # Main pipeline with intelligent tactic selection + CLI entry point
├── parser.py              # Hardened recursive descent parser
├── test_pipeline.py       # Comprehensive unit tests (pytest)
├── run_tests.py           # End-to-end + no-sorry-gate test suite
├── check_sorry.py         # Helper script for sorry detection verification
├── check_parser.py        # Helper script for parser verification
├── check_type.py          # Helper script for type inference verification
├── check_tactic.py        # Helper script for tactic selection verification
├── check_integration.py   # Integration check with real Lean compiler
├── comprehensive_demo.py  # Walkthrough demo of the pipeline
├── run_killrate.py        # Mutation kill-rate harness (wraps tether.verification.measure)
├── verify_pbpk_lemmas.py  # Verifies VeriTrial-exported PBPK lemmas through QED
├── scripts/               # Adapter helper scripts (opencode_tty.py)
├── missions/              # Tether mission files
│   ├── qed-01-no-sorry-gate.yaml
│   ├── qed-02-parser-hardening.yaml
│   ├── qed-03-type-inference.yaml
│   ├── qed-04-tactic-policy.yaml
│   ├── qed-05-integration-validation.yaml
│   ├── qed-cleanroom-integrity.yaml
│   ├── qed-mutation-strength.yaml
│   ├── qed-docs-truth-audit.yaml
│   └── qed-unit-tests-pass.yaml
├── lakefile.lean          # Lake project (requires mathlib)
├── lake-manifest.json     # Pinned Lake dependencies
├── lean-toolchain         # Pinned Lean version (leanprover/lean4:v4.34.0-rc2)
├── QED.lean               # Lean library built by the Lake project
├── Compartmental.lean     # Lean compartment model used by VeriTrialExport
├── VeriTrialExport.lean   # Lean extraction of the VeriTrial PBPK model
├── README.md              # Documentation
├── IMPLEMENTATION_SUMMARY.md  # This file
├── IMPLEMENTATION_PLAN.md     # Original implementation plan
├── LICENSE                # MIT License
├── tether.yaml            # Tether orchestration config
├── output.lean            # Generated verified proof (git-ignored, untracked)
└── traces.json            # Generated audit trail (git-ignored)
```

#### CLI:
```text
python3 agentic_pipeline.py '<statement>' [--max-iterations N] [--adapter NAME] [--adapters-config PATH]
```
- `expression` (positional) - the mathematical statement to prove. Required.
- `--max-iterations N` (default `15`) - maximum number of tactic candidates to try
- `--adapter NAME` - resolve a Tether adapter by name and use it for agentic repair
- `--adapters-config PATH` - Tether config file used to resolve `--adapter`

On success the CLI prints the verification status, the generated Lean code, the winning
tactic and the number of iterations used, and writes the proof to `output.lean`. It exits
`0` only on verified success, `1` otherwise. `traces.json` is written on both outcomes.

#### Success Criteria (Strict):
```text
Lean compiler exit code == 0
AND final Lean source (re-read from disk after compiling) contains no "sorry"/"sorryAx"
AND compiler output contains no "sorryAx"
AND #print axioms qed_goal reports no sorry axiom
```

#### Supported Inputs:
- "0 = 0" (trivial equality)
- "Nat.succ 0 = 1" (natural number successor)
- "x + 0 = x" (variable identity)
- "-1 + 1 = 0" (negative numbers with Int type)
- "(a+b)^2 = a^2 + 2ab + b^2" (polynomial identity; normalized to `2 * a * b`, needs Mathlib)
- "x < x + 1" (inequality)
- "x / 2 = y" (division with Rat type — a *type-inference* example, not a provable
  statement: it is false for free `x, y`, so no tactic can close it)
- "Q * (C_p - C_tissue / Kp) = Q * C_p - Q * C_tissue / Kp" (perfusion law, Real type, needs Mathlib)
- "3 * (5 - 4 / 2) = 3 * 5 - 3 * 4 / 2" (closed numeric witness, proved by `simp`/`decide` without Mathlib)

ODE / rate-of-change notation (`dA/dt = ...`) is *recognized* — `is_ode` /
`involves_derivative` route such statements to the `intros; dsimp; field_simp; ring`
chain and to a `Real` type — but recognition is not provability. A bare ODE equation
such as `dA/dt = Q / V` asserts the rate without any hypothesis relating it to the
compartment quantities, so no tactic can close it; the inputs that verify are the
algebraic identities *about* the right-hand side, as listed above.

Note on spelling: the statement is normalized before it is emitted, so implicit
multiplication (`2ab` -> `2 * a * b`), LaTeX macros (`\cdot` -> `*`,
`\frac{a}{b}` -> `(a) / (b)`) and the ASCII non-strict relations (`<=` -> `≤`,
`>=` -> `≥`, `!=` -> `≠`) are all rewritten into their Lean spellings. Input the parser
does not understand fails closed instead of leaking into the generated proof.

#### Supported Tactics:
- rfl / refl (reflexivity)
- simp (simplification)
- norm_num (normalization of number literals)
- decide (decision procedure)
- ring / ring_nf (algebraic simplifications)
- linarith (linear arithmetic)
- omega (linear integer arithmetic / Presburger)
- field_simp (field simplification)
- dsimp (derivative / rate-of-change head normalization)
- intro / intros (introduce quantified variables)
- positivity (non-negativity goals, e.g. `E / F > 0`)
- compound chains such as `intros; field_simp; ring` and `simp [mul_sub, mul_div_assoc]`

### Known Limitations
- Requires Mathlib4 for some tactics (ring, linarith, omega, positivity)
- Limited to constrained arithmetic expressions (not arbitrary LaTeX); unsupported macros and quantifiers fail closed rather than being verified
- Type inference is heuristic-based, not full typeclass synthesis
- Lean 4 toolchain must be available via elan
- Complex proofs requiring deep tactic sequences may need manual intervention
- Agentic repair needs an external Tether adapter; without `--adapter` the pipeline is fully deterministic
- Proofs are emitted as a single theorem named `qed_goal`, and axiom verification only inspects that name

### Tether Missions Executed
The following Tether missions were executed to harden the pipeline:

1. **qed-unit-tests-pass**: Verified all unit tests pass and pipeline handles missing Lean gracefully
2. **qed-01-no-sorry-gate**: Hardened sorry detection with comprehensive patterns and fail-closed axiom verification
3. **qed-02-parser-hardening**: Improved parser to handle dotted identifiers, unary negation before parentheses, LaTeX macros and `\frac`
4. **qed-03-type-inference**: Verified type inference and proper type annotations
5. **qed-04-tactic-policy**: Refactored tactic selection to use AST-based classification
6. **qed-05-integration-validation**: End-to-end verification with the pinned real Lean 4 toolchain
7. **qed-cleanroom-integrity**: Clean-room integrity checks
8. **qed-mutation-strength**: Mutation-strength checks on the pipeline
9. **qed-docs-truth-audit**: Brought this summary and `README.md` back in line with `agentic_pipeline.py` / `parser.py`

Run a mission with the `tether` executable from your PATH:
```bash
tether run missions/<mission>.yaml --project-dir . --adapter opencode
```
Tether refuses to start an agent on a dirty working tree, so commit or stash first.

### Conclusion
The Lean 4 Agentic Pipeline has been hardened from an MVP to a more robust implementation. Key improvements:
- Parser now correctly handles implicit multiplication chains, paren-adjacent operations, nested parentheses, dotted identifiers, LaTeX macros and Unicode operators
- The generated statement is normalized before emission, so the documented `2ab` / `\cdot` / `x <= y` spellings actually reach Lean as valid code
- Type inference produces context-appropriate types (Real/Int/Rat/Nat) instead of defaulting to Int, and emits positivity hypotheses for Real theorems
- Tactic selection uses parsed AST structure for smarter ordering (not keyword-based), covering ODE/derivative, Metzler positivity, discrete-step conservation, and non-negative-product goals
- Sorry detection has been hardened with comprehensive patterns and fail-closed axiom verification
- Comprehensive unit tests verify all improvements (262 passing)
- Pipeline gracefully handles missing Lean compiler
- The CLI honours `--max-iterations`, reports the iteration count, writes `output.lean`, and prints the audit trail on failure
- An optional agentic repair path asks an external adapter for a proof from Lean's real goal and hypotheses when the static candidates are exhausted
- A Lean timeout is reported as an infrastructure failure rather than a refutation
- Documentation is kept truthful to the implementation by the qed-docs-truth-audit mission
- Mathlib auto-detection: falls back to core-only tactics when Mathlib is unavailable
