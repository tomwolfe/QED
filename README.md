# QED: Lean 4 Agentic Pipeline

A CLI-based agentic pipeline that converts constrained mathematical statements in LaTeX into verified Lean 4 code, using iterative tactic search to resolve proof errors.

## Features

- **Input Validation**: Validates LaTeX mathematical statements, rejects non-mathematical text
- **Lean 4 Integration**: Compiles and executes Lean 4 code automatically
- **Agentic Tactic Search**: Automatically selects and applies proof tactics based on AST analysis
- **Audit Trail**: Maintains detailed traces of all attempts and corrections
- **Sorry Detection**: Regex-based detection of `sorry` and `sorryAx` in compiler output and source
- **Max Iteration Control**: Prevents token spiraling with configurable iteration limits
- **Strict No-Sorry Verification**: Success only when final Lean file contains no `sorry`
- **AST-Aware Tactic Selection**: Uses parsed AST structure for smarter tactic ordering
- **ODE / Rate-of-Change Awareness**: Recognizes `d<var>/dt = <rhs>` ODEs (`parser.is_ode`, `parser.parse_ode`) and derivative notation anywhere (`parser.involves_derivative`); `get_tactic_candidates` leads with the `intros; dsimp; field_simp; ring` chain for derivative / rate-of-change inputs
- **Comprehensive Sorry Detection**: Detects `sorry`, `sorryAx`, `Tactic.sorry`, and `Lean.Elab.Tactic.sorry`
- **Fail-Closed Axiom Verification**: Runs `#print axioms qed_goal` on every candidate proof; any failure is reported as not-clean
- **Statement Normalization**: Implicit multiplication, LaTeX macros, and ASCII `<=` / `>=` / `!=` are rewritten to the spellings Lean accepts, so `2ab`, `\cdot` and `0<=1` become provable
- **Type Inference**: Derives `Nat` / `Int` / `Rat` / `Real` from the statement, and emits positivity hypotheses (`0 < v`, `0 ≤ v`) for `Real` theorems so Mathlib's ordered-field tactics apply
- **Agentic Repair (optional)**: `--adapter NAME` asks an external agent for a proof after the static candidates are exhausted — see [Agentic repair](#agentic-repair-optional)
- **Timeout Honesty**: Distinguishes an infrastructure timeout from a refutation. If no Lean invocation ever returned a verdict, the result carries `infrastructure_failure: true` rather than "no tactic worked"

## Requirements

- Python 3.11+
- Lean 4 via elan (optional — the pipeline handles a missing Lean gracefully). The version is pinned by `lean-toolchain` (`leanprover/lean4:v4.34.0-rc2`); elan downloads it on first use
- Mathlib4 (fetched by Lake from `lakefile.lean` / `lake-manifest.json`. The pipeline auto-detects it and falls back to core-only tactics when it is unavailable)

## Installation

1. Install elan (Lean package manager):
```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
```

2. Set elan to your PATH:
```bash
export PATH="$HOME/.elan/bin:$PATH"
```

3. Install Lean 4 (automatically downloaded on first use):
```bash
elan show
```

## Usage

### Basic Usage

```bash
python3 agentic_pipeline.py "your LaTeX theorem statement"
```

Example:
```bash
python3 agentic_pipeline.py "(a+b)^2 = a^2 + 2ab + b^2"
```

Division and `Real`-valued identities route to the Mathlib field tactics:
```bash
python3 agentic_pipeline.py "Q * (C_p - C_tissue / Kp) = Q * C_p - Q * C_tissue / Kp"
```

### CLI Options

```bash
python3 agentic_pipeline.py "x + 0 = x" --max-iterations 5
python3 agentic_pipeline.py "E / F > 0" --adapter opencode
python3 agentic_pipeline.py "E / F > 0" --adapter opencode --adapters-config tether.yaml
```

| Flag | Default | Meaning |
| --- | --- | --- |
| `expression` (positional) | – | The mathematical statement to prove. Required. |
| `--max-iterations N` | `15` | Maximum number of tactic candidates to try before giving up. |
| `--adapter NAME` | none | Resolve a Tether adapter by name and use it for agentic repair. |
| `--adapters-config PATH` | none | Tether config file used to resolve `--adapter`. |

The process exits `0` only on verified success, and `1` otherwise (including invalid input).

### Test the Pipeline

Run the built-in tests:
```bash
python3 run_tests.py
```

## How your statement is translated

The statement is **normalized before it is emitted**, so ordinary LaTeX-ish input
reaches Lean in a form Lean accepts:

| You write | The theorem contains |
| --- | --- |
| `2ab` | `2 * a * b` |
| `(a+b)2` | `(a+b) * 2` |
| `a \cdot b` | `a * b` |
| `\frac{a}{b}` | `(a) / (b)` |
| `x \le 1`, `x <= 1`, `0<=1` | `x ≤ 1`, `x ≤ 1`, `0≤1` |
| `a \neq b` | `a ≠ b` |

Normalization is idempotent, so it is a no-op on already-canonical input, and the
tactic policy and type inference classify the same statement that is emitted.

Rate-of-change notation is the one exemption. In `dA/dt = Q / V` the `/dt` is a
derivative marker, not a division, so the statement is emitted exactly as written —
expanding it to `dA/d * t` would both change the meaning and leave `t` an undeclared
identifier. Tactic ordering likewise classifies the raw input, so ODE statements still
reach the `intros; dsimp; field_simp; ring` chain.

Anything the parser does not understand fails closed (it is rejected) rather than
leaking raw LaTeX into the generated proof.

## Pipeline Workflow

1. **Input Validation**: Parses LaTeX to ensure it's a complete theorem statement
2. **Translation**: Generates a Lean 4 theorem statement with proper imports and variable declarations
3. **Agentic Tactic Search**:
   - Calls the Lean compiler
   - Checks exit code and detects `sorry`/`sorryAx` in output
   - Tries ordered tactic candidates (rfl, simp, ring, etc.) based on AST analysis
   - Repeats until success or max iterations
   - **Strict**: Only reports success if final proof contains no `sorry`
4. **Audit Trail**: Logs all attempts in `traces.json`
5. **Success Criteria**: Returns exit code 0 only when verified without `sorry`

## Supported Tactic Types

The pipeline's base tactic pool is `rfl`, `simp`, `norm_num`, `decide`, `ring`,
`linarith`, `omega`, `field_simp`, `dsimp`, `intro`, `positivity`. Depending on the
AST it also proposes `refl`, `ring_nf`, `simp [mul_sub, mul_div_assoc]`, and compound
semicolon chains (e.g. `intros; field_simp; ring`) that are tried as a single proof
block.

- **rfl / refl**: For reflexive equalities and identities (e.g. `x + 0 = x`)
- **simp**: For simplification with annotated hypotheses
- **norm_num**: For normalization of number literals
- **decide**: For decision procedures
- **ring / ring_nf**: For algebraic simplifications (requires Mathlib)
- **linarith**: For inequality and arithmetic proofs (requires Mathlib)
- **omega**: For linear integer arithmetic / Presburger goals (requires Mathlib)
- **field_simp**: For field operations (required for PBPK perfusion terms with division, e.g. `C_p = A_central / V_central`)
- **dsimp**: For simplifying derivative / rate-of-change heads in formal-ODE inputs
- **intro / intros**: To bring the universally quantified variables into scope
- **positivity**: For non-negativity goals such as Jacobian off-diagonal entries `E / F > 0` (requires Mathlib)

### Tactic ordering

`get_tactic_candidates` picks the ordering purely from the parsed AST. The first
matching rule wins; the remaining base tactics are appended as fallbacks.

| # | AST condition | Leading candidates |
| --- | --- | --- |
| 1 | Closed numeric equality, no free variables (`is_numeric_equality`) | `simp`, `decide`, `norm_num`, `ring` — deliberately *not* `rfl`, so the proof is non-reflexive |
| 2 | Structurally identical sides (`statement_kind == 'identity'`) | `rfl`, `simp`, `refl` |
| 3 | ODE or derivative notation (`is_ode` / `involves_derivative`) | `intros; dsimp; field_simp; ring`, `intros; field_simp; ring`, `dsimp`, `field_simp`, `ring_nf`, `simp`, `norm_num`, `decide` |
| 4 | Metzler / Jacobian off-diagonal positivity (`is_positivity`) | `intros; positivity`, `positivity`, `intros; field_simp; ring` |
| 5 | Discrete-step conservation (`is_discrete_step_conservation`) | `intros; field_simp; ring`, `field_simp`, `ring`, `intros; positivity` |
| 6 | Non-negative product / boundary inflow (`is_nonneg_product`) | `intros; positivity`, `intros; field_simp; linarith`, `intros; field_simp; ring`, `positivity`, `linarith` |
| 7 | Strict inequality (`Gt`/`Lt`) containing `/` | `intros; positivity`, `intros; field_simp; positivity`, `positivity` |
| 8 | Rational structure over symbolic variables (`has_rational_structure`) | `intros; positivity`, `intros; field_simp; ring`, `intros; dsimp; field_simp; ring`, `intros; simp [mul_sub, mul_div_assoc]; ring`, `intro`, `dsimp`, `field_simp`, `simp [mul_sub, mul_div_assoc]`, `ring_nf`, `linarith`, `simp`, `norm_num` |
| 9 | Any `/` (`contains_op`) | `intros; positivity`, `intros; field_simp; ring`, `field_simp`, `ring`, `norm_num`, `simp` |
| 10 | Inequality (`is_inequality`) | `intros; positivity`, `intros; linarith`, `linarith`, `omega`, `simp`, `norm_num` |
| 11 | Polynomial / algebraic structure (`has_polynomial_structure`) | `ring`, `simp`, `linarith`, `norm_num` |
| 12 | Otherwise | `rfl`, `simp`, `norm_num`, `decide`, `ring` |

`select_tactic(error_info)` is the separate single-tactic picker used when a goal is
supplied directly: it returns `ring` for polynomial structure, `field_simp` for
division or derivative goals, `linarith` for inequalities, `decide` for `Bool`
mismatches, `norm_num` for concrete arithmetic, and falls back to `simp`.

### Type inference

`_suggest_type` chooses the Lean type for the whole statement, and
`_get_var_type` applies it to every declared variable:

| Expression shape | Type |
| --- | --- |
| ODE (`d<var>/dt = ...`) or any derivative notation | `Real` |
| Division whose AST has rational structure (e.g. `x / y`) | `Real` |
| Division by a pure numeric literal only (e.g. `x / 2`) | `Rat` |
| Negative literals (`-1`) or subtraction patterns (`a - b`, `0 - x`, `(a - b)`) | `Int` |
| Inequality containing `*` between words (e.g. `k * x > 0`) | `Real` |
| Everything else | `Nat` |

`Real` theorems additionally get positivity hypotheses so Mathlib's ordered-field
tactics apply: strict inequalities get `(hv : 0 < v)` for every variable, `≥ 0` / `≤ 0`
goals get `(hnv : 0 ≤ v)`, and variables inside a division get the strict form (both
numerator and denominator, since `positivity` needs both).

## Agentic repair (optional)

When the static candidates are exhausted and an adapter was supplied via `--adapter`,
the pipeline asks the agent for a proof. The prompt is built from Lean's *actual*
`unsolved goals` block — the verbatim goal after `⊢` plus its local hypotheses — so the
agent sees the same context the static tactics were given. Up to 3 repair rounds are
tried; each proposed tactic is compiled and put through the same strict no-`sorry`
gate (source re-read, compiler output, and `#print axioms`) as a static attempt.

## Output

On success:
- Prints verification status, the generated Lean, and the winning tactic
- Shows iterations used (the number of attempts made)
- Writes the final Lean 4 code to `output.lean` (generated, git-ignored)
- **No `sorry` in the output**

On failure:
- Prints failure message
- Shows the audit trail with all attempts
- `traces.json` is written with the complete execution history

`traces.json` is written on both success and failure and holds the full attempt list:
iteration index, tactic, exit code, `has_sorry`, `sorry_reason`, and truncated
stdout/stderr.

## File Structure

```
.
├── agentic_pipeline.py    # Main pipeline implementation + CLI entry point
├── parser.py              # Recursive descent parser
├── test_pipeline.py       # Comprehensive unit tests (pytest)
├── run_tests.py           # End-to-end + no-sorry-gate test suite
├── check_sorry.py         # Helper script for sorry detection verification
├── check_parser.py        # Helper script for parser verification
├── check_type.py          # Helper script for type inference verification
├── check_tactic.py        # Helper script for tactic selection verification
├── check_integration.py   # Integration check with real Lean compiler
├── comprehensive_demo.py  # Walkthrough demo of the pipeline
├── run_killrate.py        # Tactic-candidate kill-rate reporting
├── verify_pbpk_lemmas.py  # Verifies VeriTrial-exported PBPK lemmas through QED
├── scripts/               # Adapter helper scripts (opencode_tty.py)
├── missions/              # Tether mission files
├── lakefile.lean          # Lake project (requires mathlib)
├── lake-manifest.json     # Pinned Lake dependencies
├── lean-toolchain         # Pinned Lean version
├── QED.lean               # Lean library built by the Lake project
├── Compartmental.lean     # Lean compartment model used by VeriTrialExport
├── VeriTrialExport.lean   # Lean extraction of the VeriTrial PBPK model
├── README.md              # This file
├── IMPLEMENTATION_SUMMARY.md  # Implementation status report
├── IMPLEMENTATION_PLAN.md     # Original implementation plan
├── LICENSE                # MIT License
├── tether.yaml            # Tether orchestration config
├── output.lean            # Generated verified proof (git-ignored, untracked)
└── traces.json            # Generated audit trail (git-ignored)
```

## Safety Protocol

The system follows deterministic verification only. All generated code is verified by
the Lean compiler before being considered complete. The tactic search is a bounded
loop — at most `--max-iterations` (default 15) candidates, each a fresh compile — so
it cannot spiral. **Critical**: Success requires the final Lean file to contain no
`sorry` placeholders.

A run is reported as successful only when all three gates pass:
1. the Lean compiler exits `0`;
2. the source (re-read from disk after compiling) and the compiler output contain no `sorry` / `sorryAx` / `Tactic.sorry` / `Lean.Elab.Tactic.sorry`;
3. `#print axioms qed_goal` reports no sorry axiom.

If a Lean invocation times out (default budget: 180s per invocation, sized for a cold
Mathlib import), the attempt is recorded but is **not** treated as a refutation. If no
attempt ever obtained a verdict, the result carries `infrastructure_failure: true` and
an error message saying so, instead of "No tactic succeeded". The per-invocation budget
is a constructor argument (`LeanAgenticPipeline(lean_compile_timeout=...)`), not a CLI
flag, so the "raise `lean_compile_timeout`" advice in that message applies to callers
using the pipeline as a library.

## Known Limitations

- Requires Mathlib4 for certain tactics (ring, linarith, omega, positivity, field_simp)
- May fail on complex theorems requiring deep tactic sequences
- Does not handle dependent type theory proofs without Mathlib
- Limited to standard tactics; advanced tactics require manual intervention
- Recognition is not provability: a bare ODE such as `dA/dt = Q / V` asserts the rate
  without any hypothesis tying it to the compartment quantities, so no tactic closes it

## Troubleshooting

If the pipeline fails:
1. Check if Lean 4 is properly installed: `lean --version`
2. Verify Mathlib4 is accessible
3. Review the audit trail in `traces.json`
4. Try with a simpler theorem first

## Example Commands

### Simple Equality

```bash
python3 agentic_pipeline.py "0 = 0"
```
Generates a verified proof without `sorry`.

### Variable Identity

```bash
python3 agentic_pipeline.py "x + 0 = x"
```
Generates: `theorem qed_goal (x : Nat) : x + 0 = x := by rfl` (no `sorry`).

### Polynomial Identity (Mathlib required)

```bash
python3 agentic_pipeline.py "(a+b)^2 = a^2 + 2ab + b^2"
```
Generates: `import Mathlib.Tactic` + `import Mathlib.Basic.Real.Basic` and a
`(a b : ℝ)` theorem closed by `ring` (no `sorry`). The implicit `2ab` and the explicit
`2*a*b` normalize to the same `2 * a * b`, so either spelling works.

## Example of Verified Output

The Lean code below is copied verbatim from the runs shown, including the
`import Mathlib.Tactic` header the generator emits for `Nat`/`Int` statements.

**Input:** `0 = 0`

**Generated Lean file (`output.lean`):**
```lean
import Mathlib.Tactic

theorem qed_goal : 0 = 0 := by
  simp
```

**Result:** ✓ Verification Successful! (no `sorry`) — winning tactic `simp`

`0 = 0` is a *closed numeric equality*, so the policy deliberately leads with
`simp`/`decide` rather than `rfl` to produce a genuinely non-reflexive proof.

**Input:** `x + 0 = x`

**Generated Lean file (`output.lean`):**
```lean
import Mathlib.Tactic

theorem qed_goal (x : Nat) : x + 0 = x := by
  rfl
```

**Result:** ✓ Verification Successful! (no `sorry`) — winning tactic `rfl`

**Input:** `-1 + 1 = 0`

**Generated Lean file (`output.lean`):**
```lean
import Mathlib.Tactic

theorem qed_goal : (-1 : Int) + 1 = 0 := by
  simp
```

**Result:** ✓ Verification Successful! (no `sorry`) — winning tactic `simp`

The `(-1 : Int)` annotation is added automatically because the statement contains a
negative literal.

## Running Tests

```bash
python3 -m pytest test_pipeline.py -v  # all unit tests
python3 run_tests.py  # 18 checks: 5 end-to-end pipeline runs + 13 no-sorry-gate checks
python3 check_integration.py  # Integration check with real Lean compiler
```

The 3 successful end-to-end cases are skipped when Lean is unavailable; the two
rejection cases and all 13 no-sorry-gate checks need no compiler.

The `check_*.py` helpers are single-case probes, not suites — each prints a usage line
and exits `1` unless given a case name:

```bash
python3 check_sorry.py true          # sorry detection on an argument
python3 check_parser.py pre_paren    # also: post_paren, chain
python3 check_type.py int            # also: rat, annotation
python3 check_tactic.py algebraic    # also: inequality, ring_goal
```

## Tether Integration

This project uses Tether for orchestration and verification. Missions are defined in the `missions/` directory:

- `qed-unit-tests-pass.yaml`: Verifies all unit tests pass
- `qed-01-no-sorry-gate.yaml`: Hardens sorry detection
- `qed-02-parser-hardening.yaml`: Improves parser capabilities
- `qed-03-type-inference.yaml`: Verifies type inference
- `qed-04-tactic-policy.yaml`: Refactors tactic selection
- `qed-05-integration-validation.yaml`: End-to-end verification
- `qed-cleanroom-integrity.yaml`: Clean-room integrity checks
- `qed-mutation-strength.yaml`: Mutation-strength checks on the pipeline
- `qed-docs-truth-audit.yaml`: Audits that these docs match `agentic_pipeline.py` / `parser.py`

To run a mission (using the `tether` executable from your PATH):
```bash
tether run missions/<mission>.yaml --project-dir . --adapter opencode
```

Tether refuses to start an agent on a dirty working tree, so commit or stash first.

### Formal ODE verification (VeriTrial PBPK)

The pipeline recognizes PBPK ODEs of the form `d<var>/dt = <rhs>` and derivative
notation anywhere in the input (`parser.is_ode`, `parser.parse_ode`,
`parser.involves_derivative`). For such inputs `get_tactic_candidates` leads with the
compound chain `intros; dsimp; field_simp; ring`, then `intros; field_simp; ring`, then
bare `dsimp`, `field_simp`, `ring_nf` — the tactic chain QED uses (with Mathlib) to
prove the perfusion-limited uptake distributive law:

```
Q * (C_p - C_tissue / Kp) = Q * C_p - Q * C_tissue / Kp
```

QED also ships `verify_pbpk_lemmas.py`, which reads a file of QED-parseable LaTeX
lemmas (one per line) as produced by VeriTrial's `export_pbpk_to_qed.py` bridge and
verifies each one through `agentic_pipeline.py`, exiting non-zero if any lemma fails:

```bash
python3 verify_pbpk_lemmas.py path/to/pbpk_lemmas.txt
```

The bridge may export *instantiated numeric witnesses* of the law (e.g.
`3 * (5 - 4 / 2) = 3 * 5 - 3 * 4 / 2`). These are closed numeric equalities, so the
pipeline proves them with `simp`/`decide` — a genuine, non-reflexive proof under the
strict no-`sorry` policy — and they still verify in a Mathlib-free environment.

Test results verify:
- Validation correctly accepts/rejects inputs
- Lean code generation produces syntactically valid theorems
- Tactic search loop attempts multiple candidates
- No `sorry` appears in successful output
- `traces.json` is written for both success and failure
