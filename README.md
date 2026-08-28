# QED: Lean 4 Agentic Pipeline

A CLI-based agentic pipeline that converts constrained mathematical statements in LaTeX into verified Lean 4 code, using iterative tactic search to resolve proof errors.

## Features

- **Input Validation**: Validates LaTeX mathematical statements, rejects non-mathematical text
- **Lean 4 Integration**: Compiles and executes Lean 4 code automatically
- **Agentic Tactic Search**: Automatically selects and applies proof tactics based on AST analysis
- **Audit Trail**: Maintains detailed traces of all attempts and corrections
- **Error Parsing**: Regex-based parsing of Lean compiler error messages
- **Max Iteration Control**: Prevents token spiraling with configurable iteration limits
- **Strict No-Sorry Verification**: Success only when final Lean file contains no `sorry`
- **AST-Aware Tactic Selection**: Uses parsed AST structure for smarter tactic ordering
- **Comprehensive Sorry Detection**: Detects `sorry`, `sorryAx`, `Tactic.sorry`, and `Lean.Elab.Tactic.sorry`
- **Fail-Closed Axiom Verification**: Verifies no sorry axioms in compiled output

## Requirements

- Python 3.11+
- Lean 4 (v4.27.0+) via elan (optional - pipeline handles missing Lean gracefully)
- Mathlib4 (automatically downloaded by Lean compiler)

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

### Advanced Usage

```bash
python3 agentic_pipeline.py "(a+b)^2 = a^2 + 2*a*b + b^2"
```

### Test the Pipeline

Run the built-in tests:
```bash
python3 run_tests.py
```

## Pipeline Workflow

1. **Input Validation**: Parses LaTeX to ensure it's a complete theorem statement
2. **Translation**: Generates a Lean 4 theorem statement with proper imports and variable declarations
3. **Agentic Tactic Search**:
   - Calls the Lean compiler
   - Parses stderr for error messages and goal states
   - Selects appropriate tactics (ring, linarith, etc.)
   - Appends tactics and repeats until success or max iterations
   - **Strict**: Only reports success if final proof contains no `sorry`
4. **Audit Trail**: Logs all attempts in `traces.json`
5. **Success Criteria**: Returns exit code 0 only when verified without `sorries`

## Supported Tactic Types

The pipeline automatically selects tactics based on error patterns:

- **rfl**: For reflexive equalities (e.g., `0 = 0`, `Nat.succ 0 = 1`)
- **simp**: For simplification with annotated hypotheses
- **norm_num**: For normalization of number literals
- **decide**: For decision procedures
- **ring**: For algebraic simplifications (requires Mathlib)
- **linarith**: For inequality and arithmetic proofs (requires Mathlib)
- **omega**: For quantifier-free nonlinear arithmetic (requires Mathlib)
- **field_simp**: For field operations

## Output

On success:
- Prints verification status
- Shows iterations used
- Writes final Lean 4 code to output file
- **No `sorry` in the output**

On failure:
- Prints failure message
- Shows audit trail with all attempts
- `traces.json` is written with complete execution history

## File Structure

```
.
├── agentic_pipeline.py    # Main pipeline implementation
├── test_pipeline.py        # Basic identity theorem test
├── run_tests.py            # Comprehensive test suite
├── README.md              # This file
├── IMPLEMENTATION_SUMMARY.md  # Implementation status report
└── traces.json            # Generated audit trail
```

## Safety Protocol

The system follows deterministic verification only. All generated code is verified by the Lean compiler before being considered complete. The maximum recursion depth prevents infinite loops in the tactic search. **Critical**: Success requires the final Lean file to contain no `sorry` placeholders.

## Known Limitations

- Requires Mathlib4 to be available for certain tactics (ring, linarith, omega)
- May fail on complex theorems requiring deep tactic sequences
- Does not handle dependent type theory proofs without Mathlib
- Limited to standard tactics; advanced tactics require manual intervention

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
Generates verified proof without `sorry`.

### Variable Identity

```bash
python3 agentic_pipeline.py "x + 0 = x"
```
Generates: `theorem qed_goal (x : Int) : x + 0 = x := by ring` (no `sorry`).

### Polynomial Identity (Mathlib required)

```bash
python3 agentic_pipeline.py "(a+b)^2 = a^2 + 2ab + b^2"
```
Generates: `import Mathlib.Tactic` + theorem with `ring` tactic (no `sorry`).

## Example of Verified Output

**Input:** `0 = 0`

**Generated Lean file (`output.lean`):**
```lean
-- Generated by QED Pipeline
theorem qed_goal : 0 = 0 := by
  rfl
```

**Result:** ✓ Verification Successful! (no `sorry`)

**Input:** `x + 0 = x`

**Generated Lean file (`output.lean`):**
```lean
-- Generated by QED Pipeline
theorem qed_goal (x : Int) : x + 0 = x := by
  ring
```

**Result:** ✓ Verification Successful! (no `sorry`)

**Input:** `-1 + 1 = 0`

**Generated Lean file (`output.lean`):**
```lean
-- Generated by QED Pipeline
theorem qed_goal : -1 + 1 = 0 := by
  ring
```

**Result:** ✓ Verification Successful! (no `sorry`)

## Running Tests

```bash
python3 -m pytest test_pipeline.py -v  # All 54 unit tests
python3 run_tests.py  # End-to-end tests (18 tests, requires Lean 4)
python3 check_integration.py  # Integration check with real Lean compiler
```

## Tether Integration

This project uses Tether for orchestration and verification. Missions are defined in the `missions/` directory:

- `qed-unit-tests-pass.yaml`: Verifies all unit tests pass
- `qed-01-no-sorry-gate.yaml`: Hardens sorry detection
- `qed-02-parser-hardening.yaml`: Improves parser capabilities
- `qed-03-type-inference.yaml`: Verifies type inference
- `qed-04-tactic-policy.yaml`: Refactors tactic selection
- `qed-05-integration-validation.yaml`: End-to-end verification

To run a mission:
```bash
./tether/.venv/bin/tether run missions/<mission>.yaml --project-dir . --adapter opencode
```

Test results verify:
- Validation correctly accepts/rejects inputs
- Lean code generation produces syntactically valid theorems
- Tactic search loop attempts multiple candidates
- No `sorry` appears in successful output
- `traces.json` is written for both success and failure