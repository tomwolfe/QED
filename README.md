# Lean 4 Agentic Pipeline

A CLI-based agentic pipeline that converts informal mathematical statements in LaTeX into verified Lean 4 code, using iterative tactic search to resolve proof errors.

## Features

- **Input Validation**: Validates LaTeX mathematical statements
- **Lean 4 Integration**: Compiles and executes Lean 4 code automatically
- **Agentic Tactic Search**: Automatically selects and applies proof tactics
- **Audit Trail**: Maintains detailed traces of all attempts and corrections
- **Error Parsing**: Regex-based parsing of Lean compiler error messages
- **Max Iteration Control**: Prevents token spiraling with configurable iteration limits

## Requirements

- Python 3.11+
- Lean 4 (v4.27.0+) via elan
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
python3 agentic_pipeline.py "theorem ..." --output my_theorem.lean --max-iterations 10
```

### Test the Pipeline

Run the built-in tests:
```bash
python3 run_tests.py
```

Run the identity theorem test:
```bash
python3 test_pipeline.py
```

## Pipeline Workflow

1. **Input Validation**: Parses LaTeX to ensure it's a complete theorem statement
2. **Translation**: Generates a Lean 4 file with the theorem and 'sorry' placeholder
3. **Agentic Tactic Search**:
   - Calls the Lean compiler
   - Parses stderr for error messages and goal states
   - Selects appropriate tactics (ring, linarith, induction, etc.)
   - Appends tactics and repeats until success or max iterations
4. **Audit Trail**: Logs all attempts in traces.json
5. **Success Criteria**: Returns exit code 0 only when verified without 'sorries'

## Supported Tactic Types

The pipeline automatically selects tactics based on error patterns:

- **ring**: For algebraic simplifications
- **linarith**: For inequality and arithmetic proofs
- **induction**: For inductive proofs
- **intro**: For introducing variables
- **apply**: For applying theorems
- **simp**: For simplification
- **field_simp**: For field operations

## Output

On success:
- Prints verification status
- Shows iterations used
- Writes final Lean 4 code to output file

On failure:
- Prints failure message
- Shows audit trail with all attempts

## File Structure

```
.
├── agentic_pipeline.py    # Main pipeline implementation
├── test_pipeline.py        # Basic identity theorem test
├── run_tests.py            # Comprehensive test suite
├── README.md              # This file
└── traces.json            # Generated audit trail
```

## Safety Protocol

The system follows deterministic verification only. All generated code is verified by the Lean compiler before being considered complete. The maximum recursion depth prevents infinite loops in the tactic search.

## Known Limitations

- Requires Mathlib4 to be available in the Lean environment
- May fail on complex theorems requiring deep tactic sequences
- Does not handle dependent type theory proofs without Mathlib
- Limited to standard tactics; advanced tactics require manual intervention

## Troubleshooting

If the pipeline fails:
1. Check if Lean 4 is properly installed: `lean --version`
2. Verify Mathlib4 is accessible
3. Review the audit trail in traces.json
4. Try with a simpler theorem first
