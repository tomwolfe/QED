#!/usr/bin/env python3
"""Integration check: verify pipeline works end-to-end with real Lean compiler.

Every check below is an ASSERTION about the artefacts a run produced -- not
about the exit code of a helper script:

  * the run SUCCEEDED (a real Lean compile, no sorry);
  * the generated Lean source carries no ``sorry``/``sorryAx``;
  * the audit trail ``traces.json`` was written BY THIS RUN and agrees with
    the result -- a stale file left over from an earlier run must not pass
    as a fresh one;
  * the artefact ``output.lean`` holds exactly the verified source, carries
    no ``sorry``, and RECOMPILES STANDALONE with exit code 0.

The checks are Mathlib-agnostic: they hold in a clean room with no Mathlib
build as well as in a warm tree.
"""
import json
import os
import subprocess
import sys

# Ensure elan is on PATH
os.environ["PATH"] = os.path.expanduser("~/.elan/bin") + ":" + os.environ.get("PATH", "")

from agentic_pipeline import LeanAgenticPipeline

TRACE = "traces.json"
ARTIFACT = "output.lean"


def _read(path):
    """The contents of *path*, or None when it does not exist."""
    try:
        with open(path) as fh:
            return fh.read()
    except FileNotFoundError:
        return None
    except OSError:
        return None


def _remove(path):
    """Delete *path* if it is there; a missing file is not an error."""
    try:
        os.unlink(path)
    except FileNotFoundError:
        pass
    except OSError:
        pass


def _recompiles(pipeline, path):
    """Compile the artefact ON ITS OWN, the way a reviewer would."""
    return subprocess.run(
        pipeline._compile_lean_cmd(path),
        capture_output=True, text=True,
        timeout=pipeline.lean_compile_timeout,
        env=pipeline._compile_env(),
    )


def check_case(pipeline, expression, expect_success=True):
    """Run one integration case and assert on everything it produced."""
    # Remove the deliverables first: a file left over from an earlier run
    # must not be able to satisfy a check about THIS run.
    _remove(TRACE)
    artifact_before = _read(ARTIFACT)
    if expect_success:
        _remove(ARTIFACT)

    result = pipeline.run(expression)

    if expect_success:
        assert result['success'], (
            f"Expected success for '{expression}', got: {result.get('error')}")
        source = result.get('lean_code') or ''
        assert source.strip(), f"No Lean source produced for '{expression}'"
        # The no-sorry gate, on the source that was actually compiled.
        assert 'sorry' not in source, (
            f"'sorry' in the generated source for '{expression}'")
        assert 'sorryAx' not in source, (
            f"'sorryAx' in the generated source for '{expression}'")
        for attempt in result.get('attempts', []):
            assert not attempt.get('has_sorry', False), (
                f"Sorry detected in output for '{expression}': "
                f"{attempt.get('sorry_reason')}")
        # The pipeline's own three-part gate must have passed.
        verification = result.get('verification') or {}
        for gate in ('source_check', 'compiler_check', 'axioms_check'):
            assert verification.get(gate) == 'passed', (
                f"{gate} did not pass for '{expression}'")
        # The audit trail must have been written BY THIS RUN.
        assert os.path.exists(TRACE), "traces.json not written"
        trace = json.loads(_read(TRACE))
        assert trace.get('success') is True, "trace does not record the success"
        assert trace.get('tactic') == result.get('tactic'), (
            "trace records a different tactic than the result")
        assert trace.get('lean_code') == source, (
            "trace records different Lean source than the result")
        assert len(trace.get('attempts') or []) == len(
            result.get('attempts') or []), (
            "trace records a different number of attempts than the result")
        # The artefact holds exactly the verified source ...
        assert os.path.exists(ARTIFACT), "output.lean not written"
        artifact = _read(ARTIFACT)
        assert artifact == source, (
            "output.lean does not hold the verified Lean source")
        assert 'sorry' not in artifact, "'sorry' in output.lean"
        # ... and it compiles on its own.
        compiled = _recompiles(pipeline, ARTIFACT)
        assert compiled.returncode == 0, (
            f"output.lean does not recompile standalone: "
            f"{(compiled.stdout + compiled.stderr)[-500:]}")
        assert 'sorry' not in (compiled.stdout + compiled.stderr), (
            "output.lean compiles with a sorry")
    else:
        assert not result['success'], (
            f"Expected failure for '{expression}', but it was verified")
        # The audit trail is written on failure too.
        assert os.path.exists(TRACE), "traces.json not written for a failed run"
        trace = json.loads(_read(TRACE))
        assert trace.get('success') is False, (
            "trace does not record the failure")
        # A failed run must not leave a proof artefact behind.
        assert _read(ARTIFACT) == artifact_before, (
            "output.lean was overwritten by a failed run")

    print(f"  OK: {expression}")
    return result


def main():
    print("Running integration checks with real Lean compiler...")
    pipeline = LeanAgenticPipeline()

    # These should fail validation
    check_case(pipeline, "hello world", expect_success=False)
    check_case(pipeline, "", expect_success=False)

    # These should succeed
    check_case(pipeline, "0 = 0")
    check_case(pipeline, "Nat.succ 0 = 1")
    check_case(pipeline, "x + 0 = x")
    check_case(pipeline, "-1 + 1 = 0")
    # The input language is not Lean: the implicit product "2ab" and the
    # LaTeX-like macro "\cdot" have to be translated before the compiler
    # sees them, or the pipeline hands Lean a term it cannot read.
    check_case(pipeline, "2a = 2 * a")
    check_case(pipeline, r"a \cdot b = a * b")

    # Verify no-sorry gate
    has_sorry, _ = pipeline.check_for_sorry("theorem t : 0=0 := by sorry", "")
    assert has_sorry == True, "Should detect sorry"
    has_sorry, _ = pipeline.check_for_sorry("theorem t : 0=0 := by rfl", "")
    assert has_sorry == False, "Should not detect sorry"

    print("INTEGRATION OK")


if __name__ == "__main__":
    main()
