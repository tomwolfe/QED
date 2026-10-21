"""Pytest configuration for QED.

The pipeline writes a runtime artefact into the repository on every
successful proof, and that artefact is TRACKED: it is the committed record
of the last proof.  Without this file a test run rewrites it and leaves the
working tree dirty -- which is what makes Tether refuse to start the next
mission ("Working tree is dirty; refusing to start the agent"), blocking
every mission that declares QED as a sibling.

The autouse fixture below snapshots the artefact's BYTES before each test
and puts them back afterwards, so a test run leaves the file exactly as it
found it.

The pipeline is NOT silenced: ``run()`` still writes the artefact while the
test runs, and ``check_integration.py`` still finds it.  Only the residue
after the test is undone.

The ``traces.json`` audit trail needs no guard: it is gitignored, so it
cannot dirty the tree.  See ``.gitignore``.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

# The repository root is this file's directory.  It is put on ``sys.path``
# explicitly, so the guard can be imported whatever the invocation directory
# and whatever pytest's import mode decides to do with ``sys.path``.
_REPO_ROOT = Path(__file__).resolve().parent
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from artifact_guard import preserved_artifact  # noqa: E402


@pytest.fixture(autouse=True)
def _restore_the_tracked_artifact():
    """Leave the tracked artefact exactly as the test found it.

    ``LeanAgenticPipeline.run()`` writes ``output.lean`` on every successful
    proof, and that file is tracked.  A test that runs the pipeline
    therefore rewrites a tracked file, and the suite leaves the working
    tree dirty.

    The artefact is snapshotted before the test and restored after it.  The
    restore is a teardown, so it happens even when the test FAILS or
    raises; and it restores the CONTENT, not just the modification time,
    because the sandbox's filesystem-manifest diff fingerprints small files
    by sha256 -- a same-length edit with a fresh mtime is still a change.
    """
    with preserved_artifact(_REPO_ROOT):
        yield
