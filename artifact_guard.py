#!/usr/bin/env python3
"""Snapshot and restore of the runtime artefact QED writes into the repository.

``LeanAgenticPipeline.run()`` writes two files into the working directory:

* ``traces.json`` -- the audit trail.  It is GITIGNORED (see ``.gitignore``),
  so it cannot dirty the tree: it is a pure runtime record and the precedent
  this repository already follows for a generated artefact.
* ``output.lean`` -- the verified Lean source.  It is TRACKED: it is the
  committed, reviewable record of the last proof.

That asymmetry is the whole problem.  A run rewrites the tracked artefact
with whichever proof ran last, so a test suite that runs the pipeline leaves
the working tree dirty -- and a dirty tree is what makes Tether refuse to
start the next mission ("Working tree is dirty; refusing to start the
agent"), which blocks every mission that declares QED as a sibling.

The fix is to make the artefact behave like an artefact: take a snapshot of
its BYTES before a test, and put those bytes back afterwards.

* The restore runs in a ``finally``, so it happens whether the guarded block
  finished, failed an assertion, or raised.
* The restore is of CONTENT, not of the modification time: the sandbox's
  filesystem-manifest diff fingerprints small files by sha256, so a
  same-length edit with a fresh mtime is still a change.
* A file that was NOT there before is removed again, and a file that WAS
  there is never left missing: the restore never creates a file that did not
  exist, and never leaves one that did.

The pipeline is NOT silenced.  ``run()`` still writes the artefact while the
guarded block runs, and ``check_integration.py`` still finds it; only the
residue after the block is undone.
"""

from __future__ import annotations

import os
from contextlib import contextmanager
from pathlib import Path
from typing import Dict, Iterable, Iterator, List, NamedTuple, Optional

#: The tracked artefact ``LeanAgenticPipeline.run()`` writes on every
#: successful proof (``LeanAgenticPipeline.ARTIFACT_FILE``).
ARTIFACT_NAME = "output.lean"

#: The audit trail the same run writes.  It is gitignored, so it cannot dirty
#: the tree; it is named here only to document the pair of artefacts.
TRACE_NAME = "traces.json"


class Snapshot(NamedTuple):
    """What a guarded path looked like before the guarded block ran.

    ``content`` is the file's BYTES, or None when the bytes could not be
    read.  ``existed`` distinguishes "the file was not there" from "the file
    was there but could not be read" -- only the first may be removed by the
    restore.
    """

    existed: bool
    content: Optional[bytes]
    mtime_ns: Optional[int]


def repository_root() -> Path:
    """The directory this module lives in: the repository root."""
    return Path(__file__).resolve().parent


def artifact_paths(root: Optional[Path] = None) -> List[Path]:
    """Every path a run may write the tracked artefact to.

    The pipeline writes ``output.lean`` RELATIVE to the process's working
    directory, so the artefact lands in the repository root when the suite
    runs from there and in the caller's directory otherwise.  Both are
    guarded, so the restore cannot be evaded by running from somewhere else.
    """
    directories: List[Path] = [
        Path(root) if root is not None else repository_root()
    ]
    try:
        directories.append(Path.cwd())
    except OSError:  # pragma: no cover - the cwd was removed under us
        pass

    paths: List[Path] = []
    for directory in directories:
        try:
            resolved = directory.resolve()
        except OSError:  # pragma: no cover - an unreadable directory
            continue
        path = resolved / ARTIFACT_NAME
        if path not in paths:
            paths.append(path)
    return paths


def snapshot(paths: Iterable[Path]) -> Dict[Path, Snapshot]:
    """The bytes (and modification time) of each path.

    A path that does not exist is recorded as ``existed=False``: that is the
    difference between "restore this file" and "do not leave this file
    behind".
    """
    taken: Dict[Path, Snapshot] = {}
    for path in paths:
        try:
            stat = path.stat()
        except OSError:
            taken[path] = Snapshot(existed=False, content=None, mtime_ns=None)
            continue
        try:
            content: Optional[bytes] = path.read_bytes()
        except OSError:
            content = None
        taken[path] = Snapshot(
            existed=True, content=content, mtime_ns=stat.st_mtime_ns)
    return taken


def restore(taken: Dict[Path, Snapshot]) -> None:
    """Put the guarded paths back exactly as :func:`snapshot` found them.

    * a path that existed is restored BYTE FOR BYTE -- content first, so a
      same-length edit is undone as well as a different-length one;
    * a path that did NOT exist is removed again, so the restore never
      creates a file that was not there;
    * a path that existed is never left missing.

    A path that cannot be written (permissions, a directory in the way) is
    left alone rather than raising: a cleanup must never turn a passing test
    into a failing one.
    """
    for path, state in taken.items():
        if not state.existed:
            # It was not there before, so it must not be there after.
            try:
                path.unlink()
            except OSError:
                pass
            continue
        if state.content is None:
            # The file was there but could not be read: leave it alone
            # rather than replacing it with nothing.
            continue
        try:
            path.write_bytes(state.content)
        except OSError:
            continue
        if state.mtime_ns is not None:
            try:
                os.utime(path, ns=(state.mtime_ns, state.mtime_ns))
            except OSError:
                pass


@contextmanager
def preserved_artifact(root: Optional[Path] = None) -> Iterator[None]:
    """Restore the tracked artefact to the bytes it had on entry.

    The restore happens in a ``finally``, so it runs whether the guarded
    block finished, failed an assertion, or raised.
    """
    taken = snapshot(artifact_paths(root))
    try:
        yield
    finally:
        restore(taken)
