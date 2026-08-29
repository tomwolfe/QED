#!/usr/bin/env python3
"""Verify PBPK mass-conservation lemmas exported by VeriTrial, via QED.

Reads a file of QED-parseable LaTeX lemmas (one per line) as produced by
``VeriTrial/scripts/export_pbpk_to_qed.py`` and verifies each one with QED's
agentic pipeline (which proves structural identities by reflexivity, no sorry).

Exits non-zero if ANY lemma fails to verify, so this script can serve
directly as a single tether verification command. Each lemma is run through
``agentic_pipeline.py`` (which writes ``traces.json``), so the final
``traces.json`` reflects the last verified lemma for assertion checks.
"""

from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path

QED_DIR = Path(__file__).resolve().parent


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("lemmas", type=Path,
                    help="file of lemmas, one per line")
    ap.add_argument("--python", default=sys.executable,
                    help="python interpreter to invoke QED with")
    args = ap.parse_args(argv)

    if not args.lemmas.is_file():
        print(f"lemmas file not found: {args.lemmas}", file=sys.stderr)
        return 1

    lemmas = [line.strip() for line in args.lemmas.read_text().splitlines()
              if line.strip()]
    if not lemmas:
        print("no lemmas to verify", file=sys.stderr)
        return 1

    failures = 0
    for lemma in lemmas:
        proc = subprocess.run(
            [args.python, str(QED_DIR / "agentic_pipeline.py"), lemma],
            cwd=str(QED_DIR),
            capture_output=True,
            text=True,
            timeout=300,
        )
        if proc.returncode != 0:
            failures += 1
            print(f"FAILED: {lemma}")
            print(proc.stderr[-500:])
        else:
            print(f"verified: {lemma}")

    if failures:
        print(f"\n{failures}/{len(lemmas)} lemmas failed verification",
              file=sys.stderr)
        return 1
    print(f"\nall {len(lemmas)} lemmas verified by QED (no sorry)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
