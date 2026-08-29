"""Kill-rate harness that reuses tether.verification.measure with a short
per-mutant timeout (to avoid 1800s hangs on infinite-loop mutants such as a
flip_bool turning `changed = False` into `changed = True`).

Usage:
    python3 run_killrate.py --target QED/parser.py \
        --suite QED/test_pipeline.py --max-mutants 60 --min-kill-rate 0.7
"""

import argparse
import subprocess
import sys
from pathlib import Path

# tether.tools is not a package; import the mutation harness by file path.
_TOOLS_DIR = Path("/Users/tom/Documents/apps/tether/tools")
if str(_TOOLS_DIR) not in sys.path:
    sys.path.insert(0, str(_TOOLS_DIR))
from mutation_killrate import measure, format_report  # noqa: E402


def short_runner(timeout: int):
    def run() -> tuple[bool, str]:
        proc = subprocess.run(
            [sys.executable, "-m", "pytest", "-x", "-q",
             "-p", "no:cacheprovider", *SUITES],
            cwd=str(REPO_ROOT), capture_output=True, text=True,
            timeout=timeout,
        )
        detail = (proc.stdout or "")[-2000:] + (proc.stderr or "")[-1000:]
        return proc.returncode == 0, detail
    return run


REPO_ROOT = Path("/Users/tom/Documents/apps")
SUITES: list[str] = []


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--target", required=True)
    ap.add_argument("--suite", action="append", required=True)
    ap.add_argument("--max-mutants", type=int, default=0)
    ap.add_argument("--min-kill-rate", type=float, default=None)
    ap.add_argument("--timeout", type=int, default=15)
    args = ap.parse_args()

    global SUITES
    SUITES = args.suite

    # measure() restores the target byte-for-byte in a finally block, so a
    # killed mutant never corrupts the file between runs.
    report = measure(
        target=args.target,
        repo_root=REPO_ROOT,
        suites=args.suite,
        max_mutants=args.max_mutants,
        runner_factory=lambda r, s: short_runner(args.timeout),
    )
    print(format_report(report))
    if args.min_kill_rate is not None and report["kill_rate"] < args.min_kill_rate:
        print(f"FAIL: kill rate {report['kill_rate']:.4f} < --min-kill-rate "
              f"{args.min_kill_rate}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
