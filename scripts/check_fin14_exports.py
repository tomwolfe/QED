#!/usr/bin/env python3
"""Checks for the Fin 6 and Fin 14 Lean isomorphism exports.

The tri-repo gate's context block claimed the exporter "emits the N-generic
isomorphism file". GLOBAL_MINIMUM_REPORT.md audited that claim and found it
false for the live path: the exporter took N = len(DEFAULT_ORGAN_NETWORK) = 6,
the emitted file contained only Fin 6 and Fin 9, and `--fin-n 14` was a
separate, UNPROVEN path -- the gate certified Fin 6 only.

`_network_for_fin` did accept 6 and 14; what was unproven was the end-to-end
path for 14: emit it, compile it, and check its axioms. This script does
exactly that, and it exists as a file rather than as a pile of one-line
`python3 -c` gates because Tether runs verification commands with
`shlex.split` and `shell=False`: a YAML-folded multi-line Python payload
becomes a SyntaxError (a compound statement cannot follow a semicolon), and
that failure looks like a broken deliverable rather than a broken gate.

Each check is a separate subcommand so a mission gate can name the specific
property it is asserting:

  export    both sizes export, and each file carries its own Fin N and its
            own N states' worth of matrix arms
  compile   both compile with zero errors against the PINNED toolchain and
            mention no sorry
  axioms    #print axioms for each headline theorem is exactly the three
            standard axioms, for BOTH sizes
  network   _network_for_fin maps 6 and 14 and rejects every other size
  default   DEFAULT_ORGAN_NETWORK is unchanged and 14 is not promoted
  leakage   QED stays domain-agnostic (no PBPK/organ vocabulary in its core)

Exit code 0 = all selected checks pass; non-zero = the failing check's
assertion message is on stderr.
"""
from __future__ import annotations

import argparse
import importlib.util
import inspect
import pathlib
import re
import subprocess
import sys

REPO = pathlib.Path(__file__).resolve().parent.parent
VERITRIAL = REPO.parent / "VeriTrial"
EXPORT_SCRIPT = VERITRIAL / "scripts" / "export_pbpk_to_qed.py"
OUT_DIR = pathlib.Path("/tmp")

#: The theorems whose axioms the gate checks.
HEADLINE = (
    "extracted_offDiag_nonneg",
    "extracted_colSum_eq_zero",
    "veritrial_mass_dissipation",
)

#: The only axioms a theorem like these may depend on -- and, because the
#: mission asks for them EXACTLY, the set it must depend on.
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

#: A matrix arm in the emitted Lean: ``if i.val = I ∧ j.val = J then``.
#: The state indices of these arms are what makes the file a model of an
#: N-state system, so they are what the export check reads.
_MATRIX_ARM_RE = re.compile(r"if i\.val = (\d+) ∧ j\.val = (\d+) then")


def _export(n: int) -> pathlib.Path:
    """Export the isomorphism file for Fin n; return its path."""
    out = OUT_DIR / f"qed_iso_fin{n}.lean"
    proc = subprocess.run(
        [sys.executable, str(EXPORT_SCRIPT),
         "--fin-n", str(n),
         "--lean-out", str(out),
         "--out", str(OUT_DIR / f"fin{n}_lemmas.txt")],
        capture_output=True, text=True, cwd=str(VERITRIAL),
    )
    if proc.returncode != 0:
        raise AssertionError(
            f"export --fin-n {n} failed (exit {proc.returncode}):\n"
            f"{proc.stdout[-1500:]}\n{proc.stderr[-1500:]}")
    return out


def _ensure_export(n: int) -> pathlib.Path:
    """The exported Lean file for Fin n, exporting it if it is not there."""
    out = OUT_DIR / f"qed_iso_fin{n}.lean"
    if not out.exists():
        _export(n)
    return out


def _matrix_arms(text: str) -> list[tuple[int, int]]:
    """The (row, column) state indices of every arm of the emitted matrix.

    An N-state model has arms over 0..N-1.  Reading the indices out of the
    emitted arms is how the check distinguishes "fourteen states' worth of
    matrix arms" from "six arms, renamed": a renamed file still says
    ``Fin 14``, but its arms still cover six states.
    """
    return [(int(i), int(j)) for i, j in _MATRIX_ARM_RE.findall(text)]


def _pinned_lean_version() -> str:
    """The Lean version the repository pins (``lean-toolchain``).

    ``leanprover/lean4:v4.33.0`` -> ``4.33.0``.
    """
    raw = (REPO / "lean-toolchain").read_text(encoding="utf-8").strip()
    tag = raw.rsplit(":", 1)[-1]
    return tag[1:] if tag.startswith("v") else tag


def _load_export_module():
    """Import VeriTrial's export script as a module (it is not a package)."""
    for p in (str(VERITRIAL / "src"), str(VERITRIAL)):
        if p not in sys.path:
            sys.path.insert(0, p)
    spec = importlib.util.spec_from_file_location("export_pbpk_to_qed", EXPORT_SCRIPT)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def check_export() -> None:
    sizes = (6, 14)
    texts = {}
    for n in sizes:
        path = _export(n)
        texts[n] = path.read_text(encoding="utf-8")
        assert f"Fin {n}" in texts[n], (
            f"the Fin {n} export does not mention Fin {n}; the size was not "
            f"applied to the emitted file")
    for n, text in texts.items():
        other = 14 if n == 6 else 6
        assert f"Fin {other}" not in text, (
            f"the Fin {n} export also mentions Fin {other}; the two sizes are "
            f"not distinguished")
    # The wider network must really be wider, not the same file renamed.
    assert len(texts[14]) > len(texts[6]), (
        f"the Fin 14 export ({len(texts[14])} bytes) is not larger than the "
        f"Fin 6 export ({len(texts[6])} bytes); it may not carry 14 states")
    # ... and it must carry fourteen STATES, not fourteen LABELS: the arms
    # of the emitted matrix must cover exactly the states 0..N-1.
    for n, text in texts.items():
        arms = _matrix_arms(text)
        assert arms, f"the Fin {n} export has no matrix arms"
        covered = {i for i, _ in arms} | {j for _, j in arms}
        assert covered == set(range(n)), (
            f"the Fin {n} export's matrix arms cover states "
            f"{sorted(covered)}, not exactly 0..{n - 1}")
        assert len(arms) >= n, (
            f"the Fin {n} export has only {len(arms)} matrix arms for "
            f"{n} states")
    assert len(_matrix_arms(texts[14])) > len(_matrix_arms(texts[6])), (
        f"the Fin 14 export has {len(_matrix_arms(texts[14]))} matrix arms, "
        f"not more than the Fin 6 export's {len(_matrix_arms(texts[6]))}")
    print(f"both exports OK: Fin 6 = {len(texts[6])} bytes / "
          f"{len(_matrix_arms(texts[6]))} arms, "
          f"Fin 14 = {len(texts[14])} bytes / "
          f"{len(_matrix_arms(texts[14]))} arms")


def check_compile() -> None:
    expected = _pinned_lean_version()
    version = subprocess.run(
        ["lake", "env", "lean", "--version"],
        cwd=str(REPO), capture_output=True, text=True)
    assert version.returncode == 0, (
        f"could not run the pinned Lean:\n{version.stdout}\n"
        f"{version.stderr}")
    assert f"version {expected}" in version.stdout, (
        f"the compiler is not the pinned toolchain: expected Lean "
        f"{expected}, got {version.stdout.strip()!r}")
    for n in (6, 14):
        path = _ensure_export(n)
        proc = subprocess.run(["lake", "env", "lean", str(path)],
                              cwd=str(REPO), capture_output=True, text=True)
        out = proc.stdout + proc.stderr
        assert proc.returncode == 0, (
            f"the Fin {n} export did not compile (exit {proc.returncode}):\n"
            f"{out[-2000:]}")
        assert not re.search(r"^error", out, re.MULTILINE), (
            f"the Fin {n} export reports an error:\n{out[-1000:]}")
        assert "sorry" not in out.lower(), (
            f"the Fin {n} export mentions sorry:\n{out[-1000:]}")
        print(f"Fin {n} compiles clean on Lean {expected}")


def check_axioms() -> None:
    total = 0
    for n in (6, 14):
        path = _ensure_export(n)
        text = path.read_text(encoding="utf-8")
        present = [nm for nm in HEADLINE
                   if re.search(r"theorem\s+" + nm + r"\b", text)]
        assert present, (
            f"the Fin {n} export is missing the headline theorems "
            f"{HEADLINE}")
        probe = OUT_DIR / f"axioms_fin{n}.lean"
        probe.write_text(
            text + "\n" + "\n".join("#print axioms " + nm for nm in present) + "\n",
            encoding="utf-8")
        proc = subprocess.run(["lake", "env", "lean", str(probe)],
                              cwd=str(REPO), capture_output=True, text=True)
        out = proc.stdout + proc.stderr
        assert proc.returncode == 0, (
            f"the axiom probe for Fin {n} failed:\n{out[-2000:]}")
        found = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", out)
        assert len(found) == len(present), (
            f"Fin {n}: expected {len(present)} axiom lines, got {found}")
        for entry in found:
            ax = {a.strip() for a in entry.split(",") if a.strip()}
            # EXACTLY the three standard axioms: a subset would still let a
            # theorem that leans on, say, `sorryAx` through.
            assert ax == ALLOWED_AXIOMS, (
                f"Fin {n}: the axiom set is {sorted(ax)}, not exactly "
                f"{sorted(ALLOWED_AXIOMS)}")
            total += 1
        assert "sorryAx" not in out, (
            f"the Fin {n} axiom probe reports sorryAx:\n{out[-1000:]}")
        print(f"Fin {n} axioms clean ({len(found)} theorems)")
    print(f"{total} theorem axiom sets are exactly {sorted(ALLOWED_AXIOMS)}")


def check_network() -> None:
    module = _load_export_module()
    from insilico_trial.pbpk.model import (DEFAULT_ORGAN_NETWORK,
                                            STANDARD_14_ORGAN_NETWORK)
    assert module._network_for_fin(6) == DEFAULT_ORGAN_NETWORK, (
        "Fin 6 does not map to DEFAULT_ORGAN_NETWORK")
    assert module._network_for_fin(14) == STANDARD_14_ORGAN_NETWORK, (
        "Fin 14 does not map to STANDARD_14_ORGAN_NETWORK")
    assert len(DEFAULT_ORGAN_NETWORK) == 6, (
        f"DEFAULT_ORGAN_NETWORK has {len(DEFAULT_ORGAN_NETWORK)} organs, not 6")
    assert len(STANDARD_14_ORGAN_NETWORK) == 14, (
        f"STANDARD_14_ORGAN_NETWORK has {len(STANDARD_14_ORGAN_NETWORK)} "
        f"organs, not 14")
    for bad in (0, 1, 5, 7, 13, 15, 99):
        try:
            module._network_for_fin(bad)
        except ValueError:
            continue
        raise AssertionError(
            f"_network_for_fin({bad}) should have raised ValueError")
    print("_network_for_fin accepts 6 and 14 and rejects every other size")


def check_default() -> None:
    for p in (str(VERITRIAL / "src"), str(VERITRIAL)):
        if p not in sys.path:
            sys.path.insert(0, p)
    from insilico_trial.pbpk.model import (DEFAULT_ORGAN_NETWORK,
                                            STANDARD_14_ORGAN_NETWORK,
                                            make_pbpk_ode, organ_indices)
    assert DEFAULT_ORGAN_NETWORK == (
        "gut", "liver", "central", "peripheral", "effect", "elim"), (
        f"DEFAULT_ORGAN_NETWORK changed: {DEFAULT_ORGAN_NETWORK}")
    assert len(DEFAULT_ORGAN_NETWORK) == 6
    assert len(STANDARD_14_ORGAN_NETWORK) == 14
    # The validated six-state model must keep working exactly as it does
    # today: the model's own entry points still default to the six-organ
    # network, and Fin 14 is not silently promoted underneath them.
    for fn in (make_pbpk_ode, organ_indices):
        default = inspect.signature(fn).parameters["organ_network"].default
        assert default == DEFAULT_ORGAN_NETWORK, (
            f"{fn.__name__} now defaults to {default!r}, not "
            f"DEFAULT_ORGAN_NETWORK")
    # The exporter's own default (no --fin-n) must still be the Fin 6 file:
    # promoting Fin 14 to the default would show up here first.
    default_out = OUT_DIR / "qed_iso_default.lean"
    proc = subprocess.run(
        [sys.executable, str(EXPORT_SCRIPT),
         "--lean-out", str(default_out),
         "--out", str(OUT_DIR / "default_lemmas.txt")],
        capture_output=True, text=True, cwd=str(VERITRIAL))
    assert proc.returncode == 0, (
        f"the default export failed (exit {proc.returncode}):\n"
        f"{proc.stdout[-1500:]}\n{proc.stderr[-1500:]}")
    default_text = default_out.read_text(encoding="utf-8")
    fin6_text = _ensure_export(6).read_text(encoding="utf-8")
    assert default_text == fin6_text, (
        "the exporter's default (no --fin-n) output is no longer the Fin 6 "
        "file: the default moved")
    assert "Fin 6" in default_text and "Fin 14" not in default_text, (
        "the exporter's default output is not a Fin 6 file")
    print("DEFAULT_ORGAN_NETWORK unchanged; Fin 14 is not promoted")


def check_leakage() -> None:
    """QED must stay domain-agnostic: no PBPK/organ vocabulary in its core."""
    pattern = re.compile(r"pbpk|liver|dili|cyp|ka_rate", re.I)
    hits = [(name, lineno, line)
            for name in ("parser.py", "agentic_pipeline.py")
            for lineno, line in enumerate(
                (REPO / name).read_text(encoding="utf-8").splitlines(), 1)
            if pattern.search(line)]
    assert not hits, (
        f"QED is no longer domain-agnostic; {len(hits)} hit(s), first: {hits[:3]}")
    print("zero domain leakage in parser.py and agentic_pipeline.py")


CHECKS = {
    "export": check_export,
    "compile": check_compile,
    "axioms": check_axioms,
    "network": check_network,
    "default": check_default,
    "leakage": check_leakage,
}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("check", choices=sorted(CHECKS))
    args = ap.parse_args()
    try:
        CHECKS[args.check]()
    except AssertionError as exc:
        print(f"FAIL [{args.check}]: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
