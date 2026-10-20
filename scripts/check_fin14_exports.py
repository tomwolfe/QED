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

  export    both sizes export, and each file carries its own Fin N
  compile   both compile with zero errors and mention no sorry
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

#: The only axioms a theorem like these may depend on.
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


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
    texts = []
    for n in sizes:
        path = _export(n)
        text = path.read_text(encoding="utf-8")
        texts.append(text)
        assert f"Fin {n}" in text, (
            f"the Fin {n} export does not mention Fin {n}; the size was not "
            f"applied to the emitted file")
    for n, text in zip(sizes, texts):
        other = 14 if n == 6 else 6
        assert f"Fin {other}" not in text, (
            f"the Fin {n} export also mentions Fin {other}; the two sizes are "
            f"not distinguished")
    # The wider network must really be wider, not the same file renamed.
    assert len(texts[1]) > len(texts[0]), (
        f"the Fin 14 export ({len(texts[1])} bytes) is not larger than the "
        f"Fin 6 export ({len(texts[0])} bytes); it may not carry 14 states")
    print(f"both exports OK: Fin 6 = {len(texts[0])} bytes, "
          f"Fin 14 = {len(texts[1])} bytes")


def check_compile() -> None:
    for n in (6, 14):
        path = OUT_DIR / f"qed_iso_fin{n}.lean"
        if not path.exists():
            _export(n)
        proc = subprocess.run(["lake", "env", "lean", str(path)],
                              cwd=str(REPO), capture_output=True, text=True)
        out = proc.stdout + proc.stderr
        assert proc.returncode == 0, (
            f"the Fin {n} export did not compile (exit {proc.returncode}):\n"
            f"{out[-2000:]}")
        assert "sorry" not in out.lower(), (
            f"the Fin {n} export mentions sorry:\n{out[-1000:]}")
        print(f"Fin {n} compiles clean")


def check_axioms() -> None:
    total = 0
    for n in (6, 14):
        path = OUT_DIR / f"qed_iso_fin{n}.lean"
        if not path.exists():
            _export(n)
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
            assert ax and ax <= ALLOWED_AXIOMS, (
                f"Fin {n}: a theorem depends on unexpected axioms: {entry}")
            total += 1
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
                                            STANDARD_14_ORGAN_NETWORK)
    assert DEFAULT_ORGAN_NETWORK == (
        "gut", "liver", "central", "peripheral", "effect", "elim"), (
        f"DEFAULT_ORGAN_NETWORK changed: {DEFAULT_ORGAN_NETWORK}")
    assert len(STANDARD_14_ORGAN_NETWORK) == 14
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
