#!/usr/bin/env python3
"""Checks that a digit-suffixed identifier is ONE identifier, digits kept.

The parser used to split a single letter followed by a digit, so ``Q3``
reached the prover as the product ``Q * 3``.  Every indexed state then
collapsed onto its stem: ``Q3`` and ``Q4`` were the SAME variable, and the
digits were dropped.  A theorem that quantifies over ``Q3..Q12`` was
therefore read by the prover as a theorem about ``Q``.

This script exists as a FILE rather than as one-line ``python3 -c`` gates
because Tether runs verification commands with ``shlex.split`` and
``shell=False``: a YAML-folded multi-line Python payload becomes a
SyntaxError (a compound statement cannot follow a semicolon), and that
failure looks like a broken deliverable rather than a broken gate.

Each check is a separate subcommand so a mission gate can name the
specific property it is asserting:

  suffix    ``Q3`` and ``Q4`` are two DIFFERENT variables, and a multi-digit
            suffix (``Q12``) survives intact
  numeric   a genuine numeric literal is still a NUMBER, not a name
  names     the indexed-state identity names every state it mentions and
            no bare stem
  ka        the pre-existing bare-two-letter contract (``ka`` -> ``k * a``)
            is unchanged: the digit-suffix fix is a SEPARATE rule
  prove     a parametric Real-typed goal over INDEXED states still proves,
            with the positivity hypotheses and with no sorry
  fidelity  the Fin 14 lemma set, parsed by QED, names every indexed state
            and no bare stem -- the fidelity claim the export gate rests on

Exit code 0 = all selected checks pass; non-zero = the failing check's
assertion message is on stderr.
"""
from __future__ import annotations

import argparse
import pathlib
import re
import sys

REPO = pathlib.Path(__file__).resolve().parent.parent
if str(REPO) not in sys.path:
    sys.path.insert(0, str(REPO))

from parser import is_numeric_equality, parse_equation  # noqa: E402

#: The indexed states the Fin 14 lemma set mentions.  These are STRUCTURAL
#: names -- the point is the digit suffix, not what the state stands for.
INDEXED_STATES = tuple(
    f"{prefix}{index}"
    for prefix in ("Q", "V")
    for index in range(3, 13)
)

#: The stems that must NOT appear once the digit suffix is kept: a bare
#: ``Q`` means the suffix was dropped and two states became one variable.
BARE_STEMS = ("Q", "V")


def check_suffix() -> None:
    """A digit-suffixed identifier is ONE identifier, with the digits."""
    node, free_vars = parse_equation("(Q3/Vc) + (Q4/Vc) = 0")
    assert node is not None, "the indexed-state expression does not parse"
    assert "Q3" in free_vars and "Q4" in free_vars, (
        "digit-suffixed identifiers are not kept: " + str(free_vars))
    assert "Q" not in free_vars, (
        "a digit-suffixed identifier collapsed onto its stem: "
        + str(free_vars))
    assert "Vc" in free_vars, "the plain name was lost: " + str(free_vars)
    # A MULTI-digit suffix survives whole: ``Q12`` is one identifier and is
    # not ``Q`` plus the number ``12``.
    node, free_vars = parse_equation("(Q12/Vc) = 0")
    assert node is not None, "the multi-digit suffix expression does not parse"
    assert free_vars == ["Q12", "Vc"], (
        "the multi-digit suffix was not kept: " + str(free_vars))
    print("digit-suffixed identifiers are distinct and keep their digits")


def check_numeric() -> None:
    """A genuine number is still a number, never a name."""
    node, free_vars = parse_equation("129 = 129")
    assert node is not None, "the numeric equality does not parse"
    assert free_vars == [], (
        "a closed numeric equality was read as a statement about "
        "variables: " + str(free_vars))
    assert is_numeric_equality("129 = 129") is True, (
        "a closed numeric equality is no longer classified as one")
    print("numeric literals still parse as numbers")


def check_names() -> None:
    """The indexed-state identity names every state it mentions."""
    statement = (
        "(-ka_rate) + (ka_rate) + (-Ql/(Kpl*Vl)) + (Ql/(Kpl*Vl)) + (Ql/Vc)"
        " + (-(CL + Ql + Q3 + Q4 + Q5 + Q6 + Q7 + Q8 + Q9 + Q10 + Q11 + Q12)/Vc)"
        " + (Q3/Vc) + (Q4/Vc) + (Q5/Vc) + (Q6/Vc) + (Q7/Vc) + (Q8/Vc)"
        " + (Q9/Vc) + (Q10/Vc) + (Q11/Vc) + (Q12/Vc) + (CL/Vc)"
        " + (Q3/(Kp3*V3)) + (-Q3/(Kp3*V3)) + (Q4/(Kp4*V4)) + (-Q4/(Kp4*V4))"
        " + (Q5/(Kp5*V5)) + (-Q5/(Kp5*V5)) + (Q6/(Kp6*V6)) + (-Q6/(Kp6*V6))"
        " + (Q7/(Kp7*V7)) + (-Q7/(Kp7*V7)) + (Q8/(Kp8*V8)) + (-Q8/(Kp8*V8))"
        " + (Q9/(Kp9*V9)) + (-Q9/(Kp9*V9)) + (Q10/(Kp10*V10))"
        " + (-Q10/(Kp10*V10)) + (Q11/(Kp11*V11)) + (-Q11/(Kp11*V11))"
        " + (Q12/(Kp12*V12)) + (-Q12/(Kp12*V12)) = 0")
    node, free_vars = parse_equation(statement)
    assert node is not None, "the indexed-state identity does not parse"
    for prefix in ("Q", "Kp", "V"):
        for index in range(3, 13):
            name = f"{prefix}{index}"
            assert name in free_vars, (
                f"the identity does not name {name}: " + str(free_vars))
    for stem in BARE_STEMS:
        assert stem not in free_vars, (
            f"a bare {stem} appears: the digit suffix was dropped: "
            + str(free_vars))
    print("the indexed-state identity names every state it mentions")


def check_ka() -> None:
    """The bare-two-letter contract (``ka`` -> ``k * a``) is unchanged.

    The digit-suffix fix and the letter-pair rule are SEPARATE rules, and
    only the letter-then-digit direction changed.  If this check ever
    fails, the two rules became entangled and that must be said out loud.
    """
    node, free_vars = parse_equation("(-ka) + (ka) = 0")
    assert node is not None, "the bare-two-letter expression does not parse"
    assert free_vars == ["a", "k"], (
        "the bare two-letter name is no longer split into its factors: "
        + str(free_vars))
    node, free_vars = parse_equation("(-ka_rate) + (ka_rate) = 0")
    assert node is not None, "the underscored name does not parse"
    assert free_vars == ["ka_rate"], (
        "the underscored name was split: " + str(free_vars))
    print("the bare-two-letter rule is unchanged")


def check_fidelity(lemma_file: str) -> None:
    """The exported lemma set names every indexed state it mentions.

    This is the fidelity claim: the prover must certify a theorem about the
    variables the statement actually names.  A dropped digit suffix makes
    the parsed-name set disagree with the statement, and the proved theorem
    is then not the stated one.
    """
    path = pathlib.Path(lemma_file)
    assert path.is_file(), f"the lemma file does not exist: {path}"
    lines = [ln.strip() for ln in path.read_text(encoding="utf-8").splitlines()
             if ln.strip()]
    assert lines, f"the lemma file is empty: {path}"
    wanted: set[str] = set()
    for line in lines:
        node, free_vars = parse_equation(line)
        assert node is not None, "a lemma does not parse: " + line
        wanted |= set(free_vars or [])
    missing = [name for name in INDEXED_STATES if name not in wanted]
    assert not missing, (
        "the lemma set does not name every indexed state: "
        + str(missing) + " in " + str(sorted(wanted)))
    for stem in BARE_STEMS:
        assert stem not in wanted, (
            f"a bare {stem} appears in the parsed names: "
            + str(sorted(wanted)))
    print(f"the lemma set names every indexed state ({len(lines)} lemmas)")


def check_leakage() -> None:
    """QED must stay domain-agnostic: no organ vocabulary in its core."""
    pattern = re.compile(r"pbpk|liver|dili|cyp|ka_rate", re.I)
    hits = [(name, lineno, line)
            for name in ("parser.py", "agentic_pipeline.py")
            for lineno, line in enumerate(
                (REPO / name).read_text(encoding="utf-8").splitlines(), 1)
            if pattern.search(line)]
    assert not hits, (
        f"QED is no longer domain-agnostic; {len(hits)} hit(s), first: "
        f"{hits[:3]}")
    print("zero domain leakage in parser.py and agentic_pipeline.py")


def check_prove() -> None:
    """A parametric Real-typed goal over INDEXED states still proves.

    The parser change must not cost provability, and it must not weaken the
    no-sorry criterion to get there: the goal is proved for real, the proof
    carries no sorry, and the axioms check reports the theorem is clean.

    The goal is a ratio over two INDEXED names (``Q3 / V3``): it is the
    shape the fix is about, and a parser that read the digits as numbers
    would produce a different -- and much easier -- theorem.
    """
    from agentic_pipeline import LeanAgenticPipeline
    from artifact_guard import preserved_artifact

    pipeline = LeanAgenticPipeline(use_mathlib=True)
    if not pipeline.use_mathlib:
        # No Mathlib: the proof is out of reach here, and the gate must say
        # so rather than pretend.  It must still not carry a sorry.
        with preserved_artifact():
            result = pipeline.run("Q3 / V3 > 0", max_iterations=3)
        assert result.get("success") is False, (
            "the goal proved without Mathlib: the gate is not measuring what "
            "it claims to measure")
        assert "sorry" not in (result.get("lean_code") or ""), (
            "the failed run carried a sorry")
        print("no Mathlib: the goal could not be proved here, and no sorry "
              "was emitted")
        return
    # The run writes the TRACKED artefact (``output.lean``); the guard puts
    # it back, so a verification gate does not leave the tree dirty.
    with preserved_artifact():
        result = pipeline.run("Q3 / V3 > 0")
    assert result.get("success") is True, (
        "the indexed-state positivity goal did not prove: "
        + str(result.get("error")))
    code = result.get("lean_code") or ""
    assert "sorry" not in code, "the proof carries a sorry"
    assert "sorryAx" not in code, "the proof leans on sorryAx"
    verification = result.get("verification") or {}
    assert verification.get("axioms_check") == "passed", (
        "the axioms check did not pass: " + str(verification))
    # The theorem must quantify over the INDEXED names, digits kept.
    assert "(Q3 : ℝ)" in code and "(V3 : ℝ)" in code, (
        "the theorem does not quantify over the indexed names: " + code)
    assert "(hQ3 : 0 < Q3)" in code, (
        "the positivity hypothesis for the indexed name is missing: " + code)
    print("the indexed-state goal proves with no sorry and clean axioms")


CHECKS = {
    "suffix": check_suffix,
    "numeric": check_numeric,
    "names": check_names,
    "ka": check_ka,
    "leakage": check_leakage,
    "prove": check_prove,
}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("check", choices=sorted([*CHECKS, "fidelity"]))
    ap.add_argument(
        "--lemmas",
        default="/tmp/fin14_lemmas.txt",
        help="the exported lemma file the fidelity check reads",
    )
    args = ap.parse_args()
    try:
        if args.check == "fidelity":
            check_fidelity(args.lemmas)
        else:
            CHECKS[args.check]()
    except AssertionError as exc:
        print(f"FAIL [{args.check}]: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
