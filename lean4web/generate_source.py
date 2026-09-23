#!/usr/bin/env python3
"""Build the single-file Mathlib edition from the pinned FC and local proof modules."""

from pathlib import Path
import hashlib
import re
import subprocess


HERE = Path(__file__).resolve().parent
LEAN_ROOT = HERE.parent / "lean"
FC_SOURCE = (LEAN_ROOT / ".lake" / "packages" / "formal_conjectures" /
             "FormalConjectures" / "OpenQuantumProblems" / "35.lean")
EXPECTED_FC_REV = "2a46c7bd74505b85f4967475bb733ded0ef8d348"
MODULES = [
    "Data", "Phase", "Finite", "FirstCut", "Factor", "Polynomial",
    "Partition", "MixedPhase", "CharacterSum", "Certificate", "CutData",
    "FastChecks", "CutMatrices", "CutCoverage", "AllCuts", "FCInterface",
    "State", "Reduction", "Existence", "FormalTarget",
]


def fc_definitions() -> str:
    source = FC_SOURCE.read_text(encoding="utf-8")
    begin = source.index("open scoped BigOperators\n\nnamespace OpenQuantumProblem35")
    end = source.index("/-- No absolutely maximally entangled state exists", begin)
    basic = source[begin:end]
    begin = source.index("/-- The number of computational-basis configurations")
    end = source.index("/- ## Constant-support diagonal states -/", begin)
    helpers = source[begin:end]
    result = basic + helpers + "\nend OpenQuantumProblem35\n"
    # FC's metadata attributes are defined in FormalConjecturesUtil, unavailable
    # in Mathlib-only Lean4Web.  They do not change the theorem statements.
    result = re.sub(r"@\[simp, category [^\]]+\]", "@[simp]", result)
    result = re.sub(r"@\[category [^\]]+\]\n", "", result)
    return result


def module_body(name: str) -> str:
    source = (LEAN_ROOT / "AME96" / f"{name}.lean").read_text(encoding="utf-8")
    source = re.sub(r"^import .*$\n?", "", source, flags=re.MULTILINE)
    if name == "Existence":
        # mathlib v4.35 renamed the equivalence of equal set subtypes.
        assert source.count("Equiv.setCongr hrange") == 2
        source = source.replace("Equiv.setCongr hrange", "Set.equivOfEq hrange")
    return source


def main() -> None:
    # The revision is enforced by the neighboring FC Lake dependency.  Its
    # checkout is required here to extract the exact target definitions.
    assert EXPECTED_FC_REV in (LEAN_ROOT / "lakefile.toml").read_text()
    assert FC_SOURCE.is_file(), "run `lake update` in ../lean first"
    actual_rev = subprocess.check_output(
        ["git", "-C", str(FC_SOURCE.parent.parent.parent), "rev-parse", "HEAD"],
        text=True,
    ).strip()
    assert actual_rev == EXPECTED_FC_REV, (actual_rev, EXPECTED_FC_REV)
    header = """import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-!
# AME(9,6): standalone Lean4Web proof

Mathlib-only edition of the pinned Formal Conjectures target. The AME
definitions below are extracted from FormalConjectures/OpenQuantumProblems/35.lean
at commit 2a46c7bd74505b85f4967475bb733ded0ef8d348. FC metadata is omitted.
The explicit witness and proof are generated from ../lean/AME96/*.lean.
-/

-- `answer(True)` is the proposition `True` at the target, as in FC's
-- default answer elaboration. The local macro supplies its surface syntax.
macro "answer(" p:term ")" : term => `($p)

#eval Lean.versionString
#guard Lean.versionString == "4.35.0-rc2"

"""
    parts = [header, fc_definitions()]
    for name in MODULES:
        parts.append(f"\n\n/-! ## Inlined proof module: AME96.{name} -/\n\n")
        parts.append(module_body(name))
    parts.append("\n\n#check AME96.exists_ame_9_6\n")
    parts.append("#check AME96.ame_9_6_answer_true\n")
    parts.append("#print axioms AME96.exists_ame_9_6\n")
    parts.append("#print axioms AME96.ame_9_6_answer_true\n")
    output = HERE / "AME96Lean4Web.lean"
    output.write_text("".join(parts), encoding="utf-8")
    print(f"{output.name}: {output.stat().st_size} bytes, SHA256 "
          f"{hashlib.sha256(output.read_bytes()).hexdigest()}")


if __name__ == "__main__":
    main()
