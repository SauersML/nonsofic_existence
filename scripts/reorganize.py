#!/usr/bin/env python3
"""Phase 2: move the flat library into directories that mirror the paper.

    python3 scripts/reorganize.py            # plan only, changes nothing
    python3 scripts/reorganize.py --apply    # git mv + rewrite every import

BLOCKED, and deliberately not run.  See `docs/REORGANIZATION.md`: the
manuscript names 82 modules in its margin notes and hyperlinks each to
`NonsoficGroupsExist/<Module>.lean`.  Moving a module breaks both -- the link
404s, and `scripts/check.py` reports a dangling reference.  Neither can be
repaired from this side; `\\leanfileurl` in the `.tex` has to learn about
paths first.

So this script exists to make that a decision rather than an obstacle: it
prints the plan, and `--apply` performs it once the manuscript can follow.
The assignment below is by hand because the import graph does not determine
it -- `FiniteGraph` is used by the Kun layer and the matching toolkit alike,
and only the paper says which section it belongs to.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
LIB = "NonsoficGroupsExist"

# directory -> (what lives there, TeX section it backs, module prefixes/names)
LAYOUT: dict[str, tuple[str, str, tuple[str, ...]]] = {
    "Sofic": (
        "Hamming models, sofic approximations, LEF, and the error calculus",
        "sec:prelim",
        ("Sofic", "SoficErrors", "SoficRestriction", "SoficTransfer",
         "SoficPositiveControl", "SemanticPositiveControls", "LEF",
         "ThompsonFObstruction", "Asymptotics", "AlmostAutomorphism"),
    ),
    "Kazhdan": (
        "property (T): definition, GNS, complexification, universe lifting",
        "subsec:sofic",
        ("Kazhdan", "KazhdanComplex", "KazhdanUniverse", "KazhdanGNS",
         "KazhdanFiniteModel", "KazhdanFiniteGeneration", "KazhdanControl",
         "KazhdanImprovement", "KazhdanGenerators", "KazhdanOrthogonal",
         "KazhdanFixedSpace", "KazhdanTextbook", "HilbertComplexification",
         "HilbertCircumcenter", "HilbertConvexFixedPoint",
         "HilbertEpsilonOrthogonality", "GaussianPositiveDefinite",
         "PositiveOperatorGap", "DelormeFixedPoint", "UltralimitGeometry",
         "AlmostMinimalDisplacement", "ShalomFinitePresentation"),
    ),
    "PropertyT": (
        "the A2 / free-root tower proving property (T) for EL3",
        "thm:ejz",
        ("A2", "FreeRoot", "FreeAlgebraDegree", "FreeElementaryPropertyT",
         "FiniteFieldElementaryPropertyT", "FiniteTypeCharacteristicTwoPropertyT",
         "CharacterMass", "ClassTwo", "FiniteClassTwo", "InvolutionSplitting",
         "FiniteInvolutionDecomposition", "FiniteGroupAverage",
         "FiniteOrbitRepresentation", "OrthogonalRepresentationDecomposition",
         "NormalEdgeCodistance"),
    ),
    "Kun": ("Kun's expander decomposition", "thm:kun", ("Kun",)),
    "KunThom": ("the Kun--Thom centralizer obstruction", "thm:kunthom", ("KunThom",)),
    "Matching": (
        "the five finite lemmas and the finite-graph substrate",
        "sec:toolkit",
        ("Refinement", "Pinning", "Selection", "MedianNormalization",
         "PermutationConservation", "FiniteGraph", "FiniteMedian",
         "FiniteMarkov", "DirectedCoarea", "Localization", "Component",
         "Normalized", "InverseNormalization", "GlobalVariation",
         "SlowThreshold", "Block", "Generator", "Edge", "Decomposition",
         "Matched", "Matching", "Completion", "Selected", "Conservative",
         "Essential", "MaximalCutRepair", "Compression",
         "ExternalCompressorCrossing"),
    ),
    "Criterion": (
        "the local compression--centralizer theorem and its assembly",
        "sec:criterion",
        ("Criterion", "LocalCriterion", "LocalizedApproximation",
         "SelectionOutput", "CriterionAssembly", "CompressionSetup", "Scheme"),
    ),
    "Leavitt": (
        "Leavitt families, self-similarity, corners, Thompson's V",
        "sec:leavitt",
        ("Leavitt", "UniversalLeavitt", "BinaryLeavitt", "Whitehead",
         "ElementaryGroup", "ElementaryRoots", "ElementaryStabilization",
         "MatrixSelfSimilarity", "PrefixCode", "ThompsonV", "ThompsonWitness",
         "Diagonal", "Family", "Matrix", "Rank", "Universal",
         "FiniteFieldLeavitt", "UnitsGLProfile"),
    ),
    "KOne": (
        "the pencil elimination giving K1(L) = 0",
        "app:K1",
        ("Pencil", "Code", "Window", "Residual", "Balanced", "Graded",
         "Entry", "Stack", "Atom", "Mixed", "Master", "Narrow", "Refine",
         "Strict", "Zero", "Width", "Full", "Mirror", "Row", "GL",
         "Vandermonde", "Scaled", "Shape", "Nilpotent", "Pure", "Cylinder",
         "Degree", "Theta", "Opposite", "Incomparable", "Stable", "Tail",
         "Base", "Field", "AllRanks", "CompleteCodeSupply"),
    ),
    "Covers": (
        "the finite-table and Kazhdan finitely presented covers",
        "sec:fp",
        ("TableCover", "KazhdanCover"),
    ),
    "Endpoint": (
        "the public results, the reading path, and the axiom report",
        "sec:intro",
        ("MainResults", "Public", "Audit"),
    ),
}


def assign(module: str) -> str | None:
    """The directory a module belongs in: longest matching prefix wins."""
    best: tuple[int, str] | None = None
    for directory, (_, _, prefixes) in LAYOUT.items():
        for prefix in prefixes:
            if module == prefix or module.startswith(prefix):
                if best is None or len(prefix) > best[0]:
                    best = (len(prefix), directory)
    return best[1] if best else None


def plan() -> tuple[dict[str, str], list[str]]:
    modules = sorted(p.stem for p in (REPO / LIB).glob("*.lean"))
    moves: dict[str, str] = {}
    unassigned: list[str] = []
    for module in modules:
        directory = assign(module)
        if directory is None:
            unassigned.append(module)
        else:
            moves[module] = f"{directory}/{module}"
    return moves, unassigned


def apply(moves: dict[str, str]) -> None:
    for module, target in moves.items():
        dest = REPO / LIB / f"{target}.lean"
        dest.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(["git", "mv", f"{LIB}/{module}.lean", f"{LIB}/{target}.lean"],
                       cwd=REPO, check=True)

    rename = {m: t.replace("/", ".") for m, t in moves.items()}
    pattern = re.compile(rf"^import {LIB}\.(\w+)$", re.M)
    targets = list((REPO / LIB).rglob("*.lean")) + [REPO / f"{LIB}.lean"]
    for path in targets:
        text = path.read_text(encoding="utf-8")
        new = pattern.sub(
            lambda m: f"import {LIB}.{rename.get(m.group(1), m.group(1))}", text)
        if new != text:
            path.write_text(new, encoding="utf-8")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--apply", action="store_true",
                    help="perform the moves (see the blocker in the docstring)")
    args = ap.parse_args()

    moves, unassigned = plan()
    by_dir: dict[str, list[str]] = {}
    for module, target in moves.items():
        by_dir.setdefault(target.split("/")[0], []).append(module)

    for directory in LAYOUT:
        members = sorted(by_dir.get(directory, []))
        what, section, _ = LAYOUT[directory]
        print(f"{LIB}/{directory}/  ({len(members)})  -- {what}  [{section}]")
    print(f"\n{len(moves)} modules assigned, {len(unassigned)} unassigned")
    for module in unassigned:
        print(f"  UNASSIGNED  {module}")

    if not args.apply:
        print("\nplan only; nothing changed.  See docs/REORGANIZATION.md for the "
              "manuscript change this waits on.")
        return 1 if unassigned else 0

    if unassigned:
        print("\nrefusing to apply with unassigned modules: every module needs a home "
              "chosen on purpose, and a leftover directory is not one.", file=sys.stderr)
        return 1
    apply(moves)
    print("\nmoved.  Now: lake build, scripts/check.py, and the manuscript's "
          "margin-note links.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
