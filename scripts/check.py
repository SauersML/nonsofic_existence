#!/usr/bin/env python3
"""Source-text half of the validation, borrowed in shape from gnomon's
``proofs/validation/code/check.py``.

The source text and the elaborated environment are different objects and each
sees what the other cannot, which is why this file and ``scripts/Audit.lean``
both exist and neither subsumes the other:

  * this scan names the line a person typed, sees comments and docstrings, and
    -- decisively -- sees files that are never compiled at all;
  * the Lean scan sees the premises the kernel actually inserted and the
    transitive axiom closure, none of which exists in the source text.

Every check here is calibrated in BOTH directions by ``--self-test``: each
planted defect must be reported, and a clean tree must be silent.  A detector
that reports nothing is otherwise indistinguishable from a clean corpus, which
is the failure mode this whole directory exists to avoid.

    python3 scripts/check.py             # gate; nonzero exit on any finding
    python3 scripts/check.py --self-test # calibration; run first in CI
"""

from __future__ import annotations

import argparse
import re
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
LIB = "NonsoficGroupsExist"

IMPORT_RE = re.compile(r"^import\s+([A-Za-z0-9_.]+)", re.MULTILINE)

# Each entry is (label, compiled regex).  Matches are reported with file:line.
#
# `sorry` is scanned here AND caught by the kernel audit as `sorryAx`.  That is
# deliberate duplication: a `sorry` in a module outside the import closure is
# invisible to the kernel scan, and a `sorry` reached through a macro is
# invisible to this one.
FORBIDDEN = [
    ("sorry / sorryAx", re.compile(r"(?<![A-Za-z0-9_])sorry(?![A-Za-z0-9_])|sorryAx")),
    ("hand-declared axiom", re.compile(r"^[ \t]*axiom[ \t]")),
    ("native_decide (trusts the compiler, not the kernel)",
     re.compile(r"(?<![A-Za-z0-9_])native_decide(?![A-Za-z0-9_])")),
    ("unsafe / implemented_by / opaque escape hatch",
     re.compile(r"^[ \t]*unsafe[ \t]|@\[implemented_by|^[ \t]*opaque[ \t]")),
    ("warningAsError disabled", re.compile(r"warningAsError[ \t]*(:=)?[ \t]*false")),
    ("maxHeartbeats disabled", re.compile(r"set_option[ \t]+maxHeartbeats[ \t]+0")),
]


# There are no budgets: any finding, under any tag, fails the run.  Nothing is
# report-only and nothing is a ratchet, so there is no number a reviewer can
# raise instead of fixing the source, and a scan cannot be quietened by editing
# this file.  The roster below is for reporting only -- a passing run prints a
# count for every detector, since a scan that has silently stopped firing is
# otherwise indistinguishable from a clean tree -- and a finding under a tag
# missing from it fails just the same.
SCAN_TAGS: tuple[str, ...] = (
    "orphan module",
    "sorry / sorryAx",
    "hand-declared axiom",
    "native_decide (trusts the compiler, not the kernel)",
    "unsafe / implemented_by / opaque escape hatch",
    "warningAsError disabled",
    "maxHeartbeats disabled",
    "stale conditionality disclaimer",
)


class Findings:
    def __init__(self) -> None:
        self.rows: list[tuple[str, str]] = []

    def add(self, tag: str, detail: str) -> None:
        self.rows.append((tag, detail))

    def report(self, stream=sys.stdout) -> int:
        counts: dict[str, int] = {}
        for tag, _ in self.rows:
            counts[tag] = counts.get(tag, 0) + 1
        for tag, detail in self.rows:
            print(f"::error::[{tag}] {detail}", file=stream)
        for tag in SCAN_TAGS:
            print(f"{tag}: {counts.get(tag, 0)}", file=stream)
        for tag, count in sorted(counts.items()):
            if tag not in SCAN_TAGS:
                print(f"{tag}: {count} (tag not on the roster)", file=stream)
        return 1 if self.rows else 0


def module_files(root: Path) -> dict[str, Path]:
    """Module name -> path, for every ``.lean`` file under the library."""
    out = {}
    lib_root = root / f"{LIB}.lean"
    if lib_root.exists():
        out[LIB] = lib_root
    for p in sorted((root / LIB).rglob("*.lean")):
        rel = p.relative_to(root).with_suffix("")
        out[".".join(rel.parts)] = p
    return out


def import_closure(modules: dict[str, Path], start: str) -> set[str]:
    """Modules reachable from ``start`` by following in-library imports."""
    seen: set[str] = set()
    stack = [start]
    while stack:
        m = stack.pop()
        if m in seen or m not in modules:
            continue
        seen.add(m)
        text = modules[m].read_text(encoding="utf-8", errors="replace")
        for imp in IMPORT_RE.findall(text):
            if imp == LIB or imp.startswith(LIB + "."):
                stack.append(imp)
    return seen


def check_import_closure(root: Path, f: Findings) -> None:
    """Every library module must be reachable from the root module.

    This is not a tidiness check.  ``lake build`` builds the root module's
    import closure, so a module nothing imports is NEVER COMPILED: it can be
    broken, contain a `sorry`, or contradict the rest of the development, and
    both a green build and the kernel audit will agree that everything is fine,
    because neither ever loaded it.  An orphan is therefore either a missing
    import or dead code to delete, and the repository cannot tell you which.
    """
    modules = module_files(root)
    if LIB not in modules:
        f.add("import closure", f"root module {LIB}.lean not found")
        return
    reachable = import_closure(modules, LIB)
    for name in sorted(modules):
        if name not in reachable:
            rel = modules[name].relative_to(root)
            f.add("orphan module",
                  f"{rel}: not in the import closure of {LIB}.lean, so `lake build` "
                  f"never compiles it and no audit ever sees it")


def check_forbidden(root: Path, f: Findings) -> None:
    for name, path in sorted(module_files(root).items()):
        text = path.read_text(encoding="utf-8", errors="replace")
        rel = path.relative_to(root)
        for label, pattern in FORBIDDEN:
            for m in pattern.finditer(text):
                line = text.count("\n", 0, m.start()) + 1
                f.add(label, f"{rel}:{line}: {text.splitlines()[line - 1].strip()}")


# Prose that describes the development as incomplete.  Tracked because the two
# halves of this repository can disagree: `MainResults` proves an unconditional
# existence theorem while individual module docstrings still describe their
# contents as assumptions of conditional lemmas.  One of the two is stale, and
# a reader who finds the disclaimer first reasonably concludes the headline
# claim is overstated.
#
# Fatal like every other tag.  Which of the two is wrong is a question about
# mathematics that no regex can answer, so the resolution is a person's: either
# the disclaimer is stale and goes, or the headline is overstated and the
# disclaimer is right.  What a red gate must NOT buy is the third option --
# deleting an accurate disclaimer to silence the scan.
DISCLAIMER_RE = re.compile(
    r"\b(conditional|conditionally|candidate|proposed|not proved|unproved|"
    r"not yet proved|assumed rather than|remains an assumption)\b",
    re.IGNORECASE,
)

DOC_LINE_RE = re.compile(r"^\s*(--|/-|-/|\*|/-!)|^\s*$")


def check_stale_disclaimers(root: Path, f: Findings) -> None:
    for name, path in sorted(module_files(root).items()):
        text = path.read_text(encoding="utf-8", errors="replace")
        rel = path.relative_to(root)
        in_block = False
        for i, line in enumerate(text.splitlines(), start=1):
            stripped = line.strip()
            if stripped.startswith("/-"):
                in_block = True
            is_comment = in_block or stripped.startswith("--")
            if stripped.endswith("-/"):
                in_block = False
            if not is_comment:
                continue
            m = DISCLAIMER_RE.search(line)
            if m:
                f.add("stale conditionality disclaimer",
                      f"{rel}:{i}: {stripped[:110]}")


CHECKS = [
    ("import closure", check_import_closure),
    ("forbidden constructs", check_forbidden),
    ("stale conditionality disclaimers", check_stale_disclaimers),
]


def run(root: Path) -> Findings:
    f = Findings()
    for _, fn in CHECKS:
        fn(root, f)
    return f


# --------------------------------------------------------------------------
# Calibration.  Both directions, because a silent detector and a clean corpus
# look identical from the outside.
# --------------------------------------------------------------------------

CLEAN_TREE = {
    f"{LIB}.lean": f"import {LIB}.Alpha\nimport {LIB}.Beta\n",
    f"{LIB}/Alpha.lean": "theorem alpha : True := trivial\n",
    f"{LIB}/Beta.lean":
        f"import {LIB}.Alpha\n-- an ordinary comment that claims nothing\n"
        "theorem beta : True := trivial\n",
}

PLANTS = {
    "orphan module": {f"{LIB}/Orphan.lean": "theorem orphan : False := by sorry\n"},
    "sorry / sorryAx": {f"{LIB}/Alpha.lean": "theorem alpha : True := by sorry\n"},
    "hand-declared axiom": {f"{LIB}/Alpha.lean": "axiom alpha : True\n"},
    "native_decide (trusts the compiler, not the kernel)":
        {f"{LIB}/Alpha.lean": "theorem alpha : True := by native_decide\n"},
    "unsafe / implemented_by / opaque escape hatch":
        {f"{LIB}/Alpha.lean": "opaque alpha : Nat\n"},
    "warningAsError disabled":
        {f"{LIB}/Alpha.lean": "set_option warningAsError false\n"},
    "maxHeartbeats disabled":
        {f"{LIB}/Alpha.lean": "set_option maxHeartbeats 0 in\ntheorem a : True := trivial\n"},
    "stale conditionality disclaimer":
        {f"{LIB}/Alpha.lean":
             "/-- This is a conditional result. -/\ntheorem alpha : True := trivial\n"},
}


def _materialize(base: Path, tree: dict[str, str]) -> None:
    for rel, text in tree.items():
        p = base / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text, encoding="utf-8")


def self_test() -> int:
    failures = []

    # Direction 1: a clean tree is silent.  Without this, a detector that
    # crashes or matches nothing would "pass" every plant below by accident.
    with tempfile.TemporaryDirectory() as d:
        base = Path(d)
        _materialize(base, CLEAN_TREE)
        rows = run(base).rows
        if rows:
            failures.append(f"clean tree reported {len(rows)} findings: {rows}")

    # Direction 2: every planted defect is reported, under its own tag.  The
    # tag matters: a gate that fires under the wrong label can alarm but cannot
    # localize.
    for tag, plant in PLANTS.items():
        with tempfile.TemporaryDirectory() as d:
            base = Path(d)
            _materialize(base, CLEAN_TREE)
            _materialize(base, plant)
            tags = {t for t, _ in run(base).rows}
            if tag not in tags:
                failures.append(f"plant {tag!r} was NOT reported (got {sorted(tags)})")

    for line in failures:
        print(f"::error::[calibration] {line}")
    if failures:
        return 1
    print(f"calibration: clean tree silent; {len(PLANTS)} planted defects all reported")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--self-test", action="store_true",
                    help="calibrate the detectors in both directions and exit")
    args = ap.parse_args()
    if args.self_test:
        return self_test()
    f = run(REPO)
    status = f.report()
    n = len(module_files(REPO))
    verdict = "clean" if status == 0 else "FINDINGS"
    print(f"source scan: {n} modules, {len(f.rows)} findings, {verdict}")
    return status


if __name__ == "__main__":
    sys.exit(main())
