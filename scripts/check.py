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
import shutil
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


class Findings:
    def __init__(self) -> None:
        self.rows: list[tuple[str, str]] = []

    def add(self, tag: str, detail: str) -> None:
        self.rows.append((tag, detail))

    def report(self, stream=sys.stdout) -> int:
        for tag, detail in self.rows:
            print(f"::error::[{tag}] {detail}", file=stream)
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


CHECKS = [
    ("import closure", check_import_closure),
    ("forbidden constructs", check_forbidden),
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
    f"{LIB}/Beta.lean": f"import {LIB}.Alpha\ntheorem beta : True := trivial\n",
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
    if status == 0:
        n = len(module_files(REPO))
        print(f"source scan: {n} modules, all in the root import closure, no findings")
    return status


if __name__ == "__main__":
    sys.exit(main())
