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

# Every Lean library in the repository.  `Superseded` holds superseded
# developments: off the trust surface, since the audit walks the environment of
# `NonsoficGroupsExist` only and never loads it -- but still compiled, and
# still scanned here.  Superseded is not the same as unchecked, and a `sorry`
# in code CI builds is a defect wherever it lives.
LIBS = (LIB, "Superseded")

IMPORT_RE = re.compile(r"^import\s+([A-Za-z0-9_.]+)", re.MULTILINE)

sys.path.insert(0, str(Path(__file__).resolve().parent))
import claim_map  # noqa: E402  (path set above)

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
    # Any value, not just 0: `maxHeartbeats 400000` and `maxHeartbeats 0` differ
    # only in how long the same unfixed proof is allowed to flail.  A timeout is
    # a statement about the proof -- a `whnf` that unfolds something that should
    # be irreducible, a `simp` set that should be a `rw`, a `decide` that should
    # be a lemma -- and the fix is the cheaper proof, not the larger budget.
    # `synthInstance.maxHeartbeats` and friends are caught by the same rule.
    ("maxHeartbeats budget bump",
     re.compile(r"set_option[ \t]+([A-Za-z0-9_]+\.)*maxHeartbeats(?![A-Za-z0-9_])")),
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
    "maxHeartbeats budget bump",
    "unmapped result",
    "dangling Lean reference",
    "dangling Lean reference (wrapped note)",
    "axiom-report pinning",
    "stale generated claim map",
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


def module_files(root: Path, lib: str = LIB) -> dict[str, Path]:
    """Module name -> path, for every ``.lean`` file under ``lib``."""
    out = {}
    lib_root = root / f"{lib}.lean"
    if lib_root.exists():
        out[lib] = lib_root
    if (root / lib).is_dir():
        for p in sorted((root / lib).rglob("*.lean")):
            rel = p.relative_to(root).with_suffix("")
            out[".".join(rel.parts)] = p
    return out


def all_module_files(root: Path) -> dict[str, Path]:
    """Every module of every library in the repository."""
    out: dict[str, Path] = {}
    for lib in LIBS:
        out.update(module_files(root, lib))
    return out


def import_closure(modules: dict[str, Path], start: str) -> set[str]:
    """Modules reachable from ``start`` by following imports within its library."""
    lib = start.split(".", 1)[0]
    seen: set[str] = set()
    stack = [start]
    while stack:
        m = stack.pop()
        if m in seen or m not in modules:
            continue
        seen.add(m)
        text = modules[m].read_text(encoding="utf-8", errors="replace")
        for imp in IMPORT_RE.findall(text):
            if imp == lib or imp.startswith(lib + "."):
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
    for lib in LIBS:
        modules = module_files(root, lib)
        if not modules:
            continue
        if lib not in modules:
            f.add("import closure", f"root module {lib}.lean not found")
            continue
        reachable = import_closure(modules, lib)
        for name in sorted(modules):
            if name not in reachable:
                rel = modules[name].relative_to(root)
                f.add("orphan module",
                      f"{rel}: not in the import closure of {lib}.lean, so `lake build` "
                      f"never compiles it and no audit ever sees it")


def check_forbidden(root: Path, f: Findings) -> None:
    for name, path in sorted(all_module_files(root).items()):
        text = path.read_text(encoding="utf-8", errors="replace")
        rel = path.relative_to(root)
        for label, pattern in FORBIDDEN:
            for m in pattern.finditer(text):
                line = text.count("\n", 0, m.start()) + 1
                f.add(label, f"{rel}:{line}: {text.splitlines()[line - 1].strip()}")


# The "stale conditionality disclaimer" scan used to live here.  It moved to
# `Audit.Scan` as STALE_DISCLAIMER, because the question it asks is not
# answerable in the source text: a docstring saying "conditional on the
# rose-graph `K1` input" is CORRECT when the theorem takes that input as a
# hypothesis, and this file cannot see the hypothesis.  Its only findings on
# this corpus were four such sentences, every one of them true, so its only
# green state was one where accurate documentation had been deleted.
#
# The environment sees the docstring AND the type, so the scan is decidable
# there and sharper: conditionality prose on a statement with no Prop premise.
# What no longer gets checked anywhere: module docstrings (`/-! ... -/`), which
# belong to no declaration.  One of the original four was exactly that.

def check_claim_map(root: Path, f: Findings) -> None:
    """The paper's margin notes must name declarations that exist.

    The manuscript asserts, on each numbered result, which Lean declarations
    formalize it.  Nothing about editing either side keeps that true: rename a
    theorem and the paper goes on pointing at it, in a PDF that still compiles
    and a library that still builds.  Only a scan that reads both can tell.

    Three ways it can be wrong, and all three are findings:

      * a result states something the paper never claims is formalized -- the
        note is simply missing, so the reader cannot tell whether that is a gap
        in the formalization or a gap in the bookkeeping;
      * a note names a module or declaration the library does not contain;
      * the set of cited modules outside the `#print axioms` report drifts from
        the set pinned in `claim_map`, so the paper's audit story quietly stops
        describing the audit that actually runs.
    """
    tex = root / claim_map.TEX_NAME
    if not tex.is_file():
        return

    claims = claim_map.read_claims(tex)

    for claim in claims:
        if claim.env in claim_map.RESULT_ENVS and claim.status is None:
            f.add("unmapped result",
                  f"{tex.name}:{claim.line}: `{claim.label}` ({claim.env}) carries no "
                  f"Lean note, so the paper neither claims it is formalized nor says "
                  f"it is not")

    _, problems = claim_map.resolve(claims, root)
    wrapped = {c.label for c in claims if c.status and c.wrapped}
    for problem in problems:
        # Labels contain colons, so the label is recognised by prefix rather
        # than by splitting on the first one.
        tag = ("dangling Lean reference (wrapped note)"
               if any(problem.startswith(f"{label}:") for label in wrapped)
               else "dangling Lean reference")
        f.add(tag, f"{tex.name}: {problem}")

    # Pinned only against the real corpus; the synthetic tree used by
    # --self-test has its own, empty, expectation.
    expected = (claim_map.CITED_OUTSIDE_AXIOM_REPORT
                if root == REPO else frozenset())
    closure = claim_map.audit_report_closure(root)
    # Notes may name a module by path; the closure is keyed by basename, which
    # is what identifies a module regardless of which directory it sits in.
    cited = {m.rsplit("/", 1)[-1] for c in claims for m, _ in c.blocks}
    actual = frozenset(m for m in cited if m not in closure)
    for module in sorted(actual - expected):
        f.add("axiom-report pinning",
              f"{module} is cited by the paper but is outside the import closure of "
              f"{LIB}/Audit.lean, and is not pinned in claim_map.CITED_OUTSIDE_AXIOM_REPORT")
    for module in sorted(expected - actual):
        f.add("axiom-report pinning",
              f"{module} is pinned in claim_map.CITED_OUTSIDE_AXIOM_REPORT but is no "
              f"longer both cited and outside the {LIB}/Audit.lean closure; the pin is stale")

    # The committed table is a build product.  Checking it here is what makes
    # it safe for the README to point at instead of restating: a table nobody
    # regenerates is exactly the hand-maintained table this replaced.
    generated = root / claim_map.GENERATED
    if generated.is_file():
        if generated.read_text(encoding="utf-8") != claim_map.render(root):
            f.add("stale generated claim map",
                  f"{claim_map.GENERATED} no longer matches the manuscript and the "
                  f"library; regenerate it with `python3 scripts/claim_map.py --write`")
        # The declaration list feeds `scripts/Signatures.lean`; if it drifts,
        # the signature file pins the types of yesterday's mapping.
        decls = root / claim_map.GENERATED_DECLS
        if not decls.is_file() or \
                decls.read_text(encoding="utf-8") != claim_map.render_decls(root):
            f.add("stale generated claim map",
                  f"{claim_map.GENERATED_DECLS} no longer matches the manuscript and "
                  f"the library; regenerate it with `python3 scripts/claim_map.py --write`")


CHECKS = [
    ("import closure", check_import_closure),
    ("claim map", check_claim_map),
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

# The claim-map detectors read a manuscript as well as a library, so the
# synthetic corpus carries a miniature of each: one result, one margin note,
# and an `Audit` module whose import closure the note's module lies inside.
_TEX = claim_map.TEX_NAME

CLEAN_TREE = {
    f"{LIB}.lean": f"import {LIB}.Alpha\nimport {LIB}.Beta\nimport {LIB}.Audit\n",
    f"{LIB}/Alpha.lean": "theorem alpha : True := trivial\n",
    f"{LIB}/Beta.lean":
        f"import {LIB}.Alpha\n-- an ordinary comment that claims nothing\n"
        "theorem beta : True := trivial\n",
    f"{LIB}/Audit.lean": f"import {LIB}.Alpha\n#print axioms alpha\n",
    _TEX: (
        "\\begin{lemma}\\label{lem:demo}%\n"
        "\\leanverified{\\leanmod{Alpha}{alpha}}%\n"
        "A statement.\n"
        "\\end{lemma}\n"
    ),
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
    # A raise, not `0`: the plant is the case the old `maxHeartbeats 0` regex
    # walked straight past, so it fails against the detector it replaced.
    "maxHeartbeats budget bump":
        {f"{LIB}/Alpha.lean":
         "set_option maxHeartbeats 400000 in\ntheorem a : True := trivial\n"},
    # A result the paper states and never says anything about: the reader
    # cannot distinguish "not formalized" from "nobody wrote the note".
    "unmapped result":
        {_TEX: "\\begin{theorem}\\label{thm:silent}%\nA statement.\n\\end{theorem}\n"},
    # A note that points at a declaration the library does not have -- what a
    # rename on the Lean side leaves behind.
    "dangling Lean reference":
        {_TEX: ("\\begin{lemma}\\label{lem:demo}%\n"
                "\\leanverified{\\leanmod{Alpha}{alpha_renamed_away}}%\n"
                "A statement.\n\\end{lemma}\n")},
    # A note wrapped across lines.  Before brace-balanced parsing this lost
    # every \leanmod after the newline silently, so the reference below went
    # unchecked rather than reported.
    "dangling Lean reference (wrapped note)":
        {_TEX: ("\\begin{lemma}\\label{lem:demo}%\n"
                "\\leanverified{\\leanmod{Alpha}{alpha}%\n"
                "\\leanmod{Alpha}{alpha_renamed_away}}%\n"
                "A statement.\n\\end{lemma}\n")},
    # The committed table left behind by an edit to either side.
    "stale generated claim map":
        {"docs/CLAIM_MAP.md": "# TeX map\n\nstale contents\n"},
    # A citation of a module the axiom report never reaches, unpinned.
    "axiom-report pinning":
        {_TEX: ("\\begin{lemma}\\label{lem:demo}%\n"
                "\\leanverified{\\leanmod{Beta}{beta}}%\n"
                "A statement.\n\\end{lemma}\n")},
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
    n = len(all_module_files(REPO))
    verdict = "clean" if status == 0 else "FINDINGS"
    print(f"source scan: {n} modules, {len(f.rows)} findings, {verdict}")
    return status


if __name__ == "__main__":
    sys.exit(main())
