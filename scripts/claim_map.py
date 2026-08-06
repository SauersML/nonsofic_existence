#!/usr/bin/env python3
"""The TeX-to-Lean claim map, derived rather than maintained.

The manuscript already states the correspondence: every numbered result
carries a margin note naming the Lean modules and declarations behind it.
This module reads that correspondence out of the source, resolves it against
the Lean declaration index, and reports what it finds.

Deriving it is the point.  The hand-written table this replaces drifted into
self-contradiction -- one row recorded `thm:kcover` as manuscript-only while
the checklist above it recorded the same theorem as formalized, and the paper
inherited the wrong half.  A table that is generated from the two artefacts it
describes cannot disagree with them.

    python3 scripts/claim_map.py            # human-readable summary
    python3 scripts/claim_map.py --markdown # the generated table
    python3 scripts/claim_map.py --json     # the map as data
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from lean_decls import build_index

REPO = Path(__file__).resolve().parent.parent
LIB = "NonsoficGroupsExist"
TEX_NAME = "nonsofic_groups_exist.tex"

# Environments that state something.  A `remark` is commentary: it carries a
# note when it has formal content of its own, and is not required to.
RESULT_ENVS = ("theorem", "proposition", "lemma", "corollary", "claim",
               "definition", "example", "mainthm")
NOTE_ENVS = RESULT_ENVS + ("remark",)

COMMENT_RE = re.compile(r"(?<!\\)%.*")
BEGIN_RE = re.compile(r"\s*\\begin\{(" + "|".join(NOTE_ENVS) + r")\}")
LABEL_RE = re.compile(r"\\label\{([^}]+)\}")
NOTE_RE = re.compile(r"\\lean(verified|partial|absent)\b")
LEANMOD_RE = re.compile(r"\\leanmod\{([^{}]*)\}\{([^{}]*)\}")
LEANNOTE_RE = re.compile(r"\\leannote\{(.*?)\}\s*(?:\}|\\leanmod|$)", re.S)

STATUS = {"verified": "formalized", "partial": "formalized in part",
          "absent": "not formalized"}

# Modules that are proved but sit outside the import closure of
# `NonsoficGroupsExist/Audit.lean`, the module whose `#print axioms` reports
# run on an ordinary build.  They are still covered by `scripts/Audit.lean`,
# which imports the library root and walks the whole namespace -- so this is a
# statement about *reporting*, not about the trust surface.
#
# This set is pinned, not budgeted: the check fails if it stops matching
# reality in either direction, so wiring one of these into the endpoint chain
# is a deliberate edit here rather than a silent change of meaning.
CITED_OUTSIDE_AXIOM_REPORT = frozenset({
    "KazhdanCover",
    "KunSpectralCounterexample",
    "RankTwoCompression",
    "ShalomFinitePresentation",
    "ThompsonV",
    "ThompsonVEmbedding",
    "ThompsonVWitness",
    "Whitehead",
})


@dataclass
class Claim:
    label: str
    env: str
    line: int
    status: str | None = None          # None when the statement carries no note
    blocks: list[tuple[str, list[str]]] = field(default_factory=list)
    note: str = ""

    @property
    def declarations(self) -> list[tuple[str, str]]:
        return [(m, d) for m, decls in self.blocks for d in decls]


def _strip_comments(text: str) -> str:
    return COMMENT_RE.sub("", text)


def _parse_note(source: str, at: int) -> tuple[str, list, str] | None:
    """Parse the margin note beginning at `at`, if there is one."""
    m = NOTE_RE.match(source, at)
    if not m:
        return None
    # Take the balanced remainder of the note command; the notes are written on
    # one logical line, so the line is a safe bound.
    end = source.find("\n", m.end())
    body = source[m.end(): end if end != -1 else len(source)]
    blocks = [(mod.strip(), [d.strip() for d in decls.split(",") if d.strip()])
              for mod, decls in LEANMOD_RE.findall(body)]
    note = ""
    if nm := LEANNOTE_RE.search(body):
        note = re.sub(r"\s+", " ", nm.group(1)).strip()
    elif m.group(1) in ("partial", "absent"):
        # The trailing brace group of \leanpartial / the sole group of
        # \leanabsent carries the explanation.
        tail = body[body.rfind("}{") + 2:] if "}{" in body else body
        note = re.sub(r"\s+", " ", tail.strip("{} \t")).strip()
    return m.group(1), blocks, note


def read_claims(tex: Path) -> list[Claim]:
    source = _strip_comments(tex.read_text(encoding="utf-8"))
    claims: list[Claim] = []
    env: str | None = None
    for line_no, line in enumerate(source.splitlines(keepends=True), 1):
        pass  # line numbers come from the split below

    offset = 0
    env = None
    for line_no, line in enumerate(source.split("\n"), 1):
        if bm := BEGIN_RE.match(line):
            env = bm.group(1)
        if env:
            if lm := LABEL_RE.search(line):
                claim = Claim(lm.group(1), env, line_no)
                # A note follows the label, on the next line.
                nxt = offset + len(line) + 1
                if parsed := _parse_note(source, nxt):
                    claim.status, claim.blocks, claim.note = parsed
                claims.append(claim)
                env = None
            elif line.lstrip().startswith("\\end{"):
                env = None
        offset += len(line) + 1
    return claims


def audit_report_closure() -> set[str]:
    """Modules reachable from `NonsoficGroupsExist/Audit.lean`."""
    d = REPO / LIB
    imports = {
        p.stem: set(re.findall(rf"^import {LIB}\.(\w+)", p.read_text(encoding="utf-8"), re.M))
        for p in d.glob("*.lean")
    }
    seen: set[str] = set()
    stack = ["Audit"]
    while stack:
        m = stack.pop()
        if m in seen or m not in imports:
            continue
        seen.add(m)
        stack.extend(imports[m])
    return seen


def resolve(claims: list[Claim]) -> tuple[dict[str, set[str]], list[str]]:
    """Return the module→declaration index and every unresolved reference."""
    declared: dict[str, set[str]] = {}
    for full, path in build_index().items():
        declared.setdefault(path.stem, set()).add(full.split(".")[-1])

    problems: list[str] = []
    for claim in claims:
        for module, decl in claim.declarations:
            if not (REPO / LIB / f"{module}.lean").is_file():
                problems.append(f"{claim.label}: no such module {LIB}/{module}.lean")
            elif decl not in declared.get(module, set()):
                elsewhere = sorted(m for m, names in declared.items() if decl in names)
                hint = f" (declared in {', '.join(elsewhere)})" if elsewhere else ""
                problems.append(f"{claim.label}: {module}.lean does not declare `{decl}`{hint}")
    return declared, problems


def to_markdown(claims: list[Claim]) -> str:
    closure = audit_report_closure()
    out = [
        "<!-- generated by scripts/claim_map.py; do not edit by hand -->",
        "",
        "| TeX label | Status | Lean modules and declarations | Note |",
        "| --- | --- | --- | --- |",
    ]
    for c in claims:
        if c.status is None:
            continue
        cells = []
        for module, decls in c.blocks:
            mark = "" if module in closure else " \u2020"
            cells.append(f"`{module}`{mark}: " + ", ".join(f"`{d}`" for d in decls))
        out.append(
            f"| `{c.label}` | {STATUS[c.status]} | {'; '.join(cells) or '—'} | {c.note or ''} |"
        )
    out += [
        "",
        "† Proved, and covered by the whole-namespace scan in `scripts/Audit.lean`, "
        "but outside the import closure of `NonsoficGroupsExist/Audit.lean`, whose "
        "`#print axioms` reports run on an ordinary build.",
    ]
    return "\n".join(out)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--markdown", action="store_true")
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    claims = read_claims(REPO / TEX_NAME)
    _, problems = resolve(claims)

    if args.markdown:
        print(to_markdown(claims))
        return 1 if problems else 0
    if args.json:
        print(json.dumps([{
            "label": c.label, "env": c.env, "line": c.line, "status": c.status,
            "lean": [{"module": m, "declarations": d} for m, d in c.blocks],
            "note": c.note,
        } for c in claims], indent=2))
        return 1 if problems else 0

    results = [c for c in claims if c.env in RESULT_ENVS]
    mapped = [c for c in claims if c.status]
    unmapped = [c for c in results if c.status is None]
    decls = sum(len(c.declarations) for c in claims)
    print(f"{len(claims)} numbered statements, {len(results)} of them results")
    print(f"{len(mapped)} carry a note, naming {decls} declarations")
    for status in ("verified", "partial", "absent"):
        n = sum(1 for c in mapped if c.status == status)
        print(f"  {STATUS[status]:20s} {n}")
    if unmapped:
        print(f"\n{len(unmapped)} results with no note:")
        for c in unmapped:
            print(f"  {c.label} ({c.env}, line {c.line})")
    for p in problems:
        print(f"\n::error:: {p}")
    return 1 if problems or unmapped else 0


if __name__ == "__main__":
    raise SystemExit(main())
