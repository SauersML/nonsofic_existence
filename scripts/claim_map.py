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
    "CharacterCount",
    "ElementaryNoFiniteQuotients",
    "HeisenbergCentre",
    "HyperlinearReduction",
    "NoRounding",
    "PhaseCorrection",
    "RationalCharacter",
    "ScalarClass",
    "UntwistSeparation",
    "ExactCompression",
    "FiniteQuotientBlindness",
    "Hyperlinear",
    "HyperlinearAmplification",
    "ImplementerCocycle",
    "HyperlinearMetric",
    "HyperlinearNonScalar",
    "HyperlinearScalar",
    "HyperlinearUltraproduct",
    "FreeLampReduction",
    "MonomialModel",
    "NormTraceGap",
    "PhaseOrder",
    "PhasePropagation",
    "ScalarCocycle",
    "CommutantRigidity",
    "CoordinateTransfer",
    "DivisibleInvisible",
    "KunSpectralCounterexample",
    "SoficAmplification",
    "SoficUltraproduct",
    "StructuralProfile",
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
    wrapped: bool = False              # the note spans more than one line

    @property
    def declarations(self) -> list[tuple[str, str]]:
        return [(m, d) for m, decls in self.blocks for d in decls]


def _strip_comments(text: str) -> str:
    return COMMENT_RE.sub("", text)


def _balanced(source: str, at: int) -> tuple[str, int]:
    """The brace group starting at `at`, and the index just past it."""
    if at >= len(source) or source[at] != "{":
        return "", at
    depth = 0
    for i in range(at, len(source)):
        if source[i] == "{":
            depth += 1
        elif source[i] == "}":
            depth -= 1
            if depth == 0:
                return source[at + 1:i], i + 1
    return source[at + 1:], len(source)


def _parse_note(source: str, at: int) -> tuple[str, list, str] | None:
    """Parse the margin note beginning at `at`, if there is one."""
    m = NOTE_RE.match(source, at)
    if not m:
        return None
    # Read the note's brace groups by matching braces, not by stopping at the
    # end of the line.  Bounding this by the line silently dropped every
    # \leanmod after the first newline -- no error, just declarations quietly
    # missing from a table whose whole job is to notice things going missing.
    body, nxt = _balanced(source, m.end())
    trailing, _ = _balanced(source, nxt)
    blocks = [(mod.strip(), [d.strip() for d in decls.split(",") if d.strip()])
              for mod, decls in LEANMOD_RE.findall(body)]
    note = ""
    # The note's argument is a balanced brace group -- notes contain nested
    # TeX like `\abs{D_{n,i(n)}}`, which a lazy regex truncated mid-formula.
    if (pos := body.find("\\leannote")) != -1:
        raw, _ = _balanced(body, pos + len("\\leannote"))
        note = re.sub(r"\s+", " ", raw).strip()
    elif m.group(1) == "absent":
        note = re.sub(r"\s+", " ", body).strip()
    elif m.group(1) == "partial":
        # \leanpartial takes the module blocks, then the explanation.
        note = re.sub(r"\s+", " ", trailing).strip()
    return m.group(1), blocks, note, "\n" in body


def read_claims(tex: Path) -> list[Claim]:
    source = _strip_comments(tex.read_text(encoding="utf-8"))
    claims: list[Claim] = []
    offset = 0
    env: str | None = None
    for line_no, line in enumerate(source.split("\n"), 1):
        if bm := BEGIN_RE.match(line):
            env = bm.group(1)
        if env:
            if lm := LABEL_RE.search(line):
                claim = Claim(lm.group(1), env, line_no)
                # A note follows the label, on the next line.
                nxt = offset + len(line) + 1
                if parsed := _parse_note(source, nxt):
                    claim.status, claim.blocks, claim.note, claim.wrapped = parsed
                claims.append(claim)
                env = None
            elif line.lstrip().startswith("\\end{"):
                env = None
        offset += len(line) + 1
    return claims


def audit_report_closure(repo: Path | None = None) -> set[str]:
    """Modules reachable from `NonsoficGroupsExist/Audit.lean`."""
    d = (Path(repo) if repo is not None else REPO) / LIB
    if not d.is_dir():
        return set()
    imports = {
        p.stem: set(re.findall(rf"^import {LIB}\.([\w.]+)",
                               p.read_text(encoding="utf-8"), re.M))
        for p in d.rglob("*.lean")
    }
    seen: set[str] = set()
    stack = ["Audit"]
    while stack:
        m = stack.pop()
        if m in seen or m not in imports:
            continue
        seen.add(m)
        # Imports name modules by dotted path; the index is keyed by basename,
        # which is what the manuscript's notes and this closure both use.
        stack.extend(i.rsplit(".", 1)[-1] for i in imports[m])
    return seen


def module_path(module: str, repo: Path | None = None) -> Path | None:
    """The file a margin note's module name refers to, wherever it now lives."""
    base = Path(repo) if repo is not None else REPO
    direct = base / LIB / f"{module}.lean"
    if direct.is_file():
        return direct
    matches = sorted((base / LIB).rglob(f"{module.rsplit('/', 1)[-1]}.lean"))
    return matches[0] if len(matches) == 1 else None


def _matches(full: str, decl: str) -> bool:
    """A cited name matches a declaration when it is a full dotted suffix.

    Suffix matching, on component boundaries, is what lets a note cite either
    `K1_trivial` or `BinaryLeavitt.K1_trivial`; the qualified form is how a
    note disambiguates when one file declares the same short name in two
    namespaces.
    """
    return full == decl or full.endswith("." + decl)


def resolve(claims: list[Claim], repo: Path | None = None
            ) -> tuple[dict[str, set[str]], list[str]]:
    """Return the module→declaration index and every unresolved reference.

    The index maps a module basename to the *fully qualified* names it
    declares.  A reference resolves when exactly one declaration in the named
    module matches it as a dotted suffix; zero matches is a dangling
    reference, and two or more is an ambiguity the note must settle by
    qualifying the name -- a check that certifies an ambiguous name proves
    the wrong thing exists.
    """
    base = Path(repo) if repo is not None else REPO
    # Keyed by the file itself, not by its basename: two files with the same
    # stem in different directories must not pool their declarations, or a
    # note could resolve against the wrong one and never know.
    by_file: dict[Path, set[str]] = {}
    for full, path in build_index(base).items():
        by_file.setdefault(path, set()).add(full)

    problems: list[str] = []
    for claim in claims:
        for module, decl in claim.declarations:
            # A note may name a module either by bare name or by path within the
            # library.  Resolving both means moving a module into a
            # subdirectory is not, by itself, a broken reference: the paper
            # names `Whitehead`, and `Leavitt/Whitehead.lean` answers to it.
            path = module_path(module, base)
            if path is None:
                problems.append(f"{claim.label}: no such module {LIB}/{module}.lean")
                continue
            fulls = by_file.get(path, set())
            matches = sorted(f for f in fulls if _matches(f, decl))
            if not matches:
                elsewhere = sorted(p.stem for p, names in by_file.items()
                                   if any(_matches(f, decl) for f in names))
                hint = f" (declared in {', '.join(elsewhere)})" if elsewhere else ""
                problems.append(f"{claim.label}: {module}.lean does not declare `{decl}`{hint}")
            elif len(matches) > 1:
                problems.append(
                    f"{claim.label}: `{decl}` is ambiguous in {module}.lean "
                    f"({', '.join(matches)}); qualify the note's name with a namespace suffix")
    return by_file, problems


def resolved_declarations(claims: list[Claim], repo: Path | None = None) -> list[str]:
    """Every mapped declaration, fully qualified, sorted and deduplicated.

    This is the input to `scripts/Signatures.lean`, which elaborates each name
    and prints its type -- the layer that pins *statements*, where this module
    pins only *names*.
    """
    base = Path(repo) if repo is not None else REPO
    by_file, _ = resolve(claims, base)
    out: set[str] = set()
    for claim in claims:
        for module, decl in claim.declarations:
            path = module_path(module, base)
            if path is None:
                continue
            for full in by_file.get(path, set()):
                if _matches(full, decl):
                    out.add(full)
    return sorted(out)


def to_markdown(claims: list[Claim], repo: Path | None = None) -> str:
    closure = audit_report_closure(repo)
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
            mark = "" if module.rsplit("/", 1)[-1] in closure else " \u2020"
            cells.append(f"`{module}`{mark}: " + ", ".join(f"`{d}`" for d in decls))
        note = (c.note or "").replace("|", "\\|")
        out.append(
            f"| `{c.label}` | {STATUS[c.status]} | {'; '.join(cells) or '—'} | {note} |"
        )
    out += [
        "",
        "† Proved, and covered by the whole-namespace scan in `scripts/Audit.lean`, "
        "but outside the import closure of `NonsoficGroupsExist/Audit.lean`, whose "
        "`#print axioms` reports run on an ordinary build.",
    ]
    return "\n".join(out)


GENERATED = Path("docs/CLAIM_MAP.md")
GENERATED_DECLS = Path("docs/CLAIM_DECLS.txt")

HEADER = """# TeX \u2194 Lean claim map

Generated by `scripts/claim_map.py` from the manuscript's margin notes and the
Lean declaration index.  Do not edit it by hand: `scripts/check.py` fails if
this file stops matching what the two sources actually say.

The manuscript is the source of truth for the correspondence -- each numbered
result carries a margin note naming the modules and declarations behind it, and
this table is that assertion, collected and resolved.

These checks are syntactic: they establish that the named declarations exist,
resolve, and keep their signatures, not that a declaration is the intended
mathematical translation of its printed statement.  The semantic layer is the
endpoint bundles of `Endpoint/ManuscriptStatements.lean`
(`theoremA_exact`, `theoremB_exact`, `theoremC_exact`, `theoremD_subgroups`),
each of whose *type* is one printed statement, checkable by `#check` against
the print.

"""


def render(repo: Path | None = None) -> str:
    """The full generated file, header included."""
    base = Path(repo) if repo is not None else REPO
    claims = read_claims(base / TEX_NAME)
    return HEADER + to_markdown(claims, base) + "\n"


def render_decls(repo: Path | None = None) -> str:
    """The mapped declarations, fully qualified, one per line.

    `scripts/Signatures.lean` reads this file after a build and writes each
    declaration's elaborated type to `docs/CLAIM_SIGNATURES.md`; a name that
    stops existing fails there with the kernel's authority rather than this
    scan's.
    """
    base = Path(repo) if repo is not None else REPO
    claims = read_claims(base / TEX_NAME)
    return "\n".join(resolved_declarations(claims, base)) + "\n"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--write", action="store_true",
                    help=f"regenerate {GENERATED}")
    ap.add_argument("--markdown", action="store_true")
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    claims = read_claims(REPO / TEX_NAME)
    _, problems = resolve(claims)

    if args.write:
        (REPO / GENERATED).parent.mkdir(parents=True, exist_ok=True)
        (REPO / GENERATED).write_text(render(), encoding="utf-8")
        (REPO / GENERATED_DECLS).write_text(render_decls(), encoding="utf-8")
        print(f"wrote {GENERATED} and {GENERATED_DECLS}")
        return 1 if problems else 0
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
