#!/usr/bin/env python3
"""Index every declaration in the Lean development by fully qualified name.

The index is what `check_lean_refs.py` resolves manuscript `\\lean` margin
references against.  It is a lexical scan, not a Lean elaboration: it tracks
the `namespace`/`section`/`end` stack and records the names introduced by
declaration keywords.  That is enough to catch the failure this guards
against -- a margin note in the paper naming a declaration that no longer
exists, or never did.
"""

from __future__ import annotations

import re
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
LEAN_ROOTS = (
    REPO_ROOT / "NonsoficGroupsExist",
    REPO_ROOT / "NonsoficGroupsExist.lean",
    REPO_ROOT / "scripts",
)

DECL_KEYWORDS = (
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "structure",
    "inductive",
    "class",
    "instance",
    "opaque",
    "axiom",
)

# A declaration line, after any attribute/modifier prefix.  Lean identifiers
# allow Unicode letters, digits, _, ', !, ?, and dotted components.
_MODIFIERS = r"(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|scoped\s+|local\s+)*"
_IDENT = r"[^\W\d][\w'!?]*(?:\.[^\W\d][\w'!?]*)*"

DECL_RE = re.compile(
    rf"^{_MODIFIERS}(?P<kw>{'|'.join(DECL_KEYWORDS)})\s+(?P<name>{_IDENT})",
    re.UNICODE,
)
NAMESPACE_RE = re.compile(rf"^namespace\s+(?P<name>{_IDENT})", re.UNICODE)
# `noncomputable section` opens a section like any other; missing the prefix
# made the later bare `end` pop a NAMESPACE instead, silently stripping the
# prefix from every declaration indexed after it in the file.  The elaborated
# signature gate (`scripts/Signatures.lean`) is what caught it.
SECTION_RE = re.compile(
    rf"^(?:noncomputable\s+)?section(?:\s+(?P<name>{_IDENT}))?\s*$", re.UNICODE)
END_RE = re.compile(rf"^end(?:\s+(?P<name>{_IDENT}))?\s*$", re.UNICODE)


def _strip_block_comments(text: str) -> str:
    """Blank out /- ... -/ comments, keeping line structure intact."""
    out = []
    depth = 0
    i = 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif text.startswith("-/", i) and depth:
            depth -= 1
            i += 2
        else:
            ch = text[i]
            out.append(ch if (depth == 0 or ch == "\n") else " ")
            i += 1
    return "".join(out)


def index_file(path: Path) -> dict[str, Path]:
    """Map every fully qualified declaration in `path` to that path."""
    found: dict[str, Path] = {}
    stack: list[str | None] = []  # namespace name, or None for an anonymous section

    text = _strip_block_comments(path.read_text(encoding="utf-8"))
    for raw in text.splitlines():
        line = raw.split("--", 1)[0].rstrip()
        if not line:
            continue

        # Only column-zero lines open or close scopes and declarations; indented
        # `theorem` keywords are `have`-style locals or term-mode noise.
        if line[0].isspace():
            continue

        if m := NAMESPACE_RE.match(line):
            stack.append(m.group("name"))
            continue
        if SECTION_RE.match(line):
            stack.append(None)
            continue
        if m := END_RE.match(line):
            if stack:
                stack.pop()
            continue

        if m := DECL_RE.match(line):
            prefix = ".".join(part for part in stack if part)
            name = m.group("name")
            found[f"{prefix}.{name}" if prefix else name] = path

    return found


def build_index(repo: Path | None = None) -> dict[str, Path]:
    """Index the development rooted at `repo` (the repository by default).

    The root is a parameter so that `check.py --self-test` can run the same
    detectors against a synthetic tree; a detector that only works on the real
    corpus cannot be calibrated.
    """
    base = Path(repo) if repo is not None else REPO_ROOT
    roots = (base / "NonsoficGroupsExist", base / "NonsoficGroupsExist.lean",
             base / "scripts")
    index: dict[str, Path] = {}
    for root in roots:
        if not root.exists():
            continue
        paths = sorted(root.rglob("*.lean")) if root.is_dir() else [root]
        for path in paths:
            index.update(index_file(path))
    return index


if __name__ == "__main__":
    index = build_index()
    print(f"{len(index)} declarations")
    for name in sorted(index):
        print(f"{name}\t{index[name].relative_to(REPO_ROOT)}")
