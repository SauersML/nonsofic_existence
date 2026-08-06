#!/usr/bin/env python3
"""Check that every Lean margin note in the manuscript still resolves.

The paper carries a margin note on each numbered statement naming the Lean
modules and declarations that formalize it.  Those notes are only worth
anything if they are true, and nothing about editing either side forces them
to stay true: a declaration gets renamed, a module gets split, and the paper
goes on confidently pointing at something that is no longer there.

This script closes that gap.  It extracts every `\\leanmod{Module}{decls}`
from the manuscript and fails unless each named module exists and each named
declaration is actually declared in that module.  It runs in the PDF build,
so a broken correspondence blocks the PDF rather than shipping in it.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from lean_decls import REPO_ROOT, build_index

TEX = REPO_ROOT / "nonsofic_groups_exist.tex"
LEAN_DIR = REPO_ROOT / "NonsoficGroupsExist"

# \leanmod{Module}{decl_one,decl_two}
LEANMOD_RE = re.compile(r"\\leanmod\{([^{}]*)\}\{([^{}]*)\}")

# An unescaped `%` starts a TeX comment.  The preamble documents the macros
# by example, and those examples are not references to check.
COMMENT_RE = re.compile(r"(?<!\\)%.*")


def main() -> int:
    source = COMMENT_RE.sub("", TEX.read_text(encoding="utf-8"))

    # Map each module (file stem) to the set of declaration base names it
    # introduces.  The paper names declarations without their namespace,
    # which is what a reader needs to find them in the file.
    declared: dict[str, set[str]] = {}
    for full, path in build_index().items():
        declared.setdefault(path.stem, set()).add(full.split(".")[-1])

    references = LEANMOD_RE.findall(source)
    if not references:
        print("check-lean-refs: no \\leanmod references found in the manuscript", file=sys.stderr)
        return 1

    problems: list[str] = []
    checked = 0

    for module, decl_list in references:
        module = module.strip()
        if not (LEAN_DIR / f"{module}.lean").is_file():
            problems.append(f"no such module: NonsoficGroupsExist/{module}.lean")
            continue

        available = declared.get(module, set())
        for decl in (d.strip() for d in decl_list.split(",") if d.strip()):
            checked += 1
            if decl in available:
                continue
            elsewhere = sorted(m for m, names in declared.items() if decl in names)
            hint = f"; it is declared in {', '.join(elsewhere)}" if elsewhere else ""
            problems.append(f"{module}.lean does not declare `{decl}`{hint}")

    if problems:
        print(
            f"check-lean-refs: {len(problems)} broken reference(s) in {TEX.name}:",
            file=sys.stderr,
        )
        for problem in problems:
            print(f"  {problem}", file=sys.stderr)
        return 1

    print(
        f"check-lean-refs: {checked} declarations in "
        f"{len({m for m, _ in references})} modules all resolve"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
