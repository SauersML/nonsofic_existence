#!/usr/bin/env python3
"""Fail if any Lean margin reference in the manuscript no longer resolves.

This is the gate the PDF build runs, so a broken correspondence blocks the
PDF rather than shipping inside it.  The reference check itself lives in
`claim_map`, which `scripts/check.py` also uses -- one implementation, two
callers, so the PDF gate and the source gate cannot disagree about what a
valid reference is.

`scripts/check.py` is the fuller scan: it additionally reports results the
paper never maps, drift in the audit-report pinning, and a stale generated
claim map.  This entry point stays narrow on purpose, because it runs on a
machine that has TeX installed but has not built the Lean library.
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import claim_map


def main() -> int:
    tex = claim_map.REPO / claim_map.TEX_NAME
    claims = claim_map.read_claims(tex)
    references = [d for c in claims for d in c.declarations]

    if not references:
        print(f"check-lean-refs: no margin references found in {tex.name}", file=sys.stderr)
        return 1

    _, problems = claim_map.resolve(claims)
    if problems:
        print(f"check-lean-refs: {len(problems)} broken reference(s) in {tex.name}:",
              file=sys.stderr)
        for problem in problems:
            print(f"  {problem}", file=sys.stderr)
        return 1

    modules = {m for c in claims for m, _ in c.blocks}
    print(f"check-lean-refs: {len(references)} declarations in {len(modules)} modules "
          f"all resolve")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
