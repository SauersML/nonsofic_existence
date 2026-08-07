#!/usr/bin/env python3
"""Emit a manifest binding a release archive to what produced it.

An archive of this repository, on its own, proves nothing about its origin:
no commit, no toolchain, no link between the committed PDF and the committed
sources.  This script prints (or writes, with --write) a JSON manifest
carrying:

  * the repository commit and whether the tree was dirty,
  * the Lean toolchain and the Mathlib commit from the manifest,
  * a SHA-256 for every Lean source, the manuscript, the generated docs,
    and the compiled PDF.

A reviewer holding the archive and the manifest can verify every file
against it; a reviewer holding only the archive can at least see which
commit to fetch and diff.  Run at release time:

    python3 scripts/release_manifest.py --write   # writes docs/RELEASE_MANIFEST.json
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent


def _git(*args: str) -> str:
    return subprocess.run(["git", *args], cwd=REPO, check=True,
                          capture_output=True, text=True).stdout.strip()


def _sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def build_manifest() -> dict:
    manifest_path = REPO / "lake-manifest.json"
    mathlib = None
    if manifest_path.is_file():
        for pkg in json.loads(manifest_path.read_text())["packages"]:
            if pkg.get("name") == "mathlib":
                mathlib = pkg.get("rev")

    files = sorted(
        p for pattern in ("NonsoficGroupsExist/**/*.lean", "NonsoficGroupsExist.lean",
                          "Superseded/**/*.lean", "Superseded.lean",
                          "scripts/*", "docs/*",
                          "nonsofic_groups_exist.tex", "nonsofic_groups_exist.pdf",
                          "lakefile.toml", "lean-toolchain", "lake-manifest.json")
        for p in REPO.glob(pattern) if p.is_file()
    )

    return {
        "commit": _git("rev-parse", "HEAD"),
        "dirty": bool(_git("status", "--porcelain")),
        "lean_toolchain": (REPO / "lean-toolchain").read_text().strip(),
        "mathlib_commit": mathlib,
        "files": {str(p.relative_to(REPO)): _sha256(p) for p in files},
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--write", action="store_true",
                    help="write docs/RELEASE_MANIFEST.json instead of stdout")
    args = ap.parse_args()

    manifest = build_manifest()
    text = json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    if args.write:
        out = REPO / "docs" / "RELEASE_MANIFEST.json"
        out.write_text(text, encoding="utf-8")
        print(f"wrote {out.relative_to(REPO)} "
              f"({len(manifest['files'])} files, commit {manifest['commit'][:12]}, "
              f"dirty={manifest['dirty']})")
    else:
        sys.stdout.write(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
