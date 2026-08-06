# Phase 2: directory structure mirroring the manuscript

`NonsoficGroupsExist/` is 256 modules in one flat directory, ordered by the
sequence the mathematics was discovered in.  `scripts/reorganize.py` moves
them into eleven directories that track the paper's sections, rewriting every
import as it goes:

```
python3 scripts/reorganize.py          # print the plan; changes nothing
python3 scripts/reorganize.py --apply  # git mv + rewrite imports
```

The assignment is by hand, in `LAYOUT`, because the import graph does not
determine it: `FiniteGraph` is used by the Kun layer and the matching toolkit
alike, and only the manuscript says which section it belongs to.  The script
refuses to run with any module unassigned — a leftover `Misc/` is not a home
chosen on purpose.

## Why it has not been run

**The manuscript points into the flat directory, and cannot be edited from
here.**  Two things break the moment a module moves:

1. **Every margin-note hyperlink 404s.**  `\leanfileurl` in the preamble is

   ```latex
   \newcommand{\leanfileurl}[1]{%
     https://github.com/SauersML/nonsofic_existence/blob/main/NonsoficGroupsExist/#1.lean}
   ```

   It appends `.lean` to a bare module name.  After the move the file is at
   `NonsoficGroupsExist/Leavitt/Whitehead.lean`, and the paper links to
   `NonsoficGroupsExist/Whitehead.lean`, which no longer exists.  189
   declaration references across 82 modules are affected.

2. **`scripts/check.py` reports every one as a dangling reference**, because
   `\leanmod{Whitehead}{...}` no longer names a module.  That gate also runs
   in the PDF build, so the manuscript stops building.

Both are the checks working: this is exactly the drift they exist to catch.
But neither can be repaired from the Lean side.

## What the manuscript needs

The smallest change is to let a margin note carry a path.  `\leanmod`'s first
argument becomes `Leavitt/Whitehead` instead of `Whitehead`, `\leanfileurl`
keeps working unchanged, and the note displays the last component so the
margin still reads as a module name.  `claim_map.py` then resolves the path
directly and `check.py` follows without modification.

Sequencing matters: **regenerate the margin notes and the manuscript in the
same commit as the move**, or CI is red in between.  `docs/CLAIM_MAP.md` is
generated, so it follows automatically.

## The eleven directories

| Directory | Backs | Modules |
| --- | --- | --- |
| `Sofic/` | `sec:prelim` | 10 |
| `Kazhdan/` | `subsec:sofic` | 22 |
| `PropertyT/` | `thm:ejz` | 33 |
| `Kun/` | `thm:kun` | 32 |
| `KunThom/` | `thm:kunthom` | 7 |
| `Matching/` | `sec:toolkit` | 39 |
| `Criterion/` | `sec:criterion` | 7 |
| `Leavitt/` | `sec:leavitt` | 42 |
| `KOne/` | `app:K1` | 59 |
| `Covers/` | `sec:fp` | 2 |
| `Endpoint/` | `sec:intro` | 3 |
