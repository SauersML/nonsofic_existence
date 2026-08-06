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

## Status: done

The move has been made and the manuscript follows it.  What is written below
is the record of what the blocker was and how it was removed, kept because the
same shape recurs whenever the two artefacts move relative to each other.

## What the blocker was

**The manuscript pointed into the flat directory.**  Two things broke the
moment a module moved:

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

Both were the checks working: exactly the drift they exist to catch.

## How it was removed

Half of it did not need the manuscript at all.  `claim_map.module_path`
resolves a note's module by path *or* by bare name, searching the tree, so
moving a module is no longer a dangling reference on its own — the checks
follow it wherever it goes.  That is the half worth keeping: it means a future
move costs nothing here.

The hyperlink genuinely needed the `.tex`.  `\leanfileurl` appends `.lean` to
whatever a note names, so a note naming `Whitehead` links to the old flat
path.  Notes now name `Leavitt/Whitehead`, which `\leanfileurl` handles
unchanged — 117 mechanical string edits, no macro change, no mathematics
touched.  The margin displays the path, which reads no worse than the bare
name and says more.

Sequencing: the move and the note rewrite belong in **one commit**, or CI is
red in between.  `docs/CLAIM_MAP.md` is generated, so it follows on its own.

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
