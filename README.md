# NonsoficGroupsExist

An unconditional Lean 4 proof that **a nonsofic group exists**, and that a
finitely presented one does — settling a question of Weiss, open since 2000.

The witness is explicit: `EL₄(L_{𝔽₂}(1,2))`, the rank-four elementary group
over the universal binary Leavitt algebra, defined as the quotient of the free
algebra by its five displayed relations. It is infinite, finitely generated,
has Kazhdan's property `(T)`, and is not sofic — and by an explicit rank
equivalence, so is `EL_{m+1}(L_{𝔽₂}(1,2))` for every `m ≥ 1`. `TableCover`
builds a finitely presented nonsofic cover and `KazhdanCover` a Kazhdan one.

The accompanying manuscript is `nonsofic_groups_exist.tex`. Every numbered
result in it carries a margin note naming the declarations that formalize it,
and the correspondence is machine-checked in both directions (see below).

```
lake exe cache get && lake build     # the library, with its axiom reports
lake env lean scripts/Audit.lean     # kernel audit: axioms, statements, findings
python3 scripts/check.py             # source audit: what the kernel cannot see
```

## Where to start reading

`NonsoficGroupsExist.Public` — the reading path. It proves nothing; it names
the declarations a referee needs, each against the theorem of the manuscript
it establishes, and you follow the imports downward from there.

The headline theorems, all reachable from `Endpoint/MainResults`:

| Declaration | Statement |
| --- | --- |
| `nonsofic_groups_exist` | A nonsofic group exists |
| `universalLeavittEL4_not_isSofic` | The explicit witness is not sofic |
| `ambient_full_profile` | It is countable, finitely generated, infinite, and Kazhdan too |
| `universalLeavitt_profile` | The same profile at every elementary rank `≥ 2` (Theorem A in full) |
| `exists_finitelyPresented_nonsofic_group` | A finitely presented nonsofic group exists |
| `exists_infinite_finitelyPresented_nonsofic_ambient_cover` | One of them covers the explicit group |
| `binaryLeavitt_finiteField_profile` | Theorem B's elementary ranks, over every finite field |
| `binaryLeavittUnits_profile`, `binaryLeavittGL_profile` | Theorem B(i): the unit group and every `GL_r`, closed |
| `KazhdanCover.exists_kazhdan_finitelyPresented_cover_of_not_isSofic` | Theorem C's Kazhdan refinement |

## What is proved here rather than assumed

The manuscript's proofs cite external theorems, as papers do. This library
proves **every one of them internally**, in the exact forms used, so nothing
cited remains an input to any endpoint:

- **Kun's expander decomposition** —
  `KunDecomposition.exists_expanderDecomposition`, in the one-way,
  full-sequence form used. (The four-way equivalence of Kun's Theorem 3 is
  *not* imported; its spectral implication fails as written, and the
  counterexample is formalized in `KunSpectralCounterexample`. See the
  literature audit below.)
- **The Kun–Thom centralizer obstruction** —
  `KunThomTheorem.isLEF_of_exactProductExpansion`, with its essential-expander
  wrapper `KunThomEssential.isLEF_of_matchingCertificate`.
- **Property `(T)` at rank three** —
  `FiniteFieldElementaryPropertyT.finiteFieldElementaryThree_hasKazhdanPropertyT`:
  for finite-type algebras over every finite field, in every characteristic,
  with an explicit Kazhdan pair. This is the case the manuscript states and
  consumes; `LeavittRankEquivalence.rankSuccEquiv` spreads it to every rank.
- **Shalom's finitely presented Kazhdan covers** —
  `Shalom.exists_finitelyPresented_kazhdan_cover`.
- **The non-LEF witness** — no simplicity or finite-presentation theorem for
  Thompson's `V` is used. `ThompsonFObstruction` proves the two-relator
  obstruction (two noncommuting elements satisfying the Thompson-`F` relators
  kill LEF), the witness is a two-generator subgroup of explicit cylinder
  units (`ThompsonWitness`), and its elementary membership goes through
  single-commutator certificates: every cylinder transposition is one explicit
  commutator (`cylinderSwap_is_commutator`). `V` itself is proved non-LEF
  along the way (`thompsonV_not_isLEF`).

The `K₁`-theoretic inputs are eliminated as well, by the elementary two-exit
elimination written out as Appendix A of the manuscript:

- `BinaryLeavitt.K1_trivial` — `K₁(L_k(1,2)) = 0` in Whitehead form, over
  every field, so the Ara–Brustenga–Cortiñas localization sequence is
  independent confirmation rather than a dependency.
- `BinaryLeavitt.elementaryGroup_eq_top` / `glAll_eq_elementary` —
  `GL_n(L_k(1,2)) = EL_n` at **every** rank `n ≥ 2`, by flattening transport
  from rank two, with no Gaussian elimination beyond the formalized rank-two
  case.
- `BinaryLeavitt.binaryLeavittUnits_perfect` — the unit group is perfect,
  removing the last use of Ara–Goodearl–Pardo.
- `binaryLeavittRankTwo_not_isSofic` — the manuscript's rank-two realization
  (`thm:el2`), instantiated by the two-by-two compression theorem itself:
  every one of its hypotheses is a closed theorem here.

## Trust surface

Every public result reduces to exactly the three axioms of classical Lean:
`propext`, `Classical.choice`, `Quot.sound`. There are no `sorry`s and the
library builds with `warningAsError=true`.

Three independent gates, none subsuming another:

- `NonsoficGroupsExist.Audit` prints the axiom report on an ordinary build.
- `scripts/Audit.lean` walks the transitive axiom closure of the whole
  namespace through the kernel environment, pins the headline statements by
  restating them — a weakened statement stops typechecking — and runs twelve
  finding scans (laundered propositions, unwitnessed structures, unused
  binders, stale disclaimers, and more). **All twelve report zero findings**
  over the full namespace; the named propositions it depends on carry positive
  controls (closed witnesses), so no hypothesis class is vacuously assumed.
- `scripts/check.py` scans the source text, which sees what the kernel cannot:
  comments, docstrings, and files that are never compiled at all. Every
  detector is calibrated in both directions by `--self-test`.

An axiom audit says nothing about whether the statement proved is the one
intended. Two definitional questions carry most of that weight, and both are
discharged as theorems rather than left as caveats:
`hasKazhdanPropertyT_iff_textbook` shows the real-orthogonal, own-universe
property `(T)` used throughout is the textbook complex-unitary property over
every universe; `isLEF_iff_textbook` does the same for local embeddability.

## How to verify

The repository pins Lean `v4.32.2` and Mathlib commit
`905b95818eb32af7874a58b427f50c1711a5e96c` in `lean-toolchain` and
`lake-manifest.json`. Do not update the manifest during verification.

```bash
lake exe cache get
python3 scripts/check.py --self-test
python3 scripts/check.py
lake build
lake build Audit
lake env lean scripts/Calibrate.lean
lake env lean scripts/Audit.lean
```

The source scan must report every planted calibration defect, all project
modules in the root import closure, and no real-source finding. The build must
finish with zero warnings and errors. Each public and load-bearing declaration
printed by `NonsoficGroupsExist.Audit` must report exactly `propext`,
`Classical.choice`, and `Quot.sound`; `scripts/Audit.lean` additionally
rejects any other axiom in the transitive closure of the entire namespace and
fails on any finding in any scan.

CI also runs the pinned Lean toolchain's built-in `leanchecker --fresh` on
`NonsoficGroupsExist.olean`; success is exit status zero after every imported
olean has been replayed into a fresh kernel environment. A cold dependency
download requires several gigabytes, and a cold project build can take hours;
cached builds are substantially faster.

The `official/` directory contains OpenAI's proof documents. They are not
imported by Lean and are distinct from the main `nonsofic_groups_exist.tex`
manuscript. The validated built PDF is intentionally committed to `main` by
the PDF workflow.

## Claim map and margin notes

Every numbered result of `nonsofic_groups_exist.tex` is listed with its Lean
counterpart in **[docs/CLAIM_MAP.md](docs/CLAIM_MAP.md)** — status, modules,
declarations, and any way the Lean statement differs in generality from the
printed one. That file is generated from the manuscript's own margin notes
resolved against the Lean source, and `scripts/check.py` fails if it goes
stale, so the two cannot disagree without CI saying so.

```
python3 scripts/claim_map.py           # summary: statuses and coverage
python3 scripts/claim_map.py --write   # regenerate docs/CLAIM_MAP.md
python3 scripts/check_lean_refs.py     # every \leanmod margin note resolves
```

The margin notes are strictly marginal: no argument in the paper appeals to
one, and setting `\leanlinksfalse` in the preamble removes all of them and
leaves the text untouched. The PDF workflow runs the reference check before
compiling, so a stale note blocks the build instead of shipping inside the
PDF.

## Library layout

The library follows the paper's structure; each directory is a section.

| Directory | Paper | Contents |
| --- | --- | --- |
| `Sofic/` | §2 | Sofic approximations, LEF, generator graphs, the two-relator obstruction |
| `Kazhdan/` | §2 | Real-orthogonal property `(T)`, complexification, universe transfer, GNS |
| `Kun/` | §2.5 | The one-way expander decomposition, proved (with the Lemma 10 repair) |
| `KunThom/` | §2.5 | The centralizer obstruction, proved (with the relation-to-permutation repair) |
| `Matching/` | §3 | The five finite lemmas: refinement, conservation, pinning, selection, completion |
| `Criterion/` | §4 | Median normalization, matching, localization; the compression–centralizer theorem |
| `Leavitt/` | §5–§6 | Leaf calculus, self-similarity, rank equivalence, compressors, the corner witness |
| `PropertyT/` | §5 | Property `(T)` at rank three over every finite field, from an explicit `A₂` gap |
| `KOne/` | Appendix A | The elementary `K₁` elimination: windows, pencils, the two-exit loop, all-ranks `GL = EL` |
| `Covers/` | §9 | The finite-table and Kazhdan finitely presented covers |
| `Endpoint/` | §1 | `MainResults`, `Public`, and the in-build `Audit` |

The separate `Superseded` library holds developments that later proofs
replaced (earlier `K₁` routes, the master-induction scaffolding). It is a
default build target so it cannot rot, but the library root does not import
it: nothing in it is on the trust surface.

## Literature audit: Kun's spectral characterization

Version 5 of Kun's *On sofic approximations of Property (T) groups*
([arXiv:1606.04471](https://arxiv.org/abs/1606.04471)) states Theorem 3 as an
equivalence. Its final implication, `(4) → (1)`, is not valid as written: the
proof invokes the Cheeger/Dodziuk–Alon–Milman bound, which separates the
nonconstant Markov spectrum from `+1` but not from `-1`, and uniform expanders
can be arbitrarily close to bipartite. Concretely, a degree-preserving
two-edge switch in each graph of a bipartite expander family, repeated, gives
a sequence satisfying conditions `(2)`–`(4)` but not `(1)`; the counterexample
is formalized in `KunSpectralCounterexample`. The equivalence is therefore not
imported here.

This defect does not refute Kun's Theorem 1: Proposition 11 of the same paper
establishes condition `(2)`, and Theorem 1 needs only the forward
implications. This repository's Kun dependency is exactly that one-way
expander-decomposition result, proved from the forward property-`(T)`
partition-and-repair argument, with a full-sequence diagonal accuracy choice
so the conclusion applies to the given approximation rather than a
subsequence.

Two further proof-level gaps were found and repaired in the course of
formalization. Kun's Lemma 10 normalizes a Markov defect without excluding
the case in which it vanishes; the Lean proof splits off the zero-vector case
before dividing (`Kazhdan.lean`). The published Kun–Thom argument constructs
a relation between finite models and later treats it as the graph of a
permutation; the Lean proof extracts the injective matching core of the
relation and completes it to the genuine permutation `repairRelation`. These
are repairs of gaps in proofs of true results; they do not make the spectral
equivalence true.

## Development history

The checklist archaeology — what was proved when, in what order, and the
intermediate results named along the way — lives in
[docs/HISTORY.md](docs/HISTORY.md), alongside `BUILD_ITERATION_NOTES.md`.
