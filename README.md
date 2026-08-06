# NonsoficGroupsExist

An unconditional Lean 4 proof that **a nonsofic group exists**, and that a
finitely presented one does — settling a question of Weiss, open since 2000.

The witness is explicit: `EL₄(L_{𝔽₂}(1,2))`, the rank-four elementary group
over the universal binary Leavitt algebra, defined as the quotient of the free
algebra by its five displayed relations. It is infinite, finitely generated,
has Kazhdan's property `(T)`, and is not sofic. `TableCover` then builds its
finitely presented cover and `KazhdanCover` the Kazhdan one.

The accompanying manuscript is `nonsofic_groups_exist.tex`; every numbered
result in it carries a margin note naming the declarations below that
formalize it.

```
lake exe cache get && lake build     # the library, with its axiom reports
lake env lean scripts/Audit.lean     # kernel audit: axioms and statements
python3 scripts/check.py             # source audit: what the kernel cannot see
```

## Where to start reading

`NonsoficGroupsExist.Public` — the reading path. It proves nothing; it names
the ~20 declarations a referee needs, each against the theorem of the
manuscript it establishes, and you follow the imports downward from there.

The headline theorems, all in `MainResults`:

| Declaration | Statement |
| --- | --- |
| `nonsofic_groups_exist` | A nonsofic group exists |
| `universalLeavittEL4_not_isSofic` | The explicit witness is not sofic |
| `ambient_full_profile` | It is countable, finitely generated, infinite, and Kazhdan too |
| `exists_finitelyPresented_nonsofic_group` | A finitely presented nonsofic group exists |
| `exists_infinite_finitelyPresented_nonsofic_ambient_cover` | One of them covers the explicit group |

## What is proved here rather than assumed

The manuscript cites four external theorems. Three are proved in this library,
so they are inputs to the paper and not to the development:

- **Kun's expander decomposition** — `KunDecomposition.exists_expanderDecomposition`,
  in the one-way full-sequence form used. (The four-way equivalence of Kun's
  Theorem 3 is *not* imported; its spectral implication fails as written, and
  the counterexample is formalized in `KunSpectralCounterexample`. See the
  literature audit below.)
- **The Kun–Thom centralizer obstruction** — `KunThomTheorem.isLEF_of_exactProductExpansion`.
- **Shalom's finitely presented Kazhdan covers** — `Shalom.exists_finitelyPresented_kazhdan_cover`.

The fourth, property `(T)` for elementary groups over arbitrary finitely
generated rings, is genuinely imported; the characteristic-two cases the
endpoints use are proved in `FreeElementaryPropertyT`.

The `K₁`-theoretic input is eliminated as well: `BinaryLeavitt.K1_trivial`
proves `K₁(L_k(1,2)) = 0` in Whitehead form by an elementary two-exit
elimination, so the Ara–Brustenga–Cortiñas localization sequence is
independent confirmation rather than a dependency.

## Trust surface

Every public result reduces to exactly the three axioms of classical Lean:
`propext`, `Classical.choice`, `Quot.sound`. There are no `sorry`s and the
library builds with `warningAsError=true`.

Three independent gates, none subsuming another:

- `NonsoficGroupsExist.Audit` prints the axiom report on an ordinary build.
- `scripts/Audit.lean` walks the transitive axiom closure of the whole
  namespace through the kernel environment, and pins the headline statements
  by restating them — a weakened statement stops typechecking.
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
`Classical.choice`, and `Quot.sound`; `scripts/Audit.lean` additionally rejects
any other axiom in the transitive closure of the entire namespace.

CI also runs the pinned Lean toolchain's built-in `leanchecker --fresh` on
`NonsoficGroupsExist.olean`. The exact command is in
`.github/workflows/prover.yml`; success is exit status zero after every
imported olean has been replayed into a fresh kernel environment. A cold
dependency download requires several gigabytes, and a cold project build can
take hours; subsequent cached builds are substantially faster.

The `official/` directory contains OpenAI's proof documents. They are not
imported by Lean and are distinct from the main
`nonsofic_groups_exist.tex` manuscript. The validated built PDF is
intentionally committed to `main` by the PDF workflow.

## Claim map

Every numbered result of `nonsofic_groups_exist.tex` is listed with its Lean
counterpart in **[docs/CLAIM_MAP.md](docs/CLAIM_MAP.md)** — status, modules,
declarations, and any way the Lean statement differs in generality from the
printed one.

That file is generated, not maintained.  The table it replaced was written by
hand and drifted into contradicting itself: one row recorded `thm:kcover` as
manuscript-only while the checklist above it recorded the same theorem as
formalized, and the manuscript inherited the wrong half.  The generated table
is derived from the manuscript's own margin notes resolved against the Lean
source, and `scripts/check.py` fails if it goes stale, so the two cannot
disagree without CI saying so.

```
python3 scripts/claim_map.py           # summary: statuses and coverage
python3 scripts/claim_map.py --write   # regenerate docs/CLAIM_MAP.md
python3 scripts/claim_map.py --json    # the map as data
```


## Margin cross-references in the manuscript

`nonsofic_groups_exist.tex` carries a margin note on each numbered statement
naming the Lean modules and declarations that formalize it, so the
correspondence is visible at the point of use rather than only in this file.
The notes are strictly marginal: no argument in the paper appeals to one, and
setting `\leanlinksfalse` in the preamble removes all of them and leaves the
text untouched.  Appendix A of the manuscript explains the three note forms
(formalized / partly formalized / not formalized) and the trust surface.

Nothing keeps such references true by itself, so they are checked rather than
trusted:

```
python3 scripts/check_lean_refs.py
```

extracts every `\leanmod{Module}{decls}` from the manuscript and fails unless
each module exists and each declaration is actually declared in it.  The PDF
workflow runs it before compiling, so a stale reference blocks the build
instead of shipping inside the PDF.  `scripts/lean_decls.py` builds the
declaration index it resolves against, and prints it when run directly.

## Module architecture

| Layer | Principal modules | Role |
| --- | --- | --- |
| External definitions | `Sofic`, `LEF`, `Kazhdan`, `ElementaryGroup` | Hamming models, local embeddings, real-orthogonal property `(T)`, and `EL_n` |
| Kun decomposition | `KunFiniteMarkov` through `KunDecomposition` and `KunFixedDecomposition` | Turns property `(T)` sofic models into negligible-edit uniform expander components |
| Compression matching | `CompressionSetup`, `Criterion`, `MatchingPreparation`, `MatchingSelection`, `SelectionOutput` | Matches core and ambient components and localizes the product action |
| Kun–Thom obstruction | `KunThomFiniteMarkov` through `KunThomTheorem` and `KunThomEssential` | Extracts LEF from exact-product expansion after repairing the relation to a permutation |
| Property `(T)` | `FreeRoot*`, `A2*`, `Kazhdan*`, `FreeElementaryPropertyT` | Proves the free characteristic-two `EL₃` Kazhdan input |
| Universal Leavitt witness | `UniversalLeavitt`, `LeavittRankEquivalence`, `UniversalRankFour`, `UniversalPropertyT`, `UniversalCompressionSetup` | Constructs the closed `EL₄(L_{𝔽₂}(1,2))` setup |
| Finite-field compression | `FiniteFieldLeavitt` | Constructs the complete rank-four setup over every finite field; property `(T)` and nonsoficity currently specialize to characteristic two |
| Endpoint and verification | `CriterionAssembly`, `TableCover`, `MainResults`, `Audit`; `scripts/Audit.lean` | Closes nonsoficity, builds the finitely presented cover, and audits statements and axioms |

## Literature audit: Kun's spectral characterization

Version 5 of Kun's *On sofic approximations of Property (T) groups*
([arXiv:1606.04471](https://arxiv.org/abs/1606.04471)) states Theorem 3 as an
equivalence.  Its final implication, `(4) -> (1)`, is not valid as written.
The proof invokes the ordinary Cheeger/Dodziuk--Alon--Milman eigenvalue-gap
bound to obtain an estimate for `M^2`.  Ordinary Cheeger expansion bounds the
nonconstant spectrum away from `+1`; it does not bound the bottom of the
Markov spectrum away from `-1`.  Uniform expanders can be arbitrarily close to
bipartite, so their least eigenvalues can approach `-1` without being exactly
`-1`.  More explicitly, make a degree-preserving two-edge switch in each graph
of a bipartite expander family, and then form one sequence containing repeated
copies of every switched graph.  The components retain a uniform Cheeger
constant, while their least Markov eigenvalues approach `-1`.  Repeating a
least-eigenvalue eigenvector on all copies makes its `L2` norm proportional to
the square root of the total vertex count, so the additive `L-infinity` error
in condition `(1)` cannot absorb the defect.  This gives a sequence satisfying
conditions `(2)`, `(3)`, and `(4)` but not `(1)`.  Thus the full four-way
equivalence must not be imported or used here.

This defect does not by itself refute Kun's Theorem 1.  In the same paper,
Proposition 11 establishes condition `(2)`, and the proof of Theorem 1 needs
only the forward combinatorial implications `(2) -> (3) -> (4)`.  The invalid
spectral implication `(4) -> (1)` is the reverse direction.  This repository's
required Kun dependency is therefore the one-way expander-decomposition
result.  The compiled Lean proof derives it from the forward property-`(T)`
partition-and-repair argument without appealing to the false equivalence.  It
also uses a full-sequence diagonal accuracy choice, so its conclusion applies
to the given approximation rather than only a subsequence.

The proved result is the full-generality one-way theorem: for every infinite
finitely generated property-`(T)` group, every finite symmetric generating set
containing the identity, and every sofic approximation, construct an
asymptotically edge-equivalent bounded-degree multigraph whose connected
components have one uniform positive Cheeger constant.  The fully explicit
headline declaration for an arbitrary generated set is
`KunDecomposition.exists_expanderDecomposition`; the generated-set wrapper is
`KunFixedDecomposition.expanderDecomposition`.

## Literature proof gaps and compiled repairs

The false spectral converse above is not the only issue in the cited proofs.
Kun's proof of the forward expander-decomposition result normalizes a Markov
defect in Lemma 10 without first excluding the case in which that defect is
zero.  The Lean development splits off the zero-vector case before
normalization and proves the homogeneous displacement estimate separately in
`Kazhdan.lean`; the subsequent finite-model partition and graph-repair chain
uses that total estimate.  Thus the compiled proof of Result A does not inherit
the division-by-zero gap.

The published Kun--Thom centralizer argument also constructs a general
relation but later treats it as though it were already the graph of a
permutation.  The Lean proof measures the row and column fibers of the improved
relation itself, extracts its injective matching core, and completes that core
to the genuine permutation `repairRelation`.  The theorem
`KunThomTheorem.isLEF_of_exactProductExpansion`, and its essential-expander
wrapper `KunThomEssential.isLEF_of_matchingCertificate`, compile without an
assumed Kun--Thom theorem.  These are repairs of gaps in proofs of the results;
they do not make the false spectral equivalence true.


## Development history

The checklist archaeology -- what was proved when, in what order, and the
intermediate results named along the way -- lives in
[docs/HISTORY.md](docs/HISTORY.md), alongside `BUILD_ITERATION_NOTES.md`.


