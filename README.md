# NonsoficGroupsExist

A machine-checked Lean 4 proof that **nonsofic groups exist** — including a
finitely presented one — settling a question of Weiss, open since 2000.

The witness is explicit: `EL₄(L_{𝔽₂}(1,2))`, the rank-four elementary group
over the universal binary Leavitt algebra. It is countable, infinite,
finitely generated, has Kazhdan's property `(T)`, and is not sofic. The
accompanying manuscript is `nonsofic_groups_exist.tex`; the committed
`nonsofic_groups_exist.pdf` is its validated build.

## Main theorems

All reachable from `NonsoficGroupsExist/Endpoint/MainResults.lean`:

| Declaration | Statement |
| --- | --- |
| `nonsofic_groups_exist` | A nonsofic group exists |
| `countable_nonsofic_groups_exist` | A countable nonsofic group exists — the historical headline |
| `universalLeavittEL4_not_isSofic` | The explicit witness is not sofic |
| `universalLeavitt_profile` | The full profile — infinite, finitely generated, Kazhdan, nonsofic — at every elementary rank `≥ 2` (Theorem A) |
| `binaryLeavitt_finiteField_profile`, `binaryLeavittUnits_profile`, `binaryLeavittGL_profile` | The same over every finite field, for elementary ranks, the unit group, and every `GL_r` (Theorem B) |
| `exists_finitelyPresented_nonsofic_group` | A finitely presented nonsofic group exists |
| `exists_kazhdan_finitelyPresented_cover_of_not_isSofic` | ... and a finitely presented Kazhdan cover (Theorem C) |
| `exists_sofic_group_with_nonsofic_quotient` | Soficity is not closed under quotients |

The transitive axiom closure of every public result is checked to contain no
axioms beyond the three of classical Lean — `propext`, `Classical.choice`,
`Quot.sound` — with no `sorry` and no project axioms (individual results may
use a proper subset), and the library builds with `warningAsError=true`.

## Formal versus manuscript trust surface

The Lean development's external trust surface is smaller than the
manuscript's: several results the paper cites are proved internally.

| Input | Manuscript | Lean |
| --- | --- | --- |
| Kun expander decomposition | cited (arXiv v5), audited | proved — `Kun/KunDecomposition` |
| Kun–Thom centralizer obstruction | cited (arXiv v2), audited | proved — `KunThom/KunThomTheorem` |
| Property `(T)` at rank three | cited (Ershov–Jaikin) | proved — `PropertyT/FiniteFieldElementaryPropertyT` |
| Strong division for `L_k(1,2)` | cited, from pure infinite simplicity | proved — `Leavitt/LeavittSimplicity` |
| Shalom finitely presented Kazhdan covers | cited | proved — `Kazhdan/ShalomFinitePresentation` |
| Residual finiteness of free groups | standard fact | proved — `Sofic/FreeGroupResiduallyFinite` |

## How to verify

The repository pins Lean `v4.32.2` and a Mathlib commit in `lean-toolchain`
and `lake-manifest.json`; do not update the manifest during verification.

```bash
lake exe cache get
python3 scripts/check.py --self-test   # calibrate the source scan
python3 scripts/check.py               # source audit: what the kernel cannot see
lake build                             # the library, warnings as errors
lake build Audit
lake env lean scripts/Calibrate.lean
lake env lean scripts/Audit.lean       # kernel audit: axioms, statements, scans
```

Three independent gates, none subsuming another:

- `NonsoficGroupsExist.Audit` prints the axiom reports on an ordinary build.
- `scripts/Audit.lean` walks the transitive axiom closure of the whole
  namespace through the kernel, pins the headline statements by restating
  them (a weakened statement stops typechecking), and scans the compiled
  environment for laundered propositions, unwitnessed structures, and their
  relatives.
- `scripts/check.py` scans the source text, which sees what the kernel
  cannot: comments, docstrings, and files that are never compiled. Its
  detectors are calibrated in both directions by `--self-test`.

CI additionally replays every olean into a fresh kernel with the pinned
toolchain's `leanchecker --fresh`. A cold build downloads several gigabytes
and can take hours; cached builds are substantially faster.

Read "verified" as the specific layer that ran, never as a blend. The layers,
weakest to strongest: (1) the lexical source scan (`scripts/check.py`);
(2) elaboration (`lake build`); (3) kernel axiom closure and environment
scans (`scripts/Audit.lean`); (4) fresh-kernel olean replay (`leanchecker
--fresh`); (5) manuscript statement correspondence — name resolution by the
claim map, elaborated types by `docs/CLAIM_SIGNATURES.md`, verbatim
restatement pins for the headliners; (6) replay through an independently
written kernel (`independent-kernel.yml`), which is supplementary and not a
gate.

An axiom audit says nothing about whether the statement proved is the one
intended. The two definitions carrying most of that weight are discharged as
theorems: `hasKazhdanPropertyT_iff_textbook` identifies the real-orthogonal
property `(T)` used throughout with the textbook complex-unitary one, and
`isLEF_iff_textbook` does the same for local embeddability.

Two further conventions, for reading endpoints. `IsSofic` is a local
finite-model property that makes sense for arbitrary groups, while
`SoficApproximation` is the sequential object of the paper's Section 2; the
sequential direction of the interconversion is where countability enters,
and it is automatic for the finitely generated groups in every endpoint.
Property `(T)` endpoints are stated at the own-universe real-orthogonal
convention (`HasKazhdanPropertyT.{0,0}`), with the textbook identification
supplied separately by the theorem above.

## Where to start reading

`NonsoficGroupsExist/Endpoint/Public.lean` is the reading path. It proves
nothing; it names the declarations a referee needs, each against the theorem
of the manuscript it establishes, and you follow the imports downward.

Every numbered result of the manuscript is listed with its Lean counterpart
in **[docs/CLAIM_MAP.md](docs/CLAIM_MAP.md)** — modules, declarations, and
any way the Lean statement differs in generality from the printed one. The
table is generated from the manuscript's own margin notes resolved against
the Lean source, and `scripts/check.py` fails if a note names a declaration
that does not exist or the table goes stale. That check is by name: it
guarantees every mapped declaration exists (uniquely — an ambiguous short
name is an error the note must settle by qualifying it), not that its
elaborated statement matches the printed one. Statements are pinned by two
further layers: the headline theorems are restated verbatim in
`scripts/Audit.lean`, and the elaborated type of *every* mapped declaration
is recorded in `docs/CLAIM_SIGNATURES.md`, regenerated by
`lake env lean scripts/Signatures.lean` and diffed in CI — a mapped theorem
cannot lose a conclusion or gain a hypothesis without a red run. The margin notes are strictly
marginal: no argument in the paper appeals to one.

## Nothing cited, everything proved

The manuscript's proofs cite external theorems, as papers do. The library
proves every one of them internally, in the exact forms used, so no endpoint
depends on the literature. The largest of these internal proofs:

- **Kun's expander decomposition**, in the one-way full-sequence form used
  (`KunDecomposition`).
- **The Kun–Thom centralizer obstruction** (`KunThomTheorem`).
- **Property `(T)` at rank three** over every finite field, with an explicit
  Kazhdan pair (`FiniteFieldElementaryPropertyT`), spread to every rank by
  the Leavitt rank equivalence.
- **Shalom's finitely presented Kazhdan covers** (`ShalomFinitePresentation`).
- **The non-LEF witness**, with no simplicity or finite-presentation input
  for Thompson's `V`: a two-relator obstruction and explicit commutator
  certificates (`ThompsonFObstruction`, `ThompsonWitness`); `V` itself is
  proved non-LEF along the way (`thompsonV_not_isLEF`).
- **The `K₁` input**: `K₁(L_k(1,2)) = 0` over every field in Whitehead form
  (`K1_trivial`), `GL_n = EL_n` at every rank `n ≥ 2`, and perfectness of
  the unit group, by an elementary elimination written out as Appendix A —
  the cited localization-sequence results become independent confirmation
  rather than dependencies.

## Library layout

Each directory tracks a section of the paper.

| Directory | Paper | Contents |
| --- | --- | --- |
| `Sofic/` | §2 | Sofic approximations, LEF, generator graphs, the two-relator obstruction |
| `Kazhdan/` | §2 | Real-orthogonal property `(T)`, complexification, universe transfer, GNS |
| `Kun/` | §2.5 | The one-way expander decomposition |
| `KunThom/` | §2.5 | The centralizer obstruction |
| `Matching/` | §3 | The five finite lemmas: refinement, conservation, pinning, selection, completion |
| `Criterion/` | §4 | Median normalization, matching, localization; the compression–centralizer theorem |
| `Leavitt/` | §5–§6 | Leaf calculus, self-similarity, rank equivalence, compressors, the corner witness, the `d`-ary corner route |
| `PropertyT/` | §5 | Property `(T)` at rank three over every finite field, from an explicit `A₂` gap |
| `KOne/` | App. A | The elementary `K₁` elimination: windows, pencils, the two-exit loop, all-ranks `GL = EL` |
| `Covers/` | §9 | The finite-table and Kazhdan finitely presented covers |
| `Monsters/` | — | The elementary deduction layer of the omnimonster constructions |
| `Endpoint/` | §1 | `MainResults`, `Public`, `QuotientNonclosure`, the in-build `Audit` |

The `d`-ary layer and `Monsters/` prove more than the manuscript states;
they sit inside the audit gates but no numbered result maps onto them. The
separate `Superseded` library holds developments that later proofs replaced;
it is built so it cannot rot, but nothing imports it — it is off the trust
surface. `official/` contains OpenAI's proof documents, not imported by
Lean and distinct from the manuscript.

## A literature finding

Version 5 of Kun's *On sofic approximations of Property (T) groups*
([arXiv:1606.04471](https://arxiv.org/abs/1606.04471)) states Theorem 3 as a
four-way equivalence. Its implication `(4) → (1)` is not valid as written:
the cited Cheeger bound separates the Markov spectrum from `+1` but not from
`-1`, and uniform expanders can be arbitrarily close to bipartite. A
degree-preserving two-edge switch in each graph of a bipartite expander
family gives a sequence satisfying `(2)`–`(4)` but not `(1)`. The
counterexample's mathematical content is formalized in
`KunSpectralCounterexample`: the switched family, its uniform Cheeger lower
bound `1`, its non-bipartiteness, the Rayleigh quotient running to `-1`, and
the packaged refutation (`no_uniform_spectral_gap`) that no spectral gap at
`-1` follows from any uniform Cheeger bound. The translation into the
literal numbered conditions of Kun's Theorem 3, and the repetition of
components, remain prose, as that module's header records. This does not
affect Kun's Theorem 1, which needs only the forward implications — exactly
the one-way form proved and used here. Two smaller proof-level gaps (the
zero-defect case of Kun's Lemma 10, and a relation treated as a permutation
in the published Kun–Thom argument) are repaired in the Lean proofs.

## Development history

What was proved when, in what order, and the intermediate results named
along the way: [NOTEPAD.md](NOTEPAD.md).
