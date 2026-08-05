# NonsoficGroupsExist

This repository contains an unconditional Lean proof that a finitely
presented nonsofic group exists. The initial nonsofic group is now the
rank-four elementary group over the actual universal binary Leavitt algebra
`L_{𝔽₂}(1,2)`, defined as the quotient by its five displayed relations. The
proof then applies the finite-table cover theorem.

The proof establishes the dependencies in their required mathematical
generality needed by the endpoint. In particular, the Kun dependency is the
one-way theorem for every universe-0 infinite finitely generated group with
`HasKazhdanPropertyT.{0,0}`, every finite
symmetric identity-containing generating set, and every sofic approximation.
A theorem only for the concrete compression groups, an additional
non-bipartiteness hypothesis, or a caller-supplied expander decomposition will
not count as completing that dependency.  Likewise, the final nonsoficity
theorems must construct all property-`(T)`, compression, non-LEF, Kun, and
Kun--Thom inputs internally; none may remain an explicit argument, implicit
instance, bundled field, or `Nonempty` premise.

`HasKazhdanPropertyT` is stated using real orthogonal representations.  This
is the standard real form of property `(T)`, equivalent for discrete groups to
the complex-unitary formulation by realification/complexification.  The
current standalone theorem quantifies over universe-0 real Hilbert spaces; a
countable-orbit universe-reduction lemma has not yet been formalized.

The premise-free existence dependency chain is closed. Work is continuing on
the stronger objective of formalizing every result in
`nonsofic_groups_exist.tex` at its stated generality. Unchecked items in the
first checklist below are genuine manuscript-scope results not yet in Lean.

## Full manuscript scope

- [x] Define the universal algebra `L_{𝔽₂}(1,2)` as the presented quotient
- [x] Prove the universal quotient is nontrivial using its stream representation
- [x] Instantiate the full compression construction directly over the universal quotient
- [x] Prove `EL₄(L_{𝔽₂}(1,2))` is nonsofic and has property `(T)`
- [x] Generalize Theorem A to `EL_{m+1}(L_{𝔽₂}(1,2))` for every `m ≥ 1`
- [x] Define `L_k(1,2)` uniformly for every field `k`, prove its universal
  property and nontrivial stream representation, and provide finite-type,
  countability, infinitude, and canonical-family instances
- [x] Prove finite generation, infinitude, property `(T)`, and nonsoficity for
  `EL_{m+1}(L_k(1,2))` over every finite characteristic-two field and every
  `m ≥ 1`
- [x] Prove the complete rank-four compressor, elementary sign correction,
  involution, conjugation, and generation identities over every ring carrying
  a binary Leavitt family, with no characteristic assumption and no `K₁`
  input
- [x] Generalize elementary-root exponent identities and the finite
  class-two stage reduction from exponent two to arbitrary positive bounded
  exponent
- [x] Replace the irreducible class-two sign-character shortcut by a
  characteristic-free cyclic-orbit argument for central commutators of any
  positive bounded exponent
- [x] Replace the finite-dimensional sign-eigenspace recombination by an
  orthogonal irreducible decomposition with dimension induction, so the
  finite class-two `1 / sqrt 2` estimate and the universal class-two
  orthogonality theorem now hold for central commutators of any one positive
  bounded exponent; the former central-involution eigenspace module is
  removed as dead code
- [x] Generalize the entire A₂ vertex-angle, magic-graph defect,
  compressed-Laplacian gap, and root Kazhdan-subset chain from exponent-two
  roots to roots of any one positive bounded exponent; the elementary
  rank-three Kazhdan-subset theorem now holds over every ring of positive
  characteristic, so the remaining characteristic-two dependence is confined
  to the free-root Fourier relative-property-`(T)` transport
- [x] Generalize the free-algebra word-degree filtration (finite stages,
  monotonicity, degree additivity, generator advancement, word monomials,
  exhaustion) from `ZMod 2` to an arbitrary commutative coefficient
  semiring, with stage finiteness for every finite coefficient semiring;
  only the exact-support monomial expansion remains `ZMod 2`-specific
- [ ] Generalize the kernel-checked property-`(T)` theorem from
  characteristic two to arbitrary finite coefficient fields; this is now the
  only characteristic restriction in the adjacent-rank nonsoficity route
- [x] Formalize arbitrary finite-leaf self-similarity: every ring carrying a
  binary Leavitt family has explicit `M_r(R) ≃ R` for every `r ≥ 1`
- [x] Prove nonsoficity of `EL₂` by the all-positive-ranks Leavitt equivalence
- [ ] Prove a separate rank-two compression theorem
- [ ] Prove the GE/`K₁` inputs and `GL_r(L) = EL_r(L)` for all required ranks
- [x] Prove the full unit group and every positive-rank `GL_r` nonsofic
- [x] Prove every finitely generated nonsofic group has a finitely presented
  nonsofic cover
- [ ] Formalize Shalom's property-`(T)` finitely presented cover theorem
- [ ] Prove the property-`(T)` refinement and quotient claims of Theorem C
- [ ] Define Thompson's group `V` and identify the manuscript's tree-table
  and corner copies with it (the existence proof currently uses a stronger
  direct finite obstruction instead)
- [x] State and prove the bounded-degree form of the expander decomposition:
  the edited multigraphs carry one explicit occurrence-counting degree bound
- [ ] Align every TeX theorem and verification claim with its exact Lean declaration
- [ ] Re-run the complete MSI build and final axiom/source audit after all
  manuscript-scope additions

## Lean-backed claim map

| Claim | Lean declaration | Status |
| --- | --- | --- |
| `EL₄(L_{𝔽₂}(1,2))` is nonsofic | `universalLeavittEL4_not_isSofic` | Formalized |
| `EL₃(L_{𝔽₂}(1,2))` is nonsofic | `universalLeavittEL3_not_isSofic` | Formalized |
| The explicit ambient group is finitely generated, infinite, Kazhdan, and nonsofic | `ambient_profile` | Formalized |
| The explicit ambient group is countable, finitely generated, infinite, Kazhdan, and nonsofic | `ambient_full_profile` | Formalized |
| For every `m ≥ 1`, `EL_{m+1}(L_{𝔽₂}(1,2))` is finitely generated, infinite, Kazhdan, and nonsofic | `universalLeavitt_profile` | Formalized |
| The full unit group `L_{𝔽₂}(1,2)ˣ` is nonsofic | `universalLeavittUnits_not_isSofic` | Formalized |
| Every positive-rank `GL_r(L_{𝔽₂}(1,2))` is nonsofic | `universalLeavittGL_not_isSofic` | Formalized |
| Over every finite characteristic-two field, `EL_{m+1}(L_k(1,2))` is finitely generated, infinite, Kazhdan, and nonsofic for `m ≥ 1` | `binaryLeavitt_charTwo_profile` | Formalized |
| A nonsofic group exists | `nonsofic_groups_exist` | Formalized |
| A finitely presented nonsofic group exists | `exists_finitelyPresented_nonsofic_group` | Formalized |
| An infinite finitely presented nonsofic group surjects onto the explicit ambient group | `exists_infinite_finitelyPresented_nonsofic_ambient_cover` | Formalized |
| The universal binary Leavitt algebra has the required family | `UniversalLeavitt.family` | Formalized |
| The corner witness is non-LEF | `UniversalRankFour.witness_not_isLEF` | Formalized by a direct finite obstruction; not identified with `V` |
| The complete adjacent-rank compression construction works in every characteristic | `RankFour.compressorSet_conjugation`, `RankFour.coreEmbedding_compressorSet_generate` | Formalized |
| Kun's edited expander graphs have one uniform degree bound | `ExpanderDecomposition.degree_le`, `KunDecomposition.exists_expanderDecomposition` | Formalized |
| Property `(T)` and hence nonsoficity over finite fields of odd characteristic | — | Manuscript-only; the algebraic compression is already characteristic-free |
| `GL_r = EL_r` and the separate rank-two compression construction | — | Manuscript-only |
| A property-`(T)` finitely presented cover and the panorama of quotient claims | — | Manuscript-only |

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

## Proof status

Checked boxes below mean that the corresponding code has a genuine Lean proof
term and its module has compiled with warnings treated as errors. Manuscript
claims not yet formalized are listed separately in “Full manuscript scope.”

- [x] Standard finite Hamming approximation and soficity infrastructure
- [x] LEF definitions and the finite non-LEF obstruction
- [x] Explicit cylinder-transposition non-LEF subgroup
- [x] Injective embedding of that subgroup into the universal-Leavitt `EL₃` core
- [x] Universal rank-four compression maps and compressor identities
- [x] Characteristic-free elementary compressor and involution words, using
  an explicit Leavitt-unit commutator equal to scalar `-1`
- [x] Closed `UniversalRankFour.compressionSetup`
- [x] Finite-table theorem turning a finitely generated nonsofic group into a
  finitely presented nonsofic cover
- [x] GNS/Kazhdan finite-model contraction and rounding infrastructure
- [x] Terminating Kun finite partition recursion and cut accounting
- [x] Six-vertex A₂ magic graph and its exact Laplacian estimates
- [x] Class-two orthogonality estimate for central commutators of any one
  positive bounded exponent (instantiated at exponent two by the
  characteristic-two route)
- [x] Strict A₂ local and global moving-energy defect
- [x] Genuine Hilbert direct sum, fixed-family subspace, and compressed
  Laplacian
- [x] Real-Hilbert positive-operator gap proved by a convergent Neumann
  iteration (no spectral assumption)
- [x] Positivity, symmetry, and trivial kernel of the compressed A₂
  Laplacian
- [x] Strict moving-energy defect applied to prove the compressed quadratic
  operator gap
- [x] Explicit inverse norm bound for the compressed Laplacian, derived by
  the kernel-checked positive-operator iteration
- [x] Uniform A₂ constant-family/vertex projection bound with an explicit
  contraction factor below `1`
- [x] Transfer the projection contraction to strict vertex codistance and a
  genuine Kazhdan-subset bound for the union of the six root subgroups
- [x] Instantiate the root Kazhdan-subset theorem for the elementary
  rank-three group over every ring of positive characteristic; no
  exponent-law premise remains
- [x] Construct finite word-degree stages of the free characteristic-two
  algebra and prove that they are finite, monotone, and exhaustive (the
  algebraic filtration for the relative-property-`(T)` proof)
- [x] Prove multiplication adds free-word degree bounds and multiplication by
  each free generator advances the finite filtration by one stage
- [x] Construct finite, monotone degree stages inside every elementary root
  subgroup and prove that their supremum is the full root subgroup
- [x] Prove the exact elementary shear/conjugation identity and that
  commutation with each free-ring generator advances root degree by one
- [x] Build the finite two-root coefficient planes, prove that they exhaust
  the full additive plane, and prove the generator shear sends stage `n` to
  stage `n+1` by the explicit coefficient formula; prove separately, as
  ambient elementary-matrix equalities, that the shear fixes the first
  coordinate and sends the second coordinate to the precise first-times-second
  factorization in the next stage
- [x] Construct the positive/negative Hilbert-space splitting for represented
  involutions and prove orthogonality, Pythagoras, displacement, and
  conjugation covariance without a finite-dimensional spectral assumption;
  prove the resulting sign projections are idempotent, complementary, and
  pairwise commuting for commuting involutions
- [x] Iterate the involution splitting over an arbitrary finite family and
  prove exact vector reconstruction and conservation of total squared norm
  across all binary sign components; for commuting families, prove every
  component is a simultaneous eigenvector with exactly its assigned signs
- [x] Prove the simultaneous decomposition is covariant under conjugating the
  entire family, prove distinct sign components are pairwise orthogonal, and
  identify the squared norm of every finite subfamily sum with its exact
  component-mass sum; identify the mass of characters taking value `-1` on
  any finite-plane element with exactly one quarter of that element's squared
  displacement
- [x] Prove quantitative finite-stage character-mass transport under each
  free-generator shear: the next-stage sheared event and the original
  coordinate event differ by at most `2 * ‖z‖` times the displacement of `z`
  under that single elementary generator
- [x] Prove every finite free-root plane is abelian of exponent two, enumerate
  all of its elements, and instantiate the simultaneous Fourier decomposition
  and sign-action theorem for that exhaustive enumeration; prove every
  nonzero component's assigned `±1` eigenvalues are multiplicative and send
  the identity to `1`
- [x] Factor every finite-plane element through its two coefficient roots and
  derive genuine additive `𝔽₂` coefficient characters (addition maps to sign
  multiplication and zero maps to `1`) on every nonzero Fourier component;
  prove every nontrivial plane character is nontrivial on at least one of the
  two coefficient coordinates
- [x] Expand each degree-bounded free polynomial in its exact supported-word
  basis and prove that any nontrivial additive sign character is already
  detected on one of those supported word monomials; decompose every
  positive-degree witness into its first free generator and strictly shorter
  tail, with the corresponding exact monomial factorization
- [x] Define Kassabov's finite-stage character valuation as the least detected
  free-word degree (using `n+1` exactly for a stage-trivial character), prove
  valuation zero is precisely unit-coefficient detection, define the four
  `A/B/C/D` valuation regions, and prove a nonzero component with nontrivial
  plane character has at least one valuation at most `n`; prove the exact
  leading-letter lemma that a positive valuation has a generator-derived
  character whose valuation is smaller by exactly one
- [x] Enumerate the finite free-generator alphabet, collect every generator
  realizing exact valuation descent, prove that set is nonempty whenever the
  valuation is positive and detected, and define a canonical least-index
  selector with its exact descent theorem
- [x] Separate the all-trivial character pair into its own `zero` region
  (rather than incorrectly counting it in `B`), partition `A ∪ B` and `C ∪ B`
  into exact pairwise-disjoint least-leading-generator fibers, and prove both
  finite-stage dual shear formulas carry every fiber into Kassabov's required
  opposite-or-`D` valuation regions
- [x] Prove simultaneous sign projections are additive over finite sums,
  select joint eigenvectors exactly, and instantiate the resulting refinement
  theorem to show each degree-`n` plane component is the exact sum of all
  compatible degree-`n+1` Fourier components
- [x] Construct the concrete forward and opposite conjugated-plane maps into
  the next filtration stage, re-index them in the exhaustive enumeration, and
  prove exact Fourier covariance: an acted-on coarse component is the sum of
  precisely its conjugated fine extensions; identify both restricted
  coefficient characters with the algebraic dual shears and prove the
  transported valuation-region conclusions for every nonzero fine component
- [x] Prove exact squared-mass conservation for arbitrary coarse sign sets
  under refinement and conjugation, derive both concrete per-leading-fiber
  mass bounds, and prove that below the top-degree boundary restriction
  preserves every leading generator and the canonical least leading index
- [x] Prove the actual transported leading-fiber image sets are pairwise
  disjoint below the top-degree boundary, charge each interior fiber only to
  its concrete image set, and prove arbitrary selected Fourier projections
  are contractive and have the required squared-mass continuity estimate
- [x] Prove that every nonmultiplicative binary sign assignment has zero
  Fourier component, remove those invalid assignments from both transported
  image families, prove the valid images lie in the required target regions,
  and derive the two disjoint below-boundary mass-sum inequalities with the
  target mass counted once rather than once per free generator
- [x] Identify each top-degree boundary as the exact drop of a nested
  nonnegative trivial-character mass, prove both boundary masses tend to
  zero, and combine them with the disjoint interior estimates into the two
  full finite-stage Kassabov inequalities
- [x] Construct the two same-stage unit-root conjugations, prove their exact
  Fourier transport sends `A` and `C` into `B`, and bound region `D` by the
  two unit-coordinate displacements
- [x] Prove ordinary refinement preserves every valid valuation region away
  from the two new top-degree layers, charge coarse target mass to the
  same-stage target plus those already-vanishing layers, and combine both
  generator shears with the unit shears into a single explicit finite-stage
  bound for all four nonzero valuation regions
- [x] Pass the finite-stage inequalities to the limiting two-root moving
  mass and complete the uniform relative-property-`(T)` estimate
- [x] Prove property `(T)` for elementary rank three over every finite-rank
  free characteristic-two algebra, using an explicit finite Kazhdan set
- [x] Transfer/instantiate property `(T)` for every universal-Leavitt group used by the
  compression argument
- [x] Close the exact full-sequence Kun expander-decomposition theorem used at the final
  criterion boundary
- [x] Close the exact Kun--Thom centralizer/LEF implication used at the final
  criterion boundary
- [x] Assemble an unconditional universal-Leavitt nonsofic group with no setup,
  literature theorem, property-(T), or non-LEF premise
- [x] Instantiate the finite-table cover to obtain an unconditional finitely
  presented nonsofic group
- [x] Add the two unconditional public headline declarations
- [x] Run the complete `lake build` for the premise-free existence baseline
- [x] Audit the baseline closed headline signatures and run `#print axioms`
- [x] Search the baseline for and eliminate forbidden trust bypasses, stale
  conditional wrappers, dead code, and misleading documentation

The final two declarations have exactly these premise-free mathematical
types:

```lean
theorem nonsofic_groups_exist : NonsoficGroupExists := by
  ...

theorem exists_finitelyPresented_nonsofic_group :
    ∃ (G : Type) (_ : Group G),
      Group.IsFinitelyPresented G ∧ ¬ IsSofic G := by
  ...
```

The current complete MSI build reports `Build completed successfully (3245
jobs).` The transitive axiom reports for both headline theorems and for
`universalLeavittEL4_not_isSofic` are exactly
`[propext, Classical.choice, Quot.sound]`; there is no project axiom or
unproved placeholder in either proof term. The source audit finds no
declaration of a custom axiom, no proof placeholder, and none of the former
literature-hypothesis parameters. The remaining `KunThomTheorem` matches are
the module and namespace containing the compiled proof, not an assumed
proposition interface. The source audit covers all 159 project modules, and
the whole-namespace kernel audit traverses every project declaration and
reports no disallowed axiom. This build and audit are
the current universal-quotient integration checkpoint; both will be rerun after
each later manuscript-scope checkpoint.

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

## What is already formalized

What is kernel-checked includes finite Hamming/sofic bookkeeping, localization,
finite-table covers, the universal binary Leavitt quotient and its canonical
family, elementary-matrix embeddings and compression maps, and a genuine
two-generator non-LEF subgroup built from cylinder transpositions.  That
subgroup is embedded injectively into the universal-Leavitt `EL₃` core by explicit
commutator and Whitehead identities.  The rank-four compressor words satisfy
the required conjugacy identities, generate the ambient `EL₄` together with
the core, and have the required centralization and trivial-intersection
properties. `UniversalRankFour.compressionSetup` assembles these facts into a
closed algebraic setup.

The rank-four compressor and involution are now explicit elementary words in
every characteristic. The only sign formerly supplied by characteristic two
is obtained from a proved commutator of two concrete Leavitt units and the
Whitehead identity. Thus the remaining finite-field restriction comes from
the current property-`(T)` formalization, not from compressor membership or
matrix identities.

The analytic development also constructs the GNS Hilbert space of every
limiting sofic correlation, proves the iterated Kazhdan contraction there,
uniformizes it back to all sufficiently large finite models, and controls the
approximate-multiplication error between exact group words and the actual
finite permutation Markov operator.  Consequently, genuine finite-model
Markov displacements satisfy an arbitrarily strong contraction, uniformly over
every centered indicator, with arbitrarily small normalized additive error.  The
one-step displacement is now related to the genuine directed generator-cut
energy, and centering has been eliminated from the threshold-rounding input.
Finite coarea rounding, maximal-bad-set removal, and finite support propagation
are also kernel-checked.  A geometric-series movement estimate now keeps the
replacement-set proximity coefficient independent of the Markov horizon; a
second maximal-bad-set argument removes its additive finite-model error.  The
resulting rounding theorem therefore has a fixed admissible input-cut
threshold even as the requested boundary ratio tends to zero.  Kun's complete
terminating finite partition recursion constructs blocks with a uniform global
cut inequality and a linear small-boundary budget.  The development charges
all inter-block generator edges to exceptional incidence or reference cuts,
constructs an explicit edit witness, performs the selective matching repair,
and proves uniform componentwise expansion.  A slowly growing accuracy level
does this on every model of the original sofic approximation; the theorem does
not discard to a cofinal subsequence.

No decisive mathematics remains hidden behind theorem-shaped parameters. The
exact Kun expander decomposition and Kun--Thom implication are
now proved and compiled. The finite-stage Fourier argument has also been
passed to the exhaustive free-root plane and yields an explicit finite
Kazhdan pair for elementary rank three over every finite-rank free
characteristic-two algebra. The universal quotient map from the free algebra
transfers this property to the universal-Leavitt `EL₃` core, and the explicit
Leavitt rank equivalence transfers it to the `EL₄` ambient group. The stream
representation is used only to prove that the presented quotient is
nontrivial. The non-LEF witness is not yet identified with Thompson's group
`V`; the closed existence proof instead uses its directly proved finite
obstruction.

`TableCover` proves that a finitely generated nonsofic group has a finitely
presented nonsofic cover. `MainResults` instantiates it with
`EL₄(L_{𝔽₂}(1,2))`, proved nonsofic by the closed compression criterion.

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
