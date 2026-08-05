# NonsoficGroupsExist

This repository is an active Lean formalization of a proposed construction of
a finitely presented nonsofic group. It does **not yet** prove that such a
group exists.

The project is pursuing the unconditional result in full mathematical
generality.  In particular, the Kun dependency means the one-way theorem for
**every** infinite finitely generated property-`(T)` group, every finite
symmetric identity-containing generating set, and every sofic approximation.
A theorem only for the concrete compression groups, an additional
non-bipartiteness hypothesis, or a caller-supplied expander decomposition will
not count as completing that dependency.  Likewise, the final nonsoficity
theorems must construct all property-`(T)`, compression, non-LEF, Kun, and
Kun--Thom inputs internally; none may remain an explicit argument, implicit
instance, bundled field, or `Nonempty` premise.

There is no honest numerical completion percentage at present: the remaining
items include substantial theorems of very different sizes, so a percentage
would suggest precision the dependency graph cannot support.  The checked
milestones below are the progress record.

## Proof status

Checked boxes below mean that the corresponding code has a genuine Lean proof
term and its module has compiled with warnings treated as errors. An unchecked
box is still a required dependency of the final theorem.

- [x] Standard finite Hamming approximation and soficity infrastructure
- [x] LEF definitions and the finite non-LEF obstruction
- [x] Explicit cylinder-transposition non-LEF subgroup
- [x] Injective embedding of that subgroup into the concrete `EL₃` core
- [x] Concrete rank-four compression maps and compressor identities
- [x] Closed `ConcreteRankFour.compressionSetup`
- [x] Finite-table theorem turning a finitely generated nonsofic group into a
  finitely presented nonsofic cover
- [x] GNS/Kazhdan finite-model contraction and rounding infrastructure
- [x] Terminating Kun finite partition recursion and cut accounting
- [x] Six-vertex A₂ magic graph and its exact Laplacian estimates
- [x] Characteristic-two class-two orthogonality estimate
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
- [x] Instantiate the root Kazhdan-subset theorem for every characteristic-two
  elementary rank-three group; no exponent-law premise remains
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
- [ ] Pass the finite-stage inequalities to the limiting two-root moving
  mass and complete the uniform relative-property-`(T)` estimate
- [ ] Prove property (T) for the concrete characteristic-two rank-three group
- [ ] Transfer/instantiate property (T) for every concrete group used by the
  compression argument
- [ ] Close the exact Kun expander-decomposition theorem used at the final
  criterion boundary
- [ ] Close the exact Kun--Thom centralizer/LEF implication used at the final
  criterion boundary
- [ ] Assemble an unconditional concrete nonsofic group with no setup,
  literature theorem, property-(T), or non-LEF premise
- [ ] Instantiate the finite-table cover to obtain an unconditional finitely
  presented nonsofic group
- [ ] Add the two unconditional public headline declarations
- [ ] Run the complete `lake build`
- [ ] Audit the closed headline signatures and run `#print axioms`
- [ ] Search for and eliminate forbidden assumptions, `sorry`, stale
  conditional wrappers, dead code, and misleading documentation

The final two declarations will remain unchecked until they can be consumed
with exactly these premise-free mathematical types:

```lean
theorem nonsofic_groups_exist : NonsoficGroupExists := by
  ...

theorem exists_finitelyPresented_nonsofic_group :
    ∃ (G : Type) (_ : Group G),
      Group.IsFinitelyPresented G ∧ ¬ IsSofic G := by
  ...
```

## What is already formalized

What is kernel-checked includes finite Hamming/sofic bookkeeping, localization,
finite-table covers, a represented algebra satisfying the binary Leavitt
relations, elementary-matrix embeddings and compression maps, and a genuine
two-generator non-LEF subgroup built from cylinder transpositions.  That
subgroup is embedded injectively into the concrete `EL₃` core by explicit
commutator and Whitehead identities.  The rank-four compressor words satisfy
the required conjugacy identities, generate the ambient `EL₄` together with
the core, and have the required centralization and trivial-intersection
properties.  `ConcreteRankFour.compressionSetup` assembles these facts into a
closed concrete algebraic setup.

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
all inter-block generator edges to exceptional incidence or reference cuts and
constructs an explicit edit witness deleting them.  It does not yet perform
Kun's subsequent matching repair that turns the additive block inequalities
into genuine componentwise expansion.

The decisive remaining mathematics is not hidden behind theorem-shaped
parameters. In particular, the repository currently lacks proofs of the
required expander decomposition and Kun--Thom implication and the relevant
property `(T)` results.  The represented stream-operator algebra is not
identified with the universal Leavitt algebra, and the non-LEF witness is not
identified with Thompson's group `V`; neither identification is used by the
concrete compression setup.

`TableCover` proves a conditional reduction: a finitely generated nonsofic
group has a finitely presented nonsofic cover. It does not provide the initial
nonsofic group.

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
result, and it must be checked from the forward partition-and-repair argument
without appealing to the false equivalence.  The corresponding completion
checkbox remains open above until that exact Lean dependency is compiled and
wired into the final theorem.

The target here is the full-generality one-way theorem: for every infinite
finitely generated property-`(T)` group, every finite symmetric generating set
containing the identity, and every sofic approximation, construct an
asymptotically edge-equivalent bounded-degree multigraph whose connected
components have one uniform positive Cheeger constant.  Proving only the
particular instances needed by the proposed nonsofic construction would not
close this checkbox; the development is pursuing the general theorem directly.
