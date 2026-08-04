# NonsoficGroupsExist

This repository is an active Lean formalization of a proposed construction of
a finitely presented nonsofic group. It does **not yet** prove that such a
group exists. The current estimate is **about 61% of the way to the complete
unconditional proof**. This percentage measures closed dependencies on the
critical path, not lines of Lean.

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
  stage `n+1` by the explicit coefficient formula
- [x] Construct the positive/negative Hilbert-space splitting for represented
  involutions and prove orthogonality, Pythagoras, displacement, and
  conjugation covariance without a finite-dimensional spectral assumption;
  prove the resulting sign projections are idempotent, complementary, and
  pairwise commuting for commuting involutions
- [x] Iterate the involution splitting over an arbitrary finite family and
  prove exact vector reconstruction and conservation of total squared norm
  across all binary sign components
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
required expander decomposition and Kun--Thom implication, the relevant
property `(T)` results.  The represented stream-operator algebra is not
identified with the universal Leavitt algebra, and the non-LEF witness is not
identified with Thompson's group `V`; neither identification is used by the
concrete compression setup.

`TableCover` proves a conditional reduction: a finitely generated nonsofic
group has a finitely presented nonsofic cover. It does not provide the initial
nonsofic group.
