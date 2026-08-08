# The phase story: where hyperlinear and sofic part company

This is a reader's map of the unitary side of the development, in the order the
statements depend on one another rather than the order they were proved.  Every
theorem named here is machine-checked; the file names are modules under
`NonsoficGroupsExist/Sofic/`.

The question in the background is Pestov's Question 3.4 — *is every hyperlinear
group sofic?* — and the thread below does not answer it.  What it does is
replace the usual atmospheric account of the difference between the two classes
("permutations versus unitaries") with named finite statements.

## 0. The direction that holds

`Hyperlinear.lean`.  Soficity implies hyperlinearity, and for a completely
transparent reason: the two metrics are the same metric.  For permutations
`σ, τ` of a finite set,

    ‖P_σ − P_τ‖²_HS = 2 · d_Hamm(σ, τ)

(`permMatrix_hsDistSq`), and `σ ↦ P_{σ⁻¹}` is a genuine homomorphism, so a
sofic model of accuracy `ε/2` *is* a hyperlinear model of accuracy `ε`.  The
factor two is the whole of the translation.  Nothing here bears on the
converse; the point is that the difficulty is not hiding in the easy direction.

## 1. The separation constant, and an asymmetry in its proof

`SoficAmplification.lean`, `HyperlinearAmplification.lean`.

On the permutation side the separation constant is a convention: the `k`-fold
tensor power sends Hamming distance `d` to `1 − (1−d)^k`, so a fixed separation
runs to the maximum while a small multiplicative defect grows only by a factor
`k`.  Pestov's survey asserts the same refinement for the unitary
characterization, without proof.

**The unitary amplification fails.**  The algebra transports exactly —
`τ(A^{⊗k}(B^{⊗k})*) = τ(AB*)^k`, hence

    ‖A^{⊗k} − B^{⊗k}‖²_HS = 2 − 2 Re(τ(AB*)^k)

(`hsDistSq_tensorPow`) — and the conclusion still fails, because a scalar enters
the tensor power as its `k`-th power.  `1` and `i·1` are unitary, maximally
separated, and have **equal fourth tensor powers** (`tensorPow_phase_collapse`).
Permutation matrices carry no phases, which is exactly why the sofic argument
works and this one cannot.

The repair is the conjugate double `A ⊗ Ā`, whose normalized trace is `|τ(A)|²`
— a nonnegative real, so no phase survives to be recombined:

    ‖(A⊗Ā)^{⊗k} − (B⊗B̄)^{⊗k}‖²_HS = 2 − 2|τ(AB*)|^{2k}

(`hsDistSq_conjDoubleTensorPow`), which reaches the maximum iff `|τ(AB*)| < 1`.

The two classes do coincide — by Rădulescu's theorem, `Γ` hyperlinear iff
`L(Γ)` embeds in `R^ω`, which supplies the trace normalization outright.  So
the content here is a *proof-theoretic* asymmetry: elementary on one side, a von
Neumann algebra theorem on the other, and the elementary route provably does not
exist.

## 2. The trace defect is a distance

`HyperlinearScalar.lean`.  For a unitary `U` and any scalar `c`,

    ‖U − c·1‖² = 1 − 2 Re(c̄ τ(U)) + |c|²,

minimized at `c = τ(U)`, where it reads

    ‖U − τ(U)·1‖² = 1 − |τ(U)|².

The trace defect **is** the squared distance to the scalars.  Hence
`|τ(U)| ≤ 1` always, with equality exactly when `U` is that scalar.  This is
what converts a statement about phases into a statement about distance, so that
a phase can be propagated through products.  The transport it needs —
invariance under unitary multiplication on either side and under conjugate
transposition, scaling by `|c|²`, the crude triangle inequality
`‖A+B‖² ≤ 2‖A‖² + 2‖B‖²`, and Cauchy–Schwarz `|τ(C)|² ≤ ‖C‖²` — is all proved
here, in squared form, so no square roots appear anywhere in the development.

## 3. Phases live only on small torsion

`PhaseOrder.lean`, `PhasePropagation.lean`.

No point of the unit circle keeps its first four powers in the left half plane:

    max(Re ζ, Re ζ², Re ζ³, Re ζ⁴) ≥ 3/10

(`re_pow_max_ge`), the four real parts being the Chebyshev polynomials of
`Re ζ`.  Four powers are needed and no fewer, and the exceptions are exactly the
roots of unity of order at most four.

Propagation makes this bite.  From `U^{l+1} − τ^{l+1} = U^l(U − τ) + τ(U^l − τ^l)`
one gets `‖U⁴ − τ⁴·1‖² ≤ 22(1 − |τ(U)|²)`, so a unitary whose trace is within
`10⁻⁶` of the circle has `Re τ(U^l) ≥ 1/4` for some `l ≤ 4`.  Carrying this
through a model's own multiplicative defect gives:

**A separated model cannot put a phase on an element of order five or more**
(`normSq_normTrace_lt_of_separated`).

The order-two exception, which is where lamp groups live, closes too: two
nontrivial involutions with nontrivial product cannot *both* be sent near a
scalar, since each would have to be near `−1` and their product near `+1`
(`not_both_normSq_normTrace_ge`).  In an elementary abelian `2`-group at most
one element can carry a phase.

## 4. Monomial models, and what untwisting costs

`MonomialModel.lean`.  A hyperlinear model that is not visibly sofic is usually
not shapeless: Thom's microstates for `K = K₀(ℤ[1/p])/ℤ` lie in the monomial
group `T_Y ⋊ Sym Y`, and they are *forced* there, since every finite-dimensional
unitary representation of `K` kills its divisible centre.

Two inequalities measure the distance to soficity, pulling opposite ways:

    2 d_Hamm(σ, τ) ≤ ‖A(d,σ) − A(e,τ)‖²      the permutation part inherits
                                              the whole multiplicative defect
    |τ(A(d,σ))|² ≤ (1 − d_Hamm(σ, 1))²        the trace is bounded by the
                                              fixed-point fraction

So a monomial model is a sofic model exactly when its underlying permutations
are already almost fixed-point free; what it may do instead is let the phases
cancel over the fixed points (`monomial_normTrace_zero_of_identity`).

Untwisting is always available as a construction — `(y,j) ↦ (σy, j + d y)` is an
honest permutation of `Y × ℤ/m` — and its price and yield are exact:

    d_Hamm(untwist(d,σ), untwist(e,τ)) = density{ y : σy ≠ τy or d y ≠ e y }
    d_Hamm(untwist(d,σ), 1)            = 1 − density{ y : σy = y and d y = 0 }

## 5. The characterization

`MonomialModel.lean`.  The criterion and its converse give

    sofic  ⟺  combinatorial monomial approximability

(`isSofic_iff_monomial`): requiring the phases to be multiplicative
*combinatorially* — agreeing as elements of `ℤ/m` outside a small set — adds
nothing to soficity.  The open question is therefore not about monomial models
versus permutation models.  It is about **which notion of "the phases agree" is
demanded**: combinatorial agreement gives soficity on the nose, and metric
agreement is what hyperlinearity supplies.

## 6. How far apart the two demands are

`ScalarCocycle.lean`.  A scalar has two prices, and they do not match:

    ‖A(d,σ) − A(ζd,σ)‖² = |1 − ζ|²          arbitrarily small
    d_Hamm(untwist(d,σ), untwist(d+c,σ)) = 1  maximal, for every c ≠ 0

A scalar cocycle is invisible to the metric hyperlinearity uses and maximal in
the metric soficity uses.  The extreme case says it in one line: on any nonempty
model, the monomial matrices with the same permutation part and phases `1` and
`−1` sit at the *maximal* Hilbert–Schmidt distance `4` while their permutation
parts are equal (`hsDistSq_max_of_equal_perm`).

The same file records why exact infeasibility proves nothing about robustness.
`UV = c(VU)` forces `c^n = 1` by determinants, so for `c` not a root of unity the
exact locus is empty at every dimension — one line, no rigidity — while the
relation is exactly solvable at every root-of-unity dimension by the clock-and-
shift pair, which is itself monomial.  Emptiness of every exact locus carries no
dimension-free gap.

## What is not here

No resolution of Question 3.4, and no claim toward one.  The development shows
where the two classes part company and prices the gap; it does not close it.
The two live alternatives are the ones everybody has: a fixed finite window with
a dimension-free gap, or arbitrarily accurate models on every window.
