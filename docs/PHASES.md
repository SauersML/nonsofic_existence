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
roots of unity of order at most four.  The bound is near-optimal: the true
minimum is `(√5 − 1)/4 ≈ 0.30902`, attained where the second and third
Chebyshev polynomials cross at `Re ζ = -φ/2` for `φ` the golden ratio, the
crossing being exact because `4x³ - 2x² - 3x + 1 = 0` follows from
`φ² = φ + 1` (`re_pow_max_sharp`).

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

That last clause is no longer prose.  `DivisibleInvisible.lean` builds `ℤ[1/p]`
as an additive subgroup of `ℚ` (in the multiplicative form `p^N q ∈ ℤ`, so no
division appears), proves the Prüfer group `ℤ(p^∞) = ℤ[1/p]/ℤ` divisible, and
concludes that every homomorphism from it to a finite group is zero
(`prufer_map_eq_zero`) — with `pruferSubgroup_nontrivial` so the conclusion is
not vacuous.  `ℤ[1/p]` itself is *not* divisible; the divisibility is a property
of the quotient, and it needs exactly two moves: division by `p` is exact and
stays inside (`invPowSubgroup_div_p`), division by anything prime to `p` works
only modulo `ℤ` and is Bézout (`invPowSubgroup_div_coprime`).  Strong induction
on `n`, peeling `p`-factors, assembles them.

Two inequalities measure the distance to soficity, pulling opposite ways:

    2 d_Hamm(σ, τ) ≤ ‖A(d,σ) − A(e,τ)‖²      the permutation part inherits
                                              the whole multiplicative defect
    |τ(A(d,σ))|² ≤ (1 − d_Hamm(σ, 1))²        the trace is bounded by the
                                              fixed-point fraction

It is tempting to conclude that a monomial model is a sofic model exactly when
its permutations are already almost fixed-point free, so that cancellation is
worthless.  **That is false** — see §6e.  What the untwisted model needs is
scarcity of points that are fixed *and trivially phased*, so a phase that never
vanishes on `Fix(σ)` untwists to a fixed-point-free permutation however little
`σ` moves.  What decides the matter is the torsion of the phase, not how much
the permutation moves (`monomial_normTrace_zero_of_identity` is the order-two
case, where cancellation is indeed worthless).

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

`CharacterCount.lean` makes the graded version exact.  A projective model
assembled from *all* the characters of `ℤ/n` untwists with defect

    1 − gcd(n, α)/n

(`hammingDistance_characterUntwist`), because `β_l` kills `α` exactly when
`lα = 0`, and the annihilator of `α` has exactly `gcd(n, α)` elements
(`card_annihilator` — the map `l ↦ lα` has image of order `n/gcd`, so Lagrange
gives the kernel).  The two ends of that formula are the two readings: a datum
invisible to almost every character costs almost nothing, and a datum that
*generates* costs `1 − 1/n` (`hammingDistance_characterUntwist_generator`).
Thom's microstates at level `p^k` are the generating case, so untwisting them
destroys the model as `k` grows.  The obvious passage from his projective
microstates to a sofic approximation fails, with a computed defect.

The same file records why exact infeasibility proves nothing about robustness.
`UV = c(VU)` forces `c^n = 1` by determinants, so for `c` not a root of unity the
exact locus is empty at every dimension — one line, no rigidity — while the
relation is exactly solvable at every root-of-unity dimension by the clock-and-
shift pair, which is itself monomial.  Emptiness of every exact locus carries no
dimension-free gap.

## 6a. Why refining the rounding does not help

`NoRounding.lean`.  Section 5 leaves the gap as "combinatorial agreement versus
metric agreement."  The obvious way to cross it is to round each phase to a
nearby `m`-th root of unity.  That strategy does not exist, and the two horns
are exhaustive because a pointwise rule either respects the group law or does
not.

*Multiplicative rounding is trivial.*  The circle is divisible and `ℤ/m` is
finite, so every homomorphism between them is zero (`circle_map_eq_zero`) — the
argument of section 4 applied one level up, to the group the phases live in
rather than the group being modelled.  So a multiplicative rounding sends every
phase to `1`, and its separation is exactly `0` for every pair of phase systems
and every permutation part (`additiveRounding_no_separation`).

*Nearest-point rounding is not multiplicative*, at every `m` and however fine
(`roundMod_not_additive`).  The witness is uniform in `m`: `3/10m` rounds down
to `0` while its double rounds up to `1/m`.  Refining does not help because the
failure is scale-invariant — it is the non-additivity of the sawtooth
`x ↦ round(x) − x`, and rounding to `μ_m` is that sawtooth at scale `1/m`.

So the passage from a metric phase system to a combinatorial one, if it exists,
must use the group being modelled and the model itself.  Same shape as section
1: not a difficulty in carrying out a strategy, but a proof that the strategy
does not exist.

## 6b. The non-pointwise correction, and where it stops

`PhaseCorrection.lean`.  Section 6a leaves exactly one thing open: a correction
chosen with the whole group in view.  Carrying it out gives a sharp dichotomy.

The defect of a phase system `d` is the twisted 2-cocycle
`c(g,h) = g·d_h + d_g − d_gh`, and replacing `d` by `d + b` moves `c` by the
coboundary of `b`.  A cocycle with values uniformly near `0` *is* the coboundary
of something near `0`, and the correction is an average over the group:

    b_g = (1/|G|) Σ_{k ∈ G} c(g,k),   c = δb,   ‖b‖ ≤ ‖c‖

(`phaseCorrection_eq`, `abs_phaseCorrection_le`).  Summing the cocycle identity
over `k` and reindexing `k ↦ hk` is the whole proof.  Two steps make it work and
neither is pointwise: the average is over `G`, and the passage from the circle
to `ℝ` is a lifting — a cochain satisfying the identity only *modulo* `ℤ`, with
values within `1/6` of `0`, satisfies it exactly, because the identity has four
terms and `4/6 < 1` (`isPhaseCocycle_of_mod`).

So (`phase_correctable_of_small`): **no obstruction to soficity can come from a
uniformly small phase defect.**  It is correctable outright, by a correction no
larger than itself.  An obstruction has to be a defect that is small *on average
over the model* and large somewhere — exactly what the Hilbert–Schmidt metric
permits and the Hamming metric does not, and exactly the gap of section 6.  The
scalar witness there is the extreme instance: uniformly maximal rather than
uniformly small.

There is a second failure mode, independent of the first.  The average runs over
all of `G`, so for an infinite group one can only average over a finite window
`F` — and then the reindexing `k ↦ hk`, the single step that made the proof
work, no longer maps the window to itself.  What that costs is *exactly* the
boundary:

    c(g,h) − δb(g,h) = (1/|F|) ( Σ_{hF \ F} c(g,·) − Σ_{F \ hF} c(g,·) )

(`window_defect_eq`), so `‖c − δb‖ ≤ ‖c‖ · |hF △ F| / |F|`
(`abs_window_defect_le`).  The correction therefore survives to an infinite
group exactly when almost invariant windows exist — exactly for amenable
groups, which are sofic already.  The route recovers what is known and stalls
precisely at non-amenability, and the stalling is a named quantity.

Read with 6a this locates the difficulty along two independent axes.  Pointwise rules cannot work at all;
the group-averaged rule works whenever the defect is uniform *and* the window is
almost invariant; so whatever separates the two classes, if anything does, lives
in the failure of one of those — in defects concentrated on a small part of the
model, or in the non-amenability of the group.

## 6c. Where the obstruction lives: bounded cohomology

`ScalarClass.lean`.  Sections 6a–6b fence the problem but do not say what the
correction has to kill.  Averaging in the *other* direction says it.  Average
the defect over the model rather than the group:

    ĉ(g,h) = (1/|Y|) Σ_{y ∈ Y} c(g,h)(y)

Two things happen at once.  The action disappears — it enters the cocycle
identity only as a relabelling of `Y`, and an average over `Y` cannot see a
relabelling — so the *twisted* identity becomes the *untwisted* one
(`isScalarCocycle_scalarPart`).  And the bound survives, `‖ĉ‖ ≤ ‖c‖`
(`abs_scalarPart_le`).  So the average of a small twisted defect is a **bounded
2-cocycle on `G` with trivial coefficients**.

Averaging commutes with correcting (`scalarPart_phaseCob`): the scalar part of a
coboundary is the coboundary of the scalar part, with `‖β‖ ≤ ‖b‖`.  Contraposed
(`scalarClass_obstructs`): *if the bounded class of `ĉ` does not vanish, no
bounded correction of `c` exists at all.*  The scalar obstruction lives in
`H²_b(G, ℝ)`.

This names the difficulty rather than adding one.  Bounded cohomology vanishes
for amenable groups and not in general; the correction of 6b succeeds exactly
when the window is almost invariant; the two are the same fact, and the Følner
boundary is the averaging that computes the class.  It also explains why the
scalar witness of section 6 is extreme: a constant defect *is* its own scalar
part, with no mean-zero component at all.

What is missing is a group whose class is non-vanishing *and* forced on every
model.  Soficity quantifies over finite windows; a bounded class is global; any
single window can be corrected by extending the correction arbitrarily.  An
obstruction would have to be uniform over windows — the same dimension-free gap
section 6 shows exact infeasibility does not supply.

## 6d. Rounding a character, where rounding a circle failed

`RationalCharacter.lean`.  Section 6a invites a misreading worth correcting.
That no pointwise rule turns circle-valued phases into `μ_m`-valued ones does
*not* mean the `μ_m` restriction in the criterion of section 5 is an obstacle.
The failure in 6a is a failure of **freeness**, not of fineness.  A homomorphism
out of the circle is pinned down everywhere by divisibility; a homomorphism out
of a free abelian group is pinned down by nothing — its values on a basis are
arbitrary and any choice extends.

Once the phases are exactly multiplicative — which is what a correction buys —
their values on a finite window form a character of a finitely generated free
abelian group, and that *can* be rounded multiplicatively and to finite order.
Replacing each `aᵢ` by `round(q aᵢ)/q` gives a character with values in
`(1/q)ℤ`, still a homomorphism on the nose (`ratChar_add`, `ratChar_eq_div`),
agreeing with the original to within `(Σ|nᵢ|)/(2q)`.  On coefficients bounded by
`N` — which a finite window over a finite model supplies — taking `q` large
makes this as tight as one likes (`exists_ratChar_close`).

So the `ℝ/ℤ` versus `μ_m` distinction is not where the difficulty lives.  What
remains hard is 6b–6c, obtaining exact multiplicativity at all, and the
separation of the untwisted model, which no rounding addresses.  The pair 6a/6d
is sharp: rounding fails on the circle because the circle is divisible, and
succeeds on a lattice because a lattice is free.

## 6e. The other half: untwisting cannot manufacture separation

`UntwistSeparation.lean`.  Everything in 6b–6d is about *multiplicativity*.
None of it touches the other half of a sofic model — **separation**, that a
nontrivial element move almost every point.  Here the news is negative and
quantitative.

The fixed points of the untwisted permutation of `(d,σ)` are the `(y,j)` with
`σy = y` and `d y = 0`, so untwisting separates only insofar as the phase avoids
`0` on `Fix(σ)`.  But `Fix(σ)` is partitioned by the `m` classes of `d`, so some
class carries at least an average share (`exists_shift_fixed_ge`).  Renormalizing
by that `c` is a *scalar* change — invisible to Hilbert–Schmidt by section 6 —
and leaves an untwisted model of separation at most `1 − F/m`, where `F` is the
fixed-point density of `σ` (`exists_shift_hamming_le`).

So for any single element, some scalar shift retains a `1/m` share of its fixed
points.  That is a statement about one element's phase function, and it must not
be over-read.  A shift is invisible to Hilbert–Schmidt, which suggests the metric
cannot rule out a bad normalization; but a renormalization of a whole *model*,
`d_g ↦ d_g + β(g)`, has to preserve multiplicativity, and subtracting the two
multiplicativity identities gives `β(gh) = β(g) + β(h)`
(`renormalization_isHom`).

The renormalization freedom is therefore `Hom(G, ℤ/m)`, not one free constant per
element.  Being a homomorphism to an abelian group, `β` kills commutators
(`renormalization_commutator`), so on a group in which every element is a
commutator the only renormalization is trivial
(`renormalization_eq_zero_of_commutators`) and the phase system *does* determine
the untwisted separation.  The `c` from the pigeonhole is a genuine scalar for
its element but is not in general available as a renormalization of the model.

The same argument says something sharper about the phases themselves.  Nothing
in it used that `β` came from a renormalization — only that it turned products
into sums.  At a point `y` fixed by *every* element, the phase function
`g ↦ d_g(y)` is exactly that, since the action never moves `y` out of the way
(`phase_isHom_at_global_fixed`).  So on a group where every element is a
commutator the phase vanishes identically there
(`phase_eq_zero_at_global_fixed`); the point is trivially phased for every
element, survives untwisting in every fibre (`wreathPerm_fixes`), and the
untwisted model retains it whatever the phases are.

**Phases are powerless at a globally fixed point of a perfect group.**  That is
the reverse of what the witnesses suggest — there a well-chosen phase removed
every fixed point, but that model lived on a group with no perfection to
exploit.

That statement quantifies over the whole group, and a model has no whole group —
only a finite window and an approximate action, hence no genuine stabilizer
subgroup.  The argument survives anyway, because it is **local**.  To kill the
phase of `[a,b]` at `y` one needs only `σ_b y = y`, `σ_{a⁻¹} y = y`,
`σ_{b⁻¹} y = y`; then `d_ab(y) = d_a(y) + d_b(y)`, `d_{a⁻¹}(y) = −d_a(y)`,
`d_{b⁻¹}(y) = −d_b(y)` cancel in pairs (`phase_commutator_local`, with
`phase_one_eq_zero` and `phase_inv`).

Perfection of `G` is not used, no closure of the window beyond naming the
elements is used, and — slightly surprisingly — `σ_a` need not fix `y` at all:
three of the four constituents suffice.  So in *any* monomial model, at any point
fixed by `b`, `a⁻¹`, `b⁻¹`, the commutator `[a,b]` is trivially phased and the
point survives untwisting.  On a group whose elements are commutators, that is
about exactly the elements one has to separate.

The counting it needs is Bonferroni, and it simplifies: a permutation and its
inverse have the same fixed points (`fixed_inv_iff`), so a point fixed by
`b, a⁻¹, b⁻¹` is just a point fixed by `a` and by `b`, and there are at least
`F_a + F_b − 1` of them (`card_inter_fixed_ge`).  Every such point is fixed by
`[a,b]` and trivially phased there, hence survives untwisting in every fibre:

    d_Hamm(untwist(d_[a,b], σ_[a,b]), 1) ≤ 2 − F_a − F_b

(`untwist_retains_commutator`).  Read the other way: if the untwisted model
separates `[a,b]` to within `ε`, then `F_a + F_b ≤ 1 + ε` — **at most one
element of the window can fix more than half the model**.

That is the quantitative form of "untwisting only inherits separation", stated
in the permutation parts alone with the phases eliminated.  The one hypothesis a
genuinely approximate model does not supply for free is that `σ` is a
homomorphism, and it is worth saying what that costs.  Linearly, with constant
one: if the identities used hold off a set `B`, then

    d_Hamm(untwist(d_[a,b], σ_[a,b]), 1) ≤ 2 − F_a − F_b + |B|/|Y|

(`untwist_retains_commutator_offBad`), and `B = ∅` is the exact statement.  The
two ingredients separate cleanly and each is useful alone: a set of points that
are fixed and trivially phased caps the untwisted separation at `1` minus its
density (`untwist_hamming_le_of_good_set`), and Bonferroni with an exceptional
set counts them (`card_inter_sdiff_ge`).  So the argument does not degrade badly
under approximation — the exceptional density enters once, undamped.

The two bounds can now be chained, and the result assumes nothing about
untwisting.  The commutator argument bounds the trivially phased fixed points of
`[a,b]` from *below*; `card_trivially_phased_le` bounds the same set from
*above*.  Together (`card_fixed_commutator_constraint`):

    2(F_a + F_b − 1 − |B|/|Y|)  ≤  F_[a,b] + ε

with `ε` bounding the trace at `[a,b]`.  This constrains the permutation parts
of **any** monomial model whose trace at `[a,b]` is small — exactly what
hyperlinearity supplies — with the phases eliminated and no separation assumed.
Since `F_[a,b] ≤ 1` it gives `F_a + F_b ≤ 3/2 + ε/2 + |B|/|Y|` outright.

The witnesses do not violate it; they saturate it.  There every permutation part
is the identity, so `[a,b] = 1`, its trace is `1`, and the inequality reads
`2(1 + 1 − 1) = 2 = 1 + 1` exactly.

It is not obvious that hyperlinearity ever makes `F_a`, `F_b` large — separation
bounds `Re τ`, not `F`.  But `normSq_normTrace_monomial_le` bounds the trace by
the fixed-point fraction, `|τ(A_g)| ≤ F_g` (`sqrt_normSq_normTrace_le`), and a
trace can have large *modulus* while its real part is small: exactly the
near-scalar case `τ ≈ −1` or `τ ≈ ±i` that maximises Hilbert–Schmidt separation.
Chaining (`fixedDensity_sum_le_of_commutator`):

    |τ(A_a)| + |τ(A_b)| ≤ 3/2 + ε/2 + |B|/|Y|

so **two elements cannot both lie within `3/4` of the scalars unless their
commutator fails to separate**.  That is the general form of the two-involution
statement of §3: what obstructs is not the order two but the non-commuting.

The inequality reads better the other way round, as a lower bound on the
commutator's trace (`re_normTrace_commutator_ge`):

    Re τ(A_[a,b]) ≥ 2 F_a + 2 F_b − 3 − 2|B|/|Y|

If two elements are both near the scalars — `|τ_a|, |τ_b| ≈ 1`, hence
`F_a, F_b ≈ 1` — the right side is `≈ 1`, so `A_[a,b]` is as close to the
identity as Hilbert–Schmidt can report.  **Near-scalar elements have
near-trivial commutators.**

So the near-scalar elements of a monomial model form an approximately abelian
set.  That is the structural reason the scalars in a construction like Thom's
live in the *centre*: not a design choice but the only place a model can put
them.

One caution.  The chain now carries a compatibility hypothesis, a goodness
hypothesis and a trace hypothesis at once, and a theorem whose hypotheses cannot
all hold is vacuously true and caught by nothing — `UNWITNESSED` guards
`Prop`-valued *definitions* nothing satisfies, not hypothesis sets nothing
satisfies.  So `card_fixed_commutator_constraint_tight` exhibits an instance
where all three hold simultaneously — two points, trivial action, trivial
phases — and there the inequality is an **equality**, both sides `4`.  The chain
is neither vacuous nor lossy at its extreme.

### Scope

Every result in §§6a–6e is about **monomial** models.  That is the right class
for the sofic side — soficity *is* combinatorial monomial approximability (§5) —
but not for the hyperlinear side, which supplies arbitrary unitaries.  The
monomial matrices are a proper subgroup of `U(n)`, and not merely proper: the
two-point Hadamard matrix is unitary and sits at normalized Hilbert–Schmidt
distance at least `1/4` from *every* monomial matrix
(`exists_unitary_far_from_monomial`), so it cannot be approximated by monomial
data either.  
That statement is in a **fixed basis**, and the qualification matters: by the
spectral theorem every single unitary is diagonal in some basis, hence monomial
there.  So the witness does *not* show a model resists being conjugated into
monomial form.  What it shows is that the monomial matrices are metrically
isolated inside `U(n)` for a fixed indexing — which is what the phase results
assume, and so the right statement for bounding them, but not an obstruction to
monomialization.

The genuine question is whether a whole *family* `{U_g}` can be simultaneously
monomialized, and that is open here.  The seed of an obstruction:
`monomialMatrix_one_comm` — monomial matrices with trivial permutation part are
diagonal and commute, so two non-commuting unitaries are never simultaneously
diagonal.  Permutation parts give the monomial group more room, but the real
obstruction is available and is **basis-free**.

The permutation part of a monomial matrix is multiplicative
(`monomialMatrix_mul`), so a monomial matrix raised to `|Sym(Y)| = n!` has
trivial permutation part and is *diagonal*
(`monomialMatrix_pow_card_diagonal`); diagonal matrices commute, whence

    U, V monomial in a common basis  ⟹  U^{n!} V^{n!} = V^{n!} U^{n!}

(`monomialMatrix_pow_card_comm`).  Both hypothesis and conclusion are
conjugation-invariant, so two unitaries whose `n!`-th powers fail to commute
cannot be simultaneously monomialized in *any* basis.  That is what the
single-matrix witness could not supply, a lone unitary being diagonal in its own
eigenbasis.  The exponent `n!` is the crude bound `|Sym(Y)|`; the exponent of
`Sym(Y)` would serve.

**What it does not give.**  One would like to lift this to groups: if
`[g^N, h^N] ≠ 1` for every `N`, must a monomial model fail?  It does not follow.
`n!` is the size of `Sym(Y)`, so it grows with the *model*, while a window is
fixed before the model is chosen — reaching `U_{g^{n!}}` from `U_g` would need
`n!` multiplications inside the window.

Worse for the hope, the criterion is **vacuous** on the side one would want it to
decide: a sofic model is a permutation model, and a permutation matrix raised to
`|Sym(Y)|` is the identity (`permMonomial_pow_card`), so its `n!`-th powers
commute for free.  The criterion separates monomial from general unitary
matrices — which is what the scope claim needs — and says nothing about whether a
group is sofic.

## 6f. Where hyperlinearity does force soficity

Every separation result in §6e is negative for one reason: the trace bounds
`|τ| ≤ F` the wrong way round, so a small trace never forces the fixed-point
density down.  There is one situation where it does, available since the coprime
vanishing without being assembled.

If the phase is *trivial on the fixed points* — which `gcd(n,m) = 1` forces —
no cancellation is available there, and the trace is not merely bounded by the
fixed-point density but **equal** to it:

    τ(A(d,σ)) = F_σ

a nonnegative real (`normTrace_monomial_of_phase_trivial`).  Hyperlinear
separation says `Re τ ≤ ε`, and that is now a bound on `F` itself
(`fixedDensity_le_of_trace_le`).  Untwisting returns a model separated to within
`ε` (`untwist_separated_of_phase_trivial`).

So on a window where every element's order is prime to the modulus, a monomial
hyperlinear model **is** a sofic model, with no loss.  The hypothesis is strong —
it is exactly the regime where the phases were shown powerless, so the model was
never projective in any useful sense — but it is the one place in this
development where the implication runs in the direction Question 3.4 asks
about.

**The exact boundary.**  The trivial-phase hypothesis is more than the argument
needs.  What it used is only that the phases at fixed points cannot cancel — a
condition on their real parts.  If every such phase has real part at least
`c > 0` (the phases lie in the open arc of half-angle `< π/2` about `1`), then
`Re τ ≥ c · F_σ`, so hyperlinear separation gives

    F_σ ≤ ε / c

outright (`fixedDensity_le_of_re_pos`).  Trivial phases are `c = 1`.

Once the phases reach the imaginary axis, cancellation begins and the trace
stops seeing `F` at all: the `±i` witness sits precisely there, with `c = 0`,
trace zero and `F = 1`.  So the positive direction holds exactly as far as the
phases stay off the imaginary axis, and fails immediately after.

The two halves were proved far apart and were not aimed at each other, so
`hyperlinear_forces_sofic_iff_phases_off_axis` records them as one object.  The
trace is linked to the fixed-point density only through `|τ| ≤ F`, which runs
the wrong way; a trace bound can constrain `F` at all only when the phases fail
to cancel, and the condition for that is a positive lower bound on their real
parts.  Above the threshold hyperlinearity forces soficity, with `F ≤ ε/c`; at
it, it does not, and the failure is realized by a model of trace zero in which
*every* point is fixed.

So a group could be hyperlinear through models nowhere near monomial, and none
of these results would apply.  What justifies the restriction in the one case
where it is justified is external — Thom's microstates are monomial because
every finite-dimensional unitary representation of `K` kills its divisible
centre (§4) — not anything proved in §§6a–6e.

The extreme case needs no pigeonhole (`untwist_separation_undetermined`).  On
the *same* `σ`, constant phase `1` untwists to separation exactly `1`; constant
phase `0` untwists to exactly `1 − F`.  The two monomial matrices differ by a
scalar, so they sit at Hilbert–Schmidt distance `|1 − ζ|² → 0`.  Two models
arbitrarily close in the metric hyperlinearity uses have untwisted separations
`1` and `1 − F` for any `F`.

For a **torsion** element the scalar freedom disappears and what is left is
stronger.  The phases restrict to a homomorphism on the stabilizer of a point —
if `σ_g y = y` and `σ_h y = y` then `d_gh(y) = d_g(y) + d_h(y)`, since `σ_h`
does not move `y` (`phase_double_at_fixed`).  So for an involution the value
`d_g(y)` is pinned to the 2-torsion of `ℤ/m` at every fixed point
(`phase_two_torsion`), takes at most two values there, and the two contribute
opposite signs to the trace.  A trace bound `E` then *forces* the classes to be
balanced rather than merely permitting it, giving

    d_Hamm(untwist(d_g, σ_g), 1) ≤ 1 − (F − E/|Y|)/2

(`involution_untwist_hamming_le`) with no normalization chosen anywhere.
Untwisting an involution inherits its separation and halves it; it cannot create
it.  That is why involutions keep reappearing as the obstruction.

The involution is the case `n = 2` of something general, and the general case
says **when phases can help at all**.  Iterating the stabilizer homomorphism
gives `d_{g^k}(y) = k · d_g(y)` at a point fixed by `g`
(`phase_iterate_at_fixed`), so an element of order `n` has `n · d_g(y) = 0`:
the phase lies in the `n`-torsion of `ℤ/m`, a subgroup of `gcd(n,m)` elements.
When `gcd(n,m) = 1` that subgroup is trivial and the phase is *forced to vanish*
on the whole fixed-point set (`phase_eq_zero_of_coprime`).  Cancellation is then
not merely unhelpful but unavailable: the trace is exactly `F`, the untwisted
separation is exactly `1 − F` (`coprime_untwist_hamming`), and a trace bound
*is* a separation bound.

So phases can help only when the modulus shares a factor with the torsion —
which is exactly what a construction like Thom's arranges, `p`-power phases
against a `p`-power centre, and it explains why the character count of section 6
is indexed by the `p`-power torsion rather than by anything freely chosen.

There is also a bound the other way, at every order, and it is what makes the
involution extremal.  A trivially phased fixed point contributes `+1` to the
trace and every other fixed point at least `-1`, since the phases are
unimodular, so a trace bound `ε` is a *counting* bound:

    #{y : σy = y, d y = 1} ≤ (#Fix(σ) + ε|Y|)/2

(`card_trivially_phased_le`), with no hypothesis on the torsion at all.
Untwisting always removes at least half the fixed points; an involution removes
exactly half; the two bounds meet, so the involution is the worst case rather
than merely a bad one.

The order-four case shows this is about torsion, not about how much the
permutation moves.  Take the same two-point model with the identity permutation
— the *least* separated permutation part possible — and phases `±i` rather than
`±1`.  The trace is again `0`, but the phase never vanishes, so the untwisted
permutation is fixed-point free and the model is maximally separated
(`untwist_full_separation_witness`).  With `±1` it keeps half its points fixed,
attaining the involution bound (`untwist_half_separation_witness`).
Cancellation buys nothing at order two and everything at order four, and the two
witnesses differ in nothing else.

Order three forces retention too — of a third rather than a half
(`card_zero_class_ge_three`).  The cube roots of unity are *positively*
dependent: `1 + ω + ω² = 0` is their only relation over `ℝ`, so a nonnegative
combination is small only when all three coefficients are nearly equal.  Writing
`a = n₀ − n₂`, `b = n₁ − n₂`, the relation gives `n₀ + n₁ω + n₂ω² = a + bω`,
whose squared modulus is the positive definite form `a² − ab + b² ≥ (a²+b²)/2`
(`normSq_cubeRoot_comb`); a trace bound `E` forces `|a|,|b| ≤ √2·E` and hence
`n₀ + n₁ + n₂ ≤ 3n₀ + 3√2·E`.

At order four that single relation splits into two independent ones,
`1 + (−1) = 0` and `i + (−i) = 0`, and a nonnegative combination can vanish while
missing the class of `1` entirely — which is the witness above.  **The
trichotomy is complete**: orders two and three force retention of `1/2` and
`1/3`; order four and beyond force nothing.

The order is not quite the right invariant.  What the phase of an order-`n`
element can do at a point it fixes is decided by the subgroup of `ℤ/m` it is
pinned to — the `n`-torsion — and that subgroup has exactly `gcd(m,n)` elements
(`card_torsion_subgroup`, the annihilator count of §6 with its arguments
exchanged).  So the classification is really in `gcd(n,m)`: `1` forces the phase
to vanish, `2` retains a half, `3` retains a third, `≥ 4` forces nothing.

That is not a relabelling.  An involution against an **odd** modulus has
`gcd(2,m) = 1`, so its phase is forced to vanish on its fixed points exactly as
a coprime element's is (`phase_eq_zero_of_gcd_eq_one`), and untwisting gains
nothing — although the element has order two and the involution bound would
predict a half.  The gcd is what the phase sees; the two part company exactly
when the modulus is chosen incompatibly with the torsion.

The `gcd ≥ 4` side is an infinite family, not one accident at `4`.  At any even
modulus, if `ζ^{m/2} = -1` then `ζ¹ + ζ^{1+m/2} = ζ(1 + ζ^{m/2}) = 0`
(`phase_pair_cancels`), so two classes with equal weights cancel while *neither*
is trivial; the two-point model with the identity permutation and phases `ζ, −ζ`
has trace `0` and untwists fixed-point free, for every even `m ≥ 4`
(`untwist_full_separation_witness_even`).  The `±i` witness is the case `m = 4`.
The odd moduli need unequal weights, and that is not an artifact: for **prime**
`m` the numbers `1, ζ, …, ζ^{m-1}` satisfy only the rational relation
`Σ ζ^k = 0`, which involves the trivial class, so no rational nonnegative
combination of the nontrivial classes can vanish.  The irrational weights are
easy to write down (`phase_weights_cancel`): weight the two classes adjacent to
the trivial one by `1 + 1/(2 Re ζ)` and every other nontrivial class by `1`.
Since `Σ_{k=1}^{m-1} ζ^k = -1` (`geom_nontrivial_sum`) and
`ζ + ζ^{m-1} = 2 Re ζ` (`adjacent_pair_sum`), the total is `-1 + 1 = 0`, and all
weights are positive exactly when `Re ζ > 0` — for `ζ = e^{2πi/m}`, when
`m ≥ 5`.

With the even family this settles `gcd ≥ 4` at every modulus: the trivial class
can always be missed.

**The metric data does not determine the untwisted separation.**  That is the
separation-side counterpart of section 6, and it says why none of the correction
machinery bears on this half: the difficulty is not that phases are hard to make
multiplicative — they are not — but that multiplicativity and separation are
controlled by different data, and the metric supplies only the first.

## 7. Contributed by an external audit, formalized here

`ImplementerCocycle.lean`, `CoordinateTransfer.lean`.  Three statements arrived
from a referee audit of this development as prose; they are formalized because
that is the form in which they should travel.

*Implementer coherence is a cocycle problem.*  Implementing an action
elementwise is not the same as having a representation: the defect
`c(g,h) = v_g v_h v_{gh}⁻¹` satisfies a twisted `2`-cocycle identity, and
correcting the implementers moves `c` by a coboundary.  Both are group
identities and are stated at that level.

*Normalized rank blindness.*  Two orthogonal rank-one projections on a model of
size `n` are at normalized squared distance `2/n`.  Any argument tracking a
distinguished vector must first bound the relative trace of its support.

*Coordinate reverse transfer.*  Encoding a coordinate `x` as the lamp
`δ_x(k₀)` is injective and equivariant, so chart data for the lamp action pulls
back to chart data for the coordinate action — with nothing used about where
the charts take their values.  The two hypotheses are isolated as hypotheses
(`lampEmbedding_injective`, `lampEmbedding_equivariant`); the transfer itself
(`OrbitChartData.comap`) is a pullback.  The reading is the audit's: if the
coordinate action admits no chart system, neither does the lamp action.

## 6g. The root: centres

`UntwistSeparation.lean`.  Everything above about phases traces back to one
contrast between the two groups the two notions approximate.

`U(Y)` has a central element at **maximal** distance from the identity: `−1` is
scalar, commutes with every unitary, and `hsDistSq(−1, 1) = 4`
(`exists_central_unitary_separated`).  `Sym(Y)` has no nontrivial central
element at all once `|Y| ≥ 3` — a permutation commuting with every other is the
identity, at Hamming distance `0` (`eq_one_of_central_perm`; Mathlib has no
`Perm` centre lemma, so this is the transposition argument: if `σx = y ≠ x`,
compare `σ` with `swap y z` at `x` for a third point `z`).

So the unitary group can separate a central element and the symmetric group
cannot.  That is why a hyperlinear model may place a central group element at a
scalar — and be maximally separated there — while a sofic model has nowhere to
put it.  Every phase phenomenon in §§1–6f is downstream of this one asymmetry.

**But it is not itself an obstruction**, and seeing why matters — otherwise the
asymmetry looks like it should settle the question.  A model's image need not be
all of `Sym(Y)`, and a permutation commuting with a *transitive* set is
semiregular: if it fixes one point it fixes all
(`eq_one_of_fixed_of_commutes_transitive`).  So in a transitive model a
nontrivial element commuting with the image moves *every* point and is
maximally separated (`hammingDistance_eq_one_of_commutes_transitive`).

That is the resolution.  A hyperlinear model separates a central element by
putting it at a scalar; a sofic model separates it by making it act freely.  The
asymmetry between the centres is real and drives everything above, and it is
still not by itself an obstruction — which is consistent with Question 3.4 being
open rather than easy in either direction.

Stated where the question actually lives — soficity and hyperlinearity are
embeddability into `∏_𝒰 Sym` and `∏_𝒰 U` — the asymmetry says the universal
hyperlinear group has a nontrivial central element.  The constant sequence `−1`
is unitary, central in each factor (`negOne_central`), and not null, since
`hsLengthSq(−1) = 4` at every index (`not_isNullUnitarySeq_negOne`); so its class
is central and nontrivial — both halves proved, in
`exists_nontrivial_center_universalHyperlinear`.  The corresponding statement for `∏_𝒰 Sym` fails, by
`eq_one_of_central_perm`.  That is the reason the two ultraproducts are not
obviously the same object — and, by the semiregularity above, not a reason they
differ.

## Where this ends

No resolution of Question 3.4, and no claim toward one.  What follows is the
position the sections above actually reach, and the routes they close, so that
neither has to be reconstructed.

**The root** (§6g).  `U(Y)` has a central element at maximal distance from the
identity (`−1`, scalar, `hsDistSq = 4`); `Sym(Y)` has no nontrivial central
element at all for `|Y| ≥ 3`.  Every phase phenomenon here is downstream of that
one asymmetry.  It is *not* itself an obstruction: a permutation commuting with
a transitive set is semiregular, so a sofic model separates a central element by
making it act freely where a hyperlinear model uses a scalar.

**The central finding** (§6f, `hyperlinear_forces_sofic_iff_phases_off_axis`).
Hyperlinearity forces soficity *exactly* as far as the model's phases stay off
the imaginary axis at fixed points.  Above the threshold, `F ≤ ε/c`; at it, a
model with trace zero and every point fixed.  The reason there is no third
option: the trace sees the fixed-point density only through `|τ| ≤ F`, which
runs the wrong way, so a trace bound constrains `F` only when the phases cannot
cancel — and that condition *is* the threshold.

**The scope** (§6e).  All of §§6a–6f is about monomial models.  That is exactly
right for the sofic side (§5) and a proper restriction on the hyperlinear side:
monomial matrices are a subgroup of `U(n)`, and a family escapes it whenever its
`n!`-th powers fail to commute (`monomialMatrix_pow_card_comm`, basis-free).
Thom's microstates are monomial for an external reason (§4), not one proved
here.

**Routes closed, with the reason:**

| route | why it fails |
|---|---|
| tensor amplification | a scalar enters as its `k`-th power (§1) |
| pointwise rounding of phases | multiplicative ⇒ trivial; nearest-point ⇒ not multiplicative (§6a) |
| group-averaged correction | needs almost invariant windows, i.e. amenability (§6b) |
| untwisting Thom's microstates | defect `1 − p^{-k}`, computed (§6) |
| `ℝ/ℤ` vs `μ_m` | not an obstacle; freeness makes rounding work on a lattice (§6d) |
| untwisting to gain separation | can only inherit it; halves at best (§6e) |
| `n!`-power criterion → group statement | exponent grows with the model, window is fixed; and vacuous on permutation models (§6e) |
| centre asymmetry as an obstruction | centralizers of transitive sets are semiregular, so sofic models separate central elements too (§6g) |

**The group side** (`HeisenbergCentre.lean`, started at the end of this work).
`Heis R = R³` with `(a,b,c)(a',b',c') = (a+a', b+b', c+c'+ab')` has centre
exactly `(R,+)`; `ℤ[1/p]` is a subring of `ℚ`; and every homomorphism from
`Heis(ℤ[1/p])/ℤ` to a finite group kills the central image
(`heis_centre_map_eq_one`) — the Prüfer mechanism of §4 in a group built rather
than quoted.  That group is **not** residually finite; it fails to be a
candidate because it is 2-step nilpotent, hence amenable, hence sofic.

**The candidate profile.**  A nontrivial divisible subgroup obstructs residual
finiteness outright (`map_eq_one_of_mem_divisible_subgroup`), so that clause is
cheap; the non-split clause the Heisenberg construction also supplies, its
centre being generated by commutators.  The expensive clause is
**non-amenability**.  Whether Kazhdan's property is *needed* for it — as opposed
to being what Cornulier's separate application required — is open.

**What the gap is not.**  It is not a search for an exotic group.  Every clause
of the profile is met by many constructions — take any non-amenable residually
finite `Q` with `H²(Q, ℤ[1/p]) ≠ 0`, form the central extension, quotient by `ℤ`;
a surface group serves.  What is open in each case is the same thing that is open
for `K`: these groups arise as central quotients of groups known to be sofic, and
**whether soficity passes to central quotients is itself unsettled**.  So the
difficulty is not finding a suitable group; it is that no method distinguishes
the sofic ones among them.  Cornulier's group is not special in this respect —
its property (T) was wanted for a different application.  (Not formalized: a
reading of where the difficulty sits.)

**What is missing, precisely.**  Every result here constrains models.  Deciding
Question 3.4 negatively requires showing some particular hyperlinear group
admits *no* sofic model — a statement about the non-existence of models, which
nothing above supplies and which no refinement of this framework will.  The two
live alternatives remain the ones everybody has: a fixed finite window with a
dimension-free gap, or arbitrarily accurate models on every window.
