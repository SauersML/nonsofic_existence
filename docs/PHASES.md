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

So untwisting cannot manufacture separation *robustly*: whatever the phases,
some scalar renormalization retains a `1/m` share, and since scalar
renormalizations are invisible to Hilbert–Schmidt, nothing in the metric data
rules that normalization out.  This does not say every choice of phase is bad —
see the witnesses below — only that the metric cannot certify a good one.

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

## What is not here

No resolution of Question 3.4, and no claim toward one.  The development shows
where the two classes part company and prices the gap; it does not close it.
The two live alternatives are the ones everybody has: a fixed finite window with
a dimension-free gap, or arbitrarily accurate models on every window.
