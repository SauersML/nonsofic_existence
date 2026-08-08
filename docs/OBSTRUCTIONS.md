# The obstruction structure around compression

A map of what is proved about *why* the compression mechanism resists
approximation, and where the open branch actually sits. Every entry marked
**formalized** is kernel-checked in this repository; every other entry is
labelled with its status.

The organizing question throughout is:

> Let `Γ ≤ G` with a compressor `t` (`tΓt⁻¹ ≤ Γ`, strictly). In a model of `G`,
> does the compressed copy differ from `Γ` — does the relative commutant grow?

Everything below answers "no" in some category, or explains why a proposed
category was the wrong one.

## 1. The pattern: one theorem, five instances

**`Criterion/FiniteQuotientBlindness.no_strict_compression_of_invariantSize`**
(formalized). If subgroups carry a *size* that conjugation preserves and that
distinguishes proper inclusions, then a compression is an equality. Two
hypotheses, three lines.

Every collapse in this development is an instance:

| category | size | reference |
| --- | --- | --- |
| finite sets | cardinality | `ExactCompression.fixedSet_image_eq` |
| finite-dimensional spaces | `finrank` | `ExactCompression.fixedSubmodule_map_eq` |
| finite groups | `Nat.card` | `FiniteQuotientBlindness.compressedImage_eq'` |
| compact groups | Haar measure | not formalized; one line, see §4 |
| **`II₁` factors** | **trace** | **fails — see below** |

A `II₁` factor *has* a conjugation-invariant size. It fails the **other**
hypothesis: the trace is additive under refinement, hence preserved by it, hence
blind. That single failure is the whole open branch.

**And the failure is sharp.** Take `R = ⊗_{n∈ℤ}M₂` with the Bernoulli shift `θ`
and `N = ⊗_{n≥0}M₂`; then `θ(N) ⊊ N`, `θ` is properly outer, so `M = R ⋊_θ ℤ`
is a `II₁` factor whose implementing unitary satisfies `uNu* ⊊ N`. So no
conjugation-invariant strictly-monotone size exists there, and **no invariant
argument — index, entropy, or undiscovered — can settle the open branch.** The
obstruction, if there is one, can only be stability.

## 2. Consequences for models

- **`compressedImage_eq`** (formalized). For any `φ` into a finite group,
  `φ(t)` normalizes `φ(Γ)`; since `Γ` and the compressors generate, the image of
  `Γ` is **normal in every finite quotient**. So finite-quotient models cannot
  witness the compression — the data has been quotiented away before the
  construction starts. Specializes to `⟨ā⟩ = ⟨ā²⟩` in every finite quotient of
  `BS(1,2)`. Recorded in the manuscript as `rem:finiteblind`.

- **`commutant_no_growth`** (formalized). For a genuine finite-dimensional
  representation, an endomorphism commuting with `π(tΓt⁻¹)` already commutes
  with `π(Γ)` — obtained by applying the fixed-space collapse to the *adjoint*
  representation, since `π(Γ)′ = Fix(Ad π|_Γ)`. This is the load-bearing step of
  the flexible-stability reduction (§5).

- **`ray_injective`** (formalized). A strict compressor has no power in `Γ`, so
  the ray `t⁻ⁿΓ` is infinite and the `Γ`-fixed set is infinite. The complement
  of the above: finite models fail because a finite fixed set equals its own
  image; the genuine action escapes because strictness forces infinitude.

## 3. Architecture-level no-gos

- **`Sofic/LevelShiftObstruction`** (formalized). A permutation shifting a
  graded set up one level is never compatible on the top level, so it misses at
  least `|S_m|` points; and for levels growing by `k ≥ 2` the top level carries
  more than `(k−1)/k` of the mass, *uniformly in the height*. Tower
  architectures therefore lose `Θ(1)`, which is fatal against exponential
  amplification. **Calibration:** the same count applies to `BS(1,2)` with
  `k = 2`, where the wreath product *is* sofic (amenable) — its models come from
  Følner sets, not a tower. The architecture fails where the conclusion is known
  to hold, so the obstruction is in the shape, not the group.

- **`centralized_mem_iterate`** (formalized) plus tail triviality. If the
  compressor centralizes `F ≤ Γ` then `F ≤ φⁿ(Γ)` for all `n`. For a
  *half-space* tensor construction (`ρ(Γ) ⊆ ⊗_{k≥0}A`, `ρ(t)` the shift), any
  `γ ∈ ⋂ₙφⁿ(Γ)` has `ρ(γ)` in the tail `= ℂ`, contradicting `τ(ρ(γ)) = 0`. A
  monomial substitution fixes the constants, so this always bites for elementary
  groups over monoid rings **with one compressor**.
  *Scope, corrected:* the half-space hypothesis is essential. Splitting off the
  constants (`ev₀ : Γ → SL_r(k)` retracts compressor-equivariantly) puts them on
  the two-sided diagonal, where they are shift-invariant and not in the tail,
  and leaves `⋂_w φ_w(Γ(𝔪)) = 1` for two compressors. The no-go rules out
  half-space towers, not all tensor models.

- **Amplification** (not formalized; see the module docstring). A site defect of
  density `δ` becomes a configuration-space defect of size `1 − 2^{−b}`: one
  mismatched boundary coordinate destroys a model. Combined with the fact that
  `G ↷ G/Γ` has no Følner sets (property (T), infinite index), boundary error is
  never negligible.

- **No commuting branches.** With two compressors, `[e_{ij}(x^v), e_{jk}(x^{v′})]
  = e_{ik}(x^{v+v′}) ≠ 1` for cross-branch `v, v′`. So the two branch algebras
  cannot sit in commuting (tensor) position. *Free* independence is not excluded
  by this.

## 4. Where compression can exist at all

`K₀ = SL_r(𝔽_q[[t]])` is compact open in unimodular `G₀`, so Haar is
conjugation-invariant and `uK₀u⁻¹ ⊆ K₀ ⟹ equality`. Hence `Γ₀ = M ∩ K₀` has
**no strict compressor in `M = SL_r(𝔽_q[t,t⁻¹])`** — the one-variable model does
not contain the phenomenon. Confirmed from the other side: compressors come from
`SL_d(ℤ)` monomial substitutions, and `SL₁(ℤ)` is trivial.

**Diagnostic.** Before building a model, check it against
`no_strict_compression_of_invariantSize`. Four proposed architectures died
because they lived in categories with an invariant size — finite quotients,
towers, compact stabilizers, one-variable fibers. The check is minutes; the
constructions were sessions.

**Second diagnostic: (T)-compatibility.** A carrier must contain `L(Γ)` for `Γ`
Kazhdan, which is a diffuse factor with property (T). A von Neumann algebra with
the **Haagerup property** contains no diffuse (T) subalgebra. So free group
factors, and free-probability carriers built from them, are excluded — however
Connes-embeddable they are. Embeddability is cheap; (T)-compatibility is what
costs. Three candidate witnesses in a row satisfied the compression requirement
and failed a different one (no (T); wrong overlap structure; Haagerup).

## 5. The two branches

**Rigidity.** If `G` is flexibly HS-stable then the wreath candidate is not
hyperlinear: lift `ρ|_G` to genuine `π_m`, pad the lamp, apply the Kazhdan pair
to the *genuine* adjoint representation to place it near `π_m(Γ)′`, then
**`commutant_no_growth`** makes `π_m(G)` normalize `π_m(Γ)′` exactly, and two
distinct lamps collapse against trace separation. The one algebraic step is
formalized; the analysis is not. Dogon (arXiv:2211.10492) proves the same shape
for central extensions by a cohomological engine — complementary, since his is
amplification-proof but blind to split extensions.

**Flexibility.** Requires a model where the `Γ`-pieces genuinely have no
consistent size. All eight no-gos above kill *constructive* methods and none
kills abstract existence — but the tools for proving `R^𝒰`-embeddability
abstractly are thin.

**A logical caution.** Evidence that a candidate is *not* hyperlinear does not
push Pestov's Question 3.4 toward "yes". It removes that candidate and leaves
the question untouched. Only the flexible side is informative about Q3.4 at all.
Since every known nonsofic group comes from the same (T)-compression mechanism —
the mechanism all eight no-gos attack — Q3.4 may be inaccessible until a
*second* nonsoficity mechanism exists.

## 6. What is settled

**`Sofic/Hyperlinear.isHyperlinear_of_isSofic`** (formalized): soficity implies
hyperlinearity, with `IsHyperlinear` defined by unitary matrices in the
normalized Hilbert–Schmidt metric. The proof is the metric identity
`‖P_σ − P_τ‖²_{HS,norm} = 2·d_H(σ,τ)` together with the fact that
`σ ↦ P_{σ⁻¹}` is a genuine homomorphism — the inverse matters, `permMatrix`
itself being an anti-homomorphism.

The converse is Question 3.4 and is open.
