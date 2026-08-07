import NonsoficGroupsExist.Sofic.SoficAmplification
import Mathlib.Order.Filter.Ultrafilter.Defs
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Sofic embeddings into metric ultraproducts of symmetric groups

The literature that this development's negative results feed into states
soficity a third way: a countable group is sofic when it embeds into a
*universal sofic group*, the metric ultraproduct
`∏_𝒰 Sym(X i)` of finite symmetric groups along a nonprincipal ultrafilter.
That is the formulation used for sofic approximations of Kazhdan groups and
their centralizers, for sofic actions, and for the Loeb-space picture.  This
file connects it to `IsSofic`.

The ultraproduct is built here directly: `IsNullSeq` picks out the sequences of
permutations whose normalized Hamming length tends to zero along `𝒰`, these
form a normal subgroup `nullSubgroup` of the product group because the Hamming
length is conjugation invariant, and `UniversalSofic` is the quotient.

`isSofic_of_soficEmbedding` is the bridge: an injective homomorphism into any
such quotient makes the group sofic.  Amplification is exactly what makes this
work.  Lifting the images of a finite test set gives multiplicativity to within
any prescribed `ε` on a `𝒰`-large set, but injectivity gives only that distinct
elements are at *some* positive Hamming distance, an amount depending on the
pair — never the `1 - ε` that `IsSofic` asks for.  That is precisely the
hypothesis `IsSoficWeakLocal` of `Sofic.SoficAmplification`, which tensor powers
upgrade.

`no_soficEmbedding_of_not_isSofic` is the contrapositive, and is the form in
which the nonsoficity endpoints are read by that literature: the witness admits
no injective homomorphism into any metric ultraproduct of finite symmetric
groups, over any index type and any ultrafilter.
-/

namespace NonsoficGroupsExist

open Filter

/-! ## Hamming length -/

/-- Displacement from the identity. -/
noncomputable def hammingLength (Y : FiniteModel) (p : Equiv.Perm Y) : ℝ :=
  hammingDistance Y p 1

@[simp] theorem hammingLength_one (Y : FiniteModel) : hammingLength Y 1 = 0 :=
  hammingDistance_self Y 1

theorem hammingLength_nonneg (Y : FiniteModel) (p : Equiv.Perm Y) :
    0 ≤ hammingLength Y p :=
  hammingDistance_nonnegative Y p 1

/-- The identity that makes the quotient metric the Hamming metric:
`|q⁻¹p| = d(p, q)`. -/
theorem hammingLength_inv_mul (Y : FiniteModel) (p q : Equiv.Perm Y) :
    hammingLength Y (q⁻¹ * p) = hammingDistance Y p q := by
  have hq : q * (q⁻¹ * p) = p := by group
  have h := hammingDistance_left_invariant Y q (q⁻¹ * p) 1
  rw [hq, mul_one] at h
  rw [hammingLength, h]

theorem hammingLength_mul_le (Y : FiniteModel) (p q : Equiv.Perm Y) :
    hammingLength Y (p * q) ≤ hammingLength Y p + hammingLength Y q := by
  have hleft : hammingDistance Y (p * q) p = hammingDistance Y q 1 := by
    have h := hammingDistance_left_invariant Y p q 1
    rwa [mul_one] at h
  have htri := hammingDistance_triangle Y (p * q) p 1
  rw [hleft] at htri
  simp only [hammingLength]
  linarith

theorem hammingLength_inv (Y : FiniteModel) (p : Equiv.Perm Y) :
    hammingLength Y p⁻¹ = hammingLength Y p := by
  have h := hammingLength_inv_mul Y 1 p
  rw [mul_one] at h
  simp only [hammingLength] at h ⊢
  rw [h, hammingDistance_comm]

/-- Conjugation invariance, which is what makes the null sequences normal. -/
theorem hammingLength_conj (Y : FiniteModel) (t p : Equiv.Perm Y) :
    hammingLength Y (t * p * t⁻¹) = hammingLength Y p := by
  have hr := hammingDistance_right_invariant Y (t * p * t⁻¹) 1 t
  have hcancel : t * p * t⁻¹ * t = t * p := by group
  rw [hcancel, one_mul] at hr
  have hl := hammingDistance_left_invariant Y t p 1
  rw [mul_one] at hl
  simp only [hammingLength]
  rw [← hr, hl]

/-! ## The metric ultraproduct -/

variable {ι : Type*} (𝒰 : Ultrafilter ι) (X : ι → FiniteModel)

/-- Sequences of permutations whose Hamming length vanishes along `𝒰`. -/
def IsNullSeq (σ : ∀ i, Equiv.Perm (X i)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ i in (𝒰 : Filter ι), hammingLength (X i) (σ i) < ε

/-- Positive control: the constant identity sequence is null. -/
theorem isNullSeq_one : IsNullSeq 𝒰 X 1 := by
  intro ε hε
  filter_upwards with i
  show hammingLength (X i) 1 < ε
  rw [hammingLength_one]
  exact hε

/-- The null sequences, as a subgroup of the product. -/
def nullSubgroup : Subgroup (∀ i, Equiv.Perm (X i)) where
  carrier := {σ | IsNullSeq 𝒰 X σ}
  one_mem' := isNullSeq_one 𝒰 X
  mul_mem' := by
    intro σ τ hσ hτ ε hε
    filter_upwards [hσ (ε / 2) (by linarith), hτ (ε / 2) (by linarith)] with i hi hj
    calc hammingLength (X i) ((σ * τ) i)
        ≤ hammingLength (X i) (σ i) + hammingLength (X i) (τ i) :=
          hammingLength_mul_le (X i) (σ i) (τ i)
      _ < ε / 2 + ε / 2 := by linarith
      _ = ε := by ring
  inv_mem' := by
    intro σ hσ ε hε
    filter_upwards [hσ ε hε] with i hi
    show hammingLength (X i) (σ i)⁻¹ < ε
    rwa [hammingLength_inv]

instance nullSubgroup_normal : (nullSubgroup 𝒰 X).Normal where
  conj_mem := by
    intro σ hσ τ ε hε
    filter_upwards [hσ ε hε] with i hi
    show hammingLength (X i) (τ i * σ i * (τ i)⁻¹) < ε
    rwa [hammingLength_conj]

/-- The universal sofic group over `X` along `𝒰`. -/
abbrev UniversalSofic : Type _ :=
  (∀ i, Equiv.Perm (X i)) ⧸ nullSubgroup 𝒰 X

/-! ## The bridge -/

variable {G : Type*} [Group G]

/-- **Sofic embeddings give soficity.**  An injective homomorphism into a metric
ultraproduct of finite symmetric groups makes the group sofic in the local
finite-model sense.  Separation only comes out pair-by-pair, so the argument
lands in `IsSoficWeakLocal` and is amplified from there. -/
theorem isSofic_of_soficEmbedding (hX : ∀ i, 0 < Fintype.card (X i))
    (f : G →* UniversalSofic 𝒰 X) (hf : Function.Injective f) :
    IsSofic G := by
  classical
  -- lift every image to an honest sequence of permutations
  choose lift hlift using fun g : G ↦ QuotientGroup.mk_surjective (f g)
  -- multiplicativity: the defect sequence is null, so it is small `𝒰`-often
  have hmul : ∀ g h : G, ∀ ε : ℝ, 0 < ε → ∀ᶠ i in (𝒰 : Filter ι),
      hammingDistance (X i) (lift (g * h) i) (lift g i * lift h i) ≤ ε := by
    intro g h ε hε
    have heq : (QuotientGroup.mk (lift g * lift h) : UniversalSofic 𝒰 X)
        = QuotientGroup.mk (lift (g * h)) := by
      rw [QuotientGroup.mk_mul, hlift, hlift, hlift, map_mul]
    have hnull : (lift g * lift h)⁻¹ * lift (g * h) ∈ nullSubgroup 𝒰 X :=
      QuotientGroup.eq.mp heq
    filter_upwards [hnull ε hε] with i hi
    have hval : hammingLength (X i) (((lift g * lift h)⁻¹ * lift (g * h)) i)
        = hammingDistance (X i) (lift (g * h) i) (lift g i * lift h i) :=
      hammingLength_inv_mul (X i) (lift (g * h) i) (lift g i * lift h i)
    rw [hval] at hi
    exact le_of_lt hi
  -- separation: distinct elements have distinct images, so their difference is
  -- not null -- but only by some positive amount depending on the pair
  have hsep : ∀ g h : G, g ≠ h → ∃ d : ℝ, 0 < d ∧ ∀ᶠ i in (𝒰 : Filter ι),
      d ≤ hammingDistance (X i) (lift g i) (lift h i) := by
    intro g h hne
    have hfne : f g ≠ f h := fun hc ↦ hne (hf hc)
    have hnot : (lift h)⁻¹ * lift g ∉ nullSubgroup 𝒰 X := by
      intro hc
      exact hfne (by rw [← hlift g, ← hlift h]; exact (QuotientGroup.eq.mpr hc).symm)
    have hnot' : ¬ IsNullSeq 𝒰 X ((lift h)⁻¹ * lift g) := hnot
    have hex : ∃ d : ℝ, 0 < d ∧ ¬ (∀ᶠ i in (𝒰 : Filter ι),
        hammingLength (X i) (((lift h)⁻¹ * lift g) i) < d) := by
      by_contra hcon
      refine hnot' fun d hd ↦ ?_
      by_contra hbad
      exact hcon ⟨d, hd, hbad⟩
    obtain ⟨d, hd, hev⟩ := hex
    refine ⟨d, hd, ?_⟩
    have hcompl := (Ultrafilter.eventually_not (p := fun i ↦
      hammingLength (X i) (((lift h)⁻¹ * lift g) i) < d)).mpr hev
    filter_upwards [hcompl] with i hi
    have hval : hammingLength (X i) (((lift h)⁻¹ * lift g) i)
        = hammingDistance (X i) (lift g i) (lift h i) :=
      hammingLength_inv_mul (X i) (lift g i) (lift h i)
    rw [hval] at hi
    exact not_lt.mp hi
  -- one separation constant for the whole test set
  apply isSofic_of_isSoficWeakLocal
  intro F
  have hpair : ∀ p : G × G, ∃ d : ℝ, 0 < d ∧ (p.1 ≠ p.2 →
      ∀ᶠ i in (𝒰 : Filter ι), d ≤ hammingDistance (X i) (lift p.1 i) (lift p.2 i)) := by
    intro p
    by_cases hp : p.1 = p.2
    · exact ⟨1, one_pos, fun hc ↦ absurd hp hc⟩
    · obtain ⟨d, hd, hev⟩ := hsep p.1 p.2 hp
      exact ⟨d, hd, fun _ ↦ hev⟩
  choose dl hdl hdlev using hpair
  set T : Finset ℝ := insert (1 : ℝ) ((F ×ˢ F).image dl) with hT
  have hTne : T.Nonempty := ⟨1, by simp [hT]⟩
  refine ⟨T.min' hTne, ?_, ?_⟩
  · rw [Finset.lt_min'_iff]
    intro b hb
    rw [hT, Finset.mem_insert, Finset.mem_image] at hb
    rcases hb with rfl | ⟨p, -, rfl⟩
    · exact one_pos
    · exact hdl p
  intro ε hε
  -- collect the finitely many `𝒰`-large sets and pick an index in all of them
  have hall : ∀ᶠ i in (𝒰 : Filter ι), ∀ p ∈ F ×ˢ F,
      hammingDistance (X i) (lift (p.1 * p.2) i) (lift p.1 i * lift p.2 i) ≤ ε ∧
      (p.1 ≠ p.2 → T.min' hTne ≤ hammingDistance (X i) (lift p.1 i) (lift p.2 i)) := by
    rw [eventually_all_finset]
    intro p hp
    have h1 := hmul p.1 p.2 ε hε
    by_cases hne : p.1 = p.2
    · filter_upwards [h1] with i hi
      exact ⟨hi, fun hc ↦ absurd hne hc⟩
    · have hmemT : dl p ∈ T := by
        rw [hT]
        exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem dl hp)
      have hmin : T.min' hTne ≤ dl p := Finset.min'_le T (dl p) hmemT
      filter_upwards [h1, hdlev p hne] with i hi hj
      exact ⟨hi, fun _ ↦ le_trans hmin hj⟩
  obtain ⟨i, hi⟩ := hall.exists
  exact ⟨{
    carrier := X i
    nonempty := hX i
    map := fun g ↦ lift g i
    multiplicative := fun g hg h hh ↦
      (hi (g, h) (Finset.mem_product.mpr ⟨hg, hh⟩)).1
    separated := fun g hg h hh hne ↦
      (hi (g, h) (Finset.mem_product.mpr ⟨hg, hh⟩)).2 hne }⟩

/-- **The reading of a nonsoficity endpoint in ultraproduct language.**  A group
that is not sofic admits no injective homomorphism into any metric ultraproduct
of finite symmetric groups, over any index type and any ultrafilter. -/
theorem no_soficEmbedding_of_not_isSofic (h : ¬ IsSofic G)
    (hX : ∀ i, 0 < Fintype.card (X i)) (f : G →* UniversalSofic 𝒰 X) :
    ¬ Function.Injective f :=
  fun hf ↦ h (isSofic_of_soficEmbedding 𝒰 X hX f hf)

end NonsoficGroupsExist
