import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Finset.Image

/-!
# Kazhdan's property (T)

For a discrete group, Kazhdan's property `(T)` says that some finite subset and
positive tolerance form a Kazhdan pair: every orthogonal representation with
an almost invariant unit vector has a nonzero invariant vector.  This is the
standard quantitative definition used in the proofs of Kun and of
Ershov--Jaikin-Zapirain.
-/

namespace NonsoficGroupsExist

universe u v w

/-- A finite set `Q` and positive real `ε` are a Kazhdan pair when every
orthogonal representation admitting a `(Q,ε)`-almost invariant unit vector
has a nonzero invariant vector. -/
def IsKazhdanPair (G : Type u) [Group G] (Q : Finset G) (ε : ℝ) : Prop :=
  0 < ε ∧
    ∀ (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [CompleteSpace E],
      ∀ ρ : G →* (E ≃ₗᵢ[ℝ] E), ∀ x : E, ‖x‖ = 1 →
        (∀ q ∈ Q, ‖ρ q x - x‖ < ε) →
          ∃ y : E, y ≠ 0 ∧ ∀ g : G, ρ g y = y

/-- Kazhdan's property `(T)` for a discrete group, in its standard
Kazhdan-pair formulation. -/
def HasKazhdanPropertyT (G : Type u) [Group G] : Prop :=
  ∃ Q : Finset G, ∃ ε : ℝ, IsKazhdanPair.{u, v} G Q ε

namespace IsKazhdanPair

variable {G : Type u} [Group G] {Q R : Finset G} {ε : ℝ}

/-- The quantitative uniform-convexity estimate used to turn Kazhdan
displacement into contraction of a finite orbit average. -/
theorem norm_add_le_of_norm_sub_ge
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x y : E} {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hnorm : ‖y‖ = ‖x‖) (hmove : a * ‖x‖ ≤ ‖y - x‖) :
    ‖x + y‖ ≤ (2 - a ^ 2 / 4) * ‖x‖ := by
  have hpara := parallelogram_law_with_norm ℝ x y
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
  have hsum0 : 0 ≤ ‖x + y‖ := norm_nonneg _
  have hcoef : 0 ≤ 2 - a ^ 2 / 4 := by nlinarith
  have hamul : 0 ≤ a * ‖x‖ := mul_nonneg ha0 hx0
  have hmoveSq : (a * ‖x‖) ^ 2 ≤ ‖y - x‖ ^ 2 := by
    exact (sq_le_sq₀ hamul (norm_nonneg _)).2 hmove
  have hsub : ‖y - x‖ = ‖x - y‖ := by
    rw [show y - x = -(x - y) by abel, norm_neg]
  rw [hnorm] at hpara
  rw [hsub] at hmoveSq
  have hfirst : ‖x + y‖ ^ 2 ≤ (4 - a ^ 2) * ‖x‖ ^ 2 := by
    nlinarith
  have hcoefsquare : 4 - a ^ 2 ≤ (2 - a ^ 2 / 4) ^ 2 := by
    nlinarith [sq_nonneg (a ^ 2)]
  have hsquare : ‖x + y‖ ^ 2 ≤
      ((2 - a ^ 2 / 4) * ‖x‖) ^ 2 := by
    calc
      ‖x + y‖ ^ 2 ≤ (4 - a ^ 2) * ‖x‖ ^ 2 := hfirst
      _ ≤ (2 - a ^ 2 / 4) ^ 2 * ‖x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hcoefsquare (sq_nonneg _)
      _ = ((2 - a ^ 2 / 4) * ‖x‖) ^ 2 := by ring
  have hright0 : 0 ≤ (2 - a ^ 2 / 4) * ‖x‖ := mul_nonneg hcoef hx0
  exact (sq_le_sq₀ hsum0 hright0).mp hsquare

/-- If a finite equal-norm family contains a separated pair, its vector sum
falls quantitatively short of the triangle-inequality maximum. -/
theorem norm_sum_le_of_pair_separated
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {I : Type*} [DecidableEq I] (s : Finset I) (z : I → E)
    {i j : I} {a r : ℝ} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hnorm : ∀ k ∈ s, ‖z k‖ = r)
    (hmove : a * r ≤ ‖z j - z i‖) :
    ‖∑ k ∈ s, z k‖ ≤ (s.card - a ^ 2 / 4) * r := by
  let rest := (s.erase i).erase j
  have hjrest : j ∈ s.erase i := Finset.mem_erase.mpr ⟨hij.symm, hj⟩
  have hsum : ∑ k ∈ s, z k = z i + z j + ∑ k ∈ rest, z k := by
    calc
      ∑ k ∈ s, z k = (∑ k ∈ s.erase i, z k) + z i :=
        (Finset.sum_erase_add s z hi).symm
      _ = ((∑ k ∈ rest, z k) + z j) + z i := by
        rw [show ∑ k ∈ s.erase i, z k =
          (∑ k ∈ rest, z k) + z j from
            (Finset.sum_erase_add (s.erase i) z hjrest).symm]
      _ = z i + z j + ∑ k ∈ rest, z k := by abel
  have hpair : ‖z i + z j‖ ≤ (2 - a ^ 2 / 4) * r := by
    calc
      ‖z i + z j‖ ≤ (2 - a ^ 2 / 4) * ‖z i‖ :=
        norm_add_le_of_norm_sub_ge ha0 ha1
          (by rw [hnorm j hj, hnorm i hi])
          (by simpa [hnorm i hi] using hmove)
      _ = (2 - a ^ 2 / 4) * r := by rw [hnorm i hi]
  have hrestSubset : rest ⊆ s := by
    exact (Finset.erase_subset j (s.erase i)).trans (Finset.erase_subset i s)
  have hrest : ‖∑ k ∈ rest, z k‖ ≤ rest.card * r := by
    calc
      ‖∑ k ∈ rest, z k‖ ≤ ∑ k ∈ rest, ‖z k‖ := norm_sum_le _ _
      _ = ∑ _ ∈ rest, r := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hnorm k (hrestSubset hk)
      _ = rest.card * r := by simp
  have hcard : rest.card + 2 = s.card := by
    have hcardI := Finset.card_erase_add_one hi
    have hcardJ := Finset.card_erase_add_one hjrest
    change ((s.erase i).erase j).card + 2 = s.card
    omega
  have hcardReal : (rest.card : ℝ) + 2 = s.card := by exact_mod_cast hcard
  rw [hsum]
  calc
    ‖z i + z j + ∑ k ∈ rest, z k‖ ≤
        ‖z i + z j‖ + ‖∑ k ∈ rest, z k‖ := norm_add_le _ _
    _ ≤ (2 - a ^ 2 / 4) * r + rest.card * r := add_le_add hpair hrest
    _ = ((rest.card : ℝ) + 2 - a ^ 2 / 4) * r := by ring
    _ = (s.card - a ^ 2 / 4) * r := by rw [hcardReal]

/-- Enlarging the finite control set preserves a Kazhdan pair. -/
theorem mono (hQ : IsKazhdanPair.{u, v} G Q ε) (hQR : Q ⊆ R) :
    IsKazhdanPair.{u, v} G R ε := by
  refine ⟨hQ.1, ?_⟩
  intro E _ _ _ ρ x hx hnear
  exact hQ.2 E ρ x hx (fun q hq ↦ hnear q (hQR hq))

/-- Decreasing the tolerance preserves a Kazhdan pair. -/
theorem shrink (hQ : IsKazhdanPair.{u, v} G Q ε) {a : ℝ}
    (ha : 0 < a) (haε : a ≤ ε) : IsKazhdanPair.{u, v} G Q a := by
  refine ⟨ha, ?_⟩
  intro E _ _ _ ρ x hx hnear
  exact hQ.2 E ρ x hx fun q hq ↦ (hnear q hq).trans_le haε

/-- A representation has no nonzero invariant vectors. -/
def HasNoInvariantVectors {E : Type v} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (G : Type u) [Group G]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) : Prop :=
  ∀ y : E, (∀ g : G, ρ g y = y) → y = 0

/-- In a representation without invariant vectors, every unit vector is moved
by at least the Kazhdan tolerance by one element of the finite control set. -/
theorem exists_moved_of_noInvariant
    (hQ : IsKazhdanPair.{u, v} G Q ε)
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (ρ : G →* (E ≃ₗᵢ[ℝ] E))
    (hno : HasNoInvariantVectors G ρ) (x : E) (hx : ‖x‖ = 1) :
    ∃ q ∈ Q, ε ≤ ‖ρ q x - x‖ := by
  by_contra h
  have hnear : ∀ q ∈ Q, ‖ρ q x - x‖ < ε := by
    intro q hq
    exact lt_of_not_ge (fun hge ↦ h ⟨q, hq, hge⟩)
  obtain ⟨y, hy, hinv⟩ := hQ.2 E ρ x hx hnear
  exact hy (hno y hinv)

/-- Homogeneous form of the Kazhdan displacement estimate. -/
theorem exists_moved_mul_norm_of_noInvariant
    (hQ : IsKazhdanPair.{u, v} G Q ε)
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (ρ : G →* (E ≃ₗᵢ[ℝ] E))
    (hno : HasNoInvariantVectors G ρ) (x : E) (hx : x ≠ 0) :
    ∃ q ∈ Q, ε * ‖x‖ ≤ ‖ρ q x - x‖ := by
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let z : E := (‖x‖⁻¹ : ℝ) • x
  have hz : ‖z‖ = 1 := by
    rw [show ‖z‖ = |‖x‖⁻¹| * ‖x‖ by simp [z, norm_smul]]
    rw [abs_of_pos (inv_pos.mpr hnorm), inv_mul_cancel₀ hnorm.ne']
  obtain ⟨q, hq, hmove⟩ := exists_moved_of_noInvariant hQ ρ hno z hz
  refine ⟨q, hq, ?_⟩
  have hnormalized : ‖ρ q z - z‖ = ‖ρ q x - x‖ / ‖x‖ := by
    rw [show ρ q z - z = (‖x‖⁻¹ : ℝ) • (ρ q x - x) by
      simp [z, smul_sub]]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm)]
    rw [div_eq_mul_inv, mul_comm]
  rw [hnormalized] at hmove
  exact (le_div_iff₀ hnorm).mp hmove

/-- The normalized average of the orbit of a vector over a finite control
set. -/
noncomputable def orbitAverage {E : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : Finset G) (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) : E :=
  ((S.card : ℝ)⁻¹) • ∑ q ∈ S, ρ q x

/-- A Kazhdan displacement estimate makes the orbit average a strict
contraction on representations without invariant vectors.  The identity in
`S` supplies one endpoint of the separated pair. -/
theorem norm_orbitAverage_le
    (hQ : IsKazhdanPair.{u, v} G Q ε) (S : Finset G)
    (hQS : Q ⊆ S) (hone : 1 ∈ S) (hεone : ε ≤ 1)
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (ρ : G →* (E ≃ₗᵢ[ℝ] E))
    (hno : HasNoInvariantVectors G ρ) (x : E) :
    ‖orbitAverage S ρ x‖ ≤
      (1 - ε ^ 2 / (4 * S.card)) * ‖x‖ := by
  classical
  by_cases hx : x = 0
  · subst x
    simp [orbitAverage]
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  obtain ⟨q, hqQ, hmove⟩ :=
    exists_moved_mul_norm_of_noInvariant hQ ρ hno x hx
  have hqS : q ∈ S := hQS hqQ
  have hqne : (1 : G) ≠ q := by
    intro heq
    rw [← heq] at hmove
    simp at hmove
    exact (not_lt_of_ge hmove) (mul_pos hQ.1 hxnorm)
  have hsum := norm_sum_le_of_pair_separated S (fun g ↦ ρ g x)
    hone hqS hqne hQ.1.le hεone
    (fun g _ ↦ (ρ g).norm_map x) (by simpa using hmove)
  have hcardNat : 0 < S.card := Finset.card_pos.mpr ⟨1, hone⟩
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hcardNat
  rw [orbitAverage, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hcard)]
  calc
    (S.card : ℝ)⁻¹ * ‖∑ q ∈ S, ρ q x‖ ≤
        (S.card : ℝ)⁻¹ * ((S.card - ε ^ 2 / 4) * ‖x‖) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hcard.le)
    _ = (1 - ε ^ 2 / (4 * S.card)) * ‖x‖ := by
      field_simp

end IsKazhdanPair

namespace HasKazhdanPropertyT

variable {G : Type u} {H : Type v} [Group G] [Group H]

/-- A property-`(T)` group has a Kazhdan pair whose control set contains the
identity and whose tolerance lies in `(0,1]`. -/
theorem exists_identity_pair (hG : HasKazhdanPropertyT.{u, w} G) :
    ∃ S : Finset G, ∃ ε : ℝ,
      1 ∈ S ∧ 0 < ε ∧ ε ≤ 1 ∧ IsKazhdanPair.{u, w} G S ε := by
  classical
  obtain ⟨Q, a, ha⟩ := hG
  let ε := min a 1
  let S := insert 1 Q
  have hεpos : 0 < ε := lt_min ha.1 zero_lt_one
  have hεa : ε ≤ a := min_le_left _ _
  have hεone : ε ≤ 1 := min_le_right _ _
  refine ⟨S, ε, by simp [S], hεpos, hεone, ?_⟩
  apply IsKazhdanPair.mono (IsKazhdanPair.shrink ha hεpos hεa)
  exact Finset.subset_insert 1 Q

/-- Property `(T)` is invariant under group isomorphism. -/
theorem of_mulEquiv (e : G ≃* H) (hH : HasKazhdanPropertyT.{v, w} H) :
    HasKazhdanPropertyT.{u, w} G := by
  obtain ⟨Q, ε, hε, hQ⟩ := hH
  let QG : Finset G := Q.map e.symm.toEmbedding
  refine ⟨QG, ε, hε, ?_⟩
  intro E _ _ _ ρ x hx hnear
  let ρH : H →* (E ≃ₗᵢ[ℝ] E) := ρ.comp e.symm.toMonoidHom
  have hnearH : ∀ q ∈ Q, ‖ρH q x - x‖ < ε := by
    intro q hq
    apply hnear (e.symm q)
    exact Finset.mem_map.mpr ⟨q, hq, rfl⟩
  obtain ⟨y, hy, hinv⟩ := hQ E ρH x hx hnearH
  exact ⟨y, hy, fun g ↦ by simpa [ρH] using hinv (e g)⟩

theorem mulEquiv_iff (e : G ≃* H) :
    HasKazhdanPropertyT.{u, w} G ↔ HasKazhdanPropertyT.{v, w} H :=
  ⟨fun hG ↦ of_mulEquiv e.symm hG, fun hH ↦ of_mulEquiv e hH⟩

/-- Property `(T)` passes to quotients. -/
theorem of_surjective (f : G →* H) (hf : Function.Surjective f)
    (hG : HasKazhdanPropertyT.{u, w} G) : HasKazhdanPropertyT.{v, w} H := by
  classical
  obtain ⟨Q, ε, hε, hQ⟩ := hG
  let QH : Finset H := Q.image f
  refine ⟨QH, ε, hε, ?_⟩
  intro E _ _ _ ρ x hx hnear
  let ρG : G →* (E ≃ₗᵢ[ℝ] E) := ρ.comp f
  have hnearG : ∀ q ∈ Q, ‖ρG q x - x‖ < ε := by
    intro q hq
    apply hnear (f q)
    simpa [QH] using Finset.mem_image.mpr ⟨q, hq, rfl⟩
  obtain ⟨y, hy, hinv⟩ := hQ E ρG x hx hnearG
  refine ⟨y, hy, fun h ↦ ?_⟩
  obtain ⟨g, rfl⟩ := hf h
  exact hinv g

end HasKazhdanPropertyT
end NonsoficGroupsExist
