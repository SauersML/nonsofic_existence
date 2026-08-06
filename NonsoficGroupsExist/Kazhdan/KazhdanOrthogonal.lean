import NonsoficGroupsExist.Kazhdan.Kazhdan
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# The invariant-vector orthogonal complement

This module restricts an orthogonal group representation to the orthogonal
complement of its invariant vectors.  It is the bridge from the Kazhdan-pair
definition to the spectral contraction used in Kun's Markov argument.
-/

namespace NonsoficGroupsExist
namespace KazhdanOrthogonal

open scoped InnerProductSpace

universe u v

variable {G : Type u} [Group G]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The linear subspace of invariant vectors of an orthogonal
representation. -/
def invariantSubmodule (ρ : G →* (E ≃ₗᵢ[ℝ] E)) : Submodule ℝ E where
  carrier := {x | ∀ g : G, ρ g x = x}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy g
    simp [hx g, hy g]
  smul_mem' := by
    intro c x hx g
    simp [hx g]

@[simp] theorem mem_invariantSubmodule (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    x ∈ invariantSubmodule ρ ↔ ∀ g : G, ρ g x = x := Iff.rfl

theorem map_mem_orthogonal (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (g : G)
    {x : E} (hx : x ∈ (invariantSubmodule ρ)ᗮ) :
    ρ g x ∈ (invariantSubmodule ρ)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro y hy
  have hyinv : ρ g⁻¹ y = y := (mem_invariantSubmodule ρ y).1 hy g⁻¹
  have hcancel : ρ g⁻¹ (ρ g x) = x := by simp
  calc
    ⟪y, ρ g x⟫_ℝ = ⟪ρ g⁻¹ y, ρ g⁻¹ (ρ g x)⟫_ℝ := by
      rw [(ρ g⁻¹).inner_map_map]
    _ = ⟪y, x⟫_ℝ := by rw [hyinv, hcancel]
    _ = 0 := Submodule.inner_right_of_mem_orthogonal hy hx

/-- Restriction of one representation operator to the invariant-vector
orthogonal complement. -/
def orthogonalOperator (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (g : G) :
    (invariantSubmodule ρ)ᗮ ≃ₗᵢ[ℝ] (invariantSubmodule ρ)ᗮ where
  toFun x := ⟨ρ g x.1, map_mem_orthogonal ρ g x.2⟩
  invFun x := ⟨ρ g⁻¹ x.1, map_mem_orthogonal ρ g⁻¹ x.2⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv x := by
    apply Subtype.ext
    simp
  map_add' x y := by
    apply Subtype.ext
    simp
  map_smul' c x := by
    apply Subtype.ext
    simp
  norm_map' x := (ρ g).norm_map x.1

@[simp] theorem orthogonalOperator_apply_coe
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (g : G) (x : (invariantSubmodule ρ)ᗮ) :
    ((orthogonalOperator ρ g x : (invariantSubmodule ρ)ᗮ) : E) = ρ g x := rfl

/-- The orthogonal restrictions form a group representation. -/
def orthogonalRepresentation (ρ : G →* (E ≃ₗᵢ[ℝ] E)) :
    G →* ((invariantSubmodule ρ)ᗮ ≃ₗᵢ[ℝ] (invariantSubmodule ρ)ᗮ) where
  toFun := orthogonalOperator ρ
  map_one' := by
    ext x
    simp [orthogonalOperator]
  map_mul' g h := by
    ext x
    simp [orthogonalOperator]

/-- The restricted representation has no nonzero invariant vector. -/
theorem orthogonalRepresentation_hasNoInvariantVectors
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) :
    IsKazhdanPair.HasNoInvariantVectors G (orthogonalRepresentation ρ) := by
  intro x hx
  apply Subtype.ext
  change (x : E) = 0
  have hinner : inner ℝ (x : E) (x : E) = 0 := by
    apply Submodule.inner_right_of_mem_orthogonal (K := invariantSubmodule ρ)
    · rw [mem_invariantSubmodule]
      intro g
      have hg := congrArg Subtype.val (hx g)
      simpa [orthogonalRepresentation, orthogonalOperator] using hg
    · exact x.2
  exact inner_self_eq_zero.mp hinner

/-- The Kazhdan orbit-average contraction applied to the orthogonal
complement of the invariant vectors. -/
theorem norm_orbitAverage_orthogonal_le [CompleteSpace E]
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, v} G Q ε)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S) (hεone : ε ≤ 1)
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : (invariantSubmodule ρ)ᗮ) :
    ‖IsKazhdanPair.orbitAverage S (orthogonalRepresentation ρ) x‖ ≤
      (1 - ε ^ 2 / (4 * S.card)) * ‖x‖ := by
  exact hQ.norm_orbitAverage_le S hQS hone hεone
    (orthogonalRepresentation ρ)
    (orthogonalRepresentation_hasNoInvariantVectors ρ) x

/-- Coercing the restricted orbit average back to the original Hilbert
space gives the original orbit average. -/
@[simp] theorem coe_orbitAverage_orthogonal
    (S : Finset G) (ρ : G →* (E ≃ₗᵢ[ℝ] E))
    (x : (invariantSubmodule ρ)ᗮ) :
    ((IsKazhdanPair.orbitAverage S (orthogonalRepresentation ρ) x :
        (invariantSubmodule ρ)ᗮ) : E) =
      IsKazhdanPair.orbitAverage S ρ x := by
  classical
  simp [IsKazhdanPair.orbitAverage, orthogonalRepresentation,
    orthogonalOperator]

/-- The original orbit average contracts every vector orthogonal to the
invariant subspace. -/
theorem norm_orbitAverage_le_of_mem_orthogonal [CompleteSpace E]
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, v} G Q ε)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S) (hεone : ε ≤ 1)
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) {x : E}
    (hx : x ∈ (invariantSubmodule ρ)ᗮ) :
    ‖IsKazhdanPair.orbitAverage S ρ x‖ ≤
      (1 - ε ^ 2 / (4 * S.card)) * ‖x‖ := by
  let x' : (invariantSubmodule ρ)ᗮ := ⟨x, hx⟩
  have h := norm_orbitAverage_orthogonal_le hQ S hQS hone hεone ρ x'
  simpa [x'] using h

/-- Homogeneous Kazhdan displacement for a vector orthogonal to the
invariant subspace of an arbitrary representation. -/
theorem exists_moved_mul_norm_of_mem_orthogonal [CompleteSpace E]
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, v} G Q ε)
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) {x : E}
    (hxorth : x ∈ (invariantSubmodule ρ)ᗮ) (hx : x ≠ 0) :
    ∃ q ∈ Q, ε * ‖x‖ ≤ ‖ρ q x - x‖ := by
  let x' : (invariantSubmodule ρ)ᗮ := ⟨x, hxorth⟩
  have hx' : x' ≠ 0 := by
    intro hzero
    apply hx
    exact congrArg Subtype.val hzero
  obtain ⟨q, hq, hmove⟩ :=
    hQ.exists_moved_mul_norm_of_noInvariant (orthogonalRepresentation ρ)
      (orthogonalRepresentation_hasNoInvariantVectors ρ) x' hx'
  refine ⟨q, hq, ?_⟩
  change ε * ‖x‖ ≤ ‖ρ q x - x‖ at hmove
  exact hmove

/-- Subtracting a vector from its orbit average removes its invariant
component. -/
theorem orbitAverage_sub_mem_orthogonal
    (S : Finset G) (hone : 1 ∈ S) (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    IsKazhdanPair.orbitAverage S ρ x - x ∈
      (invariantSubmodule ρ)ᗮ := by
  classical
  rw [Submodule.mem_orthogonal]
  intro y hy
  have hyinv : ∀ g : G, ρ g y = y :=
    (mem_invariantSubmodule ρ y).1 hy
  have hinner : ∀ g : G, ⟪y, ρ g x⟫_ℝ = ⟪y, x⟫_ℝ := by
    intro g
    have hcancel : ρ g⁻¹ (ρ g x) = x := by simp
    calc
      ⟪y, ρ g x⟫_ℝ = ⟪ρ g⁻¹ y, ρ g⁻¹ (ρ g x)⟫_ℝ := by
        rw [(ρ g⁻¹).inner_map_map]
      _ = ⟪y, x⟫_ℝ := by rw [hyinv g⁻¹, hcancel]
  have hsum : ⟪y, ∑ g ∈ S, ρ g x⟫_ℝ =
      (S.card : ℝ) * ⟪y, x⟫_ℝ := by
    simp_rw [inner_sum, hinner]
    simp
  have hcardNat : 0 < S.card := Finset.card_pos.mpr ⟨1, hone⟩
  have hcard : (S.card : ℝ) ≠ 0 := by exact_mod_cast hcardNat.ne'
  rw [inner_sub_right, IsKazhdanPair.orbitAverage, inner_smul_right, hsum]
  field_simp
  ring

/-- Kun's basic Hilbert-space estimate: after one averaging step, the
displacement from the original vector lies in the spectral-gap subspace, so
the next averaging step contracts that displacement by the Kazhdan factor. -/
theorem norm_orbitAverage_average_sub_le [CompleteSpace E]
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, v} G Q ε)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S) (hεone : ε ≤ 1)
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    ‖IsKazhdanPair.orbitAverage S ρ
        (IsKazhdanPair.orbitAverage S ρ x - x)‖ ≤
      (1 - ε ^ 2 / (4 * S.card)) *
        ‖IsKazhdanPair.orbitAverage S ρ x - x‖ := by
  apply norm_orbitAverage_le_of_mem_orthogonal hQ S hQS hone hεone ρ
  exact orbitAverage_sub_mem_orthogonal S hone ρ x

/-- Orbit averaging is additive with respect to subtraction. -/
theorem orbitAverage_sub (S : Finset G) (ρ : G →* (E ≃ₗᵢ[ℝ] E))
    (x y : E) :
    IsKazhdanPair.orbitAverage S ρ (x - y) =
      IsKazhdanPair.orbitAverage S ρ x -
        IsKazhdanPair.orbitAverage S ρ y := by
  classical
  simp [IsKazhdanPair.orbitAverage, Finset.sum_sub_distrib, smul_sub]

/-- Equivalent second-difference form of Kun's orbit-average estimate. -/
theorem norm_orbitAverage_sq_sub_le [CompleteSpace E]
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, v} G Q ε)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S) (hεone : ε ≤ 1)
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    ‖IsKazhdanPair.orbitAverage S ρ
        (IsKazhdanPair.orbitAverage S ρ x) -
      IsKazhdanPair.orbitAverage S ρ x‖ ≤
      (1 - ε ^ 2 / (4 * S.card)) *
        ‖IsKazhdanPair.orbitAverage S ρ x - x‖ := by
  rw [← orbitAverage_sub]
  exact norm_orbitAverage_average_sub_le hQ S hQS hone hεone ρ x

/-- The Kazhdan contraction iterates: successive orbit averages converge
geometrically, with the first displacement as scale.  This is the Hilbert
estimate used in Kun's finite rounding argument. -/
theorem norm_iterate_orbitAverage_succ_sub_le [CompleteSpace E]
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, v} G Q ε)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S) (hεone : ε ≤ 1)
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) (k : ℕ) :
    let A := IsKazhdanPair.orbitAverage S ρ
    ‖(A^[k + 1]) x - (A^[k]) x‖ ≤
      (1 - ε ^ 2 / (4 * S.card)) ^ k * ‖A x - x‖ := by
  let A := IsKazhdanPair.orbitAverage S ρ
  let c : ℝ := 1 - ε ^ 2 / (4 * S.card)
  have hcardNat : 0 < S.card := Finset.card_pos.mpr ⟨1, hone⟩
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hcardNat
  have hεsq : ε ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg ε, hQ.1, hεone]
  have hden : (0 : ℝ) < 4 * S.card := mul_pos (by norm_num) hcard
  have hcardOne : (1 : ℝ) ≤ S.card := by exact_mod_cast hcardNat
  have hdenOne : (1 : ℝ) ≤ 4 * S.card := by
    nlinarith
  have hfrac : ε ^ 2 / (4 * S.card) ≤ 1 := by
    rw [div_le_one hden]
    exact hεsq.trans hdenOne
  have hc : 0 ≤ c := by
    dsimp [c]
    linarith
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hstep := norm_orbitAverage_average_sub_le hQ S hQS hone hεone ρ
        ((A^[k]) x)
      rw [orbitAverage_sub] at hstep
      change ‖A (A ((A^[k]) x)) - A ((A^[k]) x)‖ ≤
        c * ‖A ((A^[k]) x) - (A^[k]) x‖ at hstep
      dsimp only at ih
      rw [show k + 1 = k.succ by omega, Function.iterate_succ_apply'] at ih
      change ‖A ((A^[k]) x) - (A^[k]) x‖ ≤
        c ^ k * ‖A x - x‖ at ih
      dsimp only
      simp only [Nat.add_one, Function.iterate_succ_apply']
      change ‖A (A ((A^[k]) x)) - A ((A^[k]) x)‖ ≤
        c ^ (k + 1) * ‖A x - x‖
      calc
        ‖A (A ((A^[k]) x)) - A ((A^[k]) x)‖ ≤
            c * ‖A ((A^[k]) x) - (A^[k]) x‖ := hstep
        _ ≤ c * (c ^ k * ‖A x - x‖) :=
          mul_le_mul_of_nonneg_left ih hc
        _ = c ^ (k + 1) * ‖A x - x‖ := by rw [pow_succ]; ring

end KazhdanOrthogonal
end NonsoficGroupsExist
