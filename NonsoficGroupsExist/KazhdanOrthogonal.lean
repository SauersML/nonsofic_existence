import NonsoficGroupsExist.Kazhdan
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

end KazhdanOrthogonal
end NonsoficGroupsExist
