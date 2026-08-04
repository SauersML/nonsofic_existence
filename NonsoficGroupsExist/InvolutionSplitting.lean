import NonsoficGroupsExist.Kazhdan
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Explicit splitting by an orthogonal involution

Over the characteristic-two additive root planes, every represented group
element is an orthogonal involution.  This file constructs its `+1` and `-1`
parts directly, proves the orthogonal Pythagorean splitting, and proves
covariance under conjugation.  These formulas work in arbitrary complete or
incomplete real inner-product spaces; no finite-dimensional spectral theorem
is used.
-/

namespace NonsoficGroupsExist

universe u v

namespace InvolutionSplitting

variable {G : Type u} [Group G]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The `+1` piece of a vector for a represented group element. -/
noncomputable def positivePart
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (c : G) (z : E) : E :=
  (2 : ℝ)⁻¹ • (z + rho c z)

/-- The `-1` piece of a vector for a represented group element. -/
noncomputable def negativePart
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (c : G) (z : E) : E :=
  (2 : ℝ)⁻¹ • (z - rho c z)

theorem positivePart_add_negativePart
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (c : G) (z : E) :
    positivePart rho c z + negativePart rho c z = z := by
  simp only [positivePart, negativePart, ← smul_add]
  module

theorem action_sq (rho : G →* (E ≃ₗᵢ[ℝ] E))
    {c : G} (hc : c ^ 2 = 1) (z : E) :
    rho c (rho c z) = z := by
  calc
    rho c (rho c z) = rho (c * c) z := by
      change (rho c * rho c) z = rho (c * c) z
      rw [← map_mul]
    _ = z := by rw [← pow_two, hc]; simp

theorem action_positivePart
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) {c : G} (hc : c ^ 2 = 1) (z : E) :
    rho c (positivePart rho c z) = positivePart rho c z := by
  simp only [positivePart, map_smul, map_add, action_sq rho hc]
  rw [add_comm]

theorem action_negativePart
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) {c : G} (hc : c ^ 2 = 1) (z : E) :
    rho c (negativePart rho c z) = -negativePart rho c z := by
  simp only [negativePart, map_smul, map_sub, action_sq rho hc]
  rw [show rho c z - z = -(z - rho c z) by abel, smul_neg]

theorem positivePart_idem
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) {c : G} (hc : c ^ 2 = 1) (z : E) :
    positivePart rho c (positivePart rho c z) = positivePart rho c z := by
  rw [positivePart, action_positivePart rho hc]
  module

theorem negativePart_idem
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) {c : G} (hc : c ^ 2 = 1) (z : E) :
    negativePart rho c (negativePart rho c z) = negativePart rho c z := by
  rw [negativePart, action_negativePart rho hc]
  module

theorem positivePart_negativePart_eq_zero
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) {c : G} (hc : c ^ 2 = 1) (z : E) :
    positivePart rho c (negativePart rho c z) = 0 := by
  rw [positivePart, action_negativePart rho hc]
  module

theorem negativePart_positivePart_eq_zero
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) {c : G} (hc : c ^ 2 = 1) (z : E) :
    negativePart rho c (positivePart rho c z) = 0 := by
  rw [negativePart, action_positivePart rho hc]
  module

/-- Positive splitting operators commute for commuting group elements. -/
theorem positivePart_commute
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) {c d : G} (hcd : Commute c d) (z : E) :
    positivePart rho c (positivePart rho d z) =
      positivePart rho d (positivePart rho c z) := by
  have haction : rho c (rho d z) = rho d (rho c z) := by
    calc
      rho c (rho d z) = rho (c * d) z := by
        change (rho c * rho d) z = rho (c * d) z
        rw [← map_mul]
      _ = rho (d * c) z := by rw [hcd.eq]
      _ = rho d (rho c z) := by rw [map_mul]; rfl
  simp only [positivePart, map_smul, map_add]
  rw [haction]
  module

/-- Negative splitting operators commute for commuting group elements. -/
theorem negativePart_commute
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) {c d : G} (hcd : Commute c d) (z : E) :
    negativePart rho c (negativePart rho d z) =
      negativePart rho d (negativePart rho c z) := by
  have haction : rho c (rho d z) = rho d (rho c z) := by
    calc
      rho c (rho d z) = rho (c * d) z := by
        change (rho c * rho d) z = rho (c * d) z
        rw [← map_mul]
      _ = rho (d * c) z := by rw [hcd.eq]
      _ = rho d (rho c z) := by rw [map_mul]; rfl
  simp only [negativePart, map_smul, map_sub]
  rw [haction]
  module

/-- Positive and negative splitting operators commute across commuting group
elements. -/
theorem positivePart_negativePart_commute
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) {c d : G} (hcd : Commute c d) (z : E) :
    positivePart rho c (negativePart rho d z) =
      negativePart rho d (positivePart rho c z) := by
  have haction : rho c (rho d z) = rho d (rho c z) := by
    calc
      rho c (rho d z) = rho (c * d) z := by
        change (rho c * rho d) z = rho (c * d) z
        rw [← map_mul]
      _ = rho (d * c) z := by rw [hcd.eq]
      _ = rho d (rho c z) := by rw [map_mul]; rfl
  simp only [positivePart, negativePart, map_smul, map_add, map_sub]
  rw [haction]
  module

/-- An orthogonal involution is symmetric. -/
theorem inner_action_left_eq_right
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) {c : G} (hc : c ^ 2 = 1) (x y : E) :
    inner ℝ (rho c x) y = inner ℝ x (rho c y) := by
  calc
    inner ℝ (rho c x) y =
        inner ℝ (rho c x) (rho c (rho c y)) := by
      rw [action_sq rho hc]
    _ = inner ℝ x (rho c y) := (rho c).inner_map_map _ _

/-- The positive and negative pieces are orthogonal. -/
theorem inner_positivePart_negativePart
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) {c : G} (hc : c ^ 2 = 1) (z : E) :
    inner ℝ (positivePart rho c z) (negativePart rho c z) = 0 := by
  simp only [positivePart, negativePart, inner_smul_left, inner_smul_right]
  have hsymm := inner_action_left_eq_right rho hc z z
  have hiso := (rho c).inner_map_map z z
  simp only [inner_add_left, inner_sub_right]
  rw [hsymm, hiso]
  ring

/-- Squared norms split exactly across the two eigenspace pieces. -/
theorem norm_positivePart_sq_add_norm_negativePart_sq
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) {c : G} (hc : c ^ 2 = 1) (z : E) :
    ‖positivePart rho c z‖ ^ 2 + ‖negativePart rho c z‖ ^ 2 = ‖z‖ ^ 2 := by
  calc
    ‖positivePart rho c z‖ ^ 2 + ‖negativePart rho c z‖ ^ 2 =
        ‖positivePart rho c z + negativePart rho c z‖ ^ 2 := by
      symm
      simpa [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_real
        (inner_positivePart_negativePart rho hc z)
    _ = ‖z‖ ^ 2 := by rw [positivePart_add_negativePart]

/-- The negative piece is exactly half the displacement by the involution. -/
theorem negativePart_eq_neg_half_smul_displacement
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (c : G) (z : E) :
    negativePart rho c z =
      -(2 : ℝ)⁻¹ • (rho c z - z) := by
  rw [negativePart, show z - rho c z = -(rho c z - z) by abel]
  simp only [smul_neg, neg_smul]

/-- Positive splitting is covariant under conjugation. -/
theorem map_positivePart
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (g c : G) (z : E) :
    rho g (positivePart rho c z) =
      positivePart rho (g * c * g⁻¹) (rho g z) := by
  have haction : rho g (rho c z) = rho (g * c * g⁻¹) (rho g z) := by
    calc
      rho g (rho c z) = rho (g * c) z := by
        change (rho g * rho c) z = rho (g * c) z
        rw [← map_mul]
      _ = rho ((g * c * g⁻¹) * g) z := by group
      _ = rho (g * c * g⁻¹) (rho g z) := by rw [map_mul]; rfl
  unfold positivePart
  rw [map_smul, map_add, haction]

/-- Negative splitting is covariant under conjugation. -/
theorem map_negativePart
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (g c : G) (z : E) :
    rho g (negativePart rho c z) =
      negativePart rho (g * c * g⁻¹) (rho g z) := by
  have haction : rho g (rho c z) = rho (g * c * g⁻¹) (rho g z) := by
    calc
      rho g (rho c z) = rho (g * c) z := by
        change (rho g * rho c) z = rho (g * c) z
        rw [← map_mul]
      _ = rho ((g * c * g⁻¹) * g) z := by group
      _ = rho (g * c * g⁻¹) (rho g z) := by rw [map_mul]; rfl
  unfold negativePart
  rw [map_smul, map_sub, haction]

end InvolutionSplitting

end NonsoficGroupsExist
