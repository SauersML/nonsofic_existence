import NonsoficGroupsExist.Leavitt.FamilyDiagonalClass

/-!
# Unstable descent through any complete matrix family

The full-strength descent for the rose-graph `K₁` computation, at every
matrix size at once: through a complete matrix family the whole
elementary group pulls back into the diagonal class group (each
generator becomes a unipotent), and the diagonal matrix with a single
unit slot pulls back to the corner insertion `pairKappaUnit`, which is
congruent to the unit itself.  Hence if `diag(u, 1, …, 1)` is a product
of elementary matrices at any size identified with the base ring —
in particular at size `2^m` for a binary Leavitt ring — then `u` lies
in the diagonal class group.  This upgrades the one-step `M₂` descent
of `DiagonalDescent` to arbitrary complete families.
-/

namespace NonsoficGroupsExist
namespace CompleteMatrixFamily

open MatrixDiagonalization

variable {A : Type*} [Ring A] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (F : CompleteMatrixFamily A ι)

/-- The elementary group pulls back into the diagonal class group. -/
theorem unitsEquiv_elementaryGroup_mem_stableUnits
    {E : (Matrix ι ι A)ˣ} (hE : E ∈ elementaryGroup ι A) :
    F.unitsEquiv E ∈ stableUnits A := by
  induction hE using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, j, hij, a, rfl⟩ := hx
      exact F.unitsEquiv_unipotent_mem_stableUnits hij a _ rfl
  | one => rw [map_one]; exact one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  | inv x _ hx => rw [map_inv]; exact inv_mem hx

/-- The diagonal matrix with a single unit slot. -/
def cornerDiagUnit (i₀ : ι) (u : Aˣ) : (Matrix ι ι A)ˣ where
  val := Matrix.diagonal fun j ↦ if j = i₀ then (u : A) else 1
  inv := Matrix.diagonal fun j ↦ if j = i₀ then ((u⁻¹ : Aˣ) : A) else 1
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    have hfun : (fun j ↦ (if j = i₀ then (u : A) else 1) *
        (if j = i₀ then ((u⁻¹ : Aˣ) : A) else 1)) = fun _ ↦ (1 : A) := by
      funext j
      by_cases h : j = i₀ <;> simp [h]
    rw [hfun, Matrix.diagonal_one]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    have hfun : (fun j ↦ (if j = i₀ then ((u⁻¹ : Aˣ) : A) else 1) *
        (if j = i₀ then (u : A) else 1)) = fun _ ↦ (1 : A) := by
      funext j
      by_cases h : j = i₀ <;> simp [h]
    rw [hfun, Matrix.diagonal_one]

/-- Through the family identification, the single-slot diagonal is the
corner insertion. -/
theorem unitsEquiv_cornerDiagUnit (i₀ : ι) (u : Aˣ) :
    F.unitsEquiv (cornerDiagUnit i₀ u) =
      pairKappaUnit (F.left i₀) (F.right i₀)
        (F.right_mul_left_self i₀) u := by
  apply Units.ext
  rw [unitsEquiv_apply_val]
  show F.matrixRingEquiv
      (Matrix.diagonal fun j ↦ if j = i₀ then (u : A) else 1) = _
  rw [F.matrixRingEquiv_diagonal, pairKappaUnit_val]
  have hsplit : ∀ j : ι,
      F.left j * (if j = i₀ then (u : A) else 1) * F.right j =
        (if j = i₀ then
          F.left i₀ * (u : A) * F.right i₀ - F.left i₀ * F.right i₀
        else 0) + F.left j * F.right j := by
    intro j
    by_cases h : j = i₀
    · subst h
      rw [if_pos rfl, if_pos rfl]
      abel
    · rw [if_neg h, if_neg h, mul_one, zero_add]
  rw [Finset.sum_congr rfl fun j _ ↦ hsplit j, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ i₀
      (fun _ ↦ F.left i₀ * (u : A) * F.right i₀ - F.left i₀ * F.right i₀),
    if_pos (Finset.mem_univ i₀), F.complete]
  abel

include F in
/-- **Unstable descent at every size**: if the single-slot diagonal of
`u` is elementary at any size identified with the base ring, then `u`
lies in the diagonal class group. -/
theorem mem_stableUnits_of_cornerDiag_mem [Nontrivial A]
    (hdiv : ∀ x : A, x ≠ 0 → ∃ p q : A, p * x * q = 1) (i₀ : ι) (u : Aˣ)
    (h : cornerDiagUnit i₀ u ∈ elementaryGroup ι A) :
    u ∈ stableUnits A := by
  have h1 := F.unitsEquiv_elementaryGroup_mem_stableUnits h
  rw [F.unitsEquiv_cornerDiagUnit] at h1
  have hco := pairKappaUnit_mul_inv_mem_stableUnits (F.left i₀)
    (F.right i₀) (F.right_mul_left_self i₀) hdiv u
  have hmul := mul_mem (inv_mem hco) h1
  rwa [show (pairKappaUnit (F.left i₀) (F.right i₀)
      (F.right_mul_left_self i₀) u * u⁻¹)⁻¹ *
      pairKappaUnit (F.left i₀) (F.right i₀)
        (F.right_mul_left_self i₀) u = u from by group] at hmul

end CompleteMatrixFamily
end NonsoficGroupsExist
