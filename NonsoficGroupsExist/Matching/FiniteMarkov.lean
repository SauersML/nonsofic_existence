import NonsoficGroupsExist.Matching.BlockIndex
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite Markov bounds

These elementary counting inequalities turn the global `ℓ¹` pinning estimate
into a negligible set of bad vertices and then into a negligible mass of bad
components.
-/

namespace NonsoficGroupsExist

open scoped BigOperators

variable {Y : FiniteModel}

/-- Finite Markov inequality, with real-valued weights. -/
theorem threshold_mul_card_le_sum (f : Y → ℝ) (hf : ∀ x, 0 ≤ f x)
    {η : ℝ} (_hη : 0 ≤ η) :
    η * ((Finset.univ.filter fun x ↦ η < f x).card : ℝ) ≤ ∑ x, f x := by
  calc
    η * ((Finset.univ.filter fun x ↦ η < f x).card : ℝ) =
        (Finset.univ.filter fun x ↦ η < f x).sum (fun _ ↦ η) := by
      simp [mul_comm]
    _ ≤ (Finset.univ.filter fun x ↦ η < f x).sum f := by
      apply Finset.sum_le_sum
      intro x hx
      exact (Finset.mem_filter.mp hx).2.le
    _ ≤ ∑ x, f x := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ ↦ hf _)

/-- Components whose assigned nonnegative error is at least an `η` fraction
of their size carry at most `totalError / η` mass. -/
theorem threshold_mul_badBlockMass_le
    (P : BlockStructure Y) (e : BlockIndex P → ℝ)
    (he : ∀ B, 0 ≤ e B) {η : ℝ} (_hη : 0 ≤ η) :
    η * (Finset.univ.filter (fun B : BlockIndex P ↦
        η * B.block.card ≤ e B)).sum (fun B ↦ (B.block.card : ℝ)) ≤
      ∑ B, e B := by
  calc
    η * (Finset.univ.filter (fun B : BlockIndex P ↦
        η * B.block.card ≤ e B)).sum (fun B ↦ (B.block.card : ℝ)) =
      (Finset.univ.filter (fun B : BlockIndex P ↦
        η * B.block.card ≤ e B)).sum (fun B ↦ η * B.block.card) := by
          rw [Finset.mul_sum]
    _ ≤ (Finset.univ.filter (fun B : BlockIndex P ↦
        η * B.block.card ≤ e B)).sum e := by
          apply Finset.sum_le_sum
          intro B hB
          exact (Finset.mem_filter.mp hB).2
    _ ≤ ∑ B, e B := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ ↦ he _)

end NonsoficGroupsExist
