import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Permutation conservation

This is Lemma `lem:conserve` of the manuscript.  It is the exact identity
which turns one-sided drift into two-sided `L¹` variation.
-/

namespace NonsoficGroupsExist

open scoped BigOperators

theorem sum_comp_equiv {Y : Type*} [Fintype Y] (π : Y ≃ Y) (f : Y → ℝ) :
    ∑ y, f (π y) = ∑ y, f y := by
  exact Equiv.sum_comp π f

theorem permutation_conservation {Y : Type*} [Fintype Y]
    (π : Y ≃ Y) (f : Y → ℝ) :
    ∑ y, max (f y - f (π y)) 0 =
      ∑ y, max (f (π y) - f y) 0 := by
  have hzero : ∑ y, (f y - f (π y)) = 0 := by
    rw [Finset.sum_sub_distrib, sum_comp_equiv]
    simp
  calc
    ∑ y, max (f y - f (π y)) 0
        = ∑ y, (max (f (π y) - f y) 0 + (f y - f (π y))) := by
            apply Finset.sum_congr rfl
            intro y _
            rcases le_total (f y) (f (π y)) with h | h <;> simp [h]
    _ = (∑ y, max (f (π y) - f y) 0) +
          ∑ y, (f y - f (π y)) := by
            rw [Finset.sum_add_distrib]
    _ = ∑ y, max (f (π y) - f y) 0 := by rw [hzero, add_zero]

theorem permutation_conservation_abs {Y : Type*} [Fintype Y]
    (π : Y ≃ Y) (f : Y → ℝ) :
    ∑ y, |f (π y) - f y| =
      2 * ∑ y, max (f y - f (π y)) 0 := by
  have h := permutation_conservation π f
  calc
    ∑ y, |f (π y) - f y|
        = ∑ y, (max (f (π y) - f y) 0 +
            max (f y - f (π y)) 0) := by
              apply Finset.sum_congr rfl
              intro y _
              rcases le_total (f y) (f (π y)) with hle | hle
              · have hpos : 0 ≤ f (π y) - f y := sub_nonneg.mpr hle
                have hneg : f y - f (π y) ≤ 0 := sub_nonpos.mpr hle
                rw [abs_of_nonneg hpos]
                simp [hpos, hneg]
              · have hneg : f (π y) - f y ≤ 0 := sub_nonpos.mpr hle
                have hpos : 0 ≤ f y - f (π y) := sub_nonneg.mpr hle
                rw [abs_of_nonpos hneg]
                simp [hpos, hneg]
    _ = (∑ y, max (f (π y) - f y) 0) +
          ∑ y, max (f y - f (π y)) 0 := by
            rw [Finset.sum_add_distrib]
    _ = 2 * ∑ y, max (f y - f (π y)) 0 := by rw [← h]; ring

end NonsoficGroupsExist
