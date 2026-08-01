import NonsoficGroupsExist.FiniteGraph
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# A concrete median for a finite natural-valued observable

Component sizes are natural numbers.  Their median is chosen as the least
threshold containing at least half the vertices.  Minimality gives the lower
tail bound, while the defining threshold gives the upper tail bound.
-/

namespace NonsoficGroupsExist
namespace FiniteMultiGraph

variable {Y : FiniteModel}

def natMedianPredicate (s : Y → ℕ) (k : ℕ) : Prop :=
  Fintype.card Y ≤ 2 * (Finset.univ.filter fun y ↦ s y ≤ k).card

theorem exists_natMedianPredicate (s : Y → ℕ) :
    ∃ k, natMedianPredicate s k := by
  let B := ∑ y, s y
  refine ⟨B, ?_⟩
  have hfilter : (Finset.univ.filter fun y ↦ s y ≤ B) = Finset.univ := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hsum := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.singleton_subset_iff.mpr (Finset.mem_univ y))
        (fun _ _ _ ↦ Nat.zero_le _) (f := s)
    simpa using hsum
  rw [natMedianPredicate, hfilter, Finset.card_univ]
  omega

/-- The least natural threshold containing at least half the sample. -/
noncomputable def natMedian (s : Y → ℕ) : ℕ :=
  by
    classical
    exact Nat.find (exists_natMedianPredicate s)

theorem natMedian_spec (s : Y → ℕ) : natMedianPredicate s (natMedian s) :=
  by
    classical
    exact Nat.find_spec (exists_natMedianPredicate s)

/-- The least threshold is a median after coercion to `ℝ`. -/
theorem natMedian_isMedian (s : Y → ℕ) :
    IsMedian (fun y ↦ (s y : ℝ)) (natMedian s : ℝ) := by
  classical
  have hm := natMedian_spec s
  have hpartition :
      (Finset.univ.filter fun y ↦ s y ≤ natMedian s).card +
        (Finset.univ.filter fun y ↦ natMedian s < s y).card = Fintype.card Y := by
    simpa [not_le] using
      (Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (fun y : Y ↦ s y ≤ natMedian s))
  constructor
  · have hcast : (Finset.univ.filter fun y ↦ (natMedian s : ℝ) < (s y : ℝ)) =
        Finset.univ.filter fun y ↦ natMedian s < s y := by
      ext y
      simp
    rw [hcast]
    unfold natMedianPredicate at hm
    omega
  · by_cases hm0 : natMedian s = 0
    · have hempty :
          (Finset.univ.filter fun y ↦ (s y : ℝ) < (natMedian s : ℝ)) = ∅ := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.notMem_empty, iff_false]
        rw [hm0]
        apply not_lt_of_ge
        exact_mod_cast Nat.zero_le (s y)
      rw [hempty]
      simp
    · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hm0
      have hminimal : ¬ natMedianPredicate s k := by
        intro hkpred
        have hle := Nat.find_min' (exists_natMedianPredicate s) hkpred
        have hk' : Nat.find (exists_natMedianPredicate s) = k.succ := by
          simpa [natMedian] using hk
        rw [hk'] at hle
        omega
      have hcast :
          (Finset.univ.filter fun y ↦ ((s y : ℕ) : ℝ) < ((k + 1 : ℕ) : ℝ)) =
            Finset.univ.filter fun y ↦ s y ≤ k := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        norm_cast
        omega
      rw [hk]
      rw [hcast]
      unfold natMedianPredicate at hminimal
      omega

end FiniteMultiGraph
end NonsoficGroupsExist
