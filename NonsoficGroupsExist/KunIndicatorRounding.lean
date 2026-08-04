import NonsoficGroupsExist.KunGeneratorGraph

/-!
# Kun rounding for finite-model indicator trajectories

This module specializes the finite coarea and Dirichlet-form estimates to the
actual Markov iterates of a sofic permutation model.
-/

namespace NonsoficGroupsExist
namespace KunIndicatorRounding

open KazhdanFiniteModel
open KazhdanGNS
open KunGeneratorGraph
open FiniteMultiGraph

variable {G : Type} [Group G]

/-- A threshold between `1/3` and `2/3` whose generator-graph boundary is
controlled by the last Markov displacement. -/
theorem exists_threshold_indicatorIterate_boundary_sq
    (A : SoficApproximation G) (n : ℕ) (U : Finset (A.model n))
    (S : Finset G) (hS : S.Nonempty) (k : ℕ) :
    ∃ t : ℝ, (1 : ℝ) / 3 < t ∧ t < (2 : ℝ) / 3 ∧
      ((1 : ℝ) / 3) * ((2 : ℝ) / 3 - (1 : ℝ) / 3) ^ 2 *
          ((generatorGraph (A.model n) S (A.map n)).boundaryCard
            ((generatorGraph (A.model n) S (A.map n)).superlevel
              (finiteModelIndicatorIterate A n U S k) t) : ℝ) ^ 2 ≤
        4 * (S.card : ℝ) ^ 2 * U.card *
          ‖finiteModelIndicatorIterate A n U S k‖ *
          ‖finiteModelIndicatorIterate A n U S (k + 1) -
            finiteModelIndicatorIterate A n U S k‖ := by
  have hf (y : A.model n) :
      0 ≤ finiteModelIndicatorIterate A n U S k y :=
    (finiteModelIndicatorIterate_between_zero_one A n U S hS k y).1
  obtain ⟨t, ht0, ht1, ht⟩ :=
    exists_generatorGraph_boundary_sq_le_markov
      (A.model n) S hS (A.map n)
      (finiteModelIndicatorIterate A n U S k)
      ((1 : ℝ) / 3) ((2 : ℝ) / 3) (by norm_num) (by norm_num) hf
  refine ⟨t, ht0, ht1, ?_⟩
  rw [sum_finiteModelIndicatorIterate A n U S hS k] at ht
  simpa [finiteModelIndicatorIterate_succ] using ht

end KunIndicatorRounding
end NonsoficGroupsExist
