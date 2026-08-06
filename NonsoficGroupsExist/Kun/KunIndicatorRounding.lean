import NonsoficGroupsExist.Kun.KunGeneratorGraph

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

/-- The product of an indicator iterate norm and the initial displacement is
at most twice the initial cardinality. -/
theorem norm_indicatorIterate_mul_initialDisplacement_le_two_card
    (A : SoficApproximation G) (n : ℕ) (U : Finset (A.model n))
    (S : Finset G) (hS : S.Nonempty) (k : ℕ) :
    ‖finiteModelIndicatorIterate A n U S k‖ *
        ‖finiteModelIndicatorIterate A n U S 1 -
          finiteModelIndicatorIterate A n U S 0‖ ≤
      2 * U.card := by
  let x := ‖finiteModelIndicatorIterate A n U S k‖
  let d := ‖finiteModelIndicatorIterate A n U S 1 -
    finiteModelIndicatorIterate A n U S 0‖
  let m : ℝ := U.card
  have hxSq : x ^ 2 ≤ m := by
    simpa [x, m] using
      norm_finiteModelIndicatorIterate_sq_le_card A n U S hS k
  have hdSq : d ^ 2 ≤ 2 * m := by
    simpa [d, m, finiteModelIndicatorIterate] using
      norm_finiteModelAverage_indicator_sub_sq_le_two_card
        (A.model n) (A.map n) S hS U
  have hm0 : 0 ≤ m := by positivity
  have hprodSq : (x * d) ^ 2 ≤ (2 * m) ^ 2 := by
    calc
      (x * d) ^ 2 = x ^ 2 * d ^ 2 := by ring
      _ ≤ m * d ^ 2 := mul_le_mul_of_nonneg_right hxSq (sq_nonneg d)
      _ ≤ m * (2 * m) := mul_le_mul_of_nonneg_left hdSq hm0
      _ ≤ (2 * m) ^ 2 := by nlinarith [sq_nonneg m]
  have hx0 : 0 ≤ x := norm_nonneg _
  have hd0 : 0 ≤ d := norm_nonneg _
  have hright : 0 ≤ 2 * m := by positivity
  exact (sq_le_sq₀ (mul_nonneg hx0 hd0) hright).mp hprodSq

/-- A multiplicative contraction of the last displacement gives a boundary
quadratic in the input cardinality. -/
theorem exists_threshold_boundary_sq_of_contraction
    (A : SoficApproximation G) (n : ℕ) (U : Finset (A.model n))
    (S : Finset G) (hS : S.Nonempty) (k : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (hdisp : ‖finiteModelIndicatorIterate A n U S (k + 1) -
        finiteModelIndicatorIterate A n U S k‖ ≤
      c * ‖finiteModelIndicatorIterate A n U S 1 -
        finiteModelIndicatorIterate A n U S 0‖) :
    ∃ t : ℝ, (1 : ℝ) / 3 < t ∧ t < (2 : ℝ) / 3 ∧
      ((1 : ℝ) / 3) * ((2 : ℝ) / 3 - (1 : ℝ) / 3) ^ 2 *
          ((generatorGraph (A.model n) S (A.map n)).boundaryCard
            ((generatorGraph (A.model n) S (A.map n)).superlevel
              (finiteModelIndicatorIterate A n U S k) t) : ℝ) ^ 2 ≤
        8 * (S.card : ℝ) ^ 2 * c * (U.card : ℝ) ^ 2 := by
  obtain ⟨t, ht0, ht1, ht⟩ :=
    exists_threshold_indicatorIterate_boundary_sq A n U S hS k
  have hprod := norm_indicatorIterate_mul_initialDisplacement_le_two_card
    A n U S hS k
  have hnorm : 0 ≤ ‖finiteModelIndicatorIterate A n U S k‖ := norm_nonneg _
  refine ⟨t, ht0, ht1, ht.trans ?_⟩
  calc
    4 * (S.card : ℝ) ^ 2 * U.card *
        ‖finiteModelIndicatorIterate A n U S k‖ *
        ‖finiteModelIndicatorIterate A n U S (k + 1) -
          finiteModelIndicatorIterate A n U S k‖ ≤
      4 * (S.card : ℝ) ^ 2 * U.card *
        ‖finiteModelIndicatorIterate A n U S k‖ *
        (c * ‖finiteModelIndicatorIterate A n U S 1 -
          finiteModelIndicatorIterate A n U S 0‖) := by
      gcongr
    _ = 4 * (S.card : ℝ) ^ 2 * c * U.card *
        (‖finiteModelIndicatorIterate A n U S k‖ *
          ‖finiteModelIndicatorIterate A n U S 1 -
            finiteModelIndicatorIterate A n U S 0‖) := by ring
    _ ≤ 4 * (S.card : ℝ) ^ 2 * c * U.card * (2 * U.card) := by
      gcongr
    _ = 8 * (S.card : ℝ) ^ 2 * c * (U.card : ℝ) ^ 2 := by ring

/-- If the initial displacement is already small relative to the indicator,
thresholding at time zero gives an even sharper boundary estimate. -/
theorem exists_threshold_boundary_sq_of_small_initial
    (A : SoficApproximation G) (n : ℕ) (U : Finset (A.model n))
    (S : Finset G) (hS : S.Nonempty) (α : ℝ)
    (hdisp : ‖finiteModelIndicatorIterate A n U S 1 -
        finiteModelIndicatorIterate A n U S 0‖ ≤ α * ‖indicator U‖) :
    ∃ t : ℝ, (1 : ℝ) / 3 < t ∧ t < (2 : ℝ) / 3 ∧
      ((1 : ℝ) / 3) * ((2 : ℝ) / 3 - (1 : ℝ) / 3) ^ 2 *
          ((generatorGraph (A.model n) S (A.map n)).boundaryCard
            ((generatorGraph (A.model n) S (A.map n)).superlevel
              (finiteModelIndicatorIterate A n U S 0) t) : ℝ) ^ 2 ≤
        4 * (S.card : ℝ) ^ 2 * α * (U.card : ℝ) ^ 2 := by
  obtain ⟨t, ht0, ht1, ht⟩ :=
    exists_threshold_indicatorIterate_boundary_sq A n U S hS 0
  have hnorm : 0 ≤ ‖indicator U‖ := norm_nonneg _
  have hdisp' : ‖finiteModelIndicatorIterate A n U S 1 - indicator U‖ ≤
      α * ‖indicator U‖ := by
    simpa [finiteModelIndicatorIterate] using hdisp
  refine ⟨t, ht0, ht1, ht.trans ?_⟩
  simp only [finiteModelIndicatorIterate, Function.iterate_zero_apply] at ht ⊢
  calc
    4 * (S.card : ℝ) ^ 2 * U.card * ‖indicator U‖ *
        ‖finiteModelIndicatorIterate A n U S 1 - indicator U‖ ≤
      4 * (S.card : ℝ) ^ 2 * U.card * ‖indicator U‖ *
        (α * ‖indicator U‖) := by
      gcongr
    _ = 4 * (S.card : ℝ) ^ 2 * α * U.card * ‖indicator U‖ ^ 2 := by ring
    _ = 4 * (S.card : ℝ) ^ 2 * α * (U.card : ℝ) ^ 2 := by
      rw [norm_indicator_sq]
      ring

end KunIndicatorRounding
end NonsoficGroupsExist
