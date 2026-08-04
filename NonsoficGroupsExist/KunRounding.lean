import NonsoficGroupsExist.KunBoundary

/-!
# Finite threshold rounding for Kun's argument

This module formalizes the deterministic rounding estimates that turn a
Markov-smoothed characteristic function back into a nearby vertex set.
-/

namespace NonsoficGroupsExist
namespace KunRounding

open KazhdanFiniteModel
open KazhdanGNS
open scoped symmDiff

variable {Y : FiniteModel}

/-- Strict superlevel set of a finite real-valued function. -/
noncomputable def superlevelSet (f : Y → ℝ) (t : ℝ) : Finset Y :=
  Finset.univ.filter fun y ↦ t < f y

/-- Thresholding between `1/3` and `2/3` changes a characteristic function
on at most nine times its squared `ℓ²` error. -/
theorem card_superlevelSet_symmDiff_le
    (f : EuclideanSpace ℝ Y) (U : Finset Y) (t : ℝ)
    (ht0 : (1 : ℝ) / 3 < t) (ht1 : t < (2 : ℝ) / 3) :
    (((superlevelSet f t) ∆ U).card : ℝ) ≤
      9 * ‖f - indicator U‖ ^ 2 := by
  classical
  let D := (superlevelSet f t) ∆ U
  have hpoint (y : Y) (hy : y ∈ D) :
      (1 : ℝ) ≤ 9 * (f y - indicator U y) ^ 2 := by
    have hy' := hy
    simp only [D, Finset.mem_symmDiff] at hy'
    rcases hy' with ⟨hyLevel, hyU⟩ | ⟨hyU, hyLevel⟩
    · have hfy : t < f y := by
        simpa [superlevelSet] using hyLevel
      simp only [indicator_apply, if_neg hyU]
      nlinarith [sq_nonneg (f y - 1 / 3)]
    · have hfy : f y ≤ t := by
        have : ¬ t < f y := by
          simpa [superlevelSet] using hyLevel
        exact not_lt.mp this
      simp only [indicator_apply, if_pos hyU]
      nlinarith [sq_nonneg (f y - 2 / 3)]
  calc
    (D.card : ℝ) = ∑ y ∈ D, (1 : ℝ) := by simp
    _ ≤ ∑ y ∈ D, 9 * (f y - indicator U y) ^ 2 :=
      Finset.sum_le_sum fun y hy ↦ hpoint y hy
    _ ≤ ∑ y : Y, 9 * (f y - indicator U y) ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ D)
        (fun _ _ _ ↦ mul_nonneg (by norm_num) (sq_nonneg _))
    _ = 9 * ‖f - indicator U‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
      rfl

/-- Telescoping bound for an arbitrary iterated self-map in a seminormed
additive group. -/
theorem norm_iterate_sub_le_sum {E : Type*} [SeminormedAddCommGroup E]
    (F : E → E) (x : E) (k : ℕ) :
    ‖(F^[k]) x - x‖ ≤
      ∑ i ∈ Finset.range k, ‖(F^[i + 1]) x - (F^[i]) x‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hdecomp :
          (F^[k + 1]) x - x =
            ((F^[k + 1]) x - (F^[k]) x) + ((F^[k]) x - x) := by
        abel
      rw [hdecomp]
      calc
        ‖(F^[k + 1]) x - (F^[k]) x + ((F^[k]) x - x)‖ ≤
            ‖(F^[k + 1]) x - (F^[k]) x‖ + ‖(F^[k]) x - x‖ :=
          norm_add_le _ _
        _ ≤ ‖(F^[k + 1]) x - (F^[k]) x‖ +
            ∑ i ∈ Finset.range k,
              ‖(F^[i + 1]) x - (F^[i]) x‖ :=
          add_le_add_right ih _
        _ = ∑ i ∈ Finset.range (k + 1),
            ‖(F^[i + 1]) x - (F^[i]) x‖ := by
          rw [Finset.sum_range_succ]
          abel

/-- Telescoping bound for the concrete finite-model indicator trajectory. -/
theorem norm_finiteModelIndicatorIterate_sub_le_sum
    {G : Type*} [Group G] (A : SoficApproximation G) (n : ℕ)
    (U : Finset (A.model n)) (S : Finset G) (k : ℕ) :
    ‖finiteModelIndicatorIterate A n U S k - indicator U‖ ≤
      ∑ i ∈ Finset.range k,
        ‖finiteModelIndicatorIterate A n U S (i + 1) -
          finiteModelIndicatorIterate A n U S i‖ := by
  exact norm_iterate_sub_le_sum
    (finiteModelAverage (A.model n) (A.map n) S) (indicator U) k

/-- A `k`-step indicator trajectory moves at most `k` times its initial
one-step displacement. -/
theorem norm_finiteModelIndicatorIterate_sub_le
    {G : Type*} [Group G] (A : SoficApproximation G) (n : ℕ)
    (U : Finset (A.model n)) (S : Finset G) (hS : S.Nonempty) (k : ℕ) :
    ‖finiteModelIndicatorIterate A n U S k - indicator U‖ ≤
      k * ‖finiteModelIndicatorIterate A n U S 1 -
        finiteModelIndicatorIterate A n U S 0‖ := by
  calc
    ‖finiteModelIndicatorIterate A n U S k - indicator U‖ ≤
        ∑ i ∈ Finset.range k,
          ‖finiteModelIndicatorIterate A n U S (i + 1) -
            finiteModelIndicatorIterate A n U S i‖ :=
      norm_finiteModelIndicatorIterate_sub_le_sum A n U S k
    _ ≤ ∑ _i ∈ Finset.range k,
        ‖finiteModelIndicatorIterate A n U S 1 -
          finiteModelIndicatorIterate A n U S 0‖ :=
      Finset.sum_le_sum fun i hi ↦
        norm_finiteModelIndicatorIterate_displacement_le_initial
          A n U S hS i
    _ = k * ‖finiteModelIndicatorIterate A n U S 1 -
        finiteModelIndicatorIterate A n U S 0‖ := by simp

/-- The thresholded `k`-step indicator trajectory remains close to its input
whenever the trajectory itself has small telescoping displacement. -/
theorem card_thresholdedIndicatorIterate_symmDiff_le
    {G : Type*} [Group G] (A : SoficApproximation G) (n : ℕ)
    (U : Finset (A.model n)) (S : Finset G) (k : ℕ) (t : ℝ)
    (ht0 : (1 : ℝ) / 3 < t) (ht1 : t < (2 : ℝ) / 3) :
    (((superlevelSet (finiteModelIndicatorIterate A n U S k) t) ∆ U).card : ℝ) ≤
      9 * ‖finiteModelIndicatorIterate A n U S k - indicator U‖ ^ 2 :=
  card_superlevelSet_symmDiff_le
    (finiteModelIndicatorIterate A n U S k) U t ht0 ht1

/-- Quantitative proximity of the thresholded set, expressed directly in
terms of the input generator cut. -/
theorem card_thresholdedIndicatorIterate_symmDiff_le_cut
    {G : Type*} [Group G] (A : SoficApproximation G) (n : ℕ)
    (U : Finset (A.model n)) (S : Finset G) (hS : S.Nonempty)
    (k : ℕ) (t : ℝ) (ht0 : (1 : ℝ) / 3 < t)
    (ht1 : t < (2 : ℝ) / 3) :
    (((superlevelSet (finiteModelIndicatorIterate A n U S k) t) ∆ U).card : ℝ) ≤
      9 * k ^ 2 * (S.card : ℝ)⁻¹ *
        generatorCutSize (A.model n) (A.map n) S U := by
  have hpath := norm_finiteModelIndicatorIterate_sub_le A n U S hS k
  have hright : 0 ≤ (k : ℝ) *
      ‖finiteModelIndicatorIterate A n U S 1 -
        finiteModelIndicatorIterate A n U S 0‖ := by positivity
  have hpathSq := (sq_le_sq₀ (norm_nonneg _) hright).2 hpath
  have hinitial :
      ‖finiteModelIndicatorIterate A n U S 1 -
          finiteModelIndicatorIterate A n U S 0‖ ^ 2 ≤
        (S.card : ℝ)⁻¹ *
          generatorCutSize (A.model n) (A.map n) S U := by
    simpa [finiteModelIndicatorIterate] using
      norm_finiteModelAverage_indicator_sub_sq_le
        (A.model n) (A.map n) S hS U
  calc
    (((superlevelSet (finiteModelIndicatorIterate A n U S k) t) ∆ U).card : ℝ) ≤
        9 * ‖finiteModelIndicatorIterate A n U S k - indicator U‖ ^ 2 :=
      card_thresholdedIndicatorIterate_symmDiff_le A n U S k t ht0 ht1
    _ ≤ 9 * ((k : ℝ) *
        ‖finiteModelIndicatorIterate A n U S 1 -
          finiteModelIndicatorIterate A n U S 0‖) ^ 2 := by gcongr
    _ ≤ 9 * k ^ 2 * ((S.card : ℝ)⁻¹ *
        generatorCutSize (A.model n) (A.map n) S U) := by
      calc
        9 * ((k : ℝ) *
            ‖finiteModelIndicatorIterate A n U S 1 -
              finiteModelIndicatorIterate A n U S 0‖) ^ 2 =
            9 * k ^ 2 *
              ‖finiteModelIndicatorIterate A n U S 1 -
                finiteModelIndicatorIterate A n U S 0‖ ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hinitial (by positivity)
    _ = 9 * k ^ 2 * (S.card : ℝ)⁻¹ *
        generatorCutSize (A.model n) (A.map n) S U := by ring

end KunRounding
end NonsoficGroupsExist
