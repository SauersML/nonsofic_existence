import NonsoficGroupsExist.KunThomFiniteMarkov
import NonsoficGroupsExist.KunGeneratorGraph
import NonsoficGroupsExist.KunRounding

/-!
# Threshold rounding for the Kun--Thom diagonal trajectory

The diagonal action lives on `Y × Y`, but the initial permutation graph has
only `|Y|` points.  This module keeps that graph-scale normalization while
passing from the centered trajectory used by the Kazhdan argument to the
uncentered `[0,1]`-valued trajectory required by coarea thresholding.
-/

namespace NonsoficGroupsExist
namespace KunThomRounding

open KazhdanFiniteModel
open KazhdanGNS
open KazhdanImprovement
open KunGeneratorGraph
open KunThomFiniteMarkov

variable {K J : Type} [Group K] [Group J]

/-- Genuine diagonal Markov iteration started at the indicator of a
permutation graph. -/
noncomputable def pairIndicatorIterate
    (A : SoficApproximation (K × J)) (n : ℕ)
    (c : Equiv.Perm (A.model n)) (S : Finset K) (k : ℕ) :
    EuclideanSpace ℝ (pairModel (A.model n)) :=
  ((finiteModelAverage (pairModel (A.model n)) (pairMap A n) S)^[k])
    (indicator (permutationGraph (A.model n) c))

theorem pairIndicatorIterate_succ
    (A : SoficApproximation (K × J)) (n : ℕ)
    (c : Equiv.Perm (A.model n)) (S : Finset K) (k : ℕ) :
    pairIndicatorIterate A n c S (k + 1) =
      finiteModelAverage (pairModel (A.model n)) (pairMap A n) S
        (pairIndicatorIterate A n c S k) := by
  rw [pairIndicatorIterate, pairIndicatorIterate,
    Function.iterate_succ_apply']

/-- Every diagonal indicator iterate remains pointwise in `[0,1]`. -/
theorem pairIndicatorIterate_between_zero_one
    (A : SoficApproximation (K × J)) (n : ℕ)
    (c : Equiv.Perm (A.model n)) (S : Finset K) (hS : S.Nonempty)
    (k : ℕ) (z : pairModel (A.model n)) :
    0 ≤ pairIndicatorIterate A n c S k z ∧
      pairIndicatorIterate A n c S k z ≤ 1 := by
  induction k generalizing z with
  | zero =>
      by_cases hz : z ∈ permutationGraph (A.model n) c <;>
        simp [pairIndicatorIterate, indicator_apply, hz]
  | succ k ih =>
      rw [pairIndicatorIterate_succ]
      exact finiteModelAverage_between_zero_one
        (pairModel (A.model n)) (pairMap A n) S hS
        (pairIndicatorIterate A n c S k)
        (fun z ↦ (ih z).1) (fun z ↦ (ih z).2) z

/-- The diagonal Markov trajectory preserves the `|Y|` mass of its initial
permutation graph. -/
theorem sum_pairIndicatorIterate
    (A : SoficApproximation (K × J)) (n : ℕ)
    (c : Equiv.Perm (A.model n)) (S : Finset K) (hS : S.Nonempty)
    (k : ℕ) :
    ∑ z, pairIndicatorIterate A n c S k z =
      Fintype.card (A.model n) := by
  induction k with
  | zero =>
      rw [pairIndicatorIterate]
      simp only [Function.iterate_zero_apply]
      have hsum (U : Finset (pairModel (A.model n))) :
          ∑ z, indicator U z = (U.card : ℝ) := by
        simp [indicator_apply]
      rw [hsum, card_permutationGraph]
  | succ k ih =>
      rw [pairIndicatorIterate_succ,
        sum_finiteModelAverage (pairModel (A.model n)) (pairMap A n) S hS,
        ih]

/-- The squared norm of every diagonal indicator iterate is at most the
graph size, not the ambient pair-space size. -/
theorem norm_pairIndicatorIterate_sq_le_card
    (A : SoficApproximation (K × J)) (n : ℕ)
    (c : Equiv.Perm (A.model n)) (S : Finset K) (hS : S.Nonempty)
    (k : ℕ) :
    ‖pairIndicatorIterate A n c S k‖ ^ 2 ≤
      Fintype.card (A.model n) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    ∑ z, (pairIndicatorIterate A n c S k z) ^ 2 ≤
        ∑ z, pairIndicatorIterate A n c S k z := by
      apply Finset.sum_le_sum
      intro z _
      obtain ⟨hz0, hz1⟩ :=
        pairIndicatorIterate_between_zero_one A n c S hS k z
      nlinarith [mul_nonneg hz0 (sub_nonneg.mpr hz1)]
    _ = Fintype.card (A.model n) :=
      sum_pairIndicatorIterate A n c S hS k

/-- Centered and uncentered diagonal trajectories differ by the same constant
at every time. -/
theorem finiteModelAverageIterate_eq_pairIndicatorIterate_sub
    (A : SoficApproximation (K × J)) (n : ℕ)
    (c : Equiv.Perm (A.model n)) (S : Finset K) (hS : S.Nonempty)
    (k : ℕ) :
    KunThomFiniteMarkov.finiteModelAverageIterate A n c S k =
      pairIndicatorIterate A n c S k -
        (((permutationGraph (A.model n) c).card : ℝ) /
          Fintype.card (pairModel (A.model n))) • constantVector 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [KunThomFiniteMarkov.finiteModelAverageIterate_succ,
        pairIndicatorIterate_succ,
        ih, finiteModelAverage_sub, finiteModelAverage_smul,
        finiteModelAverage_constantVector
          (pairModel (A.model n)) (pairMap A n) S hS]

/-- Consecutive displacement vectors are identical before and after
centering. -/
theorem finiteModelAverageIterate_displacement_eq_pairIndicator
    (A : SoficApproximation (K × J)) (n : ℕ)
    (c : Equiv.Perm (A.model n)) (S : Finset K) (hS : S.Nonempty)
    (k : ℕ) :
    KunThomFiniteMarkov.finiteModelAverageIterate A n c S (k + 1) -
        KunThomFiniteMarkov.finiteModelAverageIterate A n c S k =
      pairIndicatorIterate A n c S (k + 1) -
        pairIndicatorIterate A n c S k := by
  rw [finiteModelAverageIterate_eq_pairIndicatorIterate_sub A n c S hS,
    finiteModelAverageIterate_eq_pairIndicatorIterate_sub A n c S hS]
  abel

/-- The graph-scale Kazhdan contraction transfers verbatim to the uncentered
diagonal indicator trajectory. -/
theorem pairIndicatorDisplacementNormSq_eventually_lt
    {Q : Finset K} {ε : ℝ} (hQ : IsKazhdanPair.{0, 0} K Q ε)
    (S : Finset K) (hQS : Q ⊆ S) (hone : 1 ∈ S) (hεone : ε ≤ 1)
    (A : SoficApproximation (K × J)) (k : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ c : Equiv.Perm (A.model n),
      ‖pairIndicatorIterate A n c S (k + 1) -
          pairIndicatorIterate A n c S k‖ ^ 2 /
          Fintype.card (A.model n) <
        4 * (1 - ε ^ 2 / (4 * S.card)) ^ (2 * k) *
          (‖pairIndicatorIterate A n c S 1 -
            pairIndicatorIterate A n c S 0‖ ^ 2 /
              Fintype.card (A.model n)) + δ := by
  obtain ⟨N, hN⟩ :=
    KunThomFiniteMarkov.finiteModelAveragingDisplacementNormSq_eventually_lt
      hQ S hQS hone hεone A k δ hδ
  refine ⟨N, fun n hn c ↦ ?_⟩
  have h := hN n hn c
  unfold KunThomFiniteMarkov.finiteModelAveragingDisplacementNormSq at h
  rw [finiteModelAverageIterate_displacement_eq_pairIndicator
      A n c S ⟨1, hone⟩ k,
    finiteModelAverageIterate_displacement_eq_pairIndicator
      A n c S ⟨1, hone⟩ 0] at h
  exact h

/-- Coarea thresholding of a diagonal indicator iterate, with every term
measured at the permutation-graph scale. -/
theorem exists_threshold_pairIndicator_boundary_sq
    (A : SoficApproximation (K × J)) (n : ℕ)
    (c : Equiv.Perm (A.model n)) (S : Finset K) (hS : S.Nonempty)
    (k : ℕ) :
    ∃ t : ℝ, (1 : ℝ) / 3 < t ∧ t < (2 : ℝ) / 3 ∧
      ((1 : ℝ) / 3) * ((2 : ℝ) / 3 - (1 : ℝ) / 3) ^ 2 *
          ((generatorGraph (pairModel (A.model n)) S (pairMap A n)).boundaryCard
            ((generatorGraph (pairModel (A.model n)) S (pairMap A n)).superlevel
              (pairIndicatorIterate A n c S k) t) : ℝ) ^ 2 ≤
        4 * (S.card : ℝ) ^ 2 * Fintype.card (A.model n) *
          ‖pairIndicatorIterate A n c S k‖ *
          ‖pairIndicatorIterate A n c S (k + 1) -
            pairIndicatorIterate A n c S k‖ := by
  have hf (z : pairModel (A.model n)) :
      0 ≤ pairIndicatorIterate A n c S k z :=
    (pairIndicatorIterate_between_zero_one A n c S hS k z).1
  obtain ⟨t, ht0, ht1, ht⟩ :=
    exists_generatorGraph_boundary_sq_le_markov
      (pairModel (A.model n)) S hS (pairMap A n)
      (pairIndicatorIterate A n c S k)
      ((1 : ℝ) / 3) ((2 : ℝ) / 3) (by norm_num) (by norm_num) hf
  refine ⟨t, ht0, ht1, ?_⟩
  rw [sum_pairIndicatorIterate A n c S hS k] at ht
  simpa [pairIndicatorIterate_succ] using ht

end KunThomRounding
end NonsoficGroupsExist
