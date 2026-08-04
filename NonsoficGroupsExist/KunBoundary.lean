import NonsoficGroupsExist.KunFiniteMarkov
import NonsoficGroupsExist.PermutationConservation

/-!
# Markov displacement and labeled cut size

This module identifies the one-step finite Markov displacement with the
standard directed generator cut energy.  It is the finite combinatorial input
to Kun's rounding argument.
-/

namespace NonsoficGroupsExist
namespace KazhdanGNS

open KazhdanFiniteModel
open scoped symmDiff

universe u v

variable {G : Type u} [Group G]

/-- The directed, generator-occurrence cut size.  A generator contributes the
symmetric difference between a set and its image; generator labels are counted
with their occurrences even when their assigned permutations coincide. -/
def generatorCutSize (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (U : Finset M) : ℕ :=
  ∑ s ∈ S, ((U.map (τ s).toEmbedding) ∆ U).card

omit [Group G] in
/-- The directed occurrence cut has the elementary degree bound `2|S||U|`. -/
theorem generatorCutSize_le_two_mul_card
    (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (U : Finset M) :
    generatorCutSize M τ S U ≤ 2 * S.card * U.card := by
  unfold generatorCutSize
  calc
    ∑ s ∈ S, ((U.map (τ s).toEmbedding) ∆ U).card ≤
        ∑ _s ∈ S, 2 * U.card := by
      apply Finset.sum_le_sum
      intro s _
      calc
        ((U.map (τ s).toEmbedding) ∆ U).card ≤
            ((U.map (τ s).toEmbedding) ∪ U).card :=
          Finset.card_le_card Finset.symmDiff_subset_union
        _ ≤ (U.map (τ s).toEmbedding).card + U.card :=
          Finset.card_union_le _ _
        _ = 2 * U.card := by simp; omega
    _ = 2 * S.card * U.card := by simp; ring

omit [Group G] in
/-- Hilbert-space Jensen inequality for a nonempty finite average. -/
theorem norm_average_sq_le_average_norm_sq
    {I E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Finset I) (hS : S.Nonempty) (e : I → E) :
    ‖(S.card : ℝ)⁻¹ • ∑ i ∈ S, e i‖ ^ 2 ≤
      (S.card : ℝ)⁻¹ * ∑ i ∈ S, ‖e i‖ ^ 2 := by
  have hcardNat : 0 < S.card := Finset.card_pos.mpr hS
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hcardNat
  have htriangle :
      ‖(S.card : ℝ)⁻¹ • ∑ i ∈ S, e i‖ ≤
        (S.card : ℝ)⁻¹ * ∑ i ∈ S, ‖e i‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hcard)]
    gcongr
    exact norm_sum_le _ _
  have hsumNonneg : 0 ≤ ∑ i ∈ S, ‖e i‖ :=
    Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hright : 0 ≤ (S.card : ℝ)⁻¹ * ∑ i ∈ S, ‖e i‖ :=
    mul_nonneg (inv_nonneg.mpr hcard.le) hsumNonneg
  have htriangleSq := (sq_le_sq₀ (norm_nonneg _) hright).2 htriangle
  have hcauchy :
      (∑ i ∈ S, ‖e i‖) ^ 2 ≤
        (S.card : ℝ) * ∑ i ∈ S, ‖e i‖ ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq S
      (fun _ ↦ (1 : ℝ)) (fun i ↦ ‖e i‖)
  calc
    ‖(S.card : ℝ)⁻¹ • ∑ i ∈ S, e i‖ ^ 2 ≤
        ((S.card : ℝ)⁻¹ * ∑ i ∈ S, ‖e i‖) ^ 2 := htriangleSq
    _ ≤ (S.card : ℝ)⁻¹ ^ 2 *
        ((S.card : ℝ) * ∑ i ∈ S, ‖e i‖ ^ 2) := by
      nlinarith [mul_nonneg (sq_nonneg (S.card : ℝ)⁻¹)
        (show 0 ≤ ∑ i ∈ S, ‖e i‖ ^ 2 from
          Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]
    _ = (S.card : ℝ)⁻¹ * ∑ i ∈ S, ‖e i‖ ^ 2 := by
      field_simp

omit [Group G] in
/-- A nonempty finite model average fixes constant vectors. -/
theorem finiteModelAverage_constantVector
    (M : FiniteModel) (τ : G → Equiv.Perm M) (S : Finset G)
    (hS : S.Nonempty) (r : ℝ) :
    finiteModelAverage M τ S (constantVector r) = constantVector r := by
  have hcard : S.card ≠ 0 := (Finset.card_pos.mpr hS).ne'
  ext y
  simp [finiteModelAverage, hcard]

omit [Group G] in
/-- The finite model average commutes with scalar multiplication. -/
theorem finiteModelAverage_smul
    (M : FiniteModel) (τ : G → Equiv.Perm M) (S : Finset G)
    (r : ℝ) (x : EuclideanSpace ℝ M) :
    finiteModelAverage M τ S (r • x) =
      r • finiteModelAverage M τ S x := by
  simp [finiteModelAverage, Finset.smul_sum, smul_smul, mul_comm]

omit [Group G] in
/-- A nonempty finite permutation average preserves the interval `[0,1]`
pointwise. -/
theorem finiteModelAverage_between_zero_one
    (M : FiniteModel) (τ : G → Equiv.Perm M) (S : Finset G)
    (hS : S.Nonempty) (x : EuclideanSpace ℝ M)
    (hx0 : ∀ y, 0 ≤ x y) (hx1 : ∀ y, x y ≤ 1) (y : M) :
    0 ≤ finiteModelAverage M τ S x y ∧
      finiteModelAverage M τ S x y ≤ 1 := by
  have hcardNat : 0 < S.card := Finset.card_pos.mpr hS
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hcardNat
  have hsum0 : 0 ≤ ∑ s ∈ S, x ((τ s).symm y) :=
    Finset.sum_nonneg fun s hs ↦ hx0 _
  have hsum1 : (∑ s ∈ S, x ((τ s).symm y)) ≤ S.card := by
    calc
      (∑ s ∈ S, x ((τ s).symm y)) ≤ ∑ _s ∈ S, (1 : ℝ) :=
        Finset.sum_le_sum fun s hs ↦ hx1 _
      _ = S.card := by simp
  have hsumApply :
      (∑ s ∈ S, permutationOperator (τ s) x) y =
        ∑ s ∈ S, x ((τ s).symm y) := by simp
  simp only [finiteModelAverage]
  change 0 ≤ (S.card : ℝ)⁻¹ *
      (∑ s ∈ S, permutationOperator (τ s) x) y ∧
    (S.card : ℝ)⁻¹ *
      (∑ s ∈ S, permutationOperator (τ s) x) y ≤ 1
  rw [hsumApply]
  constructor
  · exact mul_nonneg (inv_nonneg.mpr hcard.le) hsum0
  · rw [← inv_mul_cancel₀ hcard.ne']
    exact mul_le_mul_of_nonneg_left hsum1 (inv_nonneg.mpr hcard.le)

omit [Group G] in
/-- A nonempty finite permutation average preserves total mass. -/
theorem sum_finiteModelAverage
    (M : FiniteModel) (τ : G → Equiv.Perm M) (S : Finset G)
    (hS : S.Nonempty) (x : EuclideanSpace ℝ M) :
    ∑ y, finiteModelAverage M τ S x y = ∑ y, x y := by
  have hcard : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hS
  have hperm (s : G) :
      ∑ y, permutationOperator (τ s) x y = ∑ y, x y := by
    simpa [permutationOperator] using sum_comp_equiv (τ s).symm x
  have havg_apply (y : M) : finiteModelAverage M τ S x y =
      (S.card : ℝ)⁻¹ * ∑ s ∈ S, permutationOperator (τ s) x y := by
    simp [finiteModelAverage]
  simp_rw [havg_apply]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [hperm]
  simp [hcard]

omit [Group G] in
/-- Centering does not alter a Markov displacement. -/
theorem finiteModelAverage_centeredIndicator_sub
    (M : FiniteModel) (τ : G → Equiv.Perm M) (S : Finset G)
    (hS : S.Nonempty) (U : Finset M) :
    finiteModelAverage M τ S (centeredIndicator U) - centeredIndicator U =
      finiteModelAverage M τ S (indicator U) - indicator U := by
  rw [centeredIndicator, finiteModelAverage_sub]
  rw [finiteModelAverage_smul,
    finiteModelAverage_constantVector M τ S hS]
  abel

omit [Group G] in
/-- One-step Markov energy of an indicator is bounded by the average directed
generator cut size. -/
theorem norm_finiteModelAverage_indicator_sub_sq_le
    (M : FiniteModel) (τ : G → Equiv.Perm M) (S : Finset G)
    (hS : S.Nonempty) (U : Finset M) :
    ‖finiteModelAverage M τ S (indicator U) - indicator U‖ ^ 2 ≤
      (S.card : ℝ)⁻¹ * generatorCutSize M τ S U := by
  let e : G → EuclideanSpace ℝ M := fun s ↦
    permutationOperator (τ s) (indicator U) - indicator U
  have havg :
      finiteModelAverage M τ S (indicator U) - indicator U =
        (S.card : ℝ)⁻¹ • ∑ s ∈ S, e s := by
    simp [finiteModelAverage, e, Finset.sum_sub_distrib, smul_sub]
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
      inv_mul_cancel₀ (by exact_mod_cast Finset.card_ne_zero.mpr hS), one_smul]
  rw [havg]
  calc
    ‖(S.card : ℝ)⁻¹ • ∑ s ∈ S, e s‖ ^ 2 ≤
        (S.card : ℝ)⁻¹ * ∑ s ∈ S, ‖e s‖ ^ 2 :=
      norm_average_sq_le_average_norm_sq S hS e
    _ = (S.card : ℝ)⁻¹ * generatorCutSize M τ S U := by
      congr 1
      simp only [generatorCutSize, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro s hs
      exact_mod_cast norm_permutationOperator_indicator_sub_sq (τ s) U

omit [Group G] in
/-- The first Markov displacement of an indicator is at most `√(2|U|)`. -/
theorem norm_finiteModelAverage_indicator_sub_sq_le_two_card
    (M : FiniteModel) (τ : G → Equiv.Perm M) (S : Finset G)
    (hS : S.Nonempty) (U : Finset M) :
    ‖finiteModelAverage M τ S (indicator U) - indicator U‖ ^ 2 ≤
      2 * U.card := by
  have hcard : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hS
  have hcut : (generatorCutSize M τ S U : ℝ) ≤
      2 * (S.card : ℝ) * U.card := by
    exact_mod_cast generatorCutSize_le_two_mul_card M τ S U
  calc
    ‖finiteModelAverage M τ S (indicator U) - indicator U‖ ^ 2 ≤
        (S.card : ℝ)⁻¹ * generatorCutSize M τ S U :=
      norm_finiteModelAverage_indicator_sub_sq_le M τ S hS U
    _ ≤ (S.card : ℝ)⁻¹ * (2 * (S.card : ℝ) * U.card) := by
      gcongr
    _ = 2 * U.card := by field_simp

omit [Group G] in
/-- The same cut-energy bound for centered indicators. -/
theorem norm_finiteModelAverage_centeredIndicator_sub_sq_le
    (M : FiniteModel) (τ : G → Equiv.Perm M) (S : Finset G)
    (hS : S.Nonempty) (U : Finset M) :
    ‖finiteModelAverage M τ S (centeredIndicator U) - centeredIndicator U‖ ^ 2 ≤
      (S.card : ℝ)⁻¹ * generatorCutSize M τ S U := by
  rw [finiteModelAverage_centeredIndicator_sub M τ S hS U]
  exact norm_finiteModelAverage_indicator_sub_sq_le M τ S hS U

/-- Normalized time-zero displacement is controlled by normalized directed
cut size. -/
theorem finiteModelAveragingDisplacementNormSq_zero_le_cut
    (A : SoficApproximation G) (n : ℕ) (U : Finset (A.model n))
    (S : Finset G) (hS : S.Nonempty) :
    finiteModelAveragingDisplacementNormSq A n U S 0 ≤
      ((S.card : ℝ)⁻¹ * generatorCutSize (A.model n) (A.map n) S U) /
        Fintype.card (A.model n) := by
  rw [finiteModelAveragingDisplacementNormSq_zero]
  exact div_le_div_of_nonneg_right
    (norm_finiteModelAverage_centeredIndicator_sub_sq_le
      (A.model n) (A.map n) S hS U) (by positivity)

/-- The genuine finite-model Markov iterate of an uncentered characteristic
function. -/
noncomputable def finiteModelIndicatorIterate
    (A : SoficApproximation G) (n : ℕ) (U : Finset (A.model n))
    (S : Finset G) (k : ℕ) : EuclideanSpace ℝ (A.model n) :=
  ((finiteModelAverage (A.model n) (A.map n) S)^[k]) (indicator U)

/-- Successor time for the uncentered indicator iterate. -/
theorem finiteModelIndicatorIterate_succ
    (A : SoficApproximation G) (n : ℕ) (U : Finset (A.model n))
    (S : Finset G) (k : ℕ) :
    finiteModelIndicatorIterate A n U S (k + 1) =
      finiteModelAverage (A.model n) (A.map n) S
        (finiteModelIndicatorIterate A n U S k) := by
  rw [finiteModelIndicatorIterate, finiteModelIndicatorIterate,
    Function.iterate_succ_apply']

/-- Every indicator Markov iterate remains pointwise in `[0,1]`. -/
theorem finiteModelIndicatorIterate_between_zero_one
    (A : SoficApproximation G) (n : ℕ) (U : Finset (A.model n))
    (S : Finset G) (hS : S.Nonempty) (k : ℕ) (y : A.model n) :
    0 ≤ finiteModelIndicatorIterate A n U S k y ∧
      finiteModelIndicatorIterate A n U S k y ≤ 1 := by
  induction k generalizing y with
  | zero =>
      by_cases hy : y ∈ U <;>
        simp [finiteModelIndicatorIterate, indicator_apply, hy]
  | succ k ih =>
      rw [finiteModelIndicatorIterate_succ]
      exact finiteModelAverage_between_zero_one
        (A.model n) (A.map n) S hS
        (finiteModelIndicatorIterate A n U S k)
        (fun y ↦ (ih y).1) (fun y ↦ (ih y).2) y

/-- Every uncentered indicator trajectory has the same total mass as its
initial set. -/
theorem sum_finiteModelIndicatorIterate
    (A : SoficApproximation G) (n : ℕ) (U : Finset (A.model n))
    (S : Finset G) (hS : S.Nonempty) (k : ℕ) :
    ∑ y, finiteModelIndicatorIterate A n U S k y = U.card := by
  induction k with
  | zero => simp [finiteModelIndicatorIterate, indicator_apply]
  | succ k ih =>
      rw [finiteModelIndicatorIterate_succ,
        sum_finiteModelAverage (A.model n) (A.map n) S hS, ih]

/-- The squared norm of an indicator Markov iterate is at most the cardinality
of its initial set. -/
theorem norm_finiteModelIndicatorIterate_sq_le_card
    (A : SoficApproximation G) (n : ℕ) (U : Finset (A.model n))
    (S : Finset G) (hS : S.Nonempty) (k : ℕ) :
    ‖finiteModelIndicatorIterate A n U S k‖ ^ 2 ≤ U.card := by
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    ∑ y, (finiteModelIndicatorIterate A n U S k y) ^ 2 ≤
        ∑ y, finiteModelIndicatorIterate A n U S k y := by
      apply Finset.sum_le_sum
      intro y _
      obtain ⟨hy0, hy1⟩ :=
        finiteModelIndicatorIterate_between_zero_one A n U S hS k y
      nlinarith [mul_nonneg hy0 (sub_nonneg.mpr hy1)]
    _ = U.card := sum_finiteModelIndicatorIterate A n U S hS k

/-- Markov displacement norms are nonincreasing along the genuine finite
trajectory. -/
theorem norm_finiteModelIndicatorIterate_displacement_le_initial
    (A : SoficApproximation G) (n : ℕ) (U : Finset (A.model n))
    (S : Finset G) (hS : S.Nonempty) (k : ℕ) :
    ‖finiteModelIndicatorIterate A n U S (k + 1) -
        finiteModelIndicatorIterate A n U S k‖ ≤
      ‖finiteModelIndicatorIterate A n U S 1 -
        finiteModelIndicatorIterate A n U S 0‖ := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
      rw [finiteModelIndicatorIterate_succ,
        finiteModelIndicatorIterate_succ,
        ← finiteModelAverage_sub]
      exact (norm_finiteModelAverage_le
        (A.model n) (A.map n) S hS _).trans (by
          simpa [finiteModelIndicatorIterate_succ] using ih)

/-- Centered and uncentered trajectories differ by the same fixed constant at
every time. -/
theorem finiteModelAverageIterate_eq_indicatorIterate_sub
    (A : SoficApproximation G) (n : ℕ) (U : Finset (A.model n))
    (S : Finset G) (hS : S.Nonempty) (k : ℕ) :
    finiteModelAverageIterate A n U S k =
      finiteModelIndicatorIterate A n U S k -
        ((U.card : ℝ) / Fintype.card (A.model n)) • constantVector 1 := by
  induction k with
  | zero =>
      simp [finiteModelAverageIterate, finiteModelIndicatorIterate,
        centeredIndicator]
  | succ k ih =>
      rw [finiteModelAverageIterate_succ, finiteModelIndicatorIterate_succ,
        ih, finiteModelAverage_sub, finiteModelAverage_smul,
        finiteModelAverage_constantVector (A.model n) (A.map n) S hS]

/-- Therefore consecutive displacement vectors are identical before and
after centering. -/
theorem finiteModelAverageIterate_displacement_eq_indicator
    (A : SoficApproximation G) (n : ℕ) (U : Finset (A.model n))
    (S : Finset G) (hS : S.Nonempty) (k : ℕ) :
    finiteModelAverageIterate A n U S (k + 1) -
        finiteModelAverageIterate A n U S k =
      finiteModelIndicatorIterate A n U S (k + 1) -
        finiteModelIndicatorIterate A n U S k := by
  rw [finiteModelAverageIterate_eq_indicatorIterate_sub A n U S hS,
    finiteModelAverageIterate_eq_indicatorIterate_sub A n U S hS]
  abel

/-- The uncentered indicator contraction with coefficient below any prescribed
positive target. -/
theorem finiteModel_markovNormContraction_indicator_lt
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, u} G Q ε)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S) (hεone : ε ≤ 1)
    (A : SoficApproximation G) (θ : ℝ) (hθ : 0 < θ) :
    ∃ k : ℕ, ∃ c : ℝ, 0 ≤ c ∧ c < θ ∧
      ∀ α : ℝ, 0 < α →
        ∃ N : ℕ, ∀ n ≥ N, ∀ U : Finset (A.model n),
          ‖finiteModelIndicatorIterate A n U S (k + 1) -
              finiteModelIndicatorIterate A n U S k‖ <
            c * ‖finiteModelIndicatorIterate A n U S 1 -
              finiteModelIndicatorIterate A n U S 0‖ +
            α * Real.sqrt (Fintype.card (A.model n) : ℝ) := by
  obtain ⟨k, c, hc0, hc1, hcontract⟩ :=
    finiteModel_markovNormContraction_lt
      hQ S hQS hone hεone A θ hθ
  refine ⟨k, c, hc0, hc1, fun α hα ↦ ?_⟩
  obtain ⟨N, hN⟩ := hcontract α hα
  refine ⟨N, fun n hn U ↦ ?_⟩
  simpa only [finiteModelAverageIterate_displacement_eq_indicator
      A n U S ⟨1, hone⟩] using hN n hn U

/-- The strict Kazhdan Markov contraction in the uncentered indicator form
used by finite threshold rounding. -/
theorem finiteModel_strictMarkovNormContraction_indicator
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, u} G Q ε)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S) (hεone : ε ≤ 1)
    (A : SoficApproximation G) :
    ∃ k : ℕ, ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧
      ∀ α : ℝ, 0 < α →
        ∃ N : ℕ, ∀ n ≥ N, ∀ U : Finset (A.model n),
          ‖finiteModelIndicatorIterate A n U S (k + 1) -
              finiteModelIndicatorIterate A n U S k‖ <
            c * ‖finiteModelIndicatorIterate A n U S 1 -
              finiteModelIndicatorIterate A n U S 0‖ +
            α * Real.sqrt (Fintype.card (A.model n) : ℝ) := by
  exact finiteModel_markovNormContraction_indicator_lt
    hQ S hQS hone hεone A 1 (by norm_num)

end KazhdanGNS
end NonsoficGroupsExist
