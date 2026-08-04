import NonsoficGroupsExist.KunUniformRemoval
import NonsoficGroupsExist.KunSmallBoundary

/-!
# Rounding with a horizon-independent proximity bound

The thresholded late iterate is close to its input because the whole Markov
trajectory has bounded motion.  Unlike the crude telescoping estimate, the
coefficient below does not contain the horizon `k`.
-/

namespace NonsoficGroupsExist
namespace KunUniformRounding

open KazhdanFiniteModel
open KazhdanGNS
open KunRemoval
open KunRounding
open KunIndicatorRounding
open KunSmallBoundary
open KunUniformRemoval
open FiniteMultiGraph
open scoped symmDiff

variable {G : Type} [Group G]

/-- A movement bound supplies a fixed proximity coefficient, while a late
displacement contraction supplies the small boundary. -/
theorem exists_nearby_of_movement_contraction
    (A : SoficApproximation G) (n : ℕ) (U : Finset (A.model n))
    (S : Finset G) (hS : S.Nonempty) (k : ℕ) (L c : ℝ)
    (hL : 0 ≤ L) (hc : 0 ≤ c)
    (hmove : ‖trajectoryMovement A n U S k‖ ≤
      L * ‖indicatorDisplacement A n U S 0‖)
    (hcontract : ‖indicatorDisplacement A n U S k‖ ≤
      c * ‖indicatorDisplacement A n U S 0‖) :
    ∃ W : Finset (A.model n),
      ((W ∆ U).card : ℝ) ≤
        9 * L ^ 2 * (S.card : ℝ)⁻¹ *
          generatorCutSize (A.model n) (A.map n) S U ∧
      ((1 : ℝ) / 3) * ((2 : ℝ) / 3 - (1 : ℝ) / 3) ^ 2 *
          ((generatorGraph (A.model n) S (A.map n)).boundaryCard W : ℝ) ^ 2 ≤
        8 * (S.card : ℝ) ^ 2 * c * (U.card : ℝ) ^ 2 := by
  obtain ⟨t, ht0, ht1, htbound⟩ :=
    exists_threshold_boundary_sq_of_contraction A n U S hS k c hc
      (by simpa [indicatorDisplacement] using hcontract)
  let W := (generatorGraph (A.model n) S (A.map n)).superlevel
    (finiteModelIndicatorIterate A n U S k) t
  have hthreshold := card_thresholdedIndicatorIterate_symmDiff_le
    A n U S k t ht0 ht1
  have hmoveSq : ‖trajectoryMovement A n U S k‖ ^ 2 ≤
      (L * ‖indicatorDisplacement A n U S 0‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg hL (norm_nonneg _))).2 hmove
  have hinitial : ‖indicatorDisplacement A n U S 0‖ ^ 2 ≤
      (S.card : ℝ)⁻¹ *
        generatorCutSize (A.model n) (A.map n) S U := by
    simpa [indicatorDisplacement, finiteModelIndicatorIterate] using
      norm_finiteModelAverage_indicator_sub_sq_le
        (A.model n) (A.map n) S hS U
  refine ⟨W, ?_, htbound⟩
  calc
    ((W ∆ U).card : ℝ) ≤ 9 * ‖trajectoryMovement A n U S k‖ ^ 2 := by
      simpa [W, trajectoryMovement, superlevelSet,
        FiniteMultiGraph.superlevel] using hthreshold
    _ ≤ 9 * (L * ‖indicatorDisplacement A n U S 0‖) ^ 2 := by gcongr
    _ ≤ 9 * L ^ 2 * ((S.card : ℝ)⁻¹ *
        generatorCutSize (A.model n) (A.map n) S U) := by
      calc
        9 * (L * ‖indicatorDisplacement A n U S 0‖) ^ 2 =
            9 * L ^ 2 * ‖indicatorDisplacement A n U S 0‖ ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hinitial (by positivity)
    _ = 9 * L ^ 2 * (S.card : ℝ)⁻¹ *
        generatorCutSize (A.model n) (A.map n) S U := by ring

/-- Fixed input cut threshold associated to the horizon-independent movement
coefficient. -/
noncomputable def uniformInputCutThreshold (S : Finset G) (L : ℝ) : ℝ :=
  (S.card : ℝ) / (54 * (L ^ 2 + 1))

theorem uniformInputCutThreshold_pos {α : Type}
    (S : Finset α) (hS : S.Nonempty)
    (L : ℝ) : 0 < uniformInputCutThreshold S L := by
  unfold uniformInputCutThreshold
  have hcard : (0 : ℝ) < S.card := by
    exact_mod_cast Finset.card_pos.mpr hS
  positivity

/-- The fixed proximity estimate is below one third under the uniform input
cut threshold. -/
theorem symmDiff_lt_third_of_uniform_cut {α : Type}
    (M : FiniteModel) (τ : α → Equiv.Perm M)
    (S : Finset α) (hS : S.Nonempty) (L : ℝ) (U W : Finset M)
    (hclose : ((W ∆ U).card : ℝ) ≤
      9 * L ^ 2 * (S.card : ℝ)⁻¹ * generatorCutSize M τ S U)
    (hcut : (generatorCutSize M τ S U : ℝ) <
      uniformInputCutThreshold S L * U.card) :
    ((W ∆ U).card : ℝ) < (U.card : ℝ) / 3 := by
  have hcard : (0 : ℝ) < S.card := by
    exact_mod_cast Finset.card_pos.mpr hS
  have hUpos : (0 : ℝ) < U.card := by
    have hcut0 : (0 : ℝ) ≤ generatorCutSize M τ S U := by positivity
    by_contra h
    have hU0 : (U.card : ℝ) = 0 :=
      le_antisymm (le_of_not_gt h) (by positivity)
    rw [hU0, mul_zero] at hcut
    exact (not_lt_of_ge hcut0) hcut
  have hfactor : 0 ≤ 9 * L ^ 2 * (S.card : ℝ)⁻¹ := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hcut.le hfactor
  calc
    ((W ∆ U).card : ℝ) ≤
        9 * L ^ 2 * (S.card : ℝ)⁻¹ * generatorCutSize M τ S U := hclose
    _ ≤ 9 * L ^ 2 * (S.card : ℝ)⁻¹ *
        (uniformInputCutThreshold S L * U.card) := hscaled
    _ < (U.card : ℝ) / 3 := by
      unfold uniformInputCutThreshold
      have hL : (0 : ℝ) ≤ L ^ 2 := sq_nonneg _
      field_simp
      nlinarith

/-- Uniform small-boundary replacement.  The horizon `k` may depend on the
requested boundary ratio, but the proximity coefficient and admissible input
cut depend only on `L`. -/
theorem exists_nearby_boundary_lt_target_uniform
    (A : SoficApproximation G) (n : ℕ) (U : Finset (A.model n))
    (hU : U.Nonempty) (S : Finset G) (hS : S.Nonempty)
    (k : ℕ) (L c target : ℝ) (hL : 0 ≤ L) (hc : 0 ≤ c)
    (hcTarget : c < boundaryContraction S target)
    (htarget : 0 < target)
    (hsmallOrContract :
      ‖indicatorDisplacement A n U S 0‖ <
          boundaryAlpha S target * ‖indicator U‖ ∨
        ‖indicatorDisplacement A n U S k‖ <
          c * ‖indicatorDisplacement A n U S 0‖)
    (hsmallOrMove :
      ‖indicatorDisplacement A n U S 0‖ <
          boundaryAlpha S target * ‖indicator U‖ ∨
        ‖trajectoryMovement A n U S k‖ <
          L * ‖indicatorDisplacement A n U S 0‖) :
    ∃ W : Finset (A.model n),
      ((W ∆ U).card : ℝ) ≤
        9 * L ^ 2 * (S.card : ℝ)⁻¹ *
          generatorCutSize (A.model n) (A.map n) S U ∧
      ((generatorGraph (A.model n) S (A.map n)).boundaryCard W : ℝ) <
        target * U.card := by
  have hsmallCase
      (hsmall : ‖indicatorDisplacement A n U S 0‖ <
        boundaryAlpha S target * ‖indicator U‖) :
      ∃ W : Finset (A.model n),
        ((W ∆ U).card : ℝ) ≤
          9 * L ^ 2 * (S.card : ℝ)⁻¹ *
            generatorCutSize (A.model n) (A.map n) S U ∧
        ((generatorGraph (A.model n) S (A.map n)).boundaryCard W : ℝ) <
          target * U.card := by
    obtain ⟨t, ht0, ht1, htbound⟩ :=
      exists_threshold_boundary_sq_of_small_initial A n U S hS
        (boundaryAlpha S target)
        (by simpa [indicatorDisplacement] using hsmall.le)
    let W := (generatorGraph (A.model n) S (A.map n)).superlevel
      (finiteModelIndicatorIterate A n U S 0) t
    have hWU : W = U := by
      ext y
      have htpos : 0 < t := by linarith
      have htone : t < 1 := by linarith
      by_cases hy : y ∈ U <;>
        simp [W, FiniteMultiGraph.superlevel, finiteModelIndicatorIterate,
          indicator_apply, hy, htpos.le, htone]
    refine ⟨W, ?_, ?_⟩
    · simpa [hWU] using
        (show (0 : ℝ) ≤
          9 * L ^ 2 * (S.card : ℝ)⁻¹ *
            generatorCutSize (A.model n) (A.map n) S U by positivity)
    · have hcoefficient :
          4 * (S.card : ℝ) ^ 2 * boundaryAlpha S target < target ^ 2 / 27 :=
        (le_max_left _ _).trans_lt (boundaryCoefficient_lt S hS htarget)
      change ((1 : ℝ) / 3) * ((2 : ℝ) / 3 - (1 : ℝ) / 3) ^ 2 *
          ((generatorGraph (A.model n) S (A.map n)).boundaryCard W : ℝ) ^ 2 ≤
        4 * (S.card : ℝ) ^ 2 * boundaryAlpha S target * (U.card : ℝ) ^ 2
        at htbound
      rw [hWU] at htbound ⊢
      exact boundary_lt_of_coefficient_lt (Finset.card_pos.mpr hU) htarget
        htbound hcoefficient
  rcases hsmallOrContract with hsmall | hcontract
  · exact hsmallCase hsmall
  · rcases hsmallOrMove with hsmall | hmove
    · exact hsmallCase hsmall
    · obtain ⟨W, hclose, hboundary⟩ :=
        exists_nearby_of_movement_contraction A n U S hS k L c hL hc
          hmove.le hcontract.le
      refine ⟨W, hclose, ?_⟩
      have hScard : (0 : ℝ) < S.card := by
        exact_mod_cast Finset.card_pos.mpr hS
      have hcoeffLt :
          8 * (S.card : ℝ) ^ 2 * c < target ^ 2 / 27 := by
        have hmul : 8 * (S.card : ℝ) ^ 2 * c <
            8 * (S.card : ℝ) ^ 2 * boundaryContraction S target := by
          exact mul_lt_mul_of_pos_left hcTarget (by positivity)
        have hmax : 8 * (S.card : ℝ) ^ 2 * boundaryContraction S target ≤
            boundaryCoefficient S (boundaryAlpha S target)
              (boundaryContraction S target) :=
          le_max_right _ _
        exact (hmul.trans_le hmax).trans
          (boundaryCoefficient_lt S hS htarget)
      exact boundary_lt_of_coefficient_lt (Finset.card_pos.mpr hU) htarget
        hboundary hcoeffLt

end KunUniformRounding
end NonsoficGroupsExist
