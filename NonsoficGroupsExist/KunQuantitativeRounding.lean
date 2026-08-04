import NonsoficGroupsExist.KunIndicatorRounding
import NonsoficGroupsExist.KunRounding

/-!
# Quantitative property-(T) rounding in finite sofic models

This combines the genuine finite-model Kazhdan contraction with coarea
thresholding.  The output set is simultaneously close to its input and has a
boundary controlled by the strict Markov contraction.
-/

namespace NonsoficGroupsExist
namespace KunQuantitativeRounding

open KazhdanFiniteModel
open KazhdanGNS
open KunRounding
open KunIndicatorRounding
open FiniteMultiGraph
open scoped symmDiff

variable {G : Type} [Group G]

/-- Uniform quantitative rounding for every subset of every sufficiently
large finite sofic model. -/
theorem finiteModel_propertyT_rounding
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{0, 0} G Q ε)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S) (hεone : ε ≤ 1)
    (A : SoficApproximation G) :
    ∃ k : ℕ, ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧
      ∀ α : ℝ, 0 < α →
        ∃ N : ℕ, ∀ n ≥ N, ∀ U : Finset (A.model n),
          ∃ t : ℝ, (1 : ℝ) / 3 < t ∧ t < (2 : ℝ) / 3 ∧
            (((generatorGraph (A.model n) S (A.map n)).superlevel
              (finiteModelIndicatorIterate A n U S k) t ∆ U).card : ℝ) ≤
                9 * k ^ 2 * (S.card : ℝ)⁻¹ *
                  generatorCutSize (A.model n) (A.map n) S U ∧
            ((1 : ℝ) / 3) * ((2 : ℝ) / 3 - (1 : ℝ) / 3) ^ 2 *
                ((generatorGraph (A.model n) S (A.map n)).boundaryCard
                  ((generatorGraph (A.model n) S (A.map n)).superlevel
                    (finiteModelIndicatorIterate A n U S k) t) : ℝ) ^ 2 ≤
              4 * (S.card : ℝ) ^ 2 * U.card *
                ‖finiteModelIndicatorIterate A n U S k‖ *
                (c * ‖finiteModelIndicatorIterate A n U S 1 -
                    finiteModelIndicatorIterate A n U S 0‖ +
                  α * Real.sqrt (Fintype.card (A.model n) : ℝ)) := by
  obtain ⟨k, c, hc0, hc1, hcontract⟩ :=
    finiteModel_strictMarkovNormContraction_indicator
      hQ S hQS hone hεone A
  refine ⟨k, c, hc0, hc1, fun α hα ↦ ?_⟩
  obtain ⟨N, hN⟩ := hcontract α hα
  refine ⟨N, fun n hn U ↦ ?_⟩
  obtain ⟨t, ht0, ht1, htboundary⟩ :=
    exists_threshold_indicatorIterate_boundary_sq
      A n U S ⟨1, hone⟩ k
  have hclose := card_thresholdedIndicatorIterate_symmDiff_le_cut
    A n U S ⟨1, hone⟩ k t ht0 ht1
  have hlevel :
      (generatorGraph (A.model n) S (A.map n)).superlevel
          (finiteModelIndicatorIterate A n U S k) t =
        superlevelSet (finiteModelIndicatorIterate A n U S k) t := by
    rfl
  have hdisp := hN n hn U
  have hpref : 0 ≤ 4 * (S.card : ℝ) ^ 2 * U.card *
      ‖finiteModelIndicatorIterate A n U S k‖ := by positivity
  refine ⟨t, ht0, ht1, ?_, ?_⟩
  · rw [hlevel]
    exact hclose
  · exact htboundary.trans (mul_le_mul_of_nonneg_left hdisp.le hpref)

end KunQuantitativeRounding
end NonsoficGroupsExist
