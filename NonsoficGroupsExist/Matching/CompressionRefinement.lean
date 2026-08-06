import NonsoficGroupsExist.Matching.ExternalCompressorCrossing
import NonsoficGroupsExist.Criterion.LocalCriterion
import NonsoficGroupsExist.Matching.ComponentDivergence

/-!
# Refinement supplied by the compression setup

This connects the abstract external-compressor estimate to
`CompressionSetup.compressedEnd_spec`.  Thus every compressor has negligible
total leakage from source Γ-components into their selected target components.
-/

namespace NonsoficGroupsExist
namespace CompressionSetup

variable {G Γ J : Type} [Group G] [Group Γ] [Group J]
variable (C : CompressionSetup G Γ J) (S : SoficApproximation G)

abbrev gammaApproximation : SoficApproximation Γ :=
  S.comap C.embedΓ C.embedΓ_injective

theorem externalConjugacyError_eq (q : G) (hq : q ∈ C.compressors)
    (n : ℕ) (g : Γ) :
    ((C.gammaApproximation S).externalConjugacyError n (S.map n q)
      (C.compressedEnd q hq) g) = S.conjugacyError n q (C.embedΓ g) := by
  classical
  unfold SoficApproximation.externalConjugacyError
    SoficApproximation.conjugacyError
  apply Finset.filter_congr
  intro x _
  change (S.map n q) (S.map n (C.embedΓ g) x) ≠
      S.map n (C.embedΓ (C.compressedEnd q hq g)) (S.map n q x) ↔
    (S.map n q) (S.map n (C.embedΓ g) x) ≠
      S.map n (q * C.embedΓ g * q⁻¹) (S.map n q x)
  rw [C.compressedEnd_spec q hq g]

theorem externalConjugacyError_negligible (q : G) (hq : q ∈ C.compressors)
    (g : Γ) : Negligible
      (fun n ↦ (Fintype.card ((C.gammaApproximation S).model n) : ℝ))
      fun n ↦ (((C.gammaApproximation S).externalConjugacyError n (S.map n q)
        (C.compressedEnd q hq) g).card : ℝ) := by
  apply Negligible.congr (S.conjugacyError_negligible q (C.embedΓ g))
  intro n
  rw [C.externalConjugacyError_eq S q hq n g]
  rfl

/-- The edited Γ-decomposition has negligible crossings after transport by
an ambient compressor. -/
theorem compressorCrossing_negligible
    (D : ExpanderDecomposition (C.gammaApproximation S) C.generatorsΓ)
    (q : G) (hq : q ∈ C.compressors) :
    Negligible (fun n ↦
      (Fintype.card ((C.gammaApproximation S).model n) : ℝ))
      fun n ↦ (((D.modelGraph n).crossingEdges
        (ExpanderDecomposition.transportedTargetLabel
          (D.blocks n) (S.map n q))).card : ℝ) := by
  apply D.externalGlobalCrossing_negligible (fun n ↦ S.map n q)
    (C.compressedEnd q hq)
  · intro g _
    exact C.externalConjugacyError_negligible S q hq g
  · exact D.all_almost_invariant C.generatorsΓ_symmetric
      C.generatorsΓ_generate

/-- Total one-sided leakage over all source components is negligible. -/
theorem compressorLeakage_negligible
    (D : ExpanderDecomposition (C.gammaApproximation S) C.generatorsΓ)
    (q : G) (hq : q ∈ C.compressors) :
    Negligible (fun n ↦
      (Fintype.card ((C.gammaApproximation S).model n) : ℝ))
      fun n ↦ ∑ A : D.componentIndex n,
        (D.componentLeakage (D.blocks n) (S.map n q) A : ℝ) := by
  have hcross := C.compressorCrossing_negligible S D q hq
  have hscaled := Negligible.const_mul (4 / D.cheeger) hcross
  refine Vanishing.squeeze (fun n ↦ div_nonneg (by positivity) (by positivity))
    (fun n ↦ ?_) hscaled
  have hrefine := D.cheeger_mul_totalLeakage_le_globalCrossing
    (D.blocks n) (S.map n q)
  have hle : (∑ A : D.componentIndex n,
      (D.componentLeakage (D.blocks n) (S.map n q) A : ℝ)) ≤
      (4 / D.cheeger) *
        (((D.modelGraph n).crossingEdges
          (ExpanderDecomposition.transportedTargetLabel
            (D.blocks n) (S.map n q))).card : ℝ) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ D.cheeger_pos).2
    rw [mul_comm]
    exact hrefine
  apply div_le_div_of_nonneg_right hle
  positivity

end CompressionSetup
end NonsoficGroupsExist
