import NonsoficGroupsExist.KunSmallBoundary

/-!
# Property-(T) small-boundary replacement

This is the quantitative form of condition `(2)` in Kun's graph-sequence
characterization: outside a controlled exceptional set, every nonempty input
set has a nearby replacement with any prescribed boundary ratio.
-/

namespace NonsoficGroupsExist
namespace KunDecompositionStep

open KazhdanFiniteModel
open KazhdanGNS
open KunRemoval
open KunAsymptoticRemoval
open KunSmallBoundary
open scoped symmDiff

variable {G : Type} [Group G]

/-- Input cut ratio small enough to make Kun's rounded set differ from its
input on less than one third of the input vertices. -/
noncomputable def inputCutThreshold (S : Finset G) (k : ℕ) : ℝ :=
  (S.card : ℝ) / (54 * (k ^ 2 + 1))

omit [Group G] in
theorem inputCutThreshold_pos (S : Finset G) (hS : S.Nonempty) (k : ℕ) :
    0 < inputCutThreshold S k := by
  unfold inputCutThreshold
  have hcard : (0 : ℝ) < S.card := by
    exact_mod_cast Finset.card_pos.mpr hS
  positivity

omit [Group G] in
/-- The quantitative proximity estimate is strictly below one third whenever
the input cut satisfies `inputCutThreshold`. -/
theorem symmDiff_lt_third_of_cut_lt
    (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (hS : S.Nonempty) (k : ℕ) (U W : Finset M)
    (hclose : ((W ∆ U).card : ℝ) ≤
      9 * k ^ 2 * (S.card : ℝ)⁻¹ * generatorCutSize M τ S U)
    (hcut : (generatorCutSize M τ S U : ℝ) <
      inputCutThreshold S k * U.card) :
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
  have hfactor : 0 ≤ 9 * (k : ℝ) ^ 2 * (S.card : ℝ)⁻¹ := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hcut.le hfactor
  calc
    ((W ∆ U).card : ℝ) ≤
        9 * k ^ 2 * (S.card : ℝ)⁻¹ * generatorCutSize M τ S U := hclose
    _ ≤ 9 * k ^ 2 * (S.card : ℝ)⁻¹ *
        (inputCutThreshold S k * U.card) := hscaled
    _ < (U.card : ℝ) / 3 := by
      unfold inputCutThreshold
      have hk : (0 : ℝ) ≤ k ^ 2 := sq_nonneg _
      field_simp
      nlinarith

/-- Uniform small-boundary replacement in sufficiently large sofic models. -/
theorem finiteModel_propertyT_smallBoundaryReplacement
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{0, 0} G Q ε)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S) (hεone : ε ≤ 1)
    (A : SoficApproximation G) (target : ℝ) (htarget : 0 < target) :
    ∃ k : ℕ, ∃ c : ℝ,
      0 ≤ c ∧ c < boundaryContraction S target ∧
      ∀ δ : ℝ, 0 < δ →
        ∃ N : ℕ, ∀ n ≥ N,
          ∃ B : Finset (A.model n),
            (boundaryAlpha S target) ^ 2 *
                (boundaryContraction S target - c) ^ 2 * (B.card : ℝ) ≤
              ((S.card + 1) ^ (2 * (k + 1)) : ℕ) *
                (δ ^ 2 * Fintype.card (A.model n) : ℝ) ∧
            ∀ U : Finset (A.model n), U.Nonempty → Disjoint U B →
              ∃ W : Finset (A.model n),
                ((W ∆ U).card : ℝ) ≤
                  9 * k ^ 2 * (S.card : ℝ)⁻¹ *
                    generatorCutSize (A.model n) (A.map n) S U ∧
                ((generatorGraph (A.model n) S (A.map n)).boundaryCard W : ℝ) <
                  target * U.card := by
  have hS : S.Nonempty := ⟨1, hone⟩
  have hcontraction := boundaryContraction_pos S hS htarget
  obtain ⟨k, c, hc0, hcHalf, hremoval⟩ :=
    finiteModel_propertyT_removal_below hQ S hQS hone hεone A
      (boundaryContraction S target / 2) (by positivity)
  have hcc : c < boundaryContraction S target := by linarith
  refine ⟨k, c, hc0, hcc, fun δ hδ ↦ ?_⟩
  obtain ⟨N, hN⟩ := hremoval (boundaryContraction S target) hcc
    (boundaryAlpha S target) (boundaryAlpha_pos S hS htarget) δ hδ
  refine ⟨N, fun n hn ↦ ?_⟩
  obtain ⟨B, hBcard, hB⟩ := hN n hn
  refine ⟨B, hBcard, fun U hU hUB ↦ ?_⟩
  exact exists_nearby_boundary_lt_target A n U hU S hS k target htarget
    (hB U hU hUB)

end KunDecompositionStep
end NonsoficGroupsExist
