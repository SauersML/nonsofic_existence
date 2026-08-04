import NonsoficGroupsExist.KunAsymptoticRemoval
import NonsoficGroupsExist.KunIndicatorRounding
import NonsoficGroupsExist.KunRounding

/-!
# Small-boundary output after removal

Each of the two alternatives in Kun's removal proposition now produces an
explicit set: the input itself in the small-initial-displacement case, and a
thresholded Markov iterate in the contracted case.
-/

namespace NonsoficGroupsExist
namespace KunSmallBoundary

open KazhdanFiniteModel
open KazhdanGNS
open KunRemoval
open KunRounding
open KunIndicatorRounding
open FiniteMultiGraph
open scoped symmDiff

variable {G : Type} [Group G]

/-- Common boundary coefficient for the two removal alternatives. -/
def boundaryCoefficient (S : Finset G) (α c' : ℝ) : ℝ :=
  max (4 * (S.card : ℝ) ^ 2 * α) (8 * (S.card : ℝ) ^ 2 * c')

/-- Parameter for the small-initial-displacement alternative. -/
noncomputable def boundaryAlpha (S : Finset G) (target : ℝ) : ℝ :=
  target ^ 2 / (216 * (S.card : ℝ) ^ 2)

/-- Parameter for the contracted-displacement alternative. -/
noncomputable def boundaryContraction (S : Finset G) (target : ℝ) : ℝ :=
  target ^ 2 / (432 * (S.card : ℝ) ^ 2)

omit [Group G] in
theorem boundaryAlpha_pos (S : Finset G) (hS : S.Nonempty)
    {target : ℝ} (htarget : 0 < target) :
    0 < boundaryAlpha S target := by
  unfold boundaryAlpha
  have hcard : (0 : ℝ) < S.card := by
    exact_mod_cast Finset.card_pos.mpr hS
  positivity

omit [Group G] in
theorem boundaryContraction_pos (S : Finset G) (hS : S.Nonempty)
    {target : ℝ} (htarget : 0 < target) :
    0 < boundaryContraction S target := by
  unfold boundaryContraction
  have hcard : (0 : ℝ) < S.card := by
    exact_mod_cast Finset.card_pos.mpr hS
  positivity

omit [Group G] in
/-- The chosen parameters force the common squared-boundary coefficient below
the requested boundary-ratio target. -/
theorem boundaryCoefficient_lt (S : Finset G) (hS : S.Nonempty)
    {target : ℝ} (htarget : 0 < target) :
    boundaryCoefficient S (boundaryAlpha S target)
        (boundaryContraction S target) < target ^ 2 / 27 := by
  have hcard : (0 : ℝ) < S.card := by
    exact_mod_cast Finset.card_pos.mpr hS
  rw [boundaryCoefficient, max_lt_iff]
  constructor
  · unfold boundaryAlpha
    field_simp
    nlinarith [sq_pos_of_pos htarget]
  · unfold boundaryContraction
    field_simp
    nlinarith [sq_pos_of_pos htarget]

/-- Convert the normalized squared estimate into the requested linear
boundary ratio. -/
theorem boundary_lt_of_coefficient_lt
    {b m : ℕ} {coefficient target : ℝ} (hm : 0 < m)
    (htarget : 0 < target)
    (hbound : ((1 : ℝ) / 3) * ((2 : ℝ) / 3 - (1 : ℝ) / 3) ^ 2 *
      (b : ℝ) ^ 2 ≤ coefficient * (m : ℝ) ^ 2)
    (hcoefficient : coefficient < target ^ 2 / 27) :
    (b : ℝ) < target * m := by
  have hmReal : (0 : ℝ) < m := by exact_mod_cast hm
  have hscaled : coefficient * (m : ℝ) ^ 2 <
      (target ^ 2 / 27) * (m : ℝ) ^ 2 :=
    mul_lt_mul_of_pos_right hcoefficient (sq_pos_of_pos hmReal)
  have hsquares : (b : ℝ) ^ 2 < (target * m) ^ 2 := by
    norm_num at hbound
    nlinarith
  exact (sq_lt_sq₀ (by positivity)
    (mul_nonneg htarget.le hmReal.le)).mp hsquares

/-- Both removal alternatives yield a nearby set with the same uniform
quadratic boundary bound. -/
theorem exists_nearby_smallBoundary_of_removalAlternatives
    (A : SoficApproximation G) (n : ℕ) (U : Finset (A.model n))
    (S : Finset G) (hS : S.Nonempty) (k : ℕ) (α c' : ℝ) (hc' : 0 ≤ c')
    (halt : ‖indicatorDisplacement A n U S 0‖ < α * ‖indicator U‖ ∨
      ‖indicatorDisplacement A n U S k‖ <
        c' * ‖indicatorDisplacement A n U S 0‖) :
    ∃ W : Finset (A.model n),
      ((W ∆ U).card : ℝ) ≤
        9 * k ^ 2 * (S.card : ℝ)⁻¹ *
          generatorCutSize (A.model n) (A.map n) S U ∧
      ((1 : ℝ) / 3) * ((2 : ℝ) / 3 - (1 : ℝ) / 3) ^ 2 *
          ((generatorGraph (A.model n) S (A.map n)).boundaryCard W : ℝ) ^ 2 ≤
        boundaryCoefficient S α c' * (U.card : ℝ) ^ 2 := by
  rcases halt with hsmall | hcontract
  · obtain ⟨t, ht0, ht1, htbound⟩ :=
      exists_threshold_boundary_sq_of_small_initial
        A n U S hS α (by simpa [indicatorDisplacement] using hsmall.le)
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
    · rw [hWU]
      have hnonneg : 0 ≤ 9 * k ^ 2 * (S.card : ℝ)⁻¹ *
          generatorCutSize (A.model n) (A.map n) S U := by positivity
      simpa using hnonneg
    · have hcoeff :
          4 * (S.card : ℝ) ^ 2 * α ≤ boundaryCoefficient S α c' :=
        le_max_left _ _
      exact htbound.trans (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _))
  · obtain ⟨t, ht0, ht1, htbound⟩ :=
      exists_threshold_boundary_sq_of_contraction
        A n U S hS k c' hc'
        (by simpa [indicatorDisplacement] using hcontract.le)
    let W := (generatorGraph (A.model n) S (A.map n)).superlevel
      (finiteModelIndicatorIterate A n U S k) t
    have hclose := card_thresholdedIndicatorIterate_symmDiff_le_cut
      A n U S hS k t ht0 ht1
    have hcoeff :
        8 * (S.card : ℝ) ^ 2 * c' ≤ boundaryCoefficient S α c' :=
      le_max_right _ _
    refine ⟨W, ?_, htbound.trans
      (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _))⟩
    simpa [W, superlevelSet, FiniteMultiGraph.superlevel] using hclose

/-- Parameter-selected form with the standard linear boundary ratio. -/
theorem exists_nearby_boundary_lt_target
    (A : SoficApproximation G) (n : ℕ) (U : Finset (A.model n))
    (hU : U.Nonempty) (S : Finset G) (hS : S.Nonempty)
    (k : ℕ) (target : ℝ) (htarget : 0 < target)
    (halt : ‖indicatorDisplacement A n U S 0‖ <
          boundaryAlpha S target * ‖indicator U‖ ∨
      ‖indicatorDisplacement A n U S k‖ <
        boundaryContraction S target *
          ‖indicatorDisplacement A n U S 0‖) :
    ∃ W : Finset (A.model n),
      ((W ∆ U).card : ℝ) ≤
        9 * k ^ 2 * (S.card : ℝ)⁻¹ *
          generatorCutSize (A.model n) (A.map n) S U ∧
      ((generatorGraph (A.model n) S (A.map n)).boundaryCard W : ℝ) <
        target * U.card := by
  obtain ⟨W, hclose, hboundary⟩ :=
    exists_nearby_smallBoundary_of_removalAlternatives
      A n U S hS k (boundaryAlpha S target)
      (boundaryContraction S target)
      (boundaryContraction_pos S hS htarget).le halt
  refine ⟨W, hclose, ?_⟩
  exact boundary_lt_of_coefficient_lt (Finset.card_pos.mpr hU) htarget
    hboundary (boundaryCoefficient_lt S hS htarget)

end KunSmallBoundary
end NonsoficGroupsExist
