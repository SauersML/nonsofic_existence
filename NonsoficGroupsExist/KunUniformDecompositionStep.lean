import NonsoficGroupsExist.KunAsymptoticRemoval
import NonsoficGroupsExist.KunUniformRounding

/-!
# Uniform property-(T) replacement outside quantitative exceptional sets

The contraction and whole-trajectory estimates have separate maximal removal
arguments.  Taking the union of their two outputs gives the form needed by
Kun's finite partition recursion.  Crucially, the proximity coefficient below
depends only on the Kazhdan pair and the fixed generating set, not on the
requested output boundary ratio.
-/

namespace NonsoficGroupsExist
namespace KunUniformDecompositionStep

open KazhdanFiniteModel
open KazhdanGNS
open KunRemoval
open KunAsymptoticRemoval
open KunSmallBoundary
open KunUniformMovement
open KunUniformRemoval
open KunUniformRounding
open scoped symmDiff

variable {G : Type} [Group G]

/-- In sufficiently large finite sofic models, two quantitatively controlled
exceptional sets suffice simultaneously for late-displacement contraction and
for a horizon-independent whole-trajectory movement bound. -/
theorem finiteModel_propertyT_uniformSmallBoundaryReplacement
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{0, 0} G Q ε)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S) (hεone : ε ≤ 1)
    (A : SoficApproximation G) (target : ℝ) (htarget : 0 < target) :
    ∃ k : ℕ, ∃ c : ℝ,
      0 ≤ c ∧ c < boundaryContraction S target ∧
      ∀ δ : ℝ, 0 < δ →
        ∃ N : ℕ, ∀ n ≥ N,
          ∃ Bcontract Bmovement : Finset (A.model n),
            (boundaryAlpha S target) ^ 2 *
                (((c + boundaryContraction S target) / 2) - c) ^ 2 *
                (Bcontract.card : ℝ) ≤
              ((S.card + 1) ^ (2 * (k + 1)) : ℕ) *
                (δ ^ 2 * Fintype.card (A.model n) : ℝ) ∧
            (boundaryAlpha S target) ^ 2 *
                ((movementConstant S ε + 1) - movementConstant S ε) ^ 2 *
                (Bmovement.card : ℝ) ≤
              ((S.card + 1) ^ (2 * (k + 1)) : ℕ) *
                (δ ^ 2 * Fintype.card (A.model n) : ℝ) ∧
            ∀ U : Finset (A.model n), U.Nonempty →
                Disjoint U (Bcontract ∪ Bmovement) →
              ∃ W : Finset (A.model n),
                ((W ∆ U).card : ℝ) ≤
                  9 * (movementConstant S ε + 1) ^ 2 *
                    (S.card : ℝ)⁻¹ *
                      generatorCutSize (A.model n) (A.map n) S U ∧
                ((generatorGraph (A.model n) S (A.map n)).boundaryCard W : ℝ) <
                  target * U.card := by
  have hS : S.Nonempty := ⟨1, hone⟩
  have hcontraction := boundaryContraction_pos S hS htarget
  obtain ⟨k, c, hc0, hcHalf, hcontractRemoval⟩ :=
    finiteModel_propertyT_removal_below hQ S hQS hone hεone A
      (boundaryContraction S target / 2) (by positivity)
  have hcTarget : c < boundaryContraction S target := by linarith
  have hcLateBase : c < (c + boundaryContraction S target) / 2 := by
    linarith
  have hcLateTarget : (c + boundaryContraction S target) / 2 <
      boundaryContraction S target := by
    linarith
  refine ⟨k, c, hc0, hcTarget, fun δ hδ ↦ ?_⟩
  obtain ⟨Ncontract, hNcontract⟩ :=
    hcontractRemoval ((c + boundaryContraction S target) / 2) hcLateBase
      (boundaryAlpha S target) (boundaryAlpha_pos S hS htarget) δ hδ
  obtain ⟨Nmovement, hNmovement⟩ :=
    finiteModelIndicatorIterate_movement_eventually_lt
      hQ S hQS hone hεone A k δ hδ
  refine ⟨max Ncontract Nmovement, fun n hn ↦ ?_⟩
  have hnContract : Ncontract ≤ n := (le_max_left _ _).trans hn
  have hnMovement : Nmovement ≤ n := (le_max_right _ _).trans hn
  obtain ⟨Bcontract, hBcontractCard, hBcontract⟩ :=
    hNcontract n hnContract
  have hmovementAll (U : Finset (A.model n)) :
      ‖trajectoryMovement A n U S k‖ <
        movementConstant S ε * ‖indicatorDisplacement A n U S 0‖ +
          δ * Real.sqrt (Fintype.card (A.model n) : ℝ) := by
    simpa [trajectoryMovement, indicatorDisplacement] using
      hNmovement n hnMovement U
  have hmovementConstant : 0 < movementConstant S ε :=
    movementConstant_pos hQ S hone
  obtain ⟨Bmovement, hBmovementCard, hBmovement⟩ :=
    exists_uniformMovementRemoval A n S k
      (movementConstant S ε) (movementConstant S ε + 1)
      (boundaryAlpha S target) δ hmovementConstant.le (by linarith)
      (boundaryAlpha_pos S hS htarget) hδ.le hmovementAll
  refine ⟨Bcontract, Bmovement, hBcontractCard, hBmovementCard,
    fun U hU hUexceptional ↦ ?_⟩
  have hUcontract : Disjoint U Bcontract := by
    rw [Finset.disjoint_left] at hUexceptional ⊢
    intro y hyU hyB
    exact hUexceptional hyU (Finset.mem_union_left _ hyB)
  have hUmovement : Disjoint U Bmovement := by
    rw [Finset.disjoint_left] at hUexceptional ⊢
    intro y hyU hyB
    exact hUexceptional hyU (Finset.mem_union_right _ hyB)
  exact exists_nearby_boundary_lt_target_uniform A n U hU S hS k
    (movementConstant S ε + 1)
    ((c + boundaryContraction S target) / 2) target
    (by positivity) (by linarith) hcLateTarget htarget
    (hBcontract U hU hUcontract) (hBmovement U hU hUmovement)

end KunUniformDecompositionStep
end NonsoficGroupsExist
