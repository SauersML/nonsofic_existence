import NonsoficGroupsExist.Kun.KunRemoval

/-!
# Uniform removal along a sofic approximation

The additive error in the finite-model Kazhdan contraction can be chosen
arbitrarily small.  Applying the finite removal theorem at every sufficiently
large index gives Kun's uniform exceptional-set conclusion.
-/

namespace NonsoficGroupsExist
namespace KunAsymptoticRemoval

open KazhdanFiniteModel
open KazhdanGNS
open KunRemoval

variable {G : Type} [Group G]

/-- Property `(T)` supplies uniform finite removal data with contraction
coefficient below any prescribed positive target. -/
theorem finiteModel_propertyT_removal_below
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{0, 0} G Q ε)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S) (hεone : ε ≤ 1)
    (A : SoficApproximation G) (θ : ℝ) (hθ : 0 < θ) :
    ∃ k : ℕ, ∃ c : ℝ, 0 ≤ c ∧ c < θ ∧
      ∀ c' : ℝ, c < c' →
      ∀ α : ℝ, 0 < α →
      ∀ δ : ℝ, 0 < δ →
        ∃ N : ℕ, ∀ n ≥ N,
          ∃ B : Finset (A.model n),
            α ^ 2 * (c' - c) ^ 2 * (B.card : ℝ) ≤
              ((S.card + 1) ^ (2 * (k + 1)) : ℕ) *
                (δ ^ 2 * Fintype.card (A.model n) : ℝ) ∧
            ∀ U : Finset (A.model n), U.Nonempty → Disjoint U B →
              ‖indicatorDisplacement A n U S 0‖ < α * ‖indicator U‖ ∨
                ‖indicatorDisplacement A n U S k‖ <
                  c' * ‖indicatorDisplacement A n U S 0‖ := by
  obtain ⟨k, c, hc0, hc1, hcontract⟩ :=
    finiteModel_markovNormContraction_indicator_lt
      hQ S hQS hone hεone A θ hθ
  refine ⟨k, c, hc0, hc1, fun c' hcc' α hα δ hδ ↦ ?_⟩
  obtain ⟨N, hN⟩ := hcontract δ hδ
  refine ⟨N, fun n hn ↦ ?_⟩
  apply exists_removalSet A n S k c c' α δ hc0 hcc' hα hδ.le
  intro U
  simpa [indicatorDisplacement] using hN n hn U

/-- Property `(T)` supplies uniform finite removal data, with a quantitative
bound that is quadratic in the chosen additive error. -/
theorem finiteModel_propertyT_removal
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{0, 0} G Q ε)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S) (hεone : ε ≤ 1)
    (A : SoficApproximation G) :
    ∃ k : ℕ, ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧
      ∀ c' : ℝ, c < c' →
      ∀ α : ℝ, 0 < α →
      ∀ δ : ℝ, 0 < δ →
        ∃ N : ℕ, ∀ n ≥ N,
          ∃ B : Finset (A.model n),
            α ^ 2 * (c' - c) ^ 2 * (B.card : ℝ) ≤
              ((S.card + 1) ^ (2 * (k + 1)) : ℕ) *
                (δ ^ 2 * Fintype.card (A.model n) : ℝ) ∧
            ∀ U : Finset (A.model n), U.Nonempty → Disjoint U B →
              ‖indicatorDisplacement A n U S 0‖ < α * ‖indicator U‖ ∨
                ‖indicatorDisplacement A n U S k‖ <
                  c' * ‖indicatorDisplacement A n U S 0‖ := by
  exact finiteModel_propertyT_removal_below
    hQ S hQS hone hεone A 1 (by norm_num)

end KunAsymptoticRemoval
end NonsoficGroupsExist
