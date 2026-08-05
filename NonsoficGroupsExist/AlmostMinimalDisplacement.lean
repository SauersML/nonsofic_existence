import NonsoficGroupsExist.KazhdanFixedSpace
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Almost-minimal displacement vectors

The crucial tool in Shalom's finite-presentability theorem: an orthogonal
representation of a discrete group with almost-invariant vectors but no
nonzero invariant vectors admits, for every `M`, a vector of displacement
exactly one whose entire radius-`M` neighbourhood has displacement more
than one half.  The halving recursion of Bekka–de la Harpe–Valette's
Lemma 3.2.5 terminates because a non-terminating run would converge to a
nonzero invariant vector.
-/

namespace NonsoficGroupsExist
namespace AlmostMinimal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {G : Type*} [Group G]

/-- The maximal displacement of a vector over a finite set of group
elements. -/
noncomputable def displacement (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (Q : Finset G)
    (hQ : Q.Nonempty) (ξ : E) : ℝ :=
  Q.sup' hQ (fun g ↦ ‖ρ g ξ - ξ‖)

theorem norm_le_displacement (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (Q : Finset G)
    (hQ : Q.Nonempty) (ξ : E) {g : G} (hg : g ∈ Q) :
    ‖ρ g ξ - ξ‖ ≤ displacement ρ Q hQ ξ :=
  Finset.le_sup' _ hg

theorem displacement_le (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (Q : Finset G)
    (hQ : Q.Nonempty) (ξ : E) {r : ℝ}
    (h : ∀ g ∈ Q, ‖ρ g ξ - ξ‖ ≤ r) :
    displacement ρ Q hQ ξ ≤ r :=
  Finset.sup'_le hQ _ h

theorem displacement_nonneg (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (Q : Finset G)
    (hQ : Q.Nonempty) (ξ : E) : 0 ≤ displacement ρ Q hQ ξ := by
  obtain ⟨g, hg⟩ := hQ
  exact le_trans (norm_nonneg _) (norm_le_displacement ρ Q hQ ξ hg)

theorem displacement_smul (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (Q : Finset G)
    (hQ : Q.Nonempty) (c : ℝ) (ξ : E) :
    displacement ρ Q hQ (c • ξ) = |c| * displacement ρ Q hQ ξ := by
  unfold displacement
  rw [show (fun g ↦ ‖ρ g (c • ξ) - c • ξ‖) =
    (fun g ↦ |c| * ‖ρ g ξ - ξ‖) from by
    funext g
    rw [map_smul, ← smul_sub, norm_smul, Real.norm_eq_abs]]
  exact (Finset.comp_sup'_eq_sup'_comp hQ (fun r ↦ |c| * r)
    (fun x y ↦ mul_max_of_nonneg x y (abs_nonneg c))).symm

theorem displacement_le_add (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (Q : Finset G)
    (hQ : Q.Nonempty) (ξ η : E) :
    displacement ρ Q hQ ξ ≤ displacement ρ Q hQ η + 2 * ‖ξ - η‖ := by
  apply displacement_le
  intro g hg
  have h1 : ρ g ξ - ξ = (ρ g η - η) + (ρ g (ξ - η) - (ξ - η)) := by
    rw [map_sub]
    abel
  calc
    ‖ρ g ξ - ξ‖ ≤ ‖ρ g η - η‖ + ‖ρ g (ξ - η) - (ξ - η)‖ := by
      rw [h1]
      exact norm_add_le _ _
    _ ≤ ‖ρ g η - η‖ + (‖ρ g (ξ - η)‖ + ‖ξ - η‖) :=
      add_le_add_left (norm_sub_le _ _) _
    _ = ‖ρ g η - η‖ + 2 * ‖ξ - η‖ := by
      rw [(ρ g).norm_map]
      ring
    _ ≤ displacement ρ Q hQ η + 2 * ‖ξ - η‖ :=
      add_le_add_right (norm_le_displacement ρ Q hQ η hg) _

theorem displacement_lipschitz (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (Q : Finset G)
    (hQ : Q.Nonempty) (ξ η : E) :
    |displacement ρ Q hQ ξ - displacement ρ Q hQ η| ≤ 2 * ‖ξ - η‖ := by
  rw [abs_le]
  constructor
  · have := displacement_le_add ρ Q hQ η ξ
    rw [show ‖η - ξ‖ = ‖ξ - η‖ from norm_sub_rev η ξ] at this
    linarith
  · have := displacement_le_add ρ Q hQ ξ η
    linarith

theorem displacement_line_continuous (ρ : G →* (E ≃ₗᵢ[ℝ] E))
    (Q : Finset G) (hQ : Q.Nonempty) (ξ η : E) :
    Continuous (fun t : ℝ ↦ displacement ρ Q hQ (ξ + t • (η - ξ))) := by
  have hlip : LipschitzWith (2 * ‖η - ξ‖).toNNReal
      (fun t : ℝ ↦ displacement ρ Q hQ (ξ + t • (η - ξ))) := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    rw [Real.dist_eq, Real.dist_eq]
    have h1 := displacement_lipschitz ρ Q hQ (ξ + s • (η - ξ))
      (ξ + t • (η - ξ))
    have h2 : ‖(ξ + s • (η - ξ)) - (ξ + t • (η - ξ))‖ =
        |s - t| * ‖η - ξ‖ := by
      rw [show (ξ + s • (η - ξ)) - (ξ + t • (η - ξ)) =
        (s - t) • (η - ξ) from by
        rw [sub_smul]
        abel]
      rw [norm_smul, Real.norm_eq_abs]
    rw [h2] at h1
    have h3 : ((2 * ‖η - ξ‖).toNNReal : ℝ) = 2 * ‖η - ξ‖ :=
      Real.coe_toNNReal _ (by positivity)
    rw [h3]
    calc
      |displacement ρ Q hQ (ξ + s • (η - ξ)) -
          displacement ρ Q hQ (ξ + t • (η - ξ))| ≤
          2 * (|s - t| * ‖η - ξ‖) := h1
      _ = 2 * ‖η - ξ‖ * |s - t| := by ring
  exact hlip.continuous

theorem eq_zero_of_displacement_eq_zero (ρ : G →* (E ≃ₗᵢ[ℝ] E))
    (Q : Finset G) (hQ : Q.Nonempty)
    (hgen : Subgroup.closure (Q : Set G) = ⊤)
    (hnoinv : ∀ ξ : E, (∀ g : G, ρ g ξ = ξ) → ξ = 0)
    {ξ : E} (hξ : displacement ρ Q hQ ξ = 0) : ξ = 0 := by
  apply hnoinv
  have hfix : ∀ g ∈ Q, ρ g ξ = ξ := by
    intro g hg
    have h1 := norm_le_displacement ρ Q hQ ξ hg
    rw [hξ] at h1
    have h2 : ‖ρ g ξ - ξ‖ = 0 := le_antisymm h1 (norm_nonneg _)
    exact sub_eq_zero.1 (norm_eq_zero.1 h2)
  exact KazhdanFixedSpace.invariant_of_fixed_generators ρ
    (Q : Set G) hgen ξ hfix

end AlmostMinimal
end NonsoficGroupsExist
