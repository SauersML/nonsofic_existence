import NonsoficGroupsExist.Kazhdan.KazhdanFixedSpace
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Fixed points from bounded orthogonal orbits

This file proves the Hilbert-space fixed-point lemma used in the
property-(T) argument.  It is proved from the Hilbert projection theorem:
the closed convex hull of a bounded orbit has a unique point of least norm,
and orthogonal invariance forces that point to be fixed.
-/

namespace NonsoficGroupsExist

universe u v

namespace HilbertConvexFixedPoint

variable {G : Type u} [Group G]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The orbit of a vector under a subgroup of an orthogonal
representation. -/
def orbit (rho : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G) (x : E) : Set E :=
  {y | ∃ h : H, rho h.1 x = y}

theorem orbit_nonempty (rho : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G) (x : E) :
    (orbit rho H x).Nonempty := by
  refine ⟨x, ⟨⟨1, H.one_mem⟩, ?_⟩⟩
  simp

theorem orbit_stable (rho : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G) (x : E)
    (h : H) {y : E} (hy : y ∈ orbit rho H x) : rho h.1 y ∈ orbit rho H x := by
  rcases hy with ⟨k, rfl⟩
  refine ⟨h * k, ?_⟩
  simp [map_mul]

/-- The closed convex hull of an orbit is stable under the subgroup. -/
theorem closedConvexHull_orbit_stable (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (H : Subgroup G) (x : E) (h : H) {y : E}
    (hy : y ∈ closedConvexHull ℝ (orbit rho H x)) :
    rho h.1 y ∈ closedConvexHull ℝ (orbit rho H x) := by
  let K := closedConvexHull ℝ (orbit rho H x)
  have horbit : orbit rho H x ⊆ (rho h.1) ⁻¹' K := by
    intro z hz
    change rho h.1 z ∈ K
    exact subset_closedConvexHull (orbit_stable rho H x h hz)
  have hconv : Convex ℝ ((rho h.1) ⁻¹' K) :=
    (convex_closedConvexHull (𝕜 := ℝ)).linear_preimage
      (rho h.1).toContinuousLinearEquiv.toLinearEquiv.toLinearMap
  have hclosed : IsClosed ((rho h.1) ⁻¹' K) :=
    isClosed_closedConvexHull.preimage (rho h.1).continuous
  exact closedConvexHull_min horbit hconv hclosed hy

/-- A convex set has at most one point of minimal norm. -/
theorem eq_of_norm_eq_iInf {K : Set E} (hK : Convex ℝ K) {y z : E}
    (hyK : y ∈ K) (hzK : z ∈ K)
    (hy : ‖(0 : E) - y‖ = ⨅ w : K, ‖(0 : E) - w‖)
    (hz : ‖(0 : E) - z‖ = ⨅ w : K, ‖(0 : E) - w‖) : y = z := by
  have hy' := (norm_eq_iInf_iff_real_inner_le_zero hK hyK).mp hy z hzK
  have hz' := (norm_eq_iInf_iff_real_inner_le_zero hK hzK).mp hz y hyK
  have hy'' : inner ℝ y y ≤ inner ℝ y z := by
    rw [zero_sub, inner_neg_left, inner_sub_right] at hy'
    linarith
  have hz'' : inner ℝ z z ≤ inner ℝ z y := by
    rw [zero_sub, inner_neg_left, inner_sub_right] at hz'
    linarith
  have hself : inner ℝ (y - z) (y - z) ≤ 0 := by
    simp only [inner_sub_left, inner_sub_right]
    linarith [real_inner_comm y z]
  exact sub_eq_zero.mp (real_inner_self_nonpos.mp hself)

/-- A uniformly bounded orbit under an orthogonal subgroup action has a
fixed point within the same bound of the initial vector. -/
theorem exists_fixed_of_orbit_displacement_le [CompleteSpace E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G) (x : E) {delta : ℝ}
    (hbound : ∀ h : H, ‖rho h.1 x - x‖ ≤ delta) :
    ∃ y : E, (∀ h : H, rho h.1 y = y) ∧ ‖y - x‖ ≤ delta := by
  let K := closedConvexHull ℝ (orbit rho H x)
  have hKne : K.Nonempty :=
    (orbit_nonempty rho H x).mono subset_closedConvexHull
  have hKcomplete : IsComplete K := isClosed_closedConvexHull.isComplete
  have hKconvex : Convex ℝ K := convex_closedConvexHull
  obtain ⟨y, hyK, hymin⟩ :=
    exists_norm_eq_iInf_of_complete_convex hKne hKcomplete hKconvex (0 : E)
  have hyfixed : ∀ h : H, rho h.1 y = y := by
    intro h
    have himageK : rho h.1 y ∈ K :=
      closedConvexHull_orbit_stable rho H x h hyK
    have himagemin :
        ‖(0 : E) - rho h.1 y‖ = ⨅ w : K, ‖(0 : E) - w‖ := by
      simpa using hymin
    exact eq_of_norm_eq_iInf hKconvex himageK hyK himagemin hymin
  have horbit_ball : orbit rho H x ⊆ Metric.closedBall x delta := by
    intro z hz
    rcases hz with ⟨h, rfl⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    simpa [norm_sub_rev] using hbound h
  have hyball : y ∈ Metric.closedBall x delta :=
    closedConvexHull_min horbit_ball (convex_closedBall x delta)
      Metric.isClosed_closedBall hyK
  refine ⟨y, hyfixed, ?_⟩
  rw [Metric.mem_closedBall, dist_eq_norm] at hyball
  exact hyball

/-- Uniform displacement by a subgroup bounds the distance to its fixed
subspace.  The point in the subspace is constructed by the preceding
closed-convex-hull argument. -/
theorem exists_near_fixedSubspace [CompleteSpace E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G) (x : E) {delta : ℝ}
    (hbound : ∀ h : H, ‖rho h.1 x - x‖ ≤ delta) :
    ∃ y ∈ KazhdanFixedSpace.fixedSubspace rho H, ‖y - x‖ ≤ delta := by
  obtain ⟨y, hyfixed, hynear⟩ :=
    exists_fixed_of_orbit_displacement_le rho H x hbound
  exact ⟨y, (KazhdanFixedSpace.mem_fixedSubspace_iff rho H y).2
    (fun h hh ↦ hyfixed ⟨h, hh⟩), hynear⟩

end HilbertConvexFixedPoint
end NonsoficGroupsExist
