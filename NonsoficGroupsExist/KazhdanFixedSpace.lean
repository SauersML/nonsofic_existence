import NonsoficGroupsExist.Kazhdan
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.FixedSubmodule

/-!
# Fixed subspaces of subgroup representations

The EJZ spectral argument is expressed in terms of the closed Hilbert
subspaces fixed by its root and vertex subgroups.  This file constructs those
subspaces from an actual orthogonal representation and proves their basic
lattice and closure properties.
-/

namespace NonsoficGroupsExist

universe u v

namespace KazhdanFixedSpace

variable {G : Type u} [Group G]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The subspace fixed pointwise by a subgroup. -/
def fixedSubspace (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G) :
    Submodule ℝ E :=
  ⨅ h : H,
    ((ρ h.1).toContinuousLinearEquiv.toContinuousLinearMap.toLinearMap.fixedSubmodule)

@[simp] theorem mem_fixedSubspace_iff (ρ : G →* (E ≃ₗᵢ[ℝ] E))
    (H : Subgroup G) (x : E) :
    x ∈ fixedSubspace ρ H ↔ ∀ h ∈ H, ρ h x = x := by
  simp [fixedSubspace, LinearMap.mem_fixedSubmodule_iff]

/-- Fixed subspaces are closed, including for infinitely generated
subgroups. -/
theorem isClosed_fixedSubspace (ρ : G →* (E ≃ₗᵢ[ℝ] E))
    (H : Subgroup G) : IsClosed (fixedSubspace ρ H : Set E) := by
  rw [show (fixedSubspace ρ H : Set E) =
      ⋂ h : H, {x : E | ρ h.1 x = x} by
    ext x
    simp [mem_fixedSubspace_iff]]
  exact isClosed_iInter fun h ↦ isClosed_eq (ρ h.1).continuous continuous_id

/-- Inclusion of subgroups reverses inclusion of fixed subspaces. -/
theorem antitone (ρ : G →* (E ≃ₗᵢ[ℝ] E)) {H K : Subgroup G}
    (hHK : H ≤ K) : fixedSubspace ρ K ≤ fixedSubspace ρ H := by
  intro x hx
  rw [mem_fixedSubspace_iff] at hx ⊢
  intro h hh
  exact hx h (hHK hh)

/-- The fixed subspace of a normal subgroup is invariant under the ambient
group action. -/
theorem map_mem_fixedSubspace_of_normal (ρ : G →* (E ≃ₗᵢ[ℝ] E))
    (H : Subgroup G) [H.Normal] (g : G) {x : E}
    (hx : x ∈ fixedSubspace ρ H) : ρ g x ∈ fixedSubspace ρ H := by
  rw [mem_fixedSubspace_iff] at hx ⊢
  intro h hh
  have hconj : g⁻¹ * h * g ∈ H := by
    simpa using (inferInstance : H.Normal).conj_mem h hh g⁻¹
  calc
    ρ h (ρ g x) = ρ (h * g) x := by simp [map_mul]
    _ = ρ (g * (g⁻¹ * h * g)) x := by congr 2; group
    _ = ρ g (ρ (g⁻¹ * h * g) x) := by simp [map_mul]
    _ = ρ g x := by rw [hx _ hconj]

/-- The orthogonal complement of the fixed subspace of a normal subgroup is
also invariant under the ambient group action. -/
theorem map_mem_fixedSubspace_orthogonal_of_normal
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G) [H.Normal]
    (g : G) {x : E} (hx : x ∈ (fixedSubspace ρ H)ᗮ) :
    ρ g x ∈ (fixedSubspace ρ H)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro y hy
  have hy' : ρ g⁻¹ y ∈ fixedSubspace ρ H :=
    map_mem_fixedSubspace_of_normal ρ H g⁻¹ hy
  have hcancel : ρ g⁻¹ (ρ g x) = x := by simp
  calc
    inner ℝ y (ρ g x) = inner ℝ (ρ g⁻¹ y) (ρ g⁻¹ (ρ g x)) := by
      rw [(ρ g⁻¹).inner_map_map]
    _ = inner ℝ (ρ g⁻¹ y) x := by rw [hcancel]
    _ = 0 := Submodule.inner_right_of_mem_orthogonal hy' hx

/-- A vector fixed by a set is fixed by the subgroup it generates. -/
theorem fixed_of_mem_closure (ρ : G →* (E ≃ₗᵢ[ℝ] E))
    (S : Set G) (x : E) (hx : ∀ g ∈ S, ρ g x = x) :
    ∀ g ∈ Subgroup.closure S, ρ g x = x := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem g hg => exact hx g hg
  | one => simp
  | mul a b _ _ ha hb => simp [map_mul, ha, hb]
  | inv a _ ha =>
      have h := congrArg (fun z ↦ (ρ a)⁻¹ z) ha
      simpa [map_inv] using h.symm

/-- If a family of subgroups generates `G`, a vector fixed by each member is
globally invariant. -/
theorem invariant_of_fixed_generators (ρ : G →* (E ≃ₗᵢ[ℝ] E))
    (S : Set G) (hgen : Subgroup.closure S = ⊤) (x : E)
    (hx : ∀ g ∈ S, ρ g x = x) : ∀ g : G, ρ g x = x := by
  intro g
  apply fixed_of_mem_closure ρ S x hx g
  rw [hgen]
  exact Subgroup.mem_top g

/-- The fixed subspace carries the complete-space instance required by
orthogonal projection. -/
noncomputable def fixedProjection [CompleteSpace E] (ρ : G →* (E ≃ₗᵢ[ℝ] E))
    (H : Subgroup G) : E →L[ℝ] fixedSubspace ρ H := by
  letI : CompleteSpace (fixedSubspace ρ H) :=
    (isClosed_fixedSubspace ρ H).completeSpace_coe
  exact (fixedSubspace ρ H).orthogonalProjectionOnto

@[simp] theorem fixedProjection_mem [CompleteSpace E] (ρ : G →* (E ≃ₗᵢ[ℝ] E))
    (H : Subgroup G) (x : E) (h : H) :
    ρ h.1 (fixedProjection ρ H x : E) = fixedProjection ρ H x := by
  exact (mem_fixedSubspace_iff ρ H _).mp (fixedProjection ρ H x).property h h.property

end KazhdanFixedSpace
end NonsoficGroupsExist
