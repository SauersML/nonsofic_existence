import NonsoficGroupsExist.Kazhdan
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.FixedSubmodule
import Mathlib.Algebra.Group.Subgroup.Map

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

/-- Restriction of an orthogonal representation to a subgroup. -/
def restrictRepresentation (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (L : Subgroup G) :
    L →* (E ≃ₗᵢ[ℝ] E) := ρ.comp L.subtype

@[simp] theorem restrictRepresentation_apply
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (L : Subgroup G) (g : L) :
    restrictRepresentation ρ L g = ρ g.1 := rfl

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

/-- Fixed vectors for `H`, viewed inside a larger subgroup `L`, are exactly
the original `H`-fixed vectors. -/
theorem fixedSubspace_subgroupOf_eq (ρ : G →* (E ≃ₗᵢ[ℝ] E))
    (H L : Subgroup G) (hHL : H ≤ L) :
    fixedSubspace (restrictRepresentation ρ L) (H.subgroupOf L) =
      fixedSubspace ρ H := by
  ext x
  rw [mem_fixedSubspace_iff, mem_fixedSubspace_iff]
  constructor
  · intro hx h hh
    exact hx ⟨h, hHL hh⟩ (Subgroup.mem_subgroupOf.mpr hh)
  · intro hx h hh
    exact hx h.1 (Subgroup.mem_subgroupOf.mp hh)

/-- Inclusion of subgroups reverses inclusion of fixed subspaces. -/
theorem antitone (ρ : G →* (E ≃ₗᵢ[ℝ] E)) {H K : Subgroup G}
    (hHK : H ≤ K) : fixedSubspace ρ K ≤ fixedSubspace ρ H := by
  intro x hx
  rw [mem_fixedSubspace_iff] at hx ⊢
  intro h hh
  exact hx h (hHK hh)

/-- An element normalizing `H` preserves its fixed subspace. -/
theorem map_mem_fixedSubspace_of_mem_normalizer
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) {x : E}
    (hx : x ∈ fixedSubspace ρ H) : ρ g x ∈ fixedSubspace ρ H := by
  rw [mem_fixedSubspace_iff] at hx ⊢
  intro h hh
  have hconj : g⁻¹ * h * g ∈ H :=
    (Subgroup.mem_normalizer_iff''.mp hg h).mp hh
  calc
    ρ h (ρ g x) = ρ (h * g) x := by simp [map_mul]
    _ = ρ (g * (g⁻¹ * h * g)) x := by congr 2; group
    _ = ρ g (ρ (g⁻¹ * h * g) x) := by simp [map_mul]
    _ = ρ g x := by rw [hx _ hconj]

/-- A normalizing element also preserves the orthogonal complement of the
fixed subspace. -/
theorem map_mem_fixedSubspace_orthogonal_of_mem_normalizer
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) {x : E}
    (hx : x ∈ (fixedSubspace ρ H)ᗮ) :
    ρ g x ∈ (fixedSubspace ρ H)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro y hy
  have hginv : g⁻¹ ∈ Subgroup.normalizer (H : Set G) :=
    (Subgroup.normalizer (H : Set G)).inv_mem hg
  have hy' : ρ g⁻¹ y ∈ fixedSubspace ρ H :=
    map_mem_fixedSubspace_of_mem_normalizer ρ H hginv hy
  have hcancel : ρ g⁻¹ (ρ g x) = x := by simp
  calc
    inner ℝ y (ρ g x) = inner ℝ (ρ g⁻¹ y) (ρ g⁻¹ (ρ g x)) := by
      rw [(ρ g⁻¹).inner_map_map]
    _ = inner ℝ (ρ g⁻¹ y) x := by rw [hcancel]
    _ = 0 := Submodule.inner_right_of_mem_orthogonal hy' hx

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

/-- Fixed vectors of a join are exactly the vectors fixed by both subgroups. -/
theorem fixedSubspace_sup (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (H K : Subgroup G) :
    fixedSubspace ρ (H ⊔ K) = fixedSubspace ρ H ⊓ fixedSubspace ρ K := by
  apply le_antisymm
  · exact le_inf (antitone ρ le_sup_left) (antitone ρ le_sup_right)
  · intro x hx
    change x ∈ fixedSubspace ρ H ∧ x ∈ fixedSubspace ρ K at hx
    rw [mem_fixedSubspace_iff, mem_fixedSubspace_iff] at hx
    rw [mem_fixedSubspace_iff]
    intro g hg
    have hseed : ∀ s ∈ (H : Set G) ∪ (K : Set G), ρ s x = x := by
      intro s hs
      rcases hs with hs | hs
      · exact hx.1 s hs
      · exact hx.2 s hs
    apply fixed_of_mem_closure ρ ((H : Set G) ∪ (K : Set G)) x hseed g
    rwa [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]

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

/-- Orthogonal projection onto the fixed subspace of a normal subgroup
commutes with the ambient orthogonal representation. -/
theorem fixedProjection_equivariant_of_normal [CompleteSpace E]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G) [H.Normal]
    (g : G) (x : E) :
    (fixedProjection ρ H (ρ g x) : E) =
      ρ g (fixedProjection ρ H x : E) := by
  let U := fixedSubspace ρ H
  letI : CompleteSpace U := (isClosed_fixedSubspace ρ H).completeSpace_coe
  change U.starProjection (ρ g x) = ρ g (U.starProjection x)
  apply U.eq_starProjection_of_mem_orthogonal
  · exact map_mem_fixedSubspace_of_normal ρ H g
      (U.starProjection_apply_mem x)
  · have hxorth : x - U.starProjection x ∈ Uᗮ :=
      U.sub_starProjection_mem_orthogonal x
    have hmap := map_mem_fixedSubspace_orthogonal_of_normal ρ H g hxorth
    simpa [map_sub] using hmap

/-- Orthogonal projection onto `H`-fixed vectors commutes with every element
that normalizes `H`. -/
theorem fixedProjection_equivariant_of_mem_normalizer [CompleteSpace E]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) (x : E) :
    (fixedProjection ρ H (ρ g x) : E) =
      ρ g (fixedProjection ρ H x : E) := by
  let U := fixedSubspace ρ H
  letI : CompleteSpace U := (isClosed_fixedSubspace ρ H).completeSpace_coe
  change U.starProjection (ρ g x) = ρ g (U.starProjection x)
  apply U.eq_starProjection_of_mem_orthogonal
  · exact map_mem_fixedSubspace_of_mem_normalizer ρ H hg
      (U.starProjection_apply_mem x)
  · have hxorth : x - U.starProjection x ∈ Uᗮ :=
      U.sub_starProjection_mem_orthogonal x
    have hmap := map_mem_fixedSubspace_orthogonal_of_mem_normalizer
      ρ H hg hxorth
    simpa [map_sub] using hmap

/-- If a normal subgroup `H` together with `K` generates the ambient group,
then their fixed subspaces are orthogonal in every representation without
nonzero invariant vectors.  This is the normal-subgroup orthogonality lemma
used in the EJZ magic-graph proof. -/
theorem fixedSubspaces_isOrtho_of_normal_generate [CompleteSpace E]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (H K : Subgroup G) [H.Normal]
    (hgen : H ⊔ K = ⊤)
    (hno : IsKazhdanPair.HasNoInvariantVectors G ρ) :
    fixedSubspace ρ H ⟂ fixedSubspace ρ K := by
  rw [Submodule.isOrtho_iff_inner_eq]
  intro u hu v hv
  let U := fixedSubspace ρ H
  letI : CompleteSpace U := (isClosed_fixedSubspace ρ H).completeSpace_coe
  let p : E := U.starProjection v
  have hpH : p ∈ fixedSubspace ρ H := U.starProjection_apply_mem v
  have hpK : p ∈ fixedSubspace ρ K := by
    rw [mem_fixedSubspace_iff]
    intro k hk
    have hvk : ρ k v = v :=
      (mem_fixedSubspace_iff ρ K v).mp hv k hk
    calc
      ρ k p = U.starProjection (ρ k v) := by
        exact (fixedProjection_equivariant_of_normal ρ H k v).symm
      _ = p := by rw [hvk]
  have hpglobal : ∀ g : G, ρ g p = p := by
    intro g
    have hseed : ∀ s ∈ (H : Set G) ∪ (K : Set G), ρ s p = p := by
      intro s hs
      rcases hs with hs | hs
      · exact (mem_fixedSubspace_iff ρ H p).mp hpH s hs
      · exact (mem_fixedSubspace_iff ρ K p).mp hpK s hs
    apply fixed_of_mem_closure ρ ((H : Set G) ∪ (K : Set G)) p hseed g
    rw [Subgroup.closure_union, Subgroup.closure_eq,
        Subgroup.closure_eq, hgen]
    exact Subgroup.mem_top g
  have hpzero : p = 0 := hno p hpglobal
  have hvorth : v - p ∈ (fixedSubspace ρ H)ᗮ :=
    U.sub_starProjection_mem_orthogonal v
  calc
    inner ℝ u v = inner ℝ u (p + (v - p)) := by congr 2; abel
    _ = inner ℝ u p + inner ℝ u (v - p) := inner_add_right _ _ _
    _ = 0 := by
      have horth : inner ℝ u (v - p) = 0 :=
        Submodule.inner_right_of_mem_orthogonal hu hvorth
      rw [hpzero] at horth ⊢
      simpa using horth

end KazhdanFixedSpace
end NonsoficGroupsExist
