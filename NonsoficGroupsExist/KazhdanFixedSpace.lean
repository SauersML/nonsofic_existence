import NonsoficGroupsExist.Kazhdan
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
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

/-- Restrict an orthogonal representation to a linear subspace preserved by
the action.  The inverse is induced by `g⁻¹`, so this constructs genuine
linear isometric equivalences on the subtype rather than merely endomorphisms. -/
noncomputable def restrictToInvariantSubspace
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (U : Submodule ℝ E)
    (hU : ∀ g : G, ∀ x ∈ U, ρ g x ∈ U) :
    G →* (U ≃ₗᵢ[ℝ] U) where
  toFun g :=
    LinearIsometryEquiv.ofSurjective
      { toLinearMap :=
          { toFun := fun x ↦ ⟨ρ g x.1, hU g x.1 x.2⟩
            map_add' := fun x y ↦ by ext; simp
            map_smul' := fun r x ↦ by ext; simp }
        norm_map' := fun x ↦ (ρ g).norm_map x.1 }
      (by
        intro y
        refine ⟨⟨ρ g⁻¹ y.1, hU g⁻¹ y.1 y.2⟩, ?_⟩
        ext
        simp)
  map_one' := by
    ext x
    simp
  map_mul' := by
    intro g h
    ext x
    simp [map_mul]

@[simp] theorem restrictToInvariantSubspace_apply
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (U : Submodule ℝ E)
    (hU : ∀ g : G, ∀ x ∈ U, ρ g x ∈ U) (g : G) (x : U) :
    (restrictToInvariantSubspace ρ U hU g x : E) = ρ g x.1 := rfl

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

/-- The moving subspace relative to a subgroup is the orthogonal complement
of that subgroup's fixed vectors. -/
noncomputable def subgroupMovingSubspace
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G) : Submodule ℝ E :=
  (fixedSubspace ρ H)ᗮ

/-- The moving subspace of a representation is the orthogonal complement of
its globally invariant vectors. -/
noncomputable def movingSubspace (ρ : G →* (E ≃ₗᵢ[ℝ] E)) : Submodule ℝ E :=
  subgroupMovingSubspace ρ ⊤

/-- The action restricted to its moving subspace. -/
noncomputable def movingRepresentation (ρ : G →* (E ≃ₗᵢ[ℝ] E)) :
    G →* (movingSubspace ρ ≃ₗᵢ[ℝ] movingSubspace ρ) :=
  restrictToInvariantSubspace ρ (movingSubspace ρ) fun g x hx ↦ by
    exact map_mem_fixedSubspace_orthogonal_of_normal ρ ⊤ g hx

@[simp] theorem movingRepresentation_apply
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (g : G) (x : movingSubspace ρ) :
    ((movingRepresentation ρ g x : movingSubspace ρ) : E) = ρ g x.1 := rfl

/-- By construction, the moving representation has no nonzero invariant
vectors.  This closes the logical step that is often left implicit when a
representation is split into fixed and moving parts. -/
theorem movingRepresentation_hasNoInvariantVectors
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) :
    IsKazhdanPair.HasNoInvariantVectors G (movingRepresentation ρ) := by
  intro x hx
  have hxfix : (x : E) ∈ fixedSubspace ρ ⊤ := by
    rw [mem_fixedSubspace_iff]
    intro g _
    have h := congrArg Subtype.val (hx g)
    simpa using h
  have hxorth : (x : E) ∈ (fixedSubspace ρ ⊤)ᗮ := x.2
  have hinner : inner ℝ (x : E) x = 0 :=
    Submodule.inner_right_of_mem_orthogonal hxfix hxorth
  apply Subtype.ext
  exact inner_self_eq_zero.mp hinner

/-- The restricted action of `H` on the orthogonal complement of its fixed
space. -/
noncomputable def subgroupMovingRepresentation
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G) :
    H →* (subgroupMovingSubspace ρ H ≃ₗᵢ[ℝ] subgroupMovingSubspace ρ H) :=
  restrictToInvariantSubspace (restrictRepresentation ρ H)
    (subgroupMovingSubspace ρ H) fun g x hx ↦ by
      exact map_mem_fixedSubspace_orthogonal_of_mem_normalizer ρ H
        (H.le_normalizer g.2) hx

@[simp] theorem subgroupMovingRepresentation_apply
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G) (g : H)
    (x : subgroupMovingSubspace ρ H) :
    ((subgroupMovingRepresentation ρ H g x : subgroupMovingSubspace ρ H) : E) =
      ρ g.1 x.1 := rfl

/-- The moving representation of a subgroup has no nonzero invariant
vectors, with no hypothesis on the original representation. -/
theorem subgroupMovingRepresentation_hasNoInvariantVectors
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G) :
    IsKazhdanPair.HasNoInvariantVectors H
      (subgroupMovingRepresentation ρ H) := by
  intro x hx
  have hxfix : (x : E) ∈ fixedSubspace ρ H := by
    rw [mem_fixedSubspace_iff]
    intro g hg
    have h := congrArg Subtype.val (hx ⟨g, hg⟩)
    simpa using h
  have hxorth : (x : E) ∈ (fixedSubspace ρ H)ᗮ := x.2
  have hinner : inner ℝ (x : E) x = 0 :=
    Submodule.inner_right_of_mem_orthogonal hxfix hxorth
  apply Subtype.ext
  exact inner_self_eq_zero.mp hinner

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

/-- Fixed vectors for a supremum of subgroups are exactly the vectors fixed
by every subgroup in the family. -/
theorem fixedSubspace_iSup {ι : Type*} (ρ : G →* (E ≃ₗᵢ[ℝ] E))
    (H : ι → Subgroup G) :
    fixedSubspace ρ (⨆ i, H i) = ⨅ i, fixedSubspace ρ (H i) := by
  apply le_antisymm
  · exact le_iInf fun i ↦ antitone ρ (le_iSup H i)
  · intro x hx
    rw [mem_fixedSubspace_iff]
    intro g hg
    let S : Set G := {g | ∃ i, g ∈ H i}
    have hclosure : Subgroup.closure S = ⨆ i, H i := by
      apply le_antisymm
      · rw [Subgroup.closure_le]
        rintro s ⟨i, hs⟩
        exact (le_iSup H i) hs
      · refine iSup_le fun i s hs ↦ ?_
        exact Subgroup.subset_closure ⟨i, hs⟩
    have hxS : ∀ s ∈ S, ρ s x = x := by
      rintro s ⟨i, hs⟩
      have hxall : ∀ i, x ∈ fixedSubspace ρ (H i) := by
        simpa using hx
      have hxi : x ∈ fixedSubspace ρ (H i) := hxall i
      exact (mem_fixedSubspace_iff ρ (H i) x).mp hxi s hs
    apply fixed_of_mem_closure ρ S x hxS g
    rwa [hclosure]

/-- Absence of nonzero invariant vectors is equivalently triviality of the
fixed subspace of the whole group. -/
theorem fixedSubspace_top_eq_bot
    (ρ : G →* (E ≃ₗᵢ[ℝ] E))
    (hno : IsKazhdanPair.HasNoInvariantVectors G ρ) :
    fixedSubspace ρ ⊤ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  apply hno x
  intro g
  exact (mem_fixedSubspace_iff ρ ⊤ x).mp hx g (Subgroup.mem_top g)

/-- If a family of subgroups exhausts the ambient group and the
representation has no invariant vectors, the orthogonal complements of the
finite-stage fixed spaces have dense supremum.  This is the group-theoretic
density input to the EJZ directed-limit argument. -/
theorem movingSubspaces_iSup_dense {ι : Type*} [CompleteSpace E]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (H : ι → Subgroup G)
    (hsup : ⨆ i, H i = ⊤)
    (hno : IsKazhdanPair.HasNoInvariantVectors G ρ) :
    ⊤ ≤ (⨆ i, (fixedSubspace ρ (H i))ᗮ).topologicalClosure := by
  apply le_of_eq
  symm
  rw [Submodule.topologicalClosure_eq_top_iff]
  rw [← Submodule.iInf_orthogonal]
  have hdouble : ∀ i, (fixedSubspace ρ (H i))ᗮᗮ =
      fixedSubspace ρ (H i) := by
    intro i
    rw [Submodule.orthogonal_orthogonal_eq_closure]
    exact (isClosed_fixedSubspace ρ (H i)).submodule_topologicalClosure_eq
  simp_rw [hdouble]
  rw [← fixedSubspace_iSup, hsup]
  exact fixedSubspace_top_eq_bot ρ hno

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

/-- Orthogonal projection onto the moving subspace relative to `H`. -/
noncomputable def subgroupMovingProjection [CompleteSpace E]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G) : E →L[ℝ] E := by
  let U := fixedSubspace ρ H
  letI : CompleteSpace U := (isClosed_fixedSubspace ρ H).completeSpace_coe
  exact Uᗮ.starProjection

/-- The moving projection is the residual after orthogonal projection onto
the subgroup-fixed space. -/
theorem subgroupMovingProjection_eq_sub_fixedProjection [CompleteSpace E]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G) (x : E) :
    subgroupMovingProjection ρ H x =
      x - (fixedProjection ρ H x : E) := by
  let U := fixedSubspace ρ H
  letI : CompleteSpace U := (isClosed_fixedSubspace ρ H).completeSpace_coe
  change Uᗮ.starProjection x = x - U.starProjection x
  exact congrArg (fun T : E →L[ℝ] E ↦ T x)
    (Submodule.starProjection_orthogonal U)

/-- Fixed and moving projections are orthogonal. -/
theorem fixedProjection_inner_movingProjection [CompleteSpace E]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G) (x : E) :
    inner ℝ (fixedProjection ρ H x : E)
      (subgroupMovingProjection ρ H x) = 0 := by
  let U := fixedSubspace ρ H
  letI : CompleteSpace U := (isClosed_fixedSubspace ρ H).completeSpace_coe
  apply Submodule.inner_right_of_mem_orthogonal
  · exact (fixedProjection ρ H x).property
  · exact Uᗮ.starProjection_apply_mem x

/-- Pythagoras for the fixed/moving decomposition of a vector. -/
theorem norm_sq_fixedProjection_add_movingProjection [CompleteSpace E]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G) (x : E) :
    ‖x‖ ^ 2 = ‖(fixedProjection ρ H x : E)‖ ^ 2 +
      ‖subgroupMovingProjection ρ H x‖ ^ 2 := by
  have hsum : x = (fixedProjection ρ H x : E) +
      subgroupMovingProjection ρ H x := by
    rw [subgroupMovingProjection_eq_sub_fixedProjection]
    abel
  calc
    ‖x‖ ^ 2 = ‖(fixedProjection ρ H x : E) +
        subgroupMovingProjection ρ H x‖ ^ 2 :=
      congrArg (fun y : E ↦ ‖y‖ ^ 2) hsum
    _ = ‖(fixedProjection ρ H x : E)‖ ^ 2 +
        ‖subgroupMovingProjection ρ H x‖ ^ 2 := by
      simpa [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_real
        (fixedProjection_inner_movingProjection ρ H x)

theorem subgroupMovingProjection_mem [CompleteSpace E]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G) (x : E) :
    subgroupMovingProjection ρ H x ∈ subgroupMovingSubspace ρ H := by
  let U := fixedSubspace ρ H
  letI : CompleteSpace U := (isClosed_fixedSubspace ρ H).completeSpace_coe
  exact Uᗮ.starProjection_apply_mem x

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

/-- Projection onto the moving part, the orthogonal complement of the
`H`-fixed subspace, commutes with the action of every element of `H`. -/
theorem movingProjection_equivariant_of_mem [CompleteSpace E]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G) {g : G} (hg : g ∈ H)
    (x : E) :
    ((fixedSubspace ρ H)ᗮ).starProjection (ρ g x) =
      ρ g (((fixedSubspace ρ H)ᗮ).starProjection x) := by
  let U := fixedSubspace ρ H
  letI : CompleteSpace U := (isClosed_fixedSubspace ρ H).completeSpace_coe
  have hfixed : U.starProjection (ρ g x) = ρ g (U.starProjection x) := by
    exact fixedProjection_equivariant_of_mem_normalizer ρ H
      (H.le_normalizer hg) x
  have hmoving (y : E) : Uᗮ.starProjection y = y - U.starProjection y := by
    rw [Submodule.starProjection_orthogonal]
    rfl
  rw [hmoving, hfixed, hmoving, map_sub]

/-- The named moving projection commutes with every element of the subgroup
that defines it. -/
theorem subgroupMovingProjection_equivariant_of_mem [CompleteSpace E]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (H : Subgroup G) {g : G} (hg : g ∈ H)
    (x : E) :
    subgroupMovingProjection ρ H (ρ g x) =
      ρ g (subgroupMovingProjection ρ H x) := by
  simpa [subgroupMovingProjection, subgroupMovingSubspace] using
    movingProjection_equivariant_of_mem ρ H hg x

/-- Projecting a `K`-fixed vector onto the moving part of a larger subgroup
`H` preserves `K`-fixedness. -/
theorem subgroupMovingProjection_mem_fixedSubspace [CompleteSpace E]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (K H : Subgroup G) (hKH : K ≤ H)
    {x : E} (hx : x ∈ fixedSubspace ρ K) :
    subgroupMovingProjection ρ H x ∈ fixedSubspace ρ K := by
  rw [mem_fixedSubspace_iff]
  intro g hg
  have hxg : ρ g x = x := (mem_fixedSubspace_iff ρ K x).mp hx g hg
  calc
    ρ g (subgroupMovingProjection ρ H x) =
        subgroupMovingProjection ρ H (ρ g x) :=
      (subgroupMovingProjection_equivariant_of_mem ρ H (hKH hg) x).symm
    _ = subgroupMovingProjection ρ H x := by rw [hxg]

/-- The projected vector, bundled in the moving subtype, lies in the fixed
subspace for `K` inside the moving representation of `H`. -/
theorem subgroupMovingProjection_mem_restricted_fixedSubspace
    [CompleteSpace E]
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (K H : Subgroup G) (hKH : K ≤ H)
    {x : E} (hx : x ∈ fixedSubspace ρ K) :
    (⟨subgroupMovingProjection ρ H x,
        subgroupMovingProjection_mem ρ H x⟩ : subgroupMovingSubspace ρ H) ∈
      fixedSubspace (subgroupMovingRepresentation ρ H) (K.subgroupOf H) := by
  rw [mem_fixedSubspace_iff]
  intro g hg
  apply Subtype.ext
  change ρ g.1 (subgroupMovingProjection ρ H x) =
    subgroupMovingProjection ρ H x
  exact (mem_fixedSubspace_iff ρ K _).mp
    (subgroupMovingProjection_mem_fixedSubspace ρ K H hKH hx)
    g.1 (Subgroup.mem_subgroupOf.mp hg)

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
