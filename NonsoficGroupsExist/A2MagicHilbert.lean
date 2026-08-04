import NonsoficGroupsExist.A2MagicEnergy
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Hilbert space of A₂ vertex families

The spectral criterion lives in the genuine Hilbert direct sum of six copies
of the representation space.  This file constructs its constant and
vertex-fixed closed subspaces and proves that their intersection is zero in a
representation without invariant vectors.
-/

namespace NonsoficGroupsExist

universe u v

namespace A2MagicHilbert

open A2MagicGraph

variable {G : Type u} [Group G]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Hilbert `ℓ²`-sum of six copies of `E`. -/
abbrev Family (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :=
  PiLp 2 (fun _ : Fin 6 ↦ E)

/-- Constant six-tuples. -/
def constantSubspace : Submodule ℝ (Family E) where
  carrier := {f | ∀ i, f i = f 0}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg i
    simp [hf i, hg i]
  smul_mem' := by
    intro c f hf i
    simp [hf i]

/-- Families whose coordinate at `i` is fixed by the corresponding magic
graph vertex group. -/
def vertexFixedSubspace (A : A2System G)
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) : Submodule ℝ (Family E) where
  carrier := {f | ∀ i,
    f i ∈ KazhdanFixedSpace.fixedSubspace rho (A.vertexGroup (vertex i))}
  zero_mem' := fun i ↦ (KazhdanFixedSpace.fixedSubspace rho _).zero_mem
  add_mem' := by
    intro f g hf hg i
    exact (KazhdanFixedSpace.fixedSubspace rho _).add_mem (hf i) (hg i)
  smul_mem' := by
    intro c f hf i
    exact (KazhdanFixedSpace.fixedSubspace rho _).smul_mem c (hf i)

theorem isClosed_constantSubspace :
    IsClosed (constantSubspace (E := E) : Set (Family E)) := by
  rw [show (constantSubspace (E := E) : Set (Family E)) =
      ⋂ i : Fin 6, {f | f i = f 0} by
    ext f
    simp [constantSubspace]]
  exact isClosed_iInter fun i ↦ isClosed_eq
    (PiLp.continuous_apply (p := 2) (fun _ : Fin 6 ↦ E) i)
    (PiLp.continuous_apply (p := 2) (fun _ : Fin 6 ↦ E) 0)

theorem isClosed_vertexFixedSubspace
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E)) :
    IsClosed (vertexFixedSubspace A rho : Set (Family E)) := by
  rw [show (vertexFixedSubspace A rho : Set (Family E)) =
      ⋂ i : Fin 6,
        (fun f : Family E ↦ f i) ⁻¹'
          (KazhdanFixedSpace.fixedSubspace rho
            (A.vertexGroup (vertex i)) : Set E) by
    ext f
    simp [vertexFixedSubspace]]
  exact isClosed_iInter fun i ↦
    (KazhdanFixedSpace.isClosed_fixedSubspace rho
      (A.vertexGroup (vertex i))).preimage
        (PiLp.continuous_apply (p := 2) (fun _ : Fin 6 ↦ E) i)

/-- The coordinatewise orthogonal projection to the six vertex fixed
spaces, bundled in the Hilbert direct sum. -/
noncomputable def vertexProjectionFamily [CompleteSpace E]
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (x : Family E) : Family E :=
  WithLp.toLp 2 fun i ↦
    (KazhdanFixedSpace.fixedProjection rho (A.vertexGroup (vertex i)) (x i) : E)

@[simp] theorem vertexProjectionFamily_apply [CompleteSpace E]
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (x : Family E) (i : Fin 6) :
    vertexProjectionFamily A rho x i =
      KazhdanFixedSpace.fixedProjection rho (A.vertexGroup (vertex i)) (x i) := rfl

theorem vertexProjectionFamily_mem [CompleteSpace E]
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (x : Family E) :
    vertexProjectionFamily A rho x ∈ vertexFixedSubspace A rho := by
  intro i
  exact (KazhdanFixedSpace.fixedProjection rho
    (A.vertexGroup (vertex i)) (x i)).property

/-- The Hilbert projection onto the vertex-fixed family subspace is exactly
the coordinatewise family of subgroup-fixed projections. -/
theorem starProjection_vertexFixedSubspace [CompleteSpace E]
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (x : Family E) :
    let W := vertexFixedSubspace A rho
    letI : CompleteSpace W :=
      (isClosed_vertexFixedSubspace A rho).completeSpace_coe
    W.starProjection x = vertexProjectionFamily A rho x := by
  let W := vertexFixedSubspace A rho
  letI : CompleteSpace W :=
    (isClosed_vertexFixedSubspace A rho).completeSpace_coe
  apply W.eq_starProjection_of_mem_orthogonal
  · exact vertexProjectionFamily_mem A rho x
  · rw [Submodule.mem_orthogonal]
    intro y hy
    rw [PiLp.inner_apply]
    apply Finset.sum_eq_zero
    intro i hi
    have hyi : y i ∈ KazhdanFixedSpace.fixedSubspace rho
        (A.vertexGroup (vertex i)) := hy i
    have horth : x i -
        (KazhdanFixedSpace.fixedProjection rho
          (A.vertexGroup (vertex i)) (x i) : E) ∈
        (KazhdanFixedSpace.fixedSubspace rho
          (A.vertexGroup (vertex i)))ᗮ := by
      let U := KazhdanFixedSpace.fixedSubspace rho
        (A.vertexGroup (vertex i))
      letI : CompleteSpace U :=
        (KazhdanFixedSpace.isClosed_fixedSubspace rho
          (A.vertexGroup (vertex i))).completeSpace_coe
      exact U.sub_starProjection_mem_orthogonal (x i)
    exact Submodule.inner_right_of_mem_orthogonal hyi horth

/-- Squared norm of the coordinatewise vertex projection. -/
theorem norm_vertexProjectionFamily_sq [CompleteSpace E]
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (x : Family E) :
    ‖vertexProjectionFamily A rho x‖ ^ 2 =
      ∑ i : Fin 6,
        ‖(KazhdanFixedSpace.fixedProjection rho
          (A.vertexGroup (vertex i)) (x i) : E)‖ ^ 2 := by
  exact PiLp.norm_sq_eq_of_L2 (fun _ : Fin 6 ↦ E)
    (vertexProjectionFamily A rho x)

/-- Constant family with value `x`. -/
noncomputable def constantFamily (x : E) : Family E :=
  WithLp.toLp 2 fun _ ↦ x

@[simp] theorem constantFamily_apply (x : E) (i : Fin 6) :
    constantFamily x i = x := rfl

theorem constantFamily_mem (x : E) :
    constantFamily x ∈ constantSubspace (E := E) := by
  intro i
  rfl

theorem norm_constantFamily_sq (x : E) :
    ‖constantFamily x‖ ^ 2 = 6 * ‖x‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [constantFamily]

/-- Hilbert-space form of the desired uniform vertex projection estimate. -/
def ConstantProjectionBound (A : A2System G) (gamma : ℝ) : Prop :=
  ∀ (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E],
    ∀ rho : G →* (E ≃ₗᵢ[ℝ] E),
      IsKazhdanPair.HasNoInvariantVectors G rho →
      ∀ x : E,
        ‖vertexProjectionFamily A rho (constantFamily x)‖ ^ 2 ≤
          gamma * ‖constantFamily x‖ ^ 2

/-- The Hilbert direct-sum projection estimate is exactly the pointwise
operator estimate used to obtain codistance. -/
theorem vertexProjectionBound_of_constantProjectionBound
    (A : A2System G) {gamma : ℝ}
    (h : ConstantProjectionBound.{u, v} A gamma) :
    A2System.VertexProjectionBound.{u, v} A gamma := by
  intro E _ _ _ rho hno x
  have hb := h E rho hno x
  rw [norm_vertexProjectionFamily_sq, norm_constantFamily_sq] at hb
  simp only [constantFamily_apply] at hb
  have hreindex :
      (∑ a : A2Root,
          ‖(KazhdanFixedSpace.fixedProjection rho (A.vertexGroup a) x : E)‖ ^ 2) =
        ∑ i : Fin 6,
          ‖(KazhdanFixedSpace.fixedProjection rho
            (A.vertexGroup (vertex i)) x : E)‖ ^ 2 := by
    exact (Equiv.sum_comp vertexEquiv
      (fun a ↦ ‖(KazhdanFixedSpace.fixedProjection rho
        (A.vertexGroup a) x : E)‖ ^ 2)).symm
  rw [hreindex, A2MagicGraph.a2Root_card]
  norm_num at hb ⊢
  nlinarith [hb]

/-- A constant vertex-fixed family would be a globally invariant vector. -/
theorem constant_inf_vertexFixed_eq_bot [CompleteSpace E]
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (hno : IsKazhdanPair.HasNoInvariantVectors G rho) :
    constantSubspace (E := E) ⊓ vertexFixedSubspace A rho = ⊥ := by
  apply le_antisymm
  · intro f hf
    have hc : ∀ i, f i = f 0 := hf.1
    have hv : ∀ i, f i ∈ KazhdanFixedSpace.fixedSubspace rho
        (A.vertexGroup (vertex i)) := hf.2
    have hroot (r : A2Root) : f 0 ∈
        KazhdanFixedSpace.fixedSubspace rho (A.rootAt r) := by
      let i : Fin 6 := vertexEquiv.symm r
      have hvi : f i ∈ KazhdanFixedSpace.fixedSubspace rho
          (A.vertexGroup r) := by
        have hvertex : vertex i = r := by
          exact vertexEquiv.apply_symm_apply r
        rw [← hvertex]
        exact hv i
      rw [← hc i]
      exact KazhdanFixedSpace.antitone rho (A.rootAt_le_vertexGroup r) hvi
    have hinv : ∀ g : G, rho g (f 0) = f 0 :=
      A.invariant_of_mem_root_fixedSubspaces rho (f 0) hroot
    have hz : f 0 = 0 := hno (f 0) hinv
    change f = 0
    apply PiLp.ext
    intro i
    rw [hc i, hz]
    rfl
  · exact bot_le

end A2MagicHilbert
end NonsoficGroupsExist
