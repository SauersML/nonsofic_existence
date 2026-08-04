import NonsoficGroupsExist.A2MagicEnergy
import NonsoficGroupsExist.PositiveOperatorGap
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

/-- Reindex a concrete six-family by the six A₂ roots. -/
noncomputable def rootReindex (f : Family E) : A2Root → E :=
  fun r ↦ f (vertexEquiv.symm r)

@[simp] theorem rootReindex_vertex (f : Family E) (i : Fin 6) :
    rootReindex f (vertex i) = f i := by
  change f (vertexEquiv.symm (vertexEquiv i)) = f i
  rw [vertexEquiv.symm_apply_apply]

/-- Reindexing preserves the directed edge energy. -/
theorem edgeEnergy_rootReindex (f : Family E) :
    A2MagicEnergy.edgeEnergy (rootReindex f) =
      A2MagicLaplacian.directedEnergy f := by
  unfold A2MagicEnergy.edgeEnergy A2MagicLaplacian.directedEnergy
    A2MagicEnergy.edgeDifference
  rw [show (∑ r : A2Root,
      ∑ n : Fin 4, ‖rootReindex f r - rootReindex f (neighbor r n)‖ ^ 2) =
      ∑ i : Fin 6,
        ∑ n : Fin 4,
          ‖rootReindex f (vertexEquiv i) -
            rootReindex f (neighbor (vertexEquiv i) n)‖ ^ 2 by
    exact (Equiv.sum_comp vertexEquiv fun r ↦
      ∑ n : Fin 4, ‖rootReindex f r - rootReindex f (neighbor r n)‖ ^ 2).symm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro n hn
  rw [vertexEquiv_apply]
  rw [rootReindex_vertex]
  unfold rootReindex
  change ‖f i - f (vertexEquiv.symm (neighbor (vertex i) n))‖ ^ 2 =
    ‖f i - f (neighborIndex i n)‖ ^ 2
  rw [← vertex_neighborIndex]
  change ‖f i - f (vertexEquiv.symm (vertexEquiv (neighborIndex i n)))‖ ^ 2 = _
  rw [vertexEquiv.symm_apply_apply]

theorem rootLaplacian_rootReindex_vertex (f : Family E) (i : Fin 6) :
    A2MagicEnergy.rootLaplacian (rootReindex f) (vertex i) =
      A2MagicLaplacian.laplacian f i := by
  rw [A2MagicEnergy.rootLaplacian_vertex]
  congr 1
  funext j
  exact rootReindex_vertex f j

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

theorem rootReindex_mem_vertexFixedSubspace
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (f : vertexFixedSubspace A rho) (r : A2Root) :
    rootReindex (f : Family E) r ∈
      KazhdanFixedSpace.fixedSubspace rho (A.vertexGroup r) := by
  let i : Fin 6 := vertexEquiv.symm r
  have hi := f.property i
  have hir : vertex i = r := vertexEquiv.apply_symm_apply r
  rw [← hir]
  simpa using hi

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

/-- The magic-graph Laplacian as a linear map on the Hilbert family. -/
def laplacianFamilyLinear : Family E →ₗ[ℝ] Family E where
  toFun f := WithLp.toLp 2 (A2MagicLaplacian.laplacian f)
  map_add' := by
    intro f g
    apply PiLp.ext
    intro i
    change (∑ n : Fin 4,
      ((f i + g i) - (f (neighborIndex i n) + g (neighborIndex i n)))) =
        (∑ n : Fin 4, (f i - f (neighborIndex i n))) +
          ∑ n : Fin 4, (g i - g (neighborIndex i n))
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    module
  map_smul' := by
    intro c f
    apply PiLp.ext
    intro i
    change (∑ n : Fin 4,
      (c • f i - c • f (neighborIndex i n))) =
        c • ∑ n : Fin 4, (f i - f (neighborIndex i n))
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    module

@[simp] theorem laplacianFamilyLinear_apply (f : Family E) (i : Fin 6) :
    laplacianFamilyLinear f i = A2MagicLaplacian.laplacian f i := rfl

/-- The magic-graph Laplacian is bounded by `8` on the Hilbert direct sum. -/
noncomputable def laplacianFamily : Family E →L[ℝ] Family E :=
  laplacianFamilyLinear.mkContinuous 8 fun f ↦ by
    have hlap := A2MagicLaplacian.sum_laplacian_norm_sq_le_four_directedEnergy
      (fun i ↦ f i)
    have hedge := A2MagicLaplacian.directedEnergy_le_sixteen_sum_norm_sq
      (fun i ↦ f i)
    rw [← PiLp.norm_sq_eq_of_L2] at hedge
    have hsq :
        (∑ i : Fin 6, ‖A2MagicLaplacian.laplacian f i‖ ^ 2) ≤
          64 * ‖f‖ ^ 2 := by nlinarith
    apply (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (by norm_num) (norm_nonneg _))).mp
    rw [PiLp.norm_sq_eq_of_L2]
    change (∑ i : Fin 6, ‖A2MagicLaplacian.laplacian f i‖ ^ 2) ≤
      (8 * ‖f‖) ^ 2
    nlinarith

@[simp] theorem laplacianFamily_apply (f : Family E) (i : Fin 6) :
    laplacianFamily f i = A2MagicLaplacian.laplacian f i := rfl

theorem norm_laplacianFamily_sq (f : Family E) :
    ‖laplacianFamily f‖ ^ 2 =
      ∑ i : Fin 6, ‖A2MagicLaplacian.laplacian f i‖ ^ 2 := by
  exact PiLp.norm_sq_eq_of_L2 _ _

/-- Symmetry of the bounded family Laplacian. -/
theorem inner_laplacianFamily_comm (f g : Family E) :
    inner ℝ (laplacianFamily f) g = inner ℝ f (laplacianFamily g) := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  exact A2MagicLaplacian.sum_inner_laplacian_comm f g

/-- The family Laplacian quadratic form is half the directed edge energy. -/
theorem directedEnergy_eq_two_inner_laplacianFamily (f : Family E) :
    A2MagicLaplacian.directedEnergy f =
      2 * inner ℝ f (laplacianFamily f) := by
  rw [PiLp.inner_apply]
  exact A2MagicLaplacian.directedEnergy_eq_two_sum_inner_laplacian f

/-- Compression of the graph Laplacian to the closed vertex-fixed family
subspace. -/
noncomputable def compressedLaplacian [CompleteSpace E]
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E)) :
    vertexFixedSubspace A rho →L[ℝ] vertexFixedSubspace A rho := by
  let W := vertexFixedSubspace A rho
  letI : CompleteSpace W :=
    (isClosed_vertexFixedSubspace A rho).completeSpace_coe
  exact W.orthogonalProjectionOnto.comp (laplacianFamily.comp W.subtypeL)

/-- The compressed Laplacian is symmetric on the vertex-fixed subspace. -/
theorem inner_compressedLaplacian_comm [CompleteSpace E]
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (f g : vertexFixedSubspace A rho) :
    inner ℝ (compressedLaplacian A rho f) g =
      inner ℝ f (compressedLaplacian A rho g) := by
  let W := vertexFixedSubspace A rho
  letI : CompleteSpace W :=
    (isClosed_vertexFixedSubspace A rho).completeSpace_coe
  change inner ℝ (W.starProjection (laplacianFamily (f : Family E))) (g : Family E) =
    inner ℝ (f : Family E) (W.starProjection (laplacianFamily (g : Family E)))
  calc
    inner ℝ (W.starProjection (laplacianFamily (f : Family E))) (g : Family E) =
        inner ℝ (laplacianFamily (f : Family E)) (g : Family E) := by
      rw [W.inner_starProjection_left_eq_right,
        W.starProjection_eq_self_iff.mpr g.property]
    _ = inner ℝ (f : Family E) (laplacianFamily (g : Family E)) :=
      inner_laplacianFamily_comm _ _
    _ = inner ℝ (f : Family E)
        (W.starProjection (laplacianFamily (g : Family E))) := by
      rw [← W.inner_starProjection_left_eq_right,
        W.starProjection_eq_self_iff.mpr f.property]

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

theorem coe_compressedLaplacian_apply [CompleteSpace E]
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (f : vertexFixedSubspace A rho) :
    ((compressedLaplacian A rho f : vertexFixedSubspace A rho) : Family E) =
      vertexProjectionFamily A rho (laplacianFamily (f : Family E)) := by
  let W := vertexFixedSubspace A rho
  letI : CompleteSpace W :=
    (isClosed_vertexFixedSubspace A rho).completeSpace_coe
  change W.starProjection (laplacianFamily (f : Family E)) = _
  exact starProjection_vertexFixedSubspace A rho _

/-- The compressed quadratic form is still half the graph's directed edge
energy. -/
theorem directedEnergy_eq_two_inner_compressedLaplacian [CompleteSpace E]
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (f : vertexFixedSubspace A rho) :
    A2MagicLaplacian.directedEnergy (f : Family E) =
      2 * inner ℝ f (compressedLaplacian A rho f) := by
  let W := vertexFixedSubspace A rho
  letI : CompleteSpace W :=
    (isClosed_vertexFixedSubspace A rho).completeSpace_coe
  rw [directedEnergy_eq_two_inner_laplacianFamily]
  congr 1
  change inner ℝ (f : Family E) (laplacianFamily (f : Family E)) =
    inner ℝ (f : Family E)
      (W.starProjection (laplacianFamily (f : Family E)))
  rw [← W.inner_starProjection_left_eq_right,
    W.starProjection_eq_self_iff.mpr f.property]

/-- Positivity of the compressed Laplacian. -/
theorem compressedLaplacian_energy_nonneg [CompleteSpace E]
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (f : vertexFixedSubspace A rho) :
    0 ≤ inner ℝ f (compressedLaplacian A rho f) := by
  have hD : 0 ≤ A2MagicLaplacian.directedEnergy (f : Family E) := by
    unfold A2MagicLaplacian.directedEnergy
    positivity
  have hEq := directedEnergy_eq_two_inner_compressedLaplacian A rho f
  nlinarith

/-- Universal upper bound for the compressed quadratic form. -/
theorem compressedLaplacian_energy_le_eight_norm_sq [CompleteSpace E]
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (f : vertexFixedSubspace A rho) :
    inner ℝ f (compressedLaplacian A rho f) ≤ 8 * ‖f‖ ^ 2 := by
  have hD := A2MagicLaplacian.directedEnergy_le_sixteen_sum_norm_sq
    (fun i ↦ (f : Family E) i)
  rw [← PiLp.norm_sq_eq_of_L2] at hD
  change A2MagicLaplacian.directedEnergy (f : Family E) ≤
    16 * ‖f‖ ^ 2 at hD
  have hEq := directedEnergy_eq_two_inner_compressedLaplacian A rho f
  nlinarith

/-- The compressed operator norm squared is at most eight times its
quadratic form. -/
theorem norm_compressedLaplacian_sq_le_eight_energy [CompleteSpace E]
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (f : vertexFixedSubspace A rho) :
    ‖compressedLaplacian A rho f‖ ^ 2 ≤
      8 * inner ℝ f (compressedLaplacian A rho f) := by
  let W := vertexFixedSubspace A rho
  letI : CompleteSpace W :=
    (isClosed_vertexFixedSubspace A rho).completeSpace_coe
  have hproj : ‖compressedLaplacian A rho f‖ ≤
      ‖laplacianFamily (f : Family E)‖ := by
    exact W.norm_orthogonalProjectionOnto_apply_le _
  have hprojSq := sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.2 hproj
  have hlap := A2MagicLaplacian.sum_laplacian_norm_sq_le_four_directedEnergy
    (fun i ↦ (f : Family E) i)
  have hlap' : ‖laplacianFamily (f : Family E)‖ ^ 2 ≤
      4 * A2MagicLaplacian.directedEnergy (f : Family E) := by
    rw [PiLp.norm_sq_eq_of_L2]
    exact hlap
  have hEq := directedEnergy_eq_two_inner_compressedLaplacian A rho f
  nlinarith [hlap']

/-- Orthogonal decomposition of the full Laplacian into its compressed and
vertex-moving parts. -/
theorem norm_laplacianFamily_sq_eq_compressed_add_moving [CompleteSpace E]
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (f : vertexFixedSubspace A rho) :
    ‖laplacianFamily (f : Family E)‖ ^ 2 =
      ‖compressedLaplacian A rho f‖ ^ 2 +
        A2MagicEnergy.vertexMovingLaplacianEnergy A rho
          (rootReindex (f : Family E)) := by
  have hmove :
      A2MagicEnergy.vertexMovingLaplacianEnergy A rho
          (rootReindex (f : Family E)) =
        ∑ i : Fin 6,
          ‖KazhdanFixedSpace.subgroupMovingProjection rho
            (A.vertexGroup (vertex i))
            (A2MagicLaplacian.laplacian (f : Family E) i)‖ ^ 2 := by
    unfold A2MagicEnergy.vertexMovingLaplacianEnergy
    rw [show (∑ r : A2Root,
        ‖A2MagicEnergy.vertexMovingLaplacian A rho
          (rootReindex (f : Family E)) r‖ ^ 2) =
      ∑ i : Fin 6,
        ‖A2MagicEnergy.vertexMovingLaplacian A rho
          (rootReindex (f : Family E)) (vertexEquiv i)‖ ^ 2 by
      exact (Equiv.sum_comp vertexEquiv fun r ↦
        ‖A2MagicEnergy.vertexMovingLaplacian A rho
          (rootReindex (f : Family E)) r‖ ^ 2).symm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [vertexEquiv_apply]
    unfold A2MagicEnergy.vertexMovingLaplacian
    change ‖KazhdanFixedSpace.subgroupMovingProjection rho
      (A.vertexGroup (vertex i))
      (A2MagicEnergy.rootLaplacian
        (rootReindex (f : Family E)) (vertex i))‖ ^ 2 = _
    rw [rootLaplacian_rootReindex_vertex]
  have hcomp : ‖compressedLaplacian A rho f‖ ^ 2 =
      ∑ i : Fin 6,
        ‖(KazhdanFixedSpace.fixedProjection rho
          (A.vertexGroup (vertex i))
          (A2MagicLaplacian.laplacian (f : Family E) i) : E)‖ ^ 2 := by
    have hcoe := coe_compressedLaplacian_apply A rho f
    calc
      ‖compressedLaplacian A rho f‖ ^ 2 =
          ‖vertexProjectionFamily A rho
            (laplacianFamily (f : Family E))‖ ^ 2 :=
        congrArg (fun x : Family E ↦ ‖x‖ ^ 2) hcoe
      _ = ∑ i : Fin 6,
          ‖(KazhdanFixedSpace.fixedProjection rho
            (A.vertexGroup (vertex i))
            (A2MagicLaplacian.laplacian (f : Family E) i) : E)‖ ^ 2 := by
        rw [PiLp.norm_sq_eq_of_L2]
        rfl
  rw [PiLp.norm_sq_eq_of_L2, hcomp, hmove, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact KazhdanFixedSpace.norm_sq_fixedProjection_add_movingProjection
    rho (A.vertexGroup (vertex i)) (A2MagicLaplacian.laplacian (f : Family E) i)

/-- The characteristic-two local defect creates a strict spectral gap for
the compressed Laplacian. -/
theorem compressedLaplacian_quadratic_gap [CompleteSpace E]
    (A : A2System G)
    (hexp : ∀ (i j : Fin 3) (hij : i ≠ j),
      ∀ g ∈ A.root i j hij, g ^ 2 = 1)
    (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (f : vertexFixedSubspace A rho) :
    (2 * (1 - (Real.sqrt 2)⁻¹) / 3) *
        inner ℝ f (compressedLaplacian A rho f) ≤
      ‖compressedLaplacian A rho f‖ ^ 2 := by
  let D := A2MagicLaplacian.directedEnergy (f : Family E)
  let B := A2MagicEnergy.vertexMovingLaplacianEnergy A rho
    (rootReindex (f : Family E))
  let d : ℝ := 1 - (Real.sqrt 2)⁻¹
  let beta : ℝ := 2 - d / 3
  have hfixed (r : A2Root) :
      rootReindex (f : Family E) r ∈
        KazhdanFixedSpace.fixedSubspace rho (A.vertexGroup r) :=
    rootReindex_mem_vertexFixedSubspace A rho f r
  have hstrict : B ≤ beta * D := by
    have h := A2MagicEnergy.vertexMovingLaplacianEnergy_lt_two_mul_edgeEnergy
      A hexp rho (rootReindex (f : Family E)) hfixed
    rw [edgeEnergy_rootReindex] at h
    exact h
  have hgraph : 2 * D ≤ ‖laplacianFamily (f : Family E)‖ ^ 2 := by
    have h := A2MagicLaplacian.two_directedEnergy_le_sum_laplacian_norm_sq_general
      (fun i ↦ (f : Family E) i)
    calc
      2 * D ≤ ∑ i : Fin 6,
          ‖A2MagicLaplacian.laplacian (f : Family E) i‖ ^ 2 := h
      _ = ‖laplacianFamily (f : Family E)‖ ^ 2 :=
        (norm_laplacianFamily_sq _).symm
  have hsplit := norm_laplacianFamily_sq_eq_compressed_add_moving A rho f
  have henergy := directedEnergy_eq_two_inner_compressedLaplacian A rho f
  have hcombine : 2 * D ≤
      ‖compressedLaplacian A rho f‖ ^ 2 + beta * D := by
    calc
      2 * D ≤ ‖laplacianFamily (f : Family E)‖ ^ 2 := hgraph
      _ = ‖compressedLaplacian A rho f‖ ^ 2 + B := hsplit
      _ ≤ ‖compressedLaplacian A rho f‖ ^ 2 + beta * D := by
        simpa [add_comm] using
          add_le_add_right hstrict (‖compressedLaplacian A rho f‖ ^ 2)
  have hcomp : (2 - beta) * D ≤
      ‖compressedLaplacian A rho f‖ ^ 2 := by
    calc
      (2 - beta) * D = 2 * D - beta * D := by ring
      _ ≤ ‖compressedLaplacian A rho f‖ ^ 2 := by linarith
  have hcoef : 2 - beta = d / 3 := by
    dsimp [beta]
    ring
  change (2 * d / 3) * inner ℝ f (compressedLaplacian A rho f) ≤ _
  have henergyD : D = 2 * inner ℝ f (compressedLaplacian A rho f) := henergy
  calc
    (2 * d / 3) * inner ℝ f (compressedLaplacian A rho f) =
        (d / 3) * D := by rw [henergyD]; ring
    _ = (2 - beta) * D := by rw [hcoef]
    _ ≤ ‖compressedLaplacian A rho f‖ ^ 2 := hcomp

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

/-- In a representation without invariant vectors, the compressed
Laplacian has trivial kernel. -/
theorem compressedLaplacian_eq_zero_imp [CompleteSpace E]
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (hno : IsKazhdanPair.HasNoInvariantVectors G rho)
    (f : vertexFixedSubspace A rho)
    (hf : compressedLaplacian A rho f = 0) : f = 0 := by
  have hinner : inner ℝ f (compressedLaplacian A rho f) = 0 := by
    rw [hf]
    simp
  have hD : A2MagicLaplacian.directedEnergy (f : Family E) = 0 := by
    have hEq := directedEnergy_eq_two_inner_compressedLaplacian A rho f
    rw [hinner, mul_zero] at hEq
    exact hEq
  have hconst : (f : Family E) ∈ constantSubspace (E := E) := by
    intro i
    exact A2MagicLaplacian.eq_zero_directedEnergy_imp_constant
      (fun j ↦ (f : Family E) j) hD i
  have hinter : (f : Family E) ∈
      constantSubspace (E := E) ⊓ vertexFixedSubspace A rho :=
    ⟨hconst, f.property⟩
  rw [constant_inf_vertexFixed_eq_bot A rho hno] at hinter
  exact Subtype.ext (show (f : Family E) = 0 from hinter)

/-- The strict quadratic gap, positivity, symmetry, and trivial kernel give
an explicit bounded inverse estimate for the compressed Laplacian. -/
theorem norm_le_inverseGap_mul_norm_compressedLaplacian [CompleteSpace E]
    (A : A2System G)
    (hexp : ∀ (i j : Fin 3) (hij : i ≠ j),
      ∀ g ∈ A.root i j hij, g ^ 2 = 1)
    (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (hno : IsKazhdanPair.HasNoInvariantVectors G rho)
    (f : vertexFixedSubspace A rho) :
    let c : ℝ := 2 * (1 - (Real.sqrt 2)⁻¹) / 3
    ‖f‖ ≤ (c * (1 - Real.sqrt (1 - c / 8)))⁻¹ *
      ‖compressedLaplacian A rho f‖ := by
  let W := vertexFixedSubspace A rho
  letI : CompleteSpace W :=
    (isClosed_vertexFixedSubspace A rho).completeSpace_coe
  let c : ℝ := 2 * (1 - (Real.sqrt 2)⁻¹) / 3
  have hsqrt0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt1 : (1 : ℝ) < Real.sqrt 2 := by
    have hsqrtNonneg := Real.sqrt_nonneg 2
    nlinarith
  have hinv0 : 0 ≤ (Real.sqrt 2)⁻¹ := inv_nonneg.mpr hsqrt0.le
  have hinv1 : (Real.sqrt 2)⁻¹ < 1 :=
    (inv_lt_one₀ hsqrt0).2 hsqrt1
  have hc : 0 < c := by
    dsimp [c]
    nlinarith
  have hc8 : c ≤ 8 := by
    dsimp [c]
    nlinarith
  apply PositiveOperatorGap.norm_le_of_quadratic_gap
    (compressedLaplacian A rho) hc (by norm_num) hc8
  · intro x y
    exact inner_compressedLaplacian_comm A rho x y
  · intro x
    simpa [PositiveOperatorGap.energy] using
      compressedLaplacian_energy_nonneg A rho x
  · intro x
    simpa [c, PositiveOperatorGap.energy] using
      compressedLaplacian_quadratic_gap A hexp rho x
  · intro x
    simpa [PositiveOperatorGap.energy] using
      compressedLaplacian_energy_le_eight_norm_sq A rho x
  · intro x
    simpa [PositiveOperatorGap.energy] using
      norm_compressedLaplacian_sq_le_eight_energy A rho x
  · intro x hx
    exact compressedLaplacian_eq_zero_imp A rho hno x hx

end A2MagicHilbert
end NonsoficGroupsExist
