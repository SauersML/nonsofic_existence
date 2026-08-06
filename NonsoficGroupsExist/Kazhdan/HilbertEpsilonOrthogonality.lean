import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Quantitative orthogonality of Hilbert subspaces

This is the real-Hilbert-space form of the epsilon-orthogonality notion used
in the EJZ spectral criterion.  The accompanying norm estimate is the basic
calculation used in local codistance bounds.
-/

namespace NonsoficGroupsExist

universe v

namespace HilbertEpsilonOrthogonality

open Topology

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Two subspaces are `epsilon`-orthogonal when every cross inner product is
bounded by `epsilon` times the product of the norms. -/
def EpsilonOrthogonal (U V : Submodule ℝ E) (epsilon : ℝ) : Prop :=
  ∀ u ∈ U, ∀ v ∈ V,
    |inner ℝ u v| ≤ epsilon * ‖u‖ * ‖v‖

theorem symm {U V : Submodule ℝ E} {epsilon : ℝ}
    (h : EpsilonOrthogonal U V epsilon) :
    EpsilonOrthogonal V U epsilon := by
  intro v hv u hu
  rw [real_inner_comm]
  calc
    |inner ℝ u v| ≤ epsilon * ‖u‖ * ‖v‖ := h u hu v hv
    _ = epsilon * ‖v‖ * ‖u‖ := by ring

/-- Epsilon-orthogonality is inherited by smaller subspaces. -/
theorem mono {U V U' V' : Submodule ℝ E} {epsilon : ℝ}
    (h : EpsilonOrthogonal U V epsilon) (hU : U' ≤ U) (hV : V' ≤ V) :
    EpsilonOrthogonal U' V' epsilon := by
  intro u hu v hv
  exact h u (hU hu) v (hV hv)

/-- Increasing the allowed constant preserves epsilon-orthogonality. -/
theorem mono_epsilon {U V : Submodule ℝ E} {epsilon epsilon' : ℝ}
    (h : EpsilonOrthogonal U V epsilon) (hepsilon : epsilon ≤ epsilon') :
    EpsilonOrthogonal U V epsilon' := by
  intro u hu v hv
  calc
    |inner ℝ u v| ≤ epsilon * ‖u‖ * ‖v‖ := h u hu v hv
    _ ≤ epsilon' * ‖u‖ * ‖v‖ := by
      gcongr

/-- Epsilon-orthogonality bounds the norm of the orthogonal projection of
one subspace onto the other.  This operator form is the one used when
passing to invariant summands and directed unions. -/
theorem norm_starProjection_le {U V : Submodule ℝ E} {epsilon : ℝ}
    [U.HasOrthogonalProjection] (hepsilon : 0 ≤ epsilon)
    (h : EpsilonOrthogonal U V epsilon) {v : E} (hv : v ∈ V) :
    ‖U.starProjection v‖ ≤ epsilon * ‖v‖ := by
  let p : E := U.starProjection v
  have hpU : p ∈ U := U.starProjection_apply_mem v
  change ‖p‖ ≤ epsilon * ‖v‖
  by_cases hp : p = 0
  · rw [hp, norm_zero]
    positivity
  · have hppos : 0 < ‖p‖ := norm_pos_iff.mpr hp
    have hbound := h p hpU v hv
    have hinner : inner ℝ p v = ‖p‖ ^ 2 := by
      have horth : inner ℝ (v - p) p = 0 := by
        exact U.starProjection_inner_eq_zero v p hpU
      rw [inner_sub_left] at horth
      calc
        inner ℝ p v = inner ℝ v p := real_inner_comm v p
        _ = inner ℝ p p := by linarith
        _ = ‖p‖ ^ 2 := real_inner_self_eq_norm_sq p
    rw [hinner, abs_of_nonneg (sq_nonneg ‖p‖)] at hbound
    nlinarith

/-- A uniform projection bound implies epsilon-orthogonality. -/
theorem of_norm_starProjection_le {U V : Submodule ℝ E} {epsilon : ℝ}
    [U.HasOrthogonalProjection]
    (h : ∀ v ∈ V, ‖U.starProjection v‖ ≤ epsilon * ‖v‖) :
    EpsilonOrthogonal U V epsilon := by
  intro u hu v hv
  have hinner : inner ℝ u v = inner ℝ u (U.starProjection v) := by
    calc
      inner ℝ u v = inner ℝ (U.starProjection u) v := by
        rw [U.starProjection_eq_self_iff.mpr hu]
      _ = inner ℝ u (U.starProjection v) :=
        U.inner_starProjection_left_eq_right u v
  rw [hinner]
  calc
    |inner ℝ u (U.starProjection v)| ≤ ‖u‖ * ‖U.starProjection v‖ :=
      abs_real_inner_le_norm u (U.starProjection v)
    _ ≤ ‖u‖ * (epsilon * ‖v‖) :=
      mul_le_mul_of_nonneg_left (h v hv) (norm_nonneg u)
    _ = epsilon * ‖u‖ * ‖v‖ := by ring

/-- For a nonnegative constant, epsilon-orthogonality is equivalent to its
orthogonal-projection norm estimate. -/
theorem epsilonOrthogonal_iff_norm_starProjection_le
    {U V : Submodule ℝ E} {epsilon : ℝ} [U.HasOrthogonalProjection]
    (hepsilon : 0 ≤ epsilon) :
    EpsilonOrthogonal U V epsilon ↔
      ∀ v ∈ V, ‖U.starProjection v‖ ≤ epsilon * ‖v‖ :=
  ⟨fun h v hv ↦ norm_starProjection_le hepsilon h (v := v) hv,
    of_norm_starProjection_le⟩

/-- Epsilon-orthogonality passes through an increasing dense family of
orthogonal projections.  This is the analytic directed-limit step in the
universal class-two argument: the substantive finite-stage estimate is kept
as the explicit hypothesis `hproj`, while density removes the finite-stage
cutoff. -/
theorem of_monotone_starProjection
    {ι : Type*} [SemilatticeSup ι] (hι : Nonempty ι)
    {U V : Submodule ℝ E} {epsilon : ℝ}
    (W : ι → Submodule ℝ E) [∀ i, (W i).HasOrthogonalProjection]
    (hW : Monotone W) (hdense : ⊤ ≤ (⨆ i, W i).topologicalClosure)
    (hproj : ∀ i u, u ∈ U → ∀ v, v ∈ V →
      |inner ℝ ((W i).starProjection u) ((W i).starProjection v)| ≤
        epsilon * ‖(W i).starProjection u‖ * ‖(W i).starProjection v‖) :
    EpsilonOrthogonal U V epsilon := by
  haveI := hι
  intro u hu v hv
  have huT : Filter.Tendsto (fun i ↦ (W i).starProjection u) Filter.atTop (𝓝 u) :=
    Submodule.starProjection_tendsto_self W hW u hdense
  have hvT : Filter.Tendsto (fun i ↦ (W i).starProjection v) Filter.atTop (𝓝 v) :=
    Submodule.starProjection_tendsto_self W hW v hdense
  have hleft : Filter.Tendsto
      (fun i ↦ |inner ℝ ((W i).starProjection u) ((W i).starProjection v)|)
      Filter.atTop (𝓝 |inner ℝ u v|) :=
    (huT.inner hvT).abs
  have hright : Filter.Tendsto
      (fun i ↦ epsilon * ‖(W i).starProjection u‖ * ‖(W i).starProjection v‖)
      Filter.atTop (𝓝 (epsilon * ‖u‖ * ‖v‖)) :=
    ((tendsto_const_nhds.mul huT.norm).mul hvT.norm)
  exact le_of_tendsto_of_tendsto hleft hright
    (Filter.Eventually.of_forall fun i ↦ hproj i u hu v hv)

/-- Exact orthogonality is zero-orthogonality in the quantitative sense. -/
theorem of_isOrtho {U V : Submodule ℝ E} (h : U ⟂ V) :
    EpsilonOrthogonal U V 0 := by
  intro u hu v hv
  rw [h.inner_eq hu hv]
  simp

/-- Epsilon-orthogonality bounds the norm of a sum. -/
theorem norm_add_sq_le {U V : Submodule ℝ E} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (h : EpsilonOrthogonal U V epsilon)
    {u v : E} (hu : u ∈ U) (hv : v ∈ V) :
    ‖u + v‖ ^ 2 ≤
      (1 + epsilon) * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  have hinnerAbs := h u hu v hv
  have hinner : inner ℝ u v ≤ epsilon * ‖u‖ * ‖v‖ :=
    (le_abs_self _).trans hinnerAbs
  have hab : 2 * ‖u‖ * ‖v‖ ≤ ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
    nlinarith [sq_nonneg (‖u‖ - ‖v‖)]
  have hepsab : epsilon * (2 * ‖u‖ * ‖v‖) ≤
      epsilon * (‖u‖ ^ 2 + ‖v‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hab hepsilon
  rw [norm_add_sq_real]
  nlinarith

/-- The universal two-vector bound obtained from Cauchy--Schwarz. -/
theorem norm_add_sq_le_two (u v : E) :
    ‖u + v‖ ^ 2 ≤ 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  have hall : EpsilonOrthogonal (⊤ : Submodule ℝ E) ⊤ 1 := by
    intro x _ y _
    simpa using abs_real_inner_le_norm x y
  convert norm_add_sq_le (U := (⊤ : Submodule ℝ E)) (V := ⊤)
    (epsilon := 1) (by norm_num) hall (Submodule.mem_top : u ∈ (⊤ : Submodule ℝ E))
      (Submodule.mem_top : v ∈ (⊤ : Submodule ℝ E)) using 1
  norm_num

end HilbertEpsilonOrthogonality
end NonsoficGroupsExist
