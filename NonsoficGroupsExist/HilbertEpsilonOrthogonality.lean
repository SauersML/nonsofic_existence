import Mathlib.Analysis.InnerProductSpace.Orthogonal

/-!
# Quantitative orthogonality of Hilbert subspaces

This is the real-Hilbert-space form of the epsilon-orthogonality notion used
in the EJZ spectral criterion.  The accompanying norm estimate is the basic
calculation used in local codistance bounds.
-/

namespace NonsoficGroupsExist

universe v

namespace HilbertEpsilonOrthogonality

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
