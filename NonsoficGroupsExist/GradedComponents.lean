import NonsoficGroupsExist.BinaryLeavittWindow
import NonsoficGroupsExist.BaseChangeIndependence
import Mathlib.Data.Int.Interval

/-!
# Graded components of binary Leavitt elements

Every element of `L_k(1,2)` decomposes as a finite sum of pure-degree
components, and by graded independence the decomposition is unique.
This file provides the decomposition, the uniqueness transfer between
two decompositions of equal elements, and the componentwise reading
of products with pure-degree factors — the bookkeeping behind the
graded unit equations of the `K₁` computation.
-/

namespace NonsoficGroupsExist
namespace BinaryLeavitt

variable (k : Type) [Field k]

/-- **Graded decomposition**: every window element is a finite sum of
pure-degree components supported in the window. -/
theorem exists_components {lo hi : ℤ} {x : BinaryLeavittAlgebra k}
    (hx : x ∈ Submodule.span k ((family k).degreeMonomials lo hi)) :
    ∃ y : ℤ → BinaryLeavittAlgebra k,
      (∀ d, y d ∈
        Submodule.span k ((family k).degreeMonomials d d)) ∧
      (∀ d, d < lo ∨ hi < d → y d = 0) ∧
      x = ∑ d ∈ Finset.Icc lo hi, y d := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hxmem =>
      obtain ⟨a, b, hl, hh, rfl⟩ := hxmem
      refine ⟨fun d ↦ if d = (a.length : ℤ) - b.length then
        (family k).wordS a * (family k).wordT b else 0, ?_, ?_, ?_⟩
      · intro d
        beta_reduce
        by_cases hd : d = (a.length : ℤ) - b.length
        · rw [if_pos hd]
          exact Submodule.subset_span ⟨a, b, by omega, by omega, rfl⟩
        · rw [if_neg hd]
          exact Submodule.zero_mem _
      · intro d hd
        beta_reduce
        rw [if_neg (show ¬d = (a.length : ℤ) - b.length from by omega)]
      · refine ((Finset.sum_eq_single ((a.length : ℤ) - b.length)
          (fun d _ hd ↦ if_neg hd)
          (fun hd₀ ↦ absurd (Finset.mem_Icc.mpr ⟨hl, hh⟩)
            hd₀)).trans (if_pos rfl)).symm
  | zero =>
      exact ⟨0, fun d ↦ Submodule.zero_mem _, fun d _ ↦ rfl, by simp⟩
  | add x₁ x₂ _ _ h₁ h₂ =>
      obtain ⟨y₁, hy₁, hz₁, hs₁⟩ := h₁
      obtain ⟨y₂, hy₂, hz₂, hs₂⟩ := h₂
      refine ⟨y₁ + y₂, fun d ↦ Submodule.add_mem _ (hy₁ d) (hy₂ d),
        fun d hd ↦ ?_, ?_⟩
      · show y₁ d + y₂ d = 0
        rw [hz₁ d hd, hz₂ d hd, add_zero]
      · rw [hs₁, hs₂, ← Finset.sum_add_distrib]
        rfl
  | smul r x _ h =>
      obtain ⟨y, hy, hz, hs⟩ := h
      refine ⟨r • y, fun d ↦ Submodule.smul_mem _ _ (hy d),
        fun d hd ↦ ?_, ?_⟩
      · show r • y d = 0
        rw [hz d hd, smul_zero]
      · rw [hs, Finset.smul_sum]
        rfl

/-- **Uniqueness of components**: two componentwise decompositions of
the same element agree degreewise. -/
theorem components_unique {D : Finset ℤ}
    {y z : ℤ → BinaryLeavittAlgebra k}
    (hy : ∀ d ∈ D, y d ∈
      Submodule.span k ((family k).degreeMonomials d d))
    (hz : ∀ d ∈ D, z d ∈
      Submodule.span k ((family k).degreeMonomials d d))
    (hsum : ∑ d ∈ D, y d = ∑ d ∈ D, z d) :
    ∀ d ∈ D, y d = z d := by
  have hind := graded_independence_all (k := k) D (fun d ↦ y d - z d)
    (fun d hd ↦ Submodule.sub_mem _ (hy d hd) (hz d hd))
    (by rw [Finset.sum_sub_distrib, hsum, sub_self])
  intro d hd
  exact sub_eq_zero.mp (hind d hd)

end BinaryLeavitt
end NonsoficGroupsExist
