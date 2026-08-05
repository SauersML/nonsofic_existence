import NonsoficGroupsExist.LeavittWindowReduction
import NonsoficGroupsExist.LeavittNormalForm
import NonsoficGroupsExist.BinaryLeavittDiagonal

/-!
# Every unit of the binary Leavitt algebra narrows to degrees [-1, 1]

The monomial normal form places every element of `L_k(1,2)` in a
finite degree window, so the window reduction applies: every unit is
congruent modulo the diagonal class group to a unit whose value lies
in the span of monomials of degree `-1`, `0`, or `1`.
-/

namespace NonsoficGroupsExist
namespace BinaryLeavitt

open MatrixDiagonalization

variable (k : Type) [Field k]

/-- Every element of the binary Leavitt algebra lies in a finite
degree window. -/
theorem exists_mem_span_degreeMonomials (x : BinaryLeavittAlgebra k) :
    ∃ lo hi : ℤ,
      x ∈ Submodule.span k ((family k).degreeMonomials lo hi) := by
  have hx : x ∈ Submodule.span k (monomialSet k) := by
    rw [span_monomialSet_eq_top]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hxmem =>
      obtain ⟨a, b, rfl⟩ := hxmem
      exact ⟨(a.length : ℤ) - b.length, (a.length : ℤ) - b.length,
        Submodule.subset_span ⟨a, b, le_rfl, le_rfl, rfl⟩⟩
  | zero => exact ⟨0, 0, Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
      obtain ⟨lox, hix, hmx⟩ := hx
      obtain ⟨loy, hiy, hmy⟩ := hy
      exact ⟨min lox loy, max hix hiy, Submodule.add_mem _
        ((family k).span_degreeMonomials_mono (min_le_left _ _)
          (le_max_left _ _) hmx)
        ((family k).span_degreeMonomials_mono (min_le_right _ _)
          (le_max_right _ _) hmy)⟩
  | smul r x _ hx =>
      obtain ⟨lo, hi, hm⟩ := hx
      exact ⟨lo, hi, Submodule.smul_mem _ r hm⟩

/-- **Narrow representatives**: every unit of `L_k(1,2)` is congruent
modulo the diagonal class group to a unit with degrees in `[-1, 1]`. -/
theorem exists_narrow_representative (u : (BinaryLeavittAlgebra k)ˣ) :
    ∃ u' : (BinaryLeavittAlgebra k)ˣ,
      u' * u⁻¹ ∈ stableUnits (BinaryLeavittAlgebra k) ∧
      (u' : BinaryLeavittAlgebra k) ∈
        Submodule.span k ((family k).degreeMonomials (-1) 1) := by
  obtain ⟨lo, hi, hm⟩ :=
    exists_mem_span_degreeMonomials k (u : BinaryLeavittAlgebra k)
  exact (family k).exists_window_reduction (division k) u hm

end BinaryLeavitt
end NonsoficGroupsExist
