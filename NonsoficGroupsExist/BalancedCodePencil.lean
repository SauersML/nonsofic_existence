import NonsoficGroupsExist.RefinedCodes
import NonsoficGroupsExist.CodeScalarMoves
import NonsoficGroupsExist.CodeChangeGlue
import NonsoficGroupsExist.EntrywiseKill

/-!
# Balanced code pencils are in the class group

If every corner entry `T(Cⱼ)·u⁻¹·S(Rᵢ)` of a unit's inverse over a
pair of complete codes is *balanced*, then after padding to a common
level the inverse is the transport of a scalar matrix along the
uniformly refined code pair.  Such a scalar matrix is forced to be
square and invertible — a kernel vector on either side would produce
a vanishing column `u⁻¹·S(w) = 0` or row, impossible for a unit —
and the value then factors as a code bijection times a scalar move,
both in the class group.  This is the terminal node of the master
induction.
-/

namespace NonsoficGroupsExist
namespace BinaryLeavitt

open LeavittFamily MatrixDiagonalization

variable (k : Type) [Field k]

/-- Words of a prefix family are `k`-independent: a vanishing
combination of `wordS`'s has vanishing coefficients. -/
theorem wordS_combo_eq_zero {ι : Type*} [Fintype ι]
    [Nontrivial (BinaryLeavittAlgebra k)]
    (w : ι → List (Fin 2))
    (hfree : ∀ ⦃p q : ι⦄, p ≠ q → ¬w p <+: w q)
    (c : ι → k) (h : (∑ q, c q • (family k).wordS (w q)) = 0) :
    ∀ q, c q = 0 := by
  classical
  intro q₀
  have hstrip : (family k).wordT (w q₀) *
      (∑ q, c q • (family k).wordS (w q)) = 0 := by
    rw [h, mul_zero]
  rw [Finset.mul_sum] at hstrip
  rw [Finset.sum_congr rfl (fun q _ ↦ show
      (family k).wordT (w q₀) * (c q • (family k).wordS (w q)) =
      if q₀ = q then c q • (1 : BinaryLeavittAlgebra k) else 0 from by
    rw [mul_smul_comm]
    by_cases hq : q₀ = q
    · rw [if_pos hq, hq, (family k).wordT_mul_wordS_self]
    · rw [if_neg hq, (family k).wordT_mul_wordS_of_incomparable _ _
        (hfree hq) (hfree (Ne.symm hq)), smul_zero])] at hstrip
  rw [Finset.sum_ite_eq Finset.univ q₀,
    if_pos (Finset.mem_univ q₀)] at hstrip
  rcases smul_eq_zero.mp hstrip with h1 | h1
  · exact h1
  · exact absurd h1 one_ne_zero

/-- Mirror: a vanishing combination of `wordT`'s has vanishing
coefficients. -/
theorem wordT_combo_eq_zero {ι : Type*} [Fintype ι]
    [Nontrivial (BinaryLeavittAlgebra k)]
    (w : ι → List (Fin 2))
    (hfree : ∀ ⦃p q : ι⦄, p ≠ q → ¬w p <+: w q)
    (c : ι → k) (h : (∑ q, c q • (family k).wordT (w q)) = 0) :
    ∀ q, c q = 0 := by
  classical
  intro q₀
  have hstrip : (∑ q, c q • (family k).wordT (w q)) *
      (family k).wordS (w q₀) = 0 := by
    rw [h, zero_mul]
  rw [Finset.sum_mul] at hstrip
  rw [Finset.sum_congr rfl (fun q _ ↦ show
      (c q • (family k).wordT (w q)) * (family k).wordS (w q₀) =
      if q = q₀ then c q • (1 : BinaryLeavittAlgebra k) else 0 from by
    rw [smul_mul_assoc]
    by_cases hq : q = q₀
    · rw [if_pos hq, hq, (family k).wordT_mul_wordS_self]
    · rw [if_neg hq, (family k).wordT_mul_wordS_of_incomparable _ _
        (hfree hq) (hfree (Ne.symm hq)), smul_zero])] at hstrip
  rw [Finset.sum_ite_eq' Finset.univ q₀,
    if_pos (Finset.mem_univ q₀)] at hstrip
  rcases smul_eq_zero.mp hstrip with h1 | h1
  · exact h1
  · exact absurd h1 one_ne_zero

end BinaryLeavitt
end NonsoficGroupsExist
