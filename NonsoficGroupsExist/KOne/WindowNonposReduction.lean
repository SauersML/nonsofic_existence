import NonsoficGroupsExist.KOne.ThetaStable
import NonsoficGroupsExist.KOne.WindowNonnegReduction

/-!
# Nonpositive windows die

The mirror of the nonnegative-window reduction, obtained for free
through the transpose anti-automorphism: a unit with value in the
degree window `[-N, 0]` transposes to one with value in `[0, N]`,
which lies in the diagonal class group, and membership transfers back
along the involution.
-/

namespace NonsoficGroupsExist
namespace BinaryLeavitt

open LeavittFamily MatrixDiagonalization

variable (k : Type) [Field k]

/-- **Nonpositive-window units lie in the diagonal class group.** -/
theorem window_nonpos_mem_stableUnits
    [Nontrivial (BinaryLeavittAlgebra k)] (N : ℕ)
    (u : (BinaryLeavittAlgebra k)ˣ)
    (hu : (u : BinaryLeavittAlgebra k) ∈ Submodule.span k
      ((family k).degreeMonomials (-(N : ℤ) - 1) 0)) :
    u ∈ stableUnits (BinaryLeavittAlgebra k) := by
  have hθ : ((thetaUnit k u : (BinaryLeavittAlgebra k)ˣ) :
      BinaryLeavittAlgebra k) ∈ Submodule.span k
      ((family k).degreeMonomials 0 ((N : ℤ) + 1)) := by
    rw [thetaUnit_val]
    have h1 := thetaHat_mem_span_degree k hu
    refine (family k).span_degreeMonomials_mono ?_ ?_ h1 <;> omega
  have hθH := window_nonneg_mem_stableUnits k N (thetaUnit k u) hθ
  exact (thetaUnit_mem_stableUnits_iff k u).mp hθH

end BinaryLeavitt
end NonsoficGroupsExist
