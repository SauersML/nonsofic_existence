import NonsoficGroupsExist.LeavittSimplicity
import NonsoficGroupsExist.LeavittDiagonalClass
import NonsoficGroupsExist.GLIsElementary

/-!
# The diagonal class of the binary Leavitt algebra

Checkpoints `B4`–`B6` assembled over the actual binary Leavitt algebra
`L_k(1,2)` for every field `k`.  Strong division is discharged
internally by simplicity (`exists_mul_mul_eq_one`), so the corner
calculus, the central-scalar collapse, and the rank-two and rank-four
`GL = EL` identifications (`prop:glel`) all hold conditionally on the
single remaining rose-graph `K₁` input: every unit is a central scalar
modulo the diagonal class.
-/

namespace NonsoficGroupsExist
namespace BinaryLeavitt

open MatrixDiagonalization

variable (k : Type) [Field k]

/-- Strong division for the binary Leavitt algebra, from simplicity. -/
theorem division :
    ∀ x : BinaryLeavittAlgebra k, x ≠ 0 →
      ∃ p q : BinaryLeavittAlgebra k, p * x * q = 1 :=
  fun _ hx ↦ exists_mul_mul_eq_one k hx

/-- **Checkpoint `B4` endpoint**: given the rose-graph `K₁` input, every
unit has elementary diagonal stabilization. -/
theorem stableUnits_eq_top
    (hscalar : ScalarReduction (BinaryLeavittAlgebra k)) :
    ∀ u : (BinaryLeavittAlgebra k)ˣ,
      u ∈ stableUnits (BinaryLeavittAlgebra k) :=
  (family k).stableUnits_eq_top (division k) hscalar

/-- **`prop:glel` at rank two**, conditional on the rose-graph `K₁`
input: `GL₂(L_k(1,2)) = EL₂(L_k(1,2))`. -/
theorem glTwo_eq_elementary
    (hscalar : ScalarReduction (BinaryLeavittAlgebra k))
    (A : (Matrix (Fin 2) (Fin 2) (BinaryLeavittAlgebra k))ˣ) :
    A ∈ elementaryGroup (Fin 2) (BinaryLeavittAlgebra k) :=
  mem_elementaryGroup_of_division_of_stable (division k)
    (fun u ↦ stableUnits_eq_top k hscalar u) A

/-- **`prop:glel` at rank four**, conditional on the rose-graph `K₁`
input: `GL₄(L_k(1,2)) = EL₄(L_k(1,2))`, through the self-similarity
isomorphism. -/
theorem glFour_eq_elementary
    (hscalar : ScalarReduction (BinaryLeavittAlgebra k))
    (A : (Matrix (Fin 4) (Fin 4) (BinaryLeavittAlgebra k))ˣ) :
    A ∈ elementaryGroup (Fin 4) (BinaryLeavittAlgebra k) :=
  (family k).glFour_eq_elementary_of_stable (division k)
    (fun u ↦ stableUnits_eq_top k hscalar u) A

end BinaryLeavitt
end NonsoficGroupsExist
