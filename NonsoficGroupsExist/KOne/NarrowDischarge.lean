import NonsoficGroupsExist.KOne.MasterInduction
import NonsoficGroupsExist.KOne.PencilForm
import NonsoficGroupsExist.KOne.ResidualReduction

/-!
# Discharging the narrow reduction

The top-level bridge: a narrow unit's scalar-pencil form
(`exists_pencil_form`) feeds the master induction at the uniform
depth-`(m+1)` codes, and class-group membership follows.  This
reduces the entire `K₁`-vanishing chain — `NarrowReduction`,
`ScalarReduction`, checkpoint `B4`, and `GL = EL` — to the single
named refinement statement `StuckReduction`.
-/

namespace NonsoficGroupsExist
namespace BinaryLeavitt

open LeavittFamily MatrixDiagonalization

variable (k : Type) [Field k]

/-- **The narrow reduction follows from the stuck-branch
reduction.** -/
theorem narrowReduction_of_stuckReduction
    [Nontrivial (BinaryLeavittAlgebra k)]
    (hstuck : StuckReduction k) : NarrowReduction k := by
  intro u hu
  have hdiv : ∀ x : BinaryLeavittAlgebra k, x ≠ 0 →
      ∃ p q : BinaryLeavittAlgebra k, p * x * q = 1 :=
    fun x hx ↦ exists_mul_mul_eq_one k hx
  obtain ⟨m, A₀, A₁, Cm, B₀, B₁, hval⟩ := exists_pencil_form k _ hu
  have hmem : u ∈ stableUnits (BinaryLeavittAlgebra k) := by
    refine pencil_unit_mem k hdiv hstuck
      (Fintype.card (Fin (m + 1) → Fin 2) +
        Fintype.card (Fin (m + 1) → Fin 2)) le_rfl
      (fullBinaryCode (m + 1))
      ((family k).fullBinaryCode_complete (m + 1))
      (fullBinaryCode (m + 1))
      ((family k).fullBinaryCode_complete (m + 1))
      A₀ A₁ Cm B₀ B₁ u ?_
    rw [hval]
    rfl
  exact stableUnits_le_centralClassGroup hmem

end BinaryLeavitt
end NonsoficGroupsExist
