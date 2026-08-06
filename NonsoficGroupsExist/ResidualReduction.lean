import NonsoficGroupsExist.BinaryLeavittWindow
import NonsoficGroupsExist.ResidualMoves
import NonsoficGroupsExist.LeavittBalancedUnits

/-!
# Reduction of the rose-graph input to the narrow-window kill

The width reduction places every unit of the binary Leavitt algebra,
modulo the diagonal class group, in the degree window `[-1, 1]`.
Consequently the manuscript's rose-graph input `ScalarReduction`
follows from the single remaining statement `NarrowReduction`: every
unit with value in the `[-1,1]` window lies in the central class
group.  This theorem wires all the formalized machinery together and
isolates the one outstanding kill lemma in its weakest form.
-/

namespace NonsoficGroupsExist
namespace BinaryLeavitt

open MatrixDiagonalization

variable (k : Type) [Field k]

/-- The narrow-window kill statement: every unit of the binary
Leavitt algebra whose value lies in the degree window `[-1, 1]` is a
central scalar modulo the diagonal class group. -/
def NarrowReduction : Prop :=
  ∀ u : (BinaryLeavittAlgebra k)ˣ,
    (u : BinaryLeavittAlgebra k) ∈
      Submodule.span k ((family k).degreeMonomials (-1) 1) →
    u ∈ centralClassGroup (BinaryLeavittAlgebra k)

/-- Positive control: narrow units exist and the statement holds for
them when they are balanced — every balanced-valued unit is in the
central class group, and balanced values lie in the narrow window. -/
theorem narrowReduction_of_balanced (u : (BinaryLeavittAlgebra k)ˣ)
    {n : ℕ} (hu : (u : BinaryLeavittAlgebra k) ∈
      Submodule.span k ((family k).levelMonomials n)) :
    u ∈ centralClassGroup (BinaryLeavittAlgebra k) :=
  (family k).mem_centralClassGroup_of_val_mem_levelSpan
    (division k) n u hu

/-- **The chain**: the narrow-window kill implies the manuscript's
rose-graph input `ScalarReduction`. -/
theorem scalarReduction_of_narrowReduction
    (hnarrow : NarrowReduction k) :
    ScalarReduction (BinaryLeavittAlgebra k) := by
  refine scalarReduction_of_forall_mem_centralClassGroup ?_
  intro u
  obtain ⟨u', hmem, hval⟩ := exists_narrow_representative k u
  have hu' : u' ∈ centralClassGroup (BinaryLeavittAlgebra k) :=
    hnarrow u' hval
  have hH : u' * u⁻¹ ∈ centralClassGroup (BinaryLeavittAlgebra k) :=
    stableUnits_le_centralClassGroup hmem
  have := mul_mem (inv_mem hH) hu'
  rwa [show (u' * u⁻¹)⁻¹ * u' = u from by group] at this

/-- Checkpoint `B4` from the narrow-window kill. -/
theorem stableUnits_eq_top_of_narrowReduction
    (hnarrow : NarrowReduction k) :
    ∀ u : (BinaryLeavittAlgebra k)ˣ,
      u ∈ stableUnits (BinaryLeavittAlgebra k) :=
  stableUnits_eq_top k (scalarReduction_of_narrowReduction k hnarrow)

/-- `GL₂ = EL₂` from the narrow-window kill. -/
theorem glTwo_eq_elementary_of_narrowReduction
    (hnarrow : NarrowReduction k)
    (M : (Matrix (Fin 2) (Fin 2) (BinaryLeavittAlgebra k))ˣ) :
    M ∈ elementaryGroup (Fin 2) (BinaryLeavittAlgebra k) :=
  glTwo_eq_elementary k (scalarReduction_of_narrowReduction k hnarrow)
    M

/-- `GL₄ = EL₄` from the narrow-window kill. -/
theorem glFour_eq_elementary_of_narrowReduction
    (hnarrow : NarrowReduction k)
    (M : (Matrix (Fin 4) (Fin 4) (BinaryLeavittAlgebra k))ˣ) :
    M ∈ elementaryGroup (Fin 4) (BinaryLeavittAlgebra k) :=
  glFour_eq_elementary k (scalarReduction_of_narrowReduction k hnarrow)
    M


end BinaryLeavitt
end NonsoficGroupsExist
