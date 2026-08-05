import NonsoficGroupsExist.FreeRootFiltration

/-!
# Generator actions on the free root filtration

The relative-property-`(T)` proof uses elementary shears whose coefficients
are either `1` or one of the free ring generators.  This file proves their
exact action and records that a free generator advances coefficient degree by
one.  No bounded-generation statement is asserted.
-/

namespace NonsoficGroupsExist

namespace FreeRootActions

open scoped commutatorElement
open FreeAlgebraDegree FreeRootFiltration

variable (X : Type*) [Fintype X]

/-- A commutator with a free generator on the right advances the root
filtration by one degree. -/
theorem commutator_generator_right_mem_succ
    (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (x : X) {a : FreeRing X} {n : ℕ} (ha : a ∈ degreeLE X (ZMod 2) n) :
    ⁅elementaryRoot i j hij a,
        elementaryRoot j k hjk (FreeAlgebra.ι (ZMod 2) x)⁆ ∈
      rootDegreeSubgroup X i k hik (n + 1) := by
  rw [elementaryRoot_commutator i j k hij hjk hik]
  exact ⟨a * FreeAlgebra.ι (ZMod 2) x,
    mul_generator_mem_degreeLE_succ X (ZMod 2) x ha, rfl⟩

/-- A commutator with a free generator on the left advances the root
filtration by one degree. -/
theorem commutator_generator_left_mem_succ
    (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (x : X) {a : FreeRing X} {n : ℕ} (ha : a ∈ degreeLE X (ZMod 2) n) :
    ⁅elementaryRoot i j hij (FreeAlgebra.ι (ZMod 2) x),
        elementaryRoot j k hjk a⁆ ∈
      rootDegreeSubgroup X i k hik (n + 1) := by
  rw [elementaryRoot_commutator i j k hij hjk hik]
  exact ⟨FreeAlgebra.ι (ZMod 2) x * a,
    generator_mul_mem_degreeLE_succ X (ZMod 2) x ha, rfl⟩

omit [Fintype X] in
/-- The exact shear formula underlying the right-generator stage action. -/
theorem conjugate_by_generator
    (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (x : X) (a : FreeRing X) :
    elementaryRoot i j hij (FreeAlgebra.ι (ZMod 2) x) *
        elementaryRoot j k hjk a *
        (elementaryRoot i j hij (FreeAlgebra.ι (ZMod 2) x))⁻¹ =
      elementaryRoot i k hik (FreeAlgebra.ι (ZMod 2) x * a) *
        elementaryRoot j k hjk a :=
  elementaryRoot_conjugate i j k hij hjk hik _ _

end FreeRootActions

end NonsoficGroupsExist
