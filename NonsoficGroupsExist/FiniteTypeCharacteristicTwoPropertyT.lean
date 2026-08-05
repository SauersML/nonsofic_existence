import NonsoficGroupsExist.FreeElementaryPropertyT
import NonsoficGroupsExist.ElementaryGroup
import Mathlib.RingTheory.FiniteType

/-!
# Property `(T)` for rank three over finite-type characteristic-two algebras

Every finite-type `ZMod 2`-algebra is a quotient of a free algebra on a finite
type. The kernel-checked free-algebra theorem therefore descends to its
elementary rank-three group.
-/

namespace NonsoficGroupsExist

open FreeRootFiltration

noncomputable section

variable {R : Type} [Ring R] [Algebra (ZMod 2) R]
  [Algebra.FiniteType (ZMod 2) R]

/-- The characteristic-two, rank-three case of the
Ershov--Jaikin-Zapirain theorem needed throughout this development. -/
theorem finiteTypeElementaryThree_hasKazhdanPropertyT :
    HasKazhdanPropertyT.{0, 0} (elementaryGroup (Fin 3) R) := by
  obtain ⟨X, hX, f, hf⟩ :=
    (Algebra.FiniteType.iff_quotient_freeAlgebra'
      (R := ZMod 2) (A := R)).mp inferInstance
  letI : Fintype X := hX
  exact HasKazhdanPropertyT.of_surjective
    (elementaryGroupMap (ι := Fin 3) f.toRingHom)
    (elementaryGroupMap_surjective_of_surjective f.toRingHom hf)
    (FreeElementaryPropertyT.freeElementary_hasKazhdanPropertyT X)

end
end NonsoficGroupsExist
