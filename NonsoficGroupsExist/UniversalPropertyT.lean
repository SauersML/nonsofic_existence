import NonsoficGroupsExist.LeavittRankEquivalence
import NonsoficGroupsExist.UniversalRankFour
import NonsoficGroupsExist.FreeElementaryPropertyT

/-!
# Property `(T)` for the universal Leavitt compression groups

The four-generator free characteristic-two algebra surjects onto the universal
binary Leavitt quotient. Entrywise coefficient evaluation therefore gives a
surjection of elementary rank-three groups.  Property `(T)` passes across this
actual quotient, and the proved Leavitt rank equivalence transfers it from the
rank-three core to the rank-four ambient group.
-/

namespace NonsoficGroupsExist
namespace UniversalRankFour

open FreeRootFiltration

noncomputable section

/- `FreeAlgebra` and `Subalgebra` expose direct semiring instances in addition
to their characteristic-two ring instances.  Elementary matrices are indexed
by the latter.  Fix that coherent instance path for the coefficient map. -/
local instance freeCoefficientSemiring :
    Semiring (FreeRootFiltration.FreeRing UniversalLeavitt.Generator) :=
  (inferInstance : Ring
    (FreeRootFiltration.FreeRing UniversalLeavitt.Generator)).toSemiring

local instance concreteCoefficientSemiring : Semiring CoefficientRing :=
  (inferInstance : Ring CoefficientRing).toSemiring

/-- The universal quotient map, restated with the ring instances used by the
elementary-matrix construction. -/
noncomputable def coefficientMap :
    FreeRootFiltration.FreeRing UniversalLeavitt.Generator →+*
      CoefficientRing where
  toFun := UniversalLeavitt.quotientMap
  map_one' := UniversalLeavitt.quotientMap.map_one
  map_mul' := UniversalLeavitt.quotientMap.map_mul
  map_zero' := UniversalLeavitt.quotientMap.map_zero
  map_add' := UniversalLeavitt.quotientMap.map_add

/-- Evaluation of the four free generators is surjective onto the represented
coefficient algebra. -/
theorem coefficientMap_surjective : Function.Surjective coefficientMap :=
  RingQuot.mkAlgHom_surjective (ZMod 2) UniversalLeavitt.Relation

/-- The coefficient-evaluation map is onto the concrete elementary core. -/
theorem freeCoreMap_surjective :
    Function.Surjective (elementaryGroupMap (ι := Fin 3)
      coefficientMap) :=
  elementaryGroupMap_surjective_of_surjective
    coefficientMap coefficientMap_surjective

/-- The concrete rank-three core has property `(T)`, obtained from the
kernel-checked free-algebra theorem by the explicit coefficient quotient. -/
theorem core_hasKazhdanPropertyT : HasKazhdanPropertyT.{0, 0} Core := by
  exact HasKazhdanPropertyT.of_surjective
    (elementaryGroupMap (ι := Fin 3)
      coefficientMap) freeCoreMap_surjective
    (FreeElementaryPropertyT.freeElementary_hasKazhdanPropertyT
      UniversalLeavitt.Generator)

/-- The concrete rank-four ambient compression group has property `(T)`. -/
theorem ambient_hasKazhdanPropertyT : HasKazhdanPropertyT.{0, 0} Ambient :=
  family.rankFour_propertyT_of_rankThree core_hasKazhdanPropertyT

end
end UniversalRankFour
end NonsoficGroupsExist
