import NonsoficGroupsExist.ConcreteRankEquivalence
import NonsoficGroupsExist.ConcreteRankFour
import NonsoficGroupsExist.FreeElementaryPropertyT

/-!
# Property `(T)` for the concrete compression groups

The four-generator free characteristic-two algebra surjects onto the concrete
stream-operator algebra.  Entrywise coefficient evaluation therefore gives a
surjection of elementary rank-three groups.  Property `(T)` passes across this
actual quotient, and the proved Leavitt rank equivalence transfers it from the
rank-three core to the rank-four ambient group.
-/

namespace NonsoficGroupsExist
namespace ConcreteRankFour

open FreeRootFiltration

noncomputable section

/- `FreeAlgebra` and `Subalgebra` expose direct semiring instances in addition
to their characteristic-two ring instances.  Elementary matrices are indexed
by the latter.  Fix that coherent instance path for the coefficient map. -/
local instance freeCoefficientSemiring :
    Semiring (FreeRootFiltration.FreeRing ConcreteLeavitt.Generator) :=
  (inferInstance : Ring
    (FreeRootFiltration.FreeRing ConcreteLeavitt.Generator)).toSemiring

local instance concreteCoefficientSemiring : Semiring CoefficientRing :=
  (inferInstance : Ring CoefficientRing).toSemiring

/-- The concrete presentation, restated with the ring instances used by the
elementary-matrix construction.  This is the same evaluation function, not an
additional quotient assumption. -/
noncomputable def coefficientMap :
    FreeRootFiltration.FreeRing ConcreteLeavitt.Generator →+*
      CoefficientRing where
  toFun := ConcreteLeavitt.presentation
  map_one' := ConcreteLeavitt.presentation.map_one
  map_mul' := ConcreteLeavitt.presentation.map_mul
  map_zero' := ConcreteLeavitt.presentation.map_zero
  map_add' := ConcreteLeavitt.presentation.map_add

/-- Evaluation of the four free generators is surjective onto the represented
coefficient algebra. -/
theorem coefficientMap_surjective : Function.Surjective coefficientMap :=
  ConcreteLeavitt.presentation_surjective

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
      ConcreteLeavitt.Generator)

/-- The concrete rank-four ambient compression group has property `(T)`. -/
theorem ambient_hasKazhdanPropertyT : HasKazhdanPropertyT.{0, 0} Ambient :=
  family.rankFour_propertyT_of_rankThree core_hasKazhdanPropertyT

end
end ConcreteRankFour
end NonsoficGroupsExist
