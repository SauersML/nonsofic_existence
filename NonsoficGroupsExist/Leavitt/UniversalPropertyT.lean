import NonsoficGroupsExist.PropertyT.FiniteTypeCharacteristicTwoPropertyT
import NonsoficGroupsExist.Leavitt.LeavittRankEquivalence
import NonsoficGroupsExist.Leavitt.UniversalRankFour

/-!
# Property `(T)` for the universal binary Leavitt compression groups

The universal binary Leavitt algebra is a finite-type `ZMod 2`-algebra, so the
general characteristic-two rank-three theorem applies directly. The explicit
Leavitt rank equivalence transfers property `(T)` to rank four.
-/

namespace NonsoficGroupsExist
namespace UniversalRankFour

/-- The universal-Leavitt rank-three core has property `(T)`. -/
theorem core_hasKazhdanPropertyT : HasKazhdanPropertyT.{0, 0} Core :=
  finiteTypeElementaryThree_hasKazhdanPropertyT

/-- The universal-Leavitt rank-four ambient compression group has property
`(T)`. -/
theorem ambient_hasKazhdanPropertyT : HasKazhdanPropertyT.{0, 0} Ambient :=
  family.rankFour_propertyT_of_rankThree core_hasKazhdanPropertyT

end UniversalRankFour
end NonsoficGroupsExist
