import NonsoficGroupsExist.Leavitt.GeneralCornerTheorem
import NonsoficGroupsExist.Leavitt.LeavittOverCommRing

/-!
# The corner theorem over the integral Leavitt algebra, at every rank

The general corner theorem specialized to `L_ℤ(1,2)`: for every `m ≥ 2`,
if `EL_m` and `EL_{m+1}` of the integral Leavitt algebra have property
`(T)` and the two compressor words are elementary, then `EL_{m+1}` is not
sofic.  The property-`(T)` hypotheses at general finitely generated rings
are exactly the open Ershov–Jaikin-Zapirain input, so this records the
precise conditional statement at every adjacent pair of ranks, extending
the rank-`(3,4)` conditional of `Leavitt/IntegralConditional`.
-/

namespace NonsoficGroupsExist
namespace IntegralGeneralCorner

open CommRingLeavitt GeneralScheme GeneralCornerTheorem

/-- **The conditional integral corner theorem at every rank.**  Given
property `(T)` for the elementary groups of `L_ℤ(1,2)` at ranks `m` and
`m + 1` with `m ≥ 2`, and the membership of the two compressor words,
`EL_{m+1}(L_ℤ(1,2))` is not sofic. -/
theorem integralLeavitt_corner_not_isSofic_of_propertyT
    {m : ℕ} (hm : 0 < m) (hm2 : 2 ≤ m)
    (hu : uUnit integralFamily (m := m) ∈
      elementaryGroup (Fin (m + 1)) IntegralLeavittAlgebra)
    (hz : zUnit integralFamily hm ∈
      elementaryGroup (Fin (m + 1)) IntegralLeavittAlgebra)
    (hTG : HasKazhdanPropertyT.{0, 0}
      (elementaryGroup (Fin (m + 1)) IntegralLeavittAlgebra))
    (hTΓ : HasKazhdanPropertyT.{0, 0}
      (elementaryGroup (Fin m) IntegralLeavittAlgebra)) :
    ¬ IsSofic (elementaryGroup (Fin (m + 1)) IntegralLeavittAlgebra) :=
  corner_not_isSofic integralFamily hm hm2 hu hz hTG hTΓ

end IntegralGeneralCorner
end NonsoficGroupsExist
