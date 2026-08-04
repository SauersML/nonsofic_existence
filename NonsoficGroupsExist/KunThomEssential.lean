import NonsoficGroupsExist.EssentialExpanderRepair
import NonsoficGroupsExist.KunThomTheorem

/-!
# Kun--Thom for an essential expander certificate

The selected graph is first repaired to an exact expanding action, after which
the kernel-checked exact-expander Kun--Thom theorem applies.  No implication
representing the cited theorem is accepted as an argument.
-/

namespace NonsoficGroupsExist
namespace KunThomEssential

open EssentialExpanderRepair

variable {K J : Type} [Group K] [Group J]

/-- A `MatchingCertificate`, together with actual Kazhdan-pair data for its
first factor, forces the commuting factor to be LEF. -/
theorem isLEF_of_matchingCertificate
    {Q : Finset K} {κ : ℝ} (hQ : IsKazhdanPair.{0, 0} K Q κ)
    (C : MatchingCertificate K J)
    (S : Finset K) (hQS : Q ⊆ S) (hKS : C.generatorsK ⊆ S)
    (hone : 1 ∈ S) (hκone : κ ≤ 1)
    : IsLEF J := by
  apply KunThomTheorem.isLEF_of_exactProductExpansion hQ S hQS hone hκone
    (repairedApproximation C) (expansionConstant_pos C)
  exact repairedDirected_expands_eventually C S hKS

end KunThomEssential
end NonsoficGroupsExist
