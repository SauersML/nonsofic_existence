import NonsoficGroupsExist.Kazhdan.KazhdanGenerators
import NonsoficGroupsExist.Kun.KunDecomposition

/-!
# Kun decomposition on a prescribed generating set

The compression criterion uses fixed concrete generator sets.  Property `(T)`
is first transferred to those sets, after which the proved Kun decomposition
theorem supplies the required expander decomposition on the original sofic
approximation.
-/

namespace NonsoficGroupsExist
namespace KunFixedDecomposition

variable {G : Type} [Group G] [Infinite G]

/-- A finite symmetric generating set containing the identity supports Kun's
expander decomposition for every sofic approximation of a property-`(T)`
group. -/
theorem expanderDecomposition
    (hT : HasKazhdanPropertyT.{0, 0} G)
    (S : Finset G) (hone : 1 ∈ S)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (A : SoficApproximation G) :
    Nonempty (ExpanderDecomposition A S) := by
  obtain ⟨δ, hδ⟩ := KazhdanGenerators.exists_pair_on_generators hT S hsymm hgen
  let ε : ℝ := min δ 1
  have hεpos : 0 < ε := lt_min hδ.1 zero_lt_one
  have hεδ : ε ≤ δ := min_le_left _ _
  have hεone : ε ≤ 1 := min_le_right _ _
  have hpair : IsKazhdanPair.{0, 0} G S ε := hδ.shrink hεpos hεδ
  exact KunDecomposition.exists_expanderDecomposition
    hpair S Finset.Subset.rfl hone hεone hsymm hgen A

end KunFixedDecomposition
end NonsoficGroupsExist
