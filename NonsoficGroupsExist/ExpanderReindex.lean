import NonsoficGroupsExist.Criterion
import NonsoficGroupsExist.SoficTransfer

/-!
# Reindexing expander decompositions

All fields of an expander decomposition are stable under a pointwise cofinal
reindexing.  This is used to synchronize the decompositions of a subgroup and
its ambient group.
-/

namespace NonsoficGroupsExist

namespace SoficApproximation

variable {G H : Type} [Group G] [Group H]

/-- Restriction along an embedding commutes with cofinal reindexing. -/
theorem comap_reindex (A : SoficApproximation G) (f : H →* G)
    (hf : Function.Injective f) (φ : ℕ → ℕ) (hφ : ∀ n, n ≤ φ n) :
    (A.comap f hf).reindex φ hφ = (A.reindex φ hφ).comap f hf := by
  rfl

end SoficApproximation

namespace ExpanderDecomposition

variable {G : Type} [Group G]
variable {A : SoficApproximation G} {T : Finset G}

noncomputable def reindex (D : ExpanderDecomposition A T)
    (φ : ℕ → ℕ) (hφ : ∀ n, n ≤ φ n) :
    ExpanderDecomposition (A.reindex φ hφ) T where
  blocks n := D.blocks (φ n)
  cheeger := D.cheeger
  cheeger_pos := D.cheeger_pos
  graph n := D.graph (φ n)
  vertexEquiv n := D.vertexEquiv (φ n)
  edit_negligible := by
    convert Negligible.reindex D.edit_negligible φ hφ using 1 <;> rfl
  editWitness n := D.editWitness (φ n)
  unmatched_negligible := by
    convert Negligible.reindex D.unmatched_negligible φ hφ using 1 <;> rfl
  edge_inside n := D.edge_inside (φ n)
  component_expands n := D.component_expands (φ n)
  almost_invariant := by
    intro t ht
    convert Negligible.reindex (D.almost_invariant t ht) φ hφ using 1 <;> rfl

end ExpanderDecomposition
end NonsoficGroupsExist
