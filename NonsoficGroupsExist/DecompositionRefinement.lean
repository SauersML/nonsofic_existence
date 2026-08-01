import NonsoficGroupsExist.ComponentRefinement
import NonsoficGroupsExist.BlockIndex

/-!
# Refinement supplied by an expander decomposition

This specializes the finite component-refinement theorem to the edited graph
and block partition carried by `ExpanderDecomposition`.  Every source block now
has a canonically chosen dominant target block for a fixed compressor
permutation.
-/

namespace NonsoficGroupsExist
namespace ExpanderDecomposition

variable {G : Type} [Group G] {S : SoficApproximation G} {T : Finset G}
variable (D : ExpanderDecomposition S T)

/-- The edited graph, transported to the approximation model. -/
noncomputable def modelGraph (n : ℕ) : FiniteMultiGraph :=
  (D.graph n).transport (S.model n) (D.vertexEquiv n)

/-- The edited graph induced on one component block. -/
noncomputable def componentGraph (n : ℕ) (y : S.model n) : FiniteMultiGraph :=
  (D.modelGraph n).induce ((D.blocks n).block y)

/-- Its vertex type is definitionally the source block. -/
noncomputable def componentVertexEquiv (n : ℕ) (y : S.model n) :
    (D.componentGraph n y).vertex ≃ (D.blocks n).block y :=
  Equiv.refl _

theorem componentGraph_expands (n : ℕ) (y : S.model n) :
    ((D.componentGraph n y).transport
      (blockModel (D.blocks n) y) (D.componentVertexEquiv n y)).HasCheegerLowerBound
        D.cheeger := by
  exact FiniteMultiGraph.transport_hasCheegerLowerBound (D.componentGraph n y)
    (blockModel (D.blocks n) y) (D.componentVertexEquiv n y)
      (by simpa [componentGraph, modelGraph] using D.component_expands n y)

/-- Dominant target selected for a source component and a compressor
permutation. -/
noncomputable def refineAt (Q : BlockStructure (S.model n))
    (q : Equiv.Perm (S.model n)) (y : S.model n) :
    ComponentRefinement (D.componentGraph n y) (D.blocks n) Q q y :=
  refineComponent (D.componentGraph n y) (D.blocks n) Q q y
    (D.componentVertexEquiv n y) (D.componentGraph_expands n y)

/-- The one-component leakage bound furnished by the decomposition. -/
theorem refineAt_leakage (Q : BlockStructure (S.model n))
    (q : Equiv.Perm (S.model n)) (y : S.model n) :
    D.cheeger *
        ((((D.blocks n).block y).image q \ (D.refineAt Q q y).target).card : ℝ) ≤
      4 * (((D.componentGraph n y).transport (blockModel (D.blocks n) y)
        (D.componentVertexEquiv n y)).crossingEdges
          (componentTargetLabel (D.blocks n) Q q y)).card :=
  (D.refineAt Q q y).cheeger_mul_leakage_le_crossing

/-! ### Refinement indexed once per distinct source component -/

/-- The distinct source components at index `n`. -/
abbrev componentIndex (n : ℕ) := BlockIndex (D.blocks n)

/-- A representative vertex chosen only to access the vertex-indexed graph
interface.  The associated block is exactly the indexed component. -/
noncomputable def componentRepresentative (n : ℕ) (C : D.componentIndex n) :
    S.model n :=
  BlockIndex.representative (D.blocks n) C

@[simp] theorem componentRepresentative_block (n : ℕ)
    (C : D.componentIndex n) :
    (D.blocks n).block (D.componentRepresentative n C) = C.block :=
  BlockIndex.block_representative (D.blocks n) C

/-- Dominant target for one distinctly indexed source component. -/
noncomputable def refineBlock (Q : BlockStructure (S.model n))
    (q : Equiv.Perm (S.model n)) (C : D.componentIndex n) :=
  D.refineAt Q q (D.componentRepresentative n C)

/-- The leakage estimate, now indexed over each source component exactly once. -/
theorem refineBlock_leakage (Q : BlockStructure (S.model n))
    (q : Equiv.Perm (S.model n)) (C : D.componentIndex n) :
    D.cheeger * ((C.block.image q \ (D.refineBlock Q q C).target).card : ℝ) ≤
      4 * (((D.componentGraph n (D.componentRepresentative n C)).transport
        (blockModel (D.blocks n) (D.componentRepresentative n C))
          (D.componentVertexEquiv n (D.componentRepresentative n C))).crossingEdges
            (componentTargetLabel (D.blocks n) Q q
              (D.componentRepresentative n C))).card := by
  simpa [refineBlock] using D.refineAt_leakage Q q (D.componentRepresentative n C)

end ExpanderDecomposition
end NonsoficGroupsExist
