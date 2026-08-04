import NonsoficGroupsExist.KunPartitionBoundary
import NonsoficGroupsExist.EdgeWitnessDistance

/-!
# Deleting edges between Kun partition blocks

This is the canonical first edit: retain every original edge occurrence whose
endpoints have the same block and delete every crossing occurrence.  Parallel
edges remain distinct, and the occurrence-level edit witness is explicit.
-/

namespace NonsoficGroupsExist
namespace KunBlockGraph

open FiniteMultiGraph

/-- Edge occurrences whose endpoints lie in the same partition block. -/
def internalEdges (X : FiniteMultiGraph) (P : BlockStructure X.vertex) :
    Finset X.edge :=
  Finset.univ.filter fun e ↦ P.block (X.first e) = P.block (X.second e)

/-- The spanning subgraph obtained by deleting all inter-block occurrences. -/
def graph (X : FiniteMultiGraph) (P : BlockStructure X.vertex) :
    FiniteMultiGraph where
  vertex := X.vertex
  edge :=
    { carrier := {e : X.edge // e ∈ internalEdges X P}
      fintype := inferInstance
      decidableEq := inferInstance }
  first e := X.first e.1
  second e := X.second e.1
  loopless e := X.loopless e.1

@[simp] theorem graph_first (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (e : (graph X P).edge) :
    (graph X P).first e = X.first e.1 := rfl

@[simp] theorem graph_second (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (e : (graph X P).edge) :
    (graph X P).second e = X.second e.1 := rfl

/-- Every retained edge lies inside one block. -/
theorem edge_inside (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (e : (graph X P).edge) :
    P.block ((graph X P).first e) = P.block ((graph X P).second e) := by
  exact (Finset.mem_filter.mp e.2).2

/-- Occurrence-level witness for deleting precisely the crossing edges. -/
noncomputable def editWitness (X : FiniteMultiGraph)
    (P : BlockStructure X.vertex) :
    EdgeEditWitness X (graph X P) (Equiv.refl X.vertex) where
  sourceKept := internalEdges X P
  targetKept := Finset.univ
  edgeEquiv :=
    { toFun := fun e ↦ ⟨⟨e.1, e.2⟩, Finset.mem_univ _⟩
      invFun := fun e ↦ ⟨e.1.1, e.1.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  preservesEndpoints _ := Or.inl ⟨rfl, rfl⟩

theorem sourceUnmatched_editWitness (X : FiniteMultiGraph)
    (P : BlockStructure X.vertex) :
    (editWitness X P).sourceUnmatched =
      X.crossingEdges P.block := by
  classical
  ext e
  simp [EdgeEditWitness.sourceUnmatched, editWitness, internalEdges,
    FiniteMultiGraph.crossingEdges]

@[simp] theorem targetUnmatched_editWitness (X : FiniteMultiGraph)
    (P : BlockStructure X.vertex) :
    (editWitness X P).targetUnmatched = ∅ := by
  classical
  simp [EdgeEditWitness.targetUnmatched, editWitness]

theorem unmatchedCount_editWitness (X : FiniteMultiGraph)
    (P : BlockStructure X.vertex) :
    (editWitness X P).unmatchedCount =
      (X.crossingEdges P.block).card := by
  rw [EdgeEditWitness.unmatchedCount, sourceUnmatched_editWitness,
    targetUnmatched_editWitness]
  simp

theorem editDistance_le_two_mul_crossing (X : FiniteMultiGraph)
    (P : BlockStructure X.vertex) :
    X.editDistance (graph X P) (Equiv.refl X.vertex) ≤
      2 * (X.crossingEdges P.block).card := by
  simpa [unmatchedCount_editWitness] using
    (editWitness X P).editDistance_le_two_mul_unmatchedCount

end KunBlockGraph
end NonsoficGroupsExist
