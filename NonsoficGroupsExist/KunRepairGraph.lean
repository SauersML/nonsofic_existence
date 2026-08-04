import NonsoficGroupsExist.KunBlockGraph

/-!
# Redirecting deleted partition-boundary occurrences

Deleting every crossing occurrence separates the partition blocks but can
remove too much of a small set's boundary.  This module defines the repair
graph used to restore those losses.  A crossing occurrence has one stub in
each adjacent block.  Each stub is redirected to a marker in the same block.

The marker hypotheses here are an intermediate finite combinatorial interface;
the expander construction must subsequently construct markers satisfying them.
-/

namespace NonsoficGroupsExist
namespace KunRepairGraph

open FiniteMultiGraph
open KunBlockGraph

/-- The two endpoints, regarded as the two stubs of a crossing occurrence. -/
inductive StubSide
  | first
  | second
  deriving DecidableEq, Fintype

/-- An occurrence crossing between two partition blocks. -/
abbrev CrossingOccurrence (X : FiniteMultiGraph)
    (P : BlockStructure X.vertex) :=
  {e : X.edge // e ∈ X.crossingEdges P.block}

/-- One of the two block-side stubs of a crossing occurrence. -/
abbrev CrossingStub (X : FiniteMultiGraph)
    (P : BlockStructure X.vertex) :=
  CrossingOccurrence X P × StubSide

/-- The endpoint of a crossing stub in its original block. -/
def stubEndpoint (X : FiniteMultiGraph) (P : BlockStructure X.vertex) :
    CrossingStub X P → X.vertex
  | ⟨e, StubSide.first⟩ => X.first e.1
  | ⟨e, StubSide.second⟩ => X.second e.1

/-- The original internal occurrences together with one new occurrence for
each crossing stub. -/
abbrev RepairedEdge (X : FiniteMultiGraph) (P : BlockStructure X.vertex) :=
  Sum {e : X.edge // e ∈ internalEdges X P} (CrossingStub X P)

instance repairedEdgeFintype (X : FiniteMultiGraph)
    (P : BlockStructure X.vertex) : Fintype (RepairedEdge X P) :=
  inferInstance

instance repairedEdgeDecidableEq (X : FiniteMultiGraph)
    (P : BlockStructure X.vertex) : DecidableEq (RepairedEdge X P) :=
  inferInstance

/-- Replace every deleted crossing stub by an edge from its old endpoint to a
chosen marker in the same block. -/
def graph (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (marker : CrossingStub X P → X.vertex)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint X P s) : FiniteMultiGraph where
  vertex := X.vertex
  edge :=
    { carrier := RepairedEdge X P
      fintype := repairedEdgeFintype X P
      decidableEq := repairedEdgeDecidableEq X P }
  first
    | Sum.inl e => X.first e.1
    | Sum.inr s => stubEndpoint X P s
  second
    | Sum.inl e => X.second e.1
    | Sum.inr s => marker s
  loopless
    | Sum.inl e => X.loopless e.1
    | Sum.inr s => marker_ne s |>.symm

@[simp] theorem graph_first_internal
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (marker : CrossingStub X P → X.vertex)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint X P s)
    (e : {e : X.edge // e ∈ internalEdges X P}) :
    (graph X P marker marker_ne).first (Sum.inl e) = X.first e.1 := rfl

@[simp] theorem graph_second_internal
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (marker : CrossingStub X P → X.vertex)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint X P s)
    (e : {e : X.edge // e ∈ internalEdges X P}) :
    (graph X P marker marker_ne).second (Sum.inl e) = X.second e.1 := rfl

@[simp] theorem graph_first_stub
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (marker : CrossingStub X P → X.vertex)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint X P s)
    (s : CrossingStub X P) :
    (graph X P marker marker_ne).first (Sum.inr s) =
      stubEndpoint X P s := rfl

@[simp] theorem graph_second_stub
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (marker : CrossingStub X P → X.vertex)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint X P s)
    (s : CrossingStub X P) :
    (graph X P marker marker_ne).second (Sum.inr s) = marker s := rfl

/-- Internal retained occurrences stay inside a block. -/
theorem internal_edge_inside
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (marker : CrossingStub X P → X.vertex)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint X P s)
    (e : {e : X.edge // e ∈ internalEdges X P}) :
    P.block ((graph X P marker marker_ne).first (Sum.inl e)) =
      P.block ((graph X P marker marker_ne).second (Sum.inl e)) := by
  exact (Finset.mem_filter.mp e.2).2

/-- Repaired stub occurrences stay inside a block when their marker does. -/
theorem stub_edge_inside
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (marker : CrossingStub X P → X.vertex)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint X P s)
    (marker_inside : ∀ s, marker s ∈ P.block (stubEndpoint X P s))
    (s : CrossingStub X P) :
    P.block ((graph X P marker marker_ne).first (Sum.inr s)) =
      P.block ((graph X P marker marker_ne).second (Sum.inr s)) := by
  exact (P.eq_of_mem _ _ (marker_inside s)).symm

/-- Every occurrence of the repaired graph lies within one partition block. -/
theorem edge_inside
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (marker : CrossingStub X P → X.vertex)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint X P s)
    (marker_inside : ∀ s, marker s ∈ P.block (stubEndpoint X P s))
    (e : (graph X P marker marker_ne).edge) :
    P.block ((graph X P marker marker_ne).first e) =
      P.block ((graph X P marker marker_ne).second e) := by
  rcases e with e | s
  · exact internal_edge_inside X P marker marker_ne e
  · exact stub_edge_inside X P marker marker_ne marker_inside s

/-- There are exactly two repair stubs for each crossing occurrence. -/
theorem card_crossingStub (X : FiniteMultiGraph)
    (P : BlockStructure X.vertex) :
    Fintype.card (CrossingStub X P) = 2 * (X.crossingEdges P.block).card := by
  have hside : Fintype.card StubSide = 2 := rfl
  rw [Fintype.card_prod, Fintype.card_coe, hside]
  omega

/-- The repaired graph retains every internal occurrence and adds precisely
two occurrences per deleted crossing occurrence. -/
theorem card_repairedEdge (X : FiniteMultiGraph)
    (P : BlockStructure X.vertex) :
    Fintype.card (RepairedEdge X P) =
      (internalEdges X P).card + 2 * (X.crossingEdges P.block).card := by
  rw [Fintype.card_sum, Fintype.card_coe, card_crossingStub]

/-- The retained target occurrences are exactly the left (original internal)
summand. -/
noncomputable def targetInternalEdges
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (marker : CrossingStub X P → X.vertex)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint X P s) :
    Finset (graph X P marker marker_ne).edge := by
  classical
  exact Finset.univ.filter fun e ↦
    match e with
    | Sum.inl _ => True
    | Sum.inr _ => False

/-- The newly inserted right-summand occurrences. -/
noncomputable def targetStubEdges
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (marker : CrossingStub X P → X.vertex)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint X P s) :
    Finset (graph X P marker marker_ne).edge := by
  classical
  exact Finset.univ.filter fun e ↦
    match e with
    | Sum.inl _ => False
    | Sum.inr _ => True

/-- Newly inserted target occurrences are canonically the crossing stubs. -/
noncomputable def stubEdgeEquiv
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (marker : CrossingStub X P → X.vertex)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint X P s) :
    {e : (graph X P marker marker_ne).edge //
      e ∈ targetStubEdges X P marker marker_ne} ≃ CrossingStub X P where
  toFun e := by
    rcases e with ⟨e, he⟩
    rcases e with a | s
    · simp [targetStubEdges] at he
    · exact s
  invFun s := ⟨Sum.inr s, by simp [targetStubEdges]⟩
  left_inv e := by
    rcases e with ⟨e, he⟩
    rcases e with a | s
    · simp [targetStubEdges] at he
    · rfl
  right_inv _ := rfl

/-- The occurrence bijection between retained source and target edges. -/
noncomputable def internalEdgeEquiv
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (marker : CrossingStub X P → X.vertex)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint X P s) :
    {e : X.edge // e ∈ internalEdges X P} ≃
      {e : (graph X P marker marker_ne).edge //
        e ∈ targetInternalEdges X P marker marker_ne} where
  toFun e := ⟨Sum.inl ⟨e.1, e.2⟩, by
    simp [targetInternalEdges]⟩
  invFun b := by
    rcases b with ⟨e, he⟩
    rcases e with e | s
    · exact ⟨e.1, e.2⟩
    · simp [targetInternalEdges] at he
  left_inv _ := rfl
  right_inv b := by
    rcases b with ⟨e, he⟩
    rcases e with e | s
    · rfl
    · simp [targetInternalEdges] at he

/-- Occurrence-level witness: delete each crossing occurrence and insert its
two repaired stubs, retaining every internal occurrence verbatim. -/
noncomputable def editWitness
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (marker : CrossingStub X P → X.vertex)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint X P s) :
    EdgeEditWitness X (graph X P marker marker_ne) (Equiv.refl X.vertex) where
  sourceKept := internalEdges X P
  targetKept := targetInternalEdges X P marker marker_ne
  edgeEquiv := internalEdgeEquiv X P marker marker_ne
  preservesEndpoints _ := Or.inl ⟨rfl, rfl⟩

theorem sourceUnmatched_editWitness
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (marker : CrossingStub X P → X.vertex)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint X P s) :
    (editWitness X P marker marker_ne).sourceUnmatched =
      X.crossingEdges P.block := by
  classical
  ext e
  simp [EdgeEditWitness.sourceUnmatched, editWitness, internalEdges,
    FiniteMultiGraph.crossingEdges]

theorem targetUnmatched_editWitness
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (marker : CrossingStub X P → X.vertex)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint X P s) :
    (editWitness X P marker marker_ne).targetUnmatched =
      targetStubEdges X P marker marker_ne := by
  classical
  ext e
  rcases e with e | s <;>
    simp [EdgeEditWitness.targetUnmatched, editWitness, targetInternalEdges,
      targetStubEdges]

theorem card_targetUnmatched_editWitness
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (marker : CrossingStub X P → X.vertex)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint X P s) :
    ((editWitness X P marker marker_ne).targetUnmatched).card =
      2 * (X.crossingEdges P.block).card := by
  rw [targetUnmatched_editWitness]
  have hfilter :
      (targetStubEdges X P marker marker_ne).card =
        Fintype.card (CrossingStub X P) := by
    rw [← Fintype.card_coe]
    exact Fintype.card_congr (stubEdgeEquiv X P marker marker_ne)
  rw [hfilter, card_crossingStub]

theorem unmatchedCount_editWitness
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (marker : CrossingStub X P → X.vertex)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint X P s) :
    (editWitness X P marker marker_ne).unmatchedCount =
      3 * (X.crossingEdges P.block).card := by
  rw [EdgeEditWitness.unmatchedCount, sourceUnmatched_editWitness,
    card_targetUnmatched_editWitness]
  omega

/-- The repaired graph costs at most six ordered-pair edits per original
crossing occurrence. -/
theorem editDistance_le_six_mul_crossing
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (marker : CrossingStub X P → X.vertex)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint X P s) :
    X.editDistance (graph X P marker marker_ne) (Equiv.refl X.vertex) ≤
      6 * (X.crossingEdges P.block).card := by
  have h := (editWitness X P marker marker_ne).editDistance_le_two_mul_unmatchedCount
  rw [unmatchedCount_editWitness] at h
  omega

end KunRepairGraph
end NonsoficGroupsExist
