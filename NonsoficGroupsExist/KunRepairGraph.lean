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

/-- Repair stubs whose old endpoint and new marker lie on the same selected
side of a vertex cut.  These are precisely the redirected stubs that fail to
replace their old contribution to that cut. -/
def badStubs (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (marker : CrossingStub X P → X.vertex) (U : Finset X.vertex) :
    Finset (CrossingStub X P) :=
  Finset.univ.filter fun s ↦
    stubEndpoint X P s ∈ U ∧ marker s ∈ U

/-- If markers are distinct, at most `|U|` redirected stubs can fail on `U`.
The separated-marker argument will improve this crude estimate by charging
most such markers to repaired boundary edges. -/
theorem card_badStubs_le
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (marker : CrossingStub X P → X.vertex)
    (marker_injective : Function.Injective marker)
    (U : Finset X.vertex) :
    (badStubs X P marker U).card ≤ U.card := by
  classical
  let f : {s : CrossingStub X P // s ∈ badStubs X P marker U} →
      {y : X.vertex // y ∈ U} :=
    fun s ↦ ⟨marker s.1, (Finset.mem_filter.mp s.2).2.2⟩
  have hf : Function.Injective f := by
    intro s t hst
    apply Subtype.ext
    exact marker_injective (congrArg Subtype.val hst)
  simpa [Fintype.card_coe] using Fintype.card_le_of_injective f hf

/-- Forget whether an encoded original boundary occurrence was paid for by a
repaired boundary occurrence or by a bad stub. -/
def encodedOriginal
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (marker : CrossingStub X P → X.vertex)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint X P s)
    (U : Finset X.vertex) :
    Sum
      {e : (graph X P marker marker_ne).edge //
        e ∈ (graph X P marker marker_ne).boundary U}
      {s : CrossingStub X P // s ∈ badStubs X P marker U} → X.edge
  | Sum.inl e =>
      match e.1 with
      | Sum.inl a => a.1
      | Sum.inr s => s.1.1
  | Sum.inr s => s.1.1.1

/-- Every original boundary occurrence either survives as an internal repaired
boundary occurrence, is replaced by a repaired stub crossing the cut, or is
charged to a bad stub whose marker remains on the selected side. -/
noncomputable def boundaryEncoding
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (marker : CrossingStub X P → X.vertex)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint X P s)
    (U : Finset X.vertex) :
    {e : X.edge // e ∈ X.boundary U} →
      Sum
        {a : (graph X P marker marker_ne).edge //
          a ∈ (graph X P marker marker_ne).boundary U}
        {s : CrossingStub X P // s ∈ badStubs X P marker U} := by
  classical
  intro e
  have heBoundary := (Finset.mem_filter.mp e.2).2
  by_cases heInternal : e.1 ∈ internalEdges X P
  · exact Sum.inl ⟨Sum.inl ⟨e.1, heInternal⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, heBoundary⟩⟩
  · have heCrossing : e.1 ∈ X.crossingEdges P.block := by
      have hne : P.block (X.first e.1) ≠ P.block (X.second e.1) := by
        intro heq
        exact heInternal (Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
    by_cases hfirst : X.first e.1 ∈ U
    · let s : CrossingStub X P := (⟨e.1, heCrossing⟩, StubSide.first)
      by_cases hmarker : marker s ∈ U
      · exact Sum.inr ⟨s, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hfirst, hmarker⟩⟩
      · exact Sum.inl ⟨Sum.inr s, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, Or.inl ⟨hfirst, hmarker⟩⟩⟩
    · have hsecond : X.second e.1 ∈ U := by
        rcases heBoundary with h | h
        · exact False.elim (hfirst h.1)
        · exact h.1
      let s : CrossingStub X P := (⟨e.1, heCrossing⟩, StubSide.second)
      by_cases hmarker : marker s ∈ U
      · exact Sum.inr ⟨s, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hsecond, hmarker⟩⟩
      · exact Sum.inl ⟨Sum.inr s, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, Or.inl ⟨hsecond, hmarker⟩⟩⟩

@[simp] theorem encodedOriginal_boundaryEncoding
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (marker : CrossingStub X P → X.vertex)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint X P s)
    (U : Finset X.vertex) (e : {e : X.edge // e ∈ X.boundary U}) :
    encodedOriginal X P marker marker_ne U
        (boundaryEncoding X P marker marker_ne U e) = e.1 := by
  classical
  by_cases heInternal : e.1 ∈ internalEdges X P
  · simp [boundaryEncoding, heInternal, encodedOriginal]
  · have heCrossing : e.1 ∈ X.crossingEdges P.block := by
      have hne : P.block (X.first e.1) ≠ P.block (X.second e.1) := by
        intro heq
        exact heInternal (Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
    by_cases hfirst : X.first e.1 ∈ U
    · let s : CrossingStub X P := (⟨e.1, heCrossing⟩, StubSide.first)
      by_cases hmarker : marker s ∈ U <;>
        simp [boundaryEncoding, heInternal, hfirst, s, hmarker,
          encodedOriginal]
    · let s : CrossingStub X P := (⟨e.1, heCrossing⟩, StubSide.second)
      by_cases hmarker : marker s ∈ U <;>
        simp [boundaryEncoding, heInternal, hfirst, s, hmarker,
          encodedOriginal]

/-- Cardinal form of the boundary charging map. -/
theorem boundaryCard_le_repaired_add_badStubs
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (marker : CrossingStub X P → X.vertex)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint X P s)
    (U : Finset X.vertex) :
    X.boundaryCard U ≤
      (graph X P marker marker_ne).boundaryCard U +
        (badStubs X P marker U).card := by
  let f := boundaryEncoding X P marker marker_ne U
  have hf : Function.Injective f := by
    intro e e' he
    apply Subtype.ext
    have h := congrArg (encodedOriginal X P marker marker_ne U) he
    rw [encodedOriginal_boundaryEncoding, encodedOriginal_boundaryEncoding] at h
    exact h
  have hcard := Fintype.card_le_of_injective f hf
  simpa [FiniteMultiGraph.boundaryCard, Fintype.card_sum,
    Fintype.card_coe] using hcard

end KunRepairGraph
end NonsoficGroupsExist
