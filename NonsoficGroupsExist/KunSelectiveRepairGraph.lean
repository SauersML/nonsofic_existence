import NonsoficGroupsExist.KunBadBlocks
import NonsoficGroupsExist.EdgeWitnessDistance

/-!
# Repairing good Kun blocks and isolating bad blocks

The full repair graph cannot attach a nonloop edge inside a singleton bad
block.  This graph therefore retains internal occurrences only in good
original blocks and inserts repair edges only for good crossing stubs.  Bad
vertices are isolated by the refined singleton partition.
-/

namespace NonsoficGroupsExist
namespace KunSelectiveRepairGraph

open FiniteMultiGraph
open KunBlockGraph
open KunRepairGraph
open KunMarkerSelection
open KunBadBlocks

/-- Original internal occurrences whose source block is good. -/
def goodInternalEdges (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (B : Finset X.vertex) : Finset X.edge :=
  (internalEdges X P).filter fun e ↦ X.first e ∉ B

/-- Original occurrences charged to a bad source vertex. -/
def badSourceEdges (X : FiniteMultiGraph) (B : Finset X.vertex) :
    Finset X.edge :=
  Finset.univ.filter fun e ↦ X.first e ∈ B

/-- A generator graph has at most one source occurrence per generator and
vertex, so bad-source occurrences are bounded by `|S| |B|`. -/
theorem card_badSourceEdges_generatorGraph_le
    {G : Type} [Group G] (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (B : Finset M) :
    (badSourceEdges (generatorGraph M S τ) B).card ≤ S.card * B.card := by
  classical
  let f : {e : (generatorGraph M S τ).edge //
      e ∈ badSourceEdges (generatorGraph M S τ) B} →
      S × {x : M // x ∈ B} := fun e ↦
    ⟨e.1.1.1, ⟨e.1.1.2, (Finset.mem_filter.mp e.2).2⟩⟩
  have hf : Function.Injective f := by
    intro e e' heq
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (congrArg (fun z ↦ z.1) heq)
      (congrArg (fun z ↦ z.2.1) heq)
  have hcard := Fintype.card_le_of_injective f hf
  simpa [Fintype.card_coe, Fintype.card_prod] using hcard

/-- Retained good internal occurrences together with good-side repair stubs. -/
abbrev SelectiveEdge (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (B : Finset X.vertex) :=
  Sum {e : X.edge // e ∈ goodInternalEdges X P B}
    (GoodCrossingStub X P B)

instance selectiveEdgeFintype (X : FiniteMultiGraph)
    (P : BlockStructure X.vertex) (B : Finset X.vertex) :
    Fintype (SelectiveEdge X P B) := inferInstance

instance selectiveEdgeDecidableEq (X : FiniteMultiGraph)
    (P : BlockStructure X.vertex) (B : Finset X.vertex) :
    DecidableEq (SelectiveEdge X P B) := inferInstance

/-- The selective repaired graph. -/
def graph (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (B : Finset X.vertex) (marker : GoodCrossingStub X P B → X.vertex)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint X P s.1) :
    FiniteMultiGraph where
  vertex := X.vertex
  edge :=
    { carrier := SelectiveEdge X P B
      fintype := selectiveEdgeFintype X P B
      decidableEq := selectiveEdgeDecidableEq X P B }
  first
    | Sum.inl e => X.first e.1
    | Sum.inr s => stubEndpoint X P s.1
  second
    | Sum.inl e => X.second e.1
    | Sum.inr s => marker s
  loopless
    | Sum.inl e => X.loopless e.1
    | Sum.inr s => (marker_ne s).symm

@[simp] theorem graph_first_internal
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (B : Finset X.vertex) (marker : GoodCrossingStub X P B → X.vertex)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint X P s.1)
    (e : {e : X.edge // e ∈ goodInternalEdges X P B}) :
    (graph X P B marker marker_ne).first (Sum.inl e) = X.first e.1 := rfl

@[simp] theorem graph_second_internal
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (B : Finset X.vertex) (marker : GoodCrossingStub X P B → X.vertex)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint X P s.1)
    (e : {e : X.edge // e ∈ goodInternalEdges X P B}) :
    (graph X P B marker marker_ne).second (Sum.inl e) = X.second e.1 := rfl

@[simp] theorem graph_first_stub
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (B : Finset X.vertex) (marker : GoodCrossingStub X P B → X.vertex)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint X P s.1)
    (s : GoodCrossingStub X P B) :
    (graph X P B marker marker_ne).first (Sum.inr s) =
      stubEndpoint X P s.1 := rfl

@[simp] theorem graph_second_stub
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (B : Finset X.vertex) (marker : GoodCrossingStub X P B → X.vertex)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint X P s.1)
    (s : GoodCrossingStub X P B) :
    (graph X P B marker marker_ne).second (Sum.inr s) = marker s := rfl

/-- Selective repair preserves a uniform degree bound.  Internal occurrences
and repaired old endpoints are each charged to an original incident
occurrence; injectivity of the marker assignment permits at most one extra
marker incidence at a vertex. -/
theorem graph_degree_le
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (B : Finset X.vertex) (marker : GoodCrossingStub X P B → X.vertex)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint X P s.1)
    (marker_injective : Function.Injective marker) (x : X.vertex) :
    (graph X P B marker marker_ne).degree x ≤ 2 * X.degree x + 1 := by
  classical
  have stubEndpoint_mem_incident (s : GoodCrossingStub X P B) :
      s.1.1.1 ∈ X.incidentEdges (stubEndpoint X P s.1) := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases s.1 with ⟨e, side⟩
    rcases side <;> simp [stubEndpoint]
  have stub_eq_of_occurrence_eq_of_endpoint_eq
      (s t : CrossingStub X P) (hocc : s.1 = t.1)
      (hend : stubEndpoint X P s = stubEndpoint X P t) : s = t := by
    rcases s with ⟨e, side⟩
    rcases t with ⟨e', side'⟩
    dsimp only at hocc
    subst e'
    have hside : side = side' := by
      rcases side <;> rcases side' <;> simp [stubEndpoint] at hend ⊢
      · exact (X.loopless e.1 hend).elim
      · exact (X.loopless e.1 hend.symm).elim
    exact congrArg (fun z ↦ (e, z)) hside
  let f : {e : (graph X P B marker marker_ne).edge //
      e ∈ (graph X P B marker marker_ne).incidentEdges x} →
      ({e : X.edge // e ∈ X.incidentEdges x} × Bool) ⊕ Unit :=
    fun ⟨e, he⟩ ↦ match e with
    | Sum.inl a => Sum.inl (⟨a.1, by
        have hi := (Finset.mem_filter.mp he).2
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        exact hi⟩,
          false)
    | Sum.inr s =>
        if hs : stubEndpoint X P s.1 = x then
          Sum.inl (⟨s.1.1.1, by simpa [hs] using
            stubEndpoint_mem_incident s⟩, true)
        else Sum.inr Unit.unit
  have hf : Function.Injective f := by
    rintro ⟨e, he⟩ ⟨e', he'⟩ heq
    rcases e with a | s
    · rcases e' with a' | t
      · have hp := Sum.inl.inj heq
        have haa : a.1 = a'.1 := congrArg (fun z ↦ z.1.1) hp
        apply Subtype.ext
        exact congrArg Sum.inl (Subtype.ext haa)
      · by_cases ht : stubEndpoint X P t.1 = x <;>
          simp [f, ht] at heq
    · rcases e' with a' | t
      · by_cases hs : stubEndpoint X P s.1 = x <;>
          simp [f, hs] at heq
      · by_cases hs : stubEndpoint X P s.1 = x
        · by_cases ht : stubEndpoint X P t.1 = x
          · simp [f, hs, ht] at heq
            have hocc : s.1.1 = t.1.1 := heq
            apply Subtype.ext
            apply congrArg Sum.inr
            apply Subtype.ext
            exact stub_eq_of_occurrence_eq_of_endpoint_eq s.1 t.1 hocc
              (hs.trans ht.symm)
          · simp [f, hs, ht] at heq
        · by_cases ht : stubEndpoint X P t.1 = x
          · simp [f, hs, ht] at heq
          · apply Subtype.ext
            apply congrArg Sum.inr
            apply marker_injective
            have hmarker : marker s = x := by
              have hi := (Finset.mem_filter.mp he).2
              exact hi.resolve_left hs
            have hmarker' : marker t = x := by
              have hi := (Finset.mem_filter.mp he').2
              exact hi.resolve_left ht
            exact hmarker.trans hmarker'.symm
  have hcard := Fintype.card_le_of_injective f hf
  simpa [FiniteMultiGraph.degree, Fintype.card_coe, Fintype.card_sum,
    Fintype.card_prod, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    using hcard

theorem graph_hasDegreeBound
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (B : Finset X.vertex) (marker : GoodCrossingStub X P B → X.vertex)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint X P s.1)
    (marker_injective : Function.Injective marker) {d : ℕ}
    (hX : X.HasDegreeBound d) :
    (graph X P B marker marker_ne).HasDegreeBound (2 * d + 1) := by
  intro x
  exact (graph_degree_le X P B marker marker_ne marker_injective x).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (hX x)) 1)

/-- Every selective edge stays in a block of the singleton-refined
partition. -/
theorem edge_inside_refined
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (E : Finset X.vertex) (K : ℕ)
    (marker : GoodCrossingStub X P (badVertices X P E K) → X.vertex)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint X P s.1)
    (marker_inside : ∀ s, marker s ∈ P.block (stubEndpoint X P s.1))
    (e : (graph X P (badVertices X P E K) marker marker_ne).edge) :
    (singletonizeBadBlocks X P E K).block
        ((graph X P (badVertices X P E K) marker marker_ne).first e) =
      (singletonizeBadBlocks X P E K).block
        ((graph X P (badVertices X P E K) marker marker_ne).second e) := by
  rcases e with e | s
  · have hedata := Finset.mem_filter.mp e.2
    have hinternal := (Finset.mem_filter.mp hedata.1).2
    have hfirstGood := hedata.2
    have hsecondMem : X.second e.1 ∈ P.block (X.first e.1) := by
      rw [hinternal]
      exact P.self_mem _
    have hsecondGood : X.second e.1 ∉ badVertices X P E K := by
      intro hbad
      exact hfirstGood
        ((mem_badVertices_iff_of_mem_block X P E K hsecondMem).mpr hbad)
    change (singletonizeBadBlocks X P E K).block (X.first e.1) =
      (singletonizeBadBlocks X P E K).block (X.second e.1)
    rw [singletonizeBadBlocks_block_of_good X P E K hfirstGood,
      singletonizeBadBlocks_block_of_good X P E K hsecondGood]
    exact hinternal
  · have hendpointGood : stubEndpoint X P s.1 ∉ badVertices X P E K :=
      s.2
    have hmarkerGood : marker s ∉ badVertices X P E K := by
      intro hbad
      exact hendpointGood
        ((mem_badVertices_iff_of_mem_block X P E K (marker_inside s)).mpr hbad)
    change (singletonizeBadBlocks X P E K).block (stubEndpoint X P s.1) =
      (singletonizeBadBlocks X P E K).block (marker s)
    rw [singletonizeBadBlocks_block_of_good X P E K hendpointGood,
      singletonizeBadBlocks_block_of_good X P E K hmarkerGood]
    exact (P.eq_of_mem _ _ (marker_inside s)).symm

/-- Target occurrences retained by the edit witness are the internal left
summand. -/
noncomputable def targetInternalEdges
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (B : Finset X.vertex) (marker : GoodCrossingStub X P B → X.vertex)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint X P s.1) :
    Finset (graph X P B marker marker_ne).edge := by
  classical
  exact Finset.univ.filter fun e ↦
    match e with
    | Sum.inl _ => True
    | Sum.inr _ => False

/-- The occurrence-level edit witness retains every good internal edge
verbatim. -/
noncomputable def editWitness
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (B : Finset X.vertex) (marker : GoodCrossingStub X P B → X.vertex)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint X P s.1) :
    EdgeEditWitness X (graph X P B marker marker_ne) (Equiv.refl X.vertex) where
  sourceKept := goodInternalEdges X P B
  targetKept := targetInternalEdges X P B marker marker_ne
  edgeEquiv :=
    { toFun := fun e ↦ ⟨Sum.inl ⟨e.1, e.2⟩, by
        simp [targetInternalEdges]⟩
      invFun := fun e ↦ by
        rcases e with ⟨e, he⟩
        rcases e with e | s
        · exact ⟨e.1, e.2⟩
        · simp [targetInternalEdges] at he
      left_inv := fun _ ↦ rfl
      right_inv := fun e ↦ by
        rcases e with ⟨e, he⟩
        rcases e with e | s
        · rfl
        · simp [targetInternalEdges] at he }
  preservesEndpoints _ := Or.inl ⟨rfl, rfl⟩

theorem sourceUnmatched_subset
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (B : Finset X.vertex) (marker : GoodCrossingStub X P B → X.vertex)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint X P s.1) :
    (editWitness X P B marker marker_ne).sourceUnmatched ⊆
      X.crossingEdges P.block ∪ badSourceEdges X B := by
  classical
  intro e he
  have hnotGood : e ∉ goodInternalEdges X P B := by
    simpa [EdgeEditWitness.sourceUnmatched, editWitness] using he
  by_cases hinternal : e ∈ internalEdges X P
  · apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    by_contra hfirst
    exact hnotGood (Finset.mem_filter.mpr ⟨hinternal, hfirst⟩)
  · apply Finset.mem_union_left
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro heq
    exact hinternal (Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩)

theorem card_sourceUnmatched_le
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (B : Finset X.vertex) (marker : GoodCrossingStub X P B → X.vertex)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint X P s.1) :
    (editWitness X P B marker marker_ne).sourceUnmatched.card ≤
      (X.crossingEdges P.block).card + (badSourceEdges X B).card := by
  exact (Finset.card_le_card
    (sourceUnmatched_subset X P B marker marker_ne)).trans
      (Finset.card_union_le _ _)

theorem card_targetUnmatched_le
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (B : Finset X.vertex) (marker : GoodCrossingStub X P B → X.vertex)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint X P s.1) :
    (editWitness X P B marker marker_ne).targetUnmatched.card ≤
      2 * (X.crossingEdges P.block).card := by
  classical
  have htarget : (editWitness X P B marker marker_ne).targetUnmatched.card =
      Fintype.card (GoodCrossingStub X P B) := by
    rw [← Fintype.card_coe]
    apply Fintype.card_congr
    let T := {e : (graph X P B marker marker_ne).edge //
      e ∈ (editWitness X P B marker marker_ne).targetUnmatched}
    exact
      { toFun := fun e ↦ by
          rcases e with ⟨e, he⟩
          rcases e with a | s
          · simp [EdgeEditWitness.targetUnmatched, editWitness,
              targetInternalEdges] at he
          · exact s
        invFun := fun s ↦ ⟨Sum.inr s, by
          simp [EdgeEditWitness.targetUnmatched, editWitness,
            targetInternalEdges]⟩
        left_inv := fun e ↦ by
          rcases e with ⟨e, he⟩
          rcases e with a | s
          · simp [EdgeEditWitness.targetUnmatched, editWitness,
              targetInternalEdges] at he
          · rfl
        right_inv := fun _ ↦ rfl }
  rw [htarget, ← card_crossingStub X P]
  exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective

/-- Explicit edit-count bound for selective repair. -/
theorem unmatchedCount_le
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (B : Finset X.vertex) (marker : GoodCrossingStub X P B → X.vertex)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint X P s.1) :
    (editWitness X P B marker marker_ne).unmatchedCount ≤
      3 * (X.crossingEdges P.block).card + (badSourceEdges X B).card := by
  rw [EdgeEditWitness.unmatchedCount]
  have hs := card_sourceUnmatched_le X P B marker marker_ne
  have ht := card_targetUnmatched_le X P B marker marker_ne
  omega

theorem editDistance_le
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (B : Finset X.vertex) (marker : GoodCrossingStub X P B → X.vertex)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint X P s.1) :
    X.editDistance (graph X P B marker marker_ne) (Equiv.refl X.vertex) ≤
      2 * (3 * (X.crossingEdges P.block).card +
        (badSourceEdges X B).card) := by
  exact (editWitness X P B marker marker_ne).editDistance_le_two_mul_unmatchedCount.trans
    (Nat.mul_le_mul_left 2 (unmatchedCount_le X P B marker marker_ne))

end KunSelectiveRepairGraph
end NonsoficGroupsExist
