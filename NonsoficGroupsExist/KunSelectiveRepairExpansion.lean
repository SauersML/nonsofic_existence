import NonsoficGroupsExist.KunSelectiveRepairGraph
import NonsoficGroupsExist.KunRepairExpansion

/-!
# Expansion of selectively repaired Kun blocks

This is the boundary-charging argument for `KunSelectiveRepairGraph`.  All
statements concern a subset of a good original block; bad original blocks are
handled separately as singleton components.
-/

namespace NonsoficGroupsExist
namespace KunSelectiveRepairExpansion

open FiniteMultiGraph
open KunSupport
open KunBlockGraph
open KunRepairGraph
open KunMarkerSelection
open KunBadBlocks
open KunSelectiveRepairGraph

/-- Good repair stubs whose old endpoint and marker both lie in `U`. -/
def badStubs (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (B : Finset X.vertex) (marker : GoodCrossingStub X P B → X.vertex)
    (U : Finset X.vertex) : Finset (GoodCrossingStub X P B) :=
  Finset.univ.filter fun s ↦
    stubEndpoint X P s.1 ∈ U ∧ marker s ∈ U

/-- Recover the original occurrence represented by a selective repaired
boundary edge or a bad good-stub. -/
def encodedOriginal
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (B : Finset X.vertex) (marker : GoodCrossingStub X P B → X.vertex)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint X P s.1)
    (U : Finset X.vertex) :
    Sum
      {e : (KunSelectiveRepairGraph.graph X P B marker marker_ne).edge //
        e ∈ (KunSelectiveRepairGraph.graph X P B marker marker_ne).boundary U}
      {s : GoodCrossingStub X P B // s ∈ badStubs X P B marker U} →
        X.edge
  | Sum.inl e =>
      match e.1 with
      | Sum.inl a => a.1
      | Sum.inr s => s.1.1.1
  | Sum.inr s => s.1.1.1.1

/-- Every original boundary occurrence of a good test set is retained,
replaced by its good-side stub, or charged to a bad good-stub. -/
noncomputable def boundaryEncoding
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (E : Finset X.vertex) (K : ℕ)
    (marker : GoodCrossingStub X P (badVertices X P E K) → X.vertex)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint X P s.1)
    (U : Finset X.vertex)
    (hUgood : ∀ x ∈ U, x ∉ badVertices X P E K) :
    {e : X.edge // e ∈ X.boundary U} →
      Sum
        {a : (KunSelectiveRepairGraph.graph X P (badVertices X P E K)
            marker marker_ne).edge //
          a ∈ (KunSelectiveRepairGraph.graph X P (badVertices X P E K)
            marker marker_ne).boundary U}
        {s : GoodCrossingStub X P (badVertices X P E K) //
          s ∈ badStubs X P (badVertices X P E K) marker U} := by
  classical
  intro e
  have heBoundary := (Finset.mem_filter.mp e.2).2
  by_cases heInternal : e.1 ∈ internalEdges X P
  · have hfirstGood : X.first e.1 ∉ badVertices X P E K := by
      rcases heBoundary with h | h
      · exact hUgood _ h.1
      · have hsecondGood := hUgood _ h.1
        have hfirstMem : X.first e.1 ∈ P.block (X.second e.1) := by
          rw [← (Finset.mem_filter.mp heInternal).2]
          exact P.self_mem _
        intro hfirstBad
        exact hsecondGood
          ((mem_badVertices_iff_of_mem_block X P E K hfirstMem).mpr hfirstBad)
    have heGood : e.1 ∈ goodInternalEdges X P (badVertices X P E K) :=
      Finset.mem_filter.mpr ⟨heInternal, hfirstGood⟩
    exact Sum.inl ⟨Sum.inl ⟨e.1, heGood⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, heBoundary⟩⟩
  · have heCrossing : e.1 ∈ X.crossingEdges P.block := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro heq
      exact heInternal (Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩)
    by_cases hfirst : X.first e.1 ∈ U
    · let raw : CrossingStub X P := (⟨e.1, heCrossing⟩, StubSide.first)
      let s : GoodCrossingStub X P (badVertices X P E K) :=
        ⟨raw, by simpa [raw, stubEndpoint] using hUgood _ hfirst⟩
      by_cases hmarker : marker s ∈ U
      · exact Sum.inr ⟨s, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, by simpa [s, raw, stubEndpoint] using hfirst,
            hmarker⟩⟩
      · apply Sum.inl
        refine ⟨Sum.inr s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
        change (stubEndpoint X P s.1 ∈ U ∧ marker s ∉ U) ∨
          (marker s ∈ U ∧ stubEndpoint X P s.1 ∉ U)
        exact Or.inl ⟨by simpa [s, raw, stubEndpoint] using hfirst, hmarker⟩
    · have hsecond : X.second e.1 ∈ U := by
        rcases heBoundary with h | h
        · exact False.elim (hfirst h.1)
        · exact h.1
      let raw : CrossingStub X P := (⟨e.1, heCrossing⟩, StubSide.second)
      let s : GoodCrossingStub X P (badVertices X P E K) :=
        ⟨raw, by simpa [raw, stubEndpoint] using hUgood _ hsecond⟩
      by_cases hmarker : marker s ∈ U
      · exact Sum.inr ⟨s, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, by simpa [s, raw, stubEndpoint] using hsecond,
            hmarker⟩⟩
      · apply Sum.inl
        refine ⟨Sum.inr s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
        change (stubEndpoint X P s.1 ∈ U ∧ marker s ∉ U) ∨
          (marker s ∈ U ∧ stubEndpoint X P s.1 ∉ U)
        exact Or.inl ⟨by simpa [s, raw, stubEndpoint] using hsecond, hmarker⟩

@[simp] theorem encodedOriginal_boundaryEncoding
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (E : Finset X.vertex) (K : ℕ)
    (marker : GoodCrossingStub X P (badVertices X P E K) → X.vertex)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint X P s.1)
    (U : Finset X.vertex)
    (hUgood : ∀ x ∈ U, x ∉ badVertices X P E K)
    (e : {e : X.edge // e ∈ X.boundary U}) :
    encodedOriginal X P (badVertices X P E K) marker marker_ne U
      (boundaryEncoding X P E K marker marker_ne U hUgood e) = e.1 := by
  classical
  by_cases heInternal : e.1 ∈ internalEdges X P
  · simp [boundaryEncoding, heInternal, encodedOriginal]
  · have heCrossing : e.1 ∈ X.crossingEdges P.block := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro heq
      exact heInternal (Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩)
    by_cases hfirst : X.first e.1 ∈ U
    · let raw : CrossingStub X P := (⟨e.1, heCrossing⟩, StubSide.first)
      let s : GoodCrossingStub X P (badVertices X P E K) :=
        ⟨raw, by simpa [raw, stubEndpoint] using hUgood _ hfirst⟩
      by_cases hmarker : marker s ∈ U <;>
        simp [boundaryEncoding, heInternal, hfirst, raw, s, hmarker,
          encodedOriginal]
    · let raw : CrossingStub X P := (⟨e.1, heCrossing⟩, StubSide.second)
      have hsecond : X.second e.1 ∈ U := by
        have heBoundary := (Finset.mem_filter.mp e.2).2
        rcases heBoundary with h | h
        · exact False.elim (hfirst h.1)
        · exact h.1
      let s : GoodCrossingStub X P (badVertices X P E K) :=
        ⟨raw, by simpa [raw, stubEndpoint] using hUgood _ hsecond⟩
      by_cases hmarker : marker s ∈ U <;>
        simp [boundaryEncoding, heInternal, hfirst, raw, s, hmarker,
          encodedOriginal]

/-- Cardinal boundary charging for the selective graph. -/
theorem boundaryCard_le_repaired_add_badStubs
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (E : Finset X.vertex) (K : ℕ)
    (marker : GoodCrossingStub X P (badVertices X P E K) → X.vertex)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint X P s.1)
    (U : Finset X.vertex)
    (hUgood : ∀ x ∈ U, x ∉ badVertices X P E K) :
    X.boundaryCard U ≤
      (KunSelectiveRepairGraph.graph X P (badVertices X P E K)
        marker marker_ne).boundaryCard U +
      (badStubs X P (badVertices X P E K) marker U).card := by
  let f := boundaryEncoding X P E K marker marker_ne U hUgood
  have hf : Function.Injective f := by
    intro e e' he
    apply Subtype.ext
    have h := congrArg
      (encodedOriginal X P (badVertices X P E K) marker marker_ne U) he
    rw [encodedOriginal_boundaryEncoding, encodedOriginal_boundaryEncoding] at h
    exact h
  have hcard := Fintype.card_le_of_injective f hf
  simpa [FiniteMultiGraph.boundaryCard, Fintype.card_sum,
    Fintype.card_coe] using hcard

/-- A marker-neighborhood escape inside a good block gives a retained good
internal occurrence crossing the tested set. -/
theorem exists_goodInternalBoundary_of_marker_escape
    {G : Type} [Group G] (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (P : BlockStructure M) (E : Finset M) (K : ℕ)
    (marker : GoodCrossingStub (generatorGraph M S τ) P
      (badVertices (generatorGraph M S τ) P E K) → M)
    (y : M) (U : Finset M)
    (s : GoodCrossingStub (generatorGraph M S τ) P
      (badVertices (generatorGraph M S τ) P E K))
    (hmarkerU : marker s ∈ U) (r : ℕ) {z : M}
    (hz : z ∈ forwardNeighborhood M τ S r {marker s}) (hzout : z ∉ U)
    (hneighborhood : forwardNeighborhood M τ S r {marker s} ⊆ P.block y)
    (hyGood : y ∉ badVertices (generatorGraph M S τ) P E K) :
    ∃ e : (generatorGraph M S τ).edge,
      e ∈ (generatorGraph M S τ).boundary U ∧
      e ∈ goodInternalEdges (generatorGraph M S τ) P
        (badVertices (generatorGraph M S τ) P E K) ∧
      (generatorGraph M S τ).first e ∈
        forwardNeighborhood M τ S r {marker s} := by
  obtain ⟨e, heBoundary, heFirst, heSecond⟩ :=
    KunRepairExpansion.exists_generatorBoundary_of_mem_forwardNeighborhood_not_mem
      M τ S (marker s) hmarkerU r hz hzout
  have hfirstBlock : (generatorGraph M S τ).first e ∈ P.block y :=
    hneighborhood heFirst
  have hsecondBlock : (generatorGraph M S τ).second e ∈ P.block y :=
    hneighborhood heSecond
  have hblocks : P.block ((generatorGraph M S τ).first e) =
      P.block ((generatorGraph M S τ).second e) :=
    (P.eq_of_mem y _ hfirstBlock).trans (P.eq_of_mem y _ hsecondBlock).symm
  have hfirstGood : (generatorGraph M S τ).first e ∉
      badVertices (generatorGraph M S τ) P E K := by
    intro hbad
    exact hyGood
      ((mem_badVertices_iff_of_mem_block (generatorGraph M S τ) P E K
        hfirstBlock).mpr hbad)
  exact ⟨e, heBoundary, Finset.mem_filter.mpr
    ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hblocks⟩, hfirstGood⟩,
      heFirst⟩

/-- Bad good-stubs with fewer than `q` tested vertices in their marker
neighborhood. -/
noncomputable def sparseBadStubs
    {G : Type} [Group G] (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (P : BlockStructure M) (E : Finset M) (K r q : ℕ)
    (marker : GoodCrossingStub (generatorGraph M S τ) P
      (badVertices (generatorGraph M S τ) P E K) → M)
    (U : Finset M) :=
  (badStubs (generatorGraph M S τ) P
    (badVertices (generatorGraph M S τ) P E K) marker U).filter fun s ↦
      ((forwardNeighborhood M τ S r {marker s}) ∩ U).card < q

theorem exists_goodInternalBoundary_of_sparseBadStub
    {G : Type} [Group G] (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (P : BlockStructure M) (E : Finset M) (K : ℕ)
    (marker : GoodCrossingStub (generatorGraph M S τ) P
      (badVertices (generatorGraph M S τ) P E K) → M)
    (r q : ℕ) (U : Finset M)
    (hneighborhoodCard : ∀ s, q ≤
      (forwardNeighborhood M τ S r {marker s}).card)
    (hneighborhoodBlock : ∀ s,
      forwardNeighborhood M τ S r {marker s} ⊆
        P.block (stubEndpoint (generatorGraph M S τ) P s.1))
    (s : GoodCrossingStub (generatorGraph M S τ) P
      (badVertices (generatorGraph M S τ) P E K))
    (hs : s ∈ sparseBadStubs M τ S P E K r q marker U) :
    ∃ e : (generatorGraph M S τ).edge,
      e ∈ (generatorGraph M S τ).boundary U ∧
      e ∈ goodInternalEdges (generatorGraph M S τ) P
        (badVertices (generatorGraph M S τ) P E K) ∧
      (generatorGraph M S τ).first e ∈
        forwardNeighborhood M τ S r {marker s} := by
  have hsdata := Finset.mem_filter.mp hs
  have hsbad := (Finset.mem_filter.mp hsdata.1).2
  have hnotSubset : ¬ forwardNeighborhood M τ S r {marker s} ⊆ U := by
    intro hsubset
    have hinter : (forwardNeighborhood M τ S r {marker s}) ∩ U =
        forwardNeighborhood M τ S r {marker s} :=
      Finset.inter_eq_left.mpr hsubset
    rw [hinter] at hsdata
    exact (not_lt_of_ge (hneighborhoodCard s)) hsdata.2
  obtain ⟨z, hz, hzout⟩ := Finset.not_subset.mp hnotSubset
  exact exists_goodInternalBoundary_of_marker_escape M τ S P E K marker
    (stubEndpoint (generatorGraph M S τ) P s.1) U s hsbad.2 r hz hzout
    (hneighborhoodBlock s) s.2

/-- A chosen retained boundary edge for each sparse bad good-stub. -/
noncomputable def sparseBoundaryEdge
    {G : Type} [Group G] (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (P : BlockStructure M) (E : Finset M) (K : ℕ)
    (marker : GoodCrossingStub (generatorGraph M S τ) P
      (badVertices (generatorGraph M S τ) P E K) → M)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint (generatorGraph M S τ) P s.1)
    (r q : ℕ) (U : Finset M)
    (hneighborhoodCard : ∀ s, q ≤
      (forwardNeighborhood M τ S r {marker s}).card)
    (hneighborhoodBlock : ∀ s,
      forwardNeighborhood M τ S r {marker s} ⊆
        P.block (stubEndpoint (generatorGraph M S τ) P s.1))
    (s : {s : GoodCrossingStub (generatorGraph M S τ) P
        (badVertices (generatorGraph M S τ) P E K) //
      s ∈ sparseBadStubs M τ S P E K r q marker U}) :
    {e : (KunSelectiveRepairGraph.graph (generatorGraph M S τ) P
        (badVertices (generatorGraph M S τ) P E K) marker marker_ne).edge //
      e ∈ (KunSelectiveRepairGraph.graph (generatorGraph M S τ) P
        (badVertices (generatorGraph M S τ) P E K) marker marker_ne).boundary U} := by
  let e := Classical.choose
    (exists_goodInternalBoundary_of_sparseBadStub M τ S P E K marker
      r q U hneighborhoodCard hneighborhoodBlock s.1 s.2)
  have he := Classical.choose_spec
    (exists_goodInternalBoundary_of_sparseBadStub M τ S P E K marker
      r q U hneighborhoodCard hneighborhoodBlock s.1 s.2)
  refine ⟨Sum.inl ⟨e, he.2.1⟩, ?_⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  change ((generatorGraph M S τ).first e ∈ U ∧
      (generatorGraph M S τ).second e ∉ U) ∨
    ((generatorGraph M S τ).second e ∈ U ∧
      (generatorGraph M S τ).first e ∉ U)
  exact (Finset.mem_filter.mp he.1).2

theorem sparseBoundaryEdge_first_mem
    {G : Type} [Group G] (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (P : BlockStructure M) (E : Finset M) (K : ℕ)
    (marker : GoodCrossingStub (generatorGraph M S τ) P
      (badVertices (generatorGraph M S τ) P E K) → M)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint (generatorGraph M S τ) P s.1)
    (r q : ℕ) (U : Finset M)
    (hneighborhoodCard : ∀ s, q ≤
      (forwardNeighborhood M τ S r {marker s}).card)
    (hneighborhoodBlock : ∀ s,
      forwardNeighborhood M τ S r {marker s} ⊆
        P.block (stubEndpoint (generatorGraph M S τ) P s.1))
    (s : {s : GoodCrossingStub (generatorGraph M S τ) P
        (badVertices (generatorGraph M S τ) P E K) //
      s ∈ sparseBadStubs M τ S P E K r q marker U}) :
    (KunSelectiveRepairGraph.graph (generatorGraph M S τ) P
      (badVertices (generatorGraph M S τ) P E K) marker marker_ne).first
        (sparseBoundaryEdge M τ S P E K marker marker_ne r q U
          hneighborhoodCard hneighborhoodBlock s) ∈
      forwardNeighborhood M τ S r {marker s.1} := by
  simp only [sparseBoundaryEdge]
  exact (Classical.choose_spec
    (exists_goodInternalBoundary_of_sparseBadStub M τ S P E K marker
      r q U hneighborhoodCard hneighborhoodBlock s.1 s.2)).2.2

/-- Sparse bad good-stubs inject into the selective repaired boundary. -/
theorem card_sparseBadStubs_le_boundaryCard
    {G : Type} [Group G] (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (P : BlockStructure M) (E : Finset M) (K : ℕ)
    (marker : GoodCrossingStub (generatorGraph M S τ) P
      (badVertices (generatorGraph M S τ) P E K) → M)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint (generatorGraph M S τ) P s.1)
    (r q : ℕ) (U : Finset M)
    (hneighborhoodCard : ∀ s, q ≤
      (forwardNeighborhood M τ S r {marker s}).card)
    (hneighborhoodBlock : ∀ s,
      forwardNeighborhood M τ S r {marker s} ⊆
        P.block (stubEndpoint (generatorGraph M S τ) P s.1))
    (hdisjoint : ∀ s t, s ≠ t →
      Disjoint (forwardNeighborhood M τ S r {marker s})
        (forwardNeighborhood M τ S r {marker t})) :
    (sparseBadStubs M τ S P E K r q marker U).card ≤
      (KunSelectiveRepairGraph.graph (generatorGraph M S τ) P
        (badVertices (generatorGraph M S τ) P E K) marker marker_ne).boundaryCard U := by
  let f := sparseBoundaryEdge M τ S P E K marker marker_ne r q U
    hneighborhoodCard hneighborhoodBlock
  have hf : Function.Injective f := by
    intro s t hst
    by_contra hne
    have hbase : s.1 ≠ t.1 := fun heq ↦ hne (Subtype.ext heq)
    have hsFirst := sparseBoundaryEdge_first_mem M τ S P E K marker marker_ne
      r q U hneighborhoodCard hneighborhoodBlock s
    have htFirst := sparseBoundaryEdge_first_mem M τ S P E K marker marker_ne
      r q U hneighborhoodCard hneighborhoodBlock t
    dsimp [f] at hst
    rw [← hst] at htFirst
    exact Finset.disjoint_left.mp (hdisjoint s.1 t.1 hbase) hsFirst htFirst
  simpa [FiniteMultiGraph.boundaryCard, Fintype.card_coe] using
    Fintype.card_le_of_injective f hf

/-- Dense bad good-stubs. -/
noncomputable def denseBadStubs
    {G : Type} [Group G] (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (P : BlockStructure M) (E : Finset M) (K r q : ℕ)
    (marker : GoodCrossingStub (generatorGraph M S τ) P
      (badVertices (generatorGraph M S τ) P E K) → M)
    (U : Finset M) :=
  (badStubs (generatorGraph M S τ) P
    (badVertices (generatorGraph M S τ) P E K) marker U).filter fun s ↦
      q ≤ ((forwardNeighborhood M τ S r {marker s}) ∩ U).card

theorem mul_card_badStubs_le_boundary_add_card
    {G : Type} [Group G] (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (P : BlockStructure M) (E : Finset M) (K : ℕ)
    (marker : GoodCrossingStub (generatorGraph M S τ) P
      (badVertices (generatorGraph M S τ) P E K) → M)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint (generatorGraph M S τ) P s.1)
    (r q : ℕ) (U : Finset M)
    (hneighborhoodCard : ∀ s, q ≤
      (forwardNeighborhood M τ S r {marker s}).card)
    (hneighborhoodBlock : ∀ s,
      forwardNeighborhood M τ S r {marker s} ⊆
        P.block (stubEndpoint (generatorGraph M S τ) P s.1))
    (hdisjoint : ∀ s t, s ≠ t →
      Disjoint (forwardNeighborhood M τ S r {marker s})
        (forwardNeighborhood M τ S r {marker t})) :
    q * (badStubs (generatorGraph M S τ) P
      (badVertices (generatorGraph M S τ) P E K) marker U).card ≤
      q * (KunSelectiveRepairGraph.graph (generatorGraph M S τ) P
        (badVertices (generatorGraph M S τ) P E K) marker marker_ne).boundaryCard U +
      U.card := by
  classical
  let sparse := sparseBadStubs M τ S P E K r q marker U
  let dense := denseBadStubs M τ S P E K r q marker U
  have hcover : badStubs (generatorGraph M S τ) P
      (badVertices (generatorGraph M S τ) P E K) marker U ⊆
      sparse ∪ dense := by
    intro s hs
    by_cases hsmall :
        ((forwardNeighborhood M τ S r {marker s}) ∩ U).card < q
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hs, hsmall⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hs, Nat.le_of_not_gt hsmall⟩)
  have hbadCard : (badStubs (generatorGraph M S τ) P
      (badVertices (generatorGraph M S τ) P E K) marker U).card ≤
      sparse.card + dense.card :=
    (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  have hsparse : sparse.card ≤
      (KunSelectiveRepairGraph.graph (generatorGraph M S τ) P
        (badVertices (generatorGraph M S τ) P E K) marker marker_ne).boundaryCard U :=
    card_sparseBadStubs_le_boundaryCard M τ S P E K marker marker_ne r q U
      hneighborhoodCard hneighborhoodBlock hdisjoint
  have hdense : q * dense.card ≤ U.card :=
    mul_card_le_of_card_inter_forwardNeighborhood M τ S r q marker
      hdisjoint dense U (fun s hs ↦ (Finset.mem_filter.mp hs).2)
  calc
    q * (badStubs (generatorGraph M S τ) P
        (badVertices (generatorGraph M S τ) P E K) marker U).card ≤
      q * (sparse.card + dense.card) := Nat.mul_le_mul_left q hbadCard
    _ = q * sparse.card + q * dense.card := Nat.mul_add _ _ _
    _ ≤ q * (KunSelectiveRepairGraph.graph (generatorGraph M S τ) P
        (badVertices (generatorGraph M S τ) P E K) marker marker_ne).boundaryCard U +
        U.card := Nat.add_le_add (Nat.mul_le_mul_left q hsparse) hdense

/-- A good-set original cut is retained up to the same quantitative loss as
in the full repair. -/
theorem mul_originalBoundary_le_two_mul_repaired_add_card
    {G : Type} [Group G] (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (P : BlockStructure M) (E : Finset M) (K : ℕ)
    (marker : GoodCrossingStub (generatorGraph M S τ) P
      (badVertices (generatorGraph M S τ) P E K) → M)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint (generatorGraph M S τ) P s.1)
    (r q : ℕ) (U : Finset M)
    (hUgood : ∀ x ∈ U,
      x ∉ badVertices (generatorGraph M S τ) P E K)
    (hneighborhoodCard : ∀ s, q ≤
      (forwardNeighborhood M τ S r {marker s}).card)
    (hneighborhoodBlock : ∀ s,
      forwardNeighborhood M τ S r {marker s} ⊆
        P.block (stubEndpoint (generatorGraph M S τ) P s.1))
    (hdisjoint : ∀ s t, s ≠ t →
      Disjoint (forwardNeighborhood M τ S r {marker s})
        (forwardNeighborhood M τ S r {marker t})) :
    q * (generatorGraph M S τ).boundaryCard U ≤
      2 * q * (KunSelectiveRepairGraph.graph (generatorGraph M S τ) P
        (badVertices (generatorGraph M S τ) P E K) marker marker_ne).boundaryCard U +
      U.card := by
  have horiginal := boundaryCard_le_repaired_add_badStubs
    (generatorGraph M S τ) P E K marker marker_ne U hUgood
  have hbad := mul_card_badStubs_le_boundary_add_card
    M τ S P E K marker marker_ne r q U hneighborhoodCard
      hneighborhoodBlock hdisjoint
  calc
    q * (generatorGraph M S τ).boundaryCard U ≤
      q * ((KunSelectiveRepairGraph.graph (generatorGraph M S τ) P
        (badVertices (generatorGraph M S τ) P E K) marker marker_ne).boundaryCard U +
        (badStubs (generatorGraph M S τ) P
          (badVertices (generatorGraph M S τ) P E K) marker U).card) :=
      Nat.mul_le_mul_left q horiginal
    _ = q * (KunSelectiveRepairGraph.graph (generatorGraph M S τ) P
        (badVertices (generatorGraph M S τ) P E K) marker marker_ne).boundaryCard U +
      q * (badStubs (generatorGraph M S τ) P
        (badVertices (generatorGraph M S τ) P E K) marker U).card := Nat.mul_add _ _ _
    _ ≤ q * (KunSelectiveRepairGraph.graph (generatorGraph M S τ) P
        (badVertices (generatorGraph M S τ) P E K) marker marker_ne).boundaryCard U +
      (q * (KunSelectiveRepairGraph.graph (generatorGraph M S τ) P
        (badVertices (generatorGraph M S τ) P E K) marker marker_ne).boundaryCard U +
        U.card) := Nat.add_le_add_left hbad _
    _ = 2 * q * (KunSelectiveRepairGraph.graph (generatorGraph M S τ) P
        (badVertices (generatorGraph M S τ) P E K) marker marker_ne).boundaryCard U +
      U.card := by ring

/-- Transfer a fixed original cut lower bound to the selective repaired
graph. -/
theorem repaired_boundary_lower
    {G : Type} [Group G] (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (P : BlockStructure M) (E : Finset M) (K : ℕ)
    (marker : GoodCrossingStub (generatorGraph M S τ) P
      (badVertices (generatorGraph M S τ) P E K) → M)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint (generatorGraph M S τ) P s.1)
    (r q : ℕ) (U : Finset M)
    (hUgood : ∀ x ∈ U,
      x ∉ badVertices (generatorGraph M S τ) P E K)
    (hneighborhoodCard : ∀ s, q ≤
      (forwardNeighborhood M τ S r {marker s}).card)
    (hneighborhoodBlock : ∀ s,
      forwardNeighborhood M τ S r {marker s} ⊆
        P.block (stubEndpoint (generatorGraph M S τ) P s.1))
    (hdisjoint : ∀ s t, s ≠ t →
      Disjoint (forwardNeighborhood M τ S r {marker s})
        (forwardNeighborhood M τ S r {marker t}))
    (γ : ℝ) (hγ : 0 < γ) (hq : 2 ≤ γ * q)
    (hglobal : γ * (U.card : ℝ) ≤
      (generatorGraph M S τ).boundaryCard U) :
    (γ / 4) * (U.card : ℝ) ≤
      (KunSelectiveRepairGraph.graph (generatorGraph M S τ) P
        (badVertices (generatorGraph M S τ) P E K) marker marker_ne).boundaryCard U := by
  have hquant := mul_originalBoundary_le_two_mul_repaired_add_card
    M τ S P E K marker marker_ne r q U hUgood hneighborhoodCard
      hneighborhoodBlock hdisjoint
  have hquantReal : (q : ℝ) *
      ((generatorGraph M S τ).boundaryCard U : ℝ) ≤
      2 * q * ((KunSelectiveRepairGraph.graph (generatorGraph M S τ) P
        (badVertices (generatorGraph M S τ) P E K) marker marker_ne).boundaryCard U : ℝ) +
      (U.card : ℝ) := by exact_mod_cast hquant
  have hqpos : (0 : ℝ) < q := by
    by_contra h
    have hq0 : (q : ℝ) = 0 := le_antisymm (le_of_not_gt h) (by positivity)
    rw [hq0, mul_zero] at hq
    linarith
  have hU0 : (0 : ℝ) ≤ U.card := by positivity
  have hrepair0 : (0 : ℝ) ≤
      (KunSelectiveRepairGraph.graph (generatorGraph M S τ) P
        (badVertices (generatorGraph M S τ) P E K) marker marker_ne).boundaryCard U := by
    positivity
  nlinarith

/-- Every component of the singleton-refined selective repair graph has the
same positive Cheeger lower bound: good blocks inherit repaired expansion,
while bad singleton blocks satisfy the cut condition vacuously. -/
theorem refined_component_expands
    {G : Type} [Group G] (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (P : BlockStructure M) (E : Finset M) (K : ℕ)
    (marker : GoodCrossingStub (generatorGraph M S τ) P
      (badVertices (generatorGraph M S τ) P E K) → M)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint (generatorGraph M S τ) P s.1)
    (marker_inside : ∀ s, marker s ∈
      P.block (stubEndpoint (generatorGraph M S τ) P s.1))
    (r q : ℕ)
    (hneighborhoodCard : ∀ s, q ≤
      (forwardNeighborhood M τ S r {marker s}).card)
    (hneighborhoodBlock : ∀ s,
      forwardNeighborhood M τ S r {marker s} ⊆
        P.block (stubEndpoint (generatorGraph M S τ) P s.1))
    (hdisjoint : ∀ s t, s ≠ t →
      Disjoint (forwardNeighborhood M τ S r {marker s})
        (forwardNeighborhood M τ S r {marker t}))
    (γ : ℝ) (hγ : 0 < γ) (hq : 2 ≤ γ * q)
    (hglobal : ∀ y : M, ∀ U : Finset M,
      U ⊆ P.block y → U.Nonempty →
      2 * U.card ≤ (P.block y).card →
      γ * (U.card : ℝ) ≤ (generatorGraph M S τ).boundaryCard U)
    (y : M) :
    FiniteMultiGraph.HasCheegerLowerBound
      ((KunSelectiveRepairGraph.graph (generatorGraph M S τ) P
        (badVertices (generatorGraph M S τ) P E K) marker marker_ne).induce
        ((singletonizeBadBlocks (generatorGraph M S τ) P E K).block y))
      (γ / 4) := by
  by_cases hybad : y ∈ badVertices (generatorGraph M S τ) P E K
  ·
    let Q := singletonizeBadBlocks (generatorGraph M S τ) P E K
    have hblock : Q.block y = {y} :=
      singletonizeBadBlocks_block_of_bad (generatorGraph M S τ) P E K hybad
    rw [hblock]
    exact FiniteMultiGraph.induce_singleton_hasCheegerLowerBound _ _
      (div_pos hγ (by norm_num))
  · let Z := KunSelectiveRepairGraph.graph (generatorGraph M S τ) P
      (badVertices (generatorGraph M S τ) P E K) marker marker_ne
    let Q := singletonizeBadBlocks (generatorGraph M S τ) P E K
    have hedge : ∀ e : Z.edge,
        Q.block (Z.first e) = Q.block (Z.second e) :=
      edge_inside_refined (generatorGraph M S τ) P E K marker marker_ne
        marker_inside
    apply KunRepairExpansion.induce_block_hasCheegerLowerBound Z Q hedge
      (γ / 4) (div_pos hγ (by norm_num)) y
    intro U hU hUne hhalf
    have hblock : Q.block y = P.block y :=
      singletonizeBadBlocks_block_of_good (generatorGraph M S τ) P E K hybad
    have hUP : U ⊆ P.block y := by simpa [hblock] using hU
    have hhalfP : 2 * U.card ≤ (P.block y).card := by
      rw [hblock] at hhalf
      exact hhalf
    have hUgood : ∀ x ∈ U,
        x ∉ badVertices (generatorGraph M S τ) P E K := by
      intro x hxU hxbad
      exact hybad ((mem_badVertices_iff_of_mem_block
        (generatorGraph M S τ) P E K (hUP hxU)).mpr hxbad)
    exact repaired_boundary_lower M τ S P E K marker marker_ne r q U
      hUgood hneighborhoodCard hneighborhoodBlock hdisjoint γ hγ hq
      (hglobal y U hUP hUne hhalfP)

/-- **Constant-perturbation probe for the bad-block branch.**  Replacing the
advertised `γ / 4` by an arbitrary positive `c` still elaborates when `y` is a
bad vertex, because refinement makes its block a singleton.  The statement is
kept as a report-only semantic alarm: downstream arguments must use the
separate negligibility theorem for these vertices, never interpret this branch
as quantitative expansion. -/
theorem refined_bad_component_expands_at_every_positive_constant
    {G : Type} [Group G] (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (P : BlockStructure M) (E : Finset M) (K : ℕ)
    (marker : GoodCrossingStub (generatorGraph M S τ) P
      (badVertices (generatorGraph M S τ) P E K) → M)
    (marker_ne : ∀ s, marker s ≠ stubEndpoint (generatorGraph M S τ) P s.1)
    (y : M) (hybad : y ∈ badVertices (generatorGraph M S τ) P E K)
    (c : ℝ) (hc : 0 < c) :
    FiniteMultiGraph.HasCheegerLowerBound
      ((KunSelectiveRepairGraph.graph (generatorGraph M S τ) P
        (badVertices (generatorGraph M S τ) P E K) marker marker_ne).induce
        ((singletonizeBadBlocks (generatorGraph M S τ) P E K).block y)) c := by
  rw [singletonizeBadBlocks_block_of_bad
    (generatorGraph M S τ) P E K hybad]
  exact FiniteMultiGraph.induce_singleton_hasCheegerLowerBound _ _ hc

end KunSelectiveRepairExpansion
end NonsoficGroupsExist
