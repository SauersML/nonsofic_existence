import NonsoficGroupsExist.KunMarkerSelection

/-!
# Expansion recovered by separated repair markers

Bad repaired stubs are divided into markers with large intersection with the
tested set and markers whose neighborhood escapes it.  Disjointness bounds the
first class.  A first-exit generator occurrence, retained inside the block,
injects the second class into the repaired boundary.
-/

namespace NonsoficGroupsExist
namespace KunRepairExpansion

open FiniteMultiGraph
open KunSupport
open KunBlockGraph
open KunRepairGraph
open KunMarkerSelection

/-- A finite forward trajectory that starts in `U` and ends outside `U`
contains a concrete generator occurrence crossing `U`; both endpoints occur
within the same trajectory horizon. -/
theorem exists_generatorBoundary_of_mem_forwardNeighborhood_not_mem
    {G : Type} [Group G] (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) {U : Finset M} (x : M) (hx : x ∈ U) (r : ℕ) {z : M}
    (hz : z ∈ forwardNeighborhood M τ S r {x}) (hzout : z ∉ U) :
    ∃ e : (generatorGraph M S τ).edge,
      e ∈ (generatorGraph M S τ).boundary U ∧
      (generatorGraph M S τ).first e ∈
        forwardNeighborhood M τ S r {x} ∧
      (generatorGraph M S τ).second e ∈
        forwardNeighborhood M τ S r {x} := by
  induction r generalizing z with
  | zero =>
      have hzx : z = x := by simpa [forwardNeighborhood] using hz
      subst z
      exact False.elim (hzout hx)
  | succ r ih =>
      change z ∈ forwardStep M τ S
        (forwardNeighborhood M τ S r {x}) at hz
      simp only [forwardStep, Finset.mem_union, Finset.mem_biUnion,
        Finset.mem_map] at hz
      rcases hz with hzPrev | ⟨s, hs, w, hw, hzw⟩
      · obtain ⟨e, heBoundary, heFirst, heSecond⟩ := ih hzPrev hzout
        exact ⟨e, heBoundary,
          forwardNeighborhood_subset_succ M τ S r {x} heFirst,
          forwardNeighborhood_subset_succ M τ S r {x} heSecond⟩
      · subst z
        by_cases hwU : w ∈ U
        · have hmove : τ s w ≠ w := by
            intro hfix
            exact hzout (by simpa [hfix] using hwU)
          let t : S := ⟨s, hs⟩
          let e : (generatorGraph M S τ).edge :=
            ⟨(t, w), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmove⟩⟩
          have heFirst : (generatorGraph M S τ).first e ∈
              forwardNeighborhood M τ S (r + 1) {x} := by
            simpa [e, t] using
              forwardNeighborhood_subset_succ M τ S r {x} hw
          have heSecond : (generatorGraph M S τ).second e ∈
              forwardNeighborhood M τ S (r + 1) {x} := by
            change τ s w ∈ forwardStep M τ S
              (forwardNeighborhood M τ S r {x})
            exact mem_forwardStep_of_mem M τ S _ hs hw
          refine ⟨e, ?_, heFirst, heSecond⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨by
            simpa [e, t] using hwU, by simpa [e, t] using hzout⟩⟩
        · obtain ⟨e, heBoundary, heFirst, heSecond⟩ := ih hw hwU
          exact ⟨e, heBoundary,
            forwardNeighborhood_subset_succ M τ S r {x} heFirst,
            forwardNeighborhood_subset_succ M τ S r {x} heSecond⟩

/-- Inside one partition block, a trajectory escape from `U` supplies an
original internal occurrence that is retained as a repaired boundary edge. -/
theorem exists_internalBoundary_of_marker_escape
    {G : Type} [Group G] (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (P : BlockStructure M)
    (marker : CrossingStub (generatorGraph M S τ) P → M)
    (y : M) (U : Finset M)
    (s : CrossingStub (generatorGraph M S τ) P)
    (hmarkerU : marker s ∈ U) (r : ℕ) {z : M}
    (hz : z ∈ forwardNeighborhood M τ S r {marker s}) (hzout : z ∉ U)
    (hneighborhood : forwardNeighborhood M τ S r {marker s} ⊆ P.block y) :
    ∃ e : (generatorGraph M S τ).edge,
      e ∈ (generatorGraph M S τ).boundary U ∧
      e ∈ internalEdges (generatorGraph M S τ) P ∧
      (generatorGraph M S τ).first e ∈
        forwardNeighborhood M τ S r {marker s} := by
  obtain ⟨e, heBoundary, heFirst, heSecond⟩ :=
    exists_generatorBoundary_of_mem_forwardNeighborhood_not_mem
      M τ S (marker s) hmarkerU r hz hzout
  have hfirstBlock : (generatorGraph M S τ).first e ∈ P.block y :=
    hneighborhood heFirst
  have hsecondBlock : (generatorGraph M S τ).second e ∈ P.block y :=
    hneighborhood heSecond
  have hblocks :
      P.block ((generatorGraph M S τ).first e) =
        P.block ((generatorGraph M S τ).second e) := by
    exact (P.eq_of_mem y _ hfirstBlock).trans
      (P.eq_of_mem y _ hsecondBlock).symm
  exact ⟨e, heBoundary,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hblocks⟩, heFirst⟩

/-- Bad stubs whose marker neighborhood contains fewer than `q` vertices of
the tested set. -/
noncomputable def sparseBadStubs
    {G : Type} [Group G] (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (P : BlockStructure M)
    (marker : CrossingStub (generatorGraph M S τ) P → M)
    (r q : ℕ) (U : Finset M) :
    Finset (CrossingStub (generatorGraph M S τ) P) :=
  (badStubs (generatorGraph M S τ) P marker U).filter fun s ↦
    ((forwardNeighborhood M τ S r {marker s}) ∩ U).card < q

/-- Every sparse bad stub produces a retained internal edge crossing `U`. -/
theorem exists_repairedBoundary_of_mem_sparseBadStubs
    {G : Type} [Group G] (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (P : BlockStructure M)
    (marker : CrossingStub (generatorGraph M S τ) P → M)
    (r q : ℕ) (U : Finset M)
    (hneighborhoodCard : ∀ s, q ≤
      (forwardNeighborhood M τ S r {marker s}).card)
    (hneighborhoodBlock : ∀ s,
      forwardNeighborhood M τ S r {marker s} ⊆
        P.block (stubEndpoint (generatorGraph M S τ) P s))
    (s : CrossingStub (generatorGraph M S τ) P)
    (hs : s ∈ sparseBadStubs M τ S P marker r q U) :
    ∃ e : (generatorGraph M S τ).edge,
      e ∈ (generatorGraph M S τ).boundary U ∧
      e ∈ internalEdges (generatorGraph M S τ) P ∧
      (generatorGraph M S τ).first e ∈
        forwardNeighborhood M τ S r {marker s} := by
  have hsdata := Finset.mem_filter.mp hs
  have hsbad := (Finset.mem_filter.mp hsdata.1).2
  have hmarkerU : marker s ∈ U := hsbad.2
  have hnotSubset : ¬ forwardNeighborhood M τ S r {marker s} ⊆ U := by
    intro hsubset
    have hinter : (forwardNeighborhood M τ S r {marker s}) ∩ U =
        forwardNeighborhood M τ S r {marker s} :=
      Finset.inter_eq_left.mpr hsubset
    rw [hinter] at hsdata
    exact (not_lt_of_ge (hneighborhoodCard s)) hsdata.2
  obtain ⟨z, hz, hzout⟩ := Finset.not_subset.mp hnotSubset
  exact exists_internalBoundary_of_marker_escape M τ S P marker
    (stubEndpoint (generatorGraph M S τ) P s) U s hmarkerU r hz hzout
    (hneighborhoodBlock s)

/-- A chosen retained boundary occurrence for each sparse bad stub. -/
noncomputable def sparseBoundaryEdge
    {G : Type} [Group G] (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (P : BlockStructure M)
    (marker : CrossingStub (generatorGraph M S τ) P → M)
    (marker_ne : ∀ s, marker s ≠
      stubEndpoint (generatorGraph M S τ) P s)
    (r q : ℕ) (U : Finset M)
    (hneighborhoodCard : ∀ s, q ≤
      (forwardNeighborhood M τ S r {marker s}).card)
    (hneighborhoodBlock : ∀ s,
      forwardNeighborhood M τ S r {marker s} ⊆
        P.block (stubEndpoint (generatorGraph M S τ) P s))
    (s : {s : CrossingStub (generatorGraph M S τ) P //
      s ∈ sparseBadStubs M τ S P marker r q U}) :
    {e : (graph (generatorGraph M S τ) P marker marker_ne).edge //
      e ∈ (graph (generatorGraph M S τ) P marker marker_ne).boundary U} := by
  let e := Classical.choose
    (exists_repairedBoundary_of_mem_sparseBadStubs M τ S P marker
      r q U hneighborhoodCard hneighborhoodBlock s.1 s.2)
  have he := Classical.choose_spec
    (exists_repairedBoundary_of_mem_sparseBadStubs M τ S P marker
      r q U hneighborhoodCard hneighborhoodBlock s.1 s.2)
  exact ⟨Sum.inl ⟨e, he.2.1⟩, by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp he.1).2⟩⟩

theorem sparseBoundaryEdge_first_mem
    {G : Type} [Group G] (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (P : BlockStructure M)
    (marker : CrossingStub (generatorGraph M S τ) P → M)
    (marker_ne : ∀ s, marker s ≠
      stubEndpoint (generatorGraph M S τ) P s)
    (r q : ℕ) (U : Finset M)
    (hneighborhoodCard : ∀ s, q ≤
      (forwardNeighborhood M τ S r {marker s}).card)
    (hneighborhoodBlock : ∀ s,
      forwardNeighborhood M τ S r {marker s} ⊆
        P.block (stubEndpoint (generatorGraph M S τ) P s))
    (s : {s : CrossingStub (generatorGraph M S τ) P //
      s ∈ sparseBadStubs M τ S P marker r q U}) :
    (graph (generatorGraph M S τ) P marker marker_ne).first
        (sparseBoundaryEdge M τ S P marker marker_ne r q U
          hneighborhoodCard hneighborhoodBlock s) ∈
      forwardNeighborhood M τ S r {marker s.1} := by
  simp only [sparseBoundaryEdge]
  exact (Classical.choose_spec
    (exists_repairedBoundary_of_mem_sparseBadStubs M τ S P marker
      r q U hneighborhoodCard hneighborhoodBlock s.1 s.2)).2.2

/-- Sparse bad stubs inject into the repaired boundary because their marker
neighborhoods are pairwise disjoint. -/
theorem card_sparseBadStubs_le_boundaryCard
    {G : Type} [Group G] (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (P : BlockStructure M)
    (marker : CrossingStub (generatorGraph M S τ) P → M)
    (marker_ne : ∀ s, marker s ≠
      stubEndpoint (generatorGraph M S τ) P s)
    (r q : ℕ) (U : Finset M)
    (hneighborhoodCard : ∀ s, q ≤
      (forwardNeighborhood M τ S r {marker s}).card)
    (hneighborhoodBlock : ∀ s,
      forwardNeighborhood M τ S r {marker s} ⊆
        P.block (stubEndpoint (generatorGraph M S τ) P s))
    (hdisjoint : ∀ s t, s ≠ t →
      Disjoint (forwardNeighborhood M τ S r {marker s})
        (forwardNeighborhood M τ S r {marker t})) :
    (sparseBadStubs M τ S P marker r q U).card ≤
      (graph (generatorGraph M S τ) P marker marker_ne).boundaryCard U := by
  let f := sparseBoundaryEdge M τ S P marker marker_ne r q U
    hneighborhoodCard hneighborhoodBlock
  have hf : Function.Injective f := by
    intro s t hst
    by_contra hne
    have hneBase : s.1 ≠ t.1 := by
      intro heq
      exact hne (Subtype.ext heq)
    have hsFirst := sparseBoundaryEdge_first_mem M τ S P marker marker_ne
      r q U hneighborhoodCard hneighborhoodBlock s
    have htFirst := sparseBoundaryEdge_first_mem M τ S P marker marker_ne
      r q U hneighborhoodCard hneighborhoodBlock t
    dsimp [f] at hst
    rw [← hst] at htFirst
    exact Finset.disjoint_left.mp (hdisjoint s.1 t.1 hneBase) hsFirst htFirst
  simpa [FiniteMultiGraph.boundaryCard, Fintype.card_coe] using
    Fintype.card_le_of_injective f hf

/-- Bad stubs whose marker neighborhood contains at least `q` vertices of the
tested set. -/
noncomputable def denseBadStubs
    {G : Type} [Group G] (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (P : BlockStructure M)
    (marker : CrossingStub (generatorGraph M S τ) P → M)
    (r q : ℕ) (U : Finset M) :
    Finset (CrossingStub (generatorGraph M S τ) P) := by
  classical
  exact (badStubs (generatorGraph M S τ) P marker U).filter fun s ↦
    q ≤ ((forwardNeighborhood M τ S r {marker s}) ∩ U).card

/-- The dense bad stubs are controlled by disjoint-neighborhood mass. -/
theorem mul_card_denseBadStubs_le
    {G : Type} [Group G] (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (P : BlockStructure M)
    (marker : CrossingStub (generatorGraph M S τ) P → M)
    (r q : ℕ) (U : Finset M)
    (hdisjoint : ∀ s t, s ≠ t →
      Disjoint (forwardNeighborhood M τ S r {marker s})
        (forwardNeighborhood M τ S r {marker t})) :
    q * (denseBadStubs M τ S P marker r q U).card ≤ U.card := by
  classical
  exact mul_card_le_of_card_inter_forwardNeighborhood
    M τ S r q marker hdisjoint _ U
      (fun s hs ↦ (Finset.mem_filter.mp hs).2)

/-- Every bad stub is sparse or dense. -/
theorem mem_sparseBadStubs_or_mem_denseBadStubs
    {G : Type} [Group G] (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (P : BlockStructure M)
    (marker : CrossingStub (generatorGraph M S τ) P → M)
    (r q : ℕ) (U : Finset M)
    (s : CrossingStub (generatorGraph M S τ) P)
    (hs : s ∈ badStubs (generatorGraph M S τ) P marker U) :
    s ∈ sparseBadStubs M τ S P marker r q U ∨
      s ∈ denseBadStubs M τ S P marker r q U := by
  by_cases hsmall :
      ((forwardNeighborhood M τ S r {marker s}) ∩ U).card < q
  · exact Or.inl (Finset.mem_filter.mpr ⟨hs, hsmall⟩)
  · exact Or.inr (Finset.mem_filter.mpr ⟨hs, Nat.le_of_not_gt hsmall⟩)

/-- Quantitative bad-stub bound: after multiplying by `q`, failures are paid
for by repaired boundary occurrences and tested-set mass. -/
theorem mul_card_badStubs_le_boundary_add_card
    {G : Type} [Group G] (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (P : BlockStructure M)
    (marker : CrossingStub (generatorGraph M S τ) P → M)
    (marker_ne : ∀ s, marker s ≠
      stubEndpoint (generatorGraph M S τ) P s)
    (r q : ℕ) (U : Finset M)
    (hneighborhoodCard : ∀ s, q ≤
      (forwardNeighborhood M τ S r {marker s}).card)
    (hneighborhoodBlock : ∀ s,
      forwardNeighborhood M τ S r {marker s} ⊆
        P.block (stubEndpoint (generatorGraph M S τ) P s))
    (hdisjoint : ∀ s t, s ≠ t →
      Disjoint (forwardNeighborhood M τ S r {marker s})
        (forwardNeighborhood M τ S r {marker t})) :
    q * (badStubs (generatorGraph M S τ) P marker U).card ≤
      q * (graph (generatorGraph M S τ) P marker marker_ne).boundaryCard U +
        U.card := by
  classical
  have hcover : badStubs (generatorGraph M S τ) P marker U ⊆
      sparseBadStubs M τ S P marker r q U ∪
        denseBadStubs M τ S P marker r q U := by
    intro s hs
    rcases mem_sparseBadStubs_or_mem_denseBadStubs
      M τ S P marker r q U s hs with hsparse | hdense
    · exact Finset.mem_union_left _ hsparse
    · exact Finset.mem_union_right _ hdense
  have hbadCard :
      (badStubs (generatorGraph M S τ) P marker U).card ≤
        (sparseBadStubs M τ S P marker r q U).card +
          (denseBadStubs M τ S P marker r q U).card := by
    exact (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  have hsparse := card_sparseBadStubs_le_boundaryCard
    M τ S P marker marker_ne r q U hneighborhoodCard hneighborhoodBlock
      hdisjoint
  have hdense := mul_card_denseBadStubs_le M τ S P marker r q U hdisjoint
  calc
    q * (badStubs (generatorGraph M S τ) P marker U).card ≤
        q * ((sparseBadStubs M τ S P marker r q U).card +
          (denseBadStubs M τ S P marker r q U).card) :=
      Nat.mul_le_mul_left q hbadCard
    _ = q * (sparseBadStubs M τ S P marker r q U).card +
        q * (denseBadStubs M τ S P marker r q U).card := Nat.mul_add _ _ _
    _ ≤ q * (graph (generatorGraph M S τ) P marker marker_ne).boundaryCard U +
        U.card := Nat.add_le_add (Nat.mul_le_mul_left q hsparse) hdense

/-- The repaired boundary retains a fixed fraction of every original cut,
up to the explicit `|U|/q` loss encoded without division. -/
theorem mul_originalBoundary_le_two_mul_repaired_add_card
    {G : Type} [Group G] (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (P : BlockStructure M)
    (marker : CrossingStub (generatorGraph M S τ) P → M)
    (marker_ne : ∀ s, marker s ≠
      stubEndpoint (generatorGraph M S τ) P s)
    (r q : ℕ) (U : Finset M)
    (hneighborhoodCard : ∀ s, q ≤
      (forwardNeighborhood M τ S r {marker s}).card)
    (hneighborhoodBlock : ∀ s,
      forwardNeighborhood M τ S r {marker s} ⊆
        P.block (stubEndpoint (generatorGraph M S τ) P s))
    (hdisjoint : ∀ s t, s ≠ t →
      Disjoint (forwardNeighborhood M τ S r {marker s})
        (forwardNeighborhood M τ S r {marker t})) :
    q * (generatorGraph M S τ).boundaryCard U ≤
      2 * q * (graph (generatorGraph M S τ) P marker marker_ne).boundaryCard U +
        U.card := by
  have horiginal := boundaryCard_le_repaired_add_badStubs
    (generatorGraph M S τ) P marker marker_ne U
  have hbad := mul_card_badStubs_le_boundary_add_card
    M τ S P marker marker_ne r q U hneighborhoodCard hneighborhoodBlock
      hdisjoint
  calc
    q * (generatorGraph M S τ).boundaryCard U ≤
        q * ((graph (generatorGraph M S τ) P marker marker_ne).boundaryCard U +
          (badStubs (generatorGraph M S τ) P marker U).card) :=
      Nat.mul_le_mul_left q horiginal
    _ = q * (graph (generatorGraph M S τ) P marker marker_ne).boundaryCard U +
        q * (badStubs (generatorGraph M S τ) P marker U).card :=
      Nat.mul_add _ _ _
    _ ≤ q * (graph (generatorGraph M S τ) P marker marker_ne).boundaryCard U +
        (q * (graph (generatorGraph M S τ) P marker marker_ne).boundaryCard U +
          U.card) := Nat.add_le_add_left hbad _
    _ = 2 * q * (graph (generatorGraph M S τ) P marker marker_ne).boundaryCard U +
        U.card := by ring

/-- A global cut lower bound transfers to a fixed repaired cut lower bound
once `q` dominates its reciprocal loss. -/
theorem repaired_boundary_lower
    {G : Type} [Group G] (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (P : BlockStructure M)
    (marker : CrossingStub (generatorGraph M S τ) P → M)
    (marker_ne : ∀ s, marker s ≠
      stubEndpoint (generatorGraph M S τ) P s)
    (r q : ℕ) (U : Finset M)
    (hneighborhoodCard : ∀ s, q ≤
      (forwardNeighborhood M τ S r {marker s}).card)
    (hneighborhoodBlock : ∀ s,
      forwardNeighborhood M τ S r {marker s} ⊆
        P.block (stubEndpoint (generatorGraph M S τ) P s))
    (hdisjoint : ∀ s t, s ≠ t →
      Disjoint (forwardNeighborhood M τ S r {marker s})
        (forwardNeighborhood M τ S r {marker t}))
    (γ : ℝ) (hγ : 0 < γ) (hq : 2 ≤ γ * q)
    (hglobal : γ * (U.card : ℝ) ≤
      (generatorGraph M S τ).boundaryCard U) :
    (γ / 4) * (U.card : ℝ) ≤
      (graph (generatorGraph M S τ) P marker marker_ne).boundaryCard U := by
  have hquant := mul_originalBoundary_le_two_mul_repaired_add_card
    M τ S P marker marker_ne r q U hneighborhoodCard hneighborhoodBlock
      hdisjoint
  have hquantReal :
      (q : ℝ) * ((generatorGraph M S τ).boundaryCard U : ℝ) ≤
        2 * q *
            ((graph (generatorGraph M S τ) P marker marker_ne).boundaryCard U : ℝ) +
          (U.card : ℝ) := by
    exact_mod_cast hquant
  have hqpos : (0 : ℝ) < q := by
    by_contra h
    have hq0 : (q : ℝ) = 0 := le_antisymm (le_of_not_gt h) (by positivity)
    rw [hq0, mul_zero] at hq
    linarith
  have hU0 : (0 : ℝ) ≤ U.card := by positivity
  have hrepair0 : (0 : ℝ) ≤
      (graph (generatorGraph M S τ) P marker marker_ne).boundaryCard U := by
    positivity
  nlinarith

/-- For a graph whose edges stay inside partition blocks, the full-graph
boundary of a subset of one block is exactly its boundary in the induced
block graph. -/
theorem boundaryCard_induce_block_eq
    (Z : FiniteMultiGraph) (P : BlockStructure Z.vertex)
    (hedge : ∀ e : Z.edge,
      P.block (Z.first e) = P.block (Z.second e))
    (y : Z.vertex) (U : Finset (Z.induce (P.block y)).vertex) :
    (Z.induce (P.block y)).boundaryCard U =
      Z.boundaryCard (U.map (Function.Embedding.subtype _)) := by
  classical
  let U₀ : Finset Z.vertex := U.map (Function.Embedding.subtype _)
  have hmem (v : Z.vertex) (hv : v ∈ P.block y) :
      (⟨v, hv⟩ : (Z.induce (P.block y)).vertex) ∈ U ↔ v ∈ U₀ := by
    constructor
    · intro hvU
      exact Finset.mem_map.mpr ⟨⟨v, hv⟩, hvU, rfl⟩
    · intro hvU₀
      obtain ⟨v', hv'U, hv'v⟩ := Finset.mem_map.mp hvU₀
      have hv'eq : v' = ⟨v, hv⟩ := Subtype.ext hv'v
      rw [← hv'eq]
      exact hv'U
  apply Finset.card_bij (fun e _ ↦ e.1)
  · intro e he
    have hedata := (Finset.mem_filter.mp he).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hedata with h | h
    · exact Or.inl ⟨(hmem _ e.2.1).mp h.1, fun hsU₀ ↦
        h.2 ((hmem _ e.2.2).mpr hsU₀)⟩
    · exact Or.inr ⟨(hmem _ e.2.2).mp h.1, fun hfU₀ ↦
        h.2 ((hmem _ e.2.1).mpr hfU₀)⟩
  · intro e _ e' _ heq
    exact Subtype.ext heq
  · intro e he
    have hedata := (Finset.mem_filter.mp he).2
    have hU₀subset : U₀ ⊆ P.block y := by
      intro v hv
      obtain ⟨v', _, rfl⟩ := Finset.mem_map.mp hv
      exact v'.2
    have hfirstOrSecond : Z.first e ∈ P.block y ∨ Z.second e ∈ P.block y := by
      rcases hedata with h | h
      · exact Or.inl (hU₀subset h.1)
      · exact Or.inr (hU₀subset h.1)
    have hends : Z.first e ∈ P.block y ∧ Z.second e ∈ P.block y := by
      rcases hfirstOrSecond with hfirst | hsecond
      · have hfirstBlock : P.block (Z.first e) = P.block y :=
          P.eq_of_mem y _ hfirst
        have hsecond : Z.second e ∈ P.block y := by
          rw [← hfirstBlock, hedge e]
          exact P.self_mem _
        exact ⟨hfirst, hsecond⟩
      · have hsecondBlock : P.block (Z.second e) = P.block y :=
          P.eq_of_mem y _ hsecond
        have hfirst : Z.first e ∈ P.block y := by
          rw [← hsecondBlock, ← hedge e]
          exact P.self_mem _
        exact ⟨hfirst, hsecond⟩
    let a : (Z.induce (P.block y)).edge := ⟨e, hends⟩
    refine ⟨a, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hedata with h | h
    · exact Or.inl ⟨(hmem _ hends.1).mpr h.1, fun hsU ↦
        h.2 ((hmem _ hends.2).mp hsU)⟩
    · exact Or.inr ⟨(hmem _ hends.2).mpr h.1, fun hfU ↦
        h.2 ((hmem _ hends.1).mp hfU)⟩

/-- A blockwise full-graph cut inequality is therefore the Cheeger inequality
for the corresponding induced component. -/
theorem induce_block_hasCheegerLowerBound
    (Z : FiniteMultiGraph) (P : BlockStructure Z.vertex)
    (hedge : ∀ e : Z.edge,
      P.block (Z.first e) = P.block (Z.second e))
    (γ : ℝ) (hγ : 0 < γ) (y : Z.vertex)
    (hcut : ∀ U : Finset Z.vertex, U ⊆ P.block y → U.Nonempty →
      2 * U.card ≤ (P.block y).card →
        γ * (U.card : ℝ) ≤ Z.boundaryCard U) :
    (Z.induce (P.block y)).HasCheegerLowerBound γ := by
  refine ⟨hγ, ?_⟩
  intro U hU hhalf
  let U₀ : Finset Z.vertex := U.map (Function.Embedding.subtype _)
  have hU₀subset : U₀ ⊆ P.block y := by
    intro z hz
    obtain ⟨z', _, rfl⟩ := Finset.mem_map.mp hz
    exact z'.2
  have hU₀ : U₀.Nonempty := by
    obtain ⟨u, hu⟩ := hU
    exact ⟨u.1, Finset.mem_map.mpr ⟨u, hu, rfl⟩⟩
  have hcard : U₀.card = U.card := Finset.card_map _
  have hvertexCard : Fintype.card (Z.induce (P.block y)).vertex =
      (P.block y).card := by
    simp [FiniteMultiGraph.induce]
  have hhalf₀ : 2 * U₀.card ≤ (P.block y).card := by
    rw [hcard]
    rw [← hvertexCard]
    exact hhalf
  have hfull := hcut U₀ hU₀subset hU₀ hhalf₀
  rw [boundaryCard_induce_block_eq Z P hedge y U]
  simpa [U₀, hcard] using hfull

end KunRepairExpansion
end NonsoficGroupsExist
