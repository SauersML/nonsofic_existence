import NonsoficGroupsExist.BlockEnumeration
import NonsoficGroupsExist.KunMarkerSelection

/-!
# Isolating blocks that cannot support Kun repair markers

A block is declared bad when its local sofic-error mass plus the marker
packing cost of its crossing stubs is at least the block size.  The union of
bad blocks has cardinality bounded by the global error mass plus the global
stub count.  Refining exactly those blocks to singletons therefore costs only
a negligible vertex set in the asymptotic construction.
-/

namespace NonsoficGroupsExist
namespace KunBadBlocks

open KunMarkerSelection
open KunRepairGraph

/-- The local obstruction to fitting all repair markers in a block. -/
def packingCost (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (E C : Finset X.vertex) (K : ℕ) : ℕ :=
  (E ∩ C).card + K * (blockStubs X P C).card

/-- Blocks whose size does not dominate the packing cost. -/
noncomputable def badBlocks (X : FiniteMultiGraph)
    (P : BlockStructure X.vertex) (E : Finset X.vertex) (K : ℕ) :
    Finset (Finset X.vertex) :=
  P.blocksFinset.filter fun C ↦ C.card ≤ packingCost X P E C K

/-- The union of all bad blocks. -/
noncomputable def badVertices (X : FiniteMultiGraph)
    (P : BlockStructure X.vertex) (E : Finset X.vertex) (K : ℕ) :
    Finset X.vertex :=
  (badBlocks X P E K).biUnion id

theorem mem_badBlocks_iff (X : FiniteMultiGraph)
    (P : BlockStructure X.vertex) (E : Finset X.vertex) (K : ℕ)
    (C : Finset X.vertex) :
    C ∈ badBlocks X P E K ↔
      C ∈ P.blocksFinset ∧ C.card ≤ packingCost X P E C K := by
  simp [badBlocks]

/-- Badness is constant on each original partition block. -/
theorem mem_badVertices_iff (X : FiniteMultiGraph)
    (P : BlockStructure X.vertex) (E : Finset X.vertex) (K : ℕ)
    (y : X.vertex) :
    y ∈ badVertices X P E K ↔
      (P.block y).card ≤ packingCost X P E (P.block y) K := by
  classical
  constructor
  · intro hy
    obtain ⟨C, hCbad, hyC⟩ := Finset.mem_biUnion.mp hy
    obtain ⟨x, hxC⟩ := (P.mem_blocksFinset C).mp
      (mem_badBlocks_iff X P E K C |>.mp hCbad).1
    have hCy : C = P.block y := by
      rw [hxC]
      exact (P.eq_of_mem x y (by simpa [hxC] using hyC)).symm
    exact hCy ▸ (mem_badBlocks_iff X P E K C |>.mp hCbad).2
  · intro hy
    apply Finset.mem_biUnion.mpr
    refine ⟨P.block y, ?_, P.self_mem y⟩
    exact (mem_badBlocks_iff X P E K (P.block y)).mpr
      ⟨P.block_mem_blocksFinset y, hy⟩

theorem badBlocks_pairwise_disjoint (X : FiniteMultiGraph)
    (P : BlockStructure X.vertex) (E : Finset X.vertex) (K : ℕ) :
    (badBlocks X P E K : Set (Finset X.vertex)).PairwiseDisjoint id := by
  intro C hC D hD hne
  exact P.blocksFinset_pairwise_disjoint
    (Finset.mem_filter.mp hC).1 (Finset.mem_filter.mp hD).1 hne

theorem card_badVertices_eq_sum (X : FiniteMultiGraph)
    (P : BlockStructure X.vertex) (E : Finset X.vertex) (K : ℕ) :
    (badVertices X P E K).card =
      ∑ C ∈ badBlocks X P E K, C.card := by
  classical
  exact Finset.card_biUnion (badBlocks_pairwise_disjoint X P E K)

private theorem inter_blocks_pairwise_disjoint (X : FiniteMultiGraph)
    (P : BlockStructure X.vertex) (E : Finset X.vertex) (K : ℕ) :
    (badBlocks X P E K : Set (Finset X.vertex)).PairwiseDisjoint
      (fun C ↦ E ∩ C) := by
  intro C hC D hD hne
  exact (badBlocks_pairwise_disjoint X P E K hC hD hne).mono
    Finset.inter_subset_right Finset.inter_subset_right

private theorem sum_inter_card_le (X : FiniteMultiGraph)
    (P : BlockStructure X.vertex) (E : Finset X.vertex) (K : ℕ) :
    ∑ C ∈ badBlocks X P E K, (E ∩ C).card ≤ E.card := by
  classical
  rw [← Finset.card_biUnion (inter_blocks_pairwise_disjoint X P E K)]
  apply Finset.card_le_card
  intro y hy
  obtain ⟨C, _, hyC⟩ := Finset.mem_biUnion.mp hy
  exact (Finset.mem_inter.mp hyC).1

private theorem blockStubs_disjoint_of_disjoint
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    {C D : Finset X.vertex} (hCD : Disjoint C D) :
    Disjoint (blockStubs X P C) (blockStubs X P D) := by
  rw [Finset.disjoint_left]
  intro s hsC hsD
  exact Finset.disjoint_left.mp hCD
    (Finset.mem_filter.mp hsC).2 (Finset.mem_filter.mp hsD).2

private theorem blockStubs_badBlocks_pairwise_disjoint
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (E : Finset X.vertex) (K : ℕ) :
    (badBlocks X P E K : Set (Finset X.vertex)).PairwiseDisjoint
      (blockStubs X P) := by
  intro C hC D hD hne
  exact blockStubs_disjoint_of_disjoint X P
    (badBlocks_pairwise_disjoint X P E K hC hD hne)

private theorem sum_blockStubs_card_le (X : FiniteMultiGraph)
    (P : BlockStructure X.vertex) (E : Finset X.vertex) (K : ℕ) :
    ∑ C ∈ badBlocks X P E K, (blockStubs X P C).card ≤
      Fintype.card (CrossingStub X P) := by
  classical
  rw [← Finset.card_biUnion
    (blockStubs_badBlocks_pairwise_disjoint X P E K)]
  rw [← Finset.card_univ]
  exact Finset.card_le_card (Finset.subset_univ _)

/-- The total mass of blocks that fail the packing inequality is charged to
the global exceptional set and the global number of crossing stubs. -/
theorem card_badVertices_le (X : FiniteMultiGraph)
    (P : BlockStructure X.vertex) (E : Finset X.vertex) (K : ℕ) :
    (badVertices X P E K).card ≤
      E.card + K * Fintype.card (CrossingStub X P) := by
  classical
  rw [card_badVertices_eq_sum]
  calc
    ∑ C ∈ badBlocks X P E K, C.card ≤
        ∑ C ∈ badBlocks X P E K, packingCost X P E C K := by
      exact Finset.sum_le_sum fun C hC ↦
        (mem_badBlocks_iff X P E K C |>.mp hC).2
    _ = (∑ C ∈ badBlocks X P E K, (E ∩ C).card) +
        K * ∑ C ∈ badBlocks X P E K, (blockStubs X P C).card := by
      simp only [packingCost, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ E.card + K * Fintype.card (CrossingStub X P) := by
      exact Nat.add_le_add (sum_inter_card_le X P E K)
        (Nat.mul_le_mul_left K (sum_blockStubs_card_le X P E K))

/-- Refine every bad original block into singleton blocks, leaving every good
block unchanged. -/
noncomputable def singletonizeBadBlocks (X : FiniteMultiGraph)
    (P : BlockStructure X.vertex) (E : Finset X.vertex) (K : ℕ) :
    BlockStructure X.vertex where
  block y := if y ∈ badVertices X P E K then {y} else P.block y
  self_mem y := by
    by_cases hy : y ∈ badVertices X P E K
    · simp [hy]
    · simp [hy, P.self_mem]
  eq_of_mem x y hy := by
    by_cases hx : x ∈ badVertices X P E K
    · have hyx : y = x := by simpa [hx] using hy
      subst y
      rfl
    · have hyP : y ∈ P.block x := by simpa [hx] using hy
      have hblocks : P.block y = P.block x := P.eq_of_mem x y hyP
      have hybad : y ∉ badVertices X P E K := by
        rw [mem_badVertices_iff, hblocks]
        simpa [mem_badVertices_iff] using hx
      simp [hx, hybad, hblocks]

@[simp] theorem singletonizeBadBlocks_block_of_bad
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (E : Finset X.vertex) (K : ℕ) {y : X.vertex}
    (hy : y ∈ badVertices X P E K) :
    (singletonizeBadBlocks X P E K).block y = {y} := by
  simp [singletonizeBadBlocks, hy]

@[simp] theorem singletonizeBadBlocks_block_of_good
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (E : Finset X.vertex) (K : ℕ) {y : X.vertex}
    (hy : y ∉ badVertices X P E K) :
    (singletonizeBadBlocks X P E K).block y = P.block y := by
  simp [singletonizeBadBlocks, hy]

/-- Every retained original block satisfies the strict marker-packing
inequality by construction. -/
theorem packing_lt_block_of_good (X : FiniteMultiGraph)
    (P : BlockStructure X.vertex) (E : Finset X.vertex) (K : ℕ)
    {y : X.vertex} (hy : y ∉ badVertices X P E K) :
    packingCost X P E (P.block y) K < (P.block y).card := by
  exact Nat.lt_of_not_ge (by
    simpa [mem_badVertices_iff] using hy)

end KunBadBlocks
end NonsoficGroupsExist
