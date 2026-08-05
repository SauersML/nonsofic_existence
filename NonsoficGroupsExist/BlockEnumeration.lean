import NonsoficGroupsExist.Criterion

/-!
# Enumerating the blocks of a finite partition

`BlockStructure` presents a partition by a block map.  Weighted selection uses
the corresponding finset of distinct blocks, so this file proves the exact
covering, disjointness, and mass identities for that finset.
-/

namespace NonsoficGroupsExist
namespace BlockStructure

variable {Y : FiniteModel} (P : BlockStructure Y)

/-- The finset of distinct blocks of `P`. -/
noncomputable def blocksFinset : Finset (Finset Y) :=
  Finset.univ.image P.block

@[simp] theorem mem_blocksFinset (C : Finset Y) :
    C ∈ P.blocksFinset ↔ ∃ y, C = P.block y := by
  classical
  simp [blocksFinset, eq_comm]

theorem block_mem_blocksFinset (y : Y) : P.block y ∈ P.blocksFinset :=
  P.mem_blocksFinset (P.block y) |>.2 ⟨y, rfl⟩

theorem blocksFinset_nonempty (hY : Nonempty Y) : P.blocksFinset.Nonempty := by
  obtain ⟨y⟩ := hY
  exact ⟨P.block y, P.block_mem_blocksFinset y⟩

theorem blocksFinset_pairwise_disjoint :
    (P.blocksFinset : Set (Finset Y)).PairwiseDisjoint id := by
  intro C hC D hD hne
  obtain ⟨x, rfl⟩ := (P.mem_blocksFinset C).1 hC
  obtain ⟨y, rfl⟩ := (P.mem_blocksFinset D).1 hD
  exact P.block_disjoint hne

theorem blocksFinset_biUnion : P.blocksFinset.biUnion id = Finset.univ := by
  classical
  apply Finset.Subset.antisymm (Finset.subset_univ _)
  intro y _
  apply Finset.mem_biUnion.mpr
  exact ⟨P.block y, P.block_mem_blocksFinset y, P.self_mem y⟩

theorem sum_card_blocksFinset :
    ∑ C ∈ P.blocksFinset, C.card = Fintype.card Y := by
  classical
  rw [← Finset.card_univ, ← P.blocksFinset_biUnion]
  exact (Finset.card_biUnion fun C hC D hD hne ↦
    P.blocksFinset_pairwise_disjoint hC hD hne).symm

theorem sum_card_filter_blocksFinset_le :
    ∀ (p : Finset Y → Prop) [DecidablePred p],
      ∑ C ∈ P.blocksFinset.filter p, C.card ≤ Fintype.card Y := by
  intro p _
  rw [← P.sum_card_blocksFinset]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun _ _ _ ↦ Nat.zero_le _

end BlockStructure
end NonsoficGroupsExist
