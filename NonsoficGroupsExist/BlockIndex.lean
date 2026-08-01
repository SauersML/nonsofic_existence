import NonsoficGroupsExist.BlockEnumeration

/-!
# Distinct blocks as a finite type

The component partition is presented by a block map on vertices.  Summing over
vertices would count a component once for each of its vertices, so the matching
argument instead uses the subtype of distinct blocks.  This file packages that
finite index type and its exact mass and disjointness identities.
-/

namespace NonsoficGroupsExist

variable {Y : FiniteModel}

/-- The finite type of distinct blocks of a block structure. -/
abbrev BlockIndex (P : BlockStructure Y) := {C // C ∈ P.blocksFinset}

namespace BlockIndex

variable (P : BlockStructure Y)

/-- The block indexed by `C`. -/
def block (C : BlockIndex P) : Finset Y := C.1

/-- A representative vertex of an indexed block. -/
noncomputable def representative (C : BlockIndex P) : Y :=
  Classical.choose ((P.mem_blocksFinset C.1).mp C.2)

@[simp] theorem block_representative (C : BlockIndex P) :
    P.block (representative P C) = C.block := by
  exact (Classical.choose_spec ((P.mem_blocksFinset C.1).mp C.2)).symm

theorem representative_mem (C : BlockIndex P) : representative P C ∈ C.block := by
  rw [← block_representative]
  exact P.self_mem _

theorem block_nonempty (C : BlockIndex P) : C.block.Nonempty :=
  ⟨representative P C, representative_mem P C⟩

theorem pairwise_disjoint :
    (↑(Finset.univ : Finset (BlockIndex P)) : Set (BlockIndex P)).PairwiseDisjoint
      (block P) := by
  intro C _ D _ hCD
  exact P.blocksFinset_pairwise_disjoint C.2 D.2 (Subtype.coe_injective.ne hCD)

/-- The indexed blocks have total mass exactly the model size. -/
theorem sum_card :
    ∑ C : BlockIndex P, C.block.card = Fintype.card Y := by
  classical
  rw [← P.sum_card_blocksFinset]
  exact (P.blocksFinset.sum_subtype (p := fun C : Finset Y ↦ C ∈ P.blocksFinset)
    (fun _ ↦ Iff.rfl) (fun C ↦ C.card)).symm

end BlockIndex
end NonsoficGroupsExist
