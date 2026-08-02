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

/-- Summation over the distinct blocks is summation over all vertices exactly
once. -/
theorem sum_sum (f : Y → ℝ) :
    ∑ C : BlockIndex P, ∑ y : C.block, f (y : Y) = ∑ y, f y := by
  classical
  calc
    ∑ C : BlockIndex P, ∑ y : C.block, f (y : Y) =
        ∑ C : BlockIndex P, ∑ y ∈ C.block, f y := by
      apply Finset.sum_congr rfl
      intro C _
      simpa using (Finset.sum_attach C.block fun y ↦ f y)
    _ =
        ∑ C ∈ P.blocksFinset, ∑ y ∈ C, f y := by
      exact (P.blocksFinset.sum_subtype (p := fun C : Finset Y ↦ C ∈ P.blocksFinset)
        (fun _ ↦ Iff.rfl) (fun C ↦ ∑ y ∈ C, f y)).symm
    _ = ∑ y ∈ P.blocksFinset.biUnion id, f y := by
      exact (Finset.sum_biUnion P.blocksFinset_pairwise_disjoint).symm
    _ = ∑ y, f y := by rw [P.blocksFinset_biUnion]

/-- Cardinalities of vertex filters may be summed componentwise. -/
theorem sum_card_filter (p : Y → Prop) [DecidablePred p] :
    ∑ C : BlockIndex P,
        ((Finset.univ.filter fun x : C.block ↦ p (x : Y)).card : ℝ) =
      ((Finset.univ.filter p).card : ℝ) := by
  let f : Y → ℝ := fun y ↦ if p y then 1 else 0
  have hpartition :
      ∑ C : BlockIndex P, ∑ x : C.block, f (x : Y) = ∑ y : Y, f y :=
    sum_sum P f
  calc
    _ = ∑ C : BlockIndex P, ∑ x : C.block, f (x : Y) := by
      apply Finset.sum_congr rfl
      intro C _
      simp only [f, Finset.sum_boole]
    _ = ∑ y : Y, f y := hpartition
    _ = ((Finset.univ.filter p).card : ℝ) := by simp [f]

end BlockIndex
end NonsoficGroupsExist
