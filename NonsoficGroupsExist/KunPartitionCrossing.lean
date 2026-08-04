import NonsoficGroupsExist.KunPartitionBoundary

/-!
# Charging edges crossing the recursive partition

An edge joining two nonexceptional blocks is charged to the small-boundary
reference set used when its earlier endpoint entered the partition.  Edges
touching the exceptional set are charged separately.
-/

namespace NonsoficGroupsExist
namespace KunPartitionCrossing

open FiniteMultiGraph
open KunPartition
open KunPartitionBoundary
open scoped symmDiff

variable {X : FiniteMultiGraph}

/-- Occurrences touching the exceptional set. -/
def exceptionalIncidentEdges (X : FiniteMultiGraph) (B : Finset X.vertex) :
    Finset X.edge :=
  Finset.univ.filter fun e ↦ X.first e ∈ B ∨ X.second e ∈ B

/-- If the first endpoint enters strictly before the second, the occurrence is
in the boundary of the reference set at that stage. -/
theorem edge_mem_boundary_reference_of_first_entry_lt
    (B : Finset X.vertex) (γ α : ℝ)
    (replace : ∀ T : Finset X.vertex, T.Nonempty → Disjoint T B →
      (X.boundaryCard T : ℝ) < γ * T.card →
      ∃ W : Finset X.vertex,
        ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3 ∧
        (X.boundaryCard W : ℝ) < α * T.card)
    (e : X.edge) (hfirst : X.first e ∉ B)
    (_hsecond : X.second e ∉ B)
    (hlt : entryTime B γ α replace (X.first e) <
      entryTime B γ α replace (X.second e)) :
    ∃ i ∈ Finset.range (Fintype.card X.vertex),
      e ∈ X.boundary (referenceSetAt B γ α replace i) := by
  have htimePos : 0 < entryTime B γ α replace (X.first e) := by
    have := (entryTime_eq_zero_iff B γ α replace (X.first e)).not.mpr hfirst
    omega
  obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt htimePos)
  let A := (assignedAt B γ α replace i).1
  let P := nextPiece B A γ α (assignedAt B γ α replace i).2 replace
  have hfirstP : X.first e ∈ P := by
    have hm := (entryTime_eq_succ_iff_mem_piece B γ α replace hfirst i).1 hi
    rw [assignedAt_sdiff_eq_nextPiece B γ α replace i] at hm
    exact hm
  have hsecondA : X.second e ∉ A := by
    rw [mem_assignedAt_iff_entryTime_le B γ α replace]
    omega
  have hsecondSucc : X.second e ∉
      (assignedAt B γ α replace (i + 1)).1 := by
    rw [mem_assignedAt_iff_entryTime_le B γ α replace]
    omega
  have hbad : (lowCutSubsets X (Finset.univ \ A) γ).Nonempty := by
    by_contra hnone
    have hsecondP : X.second e ∈ P := by
      unfold P nextPiece
      rw [dif_neg hnone]
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hsecondA⟩
    apply hsecondSucc
    rw [assignedAt_succ]
    exact Finset.mem_union_right _ hsecondP
  have hPeq : P = referenceSetAt B γ α replace i \ A := by
    exact nextPiece_eq_referenceSetAt_sdiff_of_lowCut B γ α replace i hbad
  have hfirstRef : X.first e ∈ referenceSetAt B γ α replace i := by
    rw [hPeq] at hfirstP
    exact (Finset.mem_sdiff.mp hfirstP).1
  have hsecondRef : X.second e ∉ referenceSetAt B γ α replace i := by
    intro href
    have hsecondP : X.second e ∈ P := by
      rw [hPeq]
      exact Finset.mem_sdiff.mpr ⟨href, hsecondA⟩
    apply hsecondSucc
    rw [assignedAt_succ]
    exact Finset.mem_union_right _ hsecondP
  have hiCard := entryTime_le_card B γ α replace (X.first e)
  refine ⟨i, Finset.mem_range.mpr (by omega), ?_⟩
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, Or.inl ⟨hfirstRef, hsecondRef⟩⟩

/-- The symmetric orientation of the preceding charging lemma. -/
theorem edge_mem_boundary_reference_of_second_entry_lt
    (B : Finset X.vertex) (γ α : ℝ)
    (replace : ∀ T : Finset X.vertex, T.Nonempty → Disjoint T B →
      (X.boundaryCard T : ℝ) < γ * T.card →
      ∃ W : Finset X.vertex,
        ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3 ∧
        (X.boundaryCard W : ℝ) < α * T.card)
    (e : X.edge) (_hfirst : X.first e ∉ B)
    (hsecond : X.second e ∉ B)
    (hlt : entryTime B γ α replace (X.second e) <
      entryTime B γ α replace (X.first e)) :
    ∃ i ∈ Finset.range (Fintype.card X.vertex),
      e ∈ X.boundary (referenceSetAt B γ α replace i) := by
  have htimePos : 0 < entryTime B γ α replace (X.second e) := by
    have := (entryTime_eq_zero_iff B γ α replace (X.second e)).not.mpr hsecond
    omega
  obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt htimePos)
  let A := (assignedAt B γ α replace i).1
  let P := nextPiece B A γ α (assignedAt B γ α replace i).2 replace
  have hsecondP : X.second e ∈ P := by
    have hm := (entryTime_eq_succ_iff_mem_piece B γ α replace hsecond i).1 hi
    rw [assignedAt_sdiff_eq_nextPiece B γ α replace i] at hm
    exact hm
  have hfirstA : X.first e ∉ A := by
    rw [mem_assignedAt_iff_entryTime_le B γ α replace]
    omega
  have hfirstSucc : X.first e ∉
      (assignedAt B γ α replace (i + 1)).1 := by
    rw [mem_assignedAt_iff_entryTime_le B γ α replace]
    omega
  have hbad : (lowCutSubsets X (Finset.univ \ A) γ).Nonempty := by
    by_contra hnone
    have hfirstP : X.first e ∈ P := by
      unfold P nextPiece
      rw [dif_neg hnone]
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hfirstA⟩
    apply hfirstSucc
    rw [assignedAt_succ]
    exact Finset.mem_union_right _ hfirstP
  have hPeq : P = referenceSetAt B γ α replace i \ A := by
    exact nextPiece_eq_referenceSetAt_sdiff_of_lowCut B γ α replace i hbad
  have hsecondRef : X.second e ∈ referenceSetAt B γ α replace i := by
    rw [hPeq] at hsecondP
    exact (Finset.mem_sdiff.mp hsecondP).1
  have hfirstRef : X.first e ∉ referenceSetAt B γ α replace i := by
    intro href
    have hfirstP : X.first e ∈ P := by
      rw [hPeq]
      exact Finset.mem_sdiff.mpr ⟨href, hfirstA⟩
    apply hfirstSucc
    rw [assignedAt_succ]
    exact Finset.mem_union_right _ hfirstP
  have hiCard := entryTime_le_card B γ α replace (X.second e)
  refine ⟨i, Finset.mem_range.mpr (by omega), ?_⟩
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, Or.inr ⟨hsecondRef, hfirstRef⟩⟩

/-- All partition-crossing occurrences are charged either to the exceptional
set or to one of the small reference boundaries. -/
theorem crossingEdges_subset_charged
    (B : Finset X.vertex) (γ α : ℝ)
    (replace : ∀ T : Finset X.vertex, T.Nonempty → Disjoint T B →
      (X.boundaryCard T : ℝ) < γ * T.card →
      ∃ W : Finset X.vertex,
        ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3 ∧
        (X.boundaryCard W : ℝ) < α * T.card) :
    X.crossingEdges (blockStructure B γ α replace).block ⊆
      exceptionalIncidentEdges X B ∪
        (Finset.range (Fintype.card X.vertex)).biUnion
          (fun i ↦ X.boundary (referenceSetAt B γ α replace i)) := by
  classical
  intro e he
  have hblocks :
      (blockStructure B γ α replace).block (X.first e) ≠
        (blockStructure B γ α replace).block (X.second e) := by
    exact (FiniteMultiGraph.mem_crossingEdges _ _ _).1 he
  by_cases hfirst : X.first e ∈ B
  · apply Finset.mem_union_left
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hfirst⟩
  by_cases hsecond : X.second e ∈ B
  · apply Finset.mem_union_left
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr hsecond⟩
  apply Finset.mem_union_right
  have hlabels : partitionLabel B γ α replace (X.first e) ≠
      partitionLabel B γ α replace (X.second e) := by
    intro hlabel
    exact hblocks ((blockStructure_block_eq_iff_label_eq B γ α replace
      (X.first e) (X.second e)).2 hlabel)
  have htimes : entryTime B γ α replace (X.first e) ≠
      entryTime B γ α replace (X.second e) := by
    intro htime
    apply hlabels
    simp [partitionLabel, hfirst, hsecond, htime]
  rcases lt_or_gt_of_ne htimes with hlt | hlt
  · obtain ⟨i, hi, hie⟩ := edge_mem_boundary_reference_of_first_entry_lt
      B γ α replace e hfirst hsecond hlt
    exact Finset.mem_biUnion.mpr ⟨i, hi, hie⟩
  · obtain ⟨i, hi, hie⟩ := edge_mem_boundary_reference_of_second_entry_lt
      B γ α replace e hfirst hsecond hlt
    exact Finset.mem_biUnion.mpr ⟨i, hi, hie⟩

/-- Cardinal form of the charging argument. -/
theorem card_crossingEdges_le
    (B : Finset X.vertex) (γ α : ℝ)
    (replace : ∀ T : Finset X.vertex, T.Nonempty → Disjoint T B →
      (X.boundaryCard T : ℝ) < γ * T.card →
      ∃ W : Finset X.vertex,
        ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3 ∧
        (X.boundaryCard W : ℝ) < α * T.card) :
    (X.crossingEdges (blockStructure B γ α replace).block).card ≤
      (exceptionalIncidentEdges X B).card +
        ∑ i ∈ Finset.range (Fintype.card X.vertex),
          X.boundaryCard (referenceSetAt B γ α replace i) := by
  calc
    (X.crossingEdges (blockStructure B γ α replace).block).card ≤
        (exceptionalIncidentEdges X B ∪
          (Finset.range (Fintype.card X.vertex)).biUnion
            (fun i ↦ X.boundary (referenceSetAt B γ α replace i))).card :=
      Finset.card_le_card (crossingEdges_subset_charged B γ α replace)
    _ ≤ (exceptionalIncidentEdges X B).card +
        ((Finset.range (Fintype.card X.vertex)).biUnion
          (fun i ↦ X.boundary (referenceSetAt B γ α replace i))).card :=
      Finset.card_union_le _ _
    _ ≤ (exceptionalIncidentEdges X B).card +
        ∑ i ∈ Finset.range (Fintype.card X.vertex),
          X.boundaryCard (referenceSetAt B γ α replace i) := by
      exact Nat.add_le_add_left Finset.card_biUnion_le _

end KunPartitionCrossing
end NonsoficGroupsExist
