import NonsoficGroupsExist.EdgeWitnessDistance

/-!
# Restricting an occurrence edit witness

An edit witness restricts to corresponding induced subgraphs.  The restricted
unmatched count is bounded by the number of globally unmatched occurrences
incident to the chosen vertex sets.
-/

namespace NonsoficGroupsExist

namespace EdgeEditWitness

variable {X Z : FiniteMultiGraph} {e : X.vertex ≃ Z.vertex}

noncomputable def inducedVertexEquiv (U : Finset X.vertex) (V : Finset Z.vertex)
    (hUV : ∀ x, x ∈ U ↔ e x ∈ V) : (X.induce U).vertex ≃ (Z.induce V).vertex where
  toFun x := ⟨e x.1, (hUV x.1).mp x.2⟩
  invFun z := ⟨e.symm z.1, (hUV (e.symm z.1)).mpr (by simpa using z.2)⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv z := by apply Subtype.ext; simp

variable (W : EdgeEditWitness X Z e)
variable (U : Finset X.vertex) (V : Finset Z.vertex)
variable (hUV : ∀ x, x ∈ U ↔ e x ∈ V)

private def inducedSourceKept : Finset (X.induce U).edge :=
  Finset.univ.filter fun a ↦ a.1 ∈ W.sourceKept

private def inducedTargetKept : Finset (Z.induce V).edge :=
  Finset.univ.filter fun b ↦ b.1 ∈ W.targetKept

private noncomputable def inducedEdgeEquiv :
    W.inducedSourceKept U ≃ W.inducedTargetKept V := by
  let forward : W.inducedSourceKept U → W.inducedTargetKept V := fun a ↦ by
    let a' : W.sourceKept := ⟨a.1.1, (Finset.mem_filter.mp a.2).2⟩
    let b' : W.targetKept := W.edgeEquiv a'
    have hp := W.preservesEndpoints a'
    have hfirst : Z.first b'.1 ∈ V := by
      rcases hp with hp | hp
      · rw [← hp.1]
        exact (hUV (X.first a'.1)).mp a.1.2.1
      · rw [← hp.2]
        exact (hUV (X.second a'.1)).mp a.1.2.2
    have hsecond : Z.second b'.1 ∈ V := by
      rcases hp with hp | hp
      · rw [← hp.2]
        exact (hUV (X.second a'.1)).mp a.1.2.2
      · rw [← hp.1]
        exact (hUV (X.first a'.1)).mp a.1.2.1
    exact ⟨⟨b'.1, hfirst, hsecond⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, b'.2⟩⟩
  let backward : W.inducedTargetKept V → W.inducedSourceKept U := fun b ↦ by
    let b' : W.targetKept := ⟨b.1.1, (Finset.mem_filter.mp b.2).2⟩
    let a' : W.sourceKept := W.edgeEquiv.symm b'
    have hp := W.preservesEndpoints a'
    have heq : W.edgeEquiv a' = b' := W.edgeEquiv.apply_symm_apply b'
    have hfirst : X.first a'.1 ∈ U := by
      rcases hp with hp | hp
      · apply (hUV (X.first a'.1)).mpr
        rw [hp.1, heq]
        exact b.1.2.1
      · apply (hUV (X.first a'.1)).mpr
        rw [hp.1, heq]
        exact b.1.2.2
    have hsecond : X.second a'.1 ∈ U := by
      rcases hp with hp | hp
      · apply (hUV (X.second a'.1)).mpr
        rw [hp.2, heq]
        exact b.1.2.2
      · apply (hUV (X.second a'.1)).mpr
        rw [hp.2, heq]
        exact b.1.2.1
    exact ⟨⟨a'.1, hfirst, hsecond⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, a'.2⟩⟩
  exact
    { toFun := forward
      invFun := backward
      left_inv := by
        intro a
        apply Subtype.ext
        apply Subtype.ext
        exact W.edgeEquiv.symm_apply_apply _
      right_inv := by
        intro b
        apply Subtype.ext
        apply Subtype.ext
        exact W.edgeEquiv.apply_symm_apply _ }

/-- Restriction of an occurrence witness to corresponding induced subgraphs. -/
noncomputable def induce : EdgeEditWitness (X.induce U) (Z.induce V)
    (inducedVertexEquiv U V hUV) where
  sourceKept := W.inducedSourceKept U
  targetKept := W.inducedTargetKept V
  edgeEquiv := W.inducedEdgeEquiv U V hUV
  preservesEndpoints := by
    intro a
    let a' : W.sourceKept := ⟨a.1.1.1, (Finset.mem_filter.mp a.2).2⟩
    have hp := W.preservesEndpoints a'
    rcases hp with hp | hp
    · exact Or.inl ⟨Subtype.ext hp.1, Subtype.ext hp.2⟩
    · exact Or.inr ⟨Subtype.ext hp.1, Subtype.ext hp.2⟩

theorem induce_sourceUnmatched_card_le :
    ((W.induce U V hUV).sourceUnmatched).card ≤ W.sourceUnmatched.card := by
  apply Finset.card_le_card_of_injOn (fun a ↦ a.1)
  · intro a ha
    have ha' : a ∉ W.inducedSourceKept U :=
      (Finset.mem_sdiff.mp ha).2
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
      intro hkept
      apply ha'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkept⟩⟩
  · intro a _ b _ hab
      exact Subtype.ext hab

theorem induce_sourceUnmatched_card_le_filter :
    ((W.induce U V hUV).sourceUnmatched).card ≤
      (W.sourceUnmatched.filter fun a ↦ X.first a ∈ U).card := by
  apply Finset.card_le_card_of_injOn (fun a ↦ a.1)
  · intro a ha
    have ha' : a ∉ W.inducedSourceKept U := (Finset.mem_sdiff.mp ha).2
    refine Finset.mem_filter.mpr ⟨?_, a.2.1⟩
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
      intro hkept
      apply ha'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkept⟩⟩
  · intro a _ b _ hab
    exact Subtype.ext hab

theorem induce_targetUnmatched_card_le :
    ((W.induce U V hUV).targetUnmatched).card ≤ W.targetUnmatched.card := by
  apply Finset.card_le_card_of_injOn (fun b ↦ b.1)
  · intro b hb
    have hb' : b ∉ W.inducedTargetKept V :=
      (Finset.mem_sdiff.mp hb).2
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
      intro hkept
      apply hb'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkept⟩⟩
  · intro a _ b _ hab
      exact Subtype.ext hab

theorem induce_targetUnmatched_card_le_filter :
    ((W.induce U V hUV).targetUnmatched).card ≤
      (W.targetUnmatched.filter fun b ↦ Z.first b ∈ V).card := by
  apply Finset.card_le_card_of_injOn (fun b ↦ b.1)
  · intro b hb
    have hb' : b ∉ W.inducedTargetKept V := (Finset.mem_sdiff.mp hb).2
    refine Finset.mem_filter.mpr ⟨?_, b.2.1⟩
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
      intro hkept
      apply hb'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkept⟩⟩
  · intro a _ b _ hab
    exact Subtype.ext hab

theorem induce_unmatchedCount_le :
    (W.induce U V hUV).unmatchedCount ≤ W.unmatchedCount := by
  unfold unmatchedCount
  exact Nat.add_le_add (W.induce_sourceUnmatched_card_le U V hUV)
    (W.induce_targetUnmatched_card_le U V hUV)

theorem induce_unmatchedCount_le_filters :
    (W.induce U V hUV).unmatchedCount ≤
      (W.sourceUnmatched.filter fun a ↦ X.first a ∈ U).card +
        (W.targetUnmatched.filter fun b ↦ Z.first b ∈ V).card := by
  unfold unmatchedCount
  exact Nat.add_le_add (W.induce_sourceUnmatched_card_le_filter U V hUV)
    (W.induce_targetUnmatched_card_le_filter U V hUV)

end EdgeEditWitness
end NonsoficGroupsExist
