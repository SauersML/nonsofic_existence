import NonsoficGroupsExist.Refinement

/-!
# Occurrence-level edge edit accounting

An edge-edit witness bijects the kept occurrences of two multigraphs.  This
file proves the exact estimate used by component refinement: for any vertex
labelling, target crossing occurrences are bounded by inserted target
occurrences plus source crossing occurrences.
-/

namespace NonsoficGroupsExist
namespace EdgeEditWitness

variable {X Z : FiniteMultiGraph} {e : X.vertex ≃ Z.vertex}
variable (W : EdgeEditWitness X Z e)
variable {ι : Type*} [DecidableEq ι]

/-- Kept target occurrences whose endpoints have different labels. -/
def keptTargetCrossings (partZ : Z.vertex → ι) : Finset W.targetKept :=
  Finset.univ.filter fun b ↦ partZ (Z.first b.1) ≠ partZ (Z.second b.1)

/-- Source occurrences corresponding to the kept target crossings. -/
def correspondingSourceCrossings (partZ : Z.vertex → ι) : Finset X.edge :=
  (W.keptTargetCrossings partZ).map
    ⟨fun b ↦ (W.edgeEquiv.symm b).1, by
      intro a b hab
      apply W.edgeEquiv.symm.injective
      exact Subtype.ext hab⟩

theorem correspondingSourceCrossings_subset (partX : X.vertex → ι)
    (partZ : Z.vertex → ι) (hpart : ∀ x, partX x = partZ (e x)) :
    W.correspondingSourceCrossings partZ ⊆ X.crossingEdges partX := by
  intro a ha
  rw [correspondingSourceCrossings, Finset.mem_map] at ha
  obtain ⟨b, hb, rfl⟩ := ha
  apply (FiniteMultiGraph.mem_crossingEdges _ _ _).2
  have htarget : partZ (Z.first b.1) ≠ partZ (Z.second b.1) := by
    simpa [keptTargetCrossings] using hb
  have hp := W.preservesEndpoints (W.edgeEquiv.symm b)
  have hmatch : W.edgeEquiv (W.edgeEquiv.symm b) = b := W.edgeEquiv.apply_symm_apply b
  rcases hp with hp | hp
  · intro heq
    apply htarget
    calc
      partZ (Z.first b.1) = partZ (e (X.first (W.edgeEquiv.symm b).1)) :=
        congrArg partZ (by simpa [hmatch] using hp.1.symm)
      _ = partX (X.first (W.edgeEquiv.symm b).1) := (hpart _).symm
      _ = partX (X.second (W.edgeEquiv.symm b).1) := heq
      _ = partZ (e (X.second (W.edgeEquiv.symm b).1)) := hpart _
      _ = partZ (Z.second b.1) := congrArg partZ (by simpa [hmatch] using hp.2)
  · intro heq
    apply htarget
    calc
      partZ (Z.first b.1) = partZ (e (X.second (W.edgeEquiv.symm b).1)) :=
        congrArg partZ (by simpa [hmatch] using hp.2.symm)
      _ = partX (X.second (W.edgeEquiv.symm b).1) := (hpart _).symm
      _ = partX (X.first (W.edgeEquiv.symm b).1) := heq.symm
      _ = partZ (e (X.first (W.edgeEquiv.symm b).1)) := hpart _
      _ = partZ (Z.second b.1) := congrArg partZ (by simpa [hmatch] using hp.1)

theorem targetCrossings_subset (partZ : Z.vertex → ι) :
    Z.crossingEdges partZ ⊆ W.targetUnmatched ∪
      (W.keptTargetCrossings partZ).map ⟨Subtype.val, Subtype.val_injective⟩ := by
  intro b hb
  by_cases hkept : b ∈ W.targetKept
  · rw [Finset.mem_union]
    right
    rw [Finset.mem_map]
    let b' : W.targetKept := ⟨b, hkept⟩
    refine ⟨b', ?_, rfl⟩
    simpa [keptTargetCrossings] using
      (FiniteMultiGraph.mem_crossingEdges _ _ b).1 hb
  · rw [Finset.mem_union]
    left
    simp [targetUnmatched, hkept]

/-- Crossing occurrences after edge edits are bounded by inserted target
occurrences plus source crossing occurrences. -/
theorem targetCrossing_card_le (partX : X.vertex → ι)
    (partZ : Z.vertex → ι) (hpart : ∀ x, partX x = partZ (e x)) :
    (Z.crossingEdges partZ).card ≤
      W.targetUnmatched.card + (X.crossingEdges partX).card := by
  have hsub := Finset.card_le_card (W.targetCrossings_subset partZ)
  have hunion := Finset.card_union_le W.targetUnmatched
    ((W.keptTargetCrossings partZ).map ⟨Subtype.val, Subtype.val_injective⟩)
  have hcorresponding : (W.keptTargetCrossings partZ).card ≤
      (X.crossingEdges partX).card := by
    rw [← Finset.card_map]
    exact Finset.card_le_card
      (W.correspondingSourceCrossings_subset partX partZ hpart)
  rw [Finset.card_map] at hunion
  omega

theorem targetCrossing_card_le_unmatchedCount (partX : X.vertex → ι)
    (partZ : Z.vertex → ι) (hpart : ∀ x, partX x = partZ (e x)) :
    (Z.crossingEdges partZ).card ≤
      W.unmatchedCount + (X.crossingEdges partX).card := by
  have h := W.targetCrossing_card_le partX partZ hpart
  simp only [unmatchedCount]
  omega

end EdgeEditWitness
end NonsoficGroupsExist
