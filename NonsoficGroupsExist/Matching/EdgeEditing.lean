import NonsoficGroupsExist.Matching.Refinement
import Mathlib.Algebra.Order.BigOperators.Group.Finset

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

/-- Edge edits change the variation of a function valued in `[0,1]` by at
most the number of unmatched edge occurrences. -/
theorem targetVariation_le_unmatchedCount (fX : X.vertex → ℝ)
    (fZ : Z.vertex → ℝ) (hfun : ∀ x, fX x = fZ (e x))
    (hZnonneg : ∀ z, 0 ≤ fZ z) (hZone : ∀ z, fZ z ≤ 1) :
    Z.edgeVariation fZ ≤ X.edgeVariation fX + W.unmatchedCount := by
  classical
  let weightX : X.edge → ℝ := fun a ↦ |fX (X.first a) - fX (X.second a)|
  let weightZ : Z.edge → ℝ := fun b ↦ |fZ (Z.first b) - fZ (Z.second b)|
  have hkept : ∑ b ∈ W.targetKept, weightZ b =
      ∑ a ∈ W.sourceKept, weightX a := by
    have hequiv : (∑ a : W.sourceKept, weightX a.1) =
        ∑ b : W.targetKept, weightZ b.1 := by
      apply Fintype.sum_equiv W.edgeEquiv
      intro a
      rcases W.preservesEndpoints a with h | h
      · dsimp only [weightX, weightZ]
        rw [hfun (X.first a.1), hfun (X.second a.1), h.1, h.2]
      · dsimp only [weightX, weightZ]
        rw [hfun (X.first a.1), hfun (X.second a.1), h.1, h.2,
          abs_sub_comm]
    calc
      ∑ b ∈ W.targetKept, weightZ b = ∑ b : W.targetKept, weightZ b.1 := by
        simpa using (Finset.sum_attach W.targetKept weightZ).symm
      _ = ∑ a : W.sourceKept, weightX a.1 := hequiv.symm
      _ = ∑ a ∈ W.sourceKept, weightX a := by
        simpa using Finset.sum_attach W.sourceKept weightX
  have hunmatched : ∑ b ∈ W.targetUnmatched, weightZ b ≤ W.targetUnmatched.card := by
    calc
      ∑ b ∈ W.targetUnmatched, weightZ b ≤
          ∑ _b ∈ W.targetUnmatched, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro b _
        dsimp only [weightZ]
        rw [abs_sub_le_iff]
        constructor <;> linarith [hZnonneg (Z.first b), hZnonneg (Z.second b),
          hZone (Z.first b), hZone (Z.second b)]
      _ = W.targetUnmatched.card := by simp
  have hsource : ∑ a ∈ W.sourceKept, weightX a ≤ X.edgeVariation fX := by
    unfold FiniteMultiGraph.edgeVariation
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ ↦ abs_nonneg _)
  have hsplit : ∑ b ∈ W.targetUnmatched, weightZ b +
      ∑ b ∈ W.targetKept, weightZ b = Z.edgeVariation fZ := by
    unfold EdgeEditWitness.targetUnmatched FiniteMultiGraph.edgeVariation
    exact Finset.sum_sdiff (Finset.subset_univ W.targetKept)
  unfold EdgeEditWitness.unmatchedCount
  rw [← hsplit, hkept]
  push_cast
  have hsourceUnmatched : (0 : ℝ) ≤ W.sourceUnmatched.card := by positivity
  linarith

end EdgeEditWitness
end NonsoficGroupsExist
