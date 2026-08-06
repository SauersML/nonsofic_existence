import NonsoficGroupsExist.Kun.KunPartition

/-!
# Boundary budget for Kun's recursive partition

At every nonterminal stage, `referenceSetAt` is the nearby set supplied by the
small-boundary theorem.  Its boundary is charged to the genuinely disjoint new
piece.  Consequently the sum of all reference boundaries is bounded by the
small boundary parameter times the number of vertices.
-/

namespace NonsoficGroupsExist
namespace KunPartitionBoundary

open FiniteMultiGraph
open KunPartition
open scoped symmDiff BigOperators

variable {X : FiniteMultiGraph}

/-- The small-boundary set used at stage `i`; terminal stages contribute the
empty set. -/
noncomputable def referenceSetAt
    (B : Finset X.vertex) (γ α : ℝ)
    (replace : ∀ T : Finset X.vertex, T.Nonempty → Disjoint T B →
      (X.boundaryCard T : ℝ) < γ * T.card →
      ∃ W : Finset X.vertex,
        ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3 ∧
        (X.boundaryCard W : ℝ) < α * T.card)
    (i : ℕ) : Finset X.vertex := by
  let A := (assignedAt B γ α replace i).1
  if hbad : (lowCutSubsets X (Finset.univ \ A) γ).Nonempty then
    exact chosenReplacement B A γ α (assignedAt B γ α replace i).2 hbad replace
  else
    exact ∅

theorem referenceSetAt_eq_of_lowCut
    (B : Finset X.vertex) (γ α : ℝ)
    (replace : ∀ T : Finset X.vertex, T.Nonempty → Disjoint T B →
      (X.boundaryCard T : ℝ) < γ * T.card →
      ∃ W : Finset X.vertex,
        ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3 ∧
        (X.boundaryCard W : ℝ) < α * T.card)
    (i : ℕ)
    (hbad : (lowCutSubsets X
      (Finset.univ \ (assignedAt B γ α replace i).1) γ).Nonempty) :
    referenceSetAt B γ α replace i =
      chosenReplacement B (assignedAt B γ α replace i).1 γ α
        (assignedAt B γ α replace i).2 hbad replace := by
  simp [referenceSetAt, hbad]

theorem nextPiece_eq_referenceSetAt_sdiff_of_lowCut
    (B : Finset X.vertex) (γ α : ℝ)
    (replace : ∀ T : Finset X.vertex, T.Nonempty → Disjoint T B →
      (X.boundaryCard T : ℝ) < γ * T.card →
      ∃ W : Finset X.vertex,
        ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3 ∧
        (X.boundaryCard W : ℝ) < α * T.card)
    (i : ℕ)
    (hbad : (lowCutSubsets X
      (Finset.univ \ (assignedAt B γ α replace i).1) γ).Nonempty) :
    nextPiece B (assignedAt B γ α replace i).1 γ α
        (assignedAt B γ α replace i).2 replace =
      referenceSetAt B γ α replace i \
        (assignedAt B γ α replace i).1 := by
  rw [referenceSetAt_eq_of_lowCut B γ α replace i hbad]
  simp [nextPiece, hbad]

theorem boundaryCard_referenceSetAt_le
    (B : Finset X.vertex) (γ α : ℝ) (hα : 0 ≤ α)
    (replace : ∀ T : Finset X.vertex, T.Nonempty → Disjoint T B →
      (X.boundaryCard T : ℝ) < γ * T.card →
      ∃ W : Finset X.vertex,
        ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3 ∧
        (X.boundaryCard W : ℝ) < α * T.card)
    (i : ℕ) :
    (X.boundaryCard (referenceSetAt B γ α replace i) : ℝ) ≤
      2 * α *
        (nextPiece B (assignedAt B γ α replace i).1 γ α
          (assignedAt B γ α replace i).2 replace).card := by
  classical
  let A := (assignedAt B γ α replace i).1
  simp only [referenceSetAt]
  split
  next hbad =>
    let T := minimalLowCutSubset (Finset.univ \ A) γ hbad
    let W := chosenReplacement B A γ α
      (assignedAt B γ α replace i).2 hbad replace
    have hT := minimalLowCutSubset_spec (Finset.univ \ A) γ hbad
    have hW := chosenReplacement_spec B A γ α
      (assignedAt B γ α replace i).2 hbad replace
    have hpiece := replacementPiece_expands A T W γ hT.1 hT.2.1
      hT.2.2.2 hW.1
    have hTcardReal : (T.card : ℝ) <
        2 * ((W \ A).card : ℝ) := by exact_mod_cast hpiece.2.2.1
    have hbound : (X.boundaryCard W : ℝ) <
        2 * α * ((W \ A).card : ℝ) := by
      calc
        (X.boundaryCard W : ℝ) < α * T.card := hW.2
        _ ≤ α * (2 * ((W \ A).card : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hTcardReal.le hα
        _ = 2 * α * ((W \ A).card : ℝ) := by ring
    simpa [A, W, nextPiece, hbad] using hbound.le
  next hbad =>
    have hnonneg : 0 ≤ 2 * α *
        ((nextPiece B (assignedAt B γ α replace i).1 γ α
          (assignedAt B γ α replace i).2 replace).card : ℝ) := by
      positivity
    simpa [FiniteMultiGraph.boundaryCard, FiniteMultiGraph.boundary] using hnonneg

/-- Total reference boundary is linear in the small-boundary parameter. -/
theorem sum_boundaryCard_referenceSetAt_le
    (B : Finset X.vertex) (γ α : ℝ) (hα : 0 ≤ α)
    (replace : ∀ T : Finset X.vertex, T.Nonempty → Disjoint T B →
      (X.boundaryCard T : ℝ) < γ * T.card →
      ∃ W : Finset X.vertex,
        ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3 ∧
        (X.boundaryCard W : ℝ) < α * T.card)
    (m : ℕ) :
    ∑ i ∈ Finset.range m,
        (X.boundaryCard (referenceSetAt B γ α replace i) : ℝ) ≤
      2 * α * Fintype.card X.vertex := by
  calc
    ∑ i ∈ Finset.range m,
        (X.boundaryCard (referenceSetAt B γ α replace i) : ℝ) ≤
      ∑ i ∈ Finset.range m,
        2 * α *
          (nextPiece B (assignedAt B γ α replace i).1 γ α
            (assignedAt B γ α replace i).2 replace).card := by
      exact Finset.sum_le_sum fun i _ ↦
        boundaryCard_referenceSetAt_le B γ α hα replace i
    _ = 2 * α *
        (∑ i ∈ Finset.range m,
          (nextPiece B (assignedAt B γ α replace i).1 γ α
            (assignedAt B γ α replace i).2 replace).card) := by
      push_cast
      rw [Finset.mul_sum]
    _ ≤ 2 * α * Fintype.card X.vertex := by
      exact mul_le_mul_of_nonneg_left
        (by exact_mod_cast sum_nextPiece_card_le_vertices B γ α replace m)
        (mul_nonneg (by norm_num) hα)

end KunPartitionBoundary
end NonsoficGroupsExist
