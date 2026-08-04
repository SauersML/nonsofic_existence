import Mathlib.Algebra.Order.Archimedean.Real.Basic
import NonsoficGroupsExist.KunDiagonalPartition
import NonsoficGroupsExist.KunLocalNeighborhood
import NonsoficGroupsExist.KunSelectiveRepairExpansion
import NonsoficGroupsExist.KunRefinedInvariance

/-!
# Constructing Kun's expander decomposition

This module assembles the proved finite partition, local-neighborhood,
marker-packing, selective graph-repair, and boundary-charging results.  The
output is an actual `ExpanderDecomposition` on a cofinal reindexing of any
sofic approximation of an infinite finitely generated property-(T) group.
-/

namespace NonsoficGroupsExist
namespace KunDecomposition

open KunDiagonalPartition
open KunLocalNeighborhood
open KunMarkerSelection
open KunRepairGraph
open KunBadBlocks
open KunSelectiveRepairGraph
open KunSelectiveRepairExpansion
open KunRefinedInvariance
open KunUniformMovement
open KunUniformRounding

variable {G : Type} [Group G] [Infinite G]

/-- A positive real cut constant admits a finite neighborhood multiplicity
large enough for the repair charging argument. -/
theorem exists_neighborhoodMultiplicity {γ : ℝ} (hγ : 0 < γ) :
    ∃ q : ℕ, 2 ≤ γ * q := by
  obtain ⟨q, hq⟩ := exists_nat_gt (2 / γ)
  refine ⟨q, ?_⟩
  have hmul : γ * (2 / γ) < γ * (q : ℝ) :=
    mul_lt_mul_of_pos_left hq hγ
  have hcancel : γ * (2 / γ) = 2 := by
    field_simp
  rw [hcancel] at hmul
  exact hmul.le

/-- Kun's expander decomposition, with every repair datum constructed, on a
cofinal reindexing of the given sofic approximation. -/
theorem exists_reindexed_expanderDecomposition
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{0, 0} G Q ε)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S) (hεone : ε ≤ 1)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (A : SoficApproximation G) :
    ∃ (φ : ℕ → ℕ) (hφ : ∀ n, n ≤ φ n),
      Nonempty (ExpanderDecomposition (A.reindex φ hφ) S) := by
  classical
  obtain ⟨φ, hφ, P, hcrossing, hglobal⟩ :=
    exists_reindexed_partition hQ S hQS hone hεone A
  let A' := A.reindex φ hφ
  let γ := uniformInputCutThreshold S (movementConstant S ε + 1)
  have hS : S.Nonempty := ⟨1, hone⟩
  have hγ : 0 < γ := uniformInputCutThreshold_pos S hS _
  obtain ⟨q, hq⟩ := exists_neighborhoodMultiplicity hγ
  let r := witnessRadius S hsymm hgen q
  let K := (S.card + 1) ^ r + (S.card + 1) ^ (2 * r)
  let X : ℕ → FiniteMultiGraph := fun n ↦
    generatorGraph (A'.model n) S (A'.map n)
  let E : ∀ n, Finset (A'.model n) := fun n ↦
    A'.localNeighborhoodBad S hsymm hgen q n
  let B : ∀ n, Finset (A'.model n) := fun n ↦
    badVertices (X n) (P n) (E n) K
  have hmarkerExists (n : ℕ) :
      ∃ marker : GoodCrossingStub (X n) (P n) (B n) → A'.model n,
        (∀ s, marker s ≠ stubEndpoint (X n) (P n) s.1) ∧
        (∀ s, marker s ∉ E n) ∧
        (∀ s, marker s ∈ (P n).block (stubEndpoint (X n) (P n) s.1)) ∧
        (∀ s, forwardNeighborhood (A'.model n) (A'.map n) S r {marker s} ⊆
          (P n).block (stubEndpoint (X n) (P n) s.1)) ∧
        ∀ s t, s ≠ t →
          Disjoint
            (forwardNeighborhood (A'.model n) (A'.map n) S r {marker s})
            (forwardNeighborhood (A'.model n) (A'.map n) S r {marker t}) := by
    apply exists_good_marker_assignment (A'.model n) (A'.map n) S r
      (P n) (E n) (B n)
    · intro x y hy
      exact mem_badVertices_iff_of_mem_block (X n) (P n) (E n) K hy
    · intro y hy
      simpa [X, B, K, packingCost] using
        (packing_lt_block_of_good (X n) (P n) (E n) K hy)
  let marker : ∀ n, GoodCrossingStub (X n) (P n) (B n) → A'.model n :=
    fun n ↦ Classical.choose (hmarkerExists n)
  have marker_spec (n : ℕ) := Classical.choose_spec (hmarkerExists n)
  let marker_ne : ∀ n (s : GoodCrossingStub (X n) (P n) (B n)),
      marker n s ≠ stubEndpoint (X n) (P n) s.1 :=
    fun n ↦ (marker_spec n).1
  let Z : ℕ → FiniteMultiGraph := fun n ↦
    graph (X n) (P n) (B n) (marker n) (marker_ne n)
  have hE : Negligible (fun n ↦ (Fintype.card (A'.model n) : ℝ))
      (fun n ↦ ((E n).card : ℝ)) := by
    simpa [A', E] using
      (A'.localNeighborhoodBad_negligible S hsymm hgen q)
  have hB : Negligible (fun n ↦ (Fintype.card (A'.model n) : ℝ))
      (fun n ↦ ((B n).card : ℝ)) := by
    have hmajor := Negligible.add hE
      (Negligible.const_mul (2 * (K : ℝ)) hcrossing)
    apply Negligible.mono_nonneg
      (fun _ ↦ by positivity) (fun _ ↦ by positivity) _ hmajor
    intro n
    have hcard := card_badVertices_le (X n) (P n) (E n) K
    rw [card_crossingStub] at hcard
    exact_mod_cast hcard
  have hbadSource : Negligible
      (fun n ↦ (Fintype.card (A'.model n) : ℝ))
      (fun n ↦ ((badSourceEdges (X n) (B n)).card : ℝ)) := by
    have hmajor := Negligible.const_mul (S.card : ℝ) hB
    apply Negligible.mono_nonneg
      (fun _ ↦ by positivity) (fun _ ↦ by positivity) _ hmajor
    intro n
    exact_mod_cast card_badSourceEdges_generatorGraph_le
      (A'.model n) (A'.map n) S (B n)
  have hunmatched : Negligible
      (fun n ↦ (Fintype.card (A'.model n) : ℝ))
      (fun n ↦ ((editWitness (X n) (P n) (B n)
        (marker n) (marker_ne n)).unmatchedCount : ℝ)) := by
    have hmajor := Negligible.add
      (Negligible.const_mul 3 hcrossing) hbadSource
    apply Negligible.mono_nonneg
      (fun _ ↦ by positivity) (fun _ ↦ by positivity) _ hmajor
    intro n
    exact_mod_cast unmatchedCount_le (X n) (P n) (B n)
      (marker n) (marker_ne n)
  have hedit : Negligible
      (fun n ↦ (Fintype.card (A'.model n) : ℝ))
      (fun n ↦ ((X n).editDistance (Z n) (Equiv.refl _) : ℕ)) := by
    have hmajor := Negligible.const_mul 2 hunmatched
    apply Negligible.mono_nonneg
      (fun _ ↦ by positivity) (fun _ ↦ by positivity) _ hmajor
    intro n
    exact_mod_cast
      (editWitness (X n) (P n) (B n) (marker n) (marker_ne n)).editDistance_le_two_mul_unmatchedCount
  refine ⟨φ, hφ, ⟨{
    blocks := fun n ↦ singletonizeBadBlocks (X n) (P n) (E n) K
    cheeger := γ / 4
    cheeger_pos := div_pos hγ (by norm_num)
    graph := Z
    vertexEquiv := fun n ↦ Equiv.refl (A'.model n)
    edit_negligible := by
      simpa [A', X, Z] using hedit
    editWitness := fun n ↦ by
      simpa [A', X, Z] using
        (editWitness (X n) (P n) (B n) (marker n) (marker_ne n))
    unmatched_negligible := by
      simpa [A', X, Z] using hunmatched
    edge_inside := by
      intro n e
      simpa [A', X, Z] using
        edge_inside_refined (X n) (P n) (E n) K
          (marker n) (marker_ne n) (marker_spec n).2.2.1 e
    component_expands := by
      intro n y
      apply refined_component_expands (A'.model n) (A'.map n) S
        (P n) (E n) K (marker n) (marker_ne n) (marker_spec n).2.2.1
        r q
      · intro s
        apply A'.card_forwardNeighborhood_ge S hsymm hgen q n (marker n s)
        exact (marker_spec n).2.1 s
      · exact (marker_spec n).2.2.2.1
      · exact (marker_spec n).2.2.2.2
      · exact hγ
      · exact hq
      · exact hglobal n
    almost_invariant := by
      intro t ht
      have hold : Negligible
          (fun n ↦ (Fintype.card (A'.model n) : ℝ))
          (fun n ↦ ((wordCrossing (P n) (A'.map n t)).card : ℝ)) := by
        apply Negligible.mono_nonneg
          (fun _ ↦ by positivity) (fun _ ↦ by positivity) _ hcrossing
        intro n
        exact_mod_cast card_wordCrossing_le_crossingEdges
          (A'.model n) (A'.map n) S (P n) ht
      have hmajor := Negligible.add hold (Negligible.const_mul 2 hB)
      apply Negligible.mono_nonneg
        (fun _ ↦ by positivity) (fun _ ↦ by positivity) _ hmajor
      intro n
      exact_mod_cast card_wordCrossing_singletonizeBadBlocks_le
        (X n) (P n) (E n) K (A'.map n t)
  }⟩⟩

end KunDecomposition
end NonsoficGroupsExist
