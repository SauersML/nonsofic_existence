import Mathlib.Algebra.Order.Archimedean.Real.Basic
import NonsoficGroupsExist.KunDiagonalPartition
import NonsoficGroupsExist.KunLocalNeighborhood
import NonsoficGroupsExist.KunSelectiveRepairExpansion
import NonsoficGroupsExist.KunRefinedInvariance

/-!
# Constructing Kun's expander decomposition

This module assembles the proved finite partition, local-neighborhood,
marker-packing, selective graph-repair, and boundary-charging results.  The
output is an actual `ExpanderDecomposition` on every model of any sofic
approximation of an infinite finitely generated property-(T) group.
-/

namespace NonsoficGroupsExist
namespace KunDecomposition

open KunDiagonalPartition
open KunLocalNeighborhood
open KunLocalNeighborhood.SoficApproximation
open KunSupport
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

/-- Kun's expander decomposition, with every repair datum constructed, on the
given sofic approximation itself. -/
theorem exists_expanderDecomposition
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{0, 0} G Q ε)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S) (hεone : ε ≤ 1)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (A : SoficApproximation G) :
    Nonempty (ExpanderDecomposition A S) := by
  classical
  obtain ⟨P, hcrossing, hglobal⟩ :=
    exists_partition hQ S hQS hone hεone A
  let γ := uniformInputCutThreshold S (movementConstant S ε + 1)
  have hS : S.Nonempty := ⟨1, hone⟩
  have hγ : 0 < γ := uniformInputCutThreshold_pos S hS _
  obtain ⟨q, hq⟩ := exists_neighborhoodMultiplicity hγ
  let r := witnessRadius S hsymm hgen q
  let K := (S.card + 1) ^ r + (S.card + 1) ^ (2 * r)
  let X : ℕ → FiniteMultiGraph := fun n ↦
    generatorGraph (A.model n) S (A.map n)
  let E : ∀ n, Finset (A.model n) := fun n ↦
    KunLocalNeighborhood.SoficApproximation.localNeighborhoodBad
      A S hsymm hgen q n
  let B : ∀ n, Finset (A.model n) := fun n ↦
    badVertices (X n) (P n) (E n) K
  have hmarkerExists (n : ℕ) :
      ∃ marker : GoodCrossingStub (X n) (P n) (B n) → A.model n,
        (∀ s, marker s ≠ stubEndpoint (X n) (P n) s.1) ∧
        (∀ s, marker s ∉ E n) ∧
        (∀ s, marker s ∈ (P n).block (stubEndpoint (X n) (P n) s.1)) ∧
        (∀ s, forwardNeighborhood (A.model n) (A.map n) S r {marker s} ⊆
          (P n).block (stubEndpoint (X n) (P n) s.1)) ∧
        ∀ s t, s ≠ t →
          Disjoint
            (forwardNeighborhood (A.model n) (A.map n) S r {marker s})
            (forwardNeighborhood (A.model n) (A.map n) S r {marker t}) := by
    apply exists_good_marker_assignment (A.model n) (A.map n) S r
      (P n) (E n) (B n)
    · intro x y hy
      exact mem_badVertices_iff_of_mem_block (X n) (P n) (E n) K hy
    · intro y hy
      simpa [X, B, K, packingCost] using
        (packing_lt_block_of_good (X n) (P n) (E n) K hy)
  let marker : ∀ n, GoodCrossingStub (X n) (P n) (B n) → A.model n :=
    fun n ↦ Classical.choose (hmarkerExists n)
  have marker_spec (n : ℕ) := Classical.choose_spec (hmarkerExists n)
  let marker_ne : ∀ n (s : GoodCrossingStub (X n) (P n) (B n)),
      marker n s ≠ stubEndpoint (X n) (P n) s.1 :=
    fun n ↦ (marker_spec n).1
  let Z : ℕ → FiniteMultiGraph := fun n ↦
    graph (X n) (P n) (B n) (marker n) (marker_ne n)
  have hE : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ))
      (fun n ↦ ((E n).card : ℝ)) := by
    simpa [E] using
      (KunLocalNeighborhood.SoficApproximation.localNeighborhoodBad_negligible
        A S hsymm hgen q)
  have hB : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ))
      (fun n ↦ ((B n).card : ℝ)) := by
    have hmajor := Negligible.add hE
      (Negligible.const_mul (2 * (K : ℝ)) hcrossing)
    apply Negligible.mono_nonneg
      (fun _ ↦ by positivity) (fun _ ↦ by positivity) _ hmajor
    intro n
    have hcard := card_badVertices_le (X n) (P n) (E n) K
    rw [card_crossingStub] at hcard
    have hcard' : (B n).card ≤ (E n).card +
        2 * K * ((X n).crossingEdges (P n).block).card := by
      calc
        (B n).card ≤ (E n).card +
            K * (2 * ((X n).crossingEdges (P n).block).card) := by
          change (badVertices (X n) (P n) (E n) K).card ≤ _
          exact hcard
        _ = (E n).card +
            2 * K * ((X n).crossingEdges (P n).block).card := by ring
    exact_mod_cast hcard'
  have hbadSource : Negligible
      (fun n ↦ (Fintype.card (A.model n) : ℝ))
      (fun n ↦ ((badSourceEdges (X n) (B n)).card : ℝ)) := by
    have hmajor := Negligible.const_mul (S.card : ℝ) hB
    apply Negligible.mono_nonneg
      (fun _ ↦ by positivity) (fun _ ↦ by positivity) _ hmajor
    intro n
    exact_mod_cast card_badSourceEdges_generatorGraph_le
      (A.model n) (A.map n) S (B n)
  have hunmatched : Negligible
      (fun n ↦ (Fintype.card (A.model n) : ℝ))
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
      (fun n ↦ (Fintype.card (A.model n) : ℝ))
      (fun n ↦ ((X n).editDistance (Z n) (Equiv.refl _) : ℕ)) := by
    have hmajor := Negligible.const_mul 2 hunmatched
    apply Negligible.mono_nonneg
      (fun _ ↦ by positivity) (fun _ ↦ by positivity) _ hmajor
    intro n
    exact_mod_cast
      (editWitness (X n) (P n) (B n) (marker n) (marker_ne n)).editDistance_le_two_mul_unmatchedCount
  refine ⟨{
    blocks := fun n ↦ singletonizeBadBlocks (X n) (P n) (E n) K
    cheeger := γ / 4
    cheeger_pos := div_pos hγ (by norm_num)
    graph := Z
    vertexEquiv := fun n ↦ Equiv.refl (A.model n)
    edit_negligible := by
      apply Negligible.congr hedit
      intro n
      exact_mod_cast
        (FiniteMultiGraph.editDistance_transport_right
          (X n) (Z n) (Equiv.refl _)).symm
    editWitness := fun n ↦ by
      let W := editWitness (X n) (P n) (B n) (marker n) (marker_ne n)
      exact {
        sourceKept := W.sourceKept
        targetKept := W.targetKept
        edgeEquiv := W.edgeEquiv
        preservesEndpoints := by
          intro a
          exact W.preservesEndpoints a }
    unmatched_negligible := by
      apply Negligible.congr hunmatched
      intro n
      rfl
    edge_inside := by
      intro n e
      change
        (singletonizeBadBlocks (X n) (P n) (E n) K).block
            ((Equiv.refl _) ((Z n).first e)) =
          (singletonizeBadBlocks (X n) (P n) (E n) K).block
            ((Equiv.refl _) ((Z n).second e))
      simpa only [Equiv.refl_apply] using
        edge_inside_refined (X n) (P n) (E n) K
          (marker n) (marker_ne n) (marker_spec n).2.2.1 e
    component_expands := by
      intro n y
      apply refined_component_expands (A.model n) (A.map n) S
        (P n) (E n) K (marker n) (marker_ne n) (marker_spec n).2.2.1
        r q
      · intro s
        apply
          KunLocalNeighborhood.SoficApproximation.card_forwardNeighborhood_ge
            A S hsymm hgen q n (marker n s)
        exact (marker_spec n).2.1 s
      · exact (marker_spec n).2.2.2.1
      · exact (marker_spec n).2.2.2.2
      · exact hγ
      · exact hq
      · exact hglobal n
    almost_invariant := by
      intro t ht
      have hold : Negligible
          (fun n ↦ (Fintype.card (A.model n) : ℝ))
          (fun n ↦ ((wordCrossing (P n) (A.map n t)).card : ℝ)) := by
        apply Negligible.mono_nonneg
          (fun _ ↦ by positivity) (fun _ ↦ by positivity) _ hcrossing
        intro n
        exact_mod_cast card_wordCrossing_le_crossingEdges
          (A.model n) (A.map n) S (P n) ht
      have hmajor := Negligible.add hold (Negligible.const_mul 2 hB)
      apply Negligible.mono_nonneg
        (fun _ ↦ by positivity) (fun _ ↦ by positivity) _ hmajor
      intro n
      exact_mod_cast card_wordCrossing_singletonizeBadBlocks_le
        (X n) (P n) (E n) K (A.map n t)
  }⟩

/-- Unconditional Kun decomposition theorem from the standard hypotheses:
finite generation, infinitude, property `(T)`, and a sofic approximation.  A
symmetric finite generating set containing a Kazhdan pair is constructed
inside the proof. -/
theorem propertyT_expanderDecomposition [Group.FG G]
    (hT : HasKazhdanPropertyT.{0, 0} G) (A : SoficApproximation G) :
    ∃ S : Finset G,
      (∀ g ∈ S, g⁻¹ ∈ S) ∧
      Subgroup.closure (S : Set G) = ⊤ ∧
      Nonempty (ExpanderDecomposition A S) := by
  classical
  obtain ⟨Q, ε, honeQ, _hε, hεone, hQ⟩ :=
    HasKazhdanPropertyT.exists_identity_pair hT
  obtain ⟨_, F, _, hF⟩ :=
    Group.fg_iff'.mp (inferInstance : Group.FG G)
  let U : Finset G := Q ∪ F
  let S : Finset G := insert 1 (U ∪ U.image fun g ↦ g⁻¹)
  have hsymm : ∀ g ∈ S, g⁻¹ ∈ S := by
    intro g hg
    simp only [S, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hg ⊢
    rcases hg with h | h | ⟨x, hx, rfl⟩
    · left
      simp [h]
    · exact Or.inr (Or.inr ⟨g, h, rfl⟩)
    · exact Or.inr (Or.inl (by simpa using hx))
  have hQS : Q ⊆ S := by
    intro g hg
    exact Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (Finset.mem_union_left _ hg))
  have hone : (1 : G) ∈ S := Finset.mem_insert_self 1 _
  have hgen : Subgroup.closure (S : Set G) = ⊤ := by
    apply top_unique
    rw [← hF]
    apply Subgroup.closure_mono
    intro g hg
    exact Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (Finset.mem_union_right _ hg))
  have hD := exists_expanderDecomposition
    hQ S hQS hone hεone hsymm hgen A
  exact ⟨S, hsymm, hgen, hD⟩

end KunDecomposition
end NonsoficGroupsExist
