import NonsoficGroupsExist.Matching.BlockWordCrossing
import NonsoficGroupsExist.Matching.DecompositionRefinement
import NonsoficGroupsExist.Matching.EdgeEditing

/-!
# Compressor crossing errors on generator graphs

For a compressor permutation `q`, a generator arc can cross the transported
component partition only if approximate conjugacy fails at its source or the
assigned conjugate crosses a target block.  The edge type retains the
generator label, so the resulting bound is a finite sum over generators.
-/

namespace NonsoficGroupsExist
namespace SoficApproximation

variable {G : Type} [Group G] (S : SoficApproximation G)
variable {T : Finset G} (P : ∀ n, BlockStructure (S.model n))

/-- The component label after applying the compressor permutation. -/
def compressorLabel (n : ℕ) (q : G) (x : S.model n) : Finset (S.model n) :=
  (P n).block (S.map n q x)

/-- Tagged vertex errors, with one disjoint fiber for every generator. -/
noncomputable def generatorErrorPairs (n : ℕ) (q : G) :
    Finset (T × S.model n) := by
  classical
  exact (Finset.univ : Finset T).biUnion fun t ↦
    ({t} : Finset T) ×ˢ
      (S.conjugacyError n q t.1 ∪
        permutationPreimage (S.map n q)
          (wordCrossing (P n) (S.map n (q * t.1 * q⁻¹))))

theorem generator_crossing_pairs_subset (n : ℕ) (q : G) :
    ((generatorGraph (S.model n) T (S.map n)).crossingEdges
      (S.compressorLabel P n q)).map ⟨Subtype.val, Subtype.val_injective⟩ ⊆
        generatorErrorPairs (T := T) S P n q := by
  classical
  intro p hp
  rw [Finset.mem_map] at hp
  obtain ⟨a, ha, rfl⟩ := hp
  have hcross := (FiniteMultiGraph.mem_crossingEdges
    (generatorGraph (S.model n) T (S.map n)) (S.compressorLabel P n q) a).1 ha
  let t : T := a.1.1
  let x : S.model n := a.1.2
  simp only [generatorErrorPairs, Finset.mem_biUnion, Finset.mem_univ,
    Finset.mem_product, Finset.mem_singleton, true_and]
  refine ⟨t, ⟨rfl, ?_⟩⟩
  rw [Finset.mem_union]
  by_cases hc : x ∈ S.conjugacyError n q t.1
  · exact Or.inl hc
  · right
    rw [permutationPreimage, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    apply (show S.map n q x ∈
      wordCrossing (P n) (S.map n (q * t.1 * q⁻¹)) from ?_)
    rw [wordCrossing, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hconj : S.map n q (S.map n t.1 x) =
        S.map n (q * t.1 * q⁻¹) (S.map n q x) := by
      simpa [conjugacyError] using hc
    intro heq
    apply hcross
    change (P n).block (S.map n q x) ≠
      (P n).block (S.map n q (S.map n t.1 x)) at hcross
    change (P n).block (S.map n q x) =
      (P n).block (S.map n q (S.map n t.1 x))
    rw [hconj]
    exact heq.symm

theorem generatorErrorPairs_card_le (n : ℕ) (q : G) :
    (generatorErrorPairs (T := T) S P n q).card ≤
      ∑ t : T,
        ((S.conjugacyError n q t.1).card +
          (wordCrossing (P n) (S.map n (q * t.1 * q⁻¹))).card) := by
  classical
  calc
    (generatorErrorPairs (T := T) S P n q).card ≤
        ∑ t : T,
          (({t} : Finset T) ×ˢ
            (S.conjugacyError n q t.1 ∪
              permutationPreimage (S.map n q)
                (wordCrossing (P n) (S.map n (q * t.1 * q⁻¹))))).card := by
      exact Finset.card_biUnion_le
    _ = ∑ t : T,
          (S.conjugacyError n q t.1 ∪
            permutationPreimage (S.map n q)
              (wordCrossing (P n) (S.map n (q * t.1 * q⁻¹)))).card := by
      apply Finset.sum_congr rfl
      intro t _
      rw [Finset.card_product]
      simp
    _ ≤ ∑ t : T,
          ((S.conjugacyError n q t.1).card +
            (wordCrossing (P n) (S.map n (q * t.1 * q⁻¹))).card) := by
      apply Finset.sum_le_sum
      intro t _
      have hu := Finset.card_union_le (S.conjugacyError n q t.1)
        (permutationPreimage (S.map n q)
          (wordCrossing (P n) (S.map n (q * t.1 * q⁻¹))))
      rwa [permutationPreimage_card] at hu

/-- Occurrence-sensitive generator crossing bound. -/
theorem generatorGraph_crossing_card_le (n : ℕ) (q : G) :
    ((generatorGraph (S.model n) T (S.map n)).crossingEdges
      (S.compressorLabel P n q)).card ≤
      ∑ t : T,
        ((S.conjugacyError n q t.1).card +
          (wordCrossing (P n) (S.map n (q * t.1 * q⁻¹))).card) := by
  rw [← Finset.card_map]
  exact (Finset.card_le_card (S.generator_crossing_pairs_subset P n q)).trans
    (S.generatorErrorPairs_card_le P n q)

/-- The generator-graph crossings have negligible density whenever every
fixed target element almost preserves the target block structure. -/
theorem generatorGraph_crossing_negligible
    (hall : ∀ g : G, Negligible
      (fun n ↦ (Fintype.card (S.model n) : ℝ))
      fun n ↦ ((wordCrossing (P n) (S.map n g)).card : ℝ))
    (q : G) : Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      fun n ↦ (((generatorGraph (S.model n) T (S.map n)).crossingEdges
        (S.compressorLabel P n q)).card : ℝ) := by
  let I : Finset T := Finset.univ
  have hsum : Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      fun n ↦ ∑ t ∈ I,
        (((S.conjugacyError n q t.1).card : ℝ) +
          ((wordCrossing (P n) (S.map n (q * t.1 * q⁻¹))).card : ℝ)) := by
    apply Negligible.sum I
    intro t _
    exact Negligible.add (S.conjugacyError_negligible q t.1)
      (hall (q * t.1 * q⁻¹))
  refine Vanishing.squeeze (fun n ↦ div_nonneg (by positivity) (by positivity))
    (fun n ↦ ?_) hsum
  have hcard := S.generatorGraph_crossing_card_le (T := T) P n q
  have hcast :
      (((generatorGraph (S.model n) T (S.map n)).crossingEdges
        (S.compressorLabel P n q)).card : ℝ) ≤
      ∑ t : T,
        (((S.conjugacyError n q t.1).card : ℝ) +
          ((wordCrossing (P n) (S.map n (q * t.1 * q⁻¹))).card : ℝ)) := by
    exact_mod_cast hcard
  apply div_le_div_of_nonneg_right
  simpa [I] using hcast
  positivity

end SoficApproximation

namespace ExpanderDecomposition

variable {G : Type} [Group G] {S : SoficApproximation G} {T : Finset G}

/-- The edited decomposition graph has negligible compressor crossings.  The
two contributions are the occurrence edits and the generator-arc errors. -/
theorem globalCrossing_negligible (D : ExpanderDecomposition S T)
    (hall : ∀ g : G, Negligible
      (fun n ↦ (Fintype.card (S.model n) : ℝ))
      fun n ↦ ((wordCrossing (D.blocks n) (S.map n g)).card : ℝ))
    (q : G) : Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      fun n ↦ (((D.modelGraph n).crossingEdges
        (transportedTargetLabel (D.blocks n) (S.map n q))).card : ℝ) := by
  have hgenerator := S.generatorGraph_crossing_negligible (T := T) D.blocks hall q
  have hsum := Negligible.add D.unmatched_negligible hgenerator
  refine Vanishing.squeeze (fun n ↦ div_nonneg (by positivity) (by positivity))
    (fun n ↦ ?_) hsum
  have hcard := (D.editWitness n).targetCrossing_card_le_unmatchedCount
    (S.compressorLabel D.blocks n q)
    (transportedTargetLabel (D.blocks n) (S.map n q)) (fun _ ↦ rfl)
  have hcast :
      (((D.modelGraph n).crossingEdges
        (transportedTargetLabel (D.blocks n) (S.map n q))).card : ℝ) ≤
      ((D.editWitness n).unmatchedCount : ℝ) +
        (((generatorGraph (S.model n) T (S.map n)).crossingEdges
          (S.compressorLabel D.blocks n q)).card : ℝ) := by
    exact_mod_cast hcard
  apply div_le_div_of_nonneg_right hcast
  positivity

end ExpanderDecomposition
end NonsoficGroupsExist
