import NonsoficGroupsExist.GeneratorCrossing

/-!
# Compressor crossings for an external permutation

The source generator graph is indexed by an abstract group `Γ`, while a
compressor need only belong to an ambient group.  This file allows its model
permutation to be supplied independently, together with the endomorphism of
`Γ` represented by conjugation.
-/

namespace NonsoficGroupsExist
namespace SoficApproximation

variable {G : Type} [Group G] (S : SoficApproximation G)
variable {T : Finset G} (P : ∀ n, BlockStructure (S.model n))

def externalCompressorLabel (n : ℕ) (q : Equiv.Perm (S.model n))
    (x : S.model n) : Finset (S.model n) :=
  (P n).block (q x)

noncomputable def externalConjugacyError (n : ℕ)
    (q : Equiv.Perm (S.model n)) (c : G → G) (g : G) : Finset (S.model n) :=
  Finset.univ.filter fun x ↦ q (S.map n g x) ≠ S.map n (c g) (q x)

noncomputable def externalGeneratorErrorPairs (n : ℕ)
    (q : Equiv.Perm (S.model n)) (c : G → G) : Finset (T × S.model n) := by
  classical
  exact (Finset.univ : Finset T).biUnion fun t ↦
    ({t} : Finset T) ×ˢ
      (S.externalConjugacyError n q c t.1 ∪
        permutationPreimage q (wordCrossing (P n) (S.map n (c t.1))))

theorem external_generator_crossing_pairs_subset (n : ℕ)
    (q : Equiv.Perm (S.model n)) (c : G → G) :
    ((generatorGraph (S.model n) T (S.map n)).crossingEdges
      (S.externalCompressorLabel P n q)).map ⟨Subtype.val, Subtype.val_injective⟩ ⊆
        externalGeneratorErrorPairs (T := T) S P n q c := by
  classical
  intro p hp
  rw [Finset.mem_map] at hp
  obtain ⟨a, ha, rfl⟩ := hp
  have hcross := (FiniteMultiGraph.mem_crossingEdges
    (generatorGraph (S.model n) T (S.map n))
      (S.externalCompressorLabel P n q) a).1 ha
  let t : T := a.1.1
  let x : S.model n := a.1.2
  simp only [externalGeneratorErrorPairs, Finset.mem_biUnion, Finset.mem_univ,
    Finset.mem_product, Finset.mem_singleton, true_and]
  refine ⟨t, ⟨rfl, ?_⟩⟩
  rw [Finset.mem_union]
  by_cases hc : x ∈ S.externalConjugacyError n q c t.1
  · exact Or.inl hc
  · right
    rw [permutationPreimage, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [wordCrossing, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hconj : q (S.map n t.1 x) = S.map n (c t.1) (q x) := by
      simpa [externalConjugacyError] using hc
    intro heq
    apply hcross
    change (P n).block (q x) ≠ (P n).block (q (S.map n t.1 x)) at hcross
    change (P n).block (q x) = (P n).block (q (S.map n t.1 x))
    rw [hconj]
    exact heq.symm

theorem externalGeneratorErrorPairs_card_le (n : ℕ)
    (q : Equiv.Perm (S.model n)) (c : G → G) :
    (externalGeneratorErrorPairs (T := T) S P n q c).card ≤
      ∑ t : T, ((S.externalConjugacyError n q c t.1).card +
        (wordCrossing (P n) (S.map n (c t.1))).card) := by
  classical
  calc
    (externalGeneratorErrorPairs (T := T) S P n q c).card ≤
        ∑ t : T, (({t} : Finset T) ×ˢ
          (S.externalConjugacyError n q c t.1 ∪
            permutationPreimage q (wordCrossing (P n) (S.map n (c t.1))))).card :=
      Finset.card_biUnion_le
    _ = ∑ t : T, (S.externalConjugacyError n q c t.1 ∪
          permutationPreimage q (wordCrossing (P n) (S.map n (c t.1)))).card := by
      apply Finset.sum_congr rfl
      intro t _
      rw [Finset.card_product]
      simp
    _ ≤ ∑ t : T, ((S.externalConjugacyError n q c t.1).card +
          (wordCrossing (P n) (S.map n (c t.1))).card) := by
      apply Finset.sum_le_sum
      intro t _
      have hu := Finset.card_union_le (S.externalConjugacyError n q c t.1)
        (permutationPreimage q (wordCrossing (P n) (S.map n (c t.1))))
      rwa [permutationPreimage_card] at hu

theorem externalGeneratorGraph_crossing_card_le (n : ℕ)
    (q : Equiv.Perm (S.model n)) (c : G → G) :
    ((generatorGraph (S.model n) T (S.map n)).crossingEdges
      (S.externalCompressorLabel P n q)).card ≤
      ∑ t : T, ((S.externalConjugacyError n q c t.1).card +
        (wordCrossing (P n) (S.map n (c t.1))).card) := by
  rw [← Finset.card_map]
  exact (Finset.card_le_card
    (S.external_generator_crossing_pairs_subset (T := T) P n q c)).trans
      (S.externalGeneratorErrorPairs_card_le (T := T) P n q c)

theorem externalGeneratorGraph_crossing_negligible
    (q : ∀ n, Equiv.Perm (S.model n)) (c : G → G)
    (herr : ∀ g ∈ T, Negligible
      (fun n ↦ (Fintype.card (S.model n) : ℝ))
      fun n ↦ ((S.externalConjugacyError n (q n) c g).card : ℝ))
    (hall : ∀ g : G, Negligible
      (fun n ↦ (Fintype.card (S.model n) : ℝ))
      fun n ↦ ((wordCrossing (P n) (S.map n g)).card : ℝ)) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      fun n ↦ (((generatorGraph (S.model n) T (S.map n)).crossingEdges
        (S.externalCompressorLabel P n (q n))).card : ℝ) := by
  let I : Finset T := Finset.univ
  have hsum : Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      fun n ↦ ∑ t ∈ I, (((S.externalConjugacyError n (q n) c t.1).card : ℝ) +
        ((wordCrossing (P n) (S.map n (c t.1))).card : ℝ)) := by
    apply Negligible.sum I
    intro t _
    exact Negligible.add (herr t.1 t.2) (hall (c t.1))
  refine Vanishing.squeeze (fun n ↦ div_nonneg (by positivity) (by positivity))
    (fun n ↦ ?_) hsum
  have hcard := S.externalGeneratorGraph_crossing_card_le (T := T) P n (q n) c
  have hcast : (((generatorGraph (S.model n) T (S.map n)).crossingEdges
      (S.externalCompressorLabel P n (q n))).card : ℝ) ≤
      ∑ t : T, (((S.externalConjugacyError n (q n) c t.1).card : ℝ) +
        ((wordCrossing (P n) (S.map n (c t.1))).card : ℝ)) := by
    exact_mod_cast hcard
  apply div_le_div_of_nonneg_right
  simpa [I] using hcast
  positivity

end SoficApproximation

namespace ExpanderDecomposition

variable {G : Type} [Group G] {S : SoficApproximation G} {T : Finset G}

theorem externalGlobalCrossing_negligible (D : ExpanderDecomposition S T)
    (q : ∀ n, Equiv.Perm (S.model n)) (c : G → G)
    (herr : ∀ g ∈ T, Negligible
      (fun n ↦ (Fintype.card (S.model n) : ℝ))
      fun n ↦ ((S.externalConjugacyError n (q n) c g).card : ℝ))
    (hall : ∀ g : G, Negligible
      (fun n ↦ (Fintype.card (S.model n) : ℝ))
      fun n ↦ ((wordCrossing (D.blocks n) (S.map n g)).card : ℝ)) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      fun n ↦ (((D.modelGraph n).crossingEdges
        (transportedTargetLabel (D.blocks n) (q n))).card : ℝ) := by
  have hgenerator := S.externalGeneratorGraph_crossing_negligible
    (T := T) D.blocks q c herr hall
  have hsum := Negligible.add D.unmatched_negligible hgenerator
  refine Vanishing.squeeze (fun n ↦ div_nonneg (by positivity) (by positivity))
    (fun n ↦ ?_) hsum
  have hcard := (D.editWitness n).targetCrossing_card_le_unmatchedCount
    (S.externalCompressorLabel D.blocks n (q n))
    (transportedTargetLabel (D.blocks n) (q n)) (fun _ ↦ rfl)
  have hcast : (((D.modelGraph n).crossingEdges
      (transportedTargetLabel (D.blocks n) (q n))).card : ℝ) ≤
      ((D.editWitness n).unmatchedCount : ℝ) +
        (((generatorGraph (S.model n) T (S.map n)).crossingEdges
          (S.externalCompressorLabel D.blocks n (q n))).card : ℝ) := by
    exact_mod_cast hcard
  apply div_le_div_of_nonneg_right hcast
  positivity

end ExpanderDecomposition
end NonsoficGroupsExist
