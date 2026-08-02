import NonsoficGroupsExist.MatchingSelection
import NonsoficGroupsExist.CompletionGraphEditing
import NonsoficGroupsExist.GeneratorGraphEditing
import NonsoficGroupsExist.EdgeWitnessRestriction

/-!
# Comparing the localized generator graph with the selected expander

The comparison is factored through the completed restriction of the original
`Γ` action.  The three edit costs are: completion at the source component,
compressor conjugacy together with completion at the transported component,
and the restriction of Kun's occurrence edit witness.
-/

namespace NonsoficGroupsExist

open scoped BigOperators

namespace LocalCriterionData

variable {G Γ J : Type} [Group G] [Group Γ] [Group J]
  [Countable Γ] [Countable J]
variable (D : LocalCriterionData G Γ J)

noncomputable def gammaCompletion (n : ℕ) (g : Γ) :
    Equiv.Perm (D.selectedComponent n).block :=
  Classical.choose (Localization.exists_completion_with_bound
    (D.selectedComponent n).block
    (D.approximation.map (D.matchingIndex n) (D.setup.embedΓ g)))

theorem gammaCompletion_disagreement_bound (n : ℕ) (g : Γ) :
    (Finset.univ.filter fun x : (D.selectedComponent n).block ↦
      (D.gammaCompletion n g x : D.approximation.model (D.matchingIndex n)) ≠
        D.approximation.map (D.matchingIndex n) (D.setup.embedΓ g) x).card ≤
    (Finset.univ.filter fun x : (D.selectedComponent n).block ↦
      D.approximation.map (D.matchingIndex n) (D.setup.embedΓ g) x ∉
        (D.selectedComponent n).block).card :=
  Classical.choose_spec (Localization.exists_completion_with_bound
    (D.selectedComponent n).block
    (D.approximation.map (D.matchingIndex n) (D.setup.embedΓ g)))

noncomputable def transportedGammaCompletion (n : ℕ) (g : Γ) :
    Equiv.Perm (D.selectedSubset n) :=
  (D.selectedImageEquiv n).symm.trans
    ((D.gammaCompletion n g).trans (D.selectedImageEquiv n))

noncomputable def completedGammaGraph (n : ℕ) : FiniteMultiGraph :=
  generatorGraph
    { carrier := D.selectedSubset n
      fintype := inferInstance
      decidableEq := inferInstance }
    D.setup.generatorsΓ (D.transportedGammaCompletion n)

noncomputable def inducedGammaGraph (n : ℕ) : FiniteMultiGraph :=
  (generatorGraph (D.approximation.model (D.matchingIndex n))
    D.setup.generatorsΓ
    (fun g ↦ D.approximation.map (D.matchingIndex n) (D.setup.embedΓ g))).induce
      (D.selectedComponent n).block

noncomputable def transportedInducedGammaGraph (n : ℕ) : FiniteMultiGraph :=
  (D.inducedGammaGraph n).transport
    { carrier := D.selectedSubset n
      fintype := inferInstance
      decidableEq := inferInstance }
    (D.selectedImageEquiv n)

theorem selected_gammaBoundary_le_graphError (n : ℕ) :
    (∑ t : D.setup.generatorsΓ,
      (Finset.univ.filter fun x : (D.selectedComponent n).block ↦
        D.approximation.map (D.matchingIndex n) (D.setup.embedΓ t.1) x ∉
          (D.selectedComponent n).block).card : ℝ) ≤
      D.localGraphBaseError n (D.selectedComponent n) := by
  have hterm : (∑ t : D.setup.generatorsΓ,
      (Finset.univ.filter fun x : (D.selectedComponent n).block ↦
        D.approximation.map (D.matchingIndex n) (D.setup.embedΓ t.1) x ∉
          (D.selectedComponent n).block).card : ℝ) =
      D.localGammaBoundaryError n (D.selectedComponent n) := by
    apply Finset.sum_congr rfl
    intro t _
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hout hblock
      apply hout
      have hxblock : (D.gammaDecomposition.blocks (D.matchingIndex n)).block x =
          (D.selectedComponent n).block := by
        exact ((D.gammaDecomposition.blocks (D.matchingIndex n)).eq_of_mem
          (BlockIndex.representative _ (D.selectedComponent n)) x x.2).trans
            (BlockIndex.block_representative _ _)
      rw [← hxblock, hblock]
      exact (D.gammaDecomposition.blocks (D.matchingIndex n)).self_mem _
    · intro hcross hmem
      apply hcross
      have hxblock : (D.gammaDecomposition.blocks (D.matchingIndex n)).block x =
          (D.selectedComponent n).block := by
        exact ((D.gammaDecomposition.blocks (D.matchingIndex n)).eq_of_mem
          (BlockIndex.representative _ (D.selectedComponent n)) x x.2).trans
            (BlockIndex.block_representative _ _)
      rw [hxblock]
      exact (D.gammaDecomposition.blocks (D.matchingIndex n)).eq_of_mem _ _ hmem
  rw [hterm]
  unfold localGraphBaseError
  positivity

theorem completed_to_induced_edit_le (n : ℕ) :
    (D.completedGammaGraph n).editDistance (D.transportedInducedGammaGraph n)
      (Equiv.refl (D.selectedSubset n)) ≤
      4 * D.localGraphBaseError n (D.selectedComponent n) := by
  have hbase := CompletionGraphEditing.editDistance_le
    (D.selectedComponent n).block D.setup.generatorsΓ
    (fun g ↦ D.approximation.map (D.matchingIndex n) (D.setup.embedΓ g))
    (D.gammaCompletion n)
  have hcompletion : (∑ t : D.setup.generatorsΓ,
      (Finset.univ.filter fun x : (D.selectedComponent n).block ↦
        (D.gammaCompletion n t.1 x : D.approximation.model (D.matchingIndex n)) ≠
          D.approximation.map (D.matchingIndex n) (D.setup.embedΓ t.1) x).card) ≤
      ∑ t : D.setup.generatorsΓ,
      (Finset.univ.filter fun x : (D.selectedComponent n).block ↦
        D.approximation.map (D.matchingIndex n) (D.setup.embedΓ t.1) x ∉
          (D.selectedComponent n).block).card := by
    apply Finset.sum_le_sum
    intro t _
    exact D.gammaCompletion_disagreement_bound n t.1
  have htransport := FiniteMultiGraph.editDistance_transport_both
    (generatorGraph
      { carrier := (D.selectedComponent n).block
        fintype := inferInstance
        decidableEq := inferInstance }
      D.setup.generatorsΓ (D.gammaCompletion n))
    (D.inducedGammaGraph n)
    { carrier := D.selectedSubset n
      fintype := inferInstance
      decidableEq := inferInstance }
    (Equiv.refl _) (D.selectedImageEquiv n)
  change (D.completedGammaGraph n).editDistance (D.transportedInducedGammaGraph n)
      (Equiv.refl _) ≤ _
  rw [htransport]
  calc
    _ ≤ 4 * ∑ t : D.setup.generatorsΓ,
      (Finset.univ.filter fun x : (D.selectedComponent n).block ↦
        (D.gammaCompletion n t.1 x : D.approximation.model (D.matchingIndex n)) ≠
          D.approximation.map (D.matchingIndex n) (D.setup.embedΓ t.1) x).card := hbase
    _ ≤ 4 * ∑ t : D.setup.generatorsΓ,
      (Finset.univ.filter fun x : (D.selectedComponent n).block ↦
        D.approximation.map (D.matchingIndex n) (D.setup.embedΓ t.1) x ∉
          (D.selectedComponent n).block).card := Nat.mul_le_mul_left 4 hcompletion
    _ ≤ 4 * D.localGraphBaseError n (D.selectedComponent n) := by
      exact_mod_cast Nat.mul_le_mul_left 4 (by
        exact_mod_cast D.selected_gammaBoundary_le_graphError n)

theorem induced_to_selected_edit_le (n : ℕ) :
    (D.transportedInducedGammaGraph n).editDistance (D.selectedGraph n)
      (Equiv.refl (D.selectedSubset n)) ≤
      2 * D.localGammaEditError n (D.selectedComponent n) := by
  let W := D.gammaDecomposition.editWitness (D.matchingIndex n)
  let B := (D.selectedComponent n).block
  let WI := W.induce B B (fun _ ↦ Iff.rfl)
  have hw := WI.editDistance_le_two_mul_unmatchedCount
  have hlocal := W.induce_unmatchedCount_le_filters B B (fun _ ↦ Iff.rfl)
  have htransport := FiniteMultiGraph.editDistance_transport_both
    (D.inducedGammaGraph n)
    ((D.gammaDecomposition.modelGraph (D.matchingIndex n)).induce B)
    { carrier := D.selectedSubset n
      fintype := inferInstance
      decidableEq := inferInstance }
    (Equiv.refl _) (D.selectedImageEquiv n)
  rw [htransport]
  calc
    _ ≤ 2 * WI.unmatchedCount := hw
    _ ≤ 2 * D.localGammaEditError n (D.selectedComponent n) := by
      apply Nat.mul_le_mul_left
      exact_mod_cast hlocal

noncomputable def localizedGammaAct (n : ℕ) (g : Γ) :
    Equiv.Perm (D.selectedSubset n) :=
  (D.selectedLocalization.completedMap n (g, 1))

theorem localized_to_completed_disagreement_negligible (t : Γ)
    (ht : t ∈ D.setup.generatorsΓ) :
    Vanishing fun n ↦
      ((Finset.univ.filter fun y : D.selectedSubset n ↦
        D.localizedGammaAct n t y ≠ D.transportedGammaCompletion n t y).card : ℝ) /
          (D.selectedSubset n).card := by
  have hA := D.selectedLocalization.completedMap_disagreement_vanishing (t, 1)
  have hsource : Vanishing fun n ↦
      ((Finset.univ.filter fun x : (D.selectedComponent n).block ↦
        (D.gammaCompletion n t x : D.approximation.model (D.matchingIndex n)) ≠
          D.approximation.map (D.matchingIndex n) (D.setup.embedΓ t) x).card : ℝ) /
        (D.selectedComponent n).block.card := by
    refine Vanishing.squeeze (fun n ↦ div_nonneg (by positivity) (by positivity))
      (fun n ↦ ?_) (D.selectedComponent_error 0)
    apply div_le_div_of_nonneg_right
    · have h := D.gammaCompletion_disagreement_bound n t
      exact_mod_cast h.trans (by
        have hsingle : (Finset.univ.filter fun x : (D.selectedComponent n).block ↦
          D.approximation.map (D.matchingIndex n) (D.setup.embedΓ t) x ∉
            (D.selectedComponent n).block).card ≤
            D.localGammaBoundaryError n (D.selectedComponent n) := by
          unfold localGammaBoundaryError
          exact_mod_cast Finset.single_le_sum
            (fun g _ ↦ by positivity) (Finset.mem_attach _ ht)
        exact hsingle.trans (by unfold componentSelectionError localGraphBaseError; positivity))
    · positivity
  have hsource' : Vanishing fun n ↦
      ((Finset.univ.filter fun y : D.selectedSubset n ↦
        (D.transportedGammaCompletion n t y : D.approximation.model (D.matchingIndex n)) ≠
          D.approximation.map (D.matchingIndex n) (D.setup.embedΓ t)
            ((D.selectedImageEquiv n).symm y)).card : ℝ) /
        (D.selectedSubset n).card := by
    simpa [transportedGammaCompletion, D.selectedSubset_card] using hsource
  have hconj : Vanishing fun n ↦
      ((Finset.univ.filter fun x : (D.selectedComponent n).block ↦
        (x : D.approximation.model (D.matchingIndex n)) ∈
          D.approximation.conjugacyError (D.matchingIndex n)
            D.setup.distinguished (D.setup.embedΓ t)).card : ℝ) /
        (D.selectedComponent n).block.card := by
    refine Vanishing.squeeze (fun n ↦ div_nonneg (by positivity) (by positivity))
      (fun n ↦ ?_) (D.selectedComponent_error 0)
    apply div_le_div_of_nonneg_right
    · unfold componentSelectionError localGraphBaseError localConjugacyGraphError
      have hterm := Finset.single_le_sum
        (fun g _ ↦ by positivity) (Finset.mem_attach _ ht)
      positivity
    · positivity
  have hall := Vanishing.add hA (Vanishing.add hsource' (by
    simpa [D.selectedSubset_card] using hconj))
  refine Vanishing.squeeze (fun n ↦ div_nonneg (by positivity) (by positivity))
    (fun n ↦ ?_) hall
  apply div_le_div_of_nonneg_right
  · let E₀ := Finset.univ.filter fun y : D.selectedSubset n ↦
        (D.localizedGammaAct n t y :
            D.approximation.model (D.matchingIndex n)) ≠
          D.localizedProductAct n (t, 1) y
    let E₁ := Finset.univ.filter fun y : D.selectedSubset n ↦
        (D.transportedGammaCompletion n t y :
            D.approximation.model (D.matchingIndex n)) ≠
          D.approximation.map (D.matchingIndex n) (D.setup.embedΓ t)
            ((D.selectedImageEquiv n).symm y)
    let E₂ := Finset.univ.filter fun y : D.selectedSubset n ↦
        ((D.selectedImageEquiv n).symm y :
            D.approximation.model (D.matchingIndex n)) ∈
          D.approximation.conjugacyError (D.matchingIndex n)
            D.setup.distinguished (D.setup.embedΓ t)
    have hsubset : (Finset.univ.filter fun y : D.selectedSubset n ↦
        D.localizedGammaAct n t y ≠ D.transportedGammaCompletion n t y) ⊆
        E₀ ∪ (E₁ ∪ E₂) := by
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      by_cases hloc : (D.localizedGammaAct n t y :
          D.approximation.model (D.matchingIndex n)) ≠ D.localizedProductAct n (t, 1) y
      · exact Or.inl hloc
      by_cases hsrc : (D.transportedGammaCompletion n t y :
          D.approximation.model (D.matchingIndex n)) ≠
          D.approximation.map (D.matchingIndex n) (D.setup.embedΓ t)
            ((D.selectedImageEquiv n).symm y)
      · exact Or.inr (Or.inl hsrc)
      · exact Or.inr (Or.inr (by
          intro hgood
          apply hy
          apply Subtype.ext
          rw [not_ne_iff.mp hloc, not_ne_iff.mp hsrc]
          exact hgood))
    have hcard := (Finset.card_le_card hsubset).trans
      ((Finset.card_union_le E₀ (E₁ ∪ E₂)).trans
        (Nat.add_le_add_left (Finset.card_union_le E₁ E₂) E₀.card))
    exact_mod_cast hcard
  · positivity

theorem localized_to_completed_edit_negligible :
    Negligible (fun n ↦ ((D.selectedSubset n).card : ℝ)) fun n ↦
      ((generatorGraph
        { carrier := D.selectedSubset n
          fintype := inferInstance
          decidableEq := inferInstance }
        D.setup.generatorsΓ (D.localizedGammaAct n)).editDistance
          (D.completedGammaGraph n) (Equiv.refl _) : ℕ) := by
  have hsum := Negligible.sum (Finset.univ : Finset D.setup.generatorsΓ)
    (fun t n ↦ ((Finset.univ.filter fun y : D.selectedSubset n ↦
      D.localizedGammaAct n t.1 y ≠ D.transportedGammaCompletion n t.1 y).card : ℝ))
    (fun t _ ↦ D.localized_to_completed_disagreement_negligible t.1 t.2)
  refine Negligible.mono (fun n ↦ by
      rw [D.selectedSubset_card]
      exact_mod_cast (BlockIndex.block_nonempty
        (D.gammaDecomposition.blocks (D.matchingIndex n))
        (D.selectedComponent n)).card_pos)
    (fun n ↦ by positivity) (fun n ↦ ?_) (Negligible.const_mul 4 hsum)
  exact_mod_cast GeneratorGraphEditing.editDistance_le D.setup.generatorsΓ
    (D.localizedGammaAct n) (D.transportedGammaCompletion n)

theorem completed_to_selected_edit_negligible :
    Negligible (fun n ↦ ((D.selectedSubset n).card : ℝ)) fun n ↦
      ((D.completedGammaGraph n).editDistance (D.selectedGraph n) (Equiv.refl _) : ℕ) := by
  have hbase : Vanishing fun n ↦
      D.localGraphBaseError n (D.selectedComponent n) /
        (D.selectedComponent n).block.card := by
    refine Vanishing.squeeze (fun n ↦ div_nonneg (by positivity) (by positivity))
      (fun n ↦ ?_) (D.selectedComponent_error 0)
    apply div_le_div_of_nonneg_right
    · unfold componentSelectionError
      positivity
    · positivity
  have hbound := Vanishing.const_mul 6 hbase
  refine Vanishing.squeeze (fun n ↦ div_nonneg (by positivity) (by positivity))
    (fun n ↦ ?_) (by simpa [D.selectedSubset_card] using hbound)
  apply div_le_div_of_nonneg_right
  · have htri := FiniteMultiGraph.editDistance_triangle
      (D.completedGammaGraph n) (D.transportedInducedGammaGraph n)
      (D.selectedGraph n) (Equiv.refl _) (Equiv.refl _)
    have h₁ := D.completed_to_induced_edit_le n
    have h₂ := D.induced_to_selected_edit_le n
    exact_mod_cast htri.trans (by
      have : D.localGammaEditError n (D.selectedComponent n) ≤
          D.localGraphBaseError n (D.selectedComponent n) := by
        unfold localGraphBaseError
        positivity
      linarith)
  · positivity

theorem selectedGraph_edit_negligible :
    Negligible (fun n ↦ ((D.selectedSubset n).card : ℝ)) fun n ↦
      ((generatorGraph
        { carrier := D.selectedSubset n
          fintype := inferInstance
          decidableEq := inferInstance }
        D.setup.generatorsΓ (fun g ↦ D.selectedLocalization.completedMap n (g, 1))).editDistance
          (D.selectedGraph n) (Equiv.refl _) : ℕ) := by
  have hsum := Negligible.add D.localized_to_completed_edit_negligible
    D.completed_to_selected_edit_negligible
  refine Negligible.mono (fun n ↦ by positivity) (fun n ↦ by positivity)
    (fun n ↦ ?_) hsum
  exact_mod_cast FiniteMultiGraph.editDistance_triangle
    (generatorGraph
      { carrier := D.selectedSubset n
        fintype := inferInstance
        decidableEq := inferInstance }
      D.setup.generatorsΓ (D.localizedGammaAct n))
    (D.completedGammaGraph n) (D.selectedGraph n) (Equiv.refl _) (Equiv.refl _)

end LocalCriterionData
end NonsoficGroupsExist
