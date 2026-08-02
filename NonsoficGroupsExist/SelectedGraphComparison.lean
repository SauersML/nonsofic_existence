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

/-- The restricted `Γ` action, always expressed through the same `comap` used
by the expander decomposition. -/
noncomputable def gammaAct (n : ℕ) (g : Γ) :
    Equiv.Perm ((D.approximation.comap D.setup.embedΓ
      D.setup.embedΓ_injective).model (D.matchingIndex n)) :=
  (D.approximation.comap D.setup.embedΓ D.setup.embedΓ_injective).map
    (D.matchingIndex n) g

noncomputable def gammaCompletion (n : ℕ) (g : Γ) :
    Equiv.Perm (D.selectedComponent n).block :=
  Classical.choose (Localization.exists_completion_with_bound
    (D.selectedComponent n).block
    (D.gammaAct n g))

theorem gammaCompletion_disagreement_bound (n : ℕ) (g : Γ) :
    (Finset.univ.filter fun x : (D.selectedComponent n).block ↦
      (D.gammaCompletion n g x).1 ≠
        D.gammaAct n g x.1).card ≤
    (Finset.univ.filter fun x : (D.selectedComponent n).block ↦
      D.gammaAct n g x.1 ∉
        (D.selectedComponent n).block).card :=
  Classical.choose_spec (Localization.exists_completion_with_bound
    (D.selectedComponent n).block
    (D.gammaAct n g))

noncomputable def transportedGammaCompletion (n : ℕ) (g : Γ) :
    Equiv.Perm (D.selectedSubset n) :=
  (D.selectedImageEquiv n).symm.trans
    ((D.gammaCompletion n g).trans (D.selectedImageEquiv n))

noncomputable def completedGammaGraph (n : ℕ) : FiniteMultiGraph :=
  generatorGraph
    (D.selectedFiniteModel n)
    D.setup.generatorsΓ (D.transportedGammaCompletion n)

noncomputable def inducedGammaGraph (n : ℕ) : FiniteMultiGraph :=
  (generatorGraph (D.approximation.model (D.matchingIndex n))
    D.setup.generatorsΓ
    (D.gammaAct n)).induce
      (D.selectedComponent n).block

noncomputable def transportedInducedGammaGraph (n : ℕ) : FiniteMultiGraph :=
  (D.inducedGammaGraph n).transport
    (D.selectedFiniteModel n)
    (D.selectedImageEquiv n)

theorem selected_gammaBoundary_le_graphError (n : ℕ) :
    (∑ t : D.setup.generatorsΓ,
      (Finset.univ.filter fun x : (D.selectedComponent n).block ↦
        D.gammaAct n t.1 x.1 ∉
          (D.selectedComponent n).block).card : ℝ) ≤
      D.localGraphBaseError n (D.selectedComponent n) := by
  have hterm : (∑ t : D.setup.generatorsΓ,
      (Finset.univ.filter fun x : (D.selectedComponent n).block ↦
        D.gammaAct n t.1 x.1 ∉
          (D.selectedComponent n).block).card : ℝ) =
      D.localGammaBoundaryError n (D.selectedComponent n) := by
    unfold localGammaBoundaryError
    apply Finset.sum_congr rfl
    intro t _
    norm_cast
    apply congrArg Finset.card
    ext x
    simp only [gammaAct, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hout hblock
      apply hout
      have hxblock : (D.gammaDecomposition.blocks (D.matchingIndex n)).block x =
          (D.selectedComponent n).block := by
        have hxrep : x.1 ∈ (D.gammaDecomposition.blocks (D.matchingIndex n)).block
            (BlockIndex.representative _ (D.selectedComponent n)) := by
          simpa only [BlockIndex.block_representative] using x.2
        exact ((D.gammaDecomposition.blocks (D.matchingIndex n)).eq_of_mem
          (BlockIndex.representative _ (D.selectedComponent n)) x.1 hxrep).trans
            (BlockIndex.block_representative _ _)
      have hself := (D.gammaDecomposition.blocks (D.matchingIndex n)).self_mem
        (D.gammaAct n t.1 x.1)
      unfold gammaAct at hself
      rw [hblock, hxblock] at hself
      exact hself
    · intro hcross hmem
      apply hcross
      have hxblock : (D.gammaDecomposition.blocks (D.matchingIndex n)).block x =
          (D.selectedComponent n).block := by
        have hxrep : x.1 ∈ (D.gammaDecomposition.blocks (D.matchingIndex n)).block
            (BlockIndex.representative _ (D.selectedComponent n)) := by
          simpa only [BlockIndex.block_representative] using x.2
        exact ((D.gammaDecomposition.blocks (D.matchingIndex n)).eq_of_mem
          (BlockIndex.representative _ (D.selectedComponent n)) x.1 hxrep).trans
            (BlockIndex.block_representative _ _)
      apply (D.gammaDecomposition.blocks (D.matchingIndex n)).eq_of_mem
      unfold gammaAct at hmem
      simpa only [hxblock] using hmem
  rw [hterm]
  unfold localGraphBaseError
  have hedit : 0 ≤ D.localGammaEditError n (D.selectedComponent n) := by
    unfold localGammaEditError
    positivity
  have hconj : 0 ≤ D.localConjugacyGraphError n (D.selectedComponent n) := by
    unfold localConjugacyGraphError
    positivity
  linarith

theorem completed_to_induced_edit_le (n : ℕ) :
    (D.completedGammaGraph n).editDistance (D.transportedInducedGammaGraph n)
      (Equiv.refl (D.selectedSubset n)) ≤
      4 * D.localGraphBaseError n (D.selectedComponent n) := by
  have hbase := CompletionGraphEditing.editDistance_le
    (D.selectedComponent n).block D.setup.generatorsΓ
    (D.gammaAct n)
    (D.gammaCompletion n)
  have hcompletion : (∑ t : D.setup.generatorsΓ,
      (Finset.univ.filter fun x : (D.selectedComponent n).block ↦
        (D.gammaCompletion n t.1 x).1 ≠
          D.gammaAct n t.1 x.1).card) ≤
      ∑ t : D.setup.generatorsΓ,
      (Finset.univ.filter fun x : (D.selectedComponent n).block ↦
        D.gammaAct n t.1 x.1 ∉
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
    (D.selectedFiniteModel n)
    (Equiv.refl _) (D.selectedImageEquiv n)
  have hconjugate := GeneratorGraphEditing.conjugateAction_editDistance
    (Y := { carrier := (D.selectedComponent n).block
      fintype := inferInstance
      decidableEq := inferInstance })
    (Z := D.selectedFiniteModel n)
    D.setup.generatorsΓ (D.selectedImageEquiv n) (D.gammaCompletion n)
    (D.transportedInducedGammaGraph n) (Equiv.refl (D.selectedSubset n))
  have hconjugate' :
      (D.completedGammaGraph n).editDistance (D.transportedInducedGammaGraph n)
          (Equiv.refl (D.selectedSubset n)) =
        ((generatorGraph
          { carrier := (D.selectedComponent n).block
            fintype := inferInstance
            decidableEq := inferInstance }
          D.setup.generatorsΓ (D.gammaCompletion n)).transport
            (D.selectedFiniteModel n) (D.selectedImageEquiv n)).editDistance
          (D.transportedInducedGammaGraph n) (Equiv.refl (D.selectedSubset n)) := by
    simpa only [completedGammaGraph, transportedGammaCompletion,
      GeneratorGraphEditing.conjugateAction] using hconjugate
  have htransport' :
      ((generatorGraph
          { carrier := (D.selectedComponent n).block
            fintype := inferInstance
            decidableEq := inferInstance }
          D.setup.generatorsΓ (D.gammaCompletion n)).transport
            (D.selectedFiniteModel n) (D.selectedImageEquiv n)).editDistance
          (D.transportedInducedGammaGraph n) (Equiv.refl (D.selectedSubset n)) =
        (generatorGraph
          { carrier := (D.selectedComponent n).block
            fintype := inferInstance
            decidableEq := inferInstance }
          D.setup.generatorsΓ (D.gammaCompletion n)).editDistance
            (D.inducedGammaGraph n) (Equiv.refl _) := by
    simpa [transportedInducedGammaGraph] using htransport
  rw [hconjugate', htransport']
  calc
    _ ≤ 4 * ∑ t : D.setup.generatorsΓ,
      (Finset.univ.filter fun x : (D.selectedComponent n).block ↦
        (D.gammaCompletion n t.1 x).1 ≠
          D.gammaAct n t.1 x.1).card := by
      exact_mod_cast hbase
    _ ≤ 4 * ∑ t : D.setup.generatorsΓ,
      (Finset.univ.filter fun x : (D.selectedComponent n).block ↦
        D.gammaAct n t.1 x.1 ∉
          (D.selectedComponent n).block).card := by
      exact_mod_cast Nat.mul_le_mul_left 4 hcompletion
    _ ≤ 4 * D.localGraphBaseError n (D.selectedComponent n) := by
      exact mul_le_mul_of_nonneg_left
        (D.selected_gammaBoundary_le_graphError n) (by norm_num)

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
    (D.selectedFiniteModel n)
    (Equiv.refl _) (D.selectedImageEquiv n)
  have hequiv : (Equiv.refl (D.inducedGammaGraph n).vertex).symm.trans
      (D.selectedImageEquiv n) = D.selectedImageEquiv n := by
    ext x
    rfl
  rw [hequiv] at htransport
  have htransport' :
      (D.transportedInducedGammaGraph n).editDistance (D.selectedGraph n)
          (Equiv.refl (D.selectedSubset n)) =
        (D.inducedGammaGraph n).editDistance
          ((D.gammaDecomposition.modelGraph (D.matchingIndex n)).induce B)
          (Equiv.refl _) := by
    simpa [transportedInducedGammaGraph, selectedGraph] using htransport
  rw [htransport']
  calc
    _ ≤ (2 * WI.unmatchedCount : ℝ) := by exact_mod_cast hw
    _ ≤ 2 * D.localGammaEditError n (D.selectedComponent n) := by
      exact_mod_cast Nat.mul_le_mul_left 2 hlocal

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
        (D.gammaCompletion n t x).1 ≠
          D.gammaAct n t x.1).card : ℝ) /
        (D.selectedComponent n).block.card := by
    refine Vanishing.squeeze (fun n ↦ div_nonneg (by positivity) (by positivity))
      (fun n ↦ ?_) (D.selectedComponent_error 0)
    apply div_le_div_of_nonneg_right
    · have h := D.gammaCompletion_disagreement_bound n t
      have hReal : ((Finset.univ.filter fun x : (D.selectedComponent n).block ↦
          (D.gammaCompletion n t x).1 ≠
            D.gammaAct n t x.1).card : ℝ) ≤
          ((Finset.univ.filter fun x : (D.selectedComponent n).block ↦
            D.gammaAct n t x.1 ∉
              (D.selectedComponent n).block).card : ℝ) := by
        exact_mod_cast h
      have hsingleNat : (Finset.univ.filter
          (fun x : (D.selectedComponent n).block ↦
          D.gammaAct n t x.1 ∉
            (D.selectedComponent n).block)).card ≤
            ∑ g : D.setup.generatorsΓ,
              (Finset.univ.filter fun x : (D.selectedComponent n).block ↦
                D.gammaAct n g.1 x.1 ∉
                  (D.selectedComponent n).block).card :=
          Finset.single_le_sum
            (f := fun g : D.setup.generatorsΓ ↦
              (Finset.univ.filter fun x : (D.selectedComponent n).block ↦
                D.gammaAct n g.1 x.1 ∉
                  (D.selectedComponent n).block).card)
            (fun _ _ ↦ Nat.zero_le _) (Finset.mem_attach _ ht)
      have hsingle : ((Finset.univ.filter
          (fun x : (D.selectedComponent n).block ↦
            D.gammaAct n t x.1 ∉
              (D.selectedComponent n).block)).card : ℝ) ≤
          D.localGraphBaseError n (D.selectedComponent n) := by
        exact (by exact_mod_cast hsingleNat).trans
          (D.selected_gammaBoundary_le_graphError n)
      exact hReal.trans (hsingle.trans (by unfold componentSelectionError; positivity))
    · positivity
  have hsource' : Vanishing fun n ↦
      ((Finset.univ.filter fun y : D.selectedSubset n ↦
        (D.transportedGammaCompletion n t y).1 ≠
          D.distinguishedPerm (D.matchingIndex n)
            (D.gammaAct n t ((D.selectedImageEquiv n).symm y).1)).card : ℝ) /
        (D.selectedSubset n).card := by
    apply Vanishing.congr hsource
    intro n
    have hcard :
        (Finset.univ.filter fun y : D.selectedSubset n ↦
          (D.transportedGammaCompletion n t y).1 ≠
            D.distinguishedPerm (D.matchingIndex n)
              (D.gammaAct n t ((D.selectedImageEquiv n).symm y).1)).card =
        (Finset.univ.filter fun x : (D.selectedComponent n).block ↦
          (D.gammaCompletion n t x).1 ≠
            D.gammaAct n t x.1).card := by
      apply Finset.card_bij
        (fun y _ ↦ (D.selectedImageEquiv n).symm y)
      · intro y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
        intro heq
        apply hy
        change D.distinguishedPerm (D.matchingIndex n)
            (D.gammaCompletion n t ((D.selectedImageEquiv n).symm y)).1 =
          D.distinguishedPerm (D.matchingIndex n)
            (D.gammaAct n t ((D.selectedImageEquiv n).symm y).1)
        exact congrArg (D.distinguishedPerm (D.matchingIndex n)) heq
      · intro y _ z _ hyz
        exact (D.selectedImageEquiv n).symm.injective hyz
      · intro x hx
        refine ⟨D.selectedImageEquiv n x, ?_, (D.selectedImageEquiv n).symm_apply_apply x⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        change D.distinguishedPerm (D.matchingIndex n) (D.gammaCompletion n t x).1 ≠
          D.distinguishedPerm (D.matchingIndex n)
            (D.gammaAct n t x.1)
        exact (D.distinguishedPerm (D.matchingIndex n)).injective.ne hx
    rw [hcard, D.selectedSubset_card]
  have hconj : Vanishing fun n ↦
      ((Finset.univ.filter fun x : (D.selectedComponent n).block ↦
        x.1 ∈
          D.approximation.conjugacyError (D.matchingIndex n)
            D.setup.distinguished (D.setup.embedΓ t)).card : ℝ) /
        (D.selectedComponent n).block.card := by
    refine Vanishing.squeeze (fun n ↦ div_nonneg (by positivity) (by positivity))
      (fun n ↦ ?_) (D.selectedComponent_error 0)
    apply div_le_div_of_nonneg_right
    · have htermNat : (Finset.univ.filter
          (fun x : (D.selectedComponent n).block ↦
            x.1 ∈
              D.approximation.conjugacyError (D.matchingIndex n)
                D.setup.distinguished (D.setup.embedΓ t))).card ≤
            ∑ g : D.setup.generatorsΓ,
              (Finset.univ.filter fun x : (D.selectedComponent n).block ↦
                x.1 ∈
                  D.approximation.conjugacyError (D.matchingIndex n)
                    D.setup.distinguished (D.setup.embedΓ g.1)).card :=
        Finset.single_le_sum
          (f := fun g : D.setup.generatorsΓ ↦
            (Finset.univ.filter fun x : (D.selectedComponent n).block ↦
              x.1 ∈ D.approximation.conjugacyError (D.matchingIndex n)
                D.setup.distinguished (D.setup.embedΓ g.1)).card)
          (fun _ _ ↦ Nat.zero_le _) (Finset.mem_attach _ ht)
      have hterm : ((Finset.univ.filter
          (fun x : (D.selectedComponent n).block ↦
            x.1 ∈
              D.approximation.conjugacyError (D.matchingIndex n)
                D.setup.distinguished (D.setup.embedΓ t))).card : ℝ) ≤
          D.localConjugacyGraphError n (D.selectedComponent n) := by
        unfold localConjugacyGraphError
        exact_mod_cast htermNat
      exact hterm.trans (by
        unfold componentSelectionError localGraphBaseError
        positivity)
    · positivity
  have hall := Vanishing.add hA (Vanishing.add hsource' (by
    simpa [D.selectedSubset_card] using hconj))
  refine Vanishing.squeeze (fun n ↦ div_nonneg (by positivity) (by positivity))
    (fun n ↦ ?_) hall
  let E₀ := Finset.univ.filter fun y : D.selectedSubset n ↦
        (D.localizedGammaAct n t y).1 ≠
          D.localizedProductAct n (t, 1) y.1
  let E₁ := Finset.univ.filter fun y : D.selectedSubset n ↦
        (D.transportedGammaCompletion n t y).1 ≠
          D.distinguishedPerm (D.matchingIndex n)
            (D.gammaAct n t ((D.selectedImageEquiv n).symm y).1)
  let E₂ := Finset.univ.filter fun y : D.selectedSubset n ↦
        ((D.selectedImageEquiv n).symm y).1 ∈
          D.approximation.conjugacyError (D.matchingIndex n)
            D.setup.distinguished (D.setup.embedΓ t)
  let EΓ := Finset.univ.filter fun x : (D.selectedComponent n).block ↦
        x.1 ∈
          D.approximation.conjugacyError (D.matchingIndex n)
            D.setup.distinguished (D.setup.embedΓ t)
  have hsubset : (Finset.univ.filter fun y : D.selectedSubset n ↦
        D.localizedGammaAct n t y ≠ D.transportedGammaCompletion n t y) ⊆
        E₀ ∪ (E₁ ∪ E₂) := by
      intro y hy
      simp only [E₀, E₁, E₂, Finset.mem_union, Finset.mem_filter,
        Finset.mem_univ, true_and] at hy ⊢
      by_cases hloc : (D.localizedGammaAct n t y).1 ≠
          D.localizedProductAct n (t, 1) y.1
      · exact Or.inl hloc
      by_cases hsrc : (D.transportedGammaCompletion n t y).1 ≠
          D.distinguishedPerm (D.matchingIndex n)
            (D.gammaAct n t ((D.selectedImageEquiv n).symm y).1)
      · exact Or.inr (Or.inl hsrc)
      · exact Or.inr (Or.inr (by
          simp only [SoficApproximation.conjugacyError, Finset.mem_filter,
            Finset.mem_univ, true_and]
          intro hgood
          apply hy
          apply Subtype.ext
          rw [not_ne_iff.mp hloc, not_ne_iff.mp hsrc]
          have hprod : D.setup.productEmbedding (t, 1) =
              D.setup.distinguished * D.setup.embedΓ t * D.setup.distinguished⁻¹ := by
            rw [D.setup.productEmbedding_eq_embedΓ]
            simpa using D.setup.compressedEnd_spec D.setup.distinguished
              D.setup.distinguished_mem t
          have hyq : D.distinguishedPerm (D.matchingIndex n)
              ((D.selectedImageEquiv n).symm y).1 = y.1 := by
            exact congrArg Subtype.val
              ((D.selectedImageEquiv n).apply_symm_apply y)
          rw [hyq] at hgood
          rw [localizedProductAct, hprod]
          exact hgood.symm))
  have hcard := (Finset.card_le_card hsubset).trans
    ((Finset.card_union_le E₀ (E₁ ∪ E₂)).trans
      (Nat.add_le_add_left (Finset.card_union_le E₁ E₂) E₀.card))
  have hE₂card : E₂.card = EΓ.card := by
    apply Finset.card_bij (fun y _ ↦ (D.selectedImageEquiv n).symm y)
    · intro y hy
      simpa only [E₂, EΓ, Finset.mem_filter, Finset.mem_univ, true_and] using hy
    · intro y _ z _ hyz
      exact (D.selectedImageEquiv n).symm.injective hyz
    · intro x hx
      refine ⟨D.selectedImageEquiv n x, ?_,
        (D.selectedImageEquiv n).symm_apply_apply x⟩
      simpa only [E₂, EΓ, Finset.mem_filter, Finset.mem_univ, true_and,
        Equiv.symm_apply_apply] using hx
  rw [hE₂card] at hcard
  calc
    ((Finset.univ.filter fun y : D.selectedSubset n ↦
        D.localizedGammaAct n t y ≠ D.transportedGammaCompletion n t y).card : ℝ) /
        (D.selectedSubset n).card ≤
        ((E₀.card + (E₁.card + EΓ.card) : ℕ) : ℝ) /
          (D.selectedSubset n).card := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast hcard
      · positivity
    _ = (E₀.card : ℝ) / (D.selectedSubset n).card +
        ((E₁.card : ℝ) / (D.selectedSubset n).card +
          (EΓ.card : ℝ) / (D.selectedSubset n).card) := by
      push_cast
      ring
    _ ≤ _ := by
      dsimp only [E₀, E₁, EΓ, localizedGammaAct]
      rw [D.selectedSubset_card]

theorem localized_to_completed_edit_negligible :
    Negligible (fun n ↦ ((D.selectedSubset n).card : ℝ)) fun n ↦
      ((generatorGraph
        (D.selectedFiniteModel n)
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
    (fun n ↦ ?_) hbound
  rw [D.selectedSubset_card]
  calc
    ((D.completedGammaGraph n).editDistance (D.selectedGraph n)
        (Equiv.refl _) : ℝ) / (D.selectedComponent n).block.card ≤
        (6 * D.localGraphBaseError n (D.selectedComponent n)) /
          (D.selectedComponent n).block.card := by
      apply div_le_div_of_nonneg_right
      · have htri := FiniteMultiGraph.editDistance_triangle
          (D.completedGammaGraph n) (D.transportedInducedGammaGraph n)
          (D.selectedGraph n) (Equiv.refl _) (Equiv.refl _)
        have h₁ := D.completed_to_induced_edit_le n
        have h₂ := D.induced_to_selected_edit_le n
        have htriReal :
            ((D.completedGammaGraph n).editDistance (D.selectedGraph n)
              (Equiv.refl _) : ℝ) ≤
              ((D.completedGammaGraph n).editDistance
                (D.transportedInducedGammaGraph n) (Equiv.refl _) : ℝ) +
              ((D.transportedInducedGammaGraph n).editDistance
                (D.selectedGraph n) (Equiv.refl _) : ℝ) := by
          exact_mod_cast htri
        have hedit : D.localGammaEditError n (D.selectedComponent n) ≤
            D.localGraphBaseError n (D.selectedComponent n) := by
          unfold localGraphBaseError
          positivity
        linarith
      · positivity
    _ = 6 * (D.localGraphBaseError n (D.selectedComponent n) /
        (D.selectedComponent n).block.card) := by ring

theorem selectedGraph_edit_negligible :
    Negligible (fun n ↦ ((D.selectedSubset n).card : ℝ)) fun n ↦
      ((generatorGraph
        (D.selectedFiniteModel n)
        D.setup.generatorsΓ (fun g ↦ D.selectedLocalization.completedMap n (g, 1))).editDistance
          (D.selectedGraph n) (Equiv.refl _) : ℕ) := by
  have hsum := Negligible.add D.localized_to_completed_edit_negligible
    D.completed_to_selected_edit_negligible
  refine Negligible.mono (fun n ↦ by positivity) (fun n ↦ by positivity)
    (fun n ↦ ?_) hsum
  exact_mod_cast FiniteMultiGraph.editDistance_triangle
    (generatorGraph
      (D.selectedFiniteModel n)
      D.setup.generatorsΓ (D.localizedGammaAct n))
    (D.completedGammaGraph n) (D.selectedGraph n) (Equiv.refl _) (Equiv.refl _)

end LocalCriterionData
end NonsoficGroupsExist
