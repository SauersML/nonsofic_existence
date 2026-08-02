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

/-- The exact vertex equivalence produced when both induced graphs are
transported to the selected target component. -/
noncomputable def selectedGraphEquiv (n : ℕ) :
    (((D.gammaDecomposition.modelGraph (D.matchingIndex n)).induce
      (D.selectedComponent n).block).vertex) ≃ D.selectedFiniteModel n :=
  (Equiv.refl (D.inducedGammaGraph n).vertex).symm.trans
    (D.selectedImageEquiv n)

noncomputable def selectedGraph (n : ℕ) : FiniteMultiGraph :=
  ((D.gammaDecomposition.modelGraph (D.matchingIndex n)).induce
    (D.selectedComponent n).block).transport
      (D.selectedFiniteModel n) (D.selectedGraphEquiv n)

theorem selectedGraph_expands (n : ℕ) :
    (D.selectedGraph n).HasCheegerLowerBound D.gammaDecomposition.cheeger := by
  exact FiniteMultiGraph.transport_hasCheegerLowerBound
    ((D.gammaDecomposition.modelGraph (D.matchingIndex n)).induce
      (D.selectedComponent n).block)
    (D.selectedFiniteModel n)
    (D.selectedGraphEquiv n)
    (by
      let y := BlockIndex.representative
        (D.gammaDecomposition.blocks (D.matchingIndex n)) (D.selectedComponent n)
      have h := D.gammaDecomposition.component_expands (D.matchingIndex n) y
      change ((D.gammaDecomposition.modelGraph (D.matchingIndex n)).induce
        ((D.gammaDecomposition.blocks (D.matchingIndex n)).block y)).HasCheegerLowerBound
          D.gammaDecomposition.cheeger at h
      rw [BlockIndex.block_representative] at h
      exact h)

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
      (Equiv.refl (D.selectedFiniteModel n)) ≤
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
      (D.selectedSourceFiniteModel n)
      D.setup.generatorsΓ (D.gammaCompletion n))
    (D.inducedGammaGraph n)
    (D.selectedFiniteModel n)
    (Equiv.refl _) (D.selectedImageEquiv n)
  have hconjugate := GeneratorGraphEditing.conjugateAction_editDistance
    (Y := D.selectedSourceFiniteModel n)
    (Z := D.selectedFiniteModel n)
    D.setup.generatorsΓ (D.selectedImageEquiv n) (D.gammaCompletion n)
    (D.transportedInducedGammaGraph n) (Equiv.refl (D.selectedFiniteModel n))
  have haction : GeneratorGraphEditing.conjugateAction
      (G := Γ) (Y := D.selectedSourceFiniteModel n) (Z := D.selectedFiniteModel n)
      (D.selectedImageEquiv n) (D.gammaCompletion n) =
        D.transportedGammaCompletion n := by
    funext g
    ext y
    rfl
  rw [haction] at hconjugate
  have hconjugate' :
      (D.completedGammaGraph n).editDistance (D.transportedInducedGammaGraph n)
          (Equiv.refl (D.selectedFiniteModel n)) =
        ((generatorGraph
          (D.selectedSourceFiniteModel n)
          D.setup.generatorsΓ (D.gammaCompletion n)).transport
            (D.selectedFiniteModel n) (D.selectedImageEquiv n)).editDistance
          (D.transportedInducedGammaGraph n)
            (Equiv.refl (D.selectedFiniteModel n)) := by
    simpa only [completedGammaGraph, transportedGammaCompletion,
      GeneratorGraphEditing.conjugateAction] using hconjugate
  have htransport' :
      ((generatorGraph
          (D.selectedSourceFiniteModel n)
          D.setup.generatorsΓ (D.gammaCompletion n)).transport
            (D.selectedFiniteModel n) (D.selectedImageEquiv n)).editDistance
          (D.transportedInducedGammaGraph n)
            (Equiv.refl (D.selectedFiniteModel n)) =
        (generatorGraph
          (D.selectedSourceFiniteModel n)
          D.setup.generatorsΓ (D.gammaCompletion n)).editDistance
            (D.inducedGammaGraph n) (Equiv.refl _) := by
    have hequiv : (Equiv.refl (D.selectedSourceFiniteModel n)).symm.trans
        (D.selectedImageEquiv n) = D.selectedImageEquiv n := by
      ext x
      rfl
    have hgraph : (D.inducedGammaGraph n).transport (D.selectedFiniteModel n)
        ((Equiv.refl (D.selectedSourceFiniteModel n)).symm.trans
          (D.selectedImageEquiv n)) = D.transportedInducedGammaGraph n := by
      exact (congrArg (fun e ↦
        (D.inducedGammaGraph n).transport (D.selectedFiniteModel n) e)
        hequiv).trans rfl
    cases hgraph
    exact htransport
  rw [hconjugate', htransport']
  calc
    _ ≤ 4 * ((∑ t : D.setup.generatorsΓ,
      (Finset.univ.filter fun x : (D.selectedComponent n).block ↦
        (D.gammaCompletion n t.1 x).1 ≠
          D.gammaAct n t.1 x.1).card : ℕ) : ℝ) := by
      exact_mod_cast hbase
    _ ≤ 4 * ((∑ t : D.setup.generatorsΓ,
      (Finset.univ.filter fun x : (D.selectedComponent n).block ↦
        D.gammaAct n t.1 x.1 ∉
          (D.selectedComponent n).block).card : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_le_mul_left 4 hcompletion
    _ ≤ 4 * D.localGraphBaseError n (D.selectedComponent n) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      push_cast
      exact D.selected_gammaBoundary_le_graphError n

theorem induced_to_selected_edit_le (n : ℕ) :
    (D.transportedInducedGammaGraph n).editDistance (D.selectedGraph n)
      (Equiv.refl (D.selectedFiniteModel n)) ≤
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
  dsimp only [B] at htransport
  have htransport' :
      (D.transportedInducedGammaGraph n).editDistance (D.selectedGraph n)
          (Equiv.refl (D.selectedFiniteModel n)) =
        (D.inducedGammaGraph n).editDistance
          ((D.gammaDecomposition.modelGraph (D.matchingIndex n)).induce
            (D.selectedComponent n).block)
          (Equiv.refl _) := by
    change ((D.inducedGammaGraph n).transport
        (D.selectedFiniteModel n) (D.selectedImageEquiv n)).editDistance
          (((D.gammaDecomposition.modelGraph (D.matchingIndex n)).induce
            (D.selectedComponent n).block).transport
              (D.selectedFiniteModel n)
              ((Equiv.refl (D.inducedGammaGraph n).vertex).symm.trans
                (D.selectedImageEquiv n)))
          (Equiv.refl (D.selectedFiniteModel n)) =
      (D.inducedGammaGraph n).editDistance
        ((D.gammaDecomposition.modelGraph (D.matchingIndex n)).induce
          (D.selectedComponent n).block) (Equiv.refl _)
    exact htransport
  rw [htransport']
  change ((D.inducedGammaGraph n).editDistance
      ((D.gammaDecomposition.modelGraph (D.matchingIndex n)).induce B)
        (Equiv.refl _) : ℝ) ≤ _
  have hlocalReal : (WI.unmatchedCount : ℝ) ≤
      D.localGammaEditError n (D.selectedComponent n) := by
    unfold localGammaEditError
    exact_mod_cast hlocal
  calc
    _ ≤ (2 * WI.unmatchedCount : ℝ) := by exact_mod_cast hw
    _ ≤ 2 * D.localGammaEditError n (D.selectedComponent n) := by linarith

noncomputable abbrev localizedGammaAct (n : ℕ) (g : Γ) :
    Equiv.Perm (D.selectedSubset n) :=
  (D.selectedLocalization.completedMap n (g, 1))

noncomputable def gammaCompletionDisagreement (n : ℕ) (t : Γ) :
    Finset (D.selectedComponent n).block :=
  Finset.univ.filter fun x ↦
    (D.gammaCompletion n t x).1 ≠ D.gammaAct n t x.1

noncomputable def gammaBoundaryDisagreement (n : ℕ) (t : Γ) :
    Finset (D.selectedComponent n).block :=
  Finset.univ.filter fun x ↦
    D.gammaAct n t x.1 ∉ (D.selectedComponent n).block

noncomputable def selectedConjugacyError (n : ℕ) (t : Γ) :
    Finset (D.selectedComponent n).block :=
  Finset.univ.filter fun x ↦
    x.1 ∈ D.approximation.conjugacyError (D.matchingIndex n)
      D.setup.distinguished (D.setup.embedΓ t)

noncomputable def selectedError (n : ℕ) : ℝ :=
  D.componentSelectionError 0 n (D.selectedComponent n)

noncomputable def gammaBoundaryCount (n : ℕ)
    (g : D.setup.generatorsΓ) : ℝ :=
  (D.gammaBoundaryDisagreement n g.1).card

noncomputable def selectedConjugacyCount (n : ℕ)
    (g : D.setup.generatorsΓ) : ℝ :=
  (D.selectedConjugacyError n g.1).card

theorem gammaCompletionDisagreement_card_le (n : ℕ) (t : Γ) :
    (D.gammaCompletionDisagreement n t).card ≤
      (D.gammaBoundaryDisagreement n t).card := by
  unfold gammaCompletionDisagreement gammaBoundaryDisagreement
  exact D.gammaCompletion_disagreement_bound n t

theorem gammaBoundaryDisagreement_le_graphError (n : ℕ) (t : Γ)
    (ht : t ∈ D.setup.generatorsΓ) :
    ((D.gammaBoundaryDisagreement n t).card : ℝ) ≤
      D.localGraphBaseError n (D.selectedComponent n) := by
  let g : D.setup.generatorsΓ := ⟨t, ht⟩
  have hsingle : D.gammaBoundaryCount n g ≤
      ∑ a : D.setup.generatorsΓ, D.gammaBoundaryCount n a :=
    Finset.single_le_sum (fun _ _ ↦ by unfold gammaBoundaryCount; positivity)
      (Finset.mem_univ g)
  have hsum : (∑ a : D.setup.generatorsΓ, D.gammaBoundaryCount n a) ≤
      D.localGraphBaseError n (D.selectedComponent n) := by
    simpa only [gammaBoundaryCount, gammaBoundaryDisagreement] using
      D.selected_gammaBoundary_le_graphError n
  exact hsingle.trans hsum

theorem gammaCompletion_disagreement_le_selectionError (n : ℕ) (t : Γ)
    (ht : t ∈ D.setup.generatorsΓ) :
    (D.gammaCompletionDisagreement n t).card ≤
      D.selectedError n := by
  unfold selectedError
  have hcompletion : ((D.gammaCompletionDisagreement n t).card : ℝ) ≤
      (D.gammaBoundaryDisagreement n t).card := by
    exact_mod_cast D.gammaCompletionDisagreement_card_le n t
  exact hcompletion.trans ((D.gammaBoundaryDisagreement_le_graphError n t ht).trans
    (D.localGraphBaseError_le_componentSelectionError 0 n
      (D.selectedComponent n)))

theorem gammaCompletion_disagreement_negligible (t : Γ)
    (ht : t ∈ D.setup.generatorsΓ) :
    Vanishing fun n ↦
      ((D.gammaCompletionDisagreement n t).card : ℝ) /
        (D.selectedComponent n).block.card := by
  refine Vanishing.squeeze (fun n ↦ div_nonneg (by positivity) (by positivity))
    (fun n ↦ div_le_div_of_nonneg_right
      (D.gammaCompletion_disagreement_le_selectionError n t ht) (by positivity))
    (by simpa only [selectedError] using D.selectedComponent_error 0)

theorem transportedGammaCompletion_source_disagreement_negligible (t : Γ)
    (ht : t ∈ D.setup.generatorsΓ) :
    Vanishing fun n ↦
      ((Finset.univ.filter fun y : D.selectedSubset n ↦
        (D.transportedGammaCompletion n t y).1 ≠
          D.distinguishedPerm (D.matchingIndex n)
            (D.gammaAct n t ((D.selectedImageEquiv n).symm y).1)).card : ℝ) /
        (D.selectedSubset n).card := by
  apply Vanishing.congr (D.gammaCompletion_disagreement_negligible t ht)
  intro n
  have hcard :
      (Finset.univ.filter fun y : D.selectedSubset n ↦
        (D.transportedGammaCompletion n t y).1 ≠
          D.distinguishedPerm (D.matchingIndex n)
            (D.gammaAct n t ((D.selectedImageEquiv n).symm y).1)).card =
      (D.gammaCompletionDisagreement n t).card := by
    unfold gammaCompletionDisagreement
    apply Finset.card_bij (fun y _ ↦ (D.selectedImageEquiv n).symm y)
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
      simpa only [transportedGammaCompletion, Equiv.trans_apply,
        Equiv.symm_apply_apply, selectedImageEquiv_apply] using
          (D.distinguishedPerm (D.matchingIndex n)).injective.ne hx
  rw [hcard, D.selectedSubset_card]

theorem selected_conjugacyError_le_selectionError (n : ℕ) (t : Γ)
    (ht : t ∈ D.setup.generatorsΓ) :
    (D.selectedConjugacyError n t).card ≤
      D.selectedError n := by
  unfold selectedError
  let g : D.setup.generatorsΓ := ⟨t, ht⟩
  have hsingle : D.selectedConjugacyCount n g ≤
      ∑ a : D.setup.generatorsΓ, D.selectedConjugacyCount n a :=
    Finset.single_le_sum (fun _ _ ↦ by unfold selectedConjugacyCount; positivity)
      (Finset.mem_univ g)
  have hterm : (∑ a : D.setup.generatorsΓ, D.selectedConjugacyCount n a) ≤
      D.localConjugacyGraphError n (D.selectedComponent n) := by
    unfold localConjugacyGraphError
    simp only [selectedConjugacyCount, selectedConjugacyError]
    exact le_rfl
  have hconjugacyBase : D.localConjugacyGraphError n (D.selectedComponent n) ≤
      D.localGraphBaseError n (D.selectedComponent n) := by
    unfold localGraphBaseError
    have hgamma : 0 ≤ D.localGammaEditError n (D.selectedComponent n) := by
      unfold localGammaEditError
      positivity
    have hboundary : 0 ≤
        D.localGammaBoundaryError n (D.selectedComponent n) := by
      unfold localGammaBoundaryError
      positivity
    linarith
  exact hsingle.trans (hterm.trans (hconjugacyBase.trans
    (D.localGraphBaseError_le_componentSelectionError 0 n
      (D.selectedComponent n))))

theorem selected_conjugacyError_negligible (t : Γ)
    (ht : t ∈ D.setup.generatorsΓ) :
    Vanishing fun n ↦
      ((D.selectedConjugacyError n t).card : ℝ) /
        (D.selectedComponent n).block.card := by
  refine Vanishing.squeeze (fun n ↦ div_nonneg (by positivity) (by positivity))
    (fun n ↦ div_le_div_of_nonneg_right
      (D.selected_conjugacyError_le_selectionError n t ht) (by positivity))
    (by simpa only [selectedError] using D.selectedComponent_error 0)

theorem localized_to_completed_disagreement_negligible (t : Γ)
    (ht : t ∈ D.setup.generatorsΓ) :
    Vanishing fun n ↦
      ((Finset.univ.filter fun y : D.selectedSubset n ↦
        D.localizedGammaAct n t y ≠ D.transportedGammaCompletion n t y).card : ℝ) /
          (D.selectedSubset n).card := by
  have hA₀ := D.selectedLocalization.completedMap_disagreement_vanishing (t, 1)
  have hA : Vanishing fun n ↦
      ((Finset.univ.filter fun y : D.selectedSubset n ↦
        (D.localizedGammaAct n t y).1 ≠
          D.localizedProductAct n (t, 1) y.1).card : ℝ) /
        (D.selectedSubset n).card := by
    exact hA₀
  have hsource := D.transportedGammaCompletion_source_disagreement_negligible t ht
  have hconj₀ := D.selected_conjugacyError_negligible t ht
  have hconj : Vanishing fun n ↦
      ((D.selectedConjugacyError n t).card : ℝ) /
        (D.selectedSubset n).card := by
    apply Vanishing.congr hconj₀
    intro n
    rw [D.selectedSubset_card]
  have hall := Vanishing.add hA (Vanishing.add hsource hconj)
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
  let EΓ := D.selectedConjugacyError n t
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
          let x : D.approximation.model (D.matchingIndex n) :=
            ((D.selectedImageEquiv n).symm y).1
          change x ∈ D.approximation.conjugacyError (D.matchingIndex n)
            D.setup.distinguished (D.setup.embedΓ t)
          rw [SoficApproximation.conjugacyError, Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
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
              x = y.1 := by
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
      simpa only [E₂, EΓ, selectedConjugacyError, Finset.mem_filter,
        Finset.mem_univ, true_and] using hy
    · intro y _ z _ hyz
      exact (D.selectedImageEquiv n).symm.injective hyz
    · intro x hx
      refine ⟨D.selectedImageEquiv n x, ?_,
        (D.selectedImageEquiv n).symm_apply_apply x⟩
      simpa only [E₂, EΓ, selectedConjugacyError, Finset.mem_filter,
        Finset.mem_univ, true_and, Equiv.symm_apply_apply] using hx
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
      exact le_rfl

noncomputable def localizedGammaGraph (n : ℕ) : FiniteMultiGraph :=
  generatorGraph (D.selectedFiniteModel n) D.setup.generatorsΓ
    (D.localizedGammaAct n)

noncomputable def selectedCard (n : ℕ) : ℝ :=
  (D.selectedSubset n).card

noncomputable def localizedCompletedEdit (n : ℕ) : ℝ :=
  (D.localizedGammaGraph n).editDistance (D.completedGammaGraph n)
    (Equiv.refl (D.selectedFiniteModel n))

noncomputable def completedSelectedEdit (n : ℕ) : ℝ :=
  (D.completedGammaGraph n).editDistance (D.selectedGraph n)
    (Equiv.refl (D.selectedFiniteModel n))

noncomputable def localizedSelectedEdit (n : ℕ) : ℝ :=
  (D.localizedGammaGraph n).editDistance (D.selectedGraph n)
    (Equiv.refl (D.selectedFiniteModel n))

theorem localized_to_completed_edit_negligible :
    Negligible D.selectedCard D.localizedCompletedEdit := by
  have hsum := Negligible.sum (Finset.univ : Finset D.setup.generatorsΓ)
    (fun t n ↦ ((Finset.univ.filter fun y : D.selectedSubset n ↦
      D.localizedGammaAct n t.1 y ≠ D.transportedGammaCompletion n t.1 y).card : ℝ))
    (fun t _ ↦ D.localized_to_completed_disagreement_negligible t.1 t.2)
  refine Negligible.mono (fun n ↦ by
      unfold selectedCard
      rw [D.selectedSubset_card]
      exact_mod_cast (BlockIndex.block_nonempty
        (D.gammaDecomposition.blocks (D.matchingIndex n))
        (D.selectedComponent n)).card_pos)
    (fun n ↦ by unfold localizedCompletedEdit; positivity) (fun n ↦ ?_)
      (Negligible.const_mul 4 hsum)
  unfold localizedCompletedEdit localizedGammaGraph
  exact_mod_cast GeneratorGraphEditing.editDistance_le D.setup.generatorsΓ
    (D.localizedGammaAct n) (D.transportedGammaCompletion n)

theorem completed_to_selected_edit_negligible :
    Negligible D.selectedCard D.completedSelectedEdit := by
  have hbase : Vanishing fun n ↦
      D.localGraphBaseError n (D.selectedComponent n) /
        (D.selectedComponent n).block.card := by
    refine Vanishing.squeeze (fun n ↦ div_nonneg
      (D.localGraphBaseError_nonneg n (D.selectedComponent n)) (by positivity))
      (fun n ↦ ?_) (D.selectedComponent_error 0)
    apply div_le_div_of_nonneg_right
    · exact D.localGraphBaseError_le_componentSelectionError 0 n
        (D.selectedComponent n)
    · positivity
  have hbound := Vanishing.const_mul 6 hbase
  refine Vanishing.squeeze (fun n ↦ by
      unfold completedSelectedEdit selectedCard
      positivity)
    (fun n ↦ ?_) hbound
  unfold completedSelectedEdit selectedCard
  change (((D.completedGammaGraph n).editDistance (D.selectedGraph n)
      (Equiv.refl (D.selectedFiniteModel n)) : ℕ) : ℝ) /
        ((D.selectedSubset n).card : ℝ) ≤
      6 * (D.localGraphBaseError n (D.selectedComponent n) /
        ((D.selectedComponent n).block.card : ℝ))
  rw [D.selectedSubset_card]
  calc
    ((D.completedGammaGraph n).editDistance (D.selectedGraph n)
        (Equiv.refl _) : ℝ) / (D.selectedComponent n).block.card ≤
        (6 * D.localGraphBaseError n (D.selectedComponent n)) /
          (D.selectedComponent n).block.card := by
      apply div_le_div_of_nonneg_right
      · have htri := FiniteMultiGraph.editDistance_triangle
          (D.completedGammaGraph n) (D.transportedInducedGammaGraph n)
          (D.selectedGraph n) (Equiv.refl (D.selectedFiniteModel n))
            (Equiv.refl (D.selectedFiniteModel n))
        have h₁ := D.completed_to_induced_edit_le n
        have h₂ := D.induced_to_selected_edit_le n
        have htri' :
            (D.completedGammaGraph n).editDistance (D.selectedGraph n)
                (Equiv.refl (D.selectedFiniteModel n)) ≤
              (D.completedGammaGraph n).editDistance
                  (D.transportedInducedGammaGraph n)
                    (Equiv.refl (D.selectedFiniteModel n)) +
                (D.transportedInducedGammaGraph n).editDistance
                  (D.selectedGraph n) (Equiv.refl (D.selectedFiniteModel n)) := by
          have hrefl : (Equiv.refl (D.selectedFiniteModel n)).trans
              (Equiv.refl (D.selectedFiniteModel n)) =
                Equiv.refl (D.selectedFiniteModel n) := by
            ext x
            rfl
          exact Eq.mp (congrArg (fun e ↦
            (D.completedGammaGraph n).editDistance (D.selectedGraph n) e ≤
              (D.completedGammaGraph n).editDistance
                  (D.transportedInducedGammaGraph n)
                    (Equiv.refl (D.selectedFiniteModel n)) +
                (D.transportedInducedGammaGraph n).editDistance
                  (D.selectedGraph n) (Equiv.refl (D.selectedFiniteModel n))) hrefl) htri
        have htriReal :
            ((D.completedGammaGraph n).editDistance (D.selectedGraph n)
              (Equiv.refl _) : ℝ) ≤
              ((D.completedGammaGraph n).editDistance
                (D.transportedInducedGammaGraph n) (Equiv.refl _) : ℝ) +
              ((D.transportedInducedGammaGraph n).editDistance
                (D.selectedGraph n) (Equiv.refl _) : ℝ) := by
          exact_mod_cast htri'
        have h₁' :
            ((D.completedGammaGraph n).editDistance
              (D.transportedInducedGammaGraph n)
                (Equiv.refl (D.completedGammaGraph n).vertex) : ℝ) ≤
              4 * D.localGraphBaseError n (D.selectedComponent n) := by
          exact h₁
        have h₂' :
            ((D.transportedInducedGammaGraph n).editDistance
              (D.selectedGraph n)
                (Equiv.refl (D.transportedInducedGammaGraph n).vertex) : ℝ) ≤
              2 * D.localGammaEditError n (D.selectedComponent n) := by
          exact h₂
        have hedit : D.localGammaEditError n (D.selectedComponent n) ≤
            D.localGraphBaseError n (D.selectedComponent n) := by
          unfold localGraphBaseError
          have hconj : 0 ≤
              D.localConjugacyGraphError n (D.selectedComponent n) := by
            unfold localConjugacyGraphError
            positivity
          have hboundary : 0 ≤
              D.localGammaBoundaryError n (D.selectedComponent n) := by
            unfold localGammaBoundaryError
            positivity
          linarith
        linarith [htriReal, h₁', h₂', hedit]
      · positivity
    _ = 6 * (D.localGraphBaseError n (D.selectedComponent n) /
        (D.selectedComponent n).block.card) := by ring

theorem selectedGraph_edit_negligible :
    Negligible D.selectedCard D.localizedSelectedEdit := by
  have hsum := Negligible.add D.localized_to_completed_edit_negligible
    D.completed_to_selected_edit_negligible
  refine Negligible.mono (fun n ↦ by
      unfold selectedCard
      rw [D.selectedSubset_card]
      exact_mod_cast (BlockIndex.block_nonempty
        (D.gammaDecomposition.blocks (D.matchingIndex n))
        (D.selectedComponent n)).card_pos) (fun n ↦ by
          unfold localizedSelectedEdit
          positivity)
    (fun n ↦ ?_) hsum
  unfold localizedSelectedEdit localizedCompletedEdit completedSelectedEdit
  exact_mod_cast FiniteMultiGraph.editDistance_triangle
    (D.localizedGammaGraph n)
    (D.completedGammaGraph n) (D.selectedGraph n) (Equiv.refl _) (Equiv.refl _)

end LocalCriterionData
end NonsoficGroupsExist
