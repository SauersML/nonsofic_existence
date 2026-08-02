import NonsoficGroupsExist.MatchingPreparation
import NonsoficGroupsExist.SelectionOutput

/-!
# Diagonal selection of a localized component

The acceptable transported source components are disjoint and carry a fixed
proportion of the model.  This file assigns to each component all invariance,
multiplication, faithfulness, and matching errors up to a finite enumeration
level, then applies the weighted diagonal selection lemma.
-/

namespace NonsoficGroupsExist

open scoped BigOperators symmDiff

namespace LocalCriterionData

variable {G Γ J : Type} [Group G] [Group Γ] [Group J]
  [Countable Γ] [Countable J]
variable (D : LocalCriterionData G Γ J)

noncomputable def productEnumeration (_D : LocalCriterionData G Γ J) : ℕ → Γ × J :=
  Classical.choose (exists_surjective_nat (Γ × J))

theorem productEnumeration_surjective : Function.Surjective D.productEnumeration :=
  Classical.choose_spec (exists_surjective_nat (Γ × J))

noncomputable def componentPredicateCount (n : ℕ)
    (B : D.gammaDecomposition.componentIndex (D.matchingIndex n))
    (p : D.approximation.model (D.matchingIndex n) → Prop)
    [DecidablePred p] : ℕ :=
  (Finset.univ.filter fun x : B.block ↦
      p (D.distinguishedPerm (D.matchingIndex n) x.1)).card

omit [Countable Γ] [Countable J] in
theorem sum_componentPredicateCount_le (n : ℕ)
    (p : D.approximation.model (D.matchingIndex n) → Prop) [DecidablePred p] :
    (∑ B ∈ D.acceptableComponents (D.matchingIndex n)
      (D.matchingThreshold (D.matchingIndex n)),
      (D.componentPredicateCount n B p : ℝ)) ≤
        ((Finset.univ.filter p).card : ℝ) := by
  let P := D.gammaDecomposition.blocks (D.matchingIndex n)
  let q := D.distinguishedPerm (D.matchingIndex n)
  have hsub : (∑ B ∈ D.acceptableComponents (D.matchingIndex n)
      (D.matchingThreshold (D.matchingIndex n)),
      (D.componentPredicateCount n B p : ℝ)) ≤
      ∑ B : D.gammaDecomposition.componentIndex (D.matchingIndex n),
        (D.componentPredicateCount n B p : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ ↦ by positivity)
  have hpartition :
      (∑ B : D.gammaDecomposition.componentIndex (D.matchingIndex n),
        (D.componentPredicateCount n B p : ℝ)) =
        ((Finset.univ.filter fun x ↦ p (q x)).card : ℝ) := by
    unfold componentPredicateCount
    have hpartition := BlockIndex.sum_card_filter
      (D.gammaDecomposition.blocks (D.matchingIndex n))
      (fun x ↦ p (D.distinguishedPerm (D.matchingIndex n) x))
    convert hpartition using 1
    norm_cast
  have hpreimage : ((Finset.univ.filter fun x ↦ p (q x)).card : ℝ) =
      ((Finset.univ.filter p).card : ℝ) := by
    let A : Finset (D.approximation.model (D.matchingIndex n)) :=
      Finset.univ.filter p
    have heq : (Finset.univ.filter fun x ↦ p (q x)) = permutationPreimage q A := by
      ext x
      simp [A, permutationPreimage]
    rw [heq, permutationPreimage_card]
  calc
    _ ≤ ∑ B : D.gammaDecomposition.componentIndex (D.matchingIndex n),
        (D.componentPredicateCount n B p : ℝ) := hsub
    _ = ((Finset.univ.filter fun x ↦ p (q x)).card : ℝ) := hpartition
    _ = ((Finset.univ.filter p).card : ℝ) := hpreimage

omit [Countable Γ] [Countable J] in
theorem sum_componentPredicateCount_mem_le (n : ℕ)
    (E : Finset (D.approximation.model (D.matchingIndex n))) :
    (∑ B ∈ D.acceptableComponents (D.matchingIndex n)
      (D.matchingThreshold (D.matchingIndex n)),
      (D.componentPredicateCount n B (fun y ↦ y ∈ E) : ℝ)) ≤
        (E.card : ℝ) := by
  have h := D.sum_componentPredicateCount_le n (fun y ↦ y ∈ E)
  have hfilter : Finset.univ.filter (fun y ↦ y ∈ E) = E := by
    ext y
    simp
  calc
    _ ≤ ((Finset.univ.filter fun y ↦ y ∈ E).card : ℝ) := h
    _ = (E.card : ℝ) := by rw [hfilter]

noncomputable def localInvariantError (n i : ℕ)
    (B : D.gammaDecomposition.componentIndex (D.matchingIndex n)) : ℝ :=
  D.componentPredicateCount n B fun y ↦
    y ∈ wordCrossing (D.transportedBlocks n)
      (D.localizedProductAct n (D.productEnumeration i))

noncomputable def localMultiplicationError (n i j : ℕ)
    (B : D.gammaDecomposition.componentIndex (D.matchingIndex n)) : ℝ :=
  D.componentPredicateCount n B fun y ↦
    y ∈ D.approximation.multiplicationError (D.matchingIndex n)
      (D.setup.productEmbedding (D.productEnumeration i))
      (D.setup.productEmbedding (D.productEnumeration j))

noncomputable def localFixedError (n i : ℕ)
    (B : D.gammaDecomposition.componentIndex (D.matchingIndex n)) : ℝ := by
  classical
  exact if D.productEnumeration i = 1 then 0 else
    D.componentPredicateCount n B fun y ↦
      y ∈ D.approximation.fixedError (D.matchingIndex n)
        (D.setup.productEmbedding (D.productEnumeration i))

noncomputable def localGammaEditError (n : ℕ)
    (B : D.gammaDecomposition.componentIndex (D.matchingIndex n)) : ℝ :=
  (((D.gammaDecomposition.editWitness (D.matchingIndex n)).sourceUnmatched.filter
    fun e ↦ (generatorGraph
      ((D.approximation.comap D.setup.embedΓ D.setup.embedΓ_injective).model
        (D.matchingIndex n))
      D.setup.generatorsΓ
      ((D.approximation.comap D.setup.embedΓ D.setup.embedΓ_injective).map
        (D.matchingIndex n))).first e ∈
        B.block).card : ℝ) +
  (((D.gammaDecomposition.editWitness (D.matchingIndex n)).targetUnmatched.filter
    fun e ↦ (D.gammaDecomposition.modelGraph (D.matchingIndex n)).first e ∈
      B.block).card : ℝ)

noncomputable def localConjugacyGraphError (n : ℕ)
    (B : D.gammaDecomposition.componentIndex (D.matchingIndex n)) : ℝ :=
  ∑ t : D.setup.generatorsΓ,
    ((Finset.univ.filter fun x : B.block ↦
        x.1 ∈ D.approximation.conjugacyError (D.matchingIndex n)
          D.setup.distinguished (D.setup.embedΓ t.1)).card : ℝ)

noncomputable def localGammaBoundaryError (n : ℕ)
    (B : D.gammaDecomposition.componentIndex (D.matchingIndex n)) : ℝ :=
  ∑ t : D.setup.generatorsΓ,
    ((Finset.univ.filter fun x : B.block ↦
      (D.gammaDecomposition.blocks (D.matchingIndex n)).block
          ((D.approximation.comap D.setup.embedΓ D.setup.embedΓ_injective).map
            (D.matchingIndex n) t.1 x.1) ≠
            (D.gammaDecomposition.blocks (D.matchingIndex n)).block x.1).card : ℝ)

noncomputable def localGraphBaseError (n : ℕ)
    (B : D.gammaDecomposition.componentIndex (D.matchingIndex n)) : ℝ :=
  D.localGammaEditError n B + D.localConjugacyGraphError n B
    + D.localGammaBoundaryError n B

noncomputable def componentSelectionError (r n : ℕ)
    (B : D.gammaDecomposition.componentIndex (D.matchingIndex n)) : ℝ :=
  ((D.matchImage (D.matchingIndex n) B ∆
    D.matchTarget (D.matchingIndex n) B).card : ℝ) +
  D.localGraphBaseError n B +
  (∑ i ∈ Finset.range (r + 1), D.localInvariantError n i B) +
  (∑ i ∈ Finset.range (r + 1), ∑ j ∈ Finset.range (r + 1),
    D.localMultiplicationError n i j B) +
  ∑ i ∈ Finset.range (r + 1), D.localFixedError n i B

theorem localInvariantError_nonneg (n i : ℕ)
    (B : D.gammaDecomposition.componentIndex (D.matchingIndex n)) :
    0 ≤ D.localInvariantError n i B := by
  unfold localInvariantError componentPredicateCount
  positivity

theorem localMultiplicationError_nonneg (n i j : ℕ)
    (B : D.gammaDecomposition.componentIndex (D.matchingIndex n)) :
    0 ≤ D.localMultiplicationError n i j B := by
  unfold localMultiplicationError componentPredicateCount
  positivity

theorem localFixedError_nonneg (n i : ℕ)
    (B : D.gammaDecomposition.componentIndex (D.matchingIndex n)) :
    0 ≤ D.localFixedError n i B := by
  classical
  unfold localFixedError componentPredicateCount
  split_ifs <;> positivity

omit [Countable Γ] [Countable J] in
theorem localGraphBaseError_nonneg (n : ℕ)
    (B : D.gammaDecomposition.componentIndex (D.matchingIndex n)) :
    0 ≤ D.localGraphBaseError n B := by
  unfold localGraphBaseError localGammaEditError localConjugacyGraphError
    localGammaBoundaryError
  positivity

theorem componentSelectionError_nonneg (r n : ℕ)
    (B : D.gammaDecomposition.componentIndex (D.matchingIndex n)) :
    0 ≤ D.componentSelectionError r n B := by
  have hmatch : 0 ≤ ((D.matchImage (D.matchingIndex n) B ∆
      D.matchTarget (D.matchingIndex n) B).card : ℝ) := by positivity
  have hinvariant : 0 ≤ ∑ i ∈ Finset.range (r + 1),
      D.localInvariantError n i B :=
    Finset.sum_nonneg fun i _ ↦ D.localInvariantError_nonneg n i B
  have hmultiplication : 0 ≤ ∑ i ∈ Finset.range (r + 1),
      ∑ j ∈ Finset.range (r + 1), D.localMultiplicationError n i j B :=
    Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
      D.localMultiplicationError_nonneg n i j B
  have hfixed : 0 ≤ ∑ i ∈ Finset.range (r + 1), D.localFixedError n i B :=
    Finset.sum_nonneg fun i _ ↦ D.localFixedError_nonneg n i B
  unfold componentSelectionError
  linarith [D.localGraphBaseError_nonneg n B]

theorem componentSelectionError_mono {r r' : ℕ} (hrr : r ≤ r') (n : ℕ)
    (B : D.gammaDecomposition.componentIndex (D.matchingIndex n)) :
    D.componentSelectionError r n B ≤ D.componentSelectionError r' n B := by
  have hrange : Finset.range (r + 1) ⊆ Finset.range (r' + 1) :=
    Finset.range_mono (Nat.add_le_add_right hrr 1)
  have hinvariant :
      (∑ i ∈ Finset.range (r + 1), D.localInvariantError n i B) ≤
        ∑ i ∈ Finset.range (r' + 1), D.localInvariantError n i B :=
    Finset.sum_le_sum_of_subset_of_nonneg hrange (fun _ _ _ ↦ by
      exact D.localInvariantError_nonneg _ _ _)
  have hmultiplicationInner (i : ℕ) :
      (∑ j ∈ Finset.range (r + 1), D.localMultiplicationError n i j B) ≤
        ∑ j ∈ Finset.range (r' + 1), D.localMultiplicationError n i j B :=
    Finset.sum_le_sum_of_subset_of_nonneg hrange (fun _ _ _ ↦ by
      exact D.localMultiplicationError_nonneg _ _ _ _)
  have hmultiplication :
      (∑ i ∈ Finset.range (r + 1), ∑ j ∈ Finset.range (r + 1),
        D.localMultiplicationError n i j B) ≤
      ∑ i ∈ Finset.range (r' + 1), ∑ j ∈ Finset.range (r' + 1),
        D.localMultiplicationError n i j B := by
    calc
      _ ≤ ∑ i ∈ Finset.range (r + 1), ∑ j ∈ Finset.range (r' + 1),
          D.localMultiplicationError n i j B :=
        Finset.sum_le_sum fun i _ ↦ hmultiplicationInner i
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hrange (fun _ _ _ ↦
        Finset.sum_nonneg fun _ _ ↦ by
          exact D.localMultiplicationError_nonneg _ _ _ _)
  have hfixed :
      (∑ i ∈ Finset.range (r + 1), D.localFixedError n i B) ≤
        ∑ i ∈ Finset.range (r' + 1), D.localFixedError n i B :=
    Finset.sum_le_sum_of_subset_of_nonneg hrange (fun _ _ _ ↦ by
      exact D.localFixedError_nonneg _ _ _)
  unfold componentSelectionError
  exact add_le_add
    (add_le_add
      (add_le_add (add_le_add le_rfl le_rfl) hinvariant) hmultiplication)
    hfixed

theorem sum_localInvariantError_negligible (i : ℕ) :
    Negligible (fun n ↦ D.N (D.matchingIndex n)) fun n ↦
      ∑ B ∈ D.acceptableComponents (D.matchingIndex n)
        (D.matchingThreshold (D.matchingIndex n)), D.localInvariantError n i B := by
  refine Negligible.mono (fun n ↦ D.matchingIndex_card_pos n)
    (fun n ↦ Finset.sum_nonneg fun B _ ↦ D.localInvariantError_nonneg n i B)
    (fun n ↦ ?_)
    (D.transportedBlocks_almost_invariant (D.productEnumeration i))
  simpa only [localInvariantError] using D.sum_componentPredicateCount_mem_le n
    (wordCrossing (D.transportedBlocks n)
      (D.localizedProductAct n (D.productEnumeration i)))

theorem sum_localMultiplicationError_negligible (i j : ℕ) :
    Negligible (fun n ↦ D.N (D.matchingIndex n)) fun n ↦
      ∑ B ∈ D.acceptableComponents (D.matchingIndex n)
        (D.matchingThreshold (D.matchingIndex n)),
        D.localMultiplicationError n i j B := by
  let gi := D.setup.productEmbedding (D.productEnumeration i)
  let gj := D.setup.productEmbedding (D.productEnumeration j)
  have hglobal := Negligible.shift
    (D.approximation.multiplicationError_negligible gi gj) D.matchingStart
  refine Negligible.mono (fun n ↦ D.matchingIndex_card_pos n)
    (fun n ↦ Finset.sum_nonneg fun B _ ↦
      D.localMultiplicationError_nonneg n i j B) (fun n ↦ ?_) hglobal
  simpa only [localMultiplicationError, gi, gj, matchingIndex] using
    D.sum_componentPredicateCount_mem_le n
      (D.approximation.multiplicationError (D.matchingIndex n) gi gj)

theorem sum_localFixedError_negligible (i : ℕ) :
    Negligible (fun n ↦ D.N (D.matchingIndex n)) fun n ↦
      ∑ B ∈ D.acceptableComponents (D.matchingIndex n)
        (D.matchingThreshold (D.matchingIndex n)), D.localFixedError n i B := by
  by_cases hi : D.productEnumeration i = 1
  · simpa [localFixedError, hi] using
      (Negligible.zero : Negligible (fun n ↦ D.N (D.matchingIndex n)) (fun _ ↦ 0))
  · have himage : D.setup.productEmbedding (D.productEnumeration i) ≠ 1 := by
      intro h
      exact hi (D.setup.productEmbedding_injective (by simpa using h))
    have hglobal := Negligible.shift
      (D.approximation.fixedError_negligible
        (D.setup.productEmbedding (D.productEnumeration i)) himage) D.matchingStart
    refine Negligible.mono (fun n ↦ D.matchingIndex_card_pos n)
      (fun n ↦ Finset.sum_nonneg fun B _ ↦ D.localFixedError_nonneg n i B)
      (fun n ↦ ?_) hglobal
    simpa only [localFixedError, hi, if_false, matchingIndex] using
      D.sum_componentPredicateCount_mem_le n
        (D.approximation.fixedError (D.matchingIndex n)
          (D.setup.productEmbedding (D.productEnumeration i)))

omit [Countable Γ] [Countable J] in
theorem localGraphBaseError_sum_negligible :
    Negligible (fun n ↦ D.N (D.matchingIndex n)) fun n ↦
      ∑ B ∈ D.acceptableComponents (D.matchingIndex n)
        (D.matchingThreshold (D.matchingIndex n)), D.localGraphBaseError n B := by
  classical
  have hedit0 := D.gammaDecomposition.unmatched_negligible
  have hedit := Negligible.shift hedit0 D.matchingStart
  have hconjEach (t : D.setup.generatorsΓ) := Negligible.shift
    (D.approximation.conjugacyError_negligible D.setup.distinguished
      (D.setup.embedΓ t.1)) D.matchingStart
  have hconj := Negligible.sum (Finset.univ : Finset D.setup.generatorsΓ)
    (fun t n ↦ ((D.approximation.conjugacyError (D.matchingIndex n)
      D.setup.distinguished (D.setup.embedΓ t.1)).card : ℝ))
    (fun t _ ↦ hconjEach t)
  have hboundaryEach (t : D.setup.generatorsΓ) := Negligible.shift
    (D.gammaDecomposition.almost_invariant t.1 t.2) D.matchingStart
  have hboundary := Negligible.sum (Finset.univ : Finset D.setup.generatorsΓ)
    (fun t n ↦ ((wordCrossing
      (D.gammaDecomposition.blocks (D.matchingIndex n))
      ((D.approximation.comap D.setup.embedΓ D.setup.embedΓ_injective).map
        (D.matchingIndex n) t.1)).card : ℝ))
    (fun t _ ↦ by
      have ht := hboundaryEach t
      apply Negligible.congr ht
      intro n
      norm_cast)
  have hbound := Negligible.add (Negligible.add hedit hconj) hboundary
  refine Negligible.mono (fun n ↦ D.matchingIndex_card_pos n)
    (fun n ↦ Finset.sum_nonneg fun B _ ↦ D.localGraphBaseError_nonneg n B)
    (fun n ↦ ?_) hbound
  let P := D.gammaDecomposition.blocks (D.matchingIndex n)
  let W := D.gammaDecomposition.editWitness (D.matchingIndex n)
  have hsourceAll := BlockIndex.sum_card_filter_mem_block P W.sourceUnmatched
    (fun e ↦ (generatorGraph
      ((D.approximation.comap D.setup.embedΓ D.setup.embedΓ_injective).model
        (D.matchingIndex n))
      D.setup.generatorsΓ
      ((D.approximation.comap D.setup.embedΓ D.setup.embedΓ_injective).map
        (D.matchingIndex n))).first e)
  have htargetAll := BlockIndex.sum_card_filter_mem_block P W.targetUnmatched
    (fun e ↦ (D.gammaDecomposition.modelGraph (D.matchingIndex n)).first e)
  have heditLocal : (∑ B ∈ D.acceptableComponents (D.matchingIndex n)
      (D.matchingThreshold (D.matchingIndex n)), D.localGammaEditError n B) ≤
      (W.unmatchedCount : ℝ) := by
    have hsub : (∑ B ∈ D.acceptableComponents (D.matchingIndex n)
        (D.matchingThreshold (D.matchingIndex n)), D.localGammaEditError n B) ≤
        ∑ B : D.gammaDecomposition.componentIndex (D.matchingIndex n),
          D.localGammaEditError n B :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ ↦ by unfold localGammaEditError; positivity)
    have hsourceReal : (∑ C : BlockIndex P,
        ((W.sourceUnmatched.filter fun e ↦
          (generatorGraph
            ((D.approximation.comap D.setup.embedΓ D.setup.embedΓ_injective).model
              (D.matchingIndex n))
            D.setup.generatorsΓ
            ((D.approximation.comap D.setup.embedΓ D.setup.embedΓ_injective).map
              (D.matchingIndex n))).first e ∈ C.block).card : ℝ)) ≤
        (W.sourceUnmatched.card : ℝ) := by
      exact_mod_cast hsourceAll
    have htargetReal : (∑ C : BlockIndex P,
        ((W.targetUnmatched.filter fun e ↦
          (D.gammaDecomposition.modelGraph (D.matchingIndex n)).first e ∈
            C.block).card : ℝ)) ≤ (W.targetUnmatched.card : ℝ) := by
      exact_mod_cast htargetAll
    have hall : (∑ B : D.gammaDecomposition.componentIndex (D.matchingIndex n),
        D.localGammaEditError n B) ≤
        (W.sourceUnmatched.card : ℝ) + (W.targetUnmatched.card : ℝ) := by
      unfold localGammaEditError
      simp_rw [Finset.sum_add_distrib]
      exact add_le_add hsourceReal htargetReal
    unfold EdgeEditWitness.unmatchedCount
    push_cast
    exact hsub.trans hall
  have hconjLocal : (∑ B ∈ D.acceptableComponents (D.matchingIndex n)
      (D.matchingThreshold (D.matchingIndex n)), D.localConjugacyGraphError n B) ≤
      ∑ t : D.setup.generatorsΓ,
        ((D.approximation.conjugacyError (D.matchingIndex n)
          D.setup.distinguished (D.setup.embedΓ t.1)).card : ℝ) := by
    simp_rw [localConjugacyGraphError]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro t _
    have hsub : (∑ B ∈ D.acceptableComponents (D.matchingIndex n)
        (D.matchingThreshold (D.matchingIndex n)),
        ((Finset.univ.filter fun x : B.block ↦
          x.1 ∈ D.approximation.conjugacyError (D.matchingIndex n)
            D.setup.distinguished (D.setup.embedΓ t.1)).card : ℝ)) ≤
        ∑ B : D.gammaDecomposition.componentIndex (D.matchingIndex n),
        ((Finset.univ.filter fun x : B.block ↦
          x.1 ∈ D.approximation.conjugacyError (D.matchingIndex n)
            D.setup.distinguished (D.setup.embedΓ t.1)).card : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ ↦ by positivity)
    exact hsub.trans (by
      let E := D.approximation.conjugacyError (D.matchingIndex n)
        D.setup.distinguished (D.setup.embedΓ t.1)
      have hpartition := BlockIndex.sum_card_filter
        (D.gammaDecomposition.blocks (D.matchingIndex n)) (fun x ↦ x ∈ E)
      have hpartition' : (∑ B : D.gammaDecomposition.componentIndex
          (D.matchingIndex n),
          ((Finset.univ.filter fun x : B.block ↦ x.1 ∈ E).card : ℝ)) =
          ((D.approximation.conjugacyError (D.matchingIndex n)
            D.setup.distinguished (D.setup.embedΓ t.1)).card : ℝ) := by
        calc
          _ = ((Finset.univ.filter fun x ↦ x ∈ E).card : ℝ) := hpartition
          _ = (E.card : ℝ) := by
            norm_cast
            apply congrArg Finset.card
            ext x
            simp
          _ = _ := rfl
      exact hpartition'.le)
  have hboundaryLocal : (∑ B ∈ D.acceptableComponents (D.matchingIndex n)
      (D.matchingThreshold (D.matchingIndex n)), D.localGammaBoundaryError n B) ≤
      ∑ t : D.setup.generatorsΓ,
        ((wordCrossing (D.gammaDecomposition.blocks (D.matchingIndex n))
          ((D.approximation.comap D.setup.embedΓ D.setup.embedΓ_injective).map
            (D.matchingIndex n) t.1)).card : ℝ) := by
    simp_rw [localGammaBoundaryError]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro t _
    let p : (D.approximation.comap D.setup.embedΓ D.setup.embedΓ_injective).model
        (D.matchingIndex n) → Prop := fun x ↦
      (D.gammaDecomposition.blocks (D.matchingIndex n)).block
        ((D.approximation.comap D.setup.embedΓ D.setup.embedΓ_injective).map
          (D.matchingIndex n) t.1 x) ≠
          (D.gammaDecomposition.blocks (D.matchingIndex n)).block x
    have hsub : (∑ B ∈ D.acceptableComponents (D.matchingIndex n)
        (D.matchingThreshold (D.matchingIndex n)),
        ((Finset.univ.filter fun x : B.block ↦ p x.1).card : ℝ)) ≤
        ∑ B : D.gammaDecomposition.componentIndex (D.matchingIndex n),
          ((Finset.univ.filter fun x : B.block ↦ p x.1).card : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ ↦ by positivity)
    have hpartition := BlockIndex.sum_card_filter
      (D.gammaDecomposition.blocks (D.matchingIndex n)) p
    have hfilter : Finset.univ.filter p =
        wordCrossing (D.gammaDecomposition.blocks (D.matchingIndex n))
          ((D.approximation.comap D.setup.embedΓ D.setup.embedΓ_injective).map
            (D.matchingIndex n) t.1) := by
      ext x
      simp only [p, wordCrossing, Finset.mem_filter, Finset.mem_univ, true_and]
    have htotal : (∑ B : D.gammaDecomposition.componentIndex (D.matchingIndex n),
        ((Finset.univ.filter fun x : B.block ↦ p x.1).card : ℝ)) =
        ((wordCrossing (D.gammaDecomposition.blocks (D.matchingIndex n))
          ((D.approximation.comap D.setup.embedΓ D.setup.embedΓ_injective).map
            (D.matchingIndex n) t.1)).card : ℝ) := by
      calc
        _ = ((Finset.univ.filter p).card : ℝ) := hpartition
        _ = _ := by rw [hfilter]
    exact hsub.trans htotal.le
  unfold localGraphBaseError
  simp_rw [Finset.sum_add_distrib]
  exact add_le_add (add_le_add heditLocal hconjLocal) hboundaryLocal

theorem componentSelectionError_sum_negligible (r : ℕ) :
    Negligible (fun n ↦ D.N (D.matchingIndex n)) fun n ↦
      ∑ B ∈ D.acceptableComponents (D.matchingIndex n)
        (D.matchingThreshold (D.matchingIndex n)),
        D.componentSelectionError r n B := by
  have hinv := Negligible.sum (Finset.range (r + 1))
    (fun i n ↦ ∑ B ∈ D.acceptableComponents (D.matchingIndex n)
      (D.matchingThreshold (D.matchingIndex n)), D.localInvariantError n i B)
    (fun i _ ↦ D.sum_localInvariantError_negligible i)
  have hmulInner (i : ℕ) := Negligible.sum (Finset.range (r + 1))
    (fun j n ↦ ∑ B ∈ D.acceptableComponents (D.matchingIndex n)
      (D.matchingThreshold (D.matchingIndex n)),
      D.localMultiplicationError n i j B)
    (fun j _ ↦ D.sum_localMultiplicationError_negligible i j)
  have hmul := Negligible.sum (Finset.range (r + 1))
    (fun i n ↦ ∑ j ∈ Finset.range (r + 1),
      ∑ B ∈ D.acceptableComponents (D.matchingIndex n)
        (D.matchingThreshold (D.matchingIndex n)),
        D.localMultiplicationError n i j B)
    (fun i _ ↦ hmulInner i)
  have hfixed := Negligible.sum (Finset.range (r + 1))
    (fun i n ↦ ∑ B ∈ D.acceptableComponents (D.matchingIndex n)
      (D.matchingThreshold (D.matchingIndex n)), D.localFixedError n i B)
    (fun i _ ↦ D.sum_localFixedError_negligible i)
  have hall := Negligible.add
    (Negligible.add
      (Negligible.add D.acceptable_symmDiff_sum_negligible
        D.localGraphBaseError_sum_negligible) hinv)
    (Negligible.add hmul hfixed)
  apply Negligible.congr hall
  intro n
  let A := D.acceptableComponents (D.matchingIndex n)
    (D.matchingThreshold (D.matchingIndex n))
  let I := Finset.range (r + 1)
  have hinvariant :
      (∑ B ∈ A, ∑ i ∈ I, D.localInvariantError n i B) =
        ∑ i ∈ I, ∑ B ∈ A, D.localInvariantError n i B := by
    rw [Finset.sum_comm]
  have hmultiplication :
      (∑ B ∈ A, ∑ i ∈ I, ∑ j ∈ I,
        D.localMultiplicationError n i j B) =
        ∑ i ∈ I, ∑ j ∈ I, ∑ B ∈ A,
          D.localMultiplicationError n i j B := by
    calc
      _ = ∑ i ∈ I, ∑ B ∈ A, ∑ j ∈ I,
          D.localMultiplicationError n i j B := by rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
  have hfixed :
      (∑ B ∈ A, ∑ i ∈ I, D.localFixedError n i B) =
        ∑ i ∈ I, ∑ B ∈ A, D.localFixedError n i B := by
    rw [Finset.sum_comm]
  unfold componentSelectionError
  simp_rw [Finset.sum_add_distrib]
  rw [hinvariant, hmultiplication, hfixed]
  ring

omit [Countable Γ] [Countable J] in
theorem acceptable_small_mass_negligible (M : ℕ) :
    Negligible (fun n ↦ D.N (D.matchingIndex n)) fun n ↦
      ∑ B ∈ D.acceptableComponents (D.matchingIndex n)
        (D.matchingThreshold (D.matchingIndex n)),
        (if (B.block.card : ℝ) ≤ M then (B.block.card : ℝ) else 0) := by
  classical
  letI : Infinite Γ := D.setup.infiniteΓ
  have hsmall0 := D.gammaDecomposition.smallBlockVertices_negligible
    D.setup.generatorsΓ_symmetric D.setup.generatorsΓ_generate M
  have hsmall := Negligible.shift hsmall0 D.matchingStart
  refine Negligible.mono (fun n ↦ D.matchingIndex_card_pos n)
    (fun n ↦ by positivity) (fun n ↦ ?_) hsmall
  have hsub : (∑ B ∈ D.acceptableComponents (D.matchingIndex n)
      (D.matchingThreshold (D.matchingIndex n)),
      (if (B.block.card : ℝ) ≤ M then (B.block.card : ℝ) else 0)) ≤
      ∑ B : D.gammaDecomposition.componentIndex (D.matchingIndex n),
        (if (B.block.card : ℝ) ≤ M then (B.block.card : ℝ) else 0) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro B _ _
    split_ifs <;> positivity
  calc
    _ ≤ _ := hsub
    _ = ((smallBlockVertices (D.gammaDecomposition.blocks (D.matchingIndex n)) M).card : ℝ) :=
      sum_smallBlock_card _ _

theorem exists_selectedComponent :
    ∃ sel : ∀ n, D.gammaDecomposition.componentIndex (D.matchingIndex n),
      (∀ n, sel n ∈ D.acceptableComponents (D.matchingIndex n)
        (D.matchingThreshold (D.matchingIndex n))) ∧
      (∀ r, Vanishing fun n ↦
        D.componentSelectionError r n (sel n) / (sel n).block.card) ∧
      Diverges fun n ↦ ((sel n).block.card : ℝ) := by
  apply exists_selection_diverging
    (fun n ↦ D.acceptableComponents (D.matchingIndex n)
      (D.matchingThreshold (D.matchingIndex n)))
    (fun _ B ↦ (B.block.card : ℝ)) D.componentSelectionError
    (fun n ↦ D.N (D.matchingIndex n))
  · exact fun n ↦ D.matchingIndex_card_pos n
  · exact D.matchingIndex_candidates_nonempty
  · intro n B _
    exact_mod_cast (BlockIndex.block_nonempty
      (D.gammaDecomposition.blocks (D.matchingIndex n)) B).card_pos
  · intro r n B _
    exact D.componentSelectionError_nonneg r n B
  · intro r r' n B hrr
    exact D.componentSelectionError_mono hrr n B
  · exact D.matchingIndex_mass
  · exact D.componentSelectionError_sum_negligible
  · intro M
    exact D.acceptable_small_mass_negligible M

noncomputable def selectedComponent (n : ℕ) :
    D.gammaDecomposition.componentIndex (D.matchingIndex n) :=
  Classical.choose D.exists_selectedComponent n

theorem selectedComponent_mem (n : ℕ) :
    D.selectedComponent n ∈ D.acceptableComponents (D.matchingIndex n)
      (D.matchingThreshold (D.matchingIndex n)) :=
  (Classical.choose_spec D.exists_selectedComponent).1 n

theorem selectedComponent_error (r : ℕ) :
    Vanishing fun n ↦ D.componentSelectionError r n (D.selectedComponent n) /
      (D.selectedComponent n).block.card :=
  (Classical.choose_spec D.exists_selectedComponent).2.1 r

theorem selectedComponent_diverges :
    Diverges fun n ↦ ((D.selectedComponent n).block.card : ℝ) :=
  (Classical.choose_spec D.exists_selectedComponent).2.2

noncomputable def selectedSubset (n : ℕ) :
    Finset (D.approximation.model (D.matchingIndex n)) :=
  (D.selectedComponent n).block.image
    (D.distinguishedTransport (D.matchingIndex n))

theorem selectedSubset_card (n : ℕ) :
    (D.selectedSubset n).card = (D.selectedComponent n).block.card :=
  Finset.card_image_of_injective _
    (D.distinguishedTransport (D.matchingIndex n)).injective

/-- The selected transported component, bundled once as a finite model so all
graph transports use the same structure and instances. -/
noncomputable def selectedFiniteModel (n : ℕ) : FiniteModel where
  carrier := D.selectedSubset n
  fintype := inferInstance
  decidableEq := inferInstance

theorem componentPredicateCount_selected (n : ℕ)
    (p : D.approximation.model (D.matchingIndex n) → Prop) [DecidablePred p] :
    D.componentPredicateCount n (D.selectedComponent n) p =
      ((D.selectedSubset n).filter p).card := by
  unfold componentPredicateCount
  refine Finset.card_bij
    (fun x _ ↦ D.distinguishedTransport (D.matchingIndex n) x.1) ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    refine ⟨Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩, ?_⟩
    rw [D.distinguishedTransport_apply]
    exact hx.2
  · intro x _ y _ hxy
    exact Subtype.ext ((D.distinguishedTransport (D.matchingIndex n)).injective hxy)
  · intro y hy
    obtain ⟨hyU, hyp⟩ := Finset.mem_filter.mp hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hyU
    refine ⟨⟨x, hx⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    rw [D.distinguishedTransport_apply] at hyp
    exact hyp

theorem selectedSubset_filter_card (n : ℕ)
    (p : D.approximation.model (D.matchingIndex n) → Prop) [DecidablePred p] :
    (Finset.univ.filter fun y : D.selectedSubset n ↦ p y.1).card =
      ((D.selectedSubset n).filter p).card := by
  classical
  apply Finset.card_bij (fun y _ ↦ y.1)
  · intro y hy
    exact Finset.mem_filter.mpr ⟨y.2, (Finset.mem_filter.mp hy).2⟩
  · intro x _ y _ hxy
    exact Subtype.ext hxy
  · intro y hy
    refine ⟨⟨y, (Finset.mem_filter.mp hy).1⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2⟩

theorem selectedSubset_is_transportedBlock (n : ℕ) (y : D.selectedSubset n) :
    (D.transportedBlocks n).block (y : D.approximation.model (D.matchingIndex n)) =
      D.selectedSubset n := by
  obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp y.2
  rw [← hxy]
  change ((D.gammaDecomposition.blocks (D.matchingIndex n)).transportEquiv
      (D.distinguishedTransport (D.matchingIndex n))).block
        (D.distinguishedTransport (D.matchingIndex n) x) = D.selectedSubset n
  rw [BlockStructure.transportEquiv_block]
  have hblock := (D.gammaDecomposition.blocks (D.matchingIndex n)).eq_of_mem
    (BlockIndex.representative _ (D.selectedComponent n)) x (by
      simpa only [BlockIndex.block_representative] using hx)
  rw [hblock, BlockIndex.block_representative]
  rfl

theorem localInvariantError_selected (n i : ℕ) :
    D.localInvariantError n i (D.selectedComponent n) =
      ((D.selectedSubset n).filter fun y ↦
        D.localizedProductAct n (D.productEnumeration i) y ∉ D.selectedSubset n).card := by
  rw [localInvariantError, D.componentPredicateCount_selected]
  norm_cast
  apply congrArg Finset.card
  ext y
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hy, hcross⟩
    refine ⟨hy, ?_⟩
    rw [mem_wordCrossing] at hcross
    intro hmem
    apply hcross
    apply (D.transportedBlocks n).eq_of_mem
    rw [D.selectedSubset_is_transportedBlock n ⟨y, hy⟩]
    exact hmem
  · rintro ⟨hy, hout⟩
    refine ⟨hy, ?_⟩
    rw [mem_wordCrossing]
    intro heq
    apply hout
    rw [← D.selectedSubset_is_transportedBlock n ⟨y, hy⟩, ← heq]
    exact (D.transportedBlocks n).self_mem _

theorem localMultiplicationError_selected (n i j : ℕ) :
    D.localMultiplicationError n i j (D.selectedComponent n) =
      ((D.selectedSubset n).filter fun y ↦
        D.localizedProductAct n (D.productEnumeration i * D.productEnumeration j) y ≠
          D.localizedProductAct n (D.productEnumeration i)
            (D.localizedProductAct n (D.productEnumeration j) y)).card := by
  rw [localMultiplicationError, D.componentPredicateCount_selected]
  norm_cast
  apply congrArg Finset.card
  ext y
  simp [SoficApproximation.multiplicationError, localizedProductAct, map_mul]

theorem localFixedError_selected (n i : ℕ)
    (hi : D.productEnumeration i ≠ 1) :
    D.localFixedError n i (D.selectedComponent n) =
      ((D.selectedSubset n).filter fun y ↦
        D.localizedProductAct n (D.productEnumeration i) y = y).card := by
  rw [localFixedError, if_neg hi, D.componentPredicateCount_selected]
  norm_cast
  apply congrArg Finset.card
  ext y
  simp [SoficApproximation.fixedError, localizedProductAct]

theorem localInvariantError_selectedSubtype (n i : ℕ) :
    D.localInvariantError n i (D.selectedComponent n) =
      (Finset.univ.filter fun y : D.selectedSubset n ↦
        D.localizedProductAct n (D.productEnumeration i) y ∉ D.selectedSubset n).card := by
  rw [D.localInvariantError_selected n i]
  exact_mod_cast (D.selectedSubset_filter_card n fun y ↦
    D.localizedProductAct n (D.productEnumeration i) y ∉ D.selectedSubset n).symm

theorem localMultiplicationError_selectedSubtype (n i j : ℕ) :
    D.localMultiplicationError n i j (D.selectedComponent n) =
      (Finset.univ.filter fun y : D.selectedSubset n ↦
        D.localizedProductAct n (D.productEnumeration i * D.productEnumeration j) y ≠
          D.localizedProductAct n (D.productEnumeration i)
            (D.localizedProductAct n (D.productEnumeration j) y)).card := by
  rw [D.localMultiplicationError_selected n i j]
  exact_mod_cast (D.selectedSubset_filter_card n fun y ↦
    D.localizedProductAct n (D.productEnumeration i * D.productEnumeration j) y ≠
      D.localizedProductAct n (D.productEnumeration i)
        (D.localizedProductAct n (D.productEnumeration j) y)).symm

theorem localFixedError_selectedSubtype (n i : ℕ)
    (hi : D.productEnumeration i ≠ 1) :
    D.localFixedError n i (D.selectedComponent n) =
      (Finset.univ.filter fun y : D.selectedSubset n ↦
        D.localizedProductAct n (D.productEnumeration i) y = y).card := by
  rw [D.localFixedError_selected n i hi]
  exact_mod_cast (D.selectedSubset_filter_card n fun y ↦
    D.localizedProductAct n (D.productEnumeration i) y = y).symm

theorem invariantError_le_selectionError {i r : ℕ} (hir : i ≤ r) (n : ℕ) :
    D.localInvariantError n i (D.selectedComponent n) ≤
      D.componentSelectionError r n (D.selectedComponent n) := by
  unfold componentSelectionError
  have hi : i ∈ Finset.range (r + 1) := Finset.mem_range.mpr (by omega)
  have hterm := Finset.single_le_sum
    (fun j _ ↦ D.localInvariantError_nonneg n j (D.selectedComponent n)) hi
  have hmatch : 0 ≤ ((D.matchImage (D.matchingIndex n) (D.selectedComponent n) ∆
      D.matchTarget (D.matchingIndex n) (D.selectedComponent n)).card : ℝ) := by
    positivity
  have hmul : 0 ≤ ∑ a ∈ Finset.range (r + 1), ∑ b ∈ Finset.range (r + 1),
      D.localMultiplicationError n a b (D.selectedComponent n) :=
    Finset.sum_nonneg fun a _ ↦ Finset.sum_nonneg fun b _ ↦
      D.localMultiplicationError_nonneg n a b (D.selectedComponent n)
  have hfixed : 0 ≤ ∑ a ∈ Finset.range (r + 1),
      D.localFixedError n a (D.selectedComponent n) :=
    Finset.sum_nonneg fun a _ ↦ D.localFixedError_nonneg n a (D.selectedComponent n)
  linarith [D.localGraphBaseError_nonneg n (D.selectedComponent n)]

theorem multiplicationError_le_selectionError {i j r : ℕ}
    (hir : i ≤ r) (hjr : j ≤ r) (n : ℕ) :
    D.localMultiplicationError n i j (D.selectedComponent n) ≤
      D.componentSelectionError r n (D.selectedComponent n) := by
  unfold componentSelectionError
  have hi : i ∈ Finset.range (r + 1) := Finset.mem_range.mpr (by omega)
  have hj : j ∈ Finset.range (r + 1) := Finset.mem_range.mpr (by omega)
  have hjterm := Finset.single_le_sum
    (fun k _ ↦ D.localMultiplicationError_nonneg n i k (D.selectedComponent n)) hj
  have hiterm : (∑ l ∈ Finset.range (r + 1),
      D.localMultiplicationError n i l (D.selectedComponent n)) ≤
      ∑ k ∈ Finset.range (r + 1), ∑ l ∈ Finset.range (r + 1),
        D.localMultiplicationError n k l (D.selectedComponent n) :=
    Finset.single_le_sum
      (f := fun k ↦ ∑ l ∈ Finset.range (r + 1),
        D.localMultiplicationError n k l (D.selectedComponent n))
      (fun k _ ↦ Finset.sum_nonneg fun l _ ↦
        D.localMultiplicationError_nonneg n k l (D.selectedComponent n)) hi
  have hterm := hjterm.trans (by simpa using hiterm)
  have hmatch : 0 ≤ ((D.matchImage (D.matchingIndex n) (D.selectedComponent n) ∆
      D.matchTarget (D.matchingIndex n) (D.selectedComponent n)).card : ℝ) := by
    positivity
  have hinvariant : 0 ≤ ∑ a ∈ Finset.range (r + 1),
      D.localInvariantError n a (D.selectedComponent n) :=
    Finset.sum_nonneg fun a _ ↦ D.localInvariantError_nonneg n a (D.selectedComponent n)
  have hfixed : 0 ≤ ∑ a ∈ Finset.range (r + 1),
      D.localFixedError n a (D.selectedComponent n) :=
    Finset.sum_nonneg fun a _ ↦ D.localFixedError_nonneg n a (D.selectedComponent n)
  linarith [D.localGraphBaseError_nonneg n (D.selectedComponent n)]

theorem fixedError_le_selectionError {i r : ℕ} (hir : i ≤ r) (n : ℕ) :
    D.localFixedError n i (D.selectedComponent n) ≤
      D.componentSelectionError r n (D.selectedComponent n) := by
  unfold componentSelectionError
  have himem : i ∈ Finset.range (r + 1) := Finset.mem_range.mpr (by omega)
  have hterm := Finset.single_le_sum
    (fun j _ ↦ D.localFixedError_nonneg n j (D.selectedComponent n))
    himem
  have hmatch : 0 ≤ ((D.matchImage (D.matchingIndex n) (D.selectedComponent n) ∆
      D.matchTarget (D.matchingIndex n) (D.selectedComponent n)).card : ℝ) := by
    positivity
  have hinvariant : 0 ≤ ∑ a ∈ Finset.range (r + 1),
      D.localInvariantError n a (D.selectedComponent n) :=
    Finset.sum_nonneg fun a _ ↦ D.localInvariantError_nonneg n a (D.selectedComponent n)
  have hmultiplication : 0 ≤ ∑ a ∈ Finset.range (r + 1),
      ∑ b ∈ Finset.range (r + 1),
        D.localMultiplicationError n a b (D.selectedComponent n) :=
    Finset.sum_nonneg fun a _ ↦ Finset.sum_nonneg fun b _ ↦
      D.localMultiplicationError_nonneg n a b (D.selectedComponent n)
  linarith [D.localGraphBaseError_nonneg n (D.selectedComponent n)]

/-- The selected transported component carries a localized sofic
approximation of `Γ × J`. -/
noncomputable def selectedLocalization : LocalizedApproximationData (Γ × J) where
  ambient := fun n ↦ D.approximation.model (D.matchingIndex n)
  subset := D.selectedSubset
  act := D.localizedProductAct
  card_diverges := by
    apply Diverges.congr D.selectedComponent_diverges
    intro n
    exact_mod_cast (D.selectedSubset_card n).symm
  invariant := by
    intro g
    obtain ⟨i, hi⟩ := D.productEnumeration_surjective g
    have herr := D.selectedComponent_error i
    refine Vanishing.squeeze (fun n ↦ div_nonneg (by positivity) (by positivity))
      (fun n ↦ ?_) herr
    rw [← hi, ← D.localInvariantError_selectedSubtype n i,
      D.selectedSubset_card]
    apply div_le_div_of_nonneg_right (D.invariantError_le_selectionError le_rfl n)
    positivity

  multiplicative := by
    intro g h
    obtain ⟨i, hi⟩ := D.productEnumeration_surjective g
    obtain ⟨j, hj⟩ := D.productEnumeration_surjective h
    let r := max i j
    have herr := D.selectedComponent_error r
    refine Vanishing.squeeze (fun n ↦ div_nonneg (by positivity) (by positivity))
      (fun n ↦ ?_) herr
    rw [← hi, ← hj, ← D.localMultiplicationError_selectedSubtype n i j,
      D.selectedSubset_card]
    apply div_le_div_of_nonneg_right
      (D.multiplicationError_le_selectionError (le_max_left i j)
        (le_max_right i j) n)
    positivity
  faithful := by
    intro g hg
    obtain ⟨i, hi⟩ := D.productEnumeration_surjective g
    have hii : D.productEnumeration i ≠ 1 := by simpa [hi]
    have herr := D.selectedComponent_error i
    refine Vanishing.squeeze (fun n ↦ div_nonneg (by positivity) (by positivity))
      (fun n ↦ ?_) herr
    rw [← hi, ← D.localFixedError_selectedSubtype n i hii,
      D.selectedSubset_card]
    apply div_le_div_of_nonneg_right
      (D.fixedError_le_selectionError le_rfl n)
    positivity

noncomputable def selectedImageEquiv (n : ℕ) :
    (D.selectedComponent n).block ≃ D.selectedSubset n where
  toFun x := ⟨D.distinguishedTransport (D.matchingIndex n) x.1,
    Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩⟩
  invFun y := by
    refine ⟨(D.distinguishedTransport (D.matchingIndex n)).symm y, ?_⟩
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp y.2
    have hxy' : D.distinguishedTransport (D.matchingIndex n) x = y := hxy
    have hx' : (D.distinguishedTransport (D.matchingIndex n)).symm y = x := by
      rw [← hxy']
      exact (D.distinguishedTransport (D.matchingIndex n)).symm_apply_apply x
    rw [hx']
    exact hx
  left_inv x := by
    apply Subtype.ext
    exact (D.distinguishedTransport (D.matchingIndex n)).symm_apply_apply x.1
  right_inv y := by
    apply Subtype.ext
    exact (D.distinguishedTransport (D.matchingIndex n)).apply_symm_apply y.1

noncomputable def selectedGraph (n : ℕ) : FiniteMultiGraph :=
  ((D.gammaDecomposition.modelGraph (D.matchingIndex n)).induce
    (D.selectedComponent n).block).transport
      (D.selectedFiniteModel n)
      (D.selectedImageEquiv n)

theorem selectedGraph_expands (n : ℕ) :
    (D.selectedGraph n).HasCheegerLowerBound D.gammaDecomposition.cheeger := by
  exact FiniteMultiGraph.transport_hasCheegerLowerBound
    ((D.gammaDecomposition.modelGraph (D.matchingIndex n)).induce
      (D.selectedComponent n).block)
    (D.selectedFiniteModel n)
    (D.selectedImageEquiv n)
    (by
      let y := BlockIndex.representative
        (D.gammaDecomposition.blocks (D.matchingIndex n)) (D.selectedComponent n)
      have h := D.gammaDecomposition.component_expands (D.matchingIndex n) y
      change ((D.gammaDecomposition.modelGraph (D.matchingIndex n)).induce
        ((D.gammaDecomposition.blocks (D.matchingIndex n)).block y)).HasCheegerLowerBound
          D.gammaDecomposition.cheeger at h
      rw [BlockIndex.block_representative] at h
      exact h)

end LocalCriterionData

end NonsoficGroupsExist
