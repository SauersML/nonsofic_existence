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

noncomputable def productEnumeration : ℕ → Γ × J :=
  Classical.choose (exists_surjective_nat (Γ × J))

theorem productEnumeration_surjective : Function.Surjective D.productEnumeration :=
  Classical.choose_spec (exists_surjective_nat (Γ × J))

noncomputable def componentPredicateCount (n : ℕ)
    (B : D.gammaDecomposition.componentIndex (D.matchingIndex n))
    (p : D.approximation.model (D.matchingIndex n) → Prop) : ℕ :=
  (Finset.univ.filter fun x : indexedBlockModel
    (D.gammaDecomposition.blocks (D.matchingIndex n)) B ↦
      p (D.distinguishedPerm (D.matchingIndex n) x)).card

theorem sum_componentPredicateCount_le (n : ℕ)
    (p : D.approximation.model (D.matchingIndex n) → Prop) [DecidablePred p] :
    (∑ B in D.acceptableComponents (D.matchingIndex n)
      (D.matchingThreshold (D.matchingIndex n)),
      (D.componentPredicateCount n B p : ℝ)) ≤
        ((Finset.univ.filter p).card : ℝ) := by
  let P := D.gammaDecomposition.blocks (D.matchingIndex n)
  let q := D.distinguishedPerm (D.matchingIndex n)
  have hsub : (∑ B in D.acceptableComponents (D.matchingIndex n)
      (D.matchingThreshold (D.matchingIndex n)),
      (D.componentPredicateCount n B p : ℝ)) ≤
      ∑ B : D.gammaDecomposition.componentIndex (D.matchingIndex n),
        ((Finset.univ.filter fun x : indexedBlockModel P B ↦ p (q x)).card : ℝ) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ ↦ by positivity)
  have hpartition := BlockIndex.sum_card_filter P (fun x ↦ p (q x))
  have hpreimage : ((Finset.univ.filter fun x ↦ p (q x)).card : ℝ) =
      ((Finset.univ.filter p).card : ℝ) := by
    let A : Finset (D.approximation.model (D.matchingIndex n)) :=
      Finset.univ.filter p
    have heq : (Finset.univ.filter fun x ↦ p (q x)) = permutationPreimage q A := by
      ext x
      simp [A, permutationPreimage]
    rw [heq, permutationPreimage_card]
  exact hsub.trans (by simpa [componentPredicateCount, P, q, hpreimage] using hpartition)

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
    (B : D.gammaDecomposition.componentIndex (D.matchingIndex n)) : ℝ :=
  if D.productEnumeration i = 1 then 0 else
    D.componentPredicateCount n B fun y ↦
      y ∈ D.approximation.fixedError (D.matchingIndex n)
        (D.setup.productEmbedding (D.productEnumeration i))

noncomputable def localGammaEditError (n : ℕ)
    (B : D.gammaDecomposition.componentIndex (D.matchingIndex n)) : ℝ :=
  (((D.gammaDecomposition.editWitness (D.matchingIndex n)).sourceUnmatched.filter
    fun e ↦ (generatorGraph
      (D.approximation.model (D.matchingIndex n)) D.setup.generatorsΓ
      (fun g ↦ D.approximation.map (D.matchingIndex n) (D.setup.embedΓ g))).first e ∈
        B.block).card : ℝ) +
  (((D.gammaDecomposition.editWitness (D.matchingIndex n)).targetUnmatched.filter
    fun e ↦ (D.gammaDecomposition.modelGraph (D.matchingIndex n)).first e ∈
      B.block).card : ℝ)

noncomputable def localConjugacyGraphError (n : ℕ)
    (B : D.gammaDecomposition.componentIndex (D.matchingIndex n)) : ℝ :=
  ∑ t : D.setup.generatorsΓ,
    ((Finset.univ.filter fun x : indexedBlockModel
      (D.gammaDecomposition.blocks (D.matchingIndex n)) B ↦
        (x : D.approximation.model (D.matchingIndex n)) ∈
          D.approximation.conjugacyError (D.matchingIndex n)
            D.setup.distinguished (D.setup.embedΓ t.1)).card : ℝ)

noncomputable def localGammaBoundaryError (n : ℕ)
    (B : D.gammaDecomposition.componentIndex (D.matchingIndex n)) : ℝ :=
  ∑ t : D.setup.generatorsΓ,
    ((Finset.univ.filter fun x : indexedBlockModel
      (D.gammaDecomposition.blocks (D.matchingIndex n)) B ↦
        (D.gammaDecomposition.blocks (D.matchingIndex n)).block
          (D.approximation.map (D.matchingIndex n) (D.setup.embedΓ t.1) x) ≠
            B.block).card : ℝ)

noncomputable def localGraphBaseError (n : ℕ)
    (B : D.gammaDecomposition.componentIndex (D.matchingIndex n)) : ℝ :=
  D.localGammaEditError n B + D.localConjugacyGraphError n B
    + D.localGammaBoundaryError n B

noncomputable def componentSelectionError (r n : ℕ)
    (B : D.gammaDecomposition.componentIndex (D.matchingIndex n)) : ℝ :=
  ((D.matchImage (D.matchingIndex n) B ∆
    D.matchTarget (D.matchingIndex n) B).card : ℝ) +
  D.localGraphBaseError n B +
  (∑ i in Finset.range (r + 1), D.localInvariantError n i B) +
  (∑ i in Finset.range (r + 1), ∑ j in Finset.range (r + 1),
    D.localMultiplicationError n i j B) +
  ∑ i in Finset.range (r + 1), D.localFixedError n i B

theorem componentSelectionError_nonneg (r n : ℕ)
    (B : D.gammaDecomposition.componentIndex (D.matchingIndex n)) :
    0 ≤ D.componentSelectionError r n B := by
  unfold componentSelectionError localInvariantError localMultiplicationError
    localFixedError localGraphBaseError localGammaEditError localConjugacyGraphError
    localGammaBoundaryError
    componentPredicateCount
  positivity

theorem componentSelectionError_mono {r r' : ℕ} (hrr : r ≤ r') (n : ℕ)
    (B : D.gammaDecomposition.componentIndex (D.matchingIndex n)) :
    D.componentSelectionError r n B ≤ D.componentSelectionError r' n B := by
  have hrange : Finset.range (r + 1) ⊆ Finset.range (r' + 1) :=
    Finset.range_mono (Nat.add_le_add_right hrr 1)
  have hinvariant :
      (∑ i in Finset.range (r + 1), D.localInvariantError n i B) ≤
        ∑ i in Finset.range (r' + 1), D.localInvariantError n i B :=
    Finset.sum_le_sum_of_subset_of_nonneg hrange (fun _ _ _ ↦ by
      unfold localInvariantError componentPredicateCount
      positivity)
  have hmultiplicationInner (i : ℕ) :
      (∑ j in Finset.range (r + 1), D.localMultiplicationError n i j B) ≤
        ∑ j in Finset.range (r' + 1), D.localMultiplicationError n i j B :=
    Finset.sum_le_sum_of_subset_of_nonneg hrange (fun _ _ _ ↦ by
      unfold localMultiplicationError componentPredicateCount
      positivity)
  have hmultiplication :
      (∑ i in Finset.range (r + 1), ∑ j in Finset.range (r + 1),
        D.localMultiplicationError n i j B) ≤
      ∑ i in Finset.range (r' + 1), ∑ j in Finset.range (r' + 1),
        D.localMultiplicationError n i j B := by
    calc
      _ ≤ ∑ i in Finset.range (r + 1), ∑ j in Finset.range (r' + 1),
          D.localMultiplicationError n i j B :=
        Finset.sum_le_sum fun i _ ↦ hmultiplicationInner i
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hrange (fun _ _ _ ↦
        Finset.sum_nonneg fun _ _ ↦ by
          unfold localMultiplicationError componentPredicateCount
          positivity)
  have hfixed :
      (∑ i in Finset.range (r + 1), D.localFixedError n i B) ≤
        ∑ i in Finset.range (r' + 1), D.localFixedError n i B :=
    Finset.sum_le_sum_of_subset_of_nonneg hrange (fun _ _ _ ↦ by
      unfold localFixedError componentPredicateCount
      split_ifs <;> positivity)
  unfold componentSelectionError
  exact add_le_add
    (add_le_add
      (add_le_add (add_le_add le_rfl le_rfl) hinvariant) hmultiplication)
    hfixed

theorem sum_localInvariantError_negligible (i : ℕ) :
    Negligible (fun n ↦ D.N (D.matchingIndex n)) fun n ↦
      ∑ B in D.acceptableComponents (D.matchingIndex n)
        (D.matchingThreshold (D.matchingIndex n)), D.localInvariantError n i B := by
  refine Negligible.mono (fun n ↦ D.matchingIndex_card_pos n)
    (fun n ↦ by positivity) (fun n ↦ ?_)
    (D.transportedBlocks_almost_invariant (D.productEnumeration i))
  simpa [localInvariantError] using D.sum_componentPredicateCount_le n
    (fun y ↦ y ∈ wordCrossing (D.transportedBlocks n)
      (D.localizedProductAct n (D.productEnumeration i)))

theorem sum_localMultiplicationError_negligible (i j : ℕ) :
    Negligible (fun n ↦ D.N (D.matchingIndex n)) fun n ↦
      ∑ B in D.acceptableComponents (D.matchingIndex n)
        (D.matchingThreshold (D.matchingIndex n)),
        D.localMultiplicationError n i j B := by
  let gi := D.setup.productEmbedding (D.productEnumeration i)
  let gj := D.setup.productEmbedding (D.productEnumeration j)
  have hglobal := Negligible.shift
    (D.approximation.multiplicationError_negligible gi gj) D.matchingStart
  refine Negligible.mono (fun n ↦ D.matchingIndex_card_pos n)
    (fun n ↦ by positivity) (fun n ↦ ?_) hglobal
  simpa [localMultiplicationError, gi, gj] using D.sum_componentPredicateCount_le n
    (fun y ↦ y ∈ D.approximation.multiplicationError (D.matchingIndex n) gi gj)

theorem sum_localFixedError_negligible (i : ℕ) :
    Negligible (fun n ↦ D.N (D.matchingIndex n)) fun n ↦
      ∑ B in D.acceptableComponents (D.matchingIndex n)
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
      (fun n ↦ by positivity) (fun n ↦ ?_) hglobal
    simpa [localFixedError, hi] using D.sum_componentPredicateCount_le n
      (fun y ↦ y ∈ D.approximation.fixedError (D.matchingIndex n)
        (D.setup.productEmbedding (D.productEnumeration i)))

theorem localGraphBaseError_sum_negligible :
    Negligible (fun n ↦ D.N (D.matchingIndex n)) fun n ↦
      ∑ B in D.acceptableComponents (D.matchingIndex n)
        (D.matchingThreshold (D.matchingIndex n)), D.localGraphBaseError n B := by
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
      (D.approximation.map (D.matchingIndex n) (D.setup.embedΓ t.1))).card : ℝ))
    (fun t _ ↦ by simpa [wordCrossing, CompressionSetup.gammaApproximation]
      using hboundaryEach t)
  have hbound := Negligible.add (Negligible.add hedit hconj) hboundary
  refine Negligible.mono (fun n ↦ D.matchingIndex_card_pos n)
    (fun n ↦ by positivity) (fun n ↦ ?_) hbound
  let P := D.gammaDecomposition.blocks (D.matchingIndex n)
  let W := D.gammaDecomposition.editWitness (D.matchingIndex n)
  have hsourceAll := BlockIndex.sum_card_filter_mem_block P W.sourceUnmatched
    (fun e ↦ (generatorGraph
      (D.approximation.model (D.matchingIndex n)) D.setup.generatorsΓ
      (fun g ↦ D.approximation.map (D.matchingIndex n) (D.setup.embedΓ g))).first e)
  have htargetAll := BlockIndex.sum_card_filter_mem_block P W.targetUnmatched
    (fun e ↦ (D.gammaDecomposition.modelGraph (D.matchingIndex n)).first e)
  have heditLocal : (∑ B in D.acceptableComponents (D.matchingIndex n)
      (D.matchingThreshold (D.matchingIndex n)), D.localGammaEditError n B) ≤
      (W.unmatchedCount : ℝ) := by
    have hsub : (∑ B in D.acceptableComponents (D.matchingIndex n)
        (D.matchingThreshold (D.matchingIndex n)), D.localGammaEditError n B) ≤
        ∑ B : D.gammaDecomposition.componentIndex (D.matchingIndex n),
          D.localGammaEditError n B :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ ↦ by unfold localGammaEditError; positivity)
    unfold localGammaEditError at hsub
    simp_rw [Finset.sum_add_distrib] at hsub
    unfold EdgeEditWitness.unmatchedCount
    exact hsub.trans (by exact_mod_cast add_le_add hsourceAll htargetAll)
  have hconjLocal : (∑ B in D.acceptableComponents (D.matchingIndex n)
      (D.matchingThreshold (D.matchingIndex n)), D.localConjugacyGraphError n B) ≤
      ∑ t : D.setup.generatorsΓ,
        ((D.approximation.conjugacyError (D.matchingIndex n)
          D.setup.distinguished (D.setup.embedΓ t.1)).card : ℝ) := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro t _
    have hsub : (∑ B in D.acceptableComponents (D.matchingIndex n)
        (D.matchingThreshold (D.matchingIndex n)),
        ((Finset.univ.filter fun x : indexedBlockModel P B ↦
          (x : D.approximation.model (D.matchingIndex n)) ∈
            D.approximation.conjugacyError (D.matchingIndex n)
              D.setup.distinguished (D.setup.embedΓ t.1)).card : ℝ)) ≤
        ∑ B : D.gammaDecomposition.componentIndex (D.matchingIndex n),
        ((Finset.univ.filter fun x : indexedBlockModel P B ↦
          (x : D.approximation.model (D.matchingIndex n)) ∈
            D.approximation.conjugacyError (D.matchingIndex n)
              D.setup.distinguished (D.setup.embedΓ t.1)).card : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ ↦ by positivity)
    exact hsub.trans (by
      rw [BlockIndex.sum_card_filter P]
      rfl)
  have hboundaryLocal : (∑ B in D.acceptableComponents (D.matchingIndex n)
      (D.matchingThreshold (D.matchingIndex n)), D.localGammaBoundaryError n B) ≤
      ∑ t : D.setup.generatorsΓ,
        ((wordCrossing (D.gammaDecomposition.blocks (D.matchingIndex n))
          (D.approximation.map (D.matchingIndex n) (D.setup.embedΓ t.1))).card : ℝ) := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro t _
    let p : D.approximation.model (D.matchingIndex n) → Prop := fun x ↦
      (D.gammaDecomposition.blocks (D.matchingIndex n)).block
        (D.approximation.map (D.matchingIndex n) (D.setup.embedΓ t.1) x) ≠
          (D.gammaDecomposition.blocks (D.matchingIndex n)).block x
    have hsub : (∑ B in D.acceptableComponents (D.matchingIndex n)
        (D.matchingThreshold (D.matchingIndex n)),
        ((Finset.univ.filter fun x : indexedBlockModel P B ↦ p x).card : ℝ)) ≤
        ∑ B : D.gammaDecomposition.componentIndex (D.matchingIndex n),
          ((Finset.univ.filter fun x : indexedBlockModel P B ↦ p x).card : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ ↦ by positivity)
    rw [BlockIndex.sum_card_filter P] at hsub
    simpa [localGammaBoundaryError, p, wordCrossing] using hsub
  unfold localGraphBaseError
  simp_rw [Finset.sum_add_distrib]
  exact add_le_add (add_le_add heditLocal hconjLocal) hboundaryLocal

theorem componentSelectionError_sum_negligible (r : ℕ) :
    Negligible (fun n ↦ D.N (D.matchingIndex n)) fun n ↦
      ∑ B in D.acceptableComponents (D.matchingIndex n)
        (D.matchingThreshold (D.matchingIndex n)),
        D.componentSelectionError r n B := by
  have hinv := Negligible.sum (Finset.range (r + 1))
    (fun i n ↦ ∑ B in D.acceptableComponents (D.matchingIndex n)
      (D.matchingThreshold (D.matchingIndex n)), D.localInvariantError n i B)
    (fun i _ ↦ D.sum_localInvariantError_negligible i)
  have hmulInner (i : ℕ) := Negligible.sum (Finset.range (r + 1))
    (fun j n ↦ ∑ B in D.acceptableComponents (D.matchingIndex n)
      (D.matchingThreshold (D.matchingIndex n)),
      D.localMultiplicationError n i j B)
    (fun j _ ↦ D.sum_localMultiplicationError_negligible i j)
  have hmul := Negligible.sum (Finset.range (r + 1))
    (fun i n ↦ ∑ j in Finset.range (r + 1),
      ∑ B in D.acceptableComponents (D.matchingIndex n)
        (D.matchingThreshold (D.matchingIndex n)),
        D.localMultiplicationError n i j B)
    (fun i _ ↦ hmulInner i)
  have hfixed := Negligible.sum (Finset.range (r + 1))
    (fun i n ↦ ∑ B in D.acceptableComponents (D.matchingIndex n)
      (D.matchingThreshold (D.matchingIndex n)), D.localFixedError n i B)
    (fun i _ ↦ D.sum_localFixedError_negligible i)
  have hall := Negligible.add
    (Negligible.add
      (Negligible.add D.acceptable_symmDiff_sum_negligible
        D.localGraphBaseError_sum_negligible) hinv)
    (Negligible.add hmul hfixed)
  apply Negligible.congr hall
  intro n
  unfold componentSelectionError
  simp_rw [Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  congr 1
  · rw [Finset.sum_comm]
    congr 1
    ext i
    rw [Finset.sum_comm]
  · rw [Finset.sum_comm]

theorem acceptable_small_mass_negligible (M : ℕ) :
    Negligible (fun n ↦ D.N (D.matchingIndex n)) fun n ↦
      ∑ B in D.acceptableComponents (D.matchingIndex n)
        (D.matchingThreshold (D.matchingIndex n)),
        (if (B.block.card : ℝ) ≤ M then (B.block.card : ℝ) else 0) := by
  have hsmall0 := D.gammaDecomposition.smallBlockVertices_negligible
    D.setup.generatorsΓ_symmetric D.setup.generatorsΓ_generate M
  have hsmall := Negligible.shift hsmall0 D.matchingStart
  refine Negligible.mono (fun n ↦ D.matchingIndex_card_pos n)
    (fun n ↦ by positivity) (fun n ↦ ?_) hsmall
  have hsub : (∑ B in D.acceptableComponents (D.matchingIndex n)
      (D.matchingThreshold (D.matchingIndex n)),
      (if (B.block.card : ℝ) ≤ M then (B.block.card : ℝ) else 0)) ≤
      ∑ B : D.gammaDecomposition.componentIndex (D.matchingIndex n),
        (if B.block.card ≤ M then (B.block.card : ℝ) else 0) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro B _ _
    split_ifs <;> positivity
  calc
    _ ≤ _ := hsub
    _ = ((smallBlockVertices (D.gammaDecomposition.blocks (D.matchingIndex n)) M).card : ℝ) := by
      rw [← BlockIndex.sum_card_filter (D.gammaDecomposition.blocks (D.matchingIndex n))
        (fun x ↦ (D.gammaDecomposition.blocks (D.matchingIndex n)).size x ≤ M)]
      apply Finset.sum_congr rfl
      intro B _
      by_cases hB : B.block.card ≤ M
      · simp only [if_pos hB]
        have hall : Finset.univ.filter (fun x : indexedBlockModel
            (D.gammaDecomposition.blocks (D.matchingIndex n)) B ↦
              (D.gammaDecomposition.blocks (D.matchingIndex n)).size x ≤ M) =
            Finset.univ := by
          apply Finset.filter_eq_self.mpr
          intro x _
          have hx : (D.gammaDecomposition.blocks (D.matchingIndex n)).size
              (x : D.approximation.model (D.matchingIndex n)) = B.block.card := by
            change ((D.gammaDecomposition.blocks (D.matchingIndex n)).block x).card = _
            exact congrArg Finset.card
              ((D.gammaDecomposition.blocks (D.matchingIndex n)).eq_of_mem
                (BlockIndex.representative _ B) x (by
                  simpa only [BlockIndex.block_representative] using x.2) |>.trans
                (BlockIndex.block_representative _ B))
          simpa [hx]
        rw [hall]
        simp [indexedBlockModel]
      · simp only [if_neg hB]
        apply Nat.cast_eq_zero.mpr
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro x _
        have hx : (D.gammaDecomposition.blocks (D.matchingIndex n)).size
            (x : D.approximation.model (D.matchingIndex n)) = B.block.card := by
          change ((D.gammaDecomposition.blocks (D.matchingIndex n)).block x).card = _
          exact congrArg Finset.card
            ((D.gammaDecomposition.blocks (D.matchingIndex n)).eq_of_mem
              (BlockIndex.representative _ B) x (by
                simpa only [BlockIndex.block_representative] using x.2) |>.trans
              (BlockIndex.block_representative _ B))
        simpa [hx] using hB

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
  D.matchImage (D.matchingIndex n) (D.selectedComponent n)

theorem selectedSubset_card (n : ℕ) :
    (D.selectedSubset n).card = (D.selectedComponent n).block.card :=
  Finset.card_image_of_injective _ (D.distinguishedPerm (D.matchingIndex n)).injective

theorem componentPredicateCount_selected (n : ℕ)
    (p : D.approximation.model (D.matchingIndex n) → Prop) [DecidablePred p] :
    D.componentPredicateCount n (D.selectedComponent n) p =
      ((D.selectedSubset n).filter p).card := by
  classical
  apply Finset.card_bij
    (s := Finset.univ.filter fun x : indexedBlockModel
      (D.gammaDecomposition.blocks (D.matchingIndex n)) (D.selectedComponent n) ↦
        p (D.distinguishedPerm (D.matchingIndex n) x))
    (t := (D.selectedSubset n).filter p)
    (fun x _ ↦ D.distinguishedPerm (D.matchingIndex n) (x :
      D.approximation.model (D.matchingIndex n)))
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨Finset.mem_image.mpr ⟨x, x.2, rfl⟩, hx.2⟩
  · intro x _ y _ hxy
    exact Subtype.ext ((D.distinguishedPerm (D.matchingIndex n)).injective hxy)
  · intro y hy
    obtain ⟨hyU, hyp⟩ := Finset.mem_filter.mp hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hyU
    refine ⟨⟨x, hx⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyp⟩, rfl⟩

theorem selectedSubset_is_transportedBlock (n : ℕ) (y : D.selectedSubset n) :
    (D.transportedBlocks n).block (y : D.approximation.model (D.matchingIndex n)) =
      D.selectedSubset n := by
  obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp y.2
  rw [← hxy, BlockStructure.transport_block]
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
  congr 1
  ext y
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hy, hcross⟩
    refine ⟨hy, ?_⟩
    rw [mem_wordCrossing] at hcross
    intro hmem
    apply hcross
    rw [D.selectedSubset_is_transportedBlock n ⟨y, hy⟩]
    exact (D.transportedBlocks n).eq_of_mem y _ hmem
  · rintro ⟨hy, hout⟩
    refine ⟨hy, ?_⟩
    rw [mem_wordCrossing]
    intro heq
    apply hout
    rw [← D.selectedSubset_is_transportedBlock n ⟨y, hy⟩, heq]
    exact (D.transportedBlocks n).self_mem _

theorem localMultiplicationError_selected (n i j : ℕ) :
    D.localMultiplicationError n i j (D.selectedComponent n) =
      ((D.selectedSubset n).filter fun y ↦
        D.localizedProductAct n (D.productEnumeration i * D.productEnumeration j) y ≠
          D.localizedProductAct n (D.productEnumeration i)
            (D.localizedProductAct n (D.productEnumeration j) y)).card := by
  rw [localMultiplicationError, D.componentPredicateCount_selected]
  congr 1
  ext y
  simp [SoficApproximation.multiplicationError, localizedProductAct, map_mul]

theorem localFixedError_selected (n i : ℕ)
    (hi : D.productEnumeration i ≠ 1) :
    D.localFixedError n i (D.selectedComponent n) =
      ((D.selectedSubset n).filter fun y ↦
        D.localizedProductAct n (D.productEnumeration i) y = y).card := by
  rw [localFixedError, if_neg hi, D.componentPredicateCount_selected]
  congr 1
  ext y
  simp [SoficApproximation.fixedError, localizedProductAct]

theorem invariantError_le_selectionError {i r : ℕ} (hir : i ≤ r) (n : ℕ) :
    D.localInvariantError n i (D.selectedComponent n) ≤
      D.componentSelectionError r n (D.selectedComponent n) := by
  unfold componentSelectionError
  have hi : i ∈ Finset.range (r + 1) := Finset.mem_range.mpr (by omega)
  have hterm := Finset.single_le_sum
    (fun j _ ↦ by unfold localInvariantError componentPredicateCount; positivity) hi
  positivity

theorem multiplicationError_le_selectionError {i j r : ℕ}
    (hir : i ≤ r) (hjr : j ≤ r) (n : ℕ) :
    D.localMultiplicationError n i j (D.selectedComponent n) ≤
      D.componentSelectionError r n (D.selectedComponent n) := by
  unfold componentSelectionError
  have hi : i ∈ Finset.range (r + 1) := Finset.mem_range.mpr (by omega)
  have hj : j ∈ Finset.range (r + 1) := Finset.mem_range.mpr (by omega)
  have hjterm := Finset.single_le_sum
    (fun k _ ↦ by unfold localMultiplicationError componentPredicateCount; positivity) hj
  have hiterm := Finset.single_le_sum
    (fun k _ ↦ Finset.sum_nonneg fun _ _ ↦ by
      unfold localMultiplicationError componentPredicateCount
      positivity) hi
  have := hjterm.trans (by simpa using hiterm)
  positivity

theorem fixedError_le_selectionError {i r : ℕ} (hir : i ≤ r)
    (hi : D.productEnumeration i ≠ 1) (n : ℕ) :
    D.localFixedError n i (D.selectedComponent n) ≤
      D.componentSelectionError r n (D.selectedComponent n) := by
  unfold componentSelectionError
  have himem : i ∈ Finset.range (r + 1) := Finset.mem_range.mpr (by omega)
  have hterm := Finset.single_le_sum
    (fun j _ ↦ by unfold localFixedError componentPredicateCount; split_ifs <;> positivity)
    himem
  positivity

/-- The selected transported component carries a localized sofic
approximation of `Γ × J`. -/
noncomputable def selectedLocalization : LocalizedApproximationData (Γ × J) where
  ambient := fun n ↦ D.approximation.model (D.matchingIndex n)
  subset := D.selectedSubset
  act := D.localizedProductAct
  card_diverges := by
    apply Diverges.congr D.selectedComponent_diverges
    intro n
    exact_mod_cast D.selectedSubset_card n
  invariant := by
    intro g
    obtain ⟨i, hi⟩ := D.productEnumeration_surjective g
    have herr := D.selectedComponent_error i
    refine Vanishing.squeeze (fun n ↦ div_nonneg (by positivity) (by positivity))
      (fun n ↦ ?_) herr
    rw [← hi, ← D.localInvariantError_selected n i, D.selectedSubset_card]
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
    rw [← hi, ← hj, ← D.localMultiplicationError_selected n i j,
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
    rw [← hi, ← D.localFixedError_selected n i hii, D.selectedSubset_card]
    apply div_le_div_of_nonneg_right
      (D.fixedError_le_selectionError le_rfl hii n)
    positivity

noncomputable def selectedImageEquiv (n : ℕ) :
    indexedBlockModel (D.gammaDecomposition.blocks (D.matchingIndex n))
      (D.selectedComponent n) ≃ D.selectedSubset n where
  toFun x := ⟨D.distinguishedPerm (D.matchingIndex n) x,
    Finset.mem_image.mpr ⟨x, x.2, rfl⟩⟩
  invFun y := by
    refine ⟨(D.distinguishedPerm (D.matchingIndex n))⁻¹ y, ?_⟩
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp y.2
    have : (D.distinguishedPerm (D.matchingIndex n))⁻¹ y = x := by
      rw [← hxy]
      simp
    simpa [this] using hx
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv y := by
    apply Subtype.ext
    simp

noncomputable def selectedGraph (n : ℕ) : FiniteMultiGraph :=
  ((D.gammaDecomposition.modelGraph (D.matchingIndex n)).induce
    (D.selectedComponent n).block).transport
      { carrier := D.selectedSubset n
        fintype := inferInstance
        decidableEq := inferInstance }
      (D.selectedImageEquiv n)

theorem selectedGraph_expands (n : ℕ) :
    (D.selectedGraph n).HasCheegerLowerBound D.gammaDecomposition.cheeger := by
  exact FiniteMultiGraph.transport_hasCheegerLowerBound
    ((D.gammaDecomposition.modelGraph (D.matchingIndex n)).induce
      (D.selectedComponent n).block)
    { carrier := D.selectedSubset n
      fintype := inferInstance
      decidableEq := inferInstance }
    (D.selectedImageEquiv n)
    (by
      let y := BlockIndex.representative
        (D.gammaDecomposition.blocks (D.matchingIndex n)) (D.selectedComponent n)
      have h := D.gammaDecomposition.component_expands (D.matchingIndex n) y
      simpa [y, BlockIndex.block_representative] using h)

end LocalCriterionData

end NonsoficGroupsExist
