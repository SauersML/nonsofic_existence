import NonsoficGroupsExist.MaximalCutRepair
import NonsoficGroupsExist.SoficRestriction
import NonsoficGroupsExist.KunGeneratorGraph
import NonsoficGroupsExist.CompletionGraphEditing
import NonsoficGroupsExist.DirectedCoarea

/-!
# Repairing an essential expander approximation

This module applies maximal-cut removal to the actual first-factor generator
graphs in a `MatchingCertificate`.  Edit-negligibility gives an additive
Cheeger inequality, the removed cuts are proved negligible, and the induced
graphs on the retained vertices are eventually genuine expanders.
-/

namespace NonsoficGroupsExist
namespace EssentialExpanderRepair

open MaximalCutRepair

variable {K J : Type} [Group K] [Group J]

noncomputable abbrev actualGraph (C : MatchingCertificate K J) (n : ℕ) :
    FiniteMultiGraph :=
  generatorGraph (C.approx.model n) C.generatorsK
    (fun k ↦ C.approx.map n (k, 1))

noncomputable def graphEquiv (C : MatchingCertificate K J) (n : ℕ) :
    (actualGraph C n).vertex ≃ (C.graphs n).vertex :=
  (generatorGraphVertexEquiv (C.approx.model n) C.generatorsK
    (fun k ↦ C.approx.map n (k, 1))).trans (C.vertexEquiv n).symm

noncomputable def editCount (C : MatchingCertificate K J) (n : ℕ) : ℕ :=
  (actualGraph C n).editDistance (C.graphs n) (graphEquiv C n)

noncomputable def expansionConstant (C : MatchingCertificate K J) : ℝ :=
  C.cheeger / 4

noncomputable def removed (C : MatchingCertificate K J) (n : ℕ) :
    Finset (C.approx.model n) :=
  sparseCut (actualGraph C n) (expansionConstant C)

noncomputable def retained (C : MatchingCertificate K J) (n : ℕ) :
    Finset (C.approx.model n) :=
  MaximalCutRepair.retained (actualGraph C n) (expansionConstant C)

theorem expansionConstant_pos (C : MatchingCertificate K J) :
    0 < expansionConstant C := by
  exact div_pos C.cheeger_pos (by norm_num)

theorem additiveCheeger (C : MatchingCertificate K J) (n : ℕ)
    (U : Finset (C.approx.model n)) (hU : U.Nonempty)
    (hhalf : 2 * U.card ≤ Fintype.card (C.approx.model n)) :
    C.cheeger / 2 * (U.card : ℝ) ≤
      ((actualGraph C n).boundaryCard U : ℝ) + (editCount C n : ℝ) / 2 := by
  exact additiveCheeger_of_editDistance
    (actualGraph C n) (C.graphs n) (graphEquiv C n)
      (C.expands n) U hU hhalf

theorem removed_pointwise_bound (C : MatchingCertificate K J) (n : ℕ) :
    ((removed C n).card : ℝ) ≤
      (2 / C.cheeger) * editCount C n := by
  have hb := sparseCut_card_bound (actualGraph C n)
    (γ := C.cheeger / 2) (c := expansionConstant C)
    (E := (editCount C n : ℝ) / 2) (by positivity)
    (fun U hU hhalf ↦ additiveCheeger C n U hU hhalf)
  change ((removed C n).card : ℝ) ≤ _
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ C.cheeger_pos).2
  change ((removed C n).card : ℝ) * C.cheeger ≤
    2 * (editCount C n : ℝ)
  change (C.cheeger / 2 - C.cheeger / 4) *
      ((removed C n).card : ℝ) ≤ (editCount C n : ℝ) / 2 at hb
  linarith

theorem removed_negligible (C : MatchingCertificate K J) :
    Negligible (fun n ↦ (Fintype.card (C.approx.model n) : ℝ))
      fun n ↦ ((removed C n).card : ℝ) := by
  apply Negligible.mono_nonneg (fun _ ↦ by positivity) (fun _ ↦ by positivity)
    (fun n ↦ removed_pointwise_bound C n)
  have h := Negligible.const_mul (2 / C.cheeger) C.edit_negligible
  exact h

theorem actualGraph_boundary_degree (C : MatchingCertificate K J) (n : ℕ)
    (U : Finset (C.approx.model n)) :
    ((actualGraph C n).boundaryCard U : ℝ) ≤
      (2 * C.generatorsK.card : ℕ) * U.card := by
  rw [KunGeneratorGraph.boundaryCard_generatorGraph]
  exact_mod_cast KazhdanGNS.generatorCutSize_le_two_mul_card
    (C.approx.model n) (fun k ↦ C.approx.map n (k, 1)) C.generatorsK U

theorem eventually_nearHalf (C : MatchingCertificate K J) :
    ∃ N, ∀ n ≥ N,
      2 * ((editCount C n : ℝ) / 2 +
        (2 * C.generatorsK.card : ℕ) * (removed C n).card) ≤
      (C.cheeger / 2 - expansionConstant C) *
        ((Fintype.card (C.approx.model n) : ℝ) -
          2 * (removed C n).card) := by
  let coefficient : ℝ := 4 * C.generatorsK.card + C.cheeger / 2
  have htotal : Negligible
      (fun n ↦ (Fintype.card (C.approx.model n) : ℝ))
      (fun n ↦ (editCount C n : ℝ) +
        coefficient * (removed C n).card) :=
    Negligible.add C.edit_negligible
      (Negligible.const_mul coefficient (removed_negligible C))
  have hgap : 0 < C.cheeger / 4 := div_pos C.cheeger_pos (by norm_num)
  obtain ⟨Nsmall, hNsmall⟩ := htotal (C.cheeger / 4) hgap
  obtain ⟨Ncard, hNcard⟩ := C.approx.card_tendsToInfinity 1
  refine ⟨max Nsmall Ncard, fun n hn ↦ ?_⟩
  have hnsmall := (le_max_left Nsmall Ncard).trans hn
  have hncard := (le_max_right Nsmall Ncard).trans hn
  have hcardNat : 0 < Fintype.card (C.approx.model n) :=
    lt_of_lt_of_le Nat.zero_lt_one (hNcard n hncard)
  have hcard : (0 : ℝ) < Fintype.card (C.approx.model n) := by
    exact_mod_cast hcardNat
  have htotalNonneg : 0 ≤ (editCount C n : ℝ) +
      coefficient * (removed C n).card := by
    dsimp [coefficient]
    exact add_nonneg (by positivity)
      (mul_nonneg (add_nonneg (by positivity)
        (div_nonneg C.cheeger_pos.le (by norm_num))) (by positivity))
  have hratio := hNsmall n hnsmall
  rw [abs_of_nonneg (div_nonneg htotalNonneg hcard.le)] at hratio
  rw [div_lt_iff₀ hcard] at hratio
  dsimp [coefficient] at hratio
  dsimp [expansionConstant]
  push_cast
  linarith

theorem induced_expands_eventually (C : MatchingCertificate K J) :
    ∃ N, ∀ n ≥ N,
      ((actualGraph C n).induce (retained C n)).HasCheegerLowerBound
        (expansionConstant C) := by
  obtain ⟨N, hN⟩ := eventually_nearHalf C
  refine ⟨N, fun n hn ↦ ?_⟩
  apply induce_retained_hasCheegerLowerBound
    (actualGraph C n) (expansionConstant_pos C)
    (show expansionConstant C < C.cheeger / 2 by
      dsimp [expansionConstant]
      linarith [C.cheeger_pos])
    (fun U hU hhalf ↦ additiveCheeger C n U hU hhalf)
    (actualGraph_boundary_degree C n (removed C n))
    (hN n hn)

noncomputable def repairedLocalization (C : MatchingCertificate K J) :
    LocalizedApproximationData (K × J) :=
  SoficRestriction.localization C.approx (removed C) (removed_negligible C)

noncomputable def repairedApproximation (C : MatchingCertificate K J) :
    SoficApproximation (K × J) :=
  (repairedLocalization C).toSoficApproximation

noncomputable abbrev repairedActualGraph
    (C : MatchingCertificate K J) (n : ℕ) : FiniteMultiGraph :=
  generatorGraph ((repairedApproximation C).model n) C.generatorsK
    (fun k ↦ (repairedApproximation C).map n (k, 1))

/-- The second completion retains the expanding induced graph as a spanning
occurrence subgraph, so its actual first-factor generator graph expands. -/
theorem repairedActualGraph_expands_eventually
    (C : MatchingCertificate K J) :
    ∃ N, ∀ n ≥ N,
      (repairedActualGraph C n).HasCheegerLowerBound
        (expansionConstant C) := by
  obtain ⟨N, hN⟩ := induced_expands_eventually C
  refine ⟨N, fun n hn ↦ ?_⟩
  have hinduced := hN n hn
  refine ⟨expansionConstant_pos C, fun U hU hhalf ↦ ?_⟩
  have hsource := hinduced.2 U hU hhalf
  have hretain := CompletionGraphEditing.induce_boundaryCard_le_completed
    (U := retained C n) (T := C.generatorsK)
    (act := fun k ↦ C.approx.map n (k, 1))
    (completed := fun k ↦
      (repairedLocalization C).completedMap n (k, 1))
    (fun t x hx ↦
      (repairedLocalization C).completedMap_agrees n (t.1, 1) x hx) U
  have hretainReal :
      (((actualGraph C n).induce (retained C n)).boundaryCard U : ℝ) ≤
        (repairedActualGraph C n).boundaryCard U := by
    exact_mod_cast hretain
  exact hsource.trans hretainReal

/-- Enlarging the first-factor label set preserves the exact directed
Cheeger bound supplied by the repaired tagged generator graph. -/
theorem repairedDirected_expands_eventually
    (C : MatchingCertificate K J) (S : Finset K)
    (hKS : C.generatorsK ⊆ S) :
    ∃ N, ∀ n ≥ N,
      DirectedCoarea.HasCheegerLowerBound
        ((repairedApproximation C).model n)
        (AlmostAutomorphism.productLabels (repairedApproximation C) n S)
        (expansionConstant C) := by
  obtain ⟨Nexpand, hNexpand⟩ := repairedActualGraph_expands_eventually C
  obtain ⟨Ninject, hNinject⟩ :=
    AlmostAutomorphism.firstFactorLabels_injective_eventually
      (repairedApproximation C) C.generatorsK
  refine ⟨max Nexpand Ninject, fun n hn ↦ ?_⟩
  have hexpand := hNexpand n ((le_max_left Nexpand Ninject).trans hn)
  have hinject := hNinject n ((le_max_right Nexpand Ninject).trans hn)
  refine ⟨expansionConstant_pos C, fun U hU hhalf ↦ ?_⟩
  have hgraph := hexpand.2 U hU hhalf
  have htagged : (repairedActualGraph C n).boundaryCard U ≤
      (AlmostAutomorphism.directedBoundary
        ((repairedApproximation C).model n)
        (AlmostAutomorphism.productLabels (repairedApproximation C) n
          C.generatorsK) U).card := by
    rw [FiniteMultiGraph.boundaryCard,
      ← AlmostAutomorphism.crossingEdges_decide_mem]
    exact AlmostAutomorphism.generatorCrossing_card_le_directedBoundary
      (repairedApproximation C) n C.generatorsK hinject U
  have hlabelSubset :
      AlmostAutomorphism.productLabels (repairedApproximation C) n
          C.generatorsK ⊆
        AlmostAutomorphism.productLabels (repairedApproximation C) n S := by
    unfold AlmostAutomorphism.productLabels
    exact Finset.image_mono _ hKS
  have hboundarySubset :
      AlmostAutomorphism.directedBoundary
          ((repairedApproximation C).model n)
          (AlmostAutomorphism.productLabels (repairedApproximation C) n
            C.generatorsK) U ⊆
        AlmostAutomorphism.directedBoundary
          ((repairedApproximation C).model n)
          (AlmostAutomorphism.productLabels (repairedApproximation C) n S) U := by
    intro p hp
    rw [AlmostAutomorphism.mem_directedBoundary] at hp ⊢
    exact ⟨hlabelSubset hp.1, hp.2⟩
  have hboundaryCard := Finset.card_le_card hboundarySubset
  have hreal : ((repairedActualGraph C n).boundaryCard U : ℝ) ≤
      (AlmostAutomorphism.directedBoundary
        ((repairedApproximation C).model n)
        (AlmostAutomorphism.productLabels (repairedApproximation C) n S) U).card := by
    exact_mod_cast htagged.trans hboundaryCard
  exact hgraph.trans hreal

end EssentialExpanderRepair
end NonsoficGroupsExist
