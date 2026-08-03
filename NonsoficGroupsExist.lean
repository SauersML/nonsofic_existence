import NonsoficGroupsExist.Asymptotics
import NonsoficGroupsExist.Kazhdan
import NonsoficGroupsExist.CompressionSetup
import NonsoficGroupsExist.ExternalInputs
import NonsoficGroupsExist.LocalCriterion
import NonsoficGroupsExist.LocalizedApproximation
import NonsoficGroupsExist.SelectionOutput
import NonsoficGroupsExist.Pinning
import NonsoficGroupsExist.Refinement
import NonsoficGroupsExist.Selection
import NonsoficGroupsExist.MedianNormalization
import NonsoficGroupsExist.LEF
import NonsoficGroupsExist.ThompsonObstruction
import NonsoficGroupsExist.Scheme
import NonsoficGroupsExist.Criterion
import NonsoficGroupsExist.BlockEnumeration
import NonsoficGroupsExist.BlockIndex
import NonsoficGroupsExist.ComponentDivergence
import NonsoficGroupsExist.GeneratorWords
import NonsoficGroupsExist.BlockWordCrossing
import NonsoficGroupsExist.BlockTransport
import NonsoficGroupsExist.ComponentRefinement
import NonsoficGroupsExist.DecompositionRefinement
import NonsoficGroupsExist.EdgeEditing
import NonsoficGroupsExist.GeneratorCrossing
import NonsoficGroupsExist.ExternalCompressorCrossing
import NonsoficGroupsExist.CompressionRefinement
import NonsoficGroupsExist.FiniteMedian
import NonsoficGroupsExist.NormalizedComponents
import NonsoficGroupsExist.ComponentPinning
import NonsoficGroupsExist.NormalizedVariation
import NonsoficGroupsExist.InverseNormalization
import NonsoficGroupsExist.GlobalVariation
import NonsoficGroupsExist.SlowThreshold
import NonsoficGroupsExist.FiniteMarkov
import NonsoficGroupsExist.MatchingPreparation
import NonsoficGroupsExist.MatchingSelection
import NonsoficGroupsExist.EdgeWitnessDistance
import NonsoficGroupsExist.EdgeWitnessRestriction
import NonsoficGroupsExist.GeneratorGraphEditing
import NonsoficGroupsExist.CompletionGraphEditing
import NonsoficGroupsExist.SelectedGraphComparison
import NonsoficGroupsExist.ConservativeMatching
import NonsoficGroupsExist.CriterionAssembly
import NonsoficGroupsExist.MainResults
import NonsoficGroupsExist.Leavitt
import NonsoficGroupsExist.ConcreteLeavitt
import NonsoficGroupsExist.FiniteGraph
import NonsoficGroupsExist.LeavittCorner
import NonsoficGroupsExist.LeavittSelfSimilarity
import NonsoficGroupsExist.Localization
import NonsoficGroupsExist.MatrixSelfSimilarity
import NonsoficGroupsExist.PermutationConservation
import NonsoficGroupsExist.Sofic
import NonsoficGroupsExist.SoficErrors
import NonsoficGroupsExist.Whitehead
import NonsoficGroupsExist.TableCover
import NonsoficGroupsExist.LeavittWords
import NonsoficGroupsExist.PrefixCode
import NonsoficGroupsExist.ElementaryGroup
import NonsoficGroupsExist.ElementaryStabilization
import NonsoficGroupsExist.ThompsonWitness
import NonsoficGroupsExist.MatchedComponents
import NonsoficGroupsExist.SoficTransfer

/-!
# Nonsofic Groups Exist

This is the root of the Lean development accompanying
`nonsofic_groups_exist.tex`.  The modules follow the manuscript:

## Concise proof plan

1. Main idea: apply Kun's expander decomposition to the subgroup and ambient
   sofic approximations; use compressor conjugacy, permutation conservation,
   co-area pinning, conservative component matching, diagonal selection, and
   localization to obtain an essentially expanding approximation of `Γ × J`.
   Kun--Thom then forces `J` to be LEF, contradicting the supplied non-LEF
   corner witness.  A finite multiplication-table quotient gives the finitely
   presented consequence.
2. Main declarations and tactics: `FiniteMultiGraph.median_pinning`,
   `FiniteMultiGraph.exists_dominant_cell`, `permutation_conservation_abs`,
   `exists_selection_diverging`, `Localization.exists_completion_with_bound`,
   `FiniteMultiGraph.editDistance_triangle`, finite `Finset` sum/cardinality
   lemmas, and `linarith`/`nlinarith`/`positivity`/`omega` for numerical bounds.
3. Intermediate facts: negligible total compressor variation; a slowly
   vanishing threshold; negligible discarded component mass; injectivity of
   acceptable target matching; a selected component whose error ratio vanishes
   and whose size diverges; localized multiplicativity, faithfulness, and
   invariance; and negligible edit distance to the selected expander graph.
4. Coercion and rewriting points: cardinalities move between `ℕ` and `ℝ`;
   vertices of induced graphs are subtypes; transported permutations require
   explicit `Equiv` coercions; block equality is recovered from membership;
   and normalized estimates require positive finite-cardinality denominators.

| manuscript | module |
| --- | --- |
| Definition `def:sofic`, Lemma `lem:word` | `Sofic` |
| the `o(|Yₙ|)` bookkeeping used in Sections 3--4 | `Asymptotics` |
| Lemma `lem:coarea` | `FiniteGraph` |
| Lemma `lem:refine` | `Refinement` |
| Lemma `lem:conserve` | `PermutationConservation` |
| Lemma `lem:pin` | `Pinning` |
| Lemma `lem:select` | `Selection` |
| Lemma `lem:complete` | `Localization` |
| Section `subsec:median`, Proposition `prop:match` | `MedianNormalization`, `Criterion` |
| Section `subsec:lef` | `LEF` |
| Higman-free replacement for Proposition `prop:vnotlef` | `ThompsonObstruction` |
| Lemma `lem:leaf`, Lemma `lem:chartwo` | `Leavitt`, `LeavittWords` |
| prefix codes and completeness, `def:code` | `PrefixCode` |
| Proposition `prop:selfsim`, equation `eq:Theta-main` | `MatrixSelfSimilarity`, `LeavittSelfSimilarity`, `PrefixCode` |
| Lemma `lem:corner`, Proposition `prop:KJ` | `LeavittCorner`, `Scheme` |
| Lemma `lem:whitehead`, `EL_ι(M_κ(R)) ≅ EL_{ι×κ}(R)` | `Whitehead`, `ElementaryGroup` |
| Proposition `prop:vnotlef` (explicit `V`-witness) | `ThompsonWitness` |
| Section `subsec:selection` matched-component bookkeeping | `MatchedComponents` |
| conservative matching and diagonal localization | `MatchingPreparation`, `MatchingSelection` |
| occurrence restriction and final graph comparison | `EdgeWitnessDistance`, `EdgeWitnessRestriction`, `SelectedGraphComparison` |
| restriction of `σₙ` to a subgroup | `SoficTransfer` |
| Section `sec:fp`, Theorem `thm:table` | `TableCover` |

The cited inputs are isolated as ordinary proposition parameters:
`KunTheorem`, `KunThomTheorem`, and `ErshovJaikinTheorem`.  The algebraic
hypotheses of the general criterion are recorded without omission in
`CompressionSetup`.  The manuscript's appeal to simplicity and finite
presentation of Thompson's group `V` is replaced by the elementary two-relator
argument of `ThompsonObstruction`, whose hypotheses are discharged by the
explicit pair of cylinder units built in `ThompsonWitness`.
-/

#print axioms NonsoficGroupsExist.LeavittFamily.characteristicTwo_involution
#print axioms NonsoficGroupsExist.HasKazhdanPropertyT.mulEquiv_iff
#print axioms NonsoficGroupsExist.CompressionSetup.productEmbedding_injective
#print axioms NonsoficGroupsExist.KunTheorem
#print axioms NonsoficGroupsExist.KunThomTheorem
#print axioms NonsoficGroupsExist.ErshovJaikinTheorem
#print axioms NonsoficGroupsExist.CompressionSetup.ambientGenerators_generate
#print axioms NonsoficGroupsExist.LocalizedApproximationData.completedMap_disagreement_vanishing
#print axioms NonsoficGroupsExist.LocalizedApproximationData.toSoficApproximation
#print axioms NonsoficGroupsExist.SelectionOutput.toMatchingCertificate
#print axioms NonsoficGroupsExist.SelectionOutput.isLEF
#print axioms NonsoficGroupsExist.Vanishing.add
#print axioms NonsoficGroupsExist.Vanishing.sum
#print axioms NonsoficGroupsExist.Negligible.mono
#print axioms NonsoficGroupsExist.Negligible.sum
#print axioms NonsoficGroupsExist.FiniteMultiGraph.median_pinning
#print axioms NonsoficGroupsExist.FiniteMultiGraph.exists_dominant_cell
#print axioms NonsoficGroupsExist.exists_selection_diverging
#print axioms NonsoficGroupsExist.medianNormalize_loss
#print axioms NonsoficGroupsExist.medianNormalize_ratio
#print axioms NonsoficGroupsExist.card_symmDiff_le
#print axioms NonsoficGroupsExist.exists_local_word_control
#print axioms NonsoficGroupsExist.ThompsonObstruction.finite_commute_of_two_relations
#print axioms NonsoficGroupsExist.ThompsonObstruction.not_isLEF_of_two_relations
#print axioms NonsoficGroupsExist.LeavittFamily.compressed_inf_corner
#print axioms NonsoficGroupsExist.LeavittFamily.not_isLEF_cornerSubgroup
#print axioms NonsoficGroupsExist.FiniteMultiGraph.editDistance_self
#print axioms NonsoficGroupsExist.onesided_drop
#print axioms NonsoficGroupsExist.card_ratio_of_pinned
#print axioms NonsoficGroupsExist.symmDiff_le_of_pinned
#print axioms NonsoficGroupsExist.matching_injective
#print axioms NonsoficGroupsExist.BlockStructure.sum_card_blocksFinset
#print axioms NonsoficGroupsExist.BlockIndex.sum_card
#print axioms NonsoficGroupsExist.BlockIndex.sum_sum
#print axioms NonsoficGroupsExist.SoficApproximation.smallBlockVertices_negligible
#print axioms NonsoficGroupsExist.ExpanderDecomposition.smallBlockVertices_negligible
#print axioms NonsoficGroupsExist.exists_generator_word
#print axioms NonsoficGroupsExist.SoficApproximation.all_wordCrossing_negligible
#print axioms NonsoficGroupsExist.BlockStructure.transport_blocksFinset
#print axioms NonsoficGroupsExist.refineComponent
#print axioms NonsoficGroupsExist.ComponentRefinement.image_sdiff_target_card
#print axioms NonsoficGroupsExist.ComponentRefinement.cheeger_mul_leakage_le_crossing
#print axioms NonsoficGroupsExist.ExpanderDecomposition.refineAt_leakage
#print axioms NonsoficGroupsExist.ExpanderDecomposition.refineBlock_leakage
#print axioms NonsoficGroupsExist.ExpanderDecomposition.cheeger_mul_totalLeakage_le_crossings
#print axioms NonsoficGroupsExist.ExpanderDecomposition.sum_componentCrossingCount
#print axioms NonsoficGroupsExist.ExpanderDecomposition.cheeger_mul_totalLeakage_le_globalCrossing
#print axioms NonsoficGroupsExist.EdgeEditWitness.targetCrossing_card_le_unmatchedCount
#print axioms NonsoficGroupsExist.SoficApproximation.generatorGraph_crossing_card_le
#print axioms NonsoficGroupsExist.ExpanderDecomposition.globalCrossing_negligible
#print axioms NonsoficGroupsExist.ExpanderDecomposition.externalGlobalCrossing_negligible
#print axioms NonsoficGroupsExist.CompressionSetup.compressorLeakage_negligible
#print axioms NonsoficGroupsExist.FiniteMultiGraph.natMedian_isMedian
#print axioms NonsoficGroupsExist.normalizedSize_isMedian_on_block
#print axioms NonsoficGroupsExist.ExpanderDecomposition.normalized_pinning_global
#print axioms NonsoficGroupsExist.SoficApproximation.inverseError_negligible
#print axioms NonsoficGroupsExist.inverse_variation_eq
#print axioms NonsoficGroupsExist.LocalCriterionData.modelGraphVariation_negligible
#print axioms NonsoficGroupsExist.LocalCriterionData.normalizedDeviation_negligible
#print axioms NonsoficGroupsExist.LocalCriterionData.acceptable_symmDiff_sum_negligible
#print axioms NonsoficGroupsExist.threshold_mul_card_le_sum
#print axioms NonsoficGroupsExist.threshold_mul_badBlockMass_le
#print axioms NonsoficGroupsExist.error_div_slowThreshold_vanishing
#print axioms NonsoficGroupsExist.FiniteMultiGraph.editDistance_triangle
#print axioms NonsoficGroupsExist.EdgeEditWitness.editDistance_le_two_mul_unmatchedCount
#print axioms NonsoficGroupsExist.EdgeEditWitness.induce_unmatchedCount_le_filters
#print axioms NonsoficGroupsExist.LocalCriterionData.selectedLocalization
#print axioms NonsoficGroupsExist.LocalCriterionData.localized_to_completed_disagreement_negligible
#print axioms NonsoficGroupsExist.LocalCriterionData.selectedGraph_edit_negligible
#print axioms NonsoficGroupsExist.conservativeMatchingTheorem
#print axioms NonsoficGroupsExist.not_isSofic_of_kazhdan_compression
#print axioms NonsoficGroupsExist.nonsofic_groups_exist
#print axioms NonsoficGroupsExist.explicit_spine_not_sofic
#print axioms NonsoficGroupsExist.finitelyPresented_nonsofic_cover
#print axioms NonsoficGroupsExist.finitely_presented_nonsofic_groups_exist
#print axioms NonsoficGroupsExist.compression_centralizer
#print axioms NonsoficGroupsExist.LeavittFamily.characteristicTwo_compressor
#print axioms NonsoficGroupsExist.LeavittFamily.z_sq
#print axioms NonsoficGroupsExist.permutation_conservation
#print axioms NonsoficGroupsExist.permutation_conservation_abs
#print axioms NonsoficGroupsExist.permutation_conservation_full
#print axioms NonsoficGroupsExist.Whitehead.whitehead_diagonal
#print axioms NonsoficGroupsExist.Whitehead.whitehead_commutator
#print axioms NonsoficGroupsExist.Whitehead.whitehead_commutator_mem
#print axioms NonsoficGroupsExist.CompleteMatrixFamily.matrixRingEquiv
#print axioms NonsoficGroupsExist.CompleteMatrixFamily.unitsEquiv
#print axioms NonsoficGroupsExist.LeavittFamily.binaryMatrixRingEquiv
#print axioms NonsoficGroupsExist.LeavittFamily.binaryUnitsEquiv
#print axioms NonsoficGroupsExist.LeavittFamily.cornerHom
#print axioms NonsoficGroupsExist.LeavittFamily.cornerHom_injective
#print axioms NonsoficGroupsExist.LeavittFamily.compressedHom
#print axioms NonsoficGroupsExist.LeavittFamily.compressedHom_commutes_cornerHom
#print axioms NonsoficGroupsExist.LeavittFamily.compressedHom_eq_cornerHom_iff
#print axioms NonsoficGroupsExist.hammingDistance
#print axioms NonsoficGroupsExist.hammingDistance_eq_zero_iff
#print axioms NonsoficGroupsExist.hammingDistance_left_invariant
#print axioms NonsoficGroupsExist.hammingDistance_right_invariant
#print axioms NonsoficGroupsExist.hammingDistance_triangle
#print axioms NonsoficGroupsExist.SoficApproximation
#print axioms NonsoficGroupsExist.SoficApproximation.map_one_close
#print axioms NonsoficGroupsExist.SoficApproximation.word_close
#print axioms NonsoficGroupsExist.SoficApproximation.multiplicationError_negligible
#print axioms NonsoficGroupsExist.SoficApproximation.fixedError_negligible
#print axioms NonsoficGroupsExist.SoficApproximation.collisionError_negligible
#print axioms NonsoficGroupsExist.SoficApproximation.conjugacyError_negligible
#print axioms NonsoficGroupsExist.IsSofic
#print axioms NonsoficGroupsExist.FiniteMultiGraph.HasCheegerLowerBound
#print axioms NonsoficGroupsExist.FiniteMultiGraph.transport_boundaryCard
#print axioms NonsoficGroupsExist.FiniteMultiGraph.transport_hasCheegerLowerBound
#print axioms NonsoficGroupsExist.FiniteMultiGraph.IsMedian.eq_of_subsingleton
#print axioms NonsoficGroupsExist.FiniteMultiGraph.positivePart_edge_add_negativePart_edge
#print axioms NonsoficGroupsExist.FiniteMultiGraph.nonnegative_coarea
#print axioms NonsoficGroupsExist.FiniteMultiGraph.coarea_mul
#print axioms NonsoficGroupsExist.FiniteMultiGraph.coarea
#print axioms NonsoficGroupsExist.Localization.exists_completion_with_bound
#print axioms NonsoficGroupsExist.Localization.involutiveCompletion_sq
#print axioms NonsoficGroupsExist.Localization.involutiveCompletion_disagreement_bound
#print axioms NonsoficGroupsExist.FiniteMultiGraph.exists_dominant_cell
#print axioms NonsoficGroupsExist.FiniteMultiGraph.median_pinning
#print axioms NonsoficGroupsExist.FiniteMultiGraph.IsMedian.comp_increasing
#print axioms NonsoficGroupsExist.exists_le_weighted_average
#print axioms NonsoficGroupsExist.exists_selection
#print axioms NonsoficGroupsExist.exists_selection_diverging
#print axioms NonsoficGroupsExist.medianNormalize_loss
#print axioms NonsoficGroupsExist.medianNormalize_ratio
#print axioms NonsoficGroupsExist.card_symmDiff_add_two_mul_inter
#print axioms NonsoficGroupsExist.dominant_intersection_unique
#print axioms NonsoficGroupsExist.onesided_drop
#print axioms NonsoficGroupsExist.card_ratio_of_pinned
#print axioms NonsoficGroupsExist.symmDiff_le_of_pinned
#print axioms NonsoficGroupsExist.matching_injective
#print axioms NonsoficGroupsExist.ThompsonObstruction.finite_commute_of_two_relations
#print axioms NonsoficGroupsExist.ThompsonObstruction.not_isLEF_of_two_relations
#print axioms NonsoficGroupsExist.LeavittFamily.commute_compressed_corner
#print axioms NonsoficGroupsExist.LeavittFamily.compressed_inf_corner
#print axioms NonsoficGroupsExist.LeavittFamily.not_isLEF_cornerSubgroup
#print axioms NonsoficGroupsExist.tableModel_of_isSofic
#print axioms NonsoficGroupsExist.isSofic_of_tableModels
#print axioms NonsoficGroupsExist.exists_table_obstruction
#print axioms NonsoficGroupsExist.tableGroup_no_model
#print axioms NonsoficGroupsExist.exists_finitelyPresented_obstruction
#print axioms NonsoficGroupsExist.LeavittFamily.wordT_mul_wordS_self
#print axioms NonsoficGroupsExist.LeavittFamily.wordT_mul_wordS_of_incomparable
#print axioms NonsoficGroupsExist.LeavittFamily.cylinder_isIdempotent
#print axioms NonsoficGroupsExist.LeavittFamily.cylinder_mul_of_incomparable
#print axioms NonsoficGroupsExist.LeavittFamily.cylinder_split
#print axioms NonsoficGroupsExist.LeavittFamily.prefixCode_orthogonal
#print axioms NonsoficGroupsExist.LeavittFamily.prefixRingEquiv
#print axioms NonsoficGroupsExist.LeavittFamily.prefixUnitsEquiv
#print axioms NonsoficGroupsExist.elementaryUnit_commutator
#print axioms NonsoficGroupsExist.elementaryGroup_infinite
#print axioms NonsoficGroupsExist.elementaryGroup_finitelyGenerated
#print axioms NonsoficGroupsExist.elementaryReindexEquiv
#print axioms NonsoficGroupsExist.elementaryBlockEquiv
#print axioms NonsoficGroupsExist.LeavittFamily.cylinderSwap
#print axioms NonsoficGroupsExist.LeavittFamily.prefixInsertion
#print axioms NonsoficGroupsExist.LeavittFamily.prefixInsertion_conjugate
#print axioms NonsoficGroupsExist.LeavittFamily.commute_prefixInsertion_of_fixed
#print axioms NonsoficGroupsExist.LeavittFamily.relator_one
#print axioms NonsoficGroupsExist.LeavittFamily.relator_two
#print axioms NonsoficGroupsExist.LeavittFamily.generators_not_commute
#print axioms NonsoficGroupsExist.LeavittFamily.not_isLEF_cornerSubgroup_of_witness
#print axioms NonsoficGroupsExist.matchedCore_missing_card
#print axioms NonsoficGroupsExist.matchedCore_missing_card_le_symmDiff
#print axioms NonsoficGroupsExist.matching_injOn
#print axioms NonsoficGroupsExist.wordCrossing_subset
#print axioms NonsoficGroupsExist.wordCrossing_card_le
#print axioms NonsoficGroupsExist.matchedCore_missing_negligible
#print axioms NonsoficGroupsExist.wordCrossing_negligible
#print axioms NonsoficGroupsExist.SoficApproximation.comap
#print axioms NonsoficGroupsExist.isSofic_of_injective
#print axioms NonsoficGroupsExist.SoficApproximation.restrict
