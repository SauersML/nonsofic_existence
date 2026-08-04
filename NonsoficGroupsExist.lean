import NonsoficGroupsExist.Asymptotics
import NonsoficGroupsExist.AlmostAutomorphism
import NonsoficGroupsExist.DirectedCoarea
import NonsoficGroupsExist.KazhdanImprovement
import NonsoficGroupsExist.Kazhdan
import NonsoficGroupsExist.KazhdanOrthogonal
import NonsoficGroupsExist.KazhdanFiniteModel
import NonsoficGroupsExist.KazhdanGNS
import NonsoficGroupsExist.KunFiniteMarkov
import NonsoficGroupsExist.KunBoundary
import NonsoficGroupsExist.CompressionSetup
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
import NonsoficGroupsExist.Leavitt
import NonsoficGroupsExist.ConcreteLeavitt
import NonsoficGroupsExist.FiniteGraph
import NonsoficGroupsExist.LeavittCorner
import NonsoficGroupsExist.LeavittMatrixCompression
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
import NonsoficGroupsExist.RankFourCompressors
import NonsoficGroupsExist.ConcreteRankFour
import NonsoficGroupsExist.ConcreteCompressionSetup
import NonsoficGroupsExist.ThompsonWitness
import NonsoficGroupsExist.MatchedComponents
import NonsoficGroupsExist.SoficTransfer

/-!
# Partial formalization of a proposed nonsofic-group construction

This library contains proved finite, asymptotic, Leavitt-family, elementary
matrix, non-LEF-obstruction, localization, and finite-table results.  It does
**not** currently prove that a nonsofic group exists.

In particular, no declaration in this root module assumes a proposition named
after Kun, Kun--Thom, or Ershov--Jaikin and then advertises the resulting
conditional implication as an existence theorem.  The uninstantiated
`ExpanderDecomposition`, `MatchingCertificate`, and `LocalCriterionData`
structures remain specifications for intermediate conditional mathematics.
They are not evidence that the corresponding analytic data have been
constructed.  In contrast, `ConcreteRankFour.compressionSetup` is an actual
inhabitant of the algebraic `CompressionSetup` interface.

The concrete stream-operator algebra proves the binary Leavitt relations but
has not been identified with the universal Leavitt algebra.  The two explicit
cylinder units prove a genuine finite non-LEF obstruction for their generated
corner subgroup; the development does not identify that subgroup with
Thompson's group `V`.  Their generated subgroup is now embedded in `EL₃` by
explicit cylinder-commutator and Whitehead identities.  The rank-four module
also proves compressor conjugation, ambient generation, centralization, and
trivial intersection, and `ConcreteRankFour.compressionSetup` constructs the
complete algebraic setup rather than accepting it from a caller.

`TableCover` proves only the conditional finite-presentation reduction: from a
finitely generated nonsofic group it constructs a finitely presented nonsofic
cover.  It does not furnish the initial nonsofic group.
-/
