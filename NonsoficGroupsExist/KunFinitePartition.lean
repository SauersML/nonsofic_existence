import NonsoficGroupsExist.KunPartition
import NonsoficGroupsExist.KunPartitionCrossing
import NonsoficGroupsExist.KunBlockGraph
import NonsoficGroupsExist.KunUniformDecompositionStep

/-!
# Instantiating Kun's finite partition recursion

The analytic small-boundary replacement theorem is connected here to the
finite minimal-cut recursion.  The resulting blocks already satisfy the
uniform cut inequality in the original generator graph.  The remaining graph
editing theorem will turn those global inequalities into Cheeger inequalities
inside disjoint edited components.
-/

namespace NonsoficGroupsExist
namespace KunFinitePartition

open KazhdanFiniteModel
open KunPartition
open KunPartitionCrossing
open KunBlockGraph
open KunUniformMovement
open KunUniformRounding
open KunUniformDecompositionStep
open scoped symmDiff

variable {G : Type} [Group G]

/-- In every sufficiently accurate finite model, the property-(T) replacement
theorem constructs an actual partition whose blocks have the uniform global
cut lower bound required in condition `(3)` of Kun's argument. -/
theorem finiteModel_propertyT_partition
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{0, 0} G Q ε)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S) (hεone : ε ≤ 1)
    (A : SoficApproximation G) (target : ℝ) (htarget : 0 < target) :
    ∃ k : ℕ, ∃ c : ℝ,
      0 ≤ c ∧ c < KunSmallBoundary.boundaryContraction S target ∧
      ∀ δ : ℝ, 0 < δ →
        ∃ N : ℕ, ∀ n ≥ N,
          ∃ Bcontract Bmovement : Finset (A.model n),
          ∃ P : BlockStructure (A.model n),
            (KunSmallBoundary.boundaryAlpha S target) ^ 2 *
                (((c + KunSmallBoundary.boundaryContraction S target) / 2) - c) ^ 2 *
                (Bcontract.card : ℝ) ≤
              ((S.card + 1) ^ (2 * (k + 1)) : ℕ) *
                (δ ^ 2 * Fintype.card (A.model n) : ℝ) ∧
            (KunSmallBoundary.boundaryAlpha S target) ^ 2 *
                ((movementConstant S ε + 1) - movementConstant S ε) ^ 2 *
                (Bmovement.card : ℝ) ≤
              ((S.card + 1) ^ (2 * (k + 1)) : ℕ) *
                (δ ^ 2 * Fintype.card (A.model n) : ℝ) ∧
            (((generatorGraph (A.model n) S (A.map n)).crossingEdges
                P.block).card : ℝ) ≤
              2 * (S.card : ℝ) * (Bcontract.card + Bmovement.card) +
                2 * target * Fintype.card (A.model n) ∧
            ((generatorGraph (A.model n) S (A.map n)).editDistance
                (KunBlockGraph.graph
                  (generatorGraph (A.model n) S (A.map n)) P)
                (Equiv.refl (A.model n)) : ℝ) ≤
              4 * (S.card : ℝ) * (Bcontract.card + Bmovement.card) +
                4 * target * Fintype.card (A.model n) ∧
            ∀ y : A.model n, ∀ U : Finset (A.model n),
              U ⊆ P.block y → U.Nonempty →
              2 * U.card ≤ (P.block y).card →
              uniformInputCutThreshold S (movementConstant S ε + 1) * U.card ≤
                (generatorGraph (A.model n) S (A.map n)).boundaryCard U := by
  obtain ⟨k, c, hc0, hc, hreplace⟩ :=
    finiteModel_propertyT_uniformSmallBoundaryReplacement hQ S hQS hone hεone
      A target htarget
  refine ⟨k, c, hc0, hc, fun δ hδ ↦ ?_⟩
  obtain ⟨N, hN⟩ := hreplace δ hδ
  refine ⟨N, fun n hn ↦ ?_⟩
  obtain ⟨Bcontract, Bmovement, hBcontractCard, hBmovementCard, hB⟩ := hN n hn
  let B := Bcontract ∪ Bmovement
  let X := generatorGraph (A.model n) S (A.map n)
  let γ := uniformInputCutThreshold S (movementConstant S ε + 1)
  have hS : S.Nonempty := ⟨1, hone⟩
  have hrule : ∀ T : Finset (A.model n), T.Nonempty → Disjoint T B →
      (X.boundaryCard T : ℝ) < γ * T.card →
      ∃ W : Finset (A.model n),
        ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3 ∧
        (X.boundaryCard W : ℝ) < target * T.card := by
    intro T hT hTB hcut
    obtain ⟨W, hclose, hboundary⟩ := hB T hT hTB
    refine ⟨W, ?_, hboundary⟩
    have hcut' : (KazhdanGNS.generatorCutSize (A.model n) (A.map n) S T : ℝ) <
        uniformInputCutThreshold S (movementConstant S ε + 1) * T.card := by
      simpa [X, γ, KunGeneratorGraph.boundaryCard_generatorGraph] using hcut
    exact symmDiff_lt_third_of_uniform_cut (A.model n) (A.map n) S hS
      (movementConstant S ε + 1) T W hclose hcut'
  let P := blockStructure (X := X) B γ target hrule
  have hBcardNat : B.card ≤ Bcontract.card + Bmovement.card := by
    simpa [B] using Finset.card_union_le Bcontract Bmovement
  have hBcardReal : (B.card : ℝ) ≤
      (Bcontract.card : ℝ) + Bmovement.card := by
    exact_mod_cast hBcardNat
  have hcrossBase := card_crossingEdges_generatorGraph_real_le
    (A.model n) S (A.map n) B γ target htarget.le hrule
  have hcross :
      (((generatorGraph (A.model n) S (A.map n)).crossingEdges P.block).card : ℝ) ≤
        2 * (S.card : ℝ) * (Bcontract.card + Bmovement.card) +
          2 * target * Fintype.card (A.model n) := by
    calc
      (((generatorGraph (A.model n) S (A.map n)).crossingEdges P.block).card : ℝ) ≤
          2 * (S.card : ℝ) * B.card +
            2 * target * Fintype.card (A.model n) := by
        simpa [X, P] using hcrossBase
      _ ≤ 2 * (S.card : ℝ) * (Bcontract.card + Bmovement.card) +
          2 * target * Fintype.card (A.model n) := by gcongr
  have heditNat := editDistance_le_two_mul_crossing X P
  have heditReal :
      (X.editDistance (KunBlockGraph.graph X P) (Equiv.refl X.vertex) : ℝ) ≤
        2 * ((X.crossingEdges P.block).card : ℝ) := by
    exact_mod_cast heditNat
  have hedit :
      ((generatorGraph (A.model n) S (A.map n)).editDistance
          (KunBlockGraph.graph
            (generatorGraph (A.model n) S (A.map n)) P)
          (Equiv.refl (A.model n)) : ℝ) ≤
        4 * (S.card : ℝ) * (Bcontract.card + Bmovement.card) +
          4 * target * Fintype.card (A.model n) := by
    calc
      ((generatorGraph (A.model n) S (A.map n)).editDistance
          (KunBlockGraph.graph
            (generatorGraph (A.model n) S (A.map n)) P)
          (Equiv.refl (A.model n)) : ℝ) ≤
        2 * (((generatorGraph (A.model n) S (A.map n)).crossingEdges
          P.block).card : ℝ) := by simpa [X] using heditReal
      _ ≤ 2 * (2 * (S.card : ℝ) *
          (Bcontract.card + Bmovement.card) +
            2 * target * Fintype.card (A.model n)) := by gcongr
      _ = 4 * (S.card : ℝ) * (Bcontract.card + Bmovement.card) +
          4 * target * Fintype.card (A.model n) := by ring
  refine ⟨Bcontract, Bmovement, P, hBcontractCard, hBmovementCard,
    hcross, hedit, fun y U hUP hU hhalf ↦ ?_⟩
  exact blockStructure_block_expands (X := X) B γ target hrule y U hUP hU hhalf

end KunFinitePartition
end NonsoficGroupsExist
