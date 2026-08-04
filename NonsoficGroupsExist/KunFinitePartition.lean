import NonsoficGroupsExist.KunPartition

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
open KunDecompositionStep
open KunPartition
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
          ∃ B : Finset (A.model n),
          ∃ P : BlockStructure (A.model n),
            (KunSmallBoundary.boundaryAlpha S target) ^ 2 *
                (KunSmallBoundary.boundaryContraction S target - c) ^ 2 *
                (B.card : ℝ) ≤
              ((S.card + 1) ^ (2 * (k + 1)) : ℕ) *
                (δ ^ 2 * Fintype.card (A.model n) : ℝ) ∧
            ∀ y : A.model n, ∀ U : Finset (A.model n),
              U ⊆ P.block y → U.Nonempty →
              2 * U.card ≤ (P.block y).card →
              inputCutThreshold S k * U.card ≤
                (generatorGraph (A.model n) S (A.map n)).boundaryCard U := by
  obtain ⟨k, c, hc0, hc, hreplace⟩ :=
    finiteModel_propertyT_smallBoundaryReplacement hQ S hQS hone hεone
      A target htarget
  refine ⟨k, c, hc0, hc, fun δ hδ ↦ ?_⟩
  obtain ⟨N, hN⟩ := hreplace δ hδ
  refine ⟨N, fun n hn ↦ ?_⟩
  obtain ⟨B, hBcard, hB⟩ := hN n hn
  let X := generatorGraph (A.model n) S (A.map n)
  let γ := inputCutThreshold S k
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
        inputCutThreshold S k * T.card := by
      simpa [X, γ, KunGeneratorGraph.boundaryCard_generatorGraph] using hcut
    exact symmDiff_lt_third_of_cut_lt (A.model n) (A.map n) S hS k
      T W hclose hcut'
  let P := blockStructure (X := X) B γ target hrule
  refine ⟨B, P, hBcard, fun y U hUP hU hhalf ↦ ?_⟩
  exact blockStructure_block_expands (X := X) B γ target hrule y U hUP hU hhalf

end KunFinitePartition
end NonsoficGroupsExist
