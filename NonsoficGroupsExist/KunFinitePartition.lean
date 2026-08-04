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

/-- Quantitative form of the finite partition theorem in which the internal
sofic tolerance is chosen so that the total exceptional density is below an
arbitrary prescribed `ρ`.  Only the resulting crossing estimate and the
uniform block cut estimate remain in the interface. -/
theorem finiteModel_propertyT_partition_with_density
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{0, 0} G Q ε)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S) (hεone : ε ≤ 1)
    (A : SoficApproximation G) (target ρ : ℝ)
    (htarget : 0 < target) (hρ : 0 < ρ) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ P : BlockStructure (A.model n),
      (((generatorGraph (A.model n) S (A.map n)).crossingEdges
          P.block).card : ℝ) ≤
        (2 * (S.card : ℝ) * ρ + 2 * target) *
          Fintype.card (A.model n) ∧
      ∀ y : A.model n, ∀ U : Finset (A.model n),
        U ⊆ P.block y → U.Nonempty →
        2 * U.card ≤ (P.block y).card →
        uniformInputCutThreshold S (movementConstant S ε + 1) * U.card ≤
          (generatorGraph (A.model n) S (A.map n)).boundaryCard U := by
  classical
  obtain ⟨k, c, _hc0, hc, hpart⟩ :=
    finiteModel_propertyT_partition hQ S hQS hone hεone A target htarget
  have hS : S.Nonempty := ⟨1, hone⟩
  let a₁ : ℝ :=
    (KunSmallBoundary.boundaryAlpha S target) ^ 2 *
      (((c + KunSmallBoundary.boundaryContraction S target) / 2) - c) ^ 2
  let a₂ : ℝ :=
    (KunSmallBoundary.boundaryAlpha S target) ^ 2 *
      ((movementConstant S ε + 1) - movementConstant S ε) ^ 2
  have hα : 0 < KunSmallBoundary.boundaryAlpha S target :=
    KunSmallBoundary.boundaryAlpha_pos S hS htarget
  have hgap : 0 <
      ((c + KunSmallBoundary.boundaryContraction S target) / 2) - c := by
    linarith [hc]
  have ha₁ : 0 < a₁ := by
    dsimp [a₁]
    positivity
  have ha₂ : 0 < a₂ := by
    dsimp [a₂]
    have hdiff : (movementConstant S ε + 1) - movementConstant S ε = 1 := by
      ring
    rw [hdiff]
    positivity
  let a : ℝ := min a₁ a₂
  have ha : 0 < a := lt_min ha₁ ha₂
  let θ : ℝ := ρ / 2
  have hθ : 0 < θ := by dsimp [θ]; positivity
  let R : ℝ := ((S.card + 1) ^ (2 * (k + 1)) : ℕ)
  have hR : 0 < R := by
    dsimp [R]
    positivity
  let δ : ℝ := Real.sqrt (a * θ / R)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact Real.sqrt_pos.2 (div_pos (mul_pos ha hθ) hR)
  have hRδ : R * δ ^ 2 = a * θ := by
    dsimp [δ]
    rw [Real.sq_sqrt (div_nonneg (mul_nonneg ha.le hθ.le) hR.le)]
    field_simp
  obtain ⟨N, hN⟩ := hpart δ hδ
  refine ⟨N, fun n hn ↦ ?_⟩
  obtain ⟨Bcontract, Bmovement, P, hBcontract, hBmovement,
    hcross, _hedit, hexpand⟩ := hN n hn
  have hcontract : (Bcontract.card : ℝ) ≤
      θ * Fintype.card (A.model n) := by
    have hscale : a * (Bcontract.card : ℝ) ≤
        a₁ * Bcontract.card := by
      exact mul_le_mul_of_nonneg_right (min_le_left a₁ a₂) (by positivity)
    have hbound : a * (Bcontract.card : ℝ) ≤
        a * (θ * Fintype.card (A.model n)) := by
      calc
        a * (Bcontract.card : ℝ) ≤ a₁ * Bcontract.card := hscale
        _ ≤ R * (δ ^ 2 * Fintype.card (A.model n)) := by
          simpa [a₁, R] using hBcontract
        _ = a * (θ * Fintype.card (A.model n)) := by
          rw [mul_assoc, hRδ]
          ring
    exact (mul_le_mul_left ha).mp hbound
  have hmovement : (Bmovement.card : ℝ) ≤
      θ * Fintype.card (A.model n) := by
    have hscale : a * (Bmovement.card : ℝ) ≤
        a₂ * Bmovement.card := by
      exact mul_le_mul_of_nonneg_right (min_le_right a₁ a₂) (by positivity)
    have hbound : a * (Bmovement.card : ℝ) ≤
        a * (θ * Fintype.card (A.model n)) := by
      calc
        a * (Bmovement.card : ℝ) ≤ a₂ * Bmovement.card := hscale
        _ ≤ R * (δ ^ 2 * Fintype.card (A.model n)) := by
          simpa [a₂, R] using hBmovement
        _ = a * (θ * Fintype.card (A.model n)) := by
          rw [mul_assoc, hRδ]
          ring
    exact (mul_le_mul_left ha).mp hbound
  have hbad : (Bcontract.card : ℝ) + Bmovement.card ≤
      ρ * Fintype.card (A.model n) := by
    dsimp [θ] at hcontract hmovement
    linarith
  refine ⟨P, ?_, hexpand⟩
  calc
    (((generatorGraph (A.model n) S (A.map n)).crossingEdges
        P.block).card : ℝ) ≤
        2 * (S.card : ℝ) * (Bcontract.card + Bmovement.card) +
          2 * target * Fintype.card (A.model n) := hcross
    _ ≤ 2 * (S.card : ℝ) *
          (ρ * Fintype.card (A.model n)) +
        2 * target * Fintype.card (A.model n) := by gcongr
    _ = (2 * (S.card : ℝ) * ρ + 2 * target) *
        Fintype.card (A.model n) := by ring

end KunFinitePartition
end NonsoficGroupsExist
