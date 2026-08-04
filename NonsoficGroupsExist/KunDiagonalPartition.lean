import NonsoficGroupsExist.KunFinitePartition

/-!
# A diagonal sequence of Kun partitions

The finite partition theorem is eventual for each requested accuracy.  We
choose the accuracy `1/(n+1)` and reindex beyond its finite threshold.  The
result is one sofic approximation carrying partitions whose crossing density
actually tends to zero while retaining a uniform block cut constant.
-/

namespace NonsoficGroupsExist
namespace KunDiagonalPartition

open KunFinitePartition
open KunUniformMovement
open KunUniformRounding

variable {G : Type} [Group G]

/-- The accuracy used at diagonal stage `n`. -/
noncomputable def densityScale (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem densityScale_pos (n : ℕ) : 0 < densityScale n := by
  unfold densityScale
  positivity

theorem densityScale_vanishing : Vanishing densityScale := by
  intro η hη
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hη
  refine ⟨k, fun n hn ↦ ?_⟩
  rw [abs_of_pos (densityScale_pos n)]
  calc
    densityScale n ≤ 1 / ((k : ℝ) + 1) := by
      unfold densityScale
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.add_le_add_right hn 1
    _ < η := by simpa using hk

/-- A property-(T) finite-model partition sequence after a cofinal reindexing.
The partitions have negligible generator crossings and retain the same
positive cut constant in every block. -/
theorem exists_reindexed_partition
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{0, 0} G Q ε)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S) (hεone : ε ≤ 1)
    (A : SoficApproximation G) :
    ∃ (φ : ℕ → ℕ) (hφ : ∀ n, n ≤ φ n)
      (P : ∀ n, BlockStructure ((A.reindex φ hφ).model n)),
      Negligible
        (fun n ↦ (Fintype.card ((A.reindex φ hφ).model n) : ℝ))
        (fun n ↦ (((generatorGraph ((A.reindex φ hφ).model n) S
          ((A.reindex φ hφ).map n)).crossingEdges (P n).block).card : ℝ)) ∧
      ∀ n (y : (A.reindex φ hφ).model n)
        (U : Finset ((A.reindex φ hφ).model n)),
        U ⊆ (P n).block y → U.Nonempty →
        2 * U.card ≤ ((P n).block y).card →
        uniformInputCutThreshold S (movementConstant S ε + 1) * U.card ≤
          (generatorGraph ((A.reindex φ hφ).model n) S
            ((A.reindex φ hφ).map n)).boundaryCard U := by
  classical
  have hstage (m : ℕ) :=
    finiteModel_propertyT_partition_with_density hQ S hQS hone hεone A
      (densityScale m) (densityScale m)
      (densityScale_pos m) (densityScale_pos m)
  let threshold : ℕ → ℕ := fun m ↦ Classical.choose (hstage m)
  have threshold_spec (m : ℕ) : ∀ n ≥ threshold m,
      ∃ P : BlockStructure (A.model n),
        (((generatorGraph (A.model n) S (A.map n)).crossingEdges
            P.block).card : ℝ) ≤
          (2 * (S.card : ℝ) * densityScale m + 2 * densityScale m) *
            Fintype.card (A.model n) ∧
        ∀ y : A.model n, ∀ U : Finset (A.model n),
          U ⊆ P.block y → U.Nonempty →
          2 * U.card ≤ (P.block y).card →
          uniformInputCutThreshold S (movementConstant S ε + 1) * U.card ≤
            (generatorGraph (A.model n) S (A.map n)).boundaryCard U :=
    Classical.choose_spec (hstage m)
  let φ : ℕ → ℕ := fun m ↦ max m (threshold m)
  have hφ : ∀ m, m ≤ φ m := fun m ↦ le_max_left _ _
  have hchosen (m : ℕ) :
      ∃ P : BlockStructure (A.model (φ m)),
        (((generatorGraph (A.model (φ m)) S (A.map (φ m))).crossingEdges
            P.block).card : ℝ) ≤
          (2 * (S.card : ℝ) * densityScale m + 2 * densityScale m) *
            Fintype.card (A.model (φ m)) ∧
        ∀ y : A.model (φ m), ∀ U : Finset (A.model (φ m)),
          U ⊆ P.block y → U.Nonempty →
          2 * U.card ≤ (P.block y).card →
          uniformInputCutThreshold S (movementConstant S ε + 1) * U.card ≤
            (generatorGraph (A.model (φ m)) S (A.map (φ m))).boundaryCard U :=
    threshold_spec m (φ m) (le_max_right _ _)
  let P : ∀ m, BlockStructure ((A.reindex φ hφ).model m) :=
    fun m ↦ Classical.choose (hchosen m)
  have P_spec (m : ℕ) := Classical.choose_spec (hchosen m)
  refine ⟨φ, hφ, P, ?_, ?_⟩
  · let C : ℝ := 2 * (S.card : ℝ) + 2
    have hvanish : Vanishing fun n ↦ C * densityScale n :=
      Vanishing.const_mul C densityScale_vanishing
    apply Vanishing.squeeze
      (fun n ↦ div_nonneg (by positivity) (by positivity)) _ hvanish
    intro n
    by_cases hcardZero :
        Fintype.card ((A.reindex φ hφ).model n) = 0
    · have hcardReal :
          (Fintype.card ((A.reindex φ hφ).model n) : ℝ) = 0 := by
        exact_mod_cast hcardZero
      rw [hcardReal, div_zero]
      exact mul_nonneg (by dsimp [C]; positivity) (densityScale_pos n).le
    have hcardPos : (0 : ℝ) <
        Fintype.card ((A.reindex φ hφ).model n) := by
      exact_mod_cast Nat.pos_of_ne_zero hcardZero
    apply (div_le_iff₀ hcardPos).2
    calc
      (((generatorGraph ((A.reindex φ hφ).model n) S
          ((A.reindex φ hφ).map n)).crossingEdges
          (P n).block).card : ℝ) ≤
        (2 * (S.card : ℝ) * densityScale n + 2 * densityScale n) *
          Fintype.card ((A.reindex φ hφ).model n) := (P_spec n).1
      _ = (C * densityScale n) *
          Fintype.card ((A.reindex φ hφ).model n) := by
        dsimp [C]
        ring
  · intro n y U hU hUne hhalf
    exact (P_spec n).2 y U hU hUne hhalf

end KunDiagonalPartition
end NonsoficGroupsExist
