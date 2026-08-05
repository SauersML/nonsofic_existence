import NonsoficGroupsExist.KunFinitePartition
import NonsoficGroupsExist.Selection

/-!
# A full-sequence diagonal family of Kun partitions

The finite partition theorem is eventual for each requested accuracy.  A
slowly increasing diagonal level chooses, on every original finite model, the
finest accuracy that is already available there.  Before the first available
level we use the singleton partition.  Thus no subsequence or reindexing is
needed: the resulting partitions live on the given sofic approximation,
their crossing density tends to zero, and every block retains the same
uniform cut constant.
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

/-- The singleton partition, used only on the finitely many models before the
first quantitative property-`(T)` partition is available. -/
noncomputable def singletonPartition (Y : FiniteModel) : BlockStructure Y where
  block y := {y}
  self_mem y := by simp
  eq_of_mem x y hy := by
    have : y = x := by simpa using hy
    subst y
    rfl

/-- A property-`(T)` partition on every model of the original approximation.
The partitions have negligible generator crossings and retain the same
positive cut constant in every block. -/
theorem exists_partition
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{0, 0} G Q ε)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S) (hεone : ε ≤ 1)
    (A : SoficApproximation G) :
    ∃ P : ∀ n, BlockStructure (A.model n),
      Negligible
        (fun n ↦ (Fintype.card (A.model n) : ℝ))
        (fun n ↦ (((generatorGraph (A.model n) S
          (A.map n)).crossingEdges (P n).block).card : ℝ)) ∧
      ∀ n (y : A.model n) (U : Finset (A.model n)),
        U ⊆ (P n).block y → U.Nonempty →
        2 * U.card ≤ ((P n).block y).card →
        uniformInputCutThreshold S (movementConstant S ε + 1) * U.card ≤
          (generatorGraph (A.model n) S (A.map n)).boundaryCard U := by
  classical
  let Good : ℕ → ℕ → Prop := fun n m ↦
    ∃ P : BlockStructure (A.model n),
        (((generatorGraph (A.model n) S (A.map n)).crossingEdges
            P.block).card : ℝ) ≤
          (2 * (S.card : ℝ) * densityScale m + 2 * densityScale m) *
            Fintype.card (A.model n) ∧
        ∀ y : A.model n, ∀ U : Finset (A.model n),
          U ⊆ P.block y → U.Nonempty →
          2 * U.card ≤ (P.block y).card →
          uniformInputCutThreshold S (movementConstant S ε + 1) * U.card ≤
            (generatorGraph (A.model n) S (A.map n)).boundaryCard U
  have hGood_eventually (m : ℕ) : ∃ N, ∀ n ≥ N, Good n m := by
    simpa only [Good] using
      finiteModel_propertyT_partition_with_density hQ S hQS hone hεone A
        (densityScale m) (densityScale m)
        (densityScale_pos m) (densityScale_pos m)
  let unavailable : ℕ → ℕ → ℝ := fun n m ↦ if Good n m then 0 else 1
  have hunavailable (m : ℕ) : Vanishing fun n ↦ unavailable n m := by
    intro η hη
    obtain ⟨N, hN⟩ := hGood_eventually m
    refine ⟨N, fun n hn ↦ ?_⟩
    simpa [unavailable, hN n hn] using hη
  let level : ℕ → ℕ := diagonalLevel unavailable
  have hlevel : ∀ k, ∃ N, ∀ n ≥ N, k ≤ level n := by
    simpa only [level] using diagonalLevel_diverges unavailable hunavailable
  have hlevelDensity : Vanishing fun n ↦ densityScale (level n) := by
    intro η hη
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hη
    obtain ⟨N, hN⟩ := hlevel k
    refine ⟨N, fun n hn ↦ ?_⟩
    rw [abs_of_pos (densityScale_pos (level n))]
    calc
      densityScale (level n) ≤ 1 / ((k : ℝ) + 1) := by
        unfold densityScale
        apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast Nat.add_le_add_right (hN n hn) 1
      _ < η := by simpa using hk
  have hunavailable_nonneg : ∀ n m, 0 ≤ unavailable n m := by
    intro n m
    simp only [unavailable]
    split <;> norm_num
  have hselectedError : Vanishing fun n ↦ unavailable n (level n) := by
    simpa only [level] using
      diagonalLevel_error unavailable hunavailable_nonneg hunavailable
  obtain ⟨Nselected, hNselected⟩ := hselectedError (1 / 2) (by norm_num)
  have hselected : ∀ n ≥ Nselected, Good n (level n) := by
    intro n hn
    by_contra hbad
    have herr := hNselected n hn
    norm_num [unavailable, hbad] at herr
  let P : ∀ n, BlockStructure (A.model n) := fun n ↦
    if h : Good n (level n) then Classical.choose h
    else singletonPartition (A.model n)
  have P_spec (n : ℕ) (h : Good n (level n)) :
      (((generatorGraph (A.model n) S (A.map n)).crossingEdges
          (P n).block).card : ℝ) ≤
        (2 * (S.card : ℝ) * densityScale (level n) +
          2 * densityScale (level n)) * Fintype.card (A.model n) ∧
      ∀ y : A.model n, ∀ U : Finset (A.model n),
        U ⊆ (P n).block y → U.Nonempty →
        2 * U.card ≤ ((P n).block y).card →
        uniformInputCutThreshold S (movementConstant S ε + 1) * U.card ≤
          (generatorGraph (A.model n) S (A.map n)).boundaryCard U := by
    simpa only [P, dif_pos h] using Classical.choose_spec h
  refine ⟨P, ?_, ?_⟩
  · let C : ℝ := 2 * (S.card : ℝ) + 2
    have hC : 0 ≤ C := by
      dsimp only [C]
      positivity
    have hvanish : Vanishing fun n ↦ C * densityScale (level n) :=
      Vanishing.const_mul C hlevelDensity
    apply Vanishing.squeeze_eventually hvanish Nselected
    intro n hn
    have hnum : (0 : ℝ) ≤
        ((generatorGraph (A.model n) S (A.map n)).crossingEdges
          (P n).block).card := by
      exact_mod_cast Nat.zero_le
        ((generatorGraph (A.model n) S (A.map n)).crossingEdges
          (P n).block).card
    have hden : (0 : ℝ) ≤ Fintype.card (A.model n) := by
      exact_mod_cast Nat.zero_le (Fintype.card (A.model n))
    refine ⟨div_nonneg hnum hden, ?_⟩
    change
      (((generatorGraph (A.model n) S (A.map n)).crossingEdges
          (P n).block).card : ℝ) /
        (Fintype.card (A.model n) : ℝ) ≤ C * densityScale (level n)
    have hspec := (P_spec n (hselected n hn)).1
    by_cases hcardZero :
        Fintype.card (A.model n) = 0
    · have hcardReal :
          (Fintype.card (A.model n) : ℝ) = 0 := by
        exact_mod_cast hcardZero
      rw [hcardReal, div_zero]
      exact mul_nonneg hC (densityScale_pos (level n)).le
    have hcardPos : (0 : ℝ) <
        Fintype.card (A.model n) := by
      exact_mod_cast Nat.pos_of_ne_zero hcardZero
    have hbound :
        (((generatorGraph (A.model n) S (A.map n)).crossingEdges
            (P n).block).card : ℝ) ≤
          (C * densityScale (level n)) * Fintype.card (A.model n) := by
      calc
        (((generatorGraph (A.model n) S (A.map n)).crossingEdges
            (P n).block).card : ℝ) ≤
          (2 * (S.card : ℝ) * densityScale (level n) +
            2 * densityScale (level n)) * Fintype.card (A.model n) := hspec
        _ = (C * densityScale (level n)) * Fintype.card (A.model n) := by
          dsimp only [C]
          ring
    exact (div_le_iff₀ hcardPos).2 hbound
  · intro n y U hU hUne hhalf
    by_cases h : Good n (level n)
    · exact (P_spec n h).2 y U hU hUne hhalf
    · have hcardPos : 0 < U.card := Finset.card_pos.mpr hUne
      have hblock : (P n).block y = {y} := by simp [P, h, singletonPartition]
      rw [hblock] at hhalf
      simp only [Finset.card_singleton] at hhalf
      omega

end KunDiagonalPartition
end NonsoficGroupsExist
