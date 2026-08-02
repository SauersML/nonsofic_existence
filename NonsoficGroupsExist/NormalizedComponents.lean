import NonsoficGroupsExist.FiniteMedian
import NonsoficGroupsExist.DecompositionRefinement
import NonsoficGroupsExist.MedianNormalization

/-!
# Componentwise median normalization

This file defines the observable used in Section `subsec:median`.  The inner
partition `P` is the Γ-component partition and `Q` is the ambient-component
partition.  On every ambient component we choose the least natural median of
the Γ-component sizes and normalize by `t ↦ t / (t + m)`.
-/

namespace NonsoficGroupsExist

open scoped BigOperators

variable {Y : FiniteModel}

/-- The ambient component indexed by `B`, regarded as a finite model. -/
abbrev indexedBlockModel (Q : BlockStructure Y) (B : BlockIndex Q) : FiniteModel where
  carrier := B.block
  fintype := inferInstance
  decidableEq := inferInstance

/-- Identification of the representative-indexed and block-indexed subtype. -/
noncomputable def representativeBlockEquiv (Q : BlockStructure Y)
    (B : BlockIndex Q) :
    blockModel Q (BlockIndex.representative Q B) ≃ indexedBlockModel Q B where
  toFun x := ⟨x.1, by
    rw [← BlockIndex.block_representative Q B]
    exact x.2⟩
  invFun x := ⟨x.1, by
    rw [BlockIndex.block_representative Q B]
    exact x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The size of the inner component through a vertex of an ambient component. -/
def componentSize (P Q : BlockStructure Y) (B : BlockIndex Q)
    (x : indexedBlockModel Q B) : ℕ :=
  P.size (x : Y)

/-- A vertex-weighted median of the inner-component sizes on `B`. -/
noncomputable def componentMedian (P Q : BlockStructure Y) (B : BlockIndex Q) : ℕ :=
  FiniteMultiGraph.natMedian (componentSize P Q B)

theorem componentMedian_pos (P Q : BlockStructure Y) (B : BlockIndex Q) :
    0 < componentMedian P Q B := by
  classical
  have hmed := FiniteMultiGraph.natMedian_spec (componentSize P Q B)
  change Fintype.card (indexedBlockModel Q B) ≤
    2 * (Finset.univ.filter fun x : indexedBlockModel Q B ↦
      componentSize P Q B x ≤ componentMedian P Q B).card at hmed
  by_cases hm : componentMedian P Q B = 0
  · have hempty :
        (Finset.univ.filter fun x : indexedBlockModel Q B ↦
          componentSize P Q B x ≤ componentMedian P Q B) = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.notMem_empty, iff_false]
      rw [hm]
      exact not_le_of_gt (P.size_pos (x : Y))
    rw [hempty] at hmed
    simp only [Finset.card_empty, mul_zero] at hmed
    have hnonempty : Nonempty (indexedBlockModel Q B) :=
      ⟨⟨BlockIndex.representative Q B, by
        simpa [indexedBlockModel, blockModel] using
          BlockIndex.representative_mem Q B⟩⟩
    have hcard : 0 < Fintype.card (indexedBlockModel Q B) :=
      Fintype.card_pos_iff.mpr hnonempty
    exact ((Nat.not_lt_of_ge hmed) hcard).elim
  · exact Nat.pos_of_ne_zero hm

/-- The normalized Γ-component size on one ambient component. -/
noncomputable def componentNormalized (P Q : BlockStructure Y) (B : BlockIndex Q)
    (x : indexedBlockModel Q B) : ℝ :=
  medianNormalize (componentMedian P Q B : ℝ) (P.size (x : Y) : ℝ)

theorem componentNormalized_nonneg (P Q : BlockStructure Y) (B : BlockIndex Q)
    (x : indexedBlockModel Q B) : 0 ≤ componentNormalized P Q B x := by
  exact medianNormalize_nonneg (by exact_mod_cast componentMedian_pos P Q B)
    (by positivity)

theorem componentNormalized_lt_one (P Q : BlockStructure Y) (B : BlockIndex Q)
    (x : indexedBlockModel Q B) : componentNormalized P Q B x < 1 := by
  exact medianNormalize_lt_one (by exact_mod_cast componentMedian_pos P Q B)
    (by positivity)

/-- The chosen normalization has median exactly `1/2`. -/
theorem componentNormalized_isMedian (P Q : BlockStructure Y) (B : BlockIndex Q) :
    FiniteMultiGraph.IsMedian (componentNormalized P Q B) (1 / 2) := by
  have hnat := FiniteMultiGraph.natMedian_isMedian (componentSize P Q B)
  have hcomp := hnat.comp_increasing (fun _ ↦ by positivity)
    (by positivity : (0 : ℝ) ≤ componentMedian P Q B)
    (medianNormalize (componentMedian P Q B : ℝ))
    (medianNormalize_increasing (by exact_mod_cast componentMedian_pos P Q B))
  have hcenter : medianNormalize (componentMedian P Q B : ℝ)
      (componentMedian P Q B : ℝ) = 1 / 2 := by
    unfold medianNormalize
    have hm : (componentMedian P Q B : ℝ) ≠ 0 := by
      exact_mod_cast (componentMedian_pos P Q B).ne'
    field_simp
    ring
  rw [hcenter] at hcomp
  exact hcomp

/-- The global observable, with the ambient block determining its median. -/
noncomputable def normalizedSize (P Q : BlockStructure Y) (y : Y) : ℝ :=
  let B : BlockIndex Q := ⟨Q.block y, Q.block_mem_blocksFinset y⟩
  medianNormalize (componentMedian P Q B : ℝ) (P.size y : ℝ)

theorem normalizedSize_nonneg (P Q : BlockStructure Y) (y : Y) :
    0 ≤ normalizedSize P Q y := by
  let B : BlockIndex Q := ⟨Q.block y, Q.block_mem_blocksFinset y⟩
  have hm : (0 : ℝ) < componentMedian P Q B := by
    exact_mod_cast componentMedian_pos P Q B
  exact medianNormalize_nonneg hm (by positivity)

theorem normalizedSize_lt_one (P Q : BlockStructure Y) (y : Y) :
    normalizedSize P Q y < 1 := by
  let B : BlockIndex Q := ⟨Q.block y, Q.block_mem_blocksFinset y⟩
  have hm : (0 : ℝ) < componentMedian P Q B := by
    exact_mod_cast componentMedian_pos P Q B
  exact medianNormalize_lt_one hm (by positivity)

/-- The global and componentwise observables agree on the indexed component. -/
theorem normalizedSize_eq_componentNormalized (P Q : BlockStructure Y)
    (B : BlockIndex Q) (x : indexedBlockModel Q B) :
    normalizedSize P Q (x : Y) = componentNormalized P Q B x := by
  classical
  have hx : Q.block (x : Y) = B.block := by
    have hmem : (x : Y) ∈ Q.block (BlockIndex.representative Q B) := by
      simpa only [BlockIndex.block_representative] using x.2
    exact (Q.eq_of_mem _ _ hmem).trans (BlockIndex.block_representative Q B)
  let B' : BlockIndex Q := ⟨Q.block (x : Y), Q.block_mem_blocksFinset (x : Y)⟩
  have hBB : B' = B := Subtype.ext hx
  change medianNormalize (componentMedian P Q B' : ℝ) (P.size (x : Y) : ℝ) =
    medianNormalize (componentMedian P Q B : ℝ) (P.size (x : Y) : ℝ)
  rw [hBB]

/-- On a fixed ambient component the global observable has median `1/2`. -/
theorem normalizedSize_isMedian_on_block (P Q : BlockStructure Y)
    (B : BlockIndex Q) :
    FiniteMultiGraph.IsMedian
      (fun x : indexedBlockModel Q B ↦ normalizedSize P Q (x : Y)) (1 / 2) := by
  simpa only [normalizedSize_eq_componentNormalized] using
    componentNormalized_isMedian P Q B

end NonsoficGroupsExist
