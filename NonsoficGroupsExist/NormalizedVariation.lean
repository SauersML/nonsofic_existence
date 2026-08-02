import NonsoficGroupsExist.ComponentPinning
import NonsoficGroupsExist.CompressionRefinement
import NonsoficGroupsExist.PermutationConservation
import NonsoficGroupsExist.EdgeEditing

/-!
# Variation of the median-normalized component size

The compressor refinement gives a one-sided containment estimate.  Because
the compressor acts by a permutation, conservation turns that estimate into
an absolute-variation estimate.  Ordinary Γ-generator arcs vary only on
crossings of the Γ- or ambient-component partitions.  These are the finite
inequalities used before the co-area pinning lemma.
-/

namespace NonsoficGroupsExist
namespace ExpanderDecomposition

open scoped BigOperators

variable {G : Type} [Group G] {S : SoficApproximation G} {T : Finset G}

/-- Points of one source component which miss its refined Γ-target. -/
noncomputable def blockLeakageVertices (D : ExpanderDecomposition S T)
    (q : Equiv.Perm (S.model n)) (B : D.componentIndex n) :
    Finset (indexedBlockModel (D.blocks n) B) :=
  Finset.univ.filter fun x ↦
    q (x : S.model n) ∉ (D.refineBlock (D.blocks n) q B).target

theorem card_blockLeakageVertices (D : ExpanderDecomposition S T)
    (q : Equiv.Perm (S.model n)) (B : D.componentIndex n) :
    (D.blockLeakageVertices q B).card =
      D.componentLeakage (D.blocks n) q B := by
  classical
  unfold blockLeakageVertices componentLeakage
  apply Finset.card_bij
    (s := Finset.univ.filter fun x : indexedBlockModel (D.blocks n) B ↦
      q (x : S.model n) ∉ (D.refineBlock (D.blocks n) q B).target)
    (t := B.block.image q \ (D.refineBlock (D.blocks n) q B).target)
    (fun x _ ↦ q (x : S.model n))
  · intro x hx
    rw [Finset.mem_filter] at hx
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_image.mpr ⟨x, x.2, rfl⟩, hx.2⟩
  · intro x _ y _ hxy
    exact Subtype.ext (q.injective hxy)
  · intro y hy
    obtain ⟨hyimage, hytarget⟩ := Finset.mem_sdiff.mp hy
    obtain ⟨x, hxB, rfl⟩ := Finset.mem_image.mp hyimage
    exact ⟨⟨x, hxB⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hytarget⟩, rfl⟩

/-- The non-leaking image has cardinality at most that of the selected target. -/
theorem remaining_le_refinedTarget (D : ExpanderDecomposition S T)
    (q : Equiv.Perm (S.model n)) (B : D.componentIndex n) :
    B.block.card - D.componentLeakage (D.blocks n) q B ≤
      (D.refineBlock (D.blocks n) q B).target.card := by
  classical
  let U := B.block.image q
  let V := (D.refineBlock (D.blocks n) q B).target
  have himage : U.card = B.block.card := by
    simp [U, Finset.card_image_of_injective _ q.injective]
  have hsplit := Finset.card_sdiff_add_card_inter U V
  have hinter : (U ∩ V).card ≤ V.card := Finset.card_le_card Finset.inter_subset_right
  change B.block.card - (U \ V).card ≤ V.card
  omega

/-- A point which neither leaks nor changes ambient component satisfies the
one-sided normalized-size estimate for its whole source component. -/
theorem normalized_drop_le_block_ratio (D : ExpanderDecomposition S T)
    (Q : BlockStructure (S.model n)) (q : Equiv.Perm (S.model n))
    (B : D.componentIndex n) (x : indexedBlockModel (D.blocks n) B)
    (hleak : q (x : S.model n) ∈
      (D.refineBlock (D.blocks n) q B).target)
    (hamb : Q.block (q (x : S.model n)) = Q.block (x : S.model n)) :
    normalizedSize (D.blocks n) Q (x : S.model n) -
        normalizedSize (D.blocks n) Q (q (x : S.model n)) ≤
      (D.componentLeakage (D.blocks n) q B : ℝ) / B.block.card := by
  classical
  obtain ⟨z, hz⟩ := (D.refineBlock (D.blocks n) q B).target_isBlock
  have htarget : (D.blocks n).block (q (x : S.model n)) =
      (D.refineBlock (D.blocks n) q B).target := by
    rw [hz]
    exact (D.blocks n).eq_of_mem z _ (by simpa [hz] using hleak)
  let A : BlockIndex Q :=
    ⟨Q.block (x : S.model n), Q.block_mem_blocksFinset (x : S.model n)⟩
  let A' : BlockIndex Q :=
    ⟨Q.block (q (x : S.model n)), Q.block_mem_blocksFinset (q (x : S.model n))⟩
  have hAA : A' = A := Subtype.ext hamb
  have hxsize : (D.blocks n).size (x : S.model n) = B.block.card := by
    change ((D.blocks n).block (x : S.model n)).card = B.block.card
    have hmem : (x : S.model n) ∈
        (D.blocks n).block (BlockIndex.representative (D.blocks n) B) := by
      simpa only [BlockIndex.block_representative] using x.2
    exact congrArg Finset.card
      (((D.blocks n).eq_of_mem _ _ hmem).trans
        (BlockIndex.block_representative (D.blocks n) B))
  have hqsize : (D.blocks n).size (q (x : S.model n)) =
      (D.refineBlock (D.blocks n) q B).target.card := congrArg Finset.card htarget
  have hleakNat := D.remaining_le_refinedTarget q B
  have hleakCard : D.componentLeakage (D.blocks n) q B ≤ B.block.card := by
    unfold componentLeakage
    exact (Finset.card_le_card Finset.sdiff_subset).trans_eq
      (Finset.card_image_of_injective B.block q.injective)
  have hleakReal : (B.block.card : ℝ) -
      D.componentLeakage (D.blocks n) q B ≤
      ((D.refineBlock (D.blocks n) q B).target.card : ℝ) := by
    rw [← Nat.cast_sub hleakCard]
    exact_mod_cast hleakNat
  change medianNormalize (componentMedian (D.blocks n) Q A : ℝ)
      ((D.blocks n).size (x : S.model n) : ℝ) -
    medianNormalize (componentMedian (D.blocks n) Q A' : ℝ)
      ((D.blocks n).size (q (x : S.model n)) : ℝ) ≤ _
  rw [hAA, hxsize, hqsize]
  apply onesided_drop
  · exact_mod_cast componentMedian_pos (D.blocks n) Q A
  · exact_mod_cast (BlockIndex.block_nonempty (D.blocks n) B).card_pos
  · positivity
  · positivity
  · exact hleakReal

/-- One source component contributes at most twice its leakage plus its
ambient-crossing vertices to the total one-sided drop. -/
theorem block_positiveDrop_le (D : ExpanderDecomposition S T)
    (Q : BlockStructure (S.model n)) (q : Equiv.Perm (S.model n))
    (B : D.componentIndex n) :
    (∑ x : indexedBlockModel (D.blocks n) B,
      max (normalizedSize (D.blocks n) Q (x : S.model n) -
        normalizedSize (D.blocks n) Q (q (x : S.model n))) 0) ≤
      2 * (D.componentLeakage (D.blocks n) q B : ℝ) +
        ((Finset.univ.filter fun x : indexedBlockModel (D.blocks n) B ↦
          Q.block (q (x : S.model n)) ≠ Q.block (x : S.model n)).card : ℝ) := by
  classical
  let e : ℝ := D.componentLeakage (D.blocks n) q B
  let c : ℝ := B.block.card
  have hc : 0 < c := by
    change (0 : ℝ) < B.block.card
    exact_mod_cast (BlockIndex.block_nonempty (D.blocks n) B).card_pos
  calc
    (∑ x : indexedBlockModel (D.blocks n) B,
      max (normalizedSize (D.blocks n) Q (x : S.model n) -
        normalizedSize (D.blocks n) Q (q (x : S.model n))) 0) ≤
      ∑ x : indexedBlockModel (D.blocks n) B,
        (e / c + (if x ∈ D.blockLeakageVertices q B then 1 else 0) +
          if Q.block (q (x : S.model n)) ≠ Q.block (x : S.model n) then 1 else 0) := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hxleak : x ∈ D.blockLeakageVertices q B
      · have hdrop : normalizedSize (D.blocks n) Q (x : S.model n) -
            normalizedSize (D.blocks n) Q (q (x : S.model n)) < 1 := by
          linarith [normalizedSize_lt_one (D.blocks n) Q (x : S.model n),
            normalizedSize_nonneg (D.blocks n) Q (q (x : S.model n))]
        have hmax : max (normalizedSize (D.blocks n) Q (x : S.model n) -
            normalizedSize (D.blocks n) Q (q (x : S.model n))) 0 ≤ 1 :=
          max_le (le_of_lt hdrop) zero_le_one
        calc
          _ ≤ 1 := hmax
          _ ≤ e / c + (if x ∈ D.blockLeakageVertices q B then 1 else 0) +
              (if Q.block (q (x : S.model n)) ≠ Q.block (x : S.model n) then
                1 else 0) := by
                  have he : 0 ≤ e / c := div_nonneg (by positivity) hc.le
                  simp only [if_pos hxleak]
                  split_ifs <;> linarith
      · have hxmem : q (x : S.model n) ∈
            (D.refineBlock (D.blocks n) q B).target := by
          simpa [blockLeakageVertices] using hxleak
        by_cases hamb : Q.block (q (x : S.model n)) ≠ Q.block (x : S.model n)
        · have hdrop : normalizedSize (D.blocks n) Q (x : S.model n) -
              normalizedSize (D.blocks n) Q (q (x : S.model n)) < 1 := by
            linarith [normalizedSize_lt_one (D.blocks n) Q (x : S.model n),
              normalizedSize_nonneg (D.blocks n) Q (q (x : S.model n))]
          have hmax : max (normalizedSize (D.blocks n) Q (x : S.model n) -
              normalizedSize (D.blocks n) Q (q (x : S.model n))) 0 ≤ 1 :=
            max_le (le_of_lt hdrop) zero_le_one
          calc
            _ ≤ 1 := hmax
            _ ≤ e / c + (if x ∈ D.blockLeakageVertices q B then 1 else 0) +
                (if Q.block (q (x : S.model n)) ≠ Q.block (x : S.model n) then
                  1 else 0) := by
                    simp only [if_neg hxleak, if_pos hamb, add_zero]
                    have he : 0 ≤ e / c := div_nonneg (by positivity) hc.le
                    linarith
        · have hgood := max_le
            (D.normalized_drop_le_block_ratio Q q B x hxmem (not_ne_iff.mp hamb))
            (by positivity)
          simpa only [if_neg hxleak, if_neg hamb, add_zero] using hgood
    _ = 2 * (D.componentLeakage (D.blocks n) q B : ℝ) +
        ((Finset.univ.filter fun x : indexedBlockModel (D.blocks n) B ↦
          Q.block (q (x : S.model n)) ≠ Q.block (x : S.model n)).card : ℝ) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      have hcard : Fintype.card (indexedBlockModel (D.blocks n) B) = B.block.card := by
        simp [indexedBlockModel]
      have hbase : ∑ _x : indexedBlockModel (D.blocks n) B, e / c = e := by
        rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
        change c * (e / c) = e
        field_simp
      have hleaksum :
          (∑ x : indexedBlockModel (D.blocks n) B,
            if x ∈ D.blockLeakageVertices q B then (1 : ℝ) else 0) =
              (D.blockLeakageVertices q B).card := by
                simp only [Finset.sum_boole]
                norm_cast
                rw [Finset.filter_mem_eq_inter,
                  Finset.inter_eq_right.mpr (Finset.subset_univ _)]
      have hambsum :
          (∑ x : indexedBlockModel (D.blocks n) B,
            if Q.block (q (x : S.model n)) ≠ Q.block (x : S.model n) then
              (1 : ℝ) else 0) =
            (Finset.univ.filter fun x : indexedBlockModel (D.blocks n) B ↦
              Q.block (q (x : S.model n)) ≠ Q.block (x : S.model n)).card := by
                simp only [Finset.sum_boole]
      rw [hbase, hleaksum, hambsum, D.card_blockLeakageVertices q B]
      simp only [e]
      ring

/-- Summed one-sided drop along a compressor. -/
theorem positiveDrop_le (D : ExpanderDecomposition S T)
    (Q : BlockStructure (S.model n)) (q : Equiv.Perm (S.model n)) :
    (∑ x : S.model n,
      max (normalizedSize (D.blocks n) Q x - normalizedSize (D.blocks n) Q (q x)) 0) ≤
      2 * ∑ B : D.componentIndex n,
          (D.componentLeakage (D.blocks n) q B : ℝ) +
        ((wordCrossing Q q).card : ℝ) := by
  rw [← BlockIndex.sum_sum (D.blocks n) (fun x ↦
    max (normalizedSize (D.blocks n) Q x - normalizedSize (D.blocks n) Q (q x)) 0)]
  have hsum := Finset.sum_le_sum fun B (_ : B ∈ (Finset.univ : Finset _)) ↦
    D.block_positiveDrop_le Q q B
  calc
    _ ≤ ∑ B : D.componentIndex n,
        (2 * (D.componentLeakage (D.blocks n) q B : ℝ) +
          ((Finset.univ.filter fun x : indexedBlockModel (D.blocks n) B ↦
            Q.block (q (x : S.model n)) ≠ Q.block (x : S.model n)).card : ℝ)) := hsum
    _ = 2 * ∑ B : D.componentIndex n,
          (D.componentLeakage (D.blocks n) q B : ℝ) +
        ((wordCrossing Q q).card : ℝ) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      exact (BlockIndex.sum_card_filter (D.blocks n)
        (fun x ↦ Q.block (q x) ≠ Q.block x)).trans (by simp [wordCrossing])

/-- Conservation upgrades one-sided containment to absolute variation. -/
theorem compressorVariation_le (D : ExpanderDecomposition S T)
    (Q : BlockStructure (S.model n)) (q : Equiv.Perm (S.model n)) :
    ∑ x : S.model n,
      |normalizedSize (D.blocks n) Q (q x) - normalizedSize (D.blocks n) Q x| ≤
      4 * ∑ B : D.componentIndex n,
          (D.componentLeakage (D.blocks n) q B : ℝ) +
        2 * ((wordCrossing Q q).card : ℝ) := by
  rw [permutation_conservation_abs]
  linarith [D.positiveDrop_le Q q]

end ExpanderDecomposition
end NonsoficGroupsExist
