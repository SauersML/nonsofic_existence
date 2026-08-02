import NonsoficGroupsExist.InverseNormalization
import NonsoficGroupsExist.NormalizedVariation
import NonsoficGroupsExist.ComponentPinning

/-!
# Global variation bound

This file assembles the finite variation estimates for every label in the
ambient generator graph.  Embedded `Γ`-generators use almost invariance of
both component partitions, compressors use the one-sided refinement estimate,
and inverse compressors use approximate inverse normalization.
-/

namespace NonsoficGroupsExist

open scoped BigOperators

variable {Y : FiniteModel}

theorem normalizedSize_eq_of_block_eq (P Q : BlockStructure Y) {x y : Y}
    (hP : P.block x = P.block y) (hQ : Q.block x = Q.block y) :
    normalizedSize P Q x = normalizedSize P Q y := by
  classical
  let Bx : BlockIndex Q := ⟨Q.block x, Q.block_mem_blocksFinset x⟩
  let By : BlockIndex Q := ⟨Q.block y, Q.block_mem_blocksFinset y⟩
  have hB : Bx = By := Subtype.ext hQ
  have hsize : P.size x = P.size y := congrArg Finset.card hP
  change medianNormalize (componentMedian P Q Bx : ℝ) (P.size x : ℝ) =
    medianNormalize (componentMedian P Q By : ℝ) (P.size y : ℝ)
  rw [hB, hsize]

/-- The variation of the normalized size along one permutation is supported
on crossings of one of the two component partitions. -/
theorem normalizedVariation_le_crossings (P Q : BlockStructure Y)
    (p : Equiv.Perm Y) :
    (∑ x : Y, |normalizedSize P Q (p x) - normalizedSize P Q x|) ≤
      ((wordCrossing P p).card : ℝ) + (wordCrossing Q p).card := by
  calc
    (∑ x : Y, |normalizedSize P Q (p x) - normalizedSize P Q x|) ≤
        ∑ x : Y, ((if x ∈ wordCrossing P p then (1 : ℝ) else 0) +
          if x ∈ wordCrossing Q p then (1 : ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hP : x ∈ wordCrossing P p
      · have hle : |normalizedSize P Q (p x) - normalizedSize P Q x| ≤ 1 := by
          rw [abs_sub_le_iff]
          constructor <;>
            linarith [normalizedSize_nonneg P Q (p x), normalizedSize_nonneg P Q x,
              (normalizedSize_lt_one P Q (p x)).le,
              (normalizedSize_lt_one P Q x).le]
        simp only [if_pos hP]
        split_ifs <;> linarith
      · by_cases hQ : x ∈ wordCrossing Q p
        · have hle : |normalizedSize P Q (p x) - normalizedSize P Q x| ≤ 1 := by
            rw [abs_sub_le_iff]
            constructor <;>
              linarith [normalizedSize_nonneg P Q (p x), normalizedSize_nonneg P Q x,
                (normalizedSize_lt_one P Q (p x)).le,
                (normalizedSize_lt_one P Q x).le]
          simp [hP, hQ, hle]
        · have hpblock : P.block (p x) = P.block x := by
            simpa [wordCrossing] using hP
          have hqblock : Q.block (p x) = Q.block x := by
            simpa [wordCrossing] using hQ
          rw [normalizedSize_eq_of_block_eq P Q hpblock hqblock]
          simp [hP, hQ]
    _ = ((wordCrossing P p).card : ℝ) + (wordCrossing Q p).card := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_irrel, Finset.filter_mem_eq_inter,
        Finset.inter_eq_right.mpr (Finset.subset_univ (wordCrossing P p)),
        Finset.inter_eq_right.mpr (Finset.subset_univ (wordCrossing Q p))]
      norm_cast

/-- Generator-graph variation is bounded by the sum of the variations of its
labeled permutation arcs.  Removing fixed-point loops changes nothing. -/
theorem generatorGraph_edgeVariation_le {G : Type} [Group G]
    (T : Finset G) (act : G → Equiv.Perm Y) (f : Y → ℝ) :
    (generatorGraph Y T act).edgeVariation f ≤
      ∑ t : T, ∑ x : Y, |f (act t.1 x) - f x| := by
  classical
  letI : Fintype T := Fintype.ofFinset T (fun _ ↦ Iff.rfl)
  let arcs : Finset (T × Y) :=
    Finset.univ.filter fun p ↦ act p.1.1 p.2 ≠ p.2
  change (∑ a : ↑arcs, |f (act a.1.1.1 a.1.2) - f a.1.2|) ≤ _
  calc
    (∑ a : ↑arcs, |f (act a.1.1.1 a.1.2) - f a.1.2|) =
        ∑ a in arcs, |f (act a.1.1 a.2) - f a.2| := by
      simpa using Finset.sum_attach arcs
        (fun a : T × Y ↦ |f (act a.1.1 a.2) - f a.2|)
    _ ≤ ∑ a : T × Y, |f (act a.1.1 a.2) - f a.2| := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ ↦ abs_nonneg _)
    _ = ∑ t : T, ∑ x : Y, |f (act t.1 x) - f x| := by
      rw [Fintype.sum_prod_type]

namespace LocalCriterionData

variable {G Γ J : Type} [Group G] [Group Γ] [Group J]
variable (D : LocalCriterionData G Γ J)

abbrev N (n : ℕ) : ℝ := Fintype.card (D.approximation.model n)

noncomputable abbrev observable (n : ℕ) : D.approximation.model n → ℝ :=
  normalizedSize (D.gammaDecomposition.blocks n) (D.ambientDecomposition.blocks n)

/-- Variation along an embedded `Γ`-generator is negligible. -/
theorem embeddedGeneratorVariation_negligible (t : Γ)
    (ht : t ∈ D.setup.generatorsΓ) :
    Negligible D.N fun n ↦ ∑ x : D.approximation.model n,
      |D.observable n (D.approximation.map n (D.setup.embedΓ t) x) -
        D.observable n x| := by
  have hinner : Negligible D.N fun n ↦
      ((wordCrossing (D.gammaDecomposition.blocks n)
        (D.approximation.map n (D.setup.embedΓ t))).card : ℝ) := by
    simpa [CompressionSetup.gammaApproximation] using
      D.gammaDecomposition.almost_invariant t ht
  have hembed : D.setup.embedΓ t ∈ D.setup.ambientGenerators := by
    classical
    simp [CompressionSetup.ambientGenerators, ht]
  have houter : Negligible D.N fun n ↦
      ((wordCrossing (D.ambientDecomposition.blocks n)
        (D.approximation.map n (D.setup.embedΓ t))).card : ℝ) :=
    D.ambientDecomposition.almost_invariant _ hembed
  have hsum := Negligible.add hinner houter
  refine Vanishing.squeeze (fun n ↦ div_nonneg (by positivity) (by positivity))
    (fun n ↦ ?_) hsum
  apply div_le_div_of_nonneg_right
  · exact normalizedVariation_le_crossings _ _ _
  · positivity

/-- Variation along a compressor is negligible. -/
theorem compressorVariation_negligible (q : G) (hq : q ∈ D.setup.compressors) :
    Negligible D.N fun n ↦ ∑ x : D.approximation.model n,
      |D.observable n (D.approximation.map n q x) - D.observable n x| := by
  have hleak := D.setup.compressorLeakage_negligible D.approximation
    D.gammaDecomposition q hq
  have hall := D.ambientDecomposition.all_almost_invariant
    D.setup.ambientGenerators_symmetric D.setup.ambientGenerators_generate
  have hcross := hall q
  have hbound := Negligible.add (Negligible.const_mul 4 hleak)
    (Negligible.const_mul 2 hcross)
  refine Vanishing.squeeze (fun n ↦ div_nonneg (by positivity) (by positivity))
    (fun n ↦ ?_) hbound
  apply div_le_div_of_nonneg_right
  · exact D.gammaDecomposition.compressorVariation_le
      (D.ambientDecomposition.blocks n) (D.approximation.map n q)
  · positivity

/-- Variation along an inverse compressor is negligible without modifying the
approximation. -/
theorem inverseCompressorVariation_negligible (q : G)
    (hq : q ∈ D.setup.compressors) :
    Negligible D.N fun n ↦ ∑ x : D.approximation.model n,
      |D.observable n (D.approximation.map n q⁻¹ x) - D.observable n x| := by
  have hcompressor := D.compressorVariation_negligible q hq
  have hinverse := D.approximation.inverseError_negligible q
  have hsum := Negligible.add hcompressor hinverse
  refine Vanishing.squeeze (fun n ↦ div_nonneg (by positivity) (by positivity))
    (fun n ↦ ?_) hsum
  apply div_le_div_of_nonneg_right
  · have hv := variation_le_of_disagreement
      (D.approximation.map n q⁻¹) (D.approximation.map n q)⁻¹
      (D.observable n)
      (fun x ↦ normalizedSize_nonneg _ _ x)
      (fun x ↦ (normalizedSize_lt_one _ _ x).le)
      (D.approximation.inverseError n q) (by
        intro x hx
        simpa [SoficApproximation.inverseError] using hx)
    rw [inverse_variation_eq] at hv
    exact hv
  · positivity

/-- Every label of the ambient generator set has negligible variation. -/
theorem ambientGeneratorVariation_negligible (g : G)
    (hg : g ∈ D.setup.ambientGenerators) :
    Negligible D.N fun n ↦ ∑ x : D.approximation.model n,
      |D.observable n (D.approximation.map n g x) - D.observable n x| := by
  classical
  simp only [CompressionSetup.ambientGenerators, Finset.mem_union,
    Finset.mem_image] at hg
  rcases hg with (hg | hg) | hg
  · obtain ⟨t, ht, rfl⟩ := hg
    exact D.embeddedGeneratorVariation_negligible t ht
  · exact D.compressorVariation_negligible g hg
  · obtain ⟨q, hq, rfl⟩ := hg
    exact D.inverseCompressorVariation_negligible q hq

/-- The actual ambient generator graph has negligible total variation. -/
theorem generatorGraphVariation_negligible :
    Negligible D.N fun n ↦
      (generatorGraph (D.approximation.model n) D.setup.ambientGenerators
        (D.approximation.map n)).edgeVariation (D.observable n) := by
  let I : Finset D.setup.ambientGenerators := Finset.univ
  have hsum : Negligible D.N fun n ↦
      ∑ g ∈ I, ∑ x : D.approximation.model n,
        |D.observable n (D.approximation.map n g.1 x) - D.observable n x| := by
    apply Negligible.sum I
    intro g _
    exact D.ambientGeneratorVariation_negligible g.1 g.2
  refine Vanishing.squeeze (fun n ↦ div_nonneg (by positivity) (by positivity))
    (fun n ↦ ?_) hsum
  apply div_le_div_of_nonneg_right
  · simpa [I] using generatorGraph_edgeVariation_le
      D.setup.ambientGenerators (D.approximation.map n) (D.observable n)
  · positivity

/-- Edge editing transfers the variation estimate to the ambient expander
decomposition. -/
theorem modelGraphVariation_negligible :
    Negligible D.N fun n ↦
      (D.ambientDecomposition.modelGraph n).edgeVariation (D.observable n) := by
  have hsum := Negligible.add D.generatorGraphVariation_negligible
    D.ambientDecomposition.unmatched_negligible
  refine Vanishing.squeeze (fun n ↦ div_nonneg (by positivity) (by positivity))
    (fun n ↦ ?_) hsum
  apply div_le_div_of_nonneg_right
  · exact (D.ambientDecomposition.editWitness n).targetVariation_le_unmatchedCount
      (D.observable n) (D.observable n) (fun _ ↦ rfl)
      (fun x ↦ normalizedSize_nonneg _ _ x)
      (fun x ↦ (normalizedSize_lt_one _ _ x).le)
  · positivity

/-- The normalized component-size observable is globally pinned at `1/2`. -/
theorem normalizedDeviation_negligible :
    Negligible D.N fun n ↦ ∑ y : D.approximation.model n,
      |D.observable n y - 1 / 2| :=
  D.ambientDecomposition.normalizedDeviation_negligible_of_global
    D.gammaDecomposition.blocks D.modelGraphVariation_negligible

end LocalCriterionData

end NonsoficGroupsExist
