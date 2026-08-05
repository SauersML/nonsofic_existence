import NonsoficGroupsExist.CompressionSetup
import NonsoficGroupsExist.CriterionAssembly
import NonsoficGroupsExist.DiagonalCornerCompression
import NonsoficGroupsExist.FiniteTypeCharacteristicTwoPropertyT
import NonsoficGroupsExist.LeavittRankEquivalence
import NonsoficGroupsExist.RankFourCompressors
import NonsoficGroupsExist.ThompsonWitness
import NonsoficGroupsExist.UniversalLeavittOver

/-!
# The Leavitt compression construction over finite characteristic-two fields

The rank-four algebraic construction is uniform in the coefficient field.
This module instantiates every field of `CompressionSetup`, the two property
`(T)` inputs, and the non-LEF witness for `L_k(1,2)` whenever `k` is finite of
characteristic two.
-/

namespace NonsoficGroupsExist
namespace FiniteCharacteristicTwoLeavitt

noncomputable section

variable (k : Type) [Field k] [Finite k] [CharP k 2]

abbrev CoefficientRing := BinaryLeavitt.BinaryLeavittAlgebra k
abbrev Core := RankFour.Core (CoefficientRing k)
abbrev Ambient := RankFour.Ambient (CoefficientRing k)

def family : LeavittFamily (CoefficientRing k) :=
  BinaryLeavitt.family k

abbrev Witness := (family k).cornerWitnessSubgroup

instance coefficientCharP : CharP (CoefficientRing k) 2 :=
  charP_of_injective_algebraMap (R := k)
    (RingHom.injective (algebraMap k (CoefficientRing k))) 2

private def coreEntries (g : Core k) : List (CoefficientRing k) :=
  let M := (↑(g : (Matrix (Fin 3) (Fin 3) (CoefficientRing k))ˣ) :
    Matrix (Fin 3) (Fin 3) (CoefficientRing k))
  [M 0 0, M 0 1, M 0 2, M 1 0, M 1 1, M 1 2, M 2 0, M 2 1, M 2 2]

private def ambientEntries (g : Ambient k) : List (CoefficientRing k) :=
  let M := (↑(g : (Matrix (Fin 4) (Fin 4) (CoefficientRing k))ˣ) :
    Matrix (Fin 4) (Fin 4) (CoefficientRing k))
  [M 0 0, M 0 1, M 0 2, M 0 3,
   M 1 0, M 1 1, M 1 2, M 1 3,
   M 2 0, M 2 1, M 2 2, M 2 3,
   M 3 0, M 3 1, M 3 2, M 3 3]

instance coreCountable : Countable (Core k) := by
  apply (show Function.Injective (coreEntries k) from ?_).countable
  intro x y h
  simp only [coreEntries, List.cons.injEq] at h
  apply Subtype.ext
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp_all

instance ambientCountable : Countable (Ambient k) := by
  apply (show Function.Injective (ambientEntries k) from ?_).countable
  intro x y h
  simp only [ambientEntries, List.cons.injEq] at h
  apply Subtype.ext
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp_all

instance witnessCountable : Countable (Witness k) := by
  apply (show Function.Injective
      (fun g : Witness k ↦ (↑(g : (CoefficientRing k)ˣ) : CoefficientRing k))
      from ?_).countable
  intro x y h
  apply Subtype.ext
  exact Units.ext h

instance coreFG : Group.FG (Core k) :=
  finiteCharacteristicTwoElementary_finitelyGenerated
    (k := k) (A := CoefficientRing k) 3 (by omega)

instance ambientFG : Group.FG (Ambient k) :=
  finiteCharacteristicTwoElementary_finitelyGenerated
    (k := k) (A := CoefficientRing k) 4 (by omega)

instance witnessFG : Group.FG (Witness k) :=
  (Group.fg_iff').mpr
    ⟨(family k).cornerWitnessGenerators.card,
      (family k).cornerWitnessGenerators, rfl,
      (family k).cornerWitnessGenerators_generate⟩

instance coreInfinite : Infinite (Core k) :=
  elementaryGroup_infinite (R := CoefficientRing k) (0 : Fin 3) 1 (by decide)

instance ambientInfinite : Infinite (Ambient k) :=
  elementaryGroup_infinite (R := CoefficientRing k) (0 : Fin 4) 1 (by decide)

def coreEmbedding : Core k →* Ambient k := RankFour.coreEmbedding

omit [Finite k] [CharP k 2] in
theorem coreEmbedding_injective : Function.Injective (coreEmbedding k) :=
  RankFour.coreEmbedding_injective

def compressionEnd : Core k →* Core k := RankFour.compressionEnd (family k)

omit [Finite k] [CharP k 2] in
theorem compressionEnd_injective : Function.Injective (compressionEnd k) :=
  RankFour.compressionEnd_injective (family k)

def witnessEmbedding : Witness k →* Core k :=
  ((DiagonalElementary.firstDiagonalUnitHom (R := CoefficientRing k)).comp
      (family k).cornerWitnessSubgroup.subtype).codRestrict
    (elementaryGroup (Fin 3) (CoefficientRing k)) (by
      intro j
      exact DiagonalElementary.firstDiagonalUnit_mem_of_mem_commutator
        ((family k).cornerWitnessSubgroup_le_commutator j.property))

omit [Finite k] [CharP k 2] in
theorem witnessEmbedding_injective : Function.Injective (witnessEmbedding k) := by
  intro x y hxy
  apply Subtype.ext
  apply DiagonalElementary.firstDiagonalUnitHom_injective
  exact congrArg (fun z : Core k ↦
    (z : (Matrix (Fin 3) (Fin 3) (CoefficientRing k))ˣ)) hxy

omit [Finite k] [CharP k 2] in
theorem compressionEnd_commutes_witnessEmbedding (g : Core k) (j : Witness k) :
    Commute (compressionEnd k g) (witnessEmbedding k j) := by
  obtain ⟨u, hu⟩ :=
    (family k).cornerWitnessSubgroup_le_cornerSubgroup j.property
  have hj : (j : (CoefficientRing k)ˣ) = (family k).cornerHom u := hu.symm
  apply (commute_iff_eq _ _).2
  apply Subtype.ext
  apply Units.ext
  change
    (family k).matrixCompression
          (↑(g : (Matrix (Fin 3) (Fin 3) (CoefficientRing k))ˣ) :
            Matrix (Fin 3) (Fin 3) (CoefficientRing k)) *
        (↑(DiagonalElementary.firstDiagonalUnitHom
              (j : (CoefficientRing k)ˣ)) :
          Matrix (Fin 3) (Fin 3) (CoefficientRing k)) =
      (↑(DiagonalElementary.firstDiagonalUnitHom
              (j : (CoefficientRing k)ˣ)) :
          Matrix (Fin 3) (Fin 3) (CoefficientRing k)) *
        (family k).matrixCompression
          (↑(g : (Matrix (Fin 3) (Fin 3) (CoefficientRing k))ˣ) :
            Matrix (Fin 3) (Fin 3) (CoefficientRing k))
  rw [hj]
  exact (family k).matrixCompression_commutes_firstDiagonalCorner _ u

omit [Finite k] [CharP k 2] in
theorem compressionEnd_eq_witnessEmbedding_iff (g : Core k) (j : Witness k) :
    compressionEnd k g = witnessEmbedding k j ↔ g = 1 ∧ j = 1 := by
  constructor
  · intro h
    obtain ⟨u, hu⟩ :=
      (family k).cornerWitnessSubgroup_le_cornerSubgroup j.property
    have hj : (j : (CoefficientRing k)ˣ) = (family k).cornerHom u := hu.symm
    have hmatrix := congrArg
      (fun z : Core k ↦
        (↑(z : (Matrix (Fin 3) (Fin 3) (CoefficientRing k))ˣ) :
          Matrix (Fin 3) (Fin 3) (CoefficientRing k))) h
    change
      (family k).matrixCompression
          (↑(g : (Matrix (Fin 3) (Fin 3) (CoefficientRing k))ˣ) :
            Matrix (Fin 3) (Fin 3) (CoefficientRing k)) =
        (↑(DiagonalElementary.firstDiagonalUnitHom
              (j : (CoefficientRing k)ˣ)) :
          Matrix (Fin 3) (Fin 3) (CoefficientRing k)) at hmatrix
    rw [hj] at hmatrix
    obtain ⟨hg, hu⟩ :=
      ((family k).matrixCompression_eq_firstDiagonalCorner_iff _ u).mp hmatrix
    constructor
    · apply Subtype.ext
      apply Units.ext
      exact hg
    · apply Subtype.ext
      change (j : (CoefficientRing k)ˣ) = 1
      rw [hj, hu, map_one]
  · rintro ⟨rfl, rfl⟩
    exact (map_one (compressionEnd k)).trans (map_one (witnessEmbedding k)).symm

def compressors : Finset (Ambient k) := RankFour.compressorSet (family k)

omit [Finite k] in
theorem compressor_conjugation (q : Ambient k) (hq : q ∈ compressors k)
    (g : Core k) :
    coreEmbedding k (compressionEnd k g) =
      q * coreEmbedding k g * q⁻¹ :=
  RankFour.compressorSet_conjugation (family k) q hq g

omit [Finite k] in
theorem core_compressors_generate :
    Subgroup.closure
      (Set.range (coreEmbedding k) ∪ (compressors k : Set (Ambient k))) = ⊤ :=
  RankFour.coreEmbedding_compressorSet_generate (family k)

omit [Finite k] [CharP k 2] in
theorem witness_not_isLEF : ¬ IsLEF (Witness k) :=
  (family k).not_isLEF_cornerWitnessSubgroup

private theorem exists_core_generators :
    ∃ S : Finset (Core k),
      1 ∈ S ∧ (∀ g ∈ S, g⁻¹ ∈ S) ∧ Subgroup.closure (S : Set (Core k)) = ⊤ := by
  classical
  obtain ⟨_, S, _, hS⟩ := Group.fg_iff'.mp (inferInstance : Group.FG (Core k))
  let T : Finset (Core k) := insert 1 (S ∪ S.image fun g ↦ g⁻¹)
  refine ⟨T, Finset.mem_insert_self 1 _, ?_, ?_⟩
  · intro g hg
    simp only [T, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hg ⊢
    rcases hg with h | h | ⟨x, hx, rfl⟩
    · left
      simp [h]
    · exact Or.inr (Or.inr ⟨g, h, rfl⟩)
    · exact Or.inr (Or.inl (by simpa using hx))
  · apply top_unique
    rw [← hS]
    exact Subgroup.closure_mono (by intro g hg; simp [T, hg])

private def coreGenerators : Finset (Core k) :=
  Classical.choose (exists_core_generators k)

def compressionSetup : CompressionSetup (Ambient k) (Core k) (Witness k) := by
  classical
  exact
    { embedΓ := coreEmbedding k
      embedΓ_injective := coreEmbedding_injective k
      embedJ := witnessEmbedding k
      embedJ_injective := witnessEmbedding_injective k
      generatorsΓ := coreGenerators k
      generatorsΓ_one := (Classical.choose_spec (exists_core_generators k)).1
      generatorsΓ_symmetric :=
        (Classical.choose_spec (exists_core_generators k)).2.1
      generatorsΓ_generate :=
        (Classical.choose_spec (exists_core_generators k)).2.2
      generatorsJ := (family k).cornerWitnessGenerators
      generatorsJ_symmetric := (family k).cornerWitnessGenerators_symmetric
      generatorsJ_generate := (family k).cornerWitnessGenerators_generate
      infiniteΓ := inferInstance
      compressors := compressors k
      distinguished := RankFour.compressor (family k)
      distinguished_mem := RankFour.compressor_mem (family k)
      compressedEnd := fun _ _ ↦ compressionEnd k
      compressedEnd_spec := compressor_conjugation k
      generates := core_compressors_generate k
      centralizes := by
        intro g j
        rw [← compressor_conjugation k (RankFour.compressor (family k))
          (RankFour.compressor_mem (family k)) g]
        exact (compressionEnd_commutes_witnessEmbedding k g j).map (coreEmbedding k)
      disjoint := by
        intro g j h
        have h' : coreEmbedding k (compressionEnd k g) =
            coreEmbedding k (witnessEmbedding k j) :=
          (compressor_conjugation k (RankFour.compressor (family k))
            (RankFour.compressor_mem (family k)) g).trans h
        exact (compressionEnd_eq_witnessEmbedding_iff k g j).mp
          (coreEmbedding_injective k h') }

theorem core_hasKazhdanPropertyT : HasKazhdanPropertyT.{0, 0} (Core k) :=
  finiteCharacteristicTwoElementaryThree_hasKazhdanPropertyT
    (k := k) (A := CoefficientRing k)

theorem ambient_hasKazhdanPropertyT : HasKazhdanPropertyT.{0, 0} (Ambient k) :=
  (family k).rankFour_propertyT_of_rankThree (core_hasKazhdanPropertyT k)

/-- `EL₄(L_k(1,2))` is nonsofic for every finite field `k` of
characteristic two. -/
theorem ambient_not_isSofic : ¬ IsSofic (Ambient k) :=
  not_isSofic_of_not_isLEF (compressionSetup k)
    (ambient_hasKazhdanPropertyT k) (core_hasKazhdanPropertyT k)
    (witness_not_isLEF k)

end
end FiniteCharacteristicTwoLeavitt
end NonsoficGroupsExist
