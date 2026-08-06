import NonsoficGroupsExist.Leavitt.UniversalLeavitt
import NonsoficGroupsExist.Leavitt.DiagonalCornerCompression
import NonsoficGroupsExist.Leavitt.RankFourCompressors
import NonsoficGroupsExist.Leavitt.ThompsonWitness
import Mathlib.Algebra.CharP.Algebra

/-!
# The universal binary Leavitt rank-four group

This module specializes the proved rank-four matrix calculations to the
universal binary Leavitt algebra over `ZMod 2`. It constructs the coefficient ring, `EL₃` core,
`EL₄` ambient group, finite-generation instances, infinitude instances, the
two explicit compressor elements, and proves that the core and compressors
generate the ambient group.  It also embeds the explicit non-LEF cylinder
witness into the core and proves the complementary-corner centralizer and
trivial-intersection assertions.  Property `(T)` is not asserted here.
-/

namespace NonsoficGroupsExist
namespace UniversalRankFour

noncomputable abbrev CoefficientRing := UniversalLeavitt.BinaryLeavittAlgebra
noncomputable abbrev Core := RankFour.Core CoefficientRing
noncomputable abbrev Ambient := RankFour.Ambient CoefficientRing

/-- The canonical Leavitt family in the presented universal quotient. -/
noncomputable def family : LeavittFamily CoefficientRing :=
  UniversalLeavitt.family

/-- The explicit two-generated subgroup carrying the finite non-LEF
obstruction. -/
noncomputable abbrev Witness := family.cornerWitnessSubgroup

noncomputable instance : CharP CoefficientRing 2 :=
  charP_of_injective_algebraMap (R := ZMod 2) (A := CoefficientRing) (by
    intro x y h
    fin_cases x <;> fin_cases y
    · rfl
    · have h01 : (0 : CoefficientRing) = 1 := by
        calc
          0 = (algebraMap (ZMod 2) CoefficientRing) 0 := (map_zero _).symm
          _ = (algebraMap (ZMod 2) CoefficientRing) 1 := h
          _ = 1 := map_one _
      exact (zero_ne_one (α := CoefficientRing) h01).elim
    · have h10 : (1 : CoefficientRing) = 0 := by
        calc
          1 = (algebraMap (ZMod 2) CoefficientRing) 1 := (map_one _).symm
          _ = (algebraMap (ZMod 2) CoefficientRing) 0 := h
          _ = 0 := map_zero _
      exact (one_ne_zero (α := CoefficientRing) h10).elim
    · rfl) 2

private noncomputable def coreEntries (g : Core) : List CoefficientRing :=
  let M := (↑(g : (Matrix (Fin 3) (Fin 3) CoefficientRing)ˣ) :
    Matrix (Fin 3) (Fin 3) CoefficientRing)
  [M 0 0, M 0 1, M 0 2, M 1 0, M 1 1, M 1 2, M 2 0, M 2 1, M 2 2]

private noncomputable def ambientEntries (g : Ambient) : List CoefficientRing :=
  let M := (↑(g : (Matrix (Fin 4) (Fin 4) CoefficientRing)ˣ) :
    Matrix (Fin 4) (Fin 4) CoefficientRing)
  [M 0 0, M 0 1, M 0 2, M 0 3,
   M 1 0, M 1 1, M 1 2, M 1 3,
   M 2 0, M 2 1, M 2 2, M 2 3,
   M 3 0, M 3 1, M 3 2, M 3 3]

noncomputable instance : Countable Core := by
  apply (show Function.Injective coreEntries from ?_).countable
  intro x y h
  simp only [coreEntries, List.cons.injEq] at h
  apply Subtype.ext
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp_all

noncomputable instance : Countable Ambient := by
  apply (show Function.Injective ambientEntries from ?_).countable
  intro x y h
  simp only [ambientEntries, List.cons.injEq] at h
  apply Subtype.ext
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp_all

noncomputable instance : Countable Witness := by
  apply (show Function.Injective
      (fun g : Witness ↦ (↑(g : CoefficientRingˣ) : CoefficientRing)) from ?_).countable
  intro x y h
  apply Subtype.ext
  exact Units.ext h

noncomputable instance : Group.FG Core :=
  elementaryGroup_finitelyGenerated 3 (by omega)

noncomputable instance : Group.FG Ambient :=
  elementaryGroup_finitelyGenerated 4 (by omega)

noncomputable instance : Group.FG Witness :=
  (Group.fg_iff').mpr
    ⟨family.cornerWitnessGenerators.card, family.cornerWitnessGenerators, rfl,
      family.cornerWitnessGenerators_generate⟩

noncomputable instance : Infinite Core :=
  elementaryGroup_infinite (R := CoefficientRing) (0 : Fin 3) 1 (by decide)

noncomputable instance : Infinite Ambient :=
  elementaryGroup_infinite (R := CoefficientRing) (0 : Fin 4) 1 (by decide)

/-- The embedded rank-three core. -/
noncomputable def coreEmbedding : Core →* Ambient :=
  RankFour.coreEmbedding

theorem coreEmbedding_injective : Function.Injective coreEmbedding :=
  RankFour.coreEmbedding_injective

/-- The injective coefficient-compression endomorphism. -/
noncomputable def compressionEnd : Core →* Core :=
  RankFour.compressionEnd family

theorem compressionEnd_injective : Function.Injective compressionEnd :=
  RankFour.compressionEnd_injective family

/-- Embed the non-LEF corner witness diagonally into `EL₃`.  Membership in
the elementary group is supplied by the explicit cylinder-commutator and
Whitehead calculations, rather than by an assumed perfectness theorem. -/
noncomputable def witnessEmbedding : Witness →* Core :=
  ((DiagonalElementary.firstDiagonalUnitHom (R := CoefficientRing)).comp
      family.cornerWitnessSubgroup.subtype).codRestrict
    (elementaryGroup (Fin 3) CoefficientRing) (by
      intro j
      exact DiagonalElementary.firstDiagonalUnit_mem_of_mem_commutator
        (family.cornerWitnessSubgroup_le_commutator j.property))

theorem witnessEmbedding_injective : Function.Injective witnessEmbedding := by
  intro x y hxy
  apply Subtype.ext
  apply DiagonalElementary.firstDiagonalUnitHom_injective
  exact congrArg (fun z : Core ↦
    (z : (Matrix (Fin 3) (Fin 3) CoefficientRing)ˣ)) hxy

@[simp] theorem compressionEnd_val (g : Core) :
    (compressionEnd g : (Matrix (Fin 3) (Fin 3) CoefficientRing)ˣ) =
      family.matrixCompressionHom
        (g : (Matrix (Fin 3) (Fin 3) CoefficientRing)ˣ) := rfl

@[simp] theorem witnessEmbedding_val (j : Witness) :
    (witnessEmbedding j : (Matrix (Fin 3) (Fin 3) CoefficientRing)ˣ) =
      DiagonalElementary.firstDiagonalUnitHom
        (j : CoefficientRingˣ) := rfl

/-- The compressed core commutes with the explicitly embedded corner
witness. -/
theorem compressionEnd_commutes_witnessEmbedding (g : Core) (j : Witness) :
    Commute (compressionEnd g) (witnessEmbedding j) := by
  obtain ⟨u, hu⟩ := family.cornerWitnessSubgroup_le_cornerSubgroup j.property
  have hj : (j : CoefficientRingˣ) = family.cornerHom u := hu.symm
  apply (commute_iff_eq _ _).2
  apply Subtype.ext
  apply Units.ext
  change
    family.matrixCompression
          (↑(g : (Matrix (Fin 3) (Fin 3) CoefficientRing)ˣ) :
            Matrix (Fin 3) (Fin 3) CoefficientRing) *
        (↑(DiagonalElementary.firstDiagonalUnitHom
              (j : CoefficientRingˣ)) : Matrix (Fin 3) (Fin 3) CoefficientRing) =
      (↑(DiagonalElementary.firstDiagonalUnitHom
              (j : CoefficientRingˣ)) : Matrix (Fin 3) (Fin 3) CoefficientRing) *
        family.matrixCompression
          (↑(g : (Matrix (Fin 3) (Fin 3) CoefficientRing)ˣ) :
            Matrix (Fin 3) (Fin 3) CoefficientRing)
  rw [hj]
  exact family.matrixCompression_commutes_firstDiagonalCorner _ u

/-- The compressed core and the embedded corner witness have trivial
intersection. -/
theorem compressionEnd_eq_witnessEmbedding_iff (g : Core) (j : Witness) :
    compressionEnd g = witnessEmbedding j ↔ g = 1 ∧ j = 1 := by
  constructor
  · intro h
    obtain ⟨u, hu⟩ := family.cornerWitnessSubgroup_le_cornerSubgroup j.property
    have hj : (j : CoefficientRingˣ) = family.cornerHom u := hu.symm
    have hmatrix := congrArg
      (fun z : Core ↦
        (↑(z : (Matrix (Fin 3) (Fin 3) CoefficientRing)ˣ) :
          Matrix (Fin 3) (Fin 3) CoefficientRing)) h
    change
      family.matrixCompression
          (↑(g : (Matrix (Fin 3) (Fin 3) CoefficientRing)ˣ) :
            Matrix (Fin 3) (Fin 3) CoefficientRing) =
        (↑(DiagonalElementary.firstDiagonalUnitHom
              (j : CoefficientRingˣ)) : Matrix (Fin 3) (Fin 3) CoefficientRing)
      at hmatrix
    rw [hj] at hmatrix
    obtain ⟨hg, hu⟩ :=
      (family.matrixCompression_eq_firstDiagonalCorner_iff _ u).mp hmatrix
    constructor
    · apply Subtype.ext
      apply Units.ext
      exact hg
    · apply Subtype.ext
      change (j : CoefficientRingˣ) = 1
      rw [hj, hu, map_one]
  · rintro ⟨rfl, rfl⟩
    simp

/-- The two explicit ambient compressor words. -/
noncomputable def compressors : Finset Ambient :=
  RankFour.compressorSet family

/-- Every compressor implements `compressionEnd` by conjugation. -/
theorem compressor_conjugation (q : Ambient) (hq : q ∈ compressors) (g : Core) :
    coreEmbedding (compressionEnd g) = q * coreEmbedding g * q⁻¹ := by
  exact RankFour.compressorSet_conjugation family q hq g

/-- The core and compressor set generate the ambient group. -/
theorem core_compressors_generate :
    Subgroup.closure (Set.range coreEmbedding ∪ (compressors : Set Ambient)) = ⊤ := by
  exact RankFour.coreEmbedding_compressorSet_generate family

/-- The specialized witness is genuinely non-LEF. -/
theorem witness_not_isLEF : ¬ IsLEF Witness :=
  family.not_isLEF_cornerWitnessSubgroup

end UniversalRankFour
end NonsoficGroupsExist
