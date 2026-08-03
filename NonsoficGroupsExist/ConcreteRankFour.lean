import NonsoficGroupsExist.ConcreteLeavitt
import NonsoficGroupsExist.RankFourCompressors
import NonsoficGroupsExist.ThompsonWitness
import Mathlib.Algebra.CharP.Algebra

/-!
# The concrete rank-four candidate group

This module specializes the proved rank-four matrix calculations to the
stream-operator algebra.  It constructs the coefficient ring, `EL₃` core,
`EL₄` ambient group, finite-generation instances, infinitude instances, and
the two concrete compressor elements.  It does not assert property `(T)`,
ambient generation by the core and compressors, or the existence of a
non-LEF subgroup embedded in the core.
-/

namespace NonsoficGroupsExist
namespace ConcreteRankFour

noncomputable abbrev CoefficientRing := ConcreteLeavitt.StreamOperatorAlgebra
noncomputable abbrev Core := RankFour.Core CoefficientRing
noncomputable abbrev Ambient := RankFour.Ambient CoefficientRing

/-- The kernel-checked Leavitt family of stream operators. -/
noncomputable def family : LeavittFamily CoefficientRing :=
  ConcreteLeavitt.family

/-- The concrete two-generated subgroup carrying the finite non-LEF
obstruction.  No embedding of this group into `Core` is claimed. -/
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

/-- The concrete embedded core. -/
noncomputable def coreEmbedding : Core →* Ambient :=
  RankFour.coreEmbedding

theorem coreEmbedding_injective : Function.Injective coreEmbedding :=
  RankFour.coreEmbedding_injective

/-- The concrete injective coefficient-compression endomorphism. -/
noncomputable def compressionEnd : Core →* Core :=
  RankFour.compressionEnd family

theorem compressionEnd_injective : Function.Injective compressionEnd :=
  RankFour.compressionEnd_injective family

/-- The two explicit ambient compressor words. -/
noncomputable def compressors : Finset Ambient :=
  RankFour.compressorSet family

/-- Every concrete compressor implements `compressionEnd` by conjugation. -/
theorem compressor_conjugation (q : Ambient) (hq : q ∈ compressors) (g : Core) :
    coreEmbedding (compressionEnd g) = q * coreEmbedding g * q⁻¹ := by
  exact RankFour.compressorSet_conjugation family q hq g

/-- The specialized witness is genuinely non-LEF. -/
theorem witness_not_isLEF : ¬ IsLEF Witness :=
  family.not_isLEF_cornerWitnessSubgroup

end ConcreteRankFour
end NonsoficGroupsExist
