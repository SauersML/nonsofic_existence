import NonsoficGroupsExist.UniversalCompressionSetup
import NonsoficGroupsExist.UniversalPropertyT
import NonsoficGroupsExist.CriterionAssembly
import NonsoficGroupsExist.SoficTransfer
import NonsoficGroupsExist.UniversalLeavittOver
import NonsoficGroupsExist.FiniteTypeCharacteristicTwoPropertyT
import NonsoficGroupsExist.FiniteCharacteristicTwoLeavitt

/-!
# Unconditional existence theorems

All inputs to the compression criterion are instantiated here by closed
declarations: the universal-Leavitt rank-four compression setup, property `(T)` for its
ambient group and rank-three core, and the explicit non-LEF corner witness.
The finite-table theorem then supplies a finitely presented nonsofic cover.
-/

namespace NonsoficGroupsExist

/-- The elementary group in rank `m + 1` over the universal binary Leavitt
algebra over `k`. -/
noncomputable abbrev BinaryLeavittEL (k : Type) [Field k] (m : ℕ) :=
  elementaryGroup (Fin (m + 1)) (BinaryLeavitt.BinaryLeavittAlgebra k)

/-- Over every finite characteristic-two field, every elementary rank at
least two is finitely generated, infinite, Kazhdan, and nonsofic. -/
theorem binaryLeavitt_charTwo_profile (k : Type) [Field k] [Finite k]
    [CharP k 2] (m : ℕ) (hm : 1 ≤ m) :
    Group.FG (BinaryLeavittEL k m) ∧
      Infinite (BinaryLeavittEL k m) ∧
      HasKazhdanPropertyT.{0, 0} (BinaryLeavittEL k m) ∧
      ¬ IsSofic (BinaryLeavittEL k m) := by
  let L := BinaryLeavitt.family k
  let e : BinaryLeavittEL k m ≃*
      FiniteCharacteristicTwoLeavitt.Ambient k :=
    L.rankSuccEquiv m 3 (by omega) (by omega)
  have hfg : Group.FG (BinaryLeavittEL k m) := by
    letI : Group.FG (FiniteCharacteristicTwoLeavitt.Ambient k) := inferInstance
    exact Group.fg_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hinfinite : Infinite (BinaryLeavittEL k m) :=
    elementaryGroup_infinite
      (R := BinaryLeavitt.BinaryLeavittAlgebra k)
      (0 : Fin (m + 1)) ⟨1, by omega⟩ (by
        intro h
        have hval := congrArg Fin.val h
        norm_num at hval)
  have hT : HasKazhdanPropertyT.{0, 0} (BinaryLeavittEL k m) :=
    L.rankSucc_propertyT_of_rankSucc m 3 (by omega) (by omega)
      (FiniteCharacteristicTwoLeavitt.ambient_hasKazhdanPropertyT k)
  have hnsofic : ¬ IsSofic (BinaryLeavittEL k m) := by
    intro hsofic
    exact FiniteCharacteristicTwoLeavitt.ambient_not_isSofic k
      ((isSofic_mulEquiv_iff e).mp hsofic)
  exact ⟨hfg, hinfinite, hT, hnsofic⟩

/-- The elementary rank-four group over the universal binary Leavitt algebra
`L_{𝔽₂}(1,2)` is nonsofic. -/
theorem universalLeavittEL4_not_isSofic :
    ¬ IsSofic UniversalRankFour.Ambient :=
  not_isSofic_of_not_isLEF UniversalRankFour.compressionSetup
    UniversalRankFour.ambient_hasKazhdanPropertyT
    UniversalRankFour.core_hasKazhdanPropertyT
    UniversalRankFour.witness_not_isLEF

/-- The rank-three core is nonsofic, by the explicit Leavitt
rank-three/rank-four equivalence. -/
theorem universalLeavittEL3_not_isSofic :
    ¬ IsSofic UniversalRankFour.Core := by
  intro h
  exact universalLeavittEL4_not_isSofic
    ((isSofic_mulEquiv_iff UniversalRankFour.family.rankThreeEquivRankFour).mp h)

/-- The full unit group of the universal binary Leavitt algebra. -/
noncomputable abbrev UniversalLeavittUnits :=
  UniversalLeavitt.BinaryLeavittAlgebraˣ

/-- The general linear group of positive rank `m + 1` over the universal
binary Leavitt algebra. -/
noncomputable abbrev UniversalLeavittGL (m : ℕ) :=
  (Matrix (Fin (m + 1)) (Fin (m + 1))
    UniversalLeavitt.BinaryLeavittAlgebra)ˣ

/-- The full unit group of `L_{𝔽₂}(1,2)` is nonsofic.  The complete
four-leaf prefix code identifies it with `GL₄`, which contains the known
nonsofic elementary subgroup. -/
theorem universalLeavittUnits_not_isSofic :
    ¬ IsSofic UniversalLeavittUnits := by
  intro hUnits
  let e : UniversalLeavittGL 3 ≃* UniversalLeavittUnits :=
    UniversalRankFour.family.prefixUnitsEquiv (leftCombCode 3)
      (UniversalRankFour.family.leftCombCode_complete 3)
  have hGL : IsSofic (UniversalLeavittGL 3) :=
    (isSofic_mulEquiv_iff e).mpr hUnits
  exact universalLeavittEL4_not_isSofic
    (isSofic_of_injective
      (elementaryGroup (Fin 4)
        UniversalLeavitt.BinaryLeavittAlgebra).subtype
      Subtype.val_injective hGL)

/-- Every positive-rank general linear group over `L_{𝔽₂}(1,2)` is
nonsofic. -/
theorem universalLeavittGL_not_isSofic (m : ℕ) :
    ¬ IsSofic (UniversalLeavittGL m) := by
  intro hGL
  let e : UniversalLeavittGL m ≃* UniversalLeavittUnits :=
    UniversalRankFour.family.prefixUnitsEquiv (leftCombCode m)
      (UniversalRankFour.family.leftCombCode_complete m)
  exact universalLeavittUnits_not_isSofic
    ((isSofic_mulEquiv_iff e).mp hGL)

/-- The four headline properties of the explicit witness, bundled in the form
most useful to downstream citations. -/
theorem ambient_profile :
    Group.FG UniversalRankFour.Ambient ∧
      Infinite UniversalRankFour.Ambient ∧
      HasKazhdanPropertyT.{0, 0} UniversalRankFour.Ambient ∧
      ¬ IsSofic UniversalRankFour.Ambient := by
  exact ⟨inferInstance, inferInstance,
    UniversalRankFour.ambient_hasKazhdanPropertyT,
    universalLeavittEL4_not_isSofic⟩

/-- The complete five-property profile of the explicit ambient group. -/
theorem ambient_full_profile :
    Countable UniversalRankFour.Ambient ∧
      Group.FG UniversalRankFour.Ambient ∧
      Infinite UniversalRankFour.Ambient ∧
      HasKazhdanPropertyT.{0, 0} UniversalRankFour.Ambient ∧
      ¬ IsSofic UniversalRankFour.Ambient := by
  exact ⟨inferInstance, ambient_profile⟩

/-- The elementary group of rank `m + 1` over the universal binary Leavitt
algebra. -/
noncomputable abbrev UniversalLeavittEL (m : ℕ) :=
  elementaryGroup (Fin (m + 1)) UniversalLeavitt.BinaryLeavittAlgebra

/-- **Theorem A of the manuscript, strengthened to every positive elementary
rank.** For every `m ≥ 1`,
`EL_{m+1}(L_{𝔽₂}(1,2))` is infinite, finitely generated, has property `(T)`,
and is nonsofic. -/
theorem universalLeavitt_theoremA (m : ℕ) (hm : 1 ≤ m) :
    Group.FG (UniversalLeavittEL m) ∧
      Infinite (UniversalLeavittEL m) ∧
      HasKazhdanPropertyT.{0, 0} (UniversalLeavittEL m) ∧
      ¬ IsSofic (UniversalLeavittEL m) := by
  let e : UniversalLeavittEL m ≃* UniversalRankFour.Ambient :=
    UniversalLeavitt.family.rankSuccEquiv m 3 (by omega) (by omega)
  have hfg : Group.FG (UniversalLeavittEL m) := by
    letI : Group.FG UniversalRankFour.Ambient := inferInstance
    exact Group.fg_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hinfinite : Infinite (UniversalLeavittEL m) :=
    elementaryGroup_infinite
      (R := UniversalLeavitt.BinaryLeavittAlgebra)
      (0 : Fin (m + 1)) ⟨1, by omega⟩ (by
        intro h
        have hval := congrArg Fin.val h
        norm_num at hval)
  have hT : HasKazhdanPropertyT.{0, 0} (UniversalLeavittEL m) :=
    UniversalLeavitt.family.rankSucc_propertyT_of_rankSucc
      m 3 (by omega) (by omega) UniversalRankFour.ambient_hasKazhdanPropertyT
  have hnsofic : ¬ IsSofic (UniversalLeavittEL m) := by
    intro hsofic
    exact universalLeavittEL4_not_isSofic
      ((isSofic_mulEquiv_iff e).mp hsofic)
  exact ⟨hfg, hinfinite, hT, hnsofic⟩

/-- Existence of a group which is not sofic. -/
def NonsoficGroupExists : Prop :=
  ∃ (G : Type) (_ : Group G), ¬ IsSofic G

/-- An unconditional, kernel-checked nonsofic-group existence theorem. -/
theorem nonsofic_groups_exist : NonsoficGroupExists := by
  exact ⟨UniversalRankFour.Ambient, inferInstance,
    universalLeavittEL4_not_isSofic⟩

/-- An unconditional, kernel-checked finitely presented nonsofic-group
existence theorem. -/
theorem exists_finitelyPresented_nonsofic_group :
    ∃ (G : Type) (_ : Group G),
      Group.IsFinitelyPresented G ∧ ¬ IsSofic G := by
  exact exists_finitelyPresented_nonsofic_cover
    universalLeavittEL4_not_isSofic

/-- A finitely presented nonsofic group covering the explicit infinite
universal-Leavitt ambient group.  The quotient map is retained, so infinitude
of the cover is part of the checked conclusion. -/
theorem exists_infinite_finitelyPresented_nonsofic_ambient_cover :
    ∃ (H : Type) (_ : Group H),
      Infinite H ∧ Group.IsFinitelyPresented H ∧ ¬ IsSofic H ∧
        ∃ π : H →* UniversalRankFour.Ambient,
          Function.Surjective π := by
  exact exists_infinite_finitelyPresented_nonsofic_cover
    universalLeavittEL4_not_isSofic

end NonsoficGroupsExist
