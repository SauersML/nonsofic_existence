import NonsoficGroupsExist.UniversalCompressionSetup
import NonsoficGroupsExist.UniversalPropertyT
import NonsoficGroupsExist.CriterionAssembly
import NonsoficGroupsExist.SoficTransfer

/-!
# Unconditional existence theorems

All inputs to the compression criterion are instantiated here by closed
declarations: the universal-Leavitt rank-four compression setup, property `(T)` for its
ambient group and rank-three core, and the explicit non-LEF corner witness.
The finite-table theorem then supplies a finitely presented nonsofic cover.
-/

namespace NonsoficGroupsExist

/-- The elementary rank-four group over the universal binary Leavitt algebra
`L_{𝔽₂}(1,2)` is nonsofic. -/
theorem universalLeavittEL4_not_isSofic :
    ¬ IsSofic UniversalRankFour.Ambient :=
  not_isSofic_of_not_isLEF UniversalRankFour.compressionSetup
    UniversalRankFour.ambient_hasKazhdanPropertyT
    UniversalRankFour.core_hasKazhdanPropertyT
    UniversalRankFour.witness_not_isLEF

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

/-- The elementary group of rank `m + 1` over the universal binary Leavitt
algebra. -/
noncomputable abbrev UniversalLeavittEL (m : ℕ) :=
  elementaryGroup (Fin (m + 1)) UniversalLeavitt.BinaryLeavittAlgebra

/-- **Theorem A of the manuscript.** For every `m ≥ 3`,
`EL_{m+1}(L_{𝔽₂}(1,2))` is infinite, finitely generated, has property `(T)`,
and is nonsofic. -/
theorem universalLeavitt_theoremA (m : ℕ) (hm : 3 ≤ m) :
    Group.FG (UniversalLeavittEL m) ∧
      Infinite (UniversalLeavittEL m) ∧
      HasKazhdanPropertyT.{0, 0} (UniversalLeavittEL m) ∧
      ¬ IsSofic (UniversalLeavittEL m) := by
  let e : UniversalLeavittEL m ≃* UniversalRankFour.Ambient :=
    UniversalLeavitt.family.rankSuccEquiv m 3 (by omega) (by omega)
  have hfg : Group.FG (UniversalLeavittEL m) :=
    elementaryGroup_finitelyGenerated (m + 1) (by omega)
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

end NonsoficGroupsExist
