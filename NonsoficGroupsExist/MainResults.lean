import NonsoficGroupsExist.UniversalCompressionSetup
import NonsoficGroupsExist.UniversalPropertyT
import NonsoficGroupsExist.CriterionAssembly

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
