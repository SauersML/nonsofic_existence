import NonsoficGroupsExist.ConcreteCompressionSetup
import NonsoficGroupsExist.ConcretePropertyT
import NonsoficGroupsExist.CriterionAssembly

/-!
# Unconditional existence theorems

All inputs to the compression criterion are instantiated here by closed
declarations: the concrete rank-four compression setup, property `(T)` for its
ambient group and rank-three core, and the explicit non-LEF corner witness.
The finite-table theorem then supplies a finitely presented nonsofic cover.
-/

namespace NonsoficGroupsExist

/-- The concrete rank-four elementary group over the represented binary
Leavitt algebra is nonsofic. -/
theorem concreteAmbient_not_isSofic :
    ¬ IsSofic ConcreteRankFour.Ambient :=
  not_isSofic_of_not_isLEF ConcreteRankFour.compressionSetup
    ConcreteRankFour.ambient_hasKazhdanPropertyT
    ConcreteRankFour.core_hasKazhdanPropertyT
    ConcreteRankFour.witness_not_isLEF

/-- Existence of a group which is not sofic. -/
def NonsoficGroupExists : Prop :=
  ∃ (G : Type) (_ : Group G), ¬ IsSofic G

/-- An unconditional, kernel-checked nonsofic-group existence theorem. -/
theorem nonsofic_groups_exist : NonsoficGroupExists := by
  exact ⟨ConcreteRankFour.Ambient, inferInstance,
    concreteAmbient_not_isSofic⟩

/-- An unconditional, kernel-checked finitely presented nonsofic-group
existence theorem. -/
theorem exists_finitelyPresented_nonsofic_group :
    ∃ (G : Type) (_ : Group G),
      Group.IsFinitelyPresented G ∧ ¬ IsSofic G := by
  exact exists_finitelyPresented_nonsofic_cover
    concreteAmbient_not_isSofic

end NonsoficGroupsExist
