import NonsoficGroupsExist.Matching.SelectedGraphComparison

/-!
# Conservative matching from fully supplied local data

Given both expander decompositions and all algebraic fields in a local criterion
datum, the proved finite argument produces a localized approximation of
`Γ × J` whose `Γ`-generator graphs are essentially expanding.
-/

namespace NonsoficGroupsExist

namespace LocalCriterionData

variable {G Γ J : Type} [Group G] [Group Γ] [Group J]
  [Countable Γ] [Countable J]
variable (D : LocalCriterionData G Γ J)

noncomputable def selectionOutput : SelectionOutput D where
  localized := D.selectedLocalization
  graph := D.selectedGraph
  vertexEquiv := fun _ ↦ Equiv.refl _
  cheeger := D.gammaDecomposition.cheeger
  cheeger_pos := D.gammaDecomposition.cheeger_pos
  expands := D.selectedGraph_expands
  degreeBound := D.gammaDecomposition.degreeBound
  degree_le := D.selectedGraph_hasDegreeBound
  edit_negligible := by
    change Negligible D.selectedCard D.localizedSelectedEdit
    exact D.selectedGraph_edit_negligible

end LocalCriterionData

/-- Interface form of the kernel-checked finite matching argument. -/
theorem conservativeMatchingTheorem :
    ∀ (G Γ J : Type) [Group G] [Group Γ] [Group J]
      [Countable Γ] [Countable J],
      ∀ D : LocalCriterionData G Γ J, Nonempty (SelectionOutput D) := by
  intro G Γ J _ _ _ _ _ D
  exact ⟨D.selectionOutput⟩

end NonsoficGroupsExist
