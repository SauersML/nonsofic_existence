import NonsoficGroupsExist.SelectedGraphComparison

/-!
# The internal conservative matching theorem

This closes Sections `subsec:onesided`--`subsec:selection`: every local
criterion datum produces a localized approximation of `Γ × J` whose
`Γ`-generator graphs are essentially expanding.
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
  edit_negligible := by
    simpa [selectedCard, localizedSelectedEdit, localizedGammaGraph,
      localizedGammaAct, selectedLocalization,
      LocalizedApproximationData.localizedModel, generatorGraphVertexEquiv] using
        D.selectedGraph_edit_negligible

end LocalCriterionData

/-- Kernel-level statement of the manuscript's internal matching argument. -/
theorem conservativeMatchingTheorem :
    ∀ (G Γ J : Type) [Group G] [Group Γ] [Group J]
      [Countable Γ] [Countable J],
      ∀ D : LocalCriterionData G Γ J, Nonempty (SelectionOutput D) := by
  intro G Γ J _ _ _ _ _ D
  exact ⟨D.selectionOutput⟩

end NonsoficGroupsExist
