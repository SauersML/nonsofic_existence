import NonsoficGroupsExist.LocalCriterion
import NonsoficGroupsExist.LocalizedApproximation

/-!
# Output of component selection

The weighted diagonal selection in the proof of Theorem `thm:local` has two
simultaneous outputs: a localized approximation of the embedded product
`Γ × J`, and one expanding source component whose transported graph differs
negligibly from the completed `Γ`-generator graph.  This structure records
exactly those outputs.  In particular, the essential-expander conclusion is
not inferred merely from localization.
-/

namespace NonsoficGroupsExist

/-- Exact post-selection output used at the end of Theorem `thm:local`. -/
structure SelectionOutput {G Γ J : Type} [Group G] [Group Γ] [Group J]
    (D : LocalCriterionData G Γ J) where
  localized : LocalizedApproximationData (Γ × J)
  /-- The selected, transported source component. -/
  graph : ℕ → FiniteMultiGraph
  vertexEquiv : ∀ n, (graph n).vertex ≃ localized.subset n
  cheeger : ℝ
  cheeger_pos : 0 < cheeger
  expands : ∀ n, (graph n).HasCheegerLowerBound cheeger
  /-- Completion and all graph transports change only a negligible number of
  generator-edge occurrences. -/
  edit_negligible : Negligible
    (fun n ↦ ((localized.subset n).card : ℝ))
    fun n ↦
      ((generatorGraph (localized.localizedModel n) D.setup.generatorsΓ
          (fun g ↦ localized.completedMap n (g, 1))).editDistance (graph n)
        ((generatorGraphVertexEquiv (localized.localizedModel n)
          D.setup.generatorsΓ (fun g ↦ localized.completedMap n (g, 1))).trans
            (vertexEquiv n).symm) : ℕ)

namespace SelectionOutput

variable {G Γ J : Type} [Group G] [Group Γ] [Group J]
variable {D : LocalCriterionData G Γ J}

/-- The post-selection output supplies every premise of the Kun--Thom
essential-expander interface. -/
noncomputable def toMatchingCertificate (O : SelectionOutput D) :
    MatchingCertificate Γ J where
  generatorsK := D.setup.generatorsΓ
  generatorsK_generate := D.setup.generatorsΓ_generate
  generatorsJ := D.setup.generatorsJ
  generatorsJ_generate := D.setup.generatorsJ_generate
  infiniteK := D.setup.infiniteΓ
  approx := O.localized.toSoficApproximation
  graphs := O.graph
  vertexEquiv := O.vertexEquiv
  cheeger := O.cheeger
  cheeger_pos := O.cheeger_pos
  expands := O.expands
  edit_negligible := by
    simpa [LocalizedApproximationData.toSoficApproximation] using O.edit_negligible

/-- Final invocation at the end of the local theorem, after selection. -/
theorem isLEF (O : SelectionOutput D) (hT : HasKazhdanPropertyT Γ)
    (hKT : KunThomHypothesis Γ J) : IsLEF J :=
  hKT hT O.toMatchingCertificate

end SelectionOutput
end NonsoficGroupsExist
