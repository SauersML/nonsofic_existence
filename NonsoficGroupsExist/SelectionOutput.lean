import NonsoficGroupsExist.LocalCriterion
import NonsoficGroupsExist.LocalizedApproximation
import NonsoficGroupsExist.KunThomEssential

/-!
# Output of component selection

The weighted diagonal selection from supplied local criterion data has two
simultaneous outputs: a localized approximation of the embedded product
`Γ × J`, and one expanding source component whose transported graph differs
negligibly from the completed `Γ`-generator graph.  This structure records
exactly those outputs.  In particular, the essential-expander conclusion is
not inferred merely from localization.
-/

namespace NonsoficGroupsExist

/-- Exact post-selection output of the conditional matching construction. -/
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

/-- The selected component forces `J` to be LEF whenever the first factor has
property `(T)`.  The Kun--Thom argument and essential-to-exact repair are
proved internally; no theorem-shaped implication is supplied by the caller. -/
theorem isLEF (O : SelectionOutput D)
    (hT : HasKazhdanPropertyT.{0, 0} Γ) : IsLEF J := by
  classical
  obtain ⟨Q, κ, honeQ, _hκpos, hκone, hQ⟩ :=
    HasKazhdanPropertyT.exists_identity_pair hT
  let S : Finset Γ := Q ∪ D.setup.generatorsΓ
  apply KunThomEssential.isLEF_of_matchingCertificate hQ
    O.toMatchingCertificate S
  · exact Finset.subset_union_left
  · exact Finset.subset_union_right
  · exact Finset.mem_union_left _ honeQ
  · exact hκone

end SelectionOutput
end NonsoficGroupsExist
