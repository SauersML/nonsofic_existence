import NonsoficGroupsExist.CompressionSetup
import NonsoficGroupsExist.ExternalInputs

/-!
# Exact local compression criterion

This file states the input of Theorem `thm:local` with no preassembled matching
certificate.  It also verifies that `A = S ∪ Q ∪ Q⁻¹` is symmetric and really
generates `G`, facts used when Kun's theorem is applied to the ambient group.
-/

namespace NonsoficGroupsExist

namespace CompressionSetup

variable {G Γ J : Type} [Group G] [Group Γ] [Group J]
variable (C : CompressionSetup G Γ J)

/-- The manuscript's symmetric ambient generator set `A = S ∪ Q ∪ Q⁻¹`. -/
noncomputable def ambientGenerators : Finset G := by
  classical
  exact C.generatorsΓ.image C.embedΓ ∪ C.compressors ∪
    C.compressors.image fun q ↦ q⁻¹

theorem ambientGenerators_symmetric :
    ∀ g ∈ C.ambientGenerators, g⁻¹ ∈ C.ambientGenerators := by
  classical
  intro g hg
  simp only [ambientGenerators, Finset.mem_union, Finset.mem_image] at hg ⊢
  rcases hg with (hg | hg) | hg
  · obtain ⟨x, hx, rfl⟩ := hg
    exact Or.inl (Or.inl ⟨x⁻¹, C.generatorsΓ_symmetric x hx, by simp⟩)
  · exact Or.inr ⟨g, hg, rfl⟩
  · obtain ⟨q, hq, rfl⟩ := hg
    exact Or.inl (Or.inr (by simpa using hq))

theorem embedΓ_mem_closure_ambient (g : Γ) :
    C.embedΓ g ∈ Subgroup.closure (C.ambientGenerators : Set G) := by
  classical
  have hg : g ∈ Subgroup.closure (C.generatorsΓ : Set Γ) := by
    rw [C.generatorsΓ_generate]
    exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      apply Subgroup.subset_closure
      simp only [ambientGenerators, Finset.coe_union, Finset.coe_image, Set.mem_union,
        Set.mem_image]
      exact Or.inl (Or.inl ⟨x, hx, rfl⟩)
  | one => simp
  | mul x y _ _ hx hy => simpa using
      (Subgroup.closure (C.ambientGenerators : Set G)).mul_mem hx hy
  | inv x _ hx => simpa using
      (Subgroup.closure (C.ambientGenerators : Set G)).inv_mem hx

theorem ambientGenerators_generate :
    Subgroup.closure (C.ambientGenerators : Set G) = ⊤ := by
  classical
  apply top_unique
  rw [← C.generates, Subgroup.closure_le]
  intro g hg
  rcases hg with hg | hg
  · obtain ⟨x, rfl⟩ := hg
    exact C.embedΓ_mem_closure_ambient x
  · apply Subgroup.subset_closure
    simp only [ambientGenerators, Finset.coe_union, Finset.coe_image, Set.mem_union,
      Set.mem_image]
    exact Or.inl (Or.inr hg)

end CompressionSetup

/-- All hypotheses of Theorem `thm:local` before its internal matching
argument.  In particular, no `MatchingCertificate` is a field. -/
structure LocalCriterionData (G Γ J : Type) [Group G] [Group Γ] [Group J] where
  setup : CompressionSetup G Γ J
  approximation : SoficApproximation G
  gammaDecomposition : ExpanderDecomposition
    (approximation.comap setup.embedΓ setup.embedΓ_injective) setup.generatorsΓ
  ambientDecomposition : ExpanderDecomposition approximation setup.ambientGenerators

end NonsoficGroupsExist
