import NonsoficGroupsExist.CompressionRefinement
import NonsoficGroupsExist.SelectionOutput
import NonsoficGroupsExist.ExternalInputs
import NonsoficGroupsExist.ConservativeMatching

/-!
# Assembly of the compression--centralizer criterion

The finite matching argument is exposed as one proposition so that its use is
distinguishable from the two cited inputs.  Theorems below perform all logical
assembly: restriction of a hypothetical sofic approximation, both applications
of Kun's theorem, localization, and the Kun--Thom conclusion.
-/

namespace NonsoficGroupsExist

/-- The local compression--centralizer theorem after conservative matching. -/
theorem local_compression_centralizer
    (hKT : KunThomTheorem)
    {G Γ J : Type} [Group G] [Group Γ] [Group J]
    [Countable Γ] [Countable J]
    (hT : HasKazhdanPropertyT Γ) (D : LocalCriterionData G Γ J) :
    IsLEF J := by
  obtain ⟨O⟩ := conservativeMatchingTheorem G Γ J D
  exact O.isLEF hT (hKT Γ J)

/-- Corollary `cor:kazhdan`, with both cited theorems and the internal matching
theorem supplied explicitly. -/
theorem kazhdan_compression_centralizer
    (hKun : KunTheorem) (hKT : KunThomTheorem)
    {G Γ J : Type} [Group G] [Group Γ] [Group J]
    [Countable G] [Countable Γ]
    (C : CompressionSetup G Γ J)
    (hTG : HasKazhdanPropertyT G) (hTΓ : HasKazhdanPropertyT Γ)
    (hsofic : IsSofic G) : IsLEF J := by
  letI : Group.FG Γ := (Group.fg_iff').mpr
    ⟨C.generatorsΓ.card, C.generatorsΓ, rfl, C.generatorsΓ_generate⟩
  letI : Group.FG G := (Group.fg_iff').mpr
    ⟨C.ambientGenerators.card, C.ambientGenerators, rfl,
      C.ambientGenerators_generate⟩
  letI : Infinite Γ := C.infiniteΓ
  letI : Infinite G := Infinite.of_injective C.embedΓ C.embedΓ_injective
  letI : Countable J := C.embedJ_injective.countable
  obtain ⟨S⟩ := hsofic
  obtain ⟨DΓ⟩ := hKun Γ hTΓ C.infiniteΓ
    (S.comap C.embedΓ C.embedΓ_injective) C.generatorsΓ
      C.generatorsΓ_symmetric C.generatorsΓ_generate
  obtain ⟨DG⟩ := hKun G hTG (inferInstance : Infinite G) S
    C.ambientGenerators C.ambientGenerators_symmetric C.ambientGenerators_generate
  let D : LocalCriterionData G Γ J :=
    { setup := C
      approximation := S
      gammaDecomposition := DΓ
      ambientDecomposition := DG }
  exact local_compression_centralizer hKT hTΓ D

/-- Contrapositive form used by every Leavitt instantiation. -/
theorem not_isSofic_of_kazhdan_compression
    (hKun : KunTheorem) (hKT : KunThomTheorem)
    {G Γ J : Type} [Group G] [Group Γ] [Group J]
    [Countable G] [Countable Γ]
    (C : CompressionSetup G Γ J)
    (hTG : HasKazhdanPropertyT G) (hTΓ : HasKazhdanPropertyT Γ)
    (hJ : ¬ IsLEF J) : ¬ IsSofic G := by
  intro hG
  exact hJ (kazhdan_compression_centralizer hKun hKT C hTG hTΓ hG)

end NonsoficGroupsExist
