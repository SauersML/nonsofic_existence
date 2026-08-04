import NonsoficGroupsExist.ConservativeMatching
import NonsoficGroupsExist.ExpanderReindex
import NonsoficGroupsExist.KunFixedDecomposition
import NonsoficGroupsExist.TableCover

/-!
# Constructing the local criterion data

The two decompositions consumed by the finite matching argument are derived
here from property `(T)`.  The subgroup decomposition is constructed first;
the ambient decomposition is then constructed on its cofinal subsequence, and
the first decomposition is reindexed once more so that both refer to exactly
the same finite models.
-/

namespace NonsoficGroupsExist

/-- Property `(T)` for the compressed subgroup and the ambient group produces
all local criterion data from a concrete compression setup and a sofic
approximation.  No expander decomposition is supplied by the caller. -/
theorem exists_localCriterionData
    {G Γ J : Type} [Group G] [Group Γ] [Group J]
    (C : CompressionSetup G Γ J)
    (hTG : HasKazhdanPropertyT.{0, 0} G)
    (hTΓ : HasKazhdanPropertyT.{0, 0} Γ)
    (A : SoficApproximation G) :
    Nonempty (LocalCriterionData G Γ J) := by
  letI : Infinite Γ := C.infiniteΓ
  letI : Infinite G := Infinite.of_injective C.embedΓ C.embedΓ_injective
  obtain ⟨φ, hφ, ⟨DΓ⟩⟩ := KunFixedDecomposition.exists_reindexed hTΓ
    C.generatorsΓ C.generatorsΓ_one C.generatorsΓ_symmetric
    C.generatorsΓ_generate (A.comap C.embedΓ C.embedΓ_injective)
  have DΓ' : ExpanderDecomposition
      ((A.reindex φ hφ).comap C.embedΓ C.embedΓ_injective) C.generatorsΓ := by
    rw [← SoficApproximation.comap_reindex A C.embedΓ C.embedΓ_injective φ hφ]
    exact DΓ
  obtain ⟨ψ, hψ, ⟨DG⟩⟩ := KunFixedDecomposition.exists_reindexed hTG
    C.ambientGenerators C.ambientGenerators_one C.ambientGenerators_symmetric
    C.ambientGenerators_generate (A.reindex φ hφ)
  let B : SoficApproximation G := (A.reindex φ hφ).reindex ψ hψ
  have DΓ'' := DΓ'.reindex ψ hψ
  have DΓfinal : ExpanderDecomposition
      (B.comap C.embedΓ C.embedΓ_injective) C.generatorsΓ := by
    change ExpanderDecomposition
      (((A.reindex φ hφ).reindex ψ hψ).comap C.embedΓ C.embedΓ_injective)
      C.generatorsΓ
    rw [← SoficApproximation.comap_reindex (A.reindex φ hφ)
      C.embedΓ C.embedΓ_injective ψ hψ]
    exact DΓ''
  exact ⟨{
    setup := C
    approximation := B
    gammaDecomposition := DΓfinal
    ambientDecomposition := DG }⟩

/-- The fully constructed local criterion forces the witness subgroup to be
LEF.  Its only remaining inputs are the concrete compression setup, the two
property-`(T)` proofs, and a sofic approximation of the ambient group. -/
theorem isLEF_of_soficApproximation
    {G Γ J : Type} [Group G] [Group Γ] [Group J]
    [Countable Γ] [Countable J]
    (C : CompressionSetup G Γ J)
    (hTG : HasKazhdanPropertyT.{0, 0} G)
    (hTΓ : HasKazhdanPropertyT.{0, 0} Γ)
    (A : SoficApproximation G) : IsLEF J := by
  obtain ⟨D⟩ := exists_localCriterionData C hTG hTΓ A
  exact D.selectionOutput.isLEF hTΓ

/-- If the ambient group is sofic, the local-to-sequential conversion and the
fully proved compression criterion force the concrete witness subgroup to be
LEF. -/
theorem isLEF_of_isSofic
    {G Γ J : Type} [Group G] [Group Γ] [Group J]
    [Countable G] [Countable Γ] [Countable J]
    (C : CompressionSetup G Γ J)
    (hTG : HasKazhdanPropertyT.{0, 0} G)
    (hTΓ : HasKazhdanPropertyT.{0, 0} Γ)
    (hS : IsSofic G) : IsLEF J := by
  obtain ⟨A⟩ := soficApproximation_of_isSofic hS
  exact isLEF_of_soficApproximation C hTG hTΓ A

/-- A non-LEF witness in a concrete compression setup makes the ambient group
nonsofic once property `(T)` has been proved for the two relevant groups. -/
theorem not_isSofic_of_not_isLEF
    {G Γ J : Type} [Group G] [Group Γ] [Group J]
    [Countable G] [Countable Γ] [Countable J]
    (C : CompressionSetup G Γ J)
    (hTG : HasKazhdanPropertyT.{0, 0} G)
    (hTΓ : HasKazhdanPropertyT.{0, 0} Γ)
    (hJ : ¬ IsLEF J) : ¬ IsSofic G := by
  intro hS
  exact hJ (isLEF_of_isSofic C hTG hTΓ hS)

end NonsoficGroupsExist
