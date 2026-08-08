import NonsoficGroupsExist.Matching.ConservativeMatching
import NonsoficGroupsExist.Kun.KunFixedDecomposition
import NonsoficGroupsExist.Covers.TableCover

/-!
# Constructing the local criterion data

The two decompositions consumed by the finite matching argument are derived
here from property `(T)` on the same original finite models.  No subsequence
or compatibility reindexing is required.
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
  obtain ⟨DΓ⟩ := KunFixedDecomposition.expanderDecomposition hTΓ
    C.generatorsΓ C.generatorsΓ_one C.generatorsΓ_symmetric
    C.generatorsΓ_generate (A.comap C.embedΓ C.embedΓ_injective)
  obtain ⟨DG⟩ := KunFixedDecomposition.expanderDecomposition hTG
    C.ambientGenerators C.ambientGenerators_one C.ambientGenerators_symmetric
    C.ambientGenerators_generate A
  exact ⟨{
    setup := C
    approximation := A
    gammaDecomposition := DΓ
    ambientDecomposition := DG }⟩

/-! ## How much of property `(T)` the criterion actually uses

The ambient hypothesis is stronger than the proof consumes.  Property `(T)` of
`Γ` enters *twice* -- once through Kun's theorem, to decompose the restricted
approximation into uniform expanders, and once more at the very end, to supply
the Kazhdan pair that the Kun--Thom obstruction needs.  Property `(T)` of the
*ambient* group `G` enters only *once*, and only to produce the ambient
expander decomposition.

So the ambient hypothesis can be replaced by its consequence.  The criterion
below asks for the ambient decomposition directly and never mentions ambient
`(T)`; `exists_localCriterionData` is then the special case in which Kun's
theorem supplies it.  This matters because the ambient hypothesis is exactly
the one the follow-up literature asks about: whether a compression obstruction
needs the ambient group to be Kazhdan, or only needs its approximations to
decompose.  The answer here is the second.

Two honest caveats about how much that buys.  First, the per-approximation
form `isLEF_of_ambientDecomposition` is genuinely weaker: it asks for a
decomposition of the *one* approximation at hand.  Second, the nonsoficity
endpoint quantifies over *all* approximations of `G`, and whether that
quantified property is strictly weaker than `(T)` is **not settled here**.
Kun's theorem gives `(T)` implies it; the converse is not proved in this
development and, as far as the sources cited go, is not known -- Kun's
four-way equivalence is a statement about sequences of graphs, not about
groups.  What is established is the direction of dependence: the proof
consumes the decomposition and nothing else about the ambient group, so any
future sufficient condition for the decomposition slots in unchanged. -/

/-- **The criterion without ambient `(T)`.**  Only the ambient *decomposition*
is required; the ambient group itself need not be Kazhdan.  Property `(T)` of
the compressed subgroup is still used twice, for its own decomposition and for
the Kazhdan pair of the Kun--Thom obstruction. -/
theorem isLEF_of_ambientDecomposition
    {G Γ J : Type} [Group G] [Group Γ] [Group J]
    [Countable Γ] [Countable J]
    (C : CompressionSetup G Γ J)
    (hTΓ : HasKazhdanPropertyT.{0, 0} Γ)
    (A : SoficApproximation G)
    (DG : ExpanderDecomposition A C.ambientGenerators) : IsLEF J := by
  letI : Infinite Γ := C.infiniteΓ
  letI : Infinite G := Infinite.of_injective C.embedΓ C.embedΓ_injective
  obtain ⟨DΓ⟩ := KunFixedDecomposition.expanderDecomposition hTΓ
    C.generatorsΓ C.generatorsΓ_one C.generatorsΓ_symmetric
    C.generatorsΓ_generate (A.comap C.embedΓ C.embedΓ_injective)
  let D : LocalCriterionData G Γ J :=
    { setup := C
      approximation := A
      gammaDecomposition := DΓ
      ambientDecomposition := DG }
  exact D.selectionOutput.isLEF hTΓ

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

/-- **Theorem `thm:D` without ambient `(T)`.**  If every sofic approximation of
`G` admits an ambient expander decomposition, and the witness is not LEF, then
`G` is not sofic -- with no Kazhdan hypothesis on `G` itself.  The Kazhdan
hypothesis on the compressed subgroup `Γ` remains, and is used twice. -/
theorem not_isSofic_of_ambientDecomposition
    {G Γ J : Type} [Group G] [Group Γ] [Group J]
    [Countable G] [Countable Γ] [Countable J]
    (C : CompressionSetup G Γ J)
    (hTΓ : HasKazhdanPropertyT.{0, 0} Γ)
    (hdec : ∀ A : SoficApproximation G,
      Nonempty (ExpanderDecomposition A C.ambientGenerators))
    (hJ : ¬ IsLEF J) : ¬ IsSofic G := by
  intro hS
  obtain ⟨A⟩ := soficApproximation_of_isSofic hS
  obtain ⟨DG⟩ := hdec A
  exact hJ (isLEF_of_ambientDecomposition C hTΓ A DG)

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
