import NonsoficGroupsExist.Leavitt.UniversalCompressionSetup
import NonsoficGroupsExist.Leavitt.UniversalPropertyT
import NonsoficGroupsExist.Criterion.CriterionAssembly
import NonsoficGroupsExist.Sofic.SoficTransfer
import NonsoficGroupsExist.Sofic.FreeGroupResiduallyFinite
import NonsoficGroupsExist.Leavitt.UniversalLeavittOver
import NonsoficGroupsExist.PropertyT.FiniteTypeCharacteristicTwoPropertyT
import NonsoficGroupsExist.Leavitt.FiniteFieldLeavitt
import NonsoficGroupsExist.Sofic.NearActionModel

/-!
# Unconditional existence theorems

All inputs to the compression criterion are instantiated here by closed
declarations: the universal-Leavitt rank-four compression setup, property `(T)` for its
ambient group and rank-three core, and the explicit non-LEF corner witness.
The finite-table theorem then supplies a finitely presented nonsofic cover.
-/

namespace NonsoficGroupsExist

/-- The elementary group in rank `m + 1` over the universal binary Leavitt
algebra over `k`. -/
noncomputable abbrev BinaryLeavittEL (k : Type) [Field k] (m : ℕ) :=
  elementaryGroup (Fin (m + 1)) (BinaryLeavitt.BinaryLeavittAlgebra k)

/-- Over every finite field, every elementary rank at least two over
`L_k(1,2)` is finitely generated, infinite, Kazhdan, and nonsofic. -/
theorem binaryLeavitt_finiteField_profile (k : Type) [Field k] [Finite k]
    (m : ℕ) (hm : 1 ≤ m) :
    Group.FG (BinaryLeavittEL k m) ∧
      Infinite (BinaryLeavittEL k m) ∧
      HasKazhdanPropertyT.{0, 0} (BinaryLeavittEL k m) ∧
      ¬ IsSofic (BinaryLeavittEL k m) := by
  let L := BinaryLeavitt.family k
  let e : BinaryLeavittEL k m ≃*
      FiniteFieldLeavitt.Ambient k :=
    L.rankSuccEquiv m 3 (by omega) (by omega)
  have hfg : Group.FG (BinaryLeavittEL k m) := by
    letI : Group.FG (FiniteFieldLeavitt.Ambient k) := inferInstance
    exact Group.fg_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hinfinite : Infinite (BinaryLeavittEL k m) :=
    elementaryGroup_infinite
      (R := BinaryLeavitt.BinaryLeavittAlgebra k)
      (0 : Fin (m + 1)) ⟨1, by omega⟩ (by
        intro h
        have hval := congrArg Fin.val h
        norm_num at hval)
  have hT : HasKazhdanPropertyT.{0, 0} (BinaryLeavittEL k m) :=
    L.rankSucc_propertyT_of_rankSucc m 3 (by omega) (by omega)
      (FiniteFieldLeavitt.ambient_hasKazhdanPropertyT k)
  have hnsofic : ¬ IsSofic (BinaryLeavittEL k m) := by
    intro hsofic
    exact FiniteFieldLeavitt.ambient_not_isSofic k
      ((isSofic_mulEquiv_iff e).mp hsofic)
  exact ⟨hfg, hinfinite, hT, hnsofic⟩


/-- The full unit group of `L_k(1,2)` over any field. -/
noncomputable abbrev BinaryLeavittUnits (k : Type) [Field k] :=
  (BinaryLeavitt.BinaryLeavittAlgebra k)ˣ

/-- The general linear group of positive rank `m + 1` over `L_k(1,2)`. -/
noncomputable abbrev BinaryLeavittGL (k : Type) [Field k] (m : ℕ) :=
  (Matrix (Fin (m + 1)) (Fin (m + 1))
    (BinaryLeavitt.BinaryLeavittAlgebra k))ˣ

/-- The full unit group of `L_k(1,2)` is nonsofic for every finite field
`k`: the complete four-leaf prefix code identifies it with `GL₄`, which
contains the nonsofic elementary subgroup. -/
theorem binaryLeavittUnits_not_isSofic (k : Type) [Field k] [Finite k] :
    ¬ IsSofic (BinaryLeavittUnits k) := by
  intro hUnits
  let e : BinaryLeavittGL k 3 ≃* BinaryLeavittUnits k :=
    (BinaryLeavitt.family k).prefixUnitsEquiv (leftCombCode 3)
      ((BinaryLeavitt.family k).leftCombCode_complete 3)
  have hGL : IsSofic (BinaryLeavittGL k 3) :=
    (isSofic_mulEquiv_iff e).mpr hUnits
  exact FiniteFieldLeavitt.ambient_not_isSofic k
    (isSofic_of_injective
      (elementaryGroup (Fin 4)
        (BinaryLeavitt.BinaryLeavittAlgebra k)).subtype
      Subtype.val_injective hGL)

/-- Every positive-rank general linear group over `L_k(1,2)` is nonsofic
for every finite field `k`. -/
theorem binaryLeavittGL_not_isSofic (k : Type) [Field k] [Finite k]
    (m : ℕ) : ¬ IsSofic (BinaryLeavittGL k m) := by
  intro hGL
  let e : BinaryLeavittGL k m ≃* BinaryLeavittUnits k :=
    (BinaryLeavitt.family k).prefixUnitsEquiv (leftCombCode m)
      ((BinaryLeavitt.family k).leftCombCode_complete m)
  exact binaryLeavittUnits_not_isSofic k ((isSofic_mulEquiv_iff e).mp hGL)

/-- The elementary rank-four group over the universal binary Leavitt algebra
`L_{𝔽₂}(1,2)` is nonsofic. -/
theorem universalLeavittEL4_not_isSofic :
    ¬ IsSofic UniversalRankFour.Ambient :=
  not_isSofic_of_not_isLEF UniversalRankFour.compressionSetup
    UniversalRankFour.ambient_hasKazhdanPropertyT
    UniversalRankFour.core_hasKazhdanPropertyT
    UniversalRankFour.witness_not_isLEF

/-- The rank-three core is nonsofic, by the explicit Leavitt
rank-three/rank-four equivalence. -/
theorem universalLeavittEL3_not_isSofic :
    ¬ IsSofic UniversalRankFour.Core := by
  intro h
  exact universalLeavittEL4_not_isSofic
    ((isSofic_mulEquiv_iff UniversalRankFour.family.rankThreeEquivRankFour).mp h)

/-- The full unit group of the universal binary Leavitt algebra. -/
noncomputable abbrev UniversalLeavittUnits :=
  UniversalLeavitt.BinaryLeavittAlgebraˣ

/-- The general linear group of positive rank `m + 1` over the universal
binary Leavitt algebra. -/
noncomputable abbrev UniversalLeavittGL (m : ℕ) :=
  (Matrix (Fin (m + 1)) (Fin (m + 1))
    UniversalLeavitt.BinaryLeavittAlgebra)ˣ

/-- The full unit group of `L_{𝔽₂}(1,2)` is nonsofic.  The complete
four-leaf prefix code identifies it with `GL₄`, which contains the known
nonsofic elementary subgroup. -/
theorem universalLeavittUnits_not_isSofic :
    ¬ IsSofic UniversalLeavittUnits := by
  intro hUnits
  let e : UniversalLeavittGL 3 ≃* UniversalLeavittUnits :=
    UniversalRankFour.family.prefixUnitsEquiv (leftCombCode 3)
      (UniversalRankFour.family.leftCombCode_complete 3)
  have hGL : IsSofic (UniversalLeavittGL 3) :=
    (isSofic_mulEquiv_iff e).mpr hUnits
  exact universalLeavittEL4_not_isSofic
    (isSofic_of_injective
      (elementaryGroup (Fin 4)
        UniversalLeavitt.BinaryLeavittAlgebra).subtype
      Subtype.val_injective hGL)

/-- Every positive-rank general linear group over `L_{𝔽₂}(1,2)` is
nonsofic. -/
theorem universalLeavittGL_not_isSofic (m : ℕ) :
    ¬ IsSofic (UniversalLeavittGL m) := by
  intro hGL
  let e : UniversalLeavittGL m ≃* UniversalLeavittUnits :=
    UniversalRankFour.family.prefixUnitsEquiv (leftCombCode m)
      (UniversalRankFour.family.leftCombCode_complete m)
  exact universalLeavittUnits_not_isSofic
    ((isSofic_mulEquiv_iff e).mp hGL)

/-- The four headline properties of the explicit witness, bundled in the form
most useful to downstream citations. -/
theorem ambient_profile :
    Group.FG UniversalRankFour.Ambient ∧
      Infinite UniversalRankFour.Ambient ∧
      HasKazhdanPropertyT.{0, 0} UniversalRankFour.Ambient ∧
      ¬ IsSofic UniversalRankFour.Ambient := by
  exact ⟨inferInstance, inferInstance,
    UniversalRankFour.ambient_hasKazhdanPropertyT,
    universalLeavittEL4_not_isSofic⟩

/-- The complete five-property profile of the explicit ambient group. -/
theorem ambient_full_profile :
    Countable UniversalRankFour.Ambient ∧
      Group.FG UniversalRankFour.Ambient ∧
      Infinite UniversalRankFour.Ambient ∧
      HasKazhdanPropertyT.{0, 0} UniversalRankFour.Ambient ∧
      ¬ IsSofic UniversalRankFour.Ambient := by
  exact ⟨inferInstance, ambient_profile⟩

/-- The elementary group of rank `m + 1` over the universal binary Leavitt
algebra. -/
noncomputable abbrev UniversalLeavittEL (m : ℕ) :=
  elementaryGroup (Fin (m + 1)) UniversalLeavitt.BinaryLeavittAlgebra

/-- **Theorem A of the manuscript, strengthened to every positive elementary
rank.** For every `m ≥ 1`,
`EL_{m+1}(L_{𝔽₂}(1,2))` is infinite, finitely generated, has property `(T)`,
and is nonsofic. -/
theorem universalLeavitt_profile (m : ℕ) (hm : 1 ≤ m) :
    Group.FG (UniversalLeavittEL m) ∧
      Infinite (UniversalLeavittEL m) ∧
      HasKazhdanPropertyT.{0, 0} (UniversalLeavittEL m) ∧
      ¬ IsSofic (UniversalLeavittEL m) := by
  let e : UniversalLeavittEL m ≃* UniversalRankFour.Ambient :=
    UniversalLeavitt.family.rankSuccEquiv m 3 (by omega) (by omega)
  have hfg : Group.FG (UniversalLeavittEL m) := by
    letI : Group.FG UniversalRankFour.Ambient := inferInstance
    exact Group.fg_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hinfinite : Infinite (UniversalLeavittEL m) :=
    elementaryGroup_infinite
      (R := UniversalLeavitt.BinaryLeavittAlgebra)
      (0 : Fin (m + 1)) ⟨1, by omega⟩ (by
        intro h
        have hval := congrArg Fin.val h
        norm_num at hval)
  have hT : HasKazhdanPropertyT.{0, 0} (UniversalLeavittEL m) :=
    UniversalLeavitt.family.rankSucc_propertyT_of_rankSucc
      m 3 (by omega) (by omega) UniversalRankFour.ambient_hasKazhdanPropertyT
  have hnsofic : ¬ IsSofic (UniversalLeavittEL m) := by
    intro hsofic
    exact universalLeavittEL4_not_isSofic
      ((isSofic_mulEquiv_iff e).mp hsofic)
  exact ⟨hfg, hinfinite, hT, hnsofic⟩

/-- Existence of a group which is not sofic. -/
def NonsoficGroupExists : Prop :=
  ∃ (G : Type) (_ : Group G), ¬ IsSofic G

/-- An unconditional, kernel-checked nonsofic-group existence theorem. -/
theorem nonsofic_groups_exist : NonsoficGroupExists := by
  exact ⟨UniversalRankFour.Ambient, inferInstance,
    universalLeavittEL4_not_isSofic⟩

/-- The historical headline in its countable form: there exists a countable
group which is not sofic. -/
def CountableNonsoficGroupExists : Prop :=
  ∃ (G : Type) (_ : Group G), Countable G ∧ ¬ IsSofic G

/-- An unconditional, kernel-checked countable existence theorem: not every
countable discrete group is sofic.  The witness is the ambient group of
Theorem A, whose countability is the first conjunct of
`ambient_full_profile`. -/
theorem countable_nonsofic_groups_exist : CountableNonsoficGroupExists :=
  ⟨UniversalRankFour.Ambient, inferInstance, ambient_full_profile.1,
    ambient_full_profile.2.2.2.2⟩

/-! ## Pestov's near-action question

The Elek--Szabó characterization is prior mathematics.  The declarations
below record its now-formalized consequence from the nonsofic group constructed
above; they are not presented as a new proof of that characterization in the
mathematical literature.
-/

/-- The explicit countable nonsofic group admits no essentially free,
measure-preserving near action on a set carrying a finitely additive
probability measure on its full power set. -/
theorem universalLeavittEL4_not_admitsEssentiallyFreeNearAction :
    ¬ AdmitsEssentiallyFreeNearAction UniversalRankFour.Ambient := by
  intro hnear
  exact universalLeavittEL4_not_isSofic
    (isSofic_of_admitsEssentiallyFreeNearAction _ hnear)

/-- The precise negative-existence statement corresponding to Pestov's Open
Question 5.3. -/
def CountableGroupWithoutEssentiallyFreeNearActionExists : Prop :=
  ∃ (G : Type) (_ : Group G),
    Countable G ∧ ¬ AdmitsEssentiallyFreeNearAction G

/-- **Negative answer to Pestov's Question 5.3, as a formal corollary of
Elek--Szabó and nonsofic-group existence.**  There is a countable group which
admits no near action of the specified kind. -/
theorem countable_group_without_essentiallyFreeNearAction_exists :
    CountableGroupWithoutEssentiallyFreeNearActionExists :=
  ⟨UniversalRankFour.Ambient, inferInstance, ambient_full_profile.1,
    universalLeavittEL4_not_admitsEssentiallyFreeNearAction⟩

/-- An unconditional, kernel-checked finitely presented nonsofic-group
existence theorem. -/
theorem exists_finitelyPresented_nonsofic_group :
    ∃ (G : Type) (_ : Group G),
      Group.IsFinitelyPresented G ∧ ¬ IsSofic G := by
  exact exists_finitelyPresented_cover_of_not_isSofic
    universalLeavittEL4_not_isSofic

/-- A finitely presented nonsofic group covering the explicit infinite
universal-Leavitt ambient group.  The quotient map is retained, so infinitude
of the cover is part of the checked conclusion. -/
theorem exists_infinite_finitelyPresented_nonsofic_ambient_cover :
    ∃ (H : Type) (_ : Group H),
      Infinite H ∧ Group.IsFinitelyPresented H ∧ ¬ IsSofic H ∧
        ∃ π : H →* UniversalRankFour.Ambient,
          Function.Surjective π := by
  exact exists_infinite_finitelyPresented_cover_of_not_isSofic
    universalLeavittEL4_not_isSofic

/-! ## Soficity does not pass to quotients

Remark `rem:thomK` observes that the candidate groups for Question 3.4 arise as
central quotients of sofic groups, and that whether soficity survives such a
quotient is unsettled.  The *unrestricted* question is not unsettled, and this
development already answers it: soficity does not pass to arbitrary quotients.

Every group is a quotient of a free group, free groups are sofic
(`isSofic_freeGroup`), and by Theorem A a nonsofic group exists.  So some sofic
group has a nonsofic quotient.  That is why the central hypothesis is the right
restriction to be asking about, rather than a convenience: without it the
question has a negative answer for reasons that have nothing to do with
hyperlinearity.
-/

/-- **Soficity is not preserved by quotients.**  A corollary of Theorem A: every
group is a quotient of a free group, and free groups are sofic, so the nonsofic
group of `nonsofic_groups_exist` is a nonsofic quotient of a sofic one. -/
theorem exists_sofic_with_nonsofic_quotient :
    ∃ (G : Type) (_ : Group G) (H : Type) (_ : Group H) (f : G →* H),
      Function.Surjective f ∧ IsSofic G ∧ ¬ IsSofic H := by
  obtain ⟨H, hH, hnsofic⟩ := nonsofic_groups_exist
  refine ⟨FreeGroup H, inferInstance, H, hH, FreeGroup.lift id, ?_,
    isSofic_freeGroup H, hnsofic⟩
  intro h
  exact ⟨FreeGroup.of h, by simp⟩

end NonsoficGroupsExist
