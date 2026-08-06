import NonsoficGroupsExist.Endpoint.MainResults
import NonsoficGroupsExist.Sofic.SoficTransfer
import NonsoficGroupsExist.Sofic.FreeGroupResiduallyFinite

/-!
# Soficity is not closed under quotients

The two halves are both in the library: free groups are sofic
(`isSofic_freeGroup`, through residual finiteness), and nonsofic groups
exist (`nonsofic_groups_exist`).  Presenting a nonsofic group as a
quotient of the free group on its own underlying set exhibits a sofic
group with a nonsofic quotient — a sharp failure of inheritance, given
that soficity does pass to subgroups (`isSofic_of_injective`).  The same
presentation shows local embeddability and residual finiteness are not
quotient-closed either: the free group has both properties, and a non-LEF
quotient can have neither.
-/

namespace NonsoficGroupsExist

/-- The master presentation: a residually finite group with a normal
subgroup whose quotient is not sofic — the free group on the nonsofic
witness, over the kernel of its tautological presentation. -/
theorem exists_residuallyFinite_group_with_nonsofic_quotient :
    ∃ (H : Type) (_ : Group H) (N : Subgroup H) (_ : N.Normal),
      Group.ResiduallyFinite H ∧ ¬ IsSofic (H ⧸ N) := by
  obtain ⟨G, hG, hns⟩ := nonsofic_groups_exist
  letI := hG
  refine ⟨FreeGroup G, inferInstance, (FreeGroup.lift (id : G → G)).ker,
    inferInstance, freeGroup_residuallyFinite G, ?_⟩
  intro hsofic
  have hsurj : Function.Surjective (FreeGroup.lift (id : G → G)) :=
    FreeGroup.lift_surjective_of_surjective Function.surjective_id
  exact hns ((isSofic_mulEquiv_iff
    (QuotientGroup.quotientKerEquivOfSurjective _ hsurj)).mp hsofic)

/-- **Soficity is not closed under quotients**: there is a sofic group with
a normal subgroup whose quotient is not sofic. -/
theorem exists_sofic_group_with_nonsofic_quotient :
    ∃ (H : Type) (_ : Group H) (N : Subgroup H) (_ : N.Normal),
      IsSofic H ∧ ¬ IsSofic (H ⧸ N) := by
  obtain ⟨H, hH, N, hN, hrf, hns⟩ :=
    exists_residuallyFinite_group_with_nonsofic_quotient
  letI := hH
  letI := hN
  letI := hrf
  exact ⟨H, inferInstance, N, inferInstance,
    isSofic_of_isLEF isLEF_of_residuallyFinite, hns⟩

/-- **Local embeddability is not closed under quotients.** -/
theorem exists_isLEF_group_with_non_isLEF_quotient :
    ∃ (H : Type) (_ : Group H) (N : Subgroup H) (_ : N.Normal),
      IsLEF H ∧ ¬ IsLEF (H ⧸ N) := by
  obtain ⟨H, hH, N, hN, hrf, hns⟩ :=
    exists_residuallyFinite_group_with_nonsofic_quotient
  letI := hH
  letI := hN
  letI := hrf
  exact ⟨H, inferInstance, N, inferInstance, isLEF_of_residuallyFinite,
    fun hlef => hns (isSofic_of_isLEF hlef)⟩

/-- **Residual finiteness is not closed under quotients.** -/
theorem exists_residuallyFinite_group_with_non_residuallyFinite_quotient :
    ∃ (H : Type) (_ : Group H) (N : Subgroup H) (_ : N.Normal),
      Group.ResiduallyFinite H ∧ ¬ Group.ResiduallyFinite (H ⧸ N) := by
  obtain ⟨H, hH, N, hN, hrf, hns⟩ :=
    exists_residuallyFinite_group_with_nonsofic_quotient
  letI := hH
  letI := hN
  refine ⟨H, inferInstance, N, inferInstance, hrf, fun hrfq => ?_⟩
  letI := hrfq
  exact hns (isSofic_of_isLEF isLEF_of_residuallyFinite)

end NonsoficGroupsExist
