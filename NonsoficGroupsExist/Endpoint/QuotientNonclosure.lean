import NonsoficGroupsExist.Endpoint.MainResults
import NonsoficGroupsExist.Sofic.SoficTransfer
import NonsoficGroupsExist.Sofic.FreeGroupResiduallyFinite

/-!
# Soficity is not closed under quotients

The two halves are both in the library: free groups are sofic
(`isSofic_freeGroup`, through residual finiteness), and nonsofic groups
exist (`nonsofic_groups_exist`).  Presenting a nonsofic group as a
quotient of the free group on its own underlying set exhibits a sofic
group with a nonsofic quotient — the strongest failure of inheritance the
approximation hierarchy admits, since soficity does pass to subgroups and
extensions by amenable groups.
-/

namespace NonsoficGroupsExist

/-- **Soficity is not closed under quotients**: there is a sofic group with
a normal subgroup whose quotient is not sofic. -/
theorem exists_sofic_group_with_nonsofic_quotient :
    ∃ (H : Type) (_ : Group H) (N : Subgroup H) (_ : N.Normal),
      IsSofic H ∧ ¬ IsSofic (H ⧸ N) := by
  obtain ⟨G, hG, hns⟩ := nonsofic_groups_exist
  letI := hG
  refine ⟨FreeGroup G, inferInstance, (FreeGroup.lift (id : G → G)).ker,
    inferInstance, isSofic_freeGroup G, ?_⟩
  intro hsofic
  have hsurj : Function.Surjective (FreeGroup.lift (id : G → G)) :=
    FreeGroup.lift_surjective_of_surjective Function.surjective_id
  exact hns ((isSofic_mulEquiv_iff
    (QuotientGroup.quotientKerEquivOfSurjective _ hsurj)).mp hsofic)

end NonsoficGroupsExist
