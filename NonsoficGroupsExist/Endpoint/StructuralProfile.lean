import NonsoficGroupsExist.Endpoint.MainResults
import NonsoficGroupsExist.Leavitt.ElementaryNoFiniteQuotients
import NonsoficGroupsExist.Sofic.SoficUltraproduct
import NonsoficGroupsExist.Leavitt.LeavittSimplicity
import NonsoficGroupsExist.Covers.TableCover

/-!
# What the witness looks like from outside

Two endpoints about `EL₄(L_{𝔽₂}(1,2))` that the manuscript states and that are
compositions rather than single results elsewhere in the library.

`universalLeavittEL4_finite_quotient_trivial` is the positive one: every
homomorphism from the witness to a finite group is trivial.  This is much
stronger than the failure of residual finiteness that nonsoficity already
gives.  It says the group has no proper finite-index subgroup, no nontrivial
action on a finite set, and trivial profinite completion -- there is no
residual structure at all for the failure of soficity to be an artifact of.
With Malcev's theorem it also rules out every nontrivial finite-dimensional
linear representation over every field, though that step is not formalized
here.

`universalLeavittEL4_no_soficEmbedding` is the negative one, in the language
the surrounding literature uses: the witness admits no injective homomorphism
into any metric ultraproduct of finite symmetric groups, over any index type
and any ultrafilter.
-/

namespace NonsoficGroupsExist

open UniversalRankFour

/-- Three indices are available in rank four. -/
theorem rankFour_exists_third_index (l k : RankFour.Index) :
    ∃ i : RankFour.Index, i ≠ l ∧ i ≠ k :=
  exists_third_index (by simp [RankFour.Index]) l k

/-- **The witness has no nontrivial finite quotient.**  Every homomorphism from
`EL₄(L_{𝔽₂}(1,2))` to a finite group is trivial. -/
theorem universalLeavittEL4_finite_quotient_trivial
    {Q : Type*} [Group Q] [Finite Q] (φ : Ambient →* Q) (g : Ambient) :
    φ g = 1 :=
  elementaryGroup_finite_quotient_trivial
    (fun _ hx ↦ BinaryLeavitt.exists_mul_mul_eq_one (ZMod 2) hx)
    (fun l k _ ↦ rankFour_exists_third_index l k) φ g

/-- The witness has no proper subgroup of finite index: a coset action would
be a nontrivial homomorphism to a finite group. -/
theorem universalLeavittEL4_no_finite_quotient
    {Q : Type*} [Group Q] [Finite Q] (φ : Ambient →* Q) :
    φ = 1 :=
  MonoidHom.ext fun g ↦ universalLeavittEL4_finite_quotient_trivial φ g

/-- **No sofic embedding.**  The witness admits no injective homomorphism into
any metric ultraproduct of finite symmetric groups. -/
theorem universalLeavittEL4_no_soficEmbedding {ι : Type*} (𝒰 : Ultrafilter ι)
    (X : ι → FiniteModel) (hX : ∀ i, 0 < Fintype.card (X i))
    (f : Ambient →* UniversalSofic 𝒰 X) :
    ¬ Function.Injective f :=
  no_soficEmbedding_of_not_isSofic 𝒰 X universalLeavittEL4_not_isSofic hX f

/-- **Soficity is embeddability into a universal sofic group**, for countable
groups: the local finite-model definition and the operator-algebraic one agree.
Together with `isSofic_of_soficEmbedding` this closes the identification in both
directions. -/
theorem exists_soficEmbedding_of_isSofic {G : Type*} [Group G] [Countable G]
    (h : IsSofic G) {𝒰 : Ultrafilter ℕ}
    (hcof : (𝒰 : Filter ℕ) ≤ Filter.cofinite) :
    ∃ (X : ℕ → FiniteModel) (f : G →* UniversalSofic 𝒰 X),
      Function.Injective f := by
  obtain ⟨S⟩ := soficApproximation_of_isSofic h
  obtain ⟨f, hf⟩ := exists_soficEmbedding_of_soficApproximation S hcof
  exact ⟨S.model, f, hf⟩

end NonsoficGroupsExist
