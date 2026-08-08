import NonsoficGroupsExist.Sofic.Hyperlinear
import NonsoficGroupsExist.Sofic.SoficTransfer
import NonsoficGroupsExist.Sofic.LEFSofic

/-!
# Question 3.4 reduces to finitely generated groups

Both soficity and hyperlinearity are defined by quantifying over finite subsets,
so neither can see beyond the subgroup a finite subset generates.  Made precise
that is a reduction of Pestov's Question 3.4 itself: *if every finitely
generated hyperlinear group is sofic, then every hyperlinear group is sofic*.

Two ingredients, both restrictions and nothing more.  Soficity passes along an
injective homomorphism -- that is `isSofic_of_injective` of `SoficTransfer` --
and it is *local*: a model of a subgroup extends to the ambient group by sending
everything outside the image to the identity.  The guard has to be membership in
the image rather than in the finite test set, since the multiplicativity
condition names `g * h`, which need not lie in the test set but does lie in the
image.

Given a finite `F ⊆ G`, the subgroup it generates is finitely generated, and
hyperlinear by `isHyperlinear_of_injective`; the hypothesis makes it sofic; and
locality carries a model back to `G`.  So nothing is lost by restricting
Question 3.4 to finitely generated groups, which is where its known candidates
live in any case.

This does not decide the question.  It says the general case follows from the
finitely generated one.
-/

namespace NonsoficGroupsExist

variable {G : Type} [Group G]

/-- **Soficity is local**, by the same extension as for hyperlinearity. -/
theorem isSofic_of_local
    (h : ∀ F : Finset G, ∃ (H : Type) (_ : Group H) (ι : H →* G),
      Function.Injective ι ∧ IsSofic H ∧ ∀ g ∈ F, g ∈ Set.range ι) :
    IsSofic G := by
  classical
  intro F ε hε
  obtain ⟨H, _, ι, hinj, hH, hcov⟩ := h F
  set ψ : G → H := Function.invFun ι with hψ
  have hψι : ∀ x : H, ψ (ι x) = x := fun x ↦ Function.leftInverse_invFun hinj x
  have hιψ : ∀ g ∈ Set.range ι, ι (ψ g) = g := by
    rintro g ⟨x, rfl⟩
    rw [hψι]
  set F' : Finset H := F.image ψ with hF'
  obtain ⟨M⟩ := hH F' ε hε
  have hmemF' : ∀ g ∈ F, ψ g ∈ F' := fun g hg ↦ Finset.mem_image_of_mem ψ hg
  refine ⟨{
    carrier := M.carrier
    nonempty := M.nonempty
    map := fun g ↦ if g ∈ Set.range ι then M.map (ψ g) else 1
    multiplicative := ?_
    separated := ?_ }⟩
  · intro g hg h hh
    have hgr : g ∈ Set.range ι := hcov g hg
    have hhr : h ∈ Set.range ι := hcov h hh
    have hghr : g * h ∈ Set.range ι := by
      obtain ⟨a, rfl⟩ := hgr
      obtain ⟨b, rfl⟩ := hhr
      exact ⟨a * b, by rw [map_mul]⟩
    have hpsi : ψ (g * h) = ψ g * ψ h := by
      apply hinj
      rw [hιψ _ hghr, map_mul, hιψ _ hgr, hιψ _ hhr]
    simp only [if_pos hgr, if_pos hhr, if_pos hghr, hpsi]
    exact M.multiplicative _ (hmemF' g hg) _ (hmemF' h hh)
  · intro g hg h hh hne
    have hgr : g ∈ Set.range ι := hcov g hg
    have hhr : h ∈ Set.range ι := hcov h hh
    simp only [if_pos hgr, if_pos hhr]
    refine M.separated _ (hmemF' g hg) _ (hmemF' h hh) ?_
    intro hcon
    exact hne (by rw [← hιψ _ hgr, ← hιψ _ hhr, hcon])

/-- **Question 3.4 reduces to finitely generated groups.**  If every finitely
generated hyperlinear group is sofic, then every hyperlinear group is sofic. -/
theorem isSofic_of_isHyperlinear_of_fg_case
    (hfg : ∀ (H : Type) (_ : Group H), Group.FG H → IsHyperlinear H → IsSofic H)
    (hG : IsHyperlinear G) : IsSofic G := by
  classical
  refine isSofic_of_local (fun F ↦ ?_)
  refine ⟨↥(Subgroup.closure (F : Set G)), inferInstance,
    (Subgroup.closure (F : Set G)).subtype, Subgroup.subtype_injective _, ?_, ?_⟩
  · refine hfg _ _ ?_ (isHyperlinear_of_injective _
      (Subgroup.subtype_injective _) hG)
    rw [Group.fg_iff]
    refine ⟨((↑) : Subgroup.closure (F : Set G) → G) ⁻¹' (F : Set G), ?_, ?_⟩
    · exact Subgroup.closure_closure_coe_preimage
    · exact Set.Finite.preimage
        (Set.injOn_of_injective (Subgroup.subtype_injective _)) F.finite_toSet
  · intro g hg
    exact ⟨⟨g, Subgroup.subset_closure hg⟩, rfl⟩


/-! ## The two useful forms of the reduction

The reduction is worth stating twice more, because the forms one reaches for are
different from the form one proves.

As an *equivalence*: Question 3.4 holds in general exactly when it holds for
finitely generated groups.  One direction is the reduction; the other is
immediate, a finitely generated group being a group.

As a statement about *counterexamples*: a counterexample exists exactly when a
finitely generated one does.  This is the contrapositive, and it is the form a
search would use -- it says a hunt may restrict to finitely generated groups
without loss, which is not obvious from the definitions since neither property is
visibly inherited upward.
-/

/-- **Question 3.4 is equivalent to its finitely generated case.** -/
theorem isHyperlinear_imp_isSofic_iff_fg :
    (∀ (H : Type) (_ : Group H), Group.FG H → IsHyperlinear H → IsSofic H)
      ↔ (∀ (H : Type) (_ : Group H), IsHyperlinear H → IsSofic H) := by
  constructor
  · intro hfg H _ hH
    exact isSofic_of_isHyperlinear_of_fg_case hfg hH
  · intro hall H _ _ hH
    exact hall H inferInstance hH

/-- **A counterexample exists exactly when a finitely generated one does.**  The
contrapositive of the reduction: a search for a hyperlinear nonsofic group may
restrict to finitely generated groups without loss. -/
theorem exists_counterexample_iff_exists_fg :
    (∃ (H : Type) (_ : Group H), IsHyperlinear H ∧ ¬ IsSofic H)
      ↔ (∃ (H : Type) (_ : Group H), Group.FG H ∧ IsHyperlinear H
          ∧ ¬ IsSofic H) := by
  constructor
  · rintro ⟨G, hG, hhyp, hnsofic⟩
    by_contra hcon
    refine hnsofic (isSofic_of_isHyperlinear_of_fg_case ?_ hhyp)
    intro H hH hfg hhypH
    by_contra hns
    exact hcon ⟨H, hH, hfg, hhypH, hns⟩
  · rintro ⟨H, hH, _, hhyp, hns⟩
    exact ⟨H, hH, hhyp, hns⟩

/-! ## The profile of a counterexample

Assembling what is already proved, a hyperlinear nonsofic group -- if one exists
-- is constrained on several sides at once, and the constraints are worth having
in one place.

It may be taken finitely generated, by the reduction above.  It is not locally
embeddable into finite groups, since `isSofic_of_isLEF` would make it sofic; a
fortiori it is not residually finite, by `isLEF_of_residuallyFinite`; and it is
infinite, a finite group being residually finite.  What it must *also* be is
non-amenable, since amenable groups are sofic -- that step is quoted, not proved
here, and it is the one that puts the known candidate constructions out of reach.
-/

/-- Residual finiteness implies soficity, through local embeddability. -/
theorem isSofic_of_residuallyFinite [Group.ResiduallyFinite G] : IsSofic G :=
  isSofic_of_isLEF isLEF_of_residuallyFinite

/-- **A counterexample is not locally embeddable into finite groups**, hence not
residually finite. -/
theorem not_isLEF_of_hyperlinear_not_isSofic (hns : ¬ IsSofic G) : ¬ IsLEF G :=
  fun hlef ↦ hns (isSofic_of_isLEF hlef)

/-- **A counterexample may be taken finitely generated and non-residually-finite.**
The full profile in one statement: the reduction supplies the generation
hypothesis, and residual finiteness would supply soficity. -/
theorem exists_counterexample_iff_exists_fg_not_residuallyFinite :
    (∃ (H : Type) (_ : Group H), IsHyperlinear H ∧ ¬ IsSofic H)
      ↔ (∃ (H : Type) (_ : Group H), Group.FG H ∧ IsHyperlinear H
          ∧ ¬ IsSofic H ∧ ¬ IsLEF H) := by
  rw [exists_counterexample_iff_exists_fg]
  constructor
  · rintro ⟨H, hH, hfg, hhyp, hns⟩
    exact ⟨H, hH, hfg, hhyp, hns, not_isLEF_of_hyperlinear_not_isSofic hns⟩
  · rintro ⟨H, hH, hfg, hhyp, hns, _⟩
    exact ⟨H, hH, hfg, hhyp, hns⟩

end NonsoficGroupsExist
