import NonsoficGroupsExist.Sofic.SoficTransfer
import NonsoficGroupsExist.Sofic.SoficPositiveControl
import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Homomorphic terminality of a simple nonsofic group

For a *simple* nonsofic group, nonsoficity is not a defect at the margin but a
total one.  Every homomorphism into a sofic group is trivial, so the group has
no nontrivial sofic image at all, and it embeds in no sofic group.  Dually,
every proper quotient of it is sofic, so a simple nonsofic group is
quotient-minimal among nonsofic groups.

Everything here is two lines from simplicity together with the one permanence
property of soficity that `Sofic/SoficTransfer` already proves --
`isSofic_of_injective`.  No small-cancellation input is involved, and nothing
in this file is specific to any particular construction: the hypotheses are
`IsSimpleGroup` and `¬ IsSofic`, so the conclusions apply to any simple
nonsofic group, however obtained.  No such group is constructed in this
library; the small-cancellation constructions that produce them are
paper-only.

The soficity of finite groups, used for the finite-quotient and
quotient-minimality statements, is the positive control
`isSofic_of_finite` of `Sofic/SoficPositiveControl`; that this file needs it
is another reason that control is not decorative.
-/

namespace NonsoficGroupsExist.Monsters

open NonsoficGroupsExist

variable {G H S : Type*} [Group G] [Group H] [Group S]

/-! ### Permanence, in the direction the obstruction is used -/

/-- Containing a nonsofic group is an obstruction to soficity: the
contrapositive of `isSofic_of_injective`.  This is the only permanence fact
about soficity anything in this directory uses. -/
theorem not_isSofic_of_injective (f : H →* G) (hf : Function.Injective f)
    (hH : ¬ IsSofic H) : ¬ IsSofic G :=
  fun hG ↦ hH (isSofic_of_injective f hf hG)

/-- A nonsofic group embeds in no sofic group.  No simplicity is needed for
this half; simplicity is what upgrades it from "no embedding" to "no
nontrivial homomorphism at all" below. -/
theorem not_injective_of_isSofic (hG : ¬ IsSofic G) (hS : IsSofic S)
    (f : G →* S) : ¬ Function.Injective f :=
  fun hf ↦ hG (isSofic_of_injective f hf hS)

/-! ### Terminality -/

/-- **Terminality.**  Every homomorphism from a simple nonsofic group to a
sofic group is trivial.  The kernel is normal, hence trivial or everything; if
it were trivial the group would embed in a sofic group and so be sofic. -/
theorem hom_eq_one_of_not_isSofic [IsSimpleGroup G] (hG : ¬ IsSofic G)
    (hS : IsSofic S) (f : G →* S) (g : G) : f g = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker inferInstance with hbot | htop
  · exact absurd ((MonoidHom.ker_eq_bot_iff f).mp hbot)
      (not_injective_of_isSofic hG hS f)
  · have hmem : g ∈ f.ker := htop ▸ Subgroup.mem_top g
    simpa [MonoidHom.mem_ker] using hmem

/-- The range of any homomorphism from a simple nonsofic group into a sofic
group is trivial: nonsoficity is homomorphically terminal, not merely a
property of the group itself. -/
theorem range_eq_bot_of_not_isSofic [IsSimpleGroup G] (hG : ¬ IsSofic G)
    (hS : IsSofic S) (f : G →* S) : f.range = ⊥ := by
  refine Subgroup.eq_bot_iff_forall _ |>.2 ?_
  rintro _ ⟨g, rfl⟩
  exact hom_eq_one_of_not_isSofic hG hS f g

/-- A simple nonsofic group has no nontrivial finite quotient, and indeed no
nontrivial homomorphism to any finite group: finite groups are sofic. -/
theorem hom_eq_one_of_finite [IsSimpleGroup G] (hG : ¬ IsSofic G)
    (F : Type) [Group F] [Finite F] (f : G →* F) (g : G) : f g = 1 :=
  hom_eq_one_of_not_isSofic hG (isSofic_of_finite F) f g

/-! ### Quotient-minimality -/

/-- **Quotient-minimality.**  Every proper quotient of a simple group is trivial,
hence finite, hence sofic.  A simple nonsofic group is therefore minimal for
nonsoficity under passage to quotients, while remaining non-minimal under
passage to subgroups whenever it contains a proper nonsofic subgroup. -/
theorem isSofic_of_proper_quotient {Q : Type} [Group Q] [IsSimpleGroup G]
    (f : G →* Q) (hsurj : Function.Surjective f)
    (hinj : ¬ Function.Injective f) : IsSofic Q := by
  have hker : f.ker = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker inferInstance with hbot | htop
    · exact absurd ((MonoidHom.ker_eq_bot_iff f).mp hbot) hinj
    · exact htop
  have hone : ∀ g : G, f g = 1 := by
    intro g
    have hmem : g ∈ f.ker := hker ▸ Subgroup.mem_top g
    simpa [MonoidHom.mem_ker] using hmem
  have hsub : Subsingleton Q := by
    refine ⟨fun x y ↦ ?_⟩
    obtain ⟨a, rfl⟩ := hsurj x
    obtain ⟨b, rfl⟩ := hsurj y
    rw [hone a, hone b]
  have : Finite Q := Finite.of_subsingleton
  exact isSofic_of_finite Q

/-! ### Endomorphisms

Simplicity alone; recorded here because they are what makes "every proper
quotient is trivial" usable in the endomorphism direction. -/

/-- Every nontrivial endomorphism of a simple group is injective. -/
theorem injective_of_exists_ne_one [IsSimpleGroup G] (φ : G →* G)
    (hφ : ∃ g : G, φ g ≠ 1) : Function.Injective φ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker inferInstance with hbot | htop
  · exact (MonoidHom.ker_eq_bot_iff φ).mp hbot
  · obtain ⟨g, hg⟩ := hφ
    have hmem : g ∈ φ.ker := htop ▸ Subgroup.mem_top g
    exact absurd (by simpa [MonoidHom.mem_ker] using hmem) hg

/-- A simple group is Hopfian: every surjective endomorphism is injective. -/
theorem injective_of_surjective [IsSimpleGroup G] (φ : G →* G)
    (hφ : Function.Surjective φ) : Function.Injective φ := by
  obtain ⟨x, hx⟩ := exists_ne (1 : G)
  obtain ⟨g, hg⟩ := hφ x
  exact injective_of_exists_ne_one φ ⟨g, by rw [hg]; exact hx⟩

end NonsoficGroupsExist.Monsters
