import NonsoficGroupsExist.Monsters.Terminality
import Mathlib.Algebra.Group.Prod
import Mathlib.Data.Countable.Basic

/-!
# Nonsoficity constrains nothing about subgroups

Every countable group embeds in a simple nonsofic group.  Read as content
rather than as colour, this says that nonsoficity puts no restriction
whatsoever on what a group may contain, closing off the guess that nonsofic
groups must be structurally special in some locally detectable way.

The deep half is Coulon--Fournier-Facio's characteristic SQ-universality
theorem (their Theorem 4.1), which is not proved here and is not proved
anywhere in this library.  It enters as an explicit inline hypothesis `hΓ` on
each statement -- a fixed group whose simple quotients absorb any prescribed
countable group -- rather than as a named predicate, so that what is being
assumed is spelled out at every use site and no named proposition exists in
the corpus that nothing establishes.  Everything else -- that the resulting
simple group is nonsofic, and that its nonsoficity is then homomorphically
terminal -- is proved here from that hypothesis together with the soficity
permanence of `Sofic/SoficTransfer`.

What this library *does* supply unconditionally is the nonsofic seed.  The
usual choice is Fournier-Facio's torsion-free nonsofic group;
`Monsters/LeavittMonsters` takes it from `universalLeavittEL4_not_isSofic`
instead, so the only external input left standing in the final statement is the
small-cancellation one.  Torsion-freeness and property `(T)` of the embedding
group are claims about that cited seed rather than about the argument here, and
are correspondingly absent from these statements: this file proves the soficity
half and nothing more.

The countable group carrying both the prescribed `A` and the nonsofic seed `B`
is taken to be `A × B` rather than the free product `A * B`.  The free product
is what preserves the torsion spectrum, which is why a torsion-sensitive
construction needs it; for the embedding and nonsoficity conclusions the direct
product carries exactly the same two subgroups and needs no Kurosh input.
-/

namespace NonsoficGroupsExist.Monsters

open NonsoficGroupsExist

/-- The first factor of a direct product embeds in it. -/
theorem injective_inl (A B : Type) [Group A] [Group B] :
    Function.Injective (MonoidHom.inl A B) := by
  intro a₁ a₂ hab
  simpa using congrArg Prod.fst hab

/-- The second factor of a direct product embeds in it. -/
theorem injective_inr (A B : Type) [Group A] [Group B] :
    Function.Injective (MonoidHom.inr A B) := by
  intro b₁ b₂ hab
  simpa using congrArg Prod.snd hab

/-- **Every countable group sits in a simple nonsofic group.**  Given a group
whose simple quotients
absorb every countable group, and any countable nonsofic group `B`, every
countable group `A` embeds in a simple group `Q` which is nonsofic and
homomorphically terminal: every homomorphism from `Q` to a sofic group is
trivial.

The prescribed `A` is arbitrary, so no property of a group -- torsion,
amenability, solvability, any of it -- is an obstruction to sitting inside a
simple nonsofic group. -/
theorem exists_simple_not_isSofic_containing
    {Γ : Type} [Group Γ]
    (hΓ : ∀ (L : Type) [Group L], Countable L →
      ∃ (Q : Type) (_ : Group Q) (π : Γ →* Q) (ι : L →* Q),
        Function.Surjective π ∧ IsSimpleGroup Q ∧ Function.Injective ι)
    {B : Type} [Group B] [Countable B] (hB : ¬ IsSofic B)
    (A : Type) [Group A] [Countable A] :
    ∃ (Q : Type) (_ : Group Q) (ι : A →* Q),
      IsSimpleGroup Q ∧ Function.Injective ι ∧ ¬ IsSofic Q ∧
        ∀ (S : Type) (_ : Group S), IsSofic S →
          ∀ (φ : Q →* S) (x : Q), φ x = 1 := by
  obtain ⟨Q, instQ, _π, ι, _hsurj, hsimple, hinj⟩ :=
    hΓ (A × B) (inferInstance : Countable (A × B))
  letI := instQ
  haveI := hsimple
  have hQ : ¬ IsSofic Q :=
    not_isSofic_of_injective (ι.comp (MonoidHom.inr A B))
      (hinj.comp (injective_inr A B)) hB
  refine ⟨Q, instQ, ι.comp (MonoidHom.inl A B), hsimple,
    hinj.comp (injective_inl A B), hQ, ?_⟩
  intro S instS hS φ x
  letI := instS
  exact hom_eq_one_of_not_isSofic hQ hS φ x

/-- The same statement with the prescribed group left implicit in the
conclusion: some fixed group has simple nonsofic quotients containing
everything countable. -/
theorem exists_embedding_into_simple_not_isSofic
    {Γ : Type} [Group Γ]
    (hΓ : ∀ (L : Type) [Group L], Countable L →
      ∃ (Q : Type) (_ : Group Q) (π : Γ →* Q) (ι : L →* Q),
        Function.Surjective π ∧ IsSimpleGroup Q ∧ Function.Injective ι)
    {B : Type} [Group B] [Countable B] (hB : ¬ IsSofic B)
    (A : Type) [Group A] [Countable A] :
    ∃ (Q : Type) (_ : Group Q) (ι : A →* Q),
      Function.Injective ι ∧ ¬ IsSofic Q := by
  obtain ⟨Q, instQ, ι, _, hinj, hQ, _⟩ :=
    exists_simple_not_isSofic_containing hΓ hB A
  exact ⟨Q, instQ, ι, hinj, hQ⟩

end NonsoficGroupsExist.Monsters
