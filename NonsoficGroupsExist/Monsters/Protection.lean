import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Diameter one: what a radius-one injectivity theorem protects

Small-cancellation
quotient theorems protect a *ball* of prescribed finite radius in a chosen
generating set.  That normally protects a finite set.  But if an infinite
subgroup `U` is contained in the generating set itself, then every element of
`U` has length one, so radius-one injectivity already embeds all of `U`.

This file proves exactly that combinatorial statement and nothing else.  The
small-cancellation theorems that supply the injectivity hypothesis (Hull's
Theorem 7.1, in the form of Coulon--Fournier-Facio's Theorem 2.9 and
Proposition 4.4) are not formalized here, and the ellipticity bookkeeping that
makes an adjoined countable subgroup land inside the generating set is already
part of Proposition 4.4 rather than new here.  What is written out is the
mechanism: containment in the generating set, not finiteness, is what
finite-radius injectivity actually needs.
-/

namespace NonsoficGroupsExist.Monsters

variable {G H : Type*} [Group G]

/-- One step in the word metric of a generating set: a generator, an inverse
generator, or the identity. -/
def genStep (A : Set G) : Set G := {a : G | a ∈ A ∨ a⁻¹ ∈ A ∨ a = 1}

/-- The ball of radius `n` in the word metric of `A`: products of at most `n`
generators and inverse generators. -/
def ball (A : Set G) : ℕ → Set G
  | 0 => {1}
  | n + 1 => {x : G | ∃ a ∈ genStep A, ∃ y ∈ ball A n, x = a * y}

theorem mem_ball_one_iff {A : Set G} {x : G} : x ∈ ball A 1 ↔ x ∈ genStep A := by
  constructor
  · rintro ⟨a, ha, y, hy, rfl⟩
    rw [show y = 1 from hy]
    simpa using ha
  · intro hx
    exact ⟨x, hx, 1, rfl, by rw [mul_one]⟩

/-- A generator has length one. -/
theorem subset_ball_one (A : Set G) : A ⊆ ball A 1 :=
  fun _ hx ↦ mem_ball_one_iff.2 (Or.inl hx)

/-- **The protection trick.**  A set contained in the generating set has
diameter one, so injectivity on the radius-one ball is injectivity on all of
it -- however infinite it is. -/
theorem injOn_of_subset_generators {A U : Set G} {f : G → H} (hUA : U ⊆ A)
    (hf : Set.InjOn f (ball A 1)) : Set.InjOn f U :=
  hf.mono (hUA.trans (subset_ball_one A))

/-- The subgroup form: a homomorphism injective on the radius-one ball of a
generating set containing `U` restricts to an embedding of `U`. -/
theorem injective_comp_subtype [Group H] {A : Set G} (π : G →* H) (U : Subgroup G)
    (hU : (U : Set G) ⊆ A) (hπ : Set.InjOn π (ball A 1)) :
    Function.Injective (π.comp U.subtype) := by
  have hinj : Set.InjOn π (U : Set G) := injOn_of_subset_generators hU hπ
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
  exact Subtype.ext (hinj ha hb hab)

end NonsoficGroupsExist.Monsters
