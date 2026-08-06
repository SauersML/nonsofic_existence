import NonsoficGroupsExist.Monsters.Terminality
import NonsoficGroupsExist.Monsters.TwoConjugacyClasses
import NonsoficGroupsExist.Monsters.VerbalCompleteness
import NonsoficGroupsExist.Monsters.CountableEmbedding
import NonsoficGroupsExist.Endpoint.MainResults

/-!
# The monster statements over this library's own nonsofic group

Omnimonster constructions start from a fixed finitely presented torsion-free
nonsofic group, cited from Fournier-Facio.  This library proves a nonsofic
group exists, so that seed can be discharged internally instead of cited: every
statement below takes its nonsofic seed from
`universalLeavittEL4_not_isSofic`, the explicit rank-four elementary group over
the universal binary Leavitt algebra.

What the substitution costs, stated plainly.  The seed used here is finitely
generated, infinite, Kazhdan and nonsofic, and this library also builds a
finitely presented nonsofic cover of it; it is *not* known here to be
torsion-free, and torsion-freeness is what the cited seed carries into the
torsion-spectrum bookkeeping.  So the statements below are the soficity and
simplicity halves of the omnimonster package, not their torsion-free
refinements.

What the substitution buys: in `exists_simple_not_isSofic_containing_ambient`
the only external input left is the small-cancellation one.  A reader who
grants Coulon--Fournier-Facio's Theorem 4.1 and nothing else gets: every
countable group embeds in a simple group with no nontrivial homomorphism to any
sofic group.

One sharp question is untouched by any of this.  A finitely presented simple
group has decidable word problem, so monsters that contain a group with
undecidable word problem by construction can never be finitely presented.  The
witness here is not
subject to that obstruction, and this file does not address it either way: the
word problem of `EL₄(L_{𝔽₂}(1,2))` is not formalized in this library.
-/

namespace NonsoficGroupsExist.Monsters

open scoped commutatorElement

open NonsoficGroupsExist

/-! ### Containment of the witness -/

/-- Any group containing this library's nonsofic witness is nonsofic. -/
theorem not_isSofic_of_ambient_embedding {M : Type*} [Group M]
    (f : UniversalRankFour.Ambient →* M) (hf : Function.Injective f) :
    ¬ IsSofic M :=
  not_isSofic_of_injective f hf universalLeavittEL4_not_isSofic

/-- **Terminality over the explicit witness.**  A simple group containing
`EL₄(L_{𝔽₂}(1,2))` has no nontrivial homomorphism to any sofic group. -/
theorem hom_eq_one_of_ambient_embedding {M S : Type*} [Group M] [Group S]
    [IsSimpleGroup M] (f : UniversalRankFour.Ambient →* M)
    (hf : Function.Injective f) (hS : IsSofic S) (φ : M →* S) (x : M) :
    φ x = 1 :=
  hom_eq_one_of_not_isSofic (not_isSofic_of_ambient_embedding f hf) hS φ x

/-! ### Embedding every countable group, with the seed supplied internally -/

/-- **Every countable group sits in a simple nonsofic group, seed discharged.**
Granting only the
small-cancellation input, every countable group embeds in a simple group that
is nonsofic and admits no nontrivial homomorphism to a sofic group.  The
nonsofic seed is this library's own witness, not a cited one. -/
theorem exists_simple_not_isSofic_containing_ambient
    {Γ : Type} [Group Γ]
    (hΓ : ∀ (L : Type) [Group L], Countable L →
      ∃ (Q : Type) (_ : Group Q) (π : Γ →* Q) (ι : L →* Q),
        Function.Surjective π ∧ IsSimpleGroup Q ∧ Function.Injective ι)
    (A : Type) [Group A] [Countable A] :
    ∃ (Q : Type) (_ : Group Q) (ι : A →* Q),
      IsSimpleGroup Q ∧ Function.Injective ι ∧ ¬ IsSofic Q ∧
        ∀ (S : Type) (_ : Group S), IsSofic S →
          ∀ (φ : Q →* S) (x : Q), φ x = 1 :=
  exists_simple_not_isSofic_containing hΓ universalLeavittEL4_not_isSofic A

/-! ### The omnimonster package -/

/-- **The omnimonster profile, the part that is elementary given the generic
properties.**

Let `M` be infinite and torsion-free, contain this library's nonsofic witness,
have exactly two conjugacy classes, and be verbally complete -- the four
conditions a Baire-category argument over a small-cancellation space produces
simultaneously.  Then `M` is simple, centreless, perfect, nonsofic,
homomorphically terminal, divisible, of commutator width one, has no nonzero
homogeneous quasimorphism, and is ICC.

What is *not* proved here is that the four hypotheses are simultaneously
satisfiable: that is the small-cancellation and Baire content, and this library
does not establish it. -/
theorem omnimonster_profile {M : Type} [Group M] [Infinite M]
    (hcc : HasTwoConjugacyClasses M) (hvc : IsVerballyComplete M)
    (htf : ∀ x : M, x ≠ 1 → ∀ n : ℤ, n ≠ 0 → x ^ n ≠ 1)
    (f : UniversalRankFour.Ambient →* M) (hf : Function.Injective f) :
    IsSimpleGroup M ∧
      Subgroup.center M = ⊥ ∧
      commutator M = ⊤ ∧
      ¬ IsSofic M ∧
      (∀ (S : Type) (_ : Group S), IsSofic S → ∀ (φ : M →* S) (x : M), φ x = 1) ∧
      (∀ n : ℕ, n ≠ 0 → ∀ g : M, ∃ x : M, x ^ n = g) ∧
      (∀ g : M, ∃ x y : M, ⁅x, y⁆ = g) ∧
      (∀ (q : M → ℝ) (D : ℝ), IsQuasimorphism q D → IsHomogeneous q →
        ∀ g : M, q g = 0) ∧
      (∀ g : M, g ≠ 1 → {x : M | IsConj g x}.Infinite) := by
  haveI hsimple := hcc.isSimpleGroup
  have hns : ¬ IsSofic M := not_isSofic_of_ambient_embedding f hf
  refine ⟨hsimple, hcc.center_eq_bot, hcc.commutator_eq_top, hns, ?_,
    fun n hn g ↦ hvc.exists_pow_eq hn g, fun g ↦ hvc.exists_commutatorElement_eq g,
    ?_, fun g hg ↦ hcc.infinite_conjClass hg⟩
  · intro S instS hS φ x
    letI := instS
    exact hom_eq_one_of_not_isSofic hns hS φ x
  · intro q D hq hh g
    exact hcc.homogeneousQuasimorphism_eq_zero hq hh
      (fun x hx ↦ htf x hx 2 (by norm_num)) g

end NonsoficGroupsExist.Monsters
