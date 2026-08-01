import NonsoficGroupsExist.Sofic
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Transfer of sofic approximations

Two facts used silently in Section `subsec:partitions` of the manuscript:

* restricting a sofic approximation of `G` along an injective homomorphism
  gives a sofic approximation of the source -- this is what makes `σₙ|_Γ` a
  sofic approximation of `Γ`, so that Kun's theorem may be applied to `Γ`;
* soficity passes to subgroups.

Both are proved from the definition, with no extra hypotheses.
-/

namespace NonsoficGroupsExist

variable {G H : Type*} [Group G] [Group H]

/-- Restrict a sofic approximation along an injective homomorphism. -/
def SoficApproximation.comap (S : SoficApproximation G) (f : H →* G)
    (hf : Function.Injective f) : SoficApproximation H where
  model := S.model
  map n h := S.map n (f h)
  card_tendsToInfinity := S.card_tendsToInfinity
  asymptoticallyMultiplicative g h ε hε := by
    obtain ⟨N, hN⟩ := S.asymptoticallyMultiplicative (f g) (f h) ε hε
    refine ⟨N, fun n hn ↦ ?_⟩
    have := hN n hn
    rwa [← map_mul f g h] at this
  asymptoticallyFaithful g hg ε hε := by
    have hfg : f g ≠ 1 := by
      intro hcon
      exact hg (hf (by simpa using hcon))
    obtain ⟨N, hN⟩ := S.asymptoticallyFaithful (f g) hfg ε hε
    exact ⟨N, fun n hn ↦ hN n hn⟩

@[simp] theorem SoficApproximation.comap_model (S : SoficApproximation G)
    (f : H →* G) (hf : Function.Injective f) (n : ℕ) :
    (S.comap f hf).model n = S.model n := rfl

@[simp] theorem SoficApproximation.comap_map (S : SoficApproximation G)
    (f : H →* G) (hf : Function.Injective f) (n : ℕ) (h : H) :
    (S.comap f hf).map n h = S.map n (f h) := rfl

/-- Soficity passes along injective homomorphisms, in particular to
subgroups. -/
theorem isSofic_of_injective [Countable G] [Countable H] (f : H →* G)
    (hf : Function.Injective f) (h : IsSofic G) : IsSofic H := by
  obtain ⟨S⟩ := h
  exact ⟨S.comap f hf⟩

/-- The restriction of a sofic approximation of `G` to a subgroup. -/
def SoficApproximation.restrict (S : SoficApproximation G) (K : Subgroup G) :
    SoficApproximation K :=
  S.comap K.subtype Subtype.val_injective

end NonsoficGroupsExist
