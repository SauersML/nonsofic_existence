import NonsoficGroupsExist.Kazhdan.Kazhdan

/-!
# Quantitative transfer from an infinite Kazhdan subset

The Ershov--Jaikin-Zapirain proof has two logically distinct quantitative
parts.  First, the union of the elementary root subgroups is a Kazhdan subset.
Second, displacement by every root element is bounded in terms of displacement
by a finite ring-generator set.  This file proves the general lemma combining
those two statements into an ordinary finite Kazhdan pair.
-/

namespace NonsoficGroupsExist

universe u v

/-- A possibly infinite subset with a uniform Kazhdan displacement threshold.
Unlike `HasKazhdanPropertyT`, finiteness is deliberately not required here. -/
def IsKazhdanSubset (G : Type u) [Group G] (U : Set G) (κ : ℝ) : Prop :=
  0 < κ ∧
    ∀ (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [CompleteSpace E],
      ∀ ρ : G →* (E ≃ₗᵢ[ℝ] E), ∀ x : E, ‖x‖ = 1 →
        (∀ g ∈ U, ‖ρ g x - x‖ < κ) →
          ∃ y : E, y ≠ 0 ∧ ∀ g : G, ρ g y = y

/-- A finite set `S` quantitatively controls displacement by every element of
`U`, uniformly over all orthogonal representations and unit vectors. -/
def ControlsSubsetDisplacement (G : Type u) [Group G]
    (S : Finset G) (U : Set G) (C : ℝ) : Prop :=
  ∀ (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E],
    ∀ ρ : G →* (E ≃ₗᵢ[ℝ] E), ∀ x : E, ‖x‖ = 1 →
      ∀ δ : ℝ, 0 < δ →
        (∀ s ∈ S, ‖ρ s x - x‖ < δ) →
          ∀ g ∈ U, ‖ρ g x - x‖ < C * δ

namespace IsKazhdanSubset

variable {G : Type u} [Group G] {U V : Set G} {κ : ℝ}

/-- Enlarging a Kazhdan subset preserves its constant. -/
theorem mono (hU : IsKazhdanSubset.{u, v} G U κ) (hUV : U ⊆ V) :
    IsKazhdanSubset.{u, v} G V κ := by
  refine ⟨hU.1, ?_⟩
  intro E _ _ _ ρ x hx hnear
  exact hU.2 E ρ x hx fun g hg ↦ hnear g (hUV hg)

/-- A finite Kazhdan pair is the corresponding finite Kazhdan subset. -/
theorem of_pair {Q : Finset G} (hQ : IsKazhdanPair.{u, v} G Q κ) :
    IsKazhdanSubset.{u, v} G (Q : Set G) κ := hQ

/-- A finite Kazhdan subset is an ordinary Kazhdan pair. -/
theorem to_pair {Q : Finset G}
    (hQ : IsKazhdanSubset.{u, v} G (Q : Set G) κ) :
    IsKazhdanPair.{u, v} G Q κ := hQ

end IsKazhdanSubset

/-- Quantitative composition of the two EJZ inputs.  The finite set obtains
Kazhdan tolerance `κ/(2C)`; no bounded-generation hypothesis is used or
hidden in this lemma. -/
theorem IsKazhdanSubset.to_pair_of_controls
    {G : Type u} [Group G] {S : Finset G} {U : Set G} {κ C : ℝ}
    (hU : IsKazhdanSubset.{u, v} G U κ)
    (hC : 0 < C)
    (hcontrol : ControlsSubsetDisplacement.{u, v} G S U C) :
    IsKazhdanPair.{u, v} G S (κ / (2 * C)) := by
  have hden : 0 < 2 * C := mul_pos (by norm_num) hC
  have htol : 0 < κ / (2 * C) := div_pos hU.1 hden
  refine ⟨htol, ?_⟩
  intro E _ _ _ ρ x hx hnear
  apply hU.2 E ρ x hx
  intro g hg
  have hmove := hcontrol E ρ x hx (κ / (2 * C)) htol hnear g hg
  have hscale : C * (κ / (2 * C)) = κ / 2 := by
    field_simp
  rw [hscale] at hmove
  exact hmove.trans (half_lt_self hU.1)

end NonsoficGroupsExist
