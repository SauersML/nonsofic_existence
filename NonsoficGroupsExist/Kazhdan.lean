import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Kazhdan's property (T)

For countable discrete groups, Kazhdan's property `(T)` is equivalent to the
fixed-point property `(FH)`: every affine isometric action on a real Hilbert
space has a global fixed point.  We use this equivalent characterization as the
formal specification.  This avoids introducing topological-group and unitary-
representation infrastructure that is irrelevant to the manuscript's uses of
property `(T)`, while retaining its standard mathematical meaning for every
group occurring in the paper.
-/

namespace NonsoficGroupsExist

universe u v w

/-- Fixed-point property `(FH)` for affine isometric actions on real Hilbert
spaces; for countable discrete groups this is Kazhdan's property `(T)`. -/
def HasKazhdanPropertyT (G : Type u) [Group G] : Prop :=
  ∀ (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E],
    ∀ ρ : G →* (E ≃ᵃⁱ[ℝ] E), ∃ x : E, ∀ g : G, ρ g x = x

namespace HasKazhdanPropertyT

variable {G : Type u} {H : Type v} [Group G] [Group H]

/-- Property `(T)` is invariant under group isomorphism. -/
theorem of_mulEquiv (e : G ≃* H) (hH : HasKazhdanPropertyT.{v, w} H) :
    HasKazhdanPropertyT.{u, w} G := by
  intro E _ _ _ ρ
  obtain ⟨x, hx⟩ := hH E (ρ.comp e.symm.toMonoidHom)
  exact ⟨x, fun g ↦ by simpa using hx (e g)⟩

theorem mulEquiv_iff (e : G ≃* H) :
    HasKazhdanPropertyT.{u, w} G ↔ HasKazhdanPropertyT.{v, w} H :=
  ⟨fun hG ↦ of_mulEquiv e.symm hG, fun hH ↦ of_mulEquiv e hH⟩

/-- Property `(T)` passes to quotients. -/
theorem of_surjective (f : G →* H) (hf : Function.Surjective f)
    (hG : HasKazhdanPropertyT.{u, w} G) : HasKazhdanPropertyT.{v, w} H := by
  intro E _ _ _ ρ
  obtain ⟨x, hx⟩ := hG E (ρ.comp f)
  refine ⟨x, fun h ↦ ?_⟩
  obtain ⟨g, rfl⟩ := hf h
  exact hx g

end HasKazhdanPropertyT
end NonsoficGroupsExist
