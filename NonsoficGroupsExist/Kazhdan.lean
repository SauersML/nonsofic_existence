import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Finset.Image

/-!
# Kazhdan's property (T)

For a discrete group, Kazhdan's property `(T)` says that some finite subset and
positive tolerance form a Kazhdan pair: every orthogonal representation with
an almost invariant unit vector has a nonzero invariant vector.  This is the
standard quantitative definition used in the proofs of Kun and of
Ershov--Jaikin-Zapirain.
-/

namespace NonsoficGroupsExist

universe u v w

/-- A finite set `Q` and positive real `ε` are a Kazhdan pair when every
orthogonal representation admitting a `(Q,ε)`-almost invariant unit vector
has a nonzero invariant vector. -/
def IsKazhdanPair (G : Type u) [Group G] (Q : Finset G) (ε : ℝ) : Prop :=
  0 < ε ∧
    ∀ (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [CompleteSpace E],
      ∀ ρ : G →* (E ≃ₗᵢ[ℝ] E), ∀ x : E, ‖x‖ = 1 →
        (∀ q ∈ Q, ‖ρ q x - x‖ < ε) →
          ∃ y : E, y ≠ 0 ∧ ∀ g : G, ρ g y = y

/-- Kazhdan's property `(T)` for a discrete group, in its standard
Kazhdan-pair formulation. -/
def HasKazhdanPropertyT (G : Type u) [Group G] : Prop :=
  ∃ Q : Finset G, ∃ ε : ℝ, IsKazhdanPair.{u, v} G Q ε

namespace HasKazhdanPropertyT

variable {G : Type u} {H : Type v} [Group G] [Group H]

/-- Property `(T)` is invariant under group isomorphism. -/
theorem of_mulEquiv (e : G ≃* H) (hH : HasKazhdanPropertyT.{v, w} H) :
    HasKazhdanPropertyT.{u, w} G := by
  obtain ⟨Q, ε, hε, hQ⟩ := hH
  let QG : Finset G := Q.map e.symm.toEmbedding
  refine ⟨QG, ε, hε, ?_⟩
  intro E _ _ _ ρ x hx hnear
  let ρH : H →* (E ≃ₗᵢ[ℝ] E) := ρ.comp e.symm.toMonoidHom
  have hnearH : ∀ q ∈ Q, ‖ρH q x - x‖ < ε := by
    intro q hq
    apply hnear (e.symm q)
    exact Finset.mem_map.mpr ⟨q, hq, rfl⟩
  obtain ⟨y, hy, hinv⟩ := hQ E ρH x hx hnearH
  exact ⟨y, hy, fun g ↦ by simpa [ρH] using hinv (e g)⟩

theorem mulEquiv_iff (e : G ≃* H) :
    HasKazhdanPropertyT.{u, w} G ↔ HasKazhdanPropertyT.{v, w} H :=
  ⟨fun hG ↦ of_mulEquiv e.symm hG, fun hH ↦ of_mulEquiv e hH⟩

/-- Property `(T)` passes to quotients. -/
theorem of_surjective (f : G →* H) (hf : Function.Surjective f)
    (hG : HasKazhdanPropertyT.{u, w} G) : HasKazhdanPropertyT.{v, w} H := by
  classical
  obtain ⟨Q, ε, hε, hQ⟩ := hG
  let QH : Finset H := Q.image f
  refine ⟨QH, ε, hε, ?_⟩
  intro E _ _ _ ρ x hx hnear
  let ρG : G →* (E ≃ₗᵢ[ℝ] E) := ρ.comp f
  have hnearG : ∀ q ∈ Q, ‖ρG q x - x‖ < ε := by
    intro q hq
    apply hnear (f q)
    simpa [QH] using Finset.mem_image.mpr ⟨q, hq, rfl⟩
  obtain ⟨y, hy, hinv⟩ := hQ E ρG x hx hnearG
  refine ⟨y, hy, fun h ↦ ?_⟩
  obtain ⟨g, rfl⟩ := hf h
  exact hinv g

end HasKazhdanPropertyT
end NonsoficGroupsExist
