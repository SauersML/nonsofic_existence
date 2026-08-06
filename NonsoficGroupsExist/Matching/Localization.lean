import Mathlib.Logic.Equiv.Fintype
import Mathlib.GroupTheory.Perm.Support
import NonsoficGroupsExist.Sofic.Sofic

/-!
# Localization by completion

This file formalizes the finite combinatorial core of Lemma `lem:complete`.
A permutation of an ambient finite set restricts to a partial injection on a
chosen subset, and that partial injection extends to a permutation of the
subset.  The involutive case is completed involutively.
-/

namespace NonsoficGroupsExist

namespace Localization

variable {Y : Type*} [DecidableEq Y]

/-- Points of `D` whose images under `σ` remain in `D`. -/
def internalDomain (D : Finset Y) (σ : Equiv.Perm Y) : Finset D :=
  Finset.univ.filter fun x ↦ σ (x : Y) ∈ D

omit [DecidableEq Y] in
/-- Every restricted partial injection extends to a permutation of `D`. -/
theorem exists_completion (D : Finset Y) (σ : Equiv.Perm Y) :
    ∃ π : Equiv.Perm D, ∀ x : D, σ (x : Y) ∈ D → (π x : Y) = σ x := by
  let A := {x : D // σ (x : Y) ∈ D}
  let source : A → D := fun x ↦ x.1
  let target : A → D := fun x ↦ ⟨σ (x.1 : Y), x.2⟩
  have hsource : Function.Injective source := by
    intro x y hxy
    apply Subtype.ext
    change x.1 = y.1 at hxy
    exact hxy
  have htarget : Function.Injective target := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact σ.injective (Subtype.ext_iff.mp hxy)
  obtain ⟨π, hπ⟩ := Equiv.Perm.exists_extending_pair source target hsource htarget
  refine ⟨π, ?_⟩
  intro x hx
  let a : A := ⟨x, hx⟩
  have ha := hπ a
  exact Subtype.ext_iff.mp ha

/-- A completion can disagree only at points whose ambient images leave `D`. -/
theorem exists_completion_with_bound (D : Finset Y) (σ : Equiv.Perm Y) :
    ∃ π : Equiv.Perm D,
      (Finset.univ.filter fun x : D ↦ (π x : Y) ≠ σ x).card ≤
        (Finset.univ.filter fun x : D ↦ σ (x : Y) ∉ D).card := by
  obtain ⟨π, hπ⟩ := exists_completion D σ
  refine ⟨π, Finset.card_le_card ?_⟩
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  intro hin
  exact hx (hπ x hin)

/-- Complete an ambient involution by its restriction on the invariant
internal domain and by the identity on the remaining points. -/
def involutiveCompletion (D : Finset Y) (σ : Equiv.Perm Y)
    (hσ : σ * σ = 1) : Equiv.Perm D where
  toFun x := if hx : σ (x : Y) ∈ D then ⟨σ x, hx⟩ else x
  invFun x := if hx : σ (x : Y) ∈ D then ⟨σ x, hx⟩ else x
  left_inv x := by
    have hσx : σ (σ (x : Y)) = x := by
      have h := DFunLike.congr_fun hσ (x : Y)
      simpa [Equiv.Perm.mul_apply] using h
    by_cases hx : σ (x : Y) ∈ D
    · simp [hx, hσx, x.2]
    · simp [hx]
  right_inv x := by
    have hσx : σ (σ (x : Y)) = x := by
      have h := DFunLike.congr_fun hσ (x : Y)
      simpa [Equiv.Perm.mul_apply] using h
    by_cases hx : σ (x : Y) ∈ D
    · simp [hx, hσx, x.2]
    · simp [hx]

@[simp] theorem involutiveCompletion_agrees (D : Finset Y) (σ : Equiv.Perm Y)
    (hσ : σ * σ = 1) (x : D) (hx : σ (x : Y) ∈ D) :
    (involutiveCompletion D σ hσ x : Y) = σ x := by
  simp [involutiveCompletion, hx]

theorem involutiveCompletion_sq (D : Finset Y) (σ : Equiv.Perm Y)
    (hσ : σ * σ = 1) :
    involutiveCompletion D σ hσ * involutiveCompletion D σ hσ = 1 := by
  apply Equiv.ext
  intro x
  let π := involutiveCompletion D σ hσ
  change π (π x) = x
  have hinv : π.symm = π := by rfl
  rw [← hinv]
  exact π.symm_apply_apply x

theorem involutiveCompletion_disagreement_bound (D : Finset Y) (σ : Equiv.Perm Y)
    (hσ : σ * σ = 1) :
    (Finset.univ.filter fun x : D ↦
        (involutiveCompletion D σ hσ x : Y) ≠ σ x).card ≤
      (Finset.univ.filter fun x : D ↦ σ (x : Y) ∉ D).card := by
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  intro hin
  exact hx (involutiveCompletion_agrees D σ hσ x hin)

end Localization

end NonsoficGroupsExist
