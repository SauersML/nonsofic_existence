import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Perm.Basic

/-!
# Sofic approximation specification

This file formalizes Definition `def:sofic` from the manuscript.  All finite
model data and every asymptotic quantifier are explicit.
-/

namespace NonsoficGroupsExist

/-- A finite type bundled with exactly the instances needed by permutation
models. -/
structure FiniteModel where
  carrier : Type
  fintype : Fintype carrier
  decidableEq : DecidableEq carrier

instance : CoeSort FiniteModel Type := ⟨FiniteModel.carrier⟩
instance (Y : FiniteModel) : Fintype Y := Y.fintype
instance (Y : FiniteModel) : DecidableEq Y := Y.decidableEq

/-- Normalized Hamming distance on permutations of a finite set.  On the empty
set it is defined to be zero by real division; approximation cardinalities are
separately required to diverge. -/
noncomputable def hammingDistance (Y : FiniteModel) (p q : Equiv.Perm Y) : ℝ :=
  ((Finset.univ.filter fun y ↦ p y ≠ q y).card : ℝ) / Fintype.card Y

@[simp] theorem hammingDistance_self (Y : FiniteModel) (p : Equiv.Perm Y) :
    hammingDistance Y p p = 0 := by
  simp [hammingDistance]

theorem hammingDistance_comm (Y : FiniteModel) (p q : Equiv.Perm Y) :
    hammingDistance Y p q = hammingDistance Y q p := by
  unfold hammingDistance
  have h : (Finset.univ.filter fun y ↦ p y ≠ q y) =
      Finset.univ.filter fun y ↦ q y ≠ p y := by
    ext y
    simp [ne_comm]
  rw [h]

/-- A sequence of finite permutation models satisfying Definition `def:sofic`
in explicit epsilon--eventually form. -/
structure SoficApproximation (G : Type*) [Group G] where
  model : ℕ → FiniteModel
  map : (n : ℕ) → G → Equiv.Perm (model n)
  card_tendsToInfinity : ∀ M : ℕ, ∃ N : ℕ, ∀ n ≥ N, M ≤ Fintype.card (model n)
  asymptoticallyMultiplicative :
    ∀ (g h : G) (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      hammingDistance (model n) (map n (g * h)) (map n g * map n h) < ε
  asymptoticallyFaithful :
    ∀ (g : G), g ≠ 1 → ∀ (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      1 - ε < hammingDistance (model n) (map n g) 1

/-- A countable group is sofic exactly when it has a sofic approximation. -/
def IsSofic (G : Type*) [Group G] [Countable G] : Prop :=
  Nonempty (SoficApproximation G)

end NonsoficGroupsExist
