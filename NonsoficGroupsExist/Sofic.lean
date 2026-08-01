import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring

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

theorem disagreement_eq_support (Y : FiniteModel) (p q : Equiv.Perm Y) :
    (Finset.univ.filter fun y ↦ p y ≠ q y) = (q⁻¹ * p).support := by
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.Perm.mem_support,
    Equiv.Perm.mul_apply]
  constructor
  · intro hpq heq
    apply hpq
    have := congrArg q heq
    simpa using this
  · intro hne hpq
    apply hne
    rw [hpq]
    simp

theorem hammingDistance_eq_support (Y : FiniteModel) (p q : Equiv.Perm Y) :
    hammingDistance Y p q = ((q⁻¹ * p).support.card : ℝ) / Fintype.card Y := by
  rw [hammingDistance, disagreement_eq_support]

theorem hammingDistance_nonnegative (Y : FiniteModel) (p q : Equiv.Perm Y) :
    0 ≤ hammingDistance Y p q := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem hammingDistance_le_one (Y : FiniteModel) (p q : Equiv.Perm Y) :
    hammingDistance Y p q ≤ 1 := by
  by_cases hcard : Fintype.card Y = 0
  · simp [hammingDistance, hcard]
  · apply (div_le_one (by exact_mod_cast (Nat.pos_of_ne_zero hcard))).2
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)

theorem hammingDistance_eq_zero_iff (Y : FiniteModel) (p q : Equiv.Perm Y) :
    hammingDistance Y p q = 0 ↔ p = q := by
  by_cases hcard : Fintype.card Y = 0
  · haveI : IsEmpty Y := Fintype.card_eq_zero_iff.mp hcard
    constructor
    · intro _
      exact Subsingleton.elim _ _
    · rintro rfl
      exact hammingDistance_self Y p
  · rw [hammingDistance_eq_support, div_eq_zero_iff]
    simp [hcard]
    constructor
    · intro h
      have h' := congrArg (fun z : Equiv.Perm Y ↦ q * z) h
      simpa [mul_assoc] using h'
    · rintro rfl
      simp

theorem hammingDistance_left_invariant (Y : FiniteModel)
    (s p q : Equiv.Perm Y) :
    hammingDistance Y (s * p) (s * q) = hammingDistance Y p q := by
  rw [hammingDistance_eq_support, hammingDistance_eq_support]
  congr 2
  group

theorem hammingDistance_right_invariant (Y : FiniteModel)
    (p q s : Equiv.Perm Y) :
    hammingDistance Y (p * s) (q * s) = hammingDistance Y p q := by
  rw [hammingDistance_eq_support, hammingDistance_eq_support]
  congr 2
  have hconj : (q * s)⁻¹ * (p * s) = s⁻¹ * (q⁻¹ * p) * (s⁻¹)⁻¹ := by group
  rw [hconj, Equiv.Perm.card_support_conj]

theorem hammingDistance_triangle (Y : FiniteModel) (p q r : Equiv.Perm Y) :
    hammingDistance Y p r ≤ hammingDistance Y p q + hammingDistance Y q r := by
  rw [hammingDistance_eq_support, hammingDistance_eq_support, hammingDistance_eq_support]
  have hfactor : r⁻¹ * p = (r⁻¹ * q) * (q⁻¹ * p) := by group
  rw [hfactor]
  have hcard : (( ((r⁻¹ * q) * (q⁻¹ * p)).support.card : ℕ)) ≤
      (r⁻¹ * q).support.card + (q⁻¹ * p).support.card := by
    exact (Finset.card_le_card (Equiv.Perm.support_mul_le _ _)).trans
      (Finset.card_union_le _ _)
  have hcast : ((((r⁻¹ * q) * (q⁻¹ * p)).support.card : ℕ) : ℝ) ≤
      ((r⁻¹ * q).support.card : ℝ) + ((q⁻¹ * p).support.card : ℝ) := by
    exact_mod_cast hcard
  calc
    (((r⁻¹ * q) * (q⁻¹ * p)).support.card : ℝ) / Fintype.card Y ≤
        (((r⁻¹ * q).support.card : ℝ) + ((q⁻¹ * p).support.card : ℝ)) /
          Fintype.card Y := div_le_div_of_nonneg_right hcast (Nat.cast_nonneg _)
    _ = ((q⁻¹ * p).support.card : ℝ) / Fintype.card Y +
        ((r⁻¹ * q).support.card : ℝ) / Fintype.card Y := by ring

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
