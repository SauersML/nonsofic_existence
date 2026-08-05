import NonsoficGroupsExist.Asymptotics
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Sofic groups and sequential approximations

`IsSofic` is the standard local finite-permutation definition: every finite
subset has an arbitrarily accurate approximately multiplicative and separated
model.  It has no countability premise.  `SoficApproximation` is the equivalent
sequential formulation used by the analytic part of the development; the
conversion for countable groups is proved in `TableCover`.
-/

namespace NonsoficGroupsExist

open scoped Pointwise

/-- Finitely many eventual assertions have one common threshold. -/
theorem eventually_finset {ι : Type*} (s : Finset ι) (P : ι → ℕ → Prop)
    (h : ∀ i ∈ s, ∃ N, ∀ n ≥ N, P i n) :
    ∃ N, ∀ n ≥ N, ∀ i ∈ s, P i n := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert i s hi ih =>
      obtain ⟨Ni, hNi⟩ := h i (Finset.mem_insert_self i s)
      obtain ⟨Ns, hNs⟩ := ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj)
      refine ⟨max Ni Ns, fun n hn j hj ↦ ?_⟩
      rw [Finset.mem_insert] at hj
      rcases hj with rfl | hj
      · exact hNi n ((le_max_left _ _).trans hn)
      · exact hNs n ((le_max_right _ _).trans hn) j hj

/-- A finite type bundled with exactly the instances needed by permutation
models. -/
structure FiniteModel where
  carrier : Type
  fintype : Fintype carrier
  decidableEq : DecidableEq carrier

instance finiteModelCoeSort : CoeSort FiniteModel Type := ⟨FiniteModel.carrier⟩
instance finiteModelFintype (Y : FiniteModel) : Fintype Y := Y.fintype
instance finiteModelDecidableEq (Y : FiniteModel) : DecidableEq Y := Y.decidableEq

/-- The vertices on which two permutations of a finite type disagree. -/
def hammingDisagreement {Y : Type*} [Fintype Y] [DecidableEq Y]
    (p q : Equiv.Perm Y) : Finset Y :=
  Finset.univ.filter fun y ↦ p y ≠ q y

@[simp] theorem mem_hammingDisagreement {Y : Type*} [Fintype Y] [DecidableEq Y]
    (p q : Equiv.Perm Y) (y : Y) :
    y ∈ hammingDisagreement p q ↔ p y ≠ q y := by
  simp [hammingDisagreement]

/-- Normalized Hamming distance on permutations of a finite set.  On the empty
set it is defined to be zero by real division; approximation cardinalities are
separately required to diverge. -/
noncomputable def hammingDistance (Y : FiniteModel) (p q : Equiv.Perm Y) : ℝ :=
  ((hammingDisagreement p q).card : ℝ) / Fintype.card Y

@[simp] theorem hammingDistance_self (Y : FiniteModel) (p : Equiv.Perm Y) :
    hammingDistance Y p p = 0 := by
  simp [hammingDistance, hammingDisagreement]

theorem hammingDistance_comm (Y : FiniteModel) (p q : Equiv.Perm Y) :
    hammingDistance Y p q = hammingDistance Y q p := by
  unfold hammingDistance
  have h : hammingDisagreement p q = hammingDisagreement q p := by
    ext y
    simp only [mem_hammingDisagreement, ne_eq, ne_comm]
  rw [h]

theorem hammingDisagreement_eq_support {Y : Type*} [Fintype Y] [DecidableEq Y]
    (p q : Equiv.Perm Y) :
    hammingDisagreement p q = (q⁻¹ * p).support := by
  ext y
  simp only [mem_hammingDisagreement, Equiv.Perm.mem_support, Equiv.Perm.mul_apply]
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
  rw [hammingDistance, hammingDisagreement_eq_support]

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

/-- A finite permutation model on a prescribed finite subset.  The map is
defined on the whole group, while its laws are required on the test set. -/
structure SoficModel (G : Type*) [Group G] (F : Finset G) (ε : ℝ) where
  carrier : FiniteModel
  nonempty : 0 < Fintype.card carrier
  map : G → Equiv.Perm carrier
  multiplicative : ∀ g ∈ F, ∀ h ∈ F,
    hammingDistance carrier (map (g * h)) (map g * map h) ≤ ε
  separated : ∀ g ∈ F, ∀ h ∈ F, g ≠ h →
    1 - ε ≤ hammingDistance carrier (map g) (map h)

/-- Standard local definition of a sofic group. -/
def IsSofic (G : Type*) [Group G] : Prop :=
  ∀ (F : Finset G) (ε : ℝ), 0 < ε → Nonempty (SoficModel G F ε)

/-- Textbook local models in which multiplicativity is required only when the
tested product remains in the finite test set. -/
structure ProductRestrictedSoficModel (G : Type*) [Group G]
    (F : Finset G) (ε : ℝ) where
  carrier : FiniteModel
  nonempty : 0 < Fintype.card carrier
  map : G → Equiv.Perm carrier
  multiplicative : ∀ g ∈ F, ∀ h ∈ F, g * h ∈ F →
    hammingDistance carrier (map (g * h)) (map g * map h) ≤ ε
  separated : ∀ g ∈ F, ∀ h ∈ F, g ≠ h →
    1 - ε ≤ hammingDistance carrier (map g) (map h)

/-- Soficity using the product-restricted textbook convention. -/
def IsSoficProductRestricted (G : Type*) [Group G] : Prop :=
  ∀ (F : Finset G) (ε : ℝ), 0 < ε →
    Nonempty (ProductRestrictedSoficModel G F ε)

/-- Requiring multiplicativity for all pairs in the test set is equivalent to
requiring it only when their product remains in the set: enlarge `F` by
`F * F` in the reverse direction. -/
theorem isSofic_iff_productRestricted (G : Type*) [Group G] :
    IsSofic G ↔ IsSoficProductRestricted G := by
  classical
  constructor
  · intro h F ε hε
    obtain ⟨M⟩ := h F ε hε
    exact ⟨{
      carrier := M.carrier
      nonempty := M.nonempty
      map := M.map
      multiplicative := fun g hg h hh _ ↦ M.multiplicative g hg h hh
      separated := M.separated }⟩
  · intro h F ε hε
    let T : Finset G := F ∪ F * F
    obtain ⟨M⟩ := h T ε hε
    refine ⟨{
      carrier := M.carrier
      nonempty := M.nonempty
      map := M.map
      multiplicative := ?_
      separated := ?_ }⟩
    · intro g hg h hh
      exact M.multiplicative g (by simp [T, hg]) h (by simp [T, hh])
        (Finset.mem_union_right F (Finset.mul_mem_mul hg hh))
    · intro g hg h hh hgh
      exact M.separated g (by simp [T, hg]) h (by simp [T, hh]) hgh

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

namespace SoficApproximation

variable {G : Type*} [Group G]

/-- Model cardinality as a certified diverging asymptotic scale. -/
def cardScale (S : SoficApproximation G) : AsymptoticScale where
  value := fun n ↦ (Fintype.card (S.model n) : ℝ)
  diverges := by
    intro M
    obtain ⟨K : ℕ, hK : M ≤ K⟩ := exists_nat_ge M
    obtain ⟨N, hN⟩ := S.card_tendsToInfinity K
    refine ⟨N, fun n hn ↦ hK.trans ?_⟩
    have hKN : (K : ℝ) ≤ Fintype.card (S.model n) := by
      exact_mod_cast hN n hn
    exact hKN

@[simp] theorem cardScale_value (S : SoficApproximation G) (n : ℕ) :
    S.cardScale.value n = Fintype.card (S.model n) := rfl

/-- Evaluate a fixed group word using the permutation assigned to each
letter, without assuming that the assignment is a homomorphism. -/
def evaluateWord {Y : Type*} (τ : G → Equiv.Perm Y) : List G → Equiv.Perm Y
  | [] => 1
  | g :: w => τ g * evaluateWord τ w

/-- Approximate multiplicativity forces the assigned identity permutation to
approach the actual identity. -/
theorem map_one_close (S : SoficApproximation G) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N,
      hammingDistance (S.model n) (S.map n 1) 1 < ε := by
  obtain ⟨N, hN⟩ := S.asymptoticallyMultiplicative 1 1 ε hε
  refine ⟨N, ?_⟩
  intro n hn
  have h := hN n hn
  simp only [one_mul] at h
  calc
    hammingDistance (S.model n) (S.map n 1) 1 =
        hammingDistance (S.model n) 1 (S.map n 1) :=
      hammingDistance_comm _ _ _
    _ = hammingDistance (S.model n) ((S.map n 1)⁻¹ * S.map n 1)
        ((S.map n 1)⁻¹ * (S.map n 1 * S.map n 1)) := by simp
    _ = hammingDistance (S.model n) (S.map n 1) (S.map n 1 * S.map n 1) :=
      hammingDistance_left_invariant _ _ _ _
    _ < ε := h

/-- Lemma `lem:word`: every fixed word evaluated letter-by-letter agrees
asymptotically with the permutation assigned to its group value. -/
theorem word_close (S : SoficApproximation G) (w : List G) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N,
      hammingDistance (S.model n) (S.map n w.prod) (evaluateWord (S.map n) w) < ε := by
  induction w generalizing ε with
  | nil =>
      simpa [evaluateWord] using S.map_one_close ε hε
  | cons g w ih =>
      have hhalf : 0 < ε / 2 := half_pos hε
      obtain ⟨N₁, hN₁⟩ := S.asymptoticallyMultiplicative g w.prod (ε / 2) hhalf
      obtain ⟨N₂, hN₂⟩ := ih (ε / 2) hhalf
      refine ⟨max N₁ N₂, ?_⟩
      intro n hn
      have hn₁ : N₁ ≤ n := (le_max_left N₁ N₂).trans hn
      have hn₂ : N₂ ≤ n := (le_max_right N₁ N₂).trans hn
      have hmul := hN₁ n hn₁
      have hword := hN₂ n hn₂
      calc
        hammingDistance (S.model n) (S.map n (g :: w).prod)
            (evaluateWord (S.map n) (g :: w)) ≤
          hammingDistance (S.model n) (S.map n (g * w.prod))
              (S.map n g * S.map n w.prod) +
            hammingDistance (S.model n) (S.map n g * S.map n w.prod)
              (S.map n g * evaluateWord (S.map n) w) := by
                simpa [evaluateWord] using hammingDistance_triangle (S.model n)
                  (S.map n (g * w.prod)) (S.map n g * S.map n w.prod)
                  (S.map n g * evaluateWord (S.map n) w)
        _ < ε / 2 + ε / 2 := by
          apply add_lt_add hmul
          rw [hammingDistance_left_invariant]
          exact hword
        _ = ε := by ring

/-- Reindex a sofic approximation along any pointwise cofinal map.  Strict
monotonicity is unnecessary: the inequality `n ≤ φ n` alone preserves every
eventual estimate in the sequential definition. -/
def reindex (S : SoficApproximation G) (φ : ℕ → ℕ)
    (hφ : ∀ n, n ≤ φ n) : SoficApproximation G where
  model n := S.model (φ n)
  map n := S.map (φ n)
  card_tendsToInfinity M := by
    obtain ⟨N, hN⟩ := S.card_tendsToInfinity M
    exact ⟨N, fun n hn ↦ hN (φ n) (hn.trans (hφ n))⟩
  asymptoticallyMultiplicative g h ε hε := by
    obtain ⟨N, hN⟩ := S.asymptoticallyMultiplicative g h ε hε
    exact ⟨N, fun n hn ↦ hN (φ n) (hn.trans (hφ n))⟩
  asymptoticallyFaithful g hg ε hε := by
    obtain ⟨N, hN⟩ := S.asymptoticallyFaithful g hg ε hε
    exact ⟨N, fun n hn ↦ hN (φ n) (hn.trans (hφ n))⟩

@[simp] theorem reindex_model (S : SoficApproximation G) (φ : ℕ → ℕ)
    (hφ : ∀ n, n ≤ φ n) (n : ℕ) :
    (S.reindex φ hφ).model n = S.model (φ n) := rfl

@[simp] theorem reindex_map (S : SoficApproximation G) (φ : ℕ → ℕ)
    (hφ : ∀ n, n ≤ φ n) (n : ℕ) :
    (S.reindex φ hφ).map n = S.map (φ n) := rfl

end SoficApproximation

end NonsoficGroupsExist
