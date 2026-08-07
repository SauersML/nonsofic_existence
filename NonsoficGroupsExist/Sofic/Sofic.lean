import NonsoficGroupsExist.Sofic.Asymptotics
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
sequential formulation used by the analytic part of the development, and is the
direct transcription of Definition `def:sofic` of the manuscript.

`isSofic_of_soficApproximation` proves the sequential-to-local direction here,
with no countability premise.  The converse needs countability and is proved in
`TableCover`; the two are packaged as an iff in `Sofic.SoficSequential`.
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

/-- Distinct group elements are eventually separated to within any prescribed
accuracy.  Sequential faithfulness is stated only at `h⁻¹ * g` against the
identity; asymptotic multiplicativity and left invariance of the Hamming metric
transport it to the pair `(g, h)`, at the cost of splitting the accuracy in
two. -/
theorem pair_separated_eventually (S : SoficApproximation G) {g h : G}
    (hgh : g ≠ h) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N,
      1 - ε ≤ hammingDistance (S.model n) (S.map n g) (S.map n h) := by
  have hhalf : 0 < ε / 2 := half_pos hε
  have hone : h⁻¹ * g ≠ 1 := fun hcon ↦ hgh (inv_mul_eq_one.mp hcon).symm
  obtain ⟨N₁, hN₁⟩ := S.asymptoticallyFaithful (h⁻¹ * g) hone (ε / 2) hhalf
  obtain ⟨N₂, hN₂⟩ := S.asymptoticallyMultiplicative h (h⁻¹ * g) (ε / 2) hhalf
  refine ⟨max N₁ N₂, fun n hn ↦ ?_⟩
  have hfaith := hN₁ n ((le_max_left N₁ N₂).trans hn)
  have hmul := hN₂ n ((le_max_right N₁ N₂).trans hn)
  rw [mul_inv_cancel_left] at hmul
  have hleft : hammingDistance (S.model n)
      (S.map n h * S.map n (h⁻¹ * g)) (S.map n h) =
      hammingDistance (S.model n) (S.map n (h⁻¹ * g)) 1 := by
    simpa using hammingDistance_left_invariant (S.model n) (S.map n h)
      (S.map n (h⁻¹ * g)) 1
  have htriangle := hammingDistance_triangle (S.model n)
    (S.map n h * S.map n (h⁻¹ * g)) (S.map n g) (S.map n h)
  rw [hleft, hammingDistance_comm (S.model n)
    (S.map n h * S.map n (h⁻¹ * g)) (S.map n g)] at htriangle
  linarith

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

/-- A sequential sofic approximation yields the local finite-model property.

This is the direction of the definitional correspondence that the manuscript
uses implicitly: the models of Definition `def:sofic` are indexed by `ℕ` with
errors that only vanish in the limit, while every endpoint statement consumes
the local predicate `IsSofic`.  Given a finite test set `F` and an accuracy
`ε > 0`, the finitely many eventual estimates attached to elements and pairs of
`F` share a common threshold, and any single member of the sequence beyond that
threshold is a model of `F` to accuracy `ε`.  No countability hypothesis is
needed in this direction: the test set `F` supplies its own finite index set. -/
theorem isSofic_of_soficApproximation {G : Type*} [Group G]
    (A : SoficApproximation G) : IsSofic G := by
  classical
  intro F ε hε
  obtain ⟨N₁, hN₁⟩ := eventually_finset F
    (fun g n ↦ ∀ h ∈ F, hammingDistance (A.model n) (A.map n (g * h))
      (A.map n g * A.map n h) ≤ ε) (by
      intro g _
      show ∃ N : ℕ, ∀ n ≥ N, ∀ h ∈ F,
        hammingDistance (A.model n) (A.map n (g * h))
          (A.map n g * A.map n h) ≤ ε
      refine eventually_finset F
        (fun h n ↦ hammingDistance (A.model n) (A.map n (g * h))
          (A.map n g * A.map n h) ≤ ε) ?_
      intro h _
      obtain ⟨N, hN⟩ := A.asymptoticallyMultiplicative g h ε hε
      exact ⟨N, fun n hn ↦ (hN n hn).le⟩)
  obtain ⟨N₂, hN₂⟩ := eventually_finset F
    (fun g n ↦ ∀ h ∈ F, g ≠ h →
      1 - ε ≤ hammingDistance (A.model n) (A.map n g) (A.map n h)) (by
      intro g _
      show ∃ N : ℕ, ∀ n ≥ N, ∀ h ∈ F, g ≠ h →
        1 - ε ≤ hammingDistance (A.model n) (A.map n g) (A.map n h)
      refine eventually_finset F
        (fun h n ↦ g ≠ h →
          1 - ε ≤ hammingDistance (A.model n) (A.map n g) (A.map n h)) ?_
      intro h _
      by_cases hgh : g = h
      · exact ⟨0, fun _ _ hne ↦ absurd hgh hne⟩
      · obtain ⟨N, hN⟩ := A.pair_separated_eventually hgh ε hε
        exact ⟨N, fun n hn _ ↦ hN n hn⟩)
  obtain ⟨N₃, hN₃⟩ := A.card_tendsToInfinity 1
  obtain ⟨n, hn₁, hn₂, hn₃⟩ : ∃ n : ℕ, N₁ ≤ n ∧ N₂ ≤ n ∧ N₃ ≤ n :=
    ⟨max N₁ (max N₂ N₃), le_max_left _ _,
      (le_max_left N₂ N₃).trans (le_max_right _ _),
      (le_max_right N₂ N₃).trans (le_max_right _ _)⟩
  exact ⟨{
    carrier := A.model n
    nonempty := lt_of_lt_of_le Nat.zero_lt_one (hN₃ n hn₃)
    map := A.map n
    multiplicative := fun g hg h hh ↦ hN₁ n hn₁ g hg h hh
    separated := fun g hg h hh hgh ↦ hN₂ n hn₂ g hg h hh hgh }⟩

end NonsoficGroupsExist
