import NonsoficGroupsExist.Kun.KunSupport

/-!
# Finite removal for strict Markov contraction

This module formalizes the maximal-bad-set argument in Kun's removal
proposition.  Badness is squared so that it is exactly additive for separated
supports; no square-root approximation is hidden in the certificate.
-/

namespace NonsoficGroupsExist
namespace KunRemoval

open KazhdanFiniteModel
open KazhdanGNS
open KunSupport

variable {G : Type*} [Group G]

/-- Consecutive displacement of an actual finite-model indicator trajectory. -/
noncomputable def indicatorDisplacement
    (A : SoficApproximation G) (n : ℕ) (U : Finset (A.model n))
    (S : Finset G) (k : ℕ) : EuclideanSpace ℝ (A.model n) :=
  finiteModelIndicatorIterate A n U S (k + 1) -
    finiteModelIndicatorIterate A n U S k

/-- A set violates both alternatives of the desired removal conclusion, in
an additive squared formulation. -/
def IsBadSquared
    (A : SoficApproximation G) (n : ℕ) (S : Finset G)
    (k : ℕ) (c' α : ℝ) (U : Finset (A.model n)) : Prop :=
  c' ^ 2 * ‖indicatorDisplacement A n U S 0‖ ^ 2 ≤
      ‖indicatorDisplacement A n U S k‖ ^ 2 ∧
    α ^ 2 * (U.card : ℝ) ≤ ‖indicatorDisplacement A n U S 0‖ ^ 2

theorem finiteModelIndicatorIterate_empty
    (A : SoficApproximation G) (n : ℕ) (S : Finset G) (k : ℕ) :
    finiteModelIndicatorIterate A n (∅ : Finset (A.model n)) S k = 0 := by
  induction k with
  | zero =>
      ext y
      simp [finiteModelIndicatorIterate, indicator_apply]
  | succ k ih =>
      rw [finiteModelIndicatorIterate_succ, ih]
      simp [finiteModelAverage]

@[simp] theorem indicatorDisplacement_empty
    (A : SoficApproximation G) (n : ℕ) (S : Finset G) (k : ℕ) :
    indicatorDisplacement A n (∅ : Finset (A.model n)) S k = 0 := by
  simp [indicatorDisplacement, finiteModelIndicatorIterate_empty]

theorem isBadSquared_empty
    (A : SoficApproximation G) (n : ℕ) (S : Finset G)
    (k : ℕ) (c' α : ℝ) :
    IsBadSquared A n S k c' α ∅ := by
  simp [IsBadSquared]

/-- A finite model has a bad set of maximum cardinality. -/
theorem exists_maximalBadSquared
    (A : SoficApproximation G) (n : ℕ) (S : Finset G)
    (k : ℕ) (c' α : ℝ) :
    ∃ B : Finset (A.model n), IsBadSquared A n S k c' α B ∧
      ∀ U : Finset (A.model n), IsBadSquared A n S k c' α U →
        U.card ≤ B.card := by
  classical
  let candidates := (Finset.univ : Finset (A.model n)).powerset.filter
    (IsBadSquared A n S k c' α)
  have hcandidates : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates, isBadSquared_empty]
  let sizes := candidates.image Finset.card
  have hsizes : sizes.Nonempty := hcandidates.image Finset.card
  let m := sizes.max' hsizes
  have hm : m ∈ sizes := Finset.max'_mem sizes hsizes
  obtain ⟨B, hBcandidates, hBcard⟩ := Finset.mem_image.mp hm
  refine ⟨B, (Finset.mem_filter.mp hBcandidates).2, ?_⟩
  intro U hU
  have hUcandidate : U ∈ candidates := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.subset_univ U), hU⟩
  have hUsize : U.card ∈ sizes :=
    Finset.mem_image.mpr ⟨U, hUcandidate, rfl⟩
  rw [hBcard]
  exact Finset.le_max' sizes U.card hUsize

theorem indicatorDisplacement_union
    (A : SoficApproximation G) (n : ℕ) (U V : Finset (A.model n))
    (hUV : Disjoint U V) (S : Finset G) (k : ℕ) :
    indicatorDisplacement A n (U ∪ V) S k =
      indicatorDisplacement A n U S k +
        indicatorDisplacement A n V S k := by
  exact finiteModelIndicatorDisplacement_union A n U V hUV S k

/-- Squared displacement norms add when the propagation neighborhoods of the
two initial sets are disjoint. -/
theorem norm_indicatorDisplacement_union_sq
    (A : SoficApproximation G) (n : ℕ) (U V : Finset (A.model n))
    (S : Finset G) (k : ℕ)
    (hdisj : Disjoint
      (forwardNeighborhood (A.model n) (A.map n) S (k + 1) U)
      (forwardNeighborhood (A.model n) (A.map n) S (k + 1) V)) :
    ‖indicatorDisplacement A n (U ∪ V) S k‖ ^ 2 =
      ‖indicatorDisplacement A n U S k‖ ^ 2 +
        ‖indicatorDisplacement A n V S k‖ ^ 2 := by
  have hUV : Disjoint U V := by
    rw [Finset.disjoint_left] at hdisj ⊢
    intro y hyU hyV
    exact hdisj
      (forwardNeighborhood_mono_time (A.model n) (A.map n) S
        (Nat.zero_le _) U (by simpa [forwardNeighborhood] using hyU))
      (forwardNeighborhood_mono_time (A.model n) (A.map n) S
        (Nat.zero_le _) V (by simpa [forwardNeighborhood] using hyV))
  rw [indicatorDisplacement_union A n U V hUV]
  exact norm_add_sq_of_disjoint_support (A.model n)
    (indicatorDisplacement A n U S k)
    (indicatorDisplacement A n V S k)
    (forwardNeighborhood (A.model n) (A.map n) S (k + 1) U)
    (forwardNeighborhood (A.model n) (A.map n) S (k + 1) V)
    hdisj
    (fun y hy ↦ finiteModelIndicatorDisplacement_eq_zero_of_not_mem
      A n U S k hy)
    (fun y hy ↦ finiteModelIndicatorDisplacement_eq_zero_of_not_mem
      A n V S k hy)

/-- Squared badness is closed under unions whose relevant propagation
neighborhoods are disjoint. -/
theorem isBadSquared_union
    (A : SoficApproximation G) (n : ℕ) (U V : Finset (A.model n))
    (S : Finset G) (k : ℕ) (c' α : ℝ)
    (hdisj : Disjoint
      (forwardNeighborhood (A.model n) (A.map n) S (k + 1) U)
      (forwardNeighborhood (A.model n) (A.map n) S (k + 1) V))
    (hU : IsBadSquared A n S k c' α U)
    (hV : IsBadSquared A n S k c' α V) :
    IsBadSquared A n S k c' α (U ∪ V) := by
  have hUV : Disjoint U V := by
    rw [Finset.disjoint_left] at hdisj ⊢
    intro y hyU hyV
    exact hdisj
      (forwardNeighborhood_mono_time (A.model n) (A.map n) S
        (Nat.zero_le _) U (by simpa [forwardNeighborhood] using hyU))
      (forwardNeighborhood_mono_time (A.model n) (A.map n) S
        (Nat.zero_le _) V (by simpa [forwardNeighborhood] using hyV))
  have hk := norm_indicatorDisplacement_union_sq A n U V S k hdisj
  have hdisjOne : Disjoint
      (forwardNeighborhood (A.model n) (A.map n) S 1 U)
      (forwardNeighborhood (A.model n) (A.map n) S 1 V) := by
    rw [Finset.disjoint_left] at hdisj ⊢
    intro y hyU hyV
    exact hdisj
      (forwardNeighborhood_mono_time (A.model n) (A.map n) S
        (Nat.succ_le_succ (Nat.zero_le k)) U hyU)
      (forwardNeighborhood_mono_time (A.model n) (A.map n) S
        (Nat.succ_le_succ (Nat.zero_le k)) V hyV)
  have hzero := norm_indicatorDisplacement_union_sq A n U V S 0 hdisjOne
  constructor
  · rw [hzero, hk]
    nlinarith [hU.1, hV.1]
  · rw [hzero, Finset.card_union_of_disjoint hUV]
    push_cast
    nlinarith [hU.2, hV.2]

/-- The global additive contraction bounds the size of every squared-bad set. -/
theorem badSquared_card_bound
    (A : SoficApproximation G) (n : ℕ) (U : Finset (A.model n))
    (S : Finset G) (k : ℕ) (c c' α δ : ℝ)
    (hc0 : 0 ≤ c) (hcc' : c < c') (hδ : 0 ≤ δ)
    (hbad : IsBadSquared A n S k c' α U)
    (hcontract : ‖indicatorDisplacement A n U S k‖ <
      c * ‖indicatorDisplacement A n U S 0‖ +
        δ * Real.sqrt (Fintype.card (A.model n) : ℝ)) :
    α ^ 2 * (c' - c) ^ 2 * (U.card : ℝ) ≤
      δ ^ 2 * Fintype.card (A.model n) := by
  let x := ‖indicatorDisplacement A n U S 0‖
  let y := ‖indicatorDisplacement A n U S k‖
  let R := Real.sqrt (Fintype.card (A.model n) : ℝ)
  have hc'0 : 0 ≤ c' := hc0.trans hcc'.le
  have hcx0 : 0 ≤ c' * x := mul_nonneg hc'0 (norm_nonneg _)
  have hy0 : 0 ≤ y := norm_nonneg _
  have hcxSq : (c' * x) ^ 2 ≤ y ^ 2 := by
    calc
      (c' * x) ^ 2 = c' ^ 2 * x ^ 2 := by ring
      _ ≤ y ^ 2 := by simpa [x, y] using hbad.1
  have hcx : c' * x ≤ y := (sq_le_sq₀ hcx0 hy0).mp hcxSq
  have hgap0 : 0 ≤ (c' - c) * x :=
    mul_nonneg (sub_nonneg.mpr hcc'.le) (norm_nonneg _)
  have hright0 : 0 ≤ δ * R :=
    mul_nonneg hδ (Real.sqrt_nonneg _)
  have hgap : (c' - c) * x < δ * R := by
    dsimp [x, y, R] at hcx ⊢
    linarith
  have hgapSq : ((c' - c) * x) ^ 2 ≤ (δ * R) ^ 2 :=
    ((sq_lt_sq₀ hgap0 hright0).2 hgap).le
  have hscaledBad :
      (c' - c) ^ 2 * (α ^ 2 * (U.card : ℝ)) ≤
        (c' - c) ^ 2 * x ^ 2 := by
    apply mul_le_mul_of_nonneg_left
    · simpa [x] using hbad.2
    · positivity
  have hRsq : R ^ 2 = (Fintype.card (A.model n) : ℝ) := by
    dsimp [R]
    exact Real.sq_sqrt (by positivity)
  calc
    α ^ 2 * (c' - c) ^ 2 * (U.card : ℝ) =
        (c' - c) ^ 2 * (α ^ 2 * (U.card : ℝ)) := by ring
    _ ≤ (c' - c) ^ 2 * x ^ 2 := hscaledBad
    _ = ((c' - c) * x) ^ 2 := by ring
    _ ≤ (δ * R) ^ 2 := hgapSq
    _ = δ ^ 2 * Fintype.card (A.model n) := by
      rw [mul_pow, hRsq]

/-- Kun's finite removal proposition in additive squared form. -/
theorem exists_removalSet_squared
    (A : SoficApproximation G) (n : ℕ) (S : Finset G)
    (k : ℕ) (c c' α δ : ℝ)
    (hc0 : 0 ≤ c) (hcc' : c < c') (hδ : 0 ≤ δ)
    (hcontract : ∀ U : Finset (A.model n),
      ‖indicatorDisplacement A n U S k‖ <
        c * ‖indicatorDisplacement A n U S 0‖ +
          δ * Real.sqrt (Fintype.card (A.model n) : ℝ)) :
    ∃ B : Finset (A.model n),
      α ^ 2 * (c' - c) ^ 2 * (B.card : ℝ) ≤
        ((S.card + 1) ^ (2 * (k + 1)) : ℕ) *
          (δ ^ 2 * Fintype.card (A.model n) : ℝ) ∧
      ∀ U : Finset (A.model n), U.Nonempty → Disjoint U B →
        ¬ IsBadSquared A n S k c' α U := by
  classical
  obtain ⟨B', hB'bad, hB'max⟩ :=
    exists_maximalBadSquared A n S k c' α
  let B := backwardNeighborhood (A.model n) (A.map n) S (k + 1)
    (forwardNeighborhood (A.model n) (A.map n) S (k + 1) B')
  have hB'bound := badSquared_card_bound A n B' S k c c' α δ
    hc0 hcc' hδ hB'bad (hcontract B')
  have hBcardNat : B.card ≤
      (S.card + 1) ^ (2 * (k + 1)) * B'.card := by
    simpa [B] using card_backwardForwardNeighborhood_le
      (A.model n) (A.map n) S (k + 1) B'
  have hBcard : (B.card : ℝ) ≤
      ((S.card + 1) ^ (2 * (k + 1)) : ℕ) * (B'.card : ℝ) := by
    exact_mod_cast hBcardNat
  have hcoeff : 0 ≤ α ^ 2 * (c' - c) ^ 2 := by positivity
  refine ⟨B, ?_, ?_⟩
  · calc
      α ^ 2 * (c' - c) ^ 2 * (B.card : ℝ) ≤
          α ^ 2 * (c' - c) ^ 2 *
            (((S.card + 1) ^ (2 * (k + 1)) : ℕ) * (B'.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hBcard hcoeff
      _ = ((S.card + 1) ^ (2 * (k + 1)) : ℕ) *
          (α ^ 2 * (c' - c) ^ 2 * (B'.card : ℝ)) := by ring
      _ ≤ ((S.card + 1) ^ (2 * (k + 1)) : ℕ) *
          (δ ^ 2 * Fintype.card (A.model n) : ℝ) := by
        gcongr
  · intro U hU hUB hUbad
    have hseparated : Disjoint
        (forwardNeighborhood (A.model n) (A.map n) S (k + 1) B')
        (forwardNeighborhood (A.model n) (A.map n) S (k + 1) U) := by
      apply disjoint_forwardNeighborhood_of_disjoint_backwardForward
      simpa [B] using hUB
    have hB'U : Disjoint B' U := by
      rw [Finset.disjoint_left] at hseparated ⊢
      intro y hyB' hyU
      exact hseparated
        (forwardNeighborhood_mono_time (A.model n) (A.map n) S
          (Nat.zero_le _) B' (by simpa [forwardNeighborhood] using hyB'))
        (forwardNeighborhood_mono_time (A.model n) (A.map n) S
          (Nat.zero_le _) U (by simpa [forwardNeighborhood] using hyU))
    have hunionBad := isBadSquared_union A n B' U S k c' α
      hseparated hB'bad hUbad
    have hmax := hB'max (B' ∪ U) hunionBad
    rw [Finset.card_union_of_disjoint hB'U] at hmax
    exact hU.ne_empty (Finset.card_eq_zero.mp (by omega))

/-- Standard norm form of the finite removal proposition. -/
theorem exists_removalSet
    (A : SoficApproximation G) (n : ℕ) (S : Finset G)
    (k : ℕ) (c c' α δ : ℝ)
    (hc0 : 0 ≤ c) (hcc' : c < c') (hα : 0 < α) (hδ : 0 ≤ δ)
    (hcontract : ∀ U : Finset (A.model n),
      ‖indicatorDisplacement A n U S k‖ <
        c * ‖indicatorDisplacement A n U S 0‖ +
          δ * Real.sqrt (Fintype.card (A.model n) : ℝ)) :
    ∃ B : Finset (A.model n),
      α ^ 2 * (c' - c) ^ 2 * (B.card : ℝ) ≤
        ((S.card + 1) ^ (2 * (k + 1)) : ℕ) *
          (δ ^ 2 * Fintype.card (A.model n) : ℝ) ∧
      ∀ U : Finset (A.model n), U.Nonempty → Disjoint U B →
        ‖indicatorDisplacement A n U S 0‖ <
            α * ‖indicator U‖ ∨
          ‖indicatorDisplacement A n U S k‖ <
            c' * ‖indicatorDisplacement A n U S 0‖ := by
  obtain ⟨B, hBcard, hB⟩ := exists_removalSet_squared
    A n S k c c' α δ hc0 hcc' hδ hcontract
  refine ⟨B, hBcard, fun U hU hUB ↦ ?_⟩
  have hnot := hB U hU hUB
  by_cases hfirst :
      c' ^ 2 * ‖indicatorDisplacement A n U S 0‖ ^ 2 ≤
        ‖indicatorDisplacement A n U S k‖ ^ 2
  · left
    have hsecond : ‖indicatorDisplacement A n U S 0‖ ^ 2 <
        α ^ 2 * (U.card : ℝ) := by
      exact lt_of_not_ge fun hge ↦ hnot ⟨hfirst, hge⟩
    have hsquare : ‖indicatorDisplacement A n U S 0‖ ^ 2 <
        (α * ‖indicator U‖) ^ 2 := by
      rw [mul_pow, norm_indicator_sq]
      exact hsecond
    exact (sq_lt_sq₀ (norm_nonneg _)
      (mul_nonneg hα.le (norm_nonneg _))).mp hsquare
  · right
    have hc'0 : 0 ≤ c' := hc0.trans hcc'.le
    have hsquare : ‖indicatorDisplacement A n U S k‖ ^ 2 <
        (c' * ‖indicatorDisplacement A n U S 0‖) ^ 2 := by
      rw [mul_pow]
      exact lt_of_not_ge hfirst
    exact (sq_lt_sq₀ (norm_nonneg _)
      (mul_nonneg hc'0 (norm_nonneg _))).mp hsquare

end KunRemoval
end NonsoficGroupsExist
