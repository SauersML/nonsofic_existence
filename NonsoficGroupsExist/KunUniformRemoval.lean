import NonsoficGroupsExist.KunUniformMovement
import NonsoficGroupsExist.KunRemoval

/-!
# Removal with a horizon-independent proximity constant

The original removal module controls one late consecutive displacement.  For
the fixed-cut form of Kun's theorem we instead remove maximal sets on which
the whole trajectory moves too far relative to its first displacement.  The
badness predicate remains squared and additive on separated supports.
-/

namespace NonsoficGroupsExist
namespace KunUniformRemoval

open KazhdanFiniteModel
open KazhdanGNS
open KunSupport
open KunRemoval
open KunUniformMovement

variable {G : Type} [Group G]

/-- Total motion from the input indicator to time `k`. -/
noncomputable def trajectoryMovement
    (A : SoficApproximation G) (n : ℕ) (U : Finset (A.model n))
    (S : Finset G) (k : ℕ) : EuclideanSpace ℝ (A.model n) :=
  finiteModelIndicatorIterate A n U S k - indicator U

@[simp] theorem trajectoryMovement_empty
    (A : SoficApproximation G) (n : ℕ) (S : Finset G) (k : ℕ) :
    trajectoryMovement A n (∅ : Finset (A.model n)) S k = 0 := by
  rw [trajectoryMovement, finiteModelIndicatorIterate_empty]
  have hempty : indicator (∅ : Finset (A.model n)) = 0 := by
    ext y
    simp [indicator_apply]
  rw [hempty, sub_zero]

/-- Total motion is additive on disjoint initial sets. -/
theorem trajectoryMovement_union
    (A : SoficApproximation G) (n : ℕ) (U V : Finset (A.model n))
    (hUV : Disjoint U V) (S : Finset G) (k : ℕ) :
    trajectoryMovement A n (U ∪ V) S k =
      trajectoryMovement A n U S k + trajectoryMovement A n V S k := by
  rw [trajectoryMovement, trajectoryMovement, trajectoryMovement,
    show indicator (U ∪ V) = indicator U + indicator V by
      simpa [finiteModelIndicatorIterate] using
        finiteModelIndicatorIterate_union A n U V hUV S 0,
    finiteModelIndicatorIterate_union A n U V hUV]
  abel

/-- Total motion has the same radius-`k` finite propagation as the endpoint
trajectory. -/
theorem trajectoryMovement_eq_zero_of_not_mem
    (A : SoficApproximation G) (n : ℕ) (U : Finset (A.model n))
    (S : Finset G) (k : ℕ) {y : A.model n}
    (hy : y ∉ forwardNeighborhood (A.model n) (A.map n) S k U) :
    trajectoryMovement A n U S k y = 0 := by
  have hiterate :=
    finiteModelIndicatorIterate_eq_zero_of_not_mem_forwardNeighborhood
      A n U S k hy
  have hyU : y ∉ U := by
    intro hyU
    apply hy
    exact forwardNeighborhood_mono_time (A.model n) (A.map n) S
      (Nat.zero_le k) U (by simpa [forwardNeighborhood] using hyU)
  simp [trajectoryMovement, hiterate, indicator_apply, hyU]

/-- Squared total-motion norms add for radius-separated initial sets. -/
theorem norm_trajectoryMovement_union_sq
    (A : SoficApproximation G) (n : ℕ) (U V : Finset (A.model n))
    (S : Finset G) (k : ℕ)
    (hdisj : Disjoint
      (forwardNeighborhood (A.model n) (A.map n) S k U)
      (forwardNeighborhood (A.model n) (A.map n) S k V)) :
    ‖trajectoryMovement A n (U ∪ V) S k‖ ^ 2 =
      ‖trajectoryMovement A n U S k‖ ^ 2 +
        ‖trajectoryMovement A n V S k‖ ^ 2 := by
  have hUV : Disjoint U V := by
    rw [Finset.disjoint_left] at hdisj ⊢
    intro y hyU hyV
    exact hdisj
      (forwardNeighborhood_mono_time (A.model n) (A.map n) S
        (Nat.zero_le k) U (by simpa [forwardNeighborhood] using hyU))
      (forwardNeighborhood_mono_time (A.model n) (A.map n) S
        (Nat.zero_le k) V (by simpa [forwardNeighborhood] using hyV))
  rw [trajectoryMovement_union A n U V hUV]
  exact norm_add_sq_of_disjoint_support (A.model n)
    (trajectoryMovement A n U S k) (trajectoryMovement A n V S k)
    (forwardNeighborhood (A.model n) (A.map n) S k U)
    (forwardNeighborhood (A.model n) (A.map n) S k V) hdisj
    (fun y hy ↦ trajectoryMovement_eq_zero_of_not_mem A n U S k hy)
    (fun y hy ↦ trajectoryMovement_eq_zero_of_not_mem A n V S k hy)

/-- Failure of both the desired fixed proximity bound and the
small-initial-displacement alternative. -/
def IsMovementBadSquared
    (A : SoficApproximation G) (n : ℕ) (S : Finset G)
    (k : ℕ) (L' β : ℝ) (U : Finset (A.model n)) : Prop :=
  L' ^ 2 * ‖indicatorDisplacement A n U S 0‖ ^ 2 ≤
      ‖trajectoryMovement A n U S k‖ ^ 2 ∧
    β ^ 2 * (U.card : ℝ) ≤ ‖indicatorDisplacement A n U S 0‖ ^ 2

@[simp] theorem isMovementBadSquared_empty
    (A : SoficApproximation G) (n : ℕ) (S : Finset G)
    (k : ℕ) (L' β : ℝ) :
    IsMovementBadSquared A n S k L' β ∅ := by
  simp [IsMovementBadSquared]

/-- A maximum-cardinality movement-bad set exists in each finite model. -/
theorem exists_maximalMovementBadSquared
    (A : SoficApproximation G) (n : ℕ) (S : Finset G)
    (k : ℕ) (L' β : ℝ) :
    ∃ B : Finset (A.model n), IsMovementBadSquared A n S k L' β B ∧
      ∀ U : Finset (A.model n), IsMovementBadSquared A n S k L' β U →
        U.card ≤ B.card := by
  classical
  let candidates := (Finset.univ : Finset (A.model n)).powerset.filter
    (IsMovementBadSquared A n S k L' β)
  have hcandidates : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates]
  let sizes := candidates.image Finset.card
  have hsizes : sizes.Nonempty := hcandidates.image Finset.card
  let m := sizes.max' hsizes
  have hm : m ∈ sizes := Finset.max'_mem sizes hsizes
  obtain ⟨B, hBcandidates, hBcard⟩ := Finset.mem_image.mp hm
  refine ⟨B, (Finset.mem_filter.mp hBcandidates).2, fun U hU ↦ ?_⟩
  have hUcandidate : U ∈ candidates := Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.subset_univ U), hU⟩
  have hUsize : U.card ∈ sizes :=
    Finset.mem_image.mpr ⟨U, hUcandidate, rfl⟩
  rw [hBcard]
  exact Finset.le_max' sizes U.card hUsize

/-- Movement badness is additive across sets separated beyond the whole
trajectory horizon. -/
theorem isMovementBadSquared_union
    (A : SoficApproximation G) (n : ℕ) (U V : Finset (A.model n))
    (S : Finset G) (k : ℕ) (L' β : ℝ)
    (hdisj : Disjoint
      (forwardNeighborhood (A.model n) (A.map n) S (k + 1) U)
      (forwardNeighborhood (A.model n) (A.map n) S (k + 1) V))
    (hU : IsMovementBadSquared A n S k L' β U)
    (hV : IsMovementBadSquared A n S k L' β V) :
    IsMovementBadSquared A n S k L' β (U ∪ V) := by
  have hUV : Disjoint U V := by
    rw [Finset.disjoint_left] at hdisj ⊢
    intro y hyU hyV
    exact hdisj
      (forwardNeighborhood_mono_time (A.model n) (A.map n) S
        (Nat.zero_le _) U (by simpa [forwardNeighborhood] using hyU))
      (forwardNeighborhood_mono_time (A.model n) (A.map n) S
        (Nat.zero_le _) V (by simpa [forwardNeighborhood] using hyV))
  have hdisjK : Disjoint
      (forwardNeighborhood (A.model n) (A.map n) S k U)
      (forwardNeighborhood (A.model n) (A.map n) S k V) := by
    rw [Finset.disjoint_left] at hdisj ⊢
    intro y hyU hyV
    exact hdisj
      (forwardNeighborhood_mono_time (A.model n) (A.map n) S
        (Nat.le_succ k) U hyU)
      (forwardNeighborhood_mono_time (A.model n) (A.map n) S
        (Nat.le_succ k) V hyV)
  have hmove := norm_trajectoryMovement_union_sq A n U V S k hdisjK
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
  · rw [hzero, hmove]
    nlinarith [hU.1, hV.1]
  · rw [hzero, Finset.card_union_of_disjoint hUV]
    push_cast
    nlinarith [hU.2, hV.2]

/-- The global additive movement estimate bounds every squared-bad set. -/
theorem movementBadSquared_card_bound
    (A : SoficApproximation G) (n : ℕ) (U : Finset (A.model n))
    (S : Finset G) (k : ℕ) (L L' β δ : ℝ)
    (hL0 : 0 ≤ L) (hLL' : L < L') (hδ : 0 ≤ δ)
    (hbad : IsMovementBadSquared A n S k L' β U)
    (hmove : ‖trajectoryMovement A n U S k‖ <
      L * ‖indicatorDisplacement A n U S 0‖ +
        δ * Real.sqrt (Fintype.card (A.model n) : ℝ)) :
    β ^ 2 * (L' - L) ^ 2 * (U.card : ℝ) ≤
      δ ^ 2 * Fintype.card (A.model n) := by
  let x := ‖indicatorDisplacement A n U S 0‖
  let y := ‖trajectoryMovement A n U S k‖
  let R := Real.sqrt (Fintype.card (A.model n) : ℝ)
  have hL'0 : 0 ≤ L' := hL0.trans hLL'.le
  have hLx0 : 0 ≤ L' * x := mul_nonneg hL'0 (norm_nonneg _)
  have hy0 : 0 ≤ y := norm_nonneg _
  have hLxSq : (L' * x) ^ 2 ≤ y ^ 2 := by
    calc
      (L' * x) ^ 2 = L' ^ 2 * x ^ 2 := by ring
      _ ≤ y ^ 2 := by simpa [x, y] using hbad.1
  have hLx : L' * x ≤ y := (sq_le_sq₀ hLx0 hy0).mp hLxSq
  have hgap0 : 0 ≤ (L' - L) * x :=
    mul_nonneg (sub_nonneg.mpr hLL'.le) (norm_nonneg _)
  have hright0 : 0 ≤ δ * R := mul_nonneg hδ (Real.sqrt_nonneg _)
  have hgap : (L' - L) * x < δ * R := by
    dsimp [x, y, R] at hLx ⊢
    linarith
  have hgapSq : ((L' - L) * x) ^ 2 ≤ (δ * R) ^ 2 :=
    ((sq_lt_sq₀ hgap0 hright0).2 hgap).le
  have hscaledBad :
      (L' - L) ^ 2 * (β ^ 2 * (U.card : ℝ)) ≤
        (L' - L) ^ 2 * x ^ 2 := by
    apply mul_le_mul_of_nonneg_left
    · simpa [x] using hbad.2
    · positivity
  have hRsq : R ^ 2 = (Fintype.card (A.model n) : ℝ) := by
    dsimp [R]
    exact Real.sq_sqrt (by positivity)
  calc
    β ^ 2 * (L' - L) ^ 2 * (U.card : ℝ) =
        (L' - L) ^ 2 * (β ^ 2 * (U.card : ℝ)) := by ring
    _ ≤ (L' - L) ^ 2 * x ^ 2 := hscaledBad
    _ = ((L' - L) * x) ^ 2 := by ring
    _ ≤ (δ * R) ^ 2 := hgapSq
    _ = δ ^ 2 * Fintype.card (A.model n) := by rw [mul_pow, hRsq]

/-- Maximal removal for the fixed proximity bound. -/
theorem exists_uniformMovementRemoval
    (A : SoficApproximation G) (n : ℕ) (S : Finset G)
    (k : ℕ) (L L' β δ : ℝ)
    (hL0 : 0 ≤ L) (hLL' : L < L') (hβ : 0 < β) (hδ : 0 ≤ δ)
    (hmove : ∀ U : Finset (A.model n),
      ‖trajectoryMovement A n U S k‖ <
        L * ‖indicatorDisplacement A n U S 0‖ +
          δ * Real.sqrt (Fintype.card (A.model n) : ℝ)) :
    ∃ B : Finset (A.model n),
      β ^ 2 * (L' - L) ^ 2 * (B.card : ℝ) ≤
        ((S.card + 1) ^ (2 * (k + 1)) : ℕ) *
          (δ ^ 2 * Fintype.card (A.model n) : ℝ) ∧
      ∀ U : Finset (A.model n), U.Nonempty → Disjoint U B →
        ‖indicatorDisplacement A n U S 0‖ < β * ‖indicator U‖ ∨
          ‖trajectoryMovement A n U S k‖ <
            L' * ‖indicatorDisplacement A n U S 0‖ := by
  classical
  obtain ⟨B', hB'bad, hB'max⟩ :=
    exists_maximalMovementBadSquared A n S k L' β
  let B := backwardNeighborhood (A.model n) (A.map n) S (k + 1)
    (forwardNeighborhood (A.model n) (A.map n) S (k + 1) B')
  have hB'bound := movementBadSquared_card_bound A n B' S k L L' β δ
    hL0 hLL' hδ hB'bad (hmove B')
  have hBcardNat : B.card ≤
      (S.card + 1) ^ (2 * (k + 1)) * B'.card := by
    simpa [B] using card_backwardForwardNeighborhood_le
      (A.model n) (A.map n) S (k + 1) B'
  have hBcard : (B.card : ℝ) ≤
      ((S.card + 1) ^ (2 * (k + 1)) : ℕ) * (B'.card : ℝ) := by
    exact_mod_cast hBcardNat
  have hcoeff : 0 ≤ β ^ 2 * (L' - L) ^ 2 := by positivity
  refine ⟨B, ?_, ?_⟩
  · calc
      β ^ 2 * (L' - L) ^ 2 * (B.card : ℝ) ≤
          β ^ 2 * (L' - L) ^ 2 *
            (((S.card + 1) ^ (2 * (k + 1)) : ℕ) * (B'.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hBcard hcoeff
      _ = ((S.card + 1) ^ (2 * (k + 1)) : ℕ) *
          (β ^ 2 * (L' - L) ^ 2 * (B'.card : ℝ)) := by ring
      _ ≤ ((S.card + 1) ^ (2 * (k + 1)) : ℕ) *
          (δ ^ 2 * Fintype.card (A.model n) : ℝ) := by gcongr
  · intro U hU hUB
    have hnotBad : ¬ IsMovementBadSquared A n S k L' β U := by
      intro hUbad
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
      have hunionBad := isMovementBadSquared_union A n B' U S k L' β
        hseparated hB'bad hUbad
      have hmax := hB'max (B' ∪ U) hunionBad
      rw [Finset.card_union_of_disjoint hB'U] at hmax
      exact hU.ne_empty (Finset.card_eq_zero.mp (by omega))
    by_cases hfar : L' ^ 2 * ‖indicatorDisplacement A n U S 0‖ ^ 2 ≤
        ‖trajectoryMovement A n U S k‖ ^ 2
    · left
      have hsmallSq : ‖indicatorDisplacement A n U S 0‖ ^ 2 <
          β ^ 2 * (U.card : ℝ) :=
        lt_of_not_ge fun hge ↦ hnotBad ⟨hfar, hge⟩
      have hsquare : ‖indicatorDisplacement A n U S 0‖ ^ 2 <
          (β * ‖indicator U‖) ^ 2 := by
        rw [mul_pow, norm_indicator_sq]
        exact hsmallSq
      exact (sq_lt_sq₀ (norm_nonneg _)
        (mul_nonneg hβ.le (norm_nonneg _))).mp hsquare
    · right
      have hL'0 : 0 ≤ L' := hL0.trans hLL'.le
      have hsquare : ‖trajectoryMovement A n U S k‖ ^ 2 <
          (L' * ‖indicatorDisplacement A n U S 0‖) ^ 2 := by
        rw [mul_pow]
        exact lt_of_not_ge hfar
      exact (sq_lt_sq₀ (norm_nonneg _)
        (mul_nonneg hL'0 (norm_nonneg _))).mp hsquare

end KunUniformRemoval
end NonsoficGroupsExist
