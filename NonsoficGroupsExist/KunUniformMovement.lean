import NonsoficGroupsExist.KunRounding
import NonsoficGroupsExist.KunFiniteMarkov

/-!
# Uniform movement bounds for long Markov trajectories

The crude `k`-fold telescoping estimate makes the admissible input cut depend
on the requested output boundary.  Kun's fixed cut threshold instead uses the
geometric Kazhdan decay of every consecutive displacement.  The total motion
of an arbitrarily long, fixed trajectory is therefore bounded by one constant
depending only on the Kazhdan pair, plus an arbitrarily small finite-model
error.
-/

namespace NonsoficGroupsExist
namespace KunUniformMovement

open KazhdanFiniteModel
open KazhdanGNS
open KunRounding
open scoped BigOperators

variable {G : Type} [Group G]

omit [Group G] in
/-- A finite geometric sum is bounded by the infinite sum, proved directly so
the exact normalization used below is visible. -/
theorem sum_pow_le_inv_one_sub {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (k : ℕ) :
    ∑ i ∈ Finset.range k, q ^ i ≤ (1 - q)⁻¹ := by
  have hden : 0 < 1 - q := sub_pos.mpr hq1
  have hid : (1 - q) * (∑ i ∈ Finset.range k, q ^ i) = 1 - q ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Finset.sum_range_succ]
        rw [mul_add, ih]
        ring
  rw [inv_eq_one_div, le_div_iff₀ hden]
  nlinarith [pow_nonneg hq0 k]

/-- The finite-model Kazhdan estimate holds simultaneously at every time
strictly below one prescribed horizon. -/
theorem all_displacements_eventually
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{0, 0} G Q ε)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S) (hεone : ε ≤ 1)
    (A : SoficApproximation G) (k : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ U : Finset (A.model n), ∀ i < k,
      finiteModelAveragingDisplacementNormSq A n U S i <
        4 * (1 - ε ^ 2 / (4 * S.card)) ^ (2 * i) *
          finiteModelAveragingDisplacementNormSq A n U S 0 + η := by
  induction k with
  | zero =>
      exact ⟨0, by omega⟩
  | succ k ih =>
      obtain ⟨Nprev, hNprev⟩ := ih
      obtain ⟨Nlast, hNlast⟩ :=
        finiteModelAveragingDisplacementNormSq_eventually_lt
          hQ S hQS hone hεone A k η hη
      refine ⟨max Nprev Nlast, fun n hn U i hi ↦ ?_⟩
      by_cases hik : i = k
      · subst i
        exact hNlast n ((le_max_right _ _).trans hn) U
      · exact hNprev n ((le_max_left _ _).trans hn) U i (by omega)

omit [Group G] in
/-- Taking square roots of the normalized displacement estimate. -/
theorem norm_lt_of_normalized_sq_lt
    {d d₀ r η N : ℝ} (hN : 0 < N) (hr : 0 ≤ r) (hη : 0 ≤ η)
    (hd : 0 ≤ d) (hd₀ : 0 ≤ d₀)
    (h : d ^ 2 / N < 4 * r ^ 2 * (d₀ ^ 2 / N) + η ^ 2) :
    d < 2 * r * d₀ + η * Real.sqrt N := by
  have hsqrt : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN.le
  have hmul := (div_lt_iff₀ hN).mp h
  have hsq : d ^ 2 < (2 * r * d₀) ^ 2 + (η * Real.sqrt N) ^ 2 := by
    field_simp [hN.ne'] at hmul
    nlinarith
  have hright : 0 ≤ 2 * r * d₀ + η * Real.sqrt N := by positivity
  apply (sq_lt_sq₀ hd hright).mp
  have hcross : 0 ≤ 4 * r * d₀ * η * Real.sqrt N := by positivity
  nlinarith

/-- Uniform-in-time coefficient for the total Markov motion. -/
noncomputable def movementConstant (S : Finset G) (ε : ℝ) : ℝ :=
  2 * (ε ^ 2 / (4 * S.card))⁻¹

theorem movementConstant_pos
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{0, 0} G Q ε)
    (S : Finset G) (hone : 1 ∈ S) :
    0 < movementConstant S ε := by
  have hScard : (0 : ℝ) < S.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, hone⟩
  have hε : 0 < ε := hQ.1
  unfold movementConstant
  positivity

/-- Long genuine finite-model trajectories move by a fixed multiple of their
initial displacement, independent of the horizon `k`, plus an arbitrarily
small normalized error. -/
theorem finiteModelIndicatorIterate_movement_eventually_lt
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{0, 0} G Q ε)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S) (hεone : ε ≤ 1)
    (A : SoficApproximation G) (k : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ U : Finset (A.model n),
      ‖finiteModelIndicatorIterate A n U S k - indicator U‖ <
        movementConstant S ε *
            ‖finiteModelIndicatorIterate A n U S 1 -
              finiteModelIndicatorIterate A n U S 0‖ +
          δ * Real.sqrt (Fintype.card (A.model n) : ℝ) := by
  have hS : S.Nonempty := ⟨1, hone⟩
  obtain ⟨hq0, hq1⟩ := kazhdanFactor_nonneg_lt_one hQ S hone hεone
  let q : ℝ := 1 - ε ^ 2 / (4 * S.card)
  let η : ℝ := δ / (k + 1)
  have hη : 0 < η := by positivity
  obtain ⟨Ndisp, hNdisp⟩ := all_displacements_eventually
    hQ S hQS hone hεone A k (η ^ 2) (sq_pos_of_pos hη)
  obtain ⟨Ncard, hNcard⟩ := A.card_tendsToInfinity 1
  refine ⟨max Ndisp Ncard, fun n hn U ↦ ?_⟩
  have hndisp : Ndisp ≤ n := (le_max_left _ _).trans hn
  have hncard : Ncard ≤ n := (le_max_right _ _).trans hn
  have hcardNat : 0 < Fintype.card (A.model n) :=
    Nat.zero_lt_of_lt (hNcard n hncard)
  have hcard : (0 : ℝ) < Fintype.card (A.model n) := by exact_mod_cast hcardNat
  let d₀ := ‖finiteModelIndicatorIterate A n U S 1 -
    finiteModelIndicatorIterate A n U S 0‖
  have hstep (i : ℕ) (hi : i < k) :
      ‖finiteModelIndicatorIterate A n U S (i + 1) -
          finiteModelIndicatorIterate A n U S i‖ <
        2 * q ^ i * d₀ + η * Real.sqrt (Fintype.card (A.model n) : ℝ) := by
    have hsquared := hNdisp n hndisp U i hi
    have hsquared' :
        ‖finiteModelIndicatorIterate A n U S (i + 1) -
            finiteModelIndicatorIterate A n U S i‖ ^ 2 /
              Fintype.card (A.model n) <
          4 * (q ^ i) ^ 2 * (d₀ ^ 2 / Fintype.card (A.model n)) + η ^ 2 := by
      simpa [q, d₀, finiteModelAveragingDisplacementNormSq,
        finiteModelAverageIterate_displacement_eq_indicator A n U S hS,
        show q ^ (2 * i) = (q ^ i) ^ 2 by rw [show 2 * i = i * 2 by omega,
          pow_mul]] using hsquared
    exact norm_lt_of_normalized_sq_lt hcard (pow_nonneg hq0 i) hη.le
      (norm_nonneg _) (norm_nonneg _) hsquared'
  have hpath := norm_finiteModelIndicatorIterate_sub_le_sum A n U S k
  have hsumSteps :
      ∑ i ∈ Finset.range k,
          ‖finiteModelIndicatorIterate A n U S (i + 1) -
            finiteModelIndicatorIterate A n U S i‖ ≤
        ∑ i ∈ Finset.range k,
          (2 * q ^ i * d₀ + η * Real.sqrt (Fintype.card (A.model n) : ℝ)) := by
    exact Finset.sum_le_sum fun i hi ↦ (hstep i (Finset.mem_range.mp hi)).le
  have hgeom := sum_pow_le_inv_one_sub hq0 hq1 k
  have hηk : (k : ℝ) * η < δ := by
    dsimp [η]
    have hkden : (0 : ℝ) < k + 1 := by positivity
    rw [show (k : ℝ) * (δ / (k + 1)) = ((k : ℝ) * δ) / (k + 1) by ring]
    rw [div_lt_iff₀ hkden]
    nlinarith
  calc
    ‖finiteModelIndicatorIterate A n U S k - indicator U‖ ≤
        ∑ i ∈ Finset.range k,
          ‖finiteModelIndicatorIterate A n U S (i + 1) -
            finiteModelIndicatorIterate A n U S i‖ := hpath
    _ ≤ ∑ i ∈ Finset.range k,
          (2 * q ^ i * d₀ + η * Real.sqrt (Fintype.card (A.model n) : ℝ)) :=
      hsumSteps
    _ = 2 * (∑ i ∈ Finset.range k, q ^ i) * d₀ +
        (k : ℝ) * η * Real.sqrt (Fintype.card (A.model n) : ℝ) := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [Finset.mul_sum, Finset.sum_mul]
      ring
    _ < movementConstant S ε * d₀ +
        δ * Real.sqrt (Fintype.card (A.model n) : ℝ) := by
      have hsqrt : 0 < Real.sqrt (Fintype.card (A.model n) : ℝ) :=
        Real.sqrt_pos.2 hcard
      have hd₀ : 0 ≤ d₀ := norm_nonneg _
      have hden : ε ^ 2 / (4 * (S.card : ℝ)) = 1 - q := by simp [q]
      unfold movementConstant
      rw [hden]
      nlinarith [mul_le_mul_of_nonneg_right hgeom hd₀,
        mul_lt_mul_of_pos_right hηk hsqrt]

end KunUniformMovement
end NonsoficGroupsExist
