import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# A quantitative gap for positive Hilbert-space operators

This file proves the elementary Neumann-iteration lemma used for the
compressed A₂ graph Laplacian.  It is formulated over real Hilbert spaces,
so it does not rely on a complex spectral theorem.
-/

namespace NonsoficGroupsExist

universe u

namespace PositiveOperatorGap

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The real quadratic form of an operator. -/
def energy (A : E →L[ℝ] E) (x : E) : ℝ := inner ℝ x (A x)

/-- One damped Richardson step for `A`. -/
noncomputable def relax (A : E →L[ℝ] E) (M : ℝ) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - M⁻¹ • A

@[simp] theorem relax_apply (A : E →L[ℝ] E) (M : ℝ) (x : E) :
    relax A M x = x - M⁻¹ • A x := rfl

/-- If `c A ≤ A²` and the quadratic form of `A` is bounded above by
`M`, one Richardson step contracts the `A`-energy by `1-c/M`. -/
theorem energy_relax_le
    (A : E →L[ℝ] E) {c M : ℝ} (hM : 0 < M)
    (hsymm : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y))
    (hlower : ∀ x, c * energy A x ≤ ‖A x‖ ^ 2)
    (hformUpper : ∀ x, energy A x ≤ M * ‖x‖ ^ 2)
    (x : E) :
    energy A (relax A M x) ≤ (1 - c / M) * energy A x := by
  have hM0 : M ≠ 0 := ne_of_gt hM
  have hcross : inner ℝ x (A (A x)) = ‖A x‖ ^ 2 := by
    rw [← hsymm x (A x), real_inner_self_eq_norm_sq]
  have hthird : energy A (A x) ≤ M * ‖A x‖ ^ 2 := hformUpper (A x)
  have hexpand :
      energy A (relax A M x) =
        energy A x - 2 * M⁻¹ * ‖A x‖ ^ 2 + (M⁻¹) ^ 2 * energy A (A x) := by
    simp only [energy, relax_apply, map_sub, map_smul, inner_sub_left,
      inner_sub_right, inner_smul_left, inner_smul_right]
    rw [hsymm x (A x), hcross]
    norm_num
    ring
  rw [hexpand]
  have hinvM : M⁻¹ * energy A (A x) ≤ ‖A x‖ ^ 2 := by
    calc
      M⁻¹ * energy A (A x) ≤ M⁻¹ * (M * ‖A x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hthird (inv_nonneg.mpr hM.le)
      _ = ‖A x‖ ^ 2 := by field_simp
  have hscaled : c * M⁻¹ * energy A x ≤ M⁻¹ * ‖A x‖ ^ 2 := by
    calc
      c * M⁻¹ * energy A x = M⁻¹ * (c * energy A x) := by ring
      _ ≤ M⁻¹ * ‖A x‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (hlower x) (inv_nonneg.mpr hM.le)
  have hthirdScaled :
      (M⁻¹) ^ 2 * energy A (A x) ≤ M⁻¹ * ‖A x‖ ^ 2 := by
    calc
      (M⁻¹) ^ 2 * energy A (A x) = M⁻¹ * (M⁻¹ * energy A (A x)) := by
        ring
      _ ≤ M⁻¹ * ‖A x‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hinvM (inv_nonneg.mpr hM.le)
  rw [div_eq_mul_inv]
  calc
    energy A x - 2 * M⁻¹ * ‖A x‖ ^ 2 +
        (M⁻¹) ^ 2 * energy A (A x) ≤
        energy A x - M⁻¹ * ‖A x‖ ^ 2 := by linarith
    _ ≤ (1 - c * M⁻¹) * energy A x := by linarith

/-- Iterating the relaxed operator gives geometric decay of its quadratic
energy. -/
theorem energy_relax_pow_le
    (A : E →L[ℝ] E) {c M : ℝ} (hM : 0 < M) (hcM : c ≤ M)
    (hsymm : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y))
    (hlower : ∀ x, c * energy A x ≤ ‖A x‖ ^ 2)
    (hformUpper : ∀ x, energy A x ≤ M * ‖x‖ ^ 2)
    (x : E) (n : ℕ) :
    energy A (((relax A M) ^ n) x) ≤
      (1 - c / M) ^ n * energy A x := by
  have hr0 : 0 ≤ 1 - c / M := by
    rw [sub_nonneg, div_le_one hM]
    exact hcM
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ']
      change energy A (relax A M (((relax A M) ^ n) x)) ≤
        (1 - c / M) ^ (n + 1) * energy A x
      calc
        energy A (relax A M (((relax A M) ^ n) x)) ≤
            (1 - c / M) * energy A (((relax A M) ^ n) x) :=
          energy_relax_le A hM hsymm hlower hformUpper _
        _ ≤ (1 - c / M) *
            ((1 - c / M) ^ n * energy A x) :=
          mul_le_mul_of_nonneg_left ih hr0
        _ = (1 - c / M) ^ (n + 1) * energy A x := by ring

/-- A positive symmetric operator whose quadratic inequality excludes the
interval `(0,c)` and whose kernel is zero is bounded below.  The displayed
constant comes from the convergent Richardson/Neumann iteration. -/
theorem norm_le_of_quadratic_gap [CompleteSpace E]
    (A : E →L[ℝ] E) {c M : ℝ} (hc : 0 < c) (hM : 0 < M) (hcM : c ≤ M)
    (hsymm : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y))
    (henergy : ∀ x, 0 ≤ energy A x)
    (hlower : ∀ x, c * energy A x ≤ ‖A x‖ ^ 2)
    (hformUpper : ∀ x, energy A x ≤ M * ‖x‖ ^ 2)
    (hnormUpper : ∀ x, ‖A x‖ ^ 2 ≤ M * energy A x)
    (hker : ∀ x, A x = 0 → x = 0)
    (x : E) :
    ‖x‖ ≤ (c * (1 - Real.sqrt (1 - c / M)))⁻¹ * ‖A x‖ := by
  let r : ℝ := 1 - c / M
  let s : ℝ := Real.sqrt r
  let T : E →L[ℝ] E := relax A M
  let u : ℕ → E := fun n ↦ (T ^ n) x
  let d : ℕ → E := fun n ↦ u n - u (n + 1)
  have hr0 : 0 ≤ r := by
    dsimp [r]
    rw [sub_nonneg, div_le_one hM]
    exact hcM
  have hr1 : r < 1 := by
    dsimp [r]
    exact sub_lt_self _ (div_pos hc hM)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsSq : s ^ 2 = r := Real.sq_sqrt hr0
  have hs1 : s < 1 := by
    nlinarith [sq_nonneg (s - 1)]
  have henergyIter (n : ℕ) : energy A (u n) ≤ r ^ n * energy A x := by
    exact energy_relax_pow_le A hM hcM hsymm hlower hformUpper x n
  have henergyX : energy A x ≤ ‖A x‖ ^ 2 / c := by
    apply (le_div_iff₀ hc).2
    simpa [mul_comm] using hlower x
  have hratio1 : 1 ≤ M / c := by
    apply (le_div_iff₀ hc).2
    simpa using hcM
  have hratio0 : 0 ≤ M / c := le_trans zero_le_one hratio1
  have hspowSq (n : ℕ) : (s ^ n) ^ 2 = r ^ n := by
    rw [← pow_mul, mul_comm n 2, pow_mul, hsSq]
  have hAu (n : ℕ) :
      ‖A (u n)‖ ≤ (M / c) * s ^ n * ‖A x‖ := by
    have he0 : 0 ≤ energy A x := henergy x
    have hrpow0 : 0 ≤ r ^ n := pow_nonneg hr0 n
    have hsq : ‖A (u n)‖ ^ 2 ≤ (M / c) * r ^ n * ‖A x‖ ^ 2 := by
      calc
        ‖A (u n)‖ ^ 2 ≤ M * energy A (u n) := hnormUpper _
        _ ≤ M * (r ^ n * energy A x) :=
          mul_le_mul_of_nonneg_left (henergyIter n) hM.le
        _ ≤ M * (r ^ n * (‖A x‖ ^ 2 / c)) := by
          gcongr
        _ = (M / c) * r ^ n * ‖A x‖ ^ 2 := by ring
    have hcoef : (M / c) ≤ (M / c) ^ 2 := by nlinarith
    have hsquare :
        (M / c) * r ^ n * ‖A x‖ ^ 2 ≤
          ((M / c) * s ^ n * ‖A x‖) ^ 2 := by
      rw [mul_pow, mul_pow, hspowSq]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoef hrpow0) (sq_nonneg ‖A x‖)
    apply (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (mul_nonneg hratio0 (pow_nonneg hs0 n)) (norm_nonneg _))).mp
    exact hsq.trans hsquare
  have hdiff (n : ℕ) : d n = M⁻¹ • A (u n) := by
    dsimp [d, u]
    rw [pow_succ']
    change (T ^ n) x - T ((T ^ n) x) = M⁻¹ • A ((T ^ n) x)
    simp [T, relax]
  have hdNorm (n : ℕ) :
      ‖d n‖ ≤ (c⁻¹ * ‖A x‖) * s ^ n := by
    rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hM.le)]
    calc
      M⁻¹ * ‖A (u n)‖ ≤
          M⁻¹ * ((M / c) * s ^ n * ‖A x‖) :=
        mul_le_mul_of_nonneg_left (hAu n) (inv_nonneg.mpr hM.le)
      _ = (c⁻¹ * ‖A x‖) * s ^ n := by field_simp
  have hsNorm : ‖s‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs0]
    exact hs1
  have hgeom : Summable (fun n : ℕ ↦ s ^ n) :=
    summable_geometric_of_norm_lt_one hsNorm
  have hg : Summable (fun n : ℕ ↦ (c⁻¹ * ‖A x‖) * s ^ n) :=
    hgeom.mul_left _
  have hnormD : Summable (fun n ↦ ‖d n‖) :=
    hg.of_nonneg_of_le (fun n ↦ norm_nonneg _) hdNorm
  have hdSummable : Summable d := hnormD.of_norm
  let z : E := ∑' n, d n
  have hpartial : ∀ n : ℕ, ∑ i ∈ Finset.range n, d i = x - u n := by
    intro n
    induction n with
    | zero => simp [u]
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        dsimp [d]
        abel
  have hsumTendsto : Filter.Tendsto
      (fun n ↦ ∑ i ∈ Finset.range n, d i) Filter.atTop (nhds z) := by
    exact hdSummable.hasSum.tendsto_sum_nat
  have huTendsto : Filter.Tendsto u Filter.atTop (nhds (x - z)) := by
    have h := hsumTendsto.const_sub x
    simpa only [hpartial, sub_sub_cancel] using h
  have hAuTendstoZero : Filter.Tendsto (fun n ↦ A (u n)) Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hright : Filter.Tendsto
        (fun n ↦ (M / c) * s ^ n * ‖A x‖) Filter.atTop (nhds 0) := by
      have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hs0 hs1
      simpa using (hp.const_mul (M / c)).mul_const ‖A x‖
    exact squeeze_zero' (Filter.Eventually.of_forall fun n ↦ norm_nonneg _)
      (Filter.Eventually.of_forall hAu) hright
  have hAlimit : Filter.Tendsto (fun n ↦ A (u n)) Filter.atTop
      (nhds (A (x - z))) := A.continuous.tendsto (x - z) |>.comp huTendsto
  have hAz : A (x - z) = 0 := tendsto_nhds_unique hAlimit hAuTendstoZero
  have hxz : x - z = 0 := hker _ hAz
  have hzx : z = x := sub_eq_zero.mp hxz |>.symm
  have hnormZ : ‖z‖ ≤ ∑' n, ‖d n‖ := norm_tsum_le_tsum_norm hnormD
  have hnormTsum : (∑' n, ‖d n‖) ≤
      ∑' n, (c⁻¹ * ‖A x‖) * s ^ n :=
    hnormD.tsum_le_tsum hdNorm hg
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hsNorm] at hnormTsum
  rw [hzx] at hnormZ
  calc
    ‖x‖ ≤ (c⁻¹ * ‖A x‖) * (1 - s)⁻¹ := hnormZ.trans hnormTsum
    _ = (c * (1 - Real.sqrt (1 - c / M)))⁻¹ * ‖A x‖ := by
      dsimp [s, r]
      field_simp

end PositiveOperatorGap
end NonsoficGroupsExist
