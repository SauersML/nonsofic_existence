import Mathlib.Analysis.SpecificLimits.Normed
import NonsoficGroupsExist.KunThomRounding

/-!
# Numerical parameters for the Kun--Thom improvement

The finite relation-improvement theorem has two competing costs: `k` Markov
steps move the input relation by a polynomial factor in `k`, while the
Kazhdan displacement contracts exponentially.  This module proves that the
required defect, boundary, and repair parameters genuinely exist.  No
numerical premise is left for a caller to supply.
-/

namespace NonsoficGroupsExist
namespace KunThomParameters

open Filter
open scoped Topology

/-- Exponential Kazhdan contraction beats the quadratic threshold-movement
cost.  The resulting parameters simultaneously satisfy the cluster
separation, Hamming-closeness, repair-boundary, and coarea inequalities used
by the finite Kun--Thom argument. -/
theorem exists_improvementParameters
    {q h : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hh : 0 < h)
    (s : ℕ) (hs : 0 < s) :
    ∃ (k : ℕ) (η δ β : ℝ),
      0 < k ∧ 0 < η ∧ 0 < δ ∧ 0 < β ∧
      20 * η < h ∧
      108 * (k : ℝ) ^ 2 * (s : ℝ)⁻¹ * η < (1 : ℝ) / 10 ∧
      (h + 7 * (s : ℝ)) * β < h * η ∧
      16 * (s : ℝ) ^ 4 * (16 * q ^ (2 * k) * (s : ℝ)⁻¹ * η + δ) <
        (((1 : ℝ) / 3) * (((2 : ℝ) / 3) - (1 : ℝ) / 3) ^ 2) ^ 2 *
          β ^ 4 := by
  let r : ℝ := (q + 1) / 2
  have hr0 : 0 < r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hqr : q ≤ r := by dsimp [r]; linarith
  have hsReal : (0 : ℝ) < s := by exact_mod_cast hs
  let p : ℝ := h / (2 * (h + 7 * (s : ℝ)))
  have hden : 0 < h + 7 * (s : ℝ) := by positivity
  have hp : 0 < p := by dsimp [p]; positivity
  let coarea : ℝ :=
    ((1 : ℝ) / 3) * (((2 : ℝ) / 3) - (1 : ℝ) / 3) ^ 2
  have hcoarea : 0 < coarea := by dsimp [coarea]; norm_num
  let C : ℝ :=
    16 * (s : ℝ) ^ 4 * (16 * (s : ℝ)⁻¹ + 1)
  let D : ℝ := coarea ^ 2 * p ^ 4
  have hC : 0 < C := by dsimp [C]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hrpow : Tendsto (fun m : ℕ ↦ r ^ m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1
  have hrpoly : Tendsto (fun m : ℕ ↦ (m : ℝ) ^ 2 * r ^ m) atTop (𝓝 0) :=
    tendsto_pow_const_mul_const_pow_of_lt_one 2 hr0.le hr1
  have heventEta : ∀ᶠ m : ℕ in atTop, r ^ m < h / 20 :=
    (tendsto_order.1 hrpow).2 _ (div_pos hh (by norm_num))
  have heventClose : ∀ᶠ m : ℕ in atTop,
      (m : ℝ) ^ 2 * r ^ m < (s : ℝ) / 4320 :=
    (tendsto_order.1 hrpoly).2 _ (div_pos hsReal (by norm_num))
  have heventNumerical : ∀ᶠ m : ℕ in atTop, r ^ m < D / C :=
    (tendsto_order.1 hrpow).2 _ (div_pos hD hC)
  have heventPositive : ∀ᶠ m : ℕ in atTop, 1 ≤ m := eventually_ge_atTop 1
  have hall : ∀ᶠ m : ℕ in atTop,
      1 ≤ m ∧ r ^ m < h / 20 ∧
        (m : ℝ) ^ 2 * r ^ m < (s : ℝ) / 4320 ∧
        r ^ m < D / C := by
    filter_upwards [heventPositive, heventEta, heventClose, heventNumerical]
      with m hm hη hclose hnum
    exact ⟨hm, hη, hclose, hnum⟩
  obtain ⟨m, hm, hηsmall, hclose, hnum⟩ := hall.exists
  let k : ℕ := 2 * m
  let η : ℝ := r ^ m
  let δ : ℝ := r ^ (5 * m)
  let β : ℝ := p * r ^ m
  have hk : 0 < k := by dsimp [k]; omega
  have hη : 0 < η := by dsimp [η]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hβ : 0 < β := by dsimp [β]; positivity
  refine ⟨k, η, δ, β, hk, hη, hδ, hβ, ?_, ?_, ?_, ?_⟩
  · dsimp [η]
    nlinarith
  · have hcloseScaled :
        432 * ((m : ℝ) ^ 2 * r ^ m) / (s : ℝ) < (1 : ℝ) / 10 := by
      calc
        432 * ((m : ℝ) ^ 2 * r ^ m) / (s : ℝ) <
            432 * ((s : ℝ) / 4320) / (s : ℝ) := by
          apply div_lt_div_of_pos_right _ hsReal
          exact mul_lt_mul_of_pos_left hclose (by norm_num)
        _ = (1 : ℝ) / 10 := by field_simp; ring
    dsimp [k, η]
    calc
      108 * (↑(2 * m) : ℝ) ^ 2 * (s : ℝ)⁻¹ * r ^ m =
          432 * ((m : ℝ) ^ 2 * r ^ m) / (s : ℝ) := by
        norm_num [Nat.cast_mul, div_eq_mul_inv]
        ring
      _ < (1 : ℝ) / 10 := hcloseScaled
  · dsimp [β, η, p]
    have hdenne : h + 7 * (s : ℝ) ≠ 0 := ne_of_gt hden
    field_simp [hdenne]
    nlinarith
  · have hqpow : q ^ (4 * m) ≤ r ^ (4 * m) := by
      gcongr
    have hqterm : q ^ (4 * m) * r ^ m ≤ r ^ (5 * m) := by
      calc
        q ^ (4 * m) * r ^ m ≤ r ^ (4 * m) * r ^ m :=
          mul_le_mul_of_nonneg_right hqpow (pow_nonneg hr0.le _)
        _ = r ^ (5 * m) := by
          rw [← pow_add]
          congr 1
          omega
    have hinv : 0 ≤ (s : ℝ)⁻¹ := inv_nonneg.mpr hsReal.le
    have hinner :
        16 * q ^ (4 * m) * (s : ℝ)⁻¹ * r ^ m + r ^ (5 * m) ≤
          (16 * (s : ℝ)⁻¹ + 1) * r ^ (5 * m) := by
      have hscaled :
          (16 * (s : ℝ)⁻¹) * (q ^ (4 * m) * r ^ m) ≤
            (16 * (s : ℝ)⁻¹) * r ^ (5 * m) :=
        mul_le_mul_of_nonneg_left hqterm
          (mul_nonneg (by norm_num) hinv)
      calc
        16 * q ^ (4 * m) * (s : ℝ)⁻¹ * r ^ m + r ^ (5 * m) =
            (16 * (s : ℝ)⁻¹) * (q ^ (4 * m) * r ^ m) +
              r ^ (5 * m) := by ring
        _ ≤ (16 * (s : ℝ)⁻¹) * r ^ (5 * m) + r ^ (5 * m) :=
          by simpa [add_comm] using add_le_add_right hscaled (r ^ (5 * m))
        _ = (16 * (s : ℝ)⁻¹ + 1) * r ^ (5 * m) := by ring
    have hleft :
        16 * (s : ℝ) ^ 4 *
            (16 * q ^ (4 * m) * (s : ℝ)⁻¹ * r ^ m + r ^ (5 * m)) ≤
          C * r ^ (5 * m) := by
      have hout0 : 0 ≤ 16 * (s : ℝ) ^ 4 :=
        mul_nonneg (by norm_num) (pow_nonneg hsReal.le 4)
      have hscaled := mul_le_mul_of_nonneg_left hinner hout0
      simpa [C, mul_assoc] using hscaled
    have hCr : C * r ^ m < D := by
      rw [lt_div_iff₀ hC] at hnum
      simpa [mul_comm] using hnum
    have hmiddle : C * r ^ (5 * m) < D * r ^ (4 * m) := by
      have hmul := mul_lt_mul_of_pos_right hCr (pow_pos hr0 (4 * m))
      calc
        C * r ^ (5 * m) = (C * r ^ m) * r ^ (4 * m) := by
          rw [show 5 * m = m + 4 * m by omega, pow_add]
          ring
        _ < D * r ^ (4 * m) := hmul
    calc
      16 * (s : ℝ) ^ 4 *
          (16 * q ^ (2 * k) * (s : ℝ)⁻¹ * η + δ) =
        16 * (s : ℝ) ^ 4 *
          (16 * q ^ (4 * m) * (s : ℝ)⁻¹ * r ^ m + r ^ (5 * m)) := by
            have hexp : 2 * k = 4 * m := by dsimp [k]; omega
            dsimp [η, δ]
            rw [hexp]
      _ ≤ C * r ^ (5 * m) := hleft
      _ < D * r ^ (4 * m) := hmiddle
      _ = coarea ^ 2 * β ^ 4 := by
        dsimp [D, β]
        rw [mul_pow]
        ring
      _ = (((1 : ℝ) / 3) *
          (((2 : ℝ) / 3) - (1 : ℝ) / 3) ^ 2) ^ 2 * β ^ 4 := by
        rfl

end KunThomParameters
end NonsoficGroupsExist
