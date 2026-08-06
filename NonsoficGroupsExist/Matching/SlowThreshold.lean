import NonsoficGroupsExist.Matching.Selection

/-!
# A slowly vanishing threshold

Given a nonnegative error density `rₙ → 0`, the matching proof needs a
threshold `ηₙ → 0` for which `rₙ / ηₙ → 0`.  The construction below is
the diagonal device used implicitly in the manuscript.  It avoids square roots
and all filter-level asymptotics.
-/

namespace NonsoficGroupsExist

/-- A level growing slowly enough that the cubically rescaled error still
vanishes along the diagonal. -/
noncomputable def slowLevel (r : ℕ → ℝ) (n : ℕ) : ℕ :=
  diagonalLevel (fun n k ↦ ((k : ℝ) + 1) ^ 3 * r n) n

/-- The associated positive threshold. -/
noncomputable def slowThreshold (r : ℕ → ℝ) (n : ℕ) : ℝ :=
  1 / ((slowLevel r n : ℝ) + 1)

theorem slowThreshold_pos (r : ℕ → ℝ) (n : ℕ) :
    0 < slowThreshold r n := by
  unfold slowThreshold
  positivity

theorem slowLevel_diverges (r : ℕ → ℝ) (hr : Vanishing r) :
    ∀ k : ℕ, ∃ N : ℕ, ∀ n, N ≤ n → k ≤ slowLevel r n := by
  apply diagonalLevel_diverges
  intro k
  exact Vanishing.const_mul (((k : ℝ) + 1) ^ 3) hr

theorem slowThreshold_vanishing (r : ℕ → ℝ) (hr : Vanishing r) :
    Vanishing (slowThreshold r) := by
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := slowLevel_diverges r hr k
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [abs_of_pos (slowThreshold_pos r n)]
  calc
    slowThreshold r n ≤ 1 / ((k : ℝ) + 1) := by
      unfold slowThreshold
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.add_le_add_right (hN n hn) 1
    _ < ε := by simpa using hk

theorem error_div_slowThreshold_vanishing (r : ℕ → ℝ)
    (hrnonneg : ∀ n, 0 ≤ r n) (hr : Vanishing r) :
    Vanishing fun n ↦ r n / slowThreshold r n := by
  let e : ℕ → ℕ → ℝ := fun n k ↦ ((k : ℝ) + 1) ^ 3 * r n
  have henonneg : ∀ n k, 0 ≤ e n k := by
    intro n k
    exact mul_nonneg (by positivity) (hrnonneg n)
  have hev : ∀ k, Vanishing fun n ↦ e n k := by
    intro k
    exact Vanishing.const_mul (((k : ℝ) + 1) ^ 3) hr
  have hdiag := diagonalLevel_error e henonneg hev
  refine Vanishing.squeeze (b := fun n ↦ e n (diagonalLevel e n))
    (fun n ↦ div_nonneg (hrnonneg n) (slowThreshold_pos r n).le)
    (fun n ↦ ?_) ?_
  · let a : ℝ := (slowLevel r n : ℝ) + 1
    have ha : 1 ≤ a := by
      dsimp only [a]
      have hlevel : (0 : ℝ) ≤ slowLevel r n := by positivity
      linarith
    have hcube : a ≤ a ^ 3 := by nlinarith [sq_nonneg a]
    calc
      r n / slowThreshold r n = a * r n := by
        dsimp only [slowThreshold, a]
        field_simp
      _ ≤ a ^ 3 * r n := mul_le_mul_of_nonneg_right hcube (hrnonneg n)
      _ = e n (diagonalLevel e n) := by
        simp only [e, slowLevel, a]
  · simpa [e, slowLevel] using hdiag

end NonsoficGroupsExist
