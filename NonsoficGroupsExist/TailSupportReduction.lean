import NonsoficGroupsExist.BalancedRegularity
import NonsoficGroupsExist.LeavittGradingSpans

/-!
# Tail support reduction: tails restrict to the `p₁` corner

The exact product split
`(1 + s₁·z·p₀)·(1 + s₁·z·p₁) = 1 + s₁·z` — the cross term dies
because `p₀s₁ = 0` — together with the square-zero kill of the first
factor reduces every `s₁`-tail modulo the diagonal class group to one
right-supported on `p₁`.  Right multiplication by `p₀ = s₀t₀` selects
the balanced monomials whose `t`-word starts with `0`, so the pieces
stay in the balanced span.
-/

namespace NonsoficGroupsExist
namespace LeavittFamily

open MatrixDiagonalization

variable {A : Type*} [Ring A] (L : LeavittFamily A)

section SpanClosure

variable {k : Type*} [Field k] [Algebra k A]

/-- Right multiplication by `p₀` keeps the balanced span (it selects
monomials by the first letter of the `t`-word, padding depth by
one). -/
theorem mul_p0_mem_span {n : ℕ} {z : A}
    (hz : z ∈ Submodule.span k (L.levelMonomials n)) :
    z * (L.s 0 * L.t 0) ∈
      Submodule.span k (L.levelMonomials (n + 1)) := by
  have hz' : z ∈ Submodule.span k (L.levelMonomials (n + 1)) :=
    L.span_levelMonomials_mono (Nat.le_succ n) hz
  clear hz
  induction hz' using Submodule.span_induction with
  | mem x hxmem =>
      rw [levelMonomials_eq] at hxmem
      obtain ⟨a, b, ha, hb, rfl⟩ := hxmem
      -- b has length n+1 ≥ 1: split on its first letter
      match b, hb with
      | [], hb => exact absurd hb (by simp)
      | i :: b', hb =>
        by_cases hi : i = 0
        · subst hi
          have hsel : L.wordS a * L.wordT (0 :: b') *
              (L.s 0 * L.t 0) = L.wordS a * L.wordT (0 :: b') := by
            rw [L.wordT_cons]
            have h1 : L.t 0 * (L.s 0 * L.t 0) = L.t 0 := by
              rw [← mul_assoc, t_mul_s, if_pos rfl, one_mul]
            calc L.wordS a * (L.wordT b' * L.t 0) * (L.s 0 * L.t 0)
                = L.wordS a * (L.wordT b' *
                    (L.t 0 * (L.s 0 * L.t 0))) := by noncomm_ring
              _ = L.wordS a * (L.wordT b' * L.t 0) := by rw [h1]
          rw [hsel]
          exact Submodule.subset_span (by
            rw [levelMonomials_eq]
            exact ⟨a, 0 :: b', ha, hb, rfl⟩)
        · have hi1 : i = 1 := by omega
          subst hi1
          have hsel : L.wordS a * L.wordT (1 :: b') *
              (L.s 0 * L.t 0) = 0 := by
            rw [L.wordT_cons]
            have h1 : L.t 1 * L.s 0 = 0 := by
              rw [t_mul_s]; simp
            calc L.wordS a * (L.wordT b' * L.t 1) * (L.s 0 * L.t 0)
                = L.wordS a * L.wordT b' * (L.t 1 * L.s 0) * L.t 0 := by
                  noncomm_ring
              _ = 0 := by rw [h1]; noncomm_ring
          rw [hsel]
          exact Submodule.zero_mem _
  | zero =>
      rw [zero_mul]
      exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
      rw [add_mul]
      exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ r hx

/-- Right multiplication by `p₁` keeps the balanced span. -/
theorem mul_p1_mem_span {n : ℕ} {z : A}
    (hz : z ∈ Submodule.span k (L.levelMonomials n)) :
    z * (L.s 1 * L.t 1) ∈
      Submodule.span k (L.levelMonomials (n + 1)) := by
  have hz' : z ∈ Submodule.span k (L.levelMonomials (n + 1)) :=
    L.span_levelMonomials_mono (Nat.le_succ n) hz
  clear hz
  induction hz' using Submodule.span_induction with
  | mem x hxmem =>
      rw [levelMonomials_eq] at hxmem
      obtain ⟨a, b, ha, hb, rfl⟩ := hxmem
      match b, hb with
      | [], hb => exact absurd hb (by simp)
      | i :: b', hb =>
        by_cases hi : i = 1
        · subst hi
          have hsel : L.wordS a * L.wordT (1 :: b') *
              (L.s 1 * L.t 1) = L.wordS a * L.wordT (1 :: b') := by
            rw [L.wordT_cons]
            have h1 : L.t 1 * (L.s 1 * L.t 1) = L.t 1 := by
              rw [← mul_assoc, t_mul_s, if_pos rfl, one_mul]
            calc L.wordS a * (L.wordT b' * L.t 1) * (L.s 1 * L.t 1)
                = L.wordS a * (L.wordT b' *
                    (L.t 1 * (L.s 1 * L.t 1))) := by noncomm_ring
              _ = L.wordS a * (L.wordT b' * L.t 1) := by rw [h1]
          rw [hsel]
          exact Submodule.subset_span (by
            rw [levelMonomials_eq]
            exact ⟨a, 1 :: b', ha, hb, rfl⟩)
        · have hi0 : i = 0 := by omega
          subst hi0
          have hsel : L.wordS a * L.wordT (0 :: b') *
              (L.s 1 * L.t 1) = 0 := by
            rw [L.wordT_cons]
            have h1 : L.t 0 * L.s 1 = 0 := by
              rw [t_mul_s]; simp
            calc L.wordS a * (L.wordT b' * L.t 0) * (L.s 1 * L.t 1)
                = L.wordS a * L.wordT b' * (L.t 0 * L.s 1) * L.t 1 := by
                  noncomm_ring
              _ = 0 := by rw [h1]; noncomm_ring
          rw [hsel]
          exact Submodule.zero_mem _
  | zero =>
      rw [zero_mul]
      exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
      rw [add_mul]
      exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ r hx

end SpanClosure

section PSplit

variable {k : Type*} [Field k] [Algebra k A]

/-- **The exact `p`-split**: any unit of value `1 + s₁z` with `z`
balanced is congruent modulo the diagonal class group to a unit of
value `1 + s₁(z·p₁)`. -/
theorem exists_tail_support_reduction [Nontrivial A] {n : ℕ} {z : A}
    (hz : z ∈ Submodule.span k (L.levelMonomials n)) (u : Aˣ)
    (hu : (u : A) = 1 + L.s 1 * z) :
    ∃ u' : Aˣ, u' * u⁻¹ ∈ stableUnits A ∧
      (u' : A) = 1 + L.s 1 * (z * (L.s 1 * L.t 1)) := by
  have hp0s1 : (L.s 0 * L.t 0) * L.s 1 = 0 := by
    rw [mul_assoc, t_mul_s, if_neg (by decide), mul_zero]
  -- the p₀-piece is square-zero
  have hsq : L.s 1 * (z * (L.s 0 * L.t 0)) *
      (L.s 1 * (z * (L.s 0 * L.t 0))) = 0 := by
    rw [show L.s 1 * (z * (L.s 0 * L.t 0)) *
      (L.s 1 * (z * (L.s 0 * L.t 0))) =
      L.s 1 * z * ((L.s 0 * L.t 0) * L.s 1) *
        (z * (L.s 0 * L.t 0)) from by noncomm_ring, hp0s1]
    noncomm_ring
  -- the p₀-piece unit
  set E : Aˣ := ⟨1 - L.s 1 * (z * (L.s 0 * L.t 0)),
    1 + L.s 1 * (z * (L.s 0 * L.t 0)),
    by
      calc (1 - L.s 1 * (z * (L.s 0 * L.t 0))) *
            (1 + L.s 1 * (z * (L.s 0 * L.t 0)))
          = 1 - L.s 1 * (z * (L.s 0 * L.t 0)) *
              (L.s 1 * (z * (L.s 0 * L.t 0))) := by noncomm_ring
        _ = 1 := by rw [hsq, sub_zero],
    by
      calc (1 + L.s 1 * (z * (L.s 0 * L.t 0))) *
            (1 - L.s 1 * (z * (L.s 0 * L.t 0)))
          = 1 - L.s 1 * (z * (L.s 0 * L.t 0)) *
              (L.s 1 * (z * (L.s 0 * L.t 0))) := by noncomm_ring
        _ = 1 := by rw [hsq, sub_zero]⟩ with hE
  refine ⟨E * u, ?_, ?_⟩
  · -- E ∈ H: square-zero tail with balanced coefficient -z·p₀
    have hEmem : E ∈ stableUnits A := by
      have hzp₀ : -(z * (L.s 0 * L.t 0)) ∈
          Submodule.span k (L.levelMonomials (n + 1)) :=
        Submodule.neg_mem _ (L.mul_p0_mem_span hz)
      refine L.square_zero_tail_mem_stableUnits hzp₀ ?_ E ?_
      · rw [show L.s 1 * -(z * (L.s 0 * L.t 0)) *
          (L.s 1 * -(z * (L.s 0 * L.t 0))) =
          L.s 1 * (z * (L.s 0 * L.t 0)) *
            (L.s 1 * (z * (L.s 0 * L.t 0))) from by noncomm_ring, hsq]
      · show (1 : A) - L.s 1 * (z * (L.s 0 * L.t 0)) = _
        noncomm_ring
    have : E * u * u⁻¹ = E := by group
    rwa [this]
  · show (E : A) * (u : A) = _
    rw [hu]
    show (1 - L.s 1 * (z * (L.s 0 * L.t 0))) * (1 + L.s 1 * z) = _
    have hcross : L.s 1 * (z * (L.s 0 * L.t 0)) * (L.s 1 * z) = 0 := by
      rw [show L.s 1 * (z * (L.s 0 * L.t 0)) * (L.s 1 * z) =
        L.s 1 * z * ((L.s 0 * L.t 0) * L.s 1) * z from by noncomm_ring,
        hp0s1]
      noncomm_ring
    have hsplit : z - z * (L.s 0 * L.t 0) = z * (L.s 1 * L.t 1) := by
      have h1 := L.sum_s_mul_t
      calc z - z * (L.s 0 * L.t 0)
          = z * (L.s 0 * L.t 0 + L.s 1 * L.t 1) -
            z * (L.s 0 * L.t 0) := by rw [h1, mul_one]
        _ = z * (L.s 1 * L.t 1) := by noncomm_ring
    calc (1 - L.s 1 * (z * (L.s 0 * L.t 0))) * (1 + L.s 1 * z)
        = 1 + L.s 1 * (z - z * (L.s 0 * L.t 0)) -
          L.s 1 * (z * (L.s 0 * L.t 0)) * (L.s 1 * z) := by
          noncomm_ring
      _ = 1 + L.s 1 * (z - z * (L.s 0 * L.t 0)) := by
          rw [hcross]; noncomm_ring
      _ = 1 + L.s 1 * (z * (L.s 1 * L.t 1)) := by rw [hsplit]

end PSplit

end LeavittFamily
end NonsoficGroupsExist
