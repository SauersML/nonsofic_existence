import NonsoficGroupsExist.Sofic.NoRounding

/-!
# Rounding a character, where rounding a circle failed

`NoRounding` proves that no pointwise rule turns a circle-valued phase system
into a `μ_m`-valued one: a multiplicative rounding of the circle is trivial,
because the circle is divisible, and a nearest-point rounding is not
multiplicative.  It is natural to read that as saying the restriction to `m`-th
roots of unity in the soficity criterion of `MonomialModel` is itself an
obstacle.  It is not, and this file isolates why.

The failure in `NoRounding` is a failure of *freeness*, not of fineness.  A
homomorphism out of the circle is pinned down everywhere by divisibility.  A
homomorphism out of a **free** abelian group is pinned down by nothing at all:
its values on a basis may be chosen arbitrarily, and any choice extends.  So
once the phases are exactly multiplicative -- which is what a correction buys --
their values are a character of a free abelian group, and that character *can*
be rounded, multiplicatively and to finite order.

Concretely, a real character of `ℤ^r` is `n ↦ Σ nᵢ aᵢ`, and replacing each `aᵢ`
by `round(q aᵢ)/q` gives a character with values in `(1/q)ℤ`
(`ratChar_add`, `ratChar_eq_div`) that agrees with it to within
`(Σ |nᵢ|)/(2q)` (`abs_ratChar_sub_charEval_le`).  On any set of coefficients
bounded by `N` -- and a finite window over a finite model supplies exactly such
a set -- taking `q` large makes the agreement as tight as one likes
(`exists_ratChar_close`).

So the `ℝ/ℤ` versus `μ_m` distinction is not where the difficulty lives.  Once
multiplicativity is exact, finite order is free.  What remains hard is getting
exact multiplicativity in the first place -- `PhaseCorrection` and `ScalarClass`
-- and the separation of the untwisted model, which no amount of rounding
addresses.  Nothing here decides Question 3.4; it removes a candidate obstacle.
-/

namespace NonsoficGroupsExist

open Finset

/-! ## Characters of a free abelian group -/

/-- A real character of `ℤ^r`, given by its values on the basis. -/
noncomputable def charEval (r : ℕ) (a : Fin r → ℝ) (n : Fin r → ℤ) : ℝ :=
  ∑ i, (n i : ℝ) * a i

/-- **A real character is a homomorphism.**  Nothing is assumed about `a`; this
is the freeness that the circle does not have. -/
theorem charEval_add (r : ℕ) (a : Fin r → ℝ) (n n' : Fin r → ℤ) :
    charEval r a (n + n') = charEval r a n + charEval r a n' := by
  simp only [charEval, Pi.add_apply, Int.cast_add]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-! ## The rounded character -/

/-- The numerator of the rounded character: an integer by construction. -/
noncomputable def ratNumer (r : ℕ) (a : Fin r → ℝ) (q : ℕ) (n : Fin r → ℤ) : ℤ :=
  ∑ i, n i * round ((q : ℝ) * a i)

/-- The rounded character: each basis value `aᵢ` is replaced by the nearest
multiple of `1/q`, and the result is extended by freeness. -/
noncomputable def ratChar (r : ℕ) (a : Fin r → ℝ) (q : ℕ) (n : Fin r → ℤ) : ℝ :=
  (ratNumer r a q n : ℝ) / q

/-- **The rounded character is still a homomorphism.**  This is exactly what a
rounding of the circle could not be. -/
theorem ratChar_add (r : ℕ) (a : Fin r → ℝ) (q : ℕ) (n n' : Fin r → ℤ) :
    ratChar r a q (n + n') = ratChar r a q n + ratChar r a q n' := by
  have h : ratNumer r a q (n + n') = ratNumer r a q n + ratNumer r a q n' := by
    simp only [ratNumer, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  simp only [ratChar, h, Int.cast_add]
  ring

/-- **The rounded character has finite order**: every value is a multiple of
`1/q`, so the induced character of the circle lands in `μ_q`. -/
theorem ratChar_eq_div (r : ℕ) (a : Fin r → ℝ) (q : ℕ) (n : Fin r → ℤ) :
    ∃ k : ℤ, ratChar r a q n = (k : ℝ) / q :=
  ⟨ratNumer r a q n, rfl⟩

/-! ## How close the rounding is -/

/-- **The rounding error is controlled by the coefficients.**  Each basis value
moves by at most `1/(2q)`, and the character is linear in the coefficients. -/
theorem abs_ratChar_sub_charEval_le (r : ℕ) (a : Fin r → ℝ) {q : ℕ} (hq : 0 < q)
    (n : Fin r → ℤ) :
    |ratChar r a q n - charEval r a n| ≤ (∑ i, |(n i : ℝ)|) / (2 * q) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsplit : ratChar r a q n - charEval r a n
      = ∑ i, (n i : ℝ) * ((round ((q : ℝ) * a i) : ℝ) / q - a i) := by
    simp only [ratChar, ratNumer, charEval]
    push_cast
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by field_simp
  rw [hsplit]
  calc |∑ i, (n i : ℝ) * ((round ((q : ℝ) * a i) : ℝ) / q - a i)|
      ≤ ∑ i, |(n i : ℝ) * ((round ((q : ℝ) * a i) : ℝ) / q - a i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |(n i : ℝ)| / (2 * q) := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        rw [abs_mul]
        have hround : |(round ((q : ℝ) * a i) : ℝ) / q - a i| ≤ 1 / (2 * q) := by
          have hkey : (round ((q : ℝ) * a i) : ℝ) / q - a i
              = ((round ((q : ℝ) * a i) : ℝ) - (q : ℝ) * a i) / q := by
            field_simp
          have habs : |(round ((q : ℝ) * a i) : ℝ) - (q : ℝ) * a i| ≤ 1 / 2 := by
            rw [abs_sub_comm]
            exact abs_sub_round _
          rw [hkey, abs_div, abs_of_pos hqR, div_le_div_iff₀ hqR (by positivity)]
          nlinarith [habs, hqR]
        calc |(n i : ℝ)| * |(round ((q : ℝ) * a i) : ℝ) / q - a i|
            ≤ |(n i : ℝ)| * (1 / (2 * q)) := by
              exact mul_le_mul_of_nonneg_left hround (abs_nonneg _)
          _ = |(n i : ℝ)| / (2 * q) := by ring
    _ = (∑ i, |(n i : ℝ)|) / (2 * q) := by rw [Finset.sum_div]

/-- **On any bounded set of coefficients the rounding is as tight as one likes.**
A finite window over a finite model supplies exactly such a bounded set, so the
restriction to `m`-th roots of unity in the soficity criterion costs nothing
once the phases are exactly multiplicative. -/
theorem exists_ratChar_close (r : ℕ) (a : Fin r → ℝ) (N : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ q : ℕ, 0 < q ∧ ∀ n : Fin r → ℤ, (∀ i, |n i| ≤ (N : ℤ)) →
      |ratChar r a q n - charEval r a n| ≤ δ := by
  obtain ⟨q, hq⟩ := exists_nat_gt ((r * N : ℝ) / (2 * δ) + 1)
  have hqpos : 0 < q := by
    have hnn : (0 : ℝ) ≤ (r * N : ℝ) / (2 * δ) := by positivity
    have : (0 : ℝ) < q := by linarith
    exact_mod_cast this
  refine ⟨q, hqpos, fun n hn ↦ ?_⟩
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hbound : ∑ i, |(n i : ℝ)| ≤ (r : ℝ) * N := by
    calc ∑ i, |(n i : ℝ)| ≤ ∑ _i : Fin r, (N : ℝ) := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          have := hn i
          have : |(n i : ℝ)| ≤ (N : ℝ) := by
            rw [← Int.cast_abs]
            exact_mod_cast hn i
          exact this
      _ = (r : ℝ) * N := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  refine le_trans (abs_ratChar_sub_charEval_le r a hqpos n) ?_
  rw [div_le_iff₀ (by positivity)]
  have hstep : (r : ℝ) * N < 2 * δ * q := by
    have h1 : (r * N : ℝ) / (2 * δ) < q := by linarith
    rw [div_lt_iff₀ (by positivity)] at h1
    linarith
  linarith [hbound, hstep]

end NonsoficGroupsExist
