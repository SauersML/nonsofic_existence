import NonsoficGroupsExist.Sofic.HyperlinearScalar

/-!
# A phase cannot hide from its first four powers

`Sofic.HyperlinearScalar` shows that a unitary whose normalized trace has
modulus near `1` is near a scalar, so the phase obstruction of
`Sofic.HyperlinearAmplification` can be propagated through powers.  This file
supplies the arithmetic fact that makes propagation bite.

A model separated in the sense of `HyperlinearModel` has `Re τ(u_g u_h^*) ≤ ε/2`
for distinct `g, h`, so if `u_w` is close to the scalar `ζ` then *every* power
`ζ^l` with `w^l ≠ 1` is confined to the left half plane.  The point is that
**no point of the unit circle can keep its first four powers there**:

  `max (Re ζ, Re ζ², Re ζ³, Re ζ⁴) ≥ 3/10`   (`re_pow_max_ge`).

Writing `x = Re ζ`, the four real parts are the Chebyshev polynomials
`x`, `2x² - 1`, `4x³ - 3x`, `8x⁴ - 8x² + 1`, so this is a statement about one
real variable on `[-1, 1]`.  The minimum of the maximum is `≈ 0.3106`, attained
where the second and third cross at `x ≈ -0.8095`; `3/10` is that value with a
little room.

Four powers are needed and no fewer: `ζ = i` keeps `Re ζ, Re ζ², Re ζ³` all
`≤ 0`, and only the fourth power returns to `1`.  The elements a strong model
*can* send to a scalar are therefore exactly those of order at most `4` --
`-1`, `±i` and the primitive cube roots, whose nontrivial powers all have
nonpositive real part.  So the phase obstruction to Pestov's Question 3.4 is
confined to small torsion.
-/

namespace NonsoficGroupsExist

/-- The real parts of the first four powers of a unit complex number are the
Chebyshev polynomials of its real part. -/
theorem re_pow_two (z : ℂ) (hz : Complex.normSq z = 1) :
    (z ^ 2).re = 2 * z.re ^ 2 - 1 := by
  have him : z.im ^ 2 = 1 - z.re ^ 2 := by
    rw [Complex.normSq_apply] at hz; nlinarith
  simp only [pow_two, Complex.mul_re]
  linear_combination -him

theorem re_pow_three (z : ℂ) (hz : Complex.normSq z = 1) :
    (z ^ 3).re = 4 * z.re ^ 3 - 3 * z.re := by
  have him : z.im ^ 2 = 1 - z.re ^ 2 := by
    rw [Complex.normSq_apply] at hz; nlinarith
  simp only [pow_succ, pow_zero, one_mul, Complex.mul_re, Complex.mul_im]
  linear_combination (-3 * z.re) * him

theorem re_pow_four (z : ℂ) (hz : Complex.normSq z = 1) :
    (z ^ 4).re = 8 * z.re ^ 4 - 8 * z.re ^ 2 + 1 := by
  have him : z.im ^ 2 = 1 - z.re ^ 2 := by
    rw [Complex.normSq_apply] at hz; nlinarith
  simp only [pow_succ, pow_zero, one_mul, Complex.mul_re, Complex.mul_im]
  linear_combination (-7 * z.re ^ 2 + 1 + z.im ^ 2) * him

/-- **No point of the unit circle keeps its first four powers in the left half
plane.**  This is the reason a strong unitary model cannot put a phase on an
element of order five or more. -/
theorem re_pow_max_ge (z : ℂ) (hz : Complex.normSq z = 1) :
    3 / 10 ≤ max (max z.re ((z ^ 2).re)) (max ((z ^ 3).re) ((z ^ 4).re)) := by
  rw [re_pow_two z hz, re_pow_three z hz, re_pow_four z hz]
  by_contra hcon
  rw [not_le, max_lt_iff, max_lt_iff, max_lt_iff] at hcon
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hcon
  -- `h2` bounds `Re z` squared above; `h4` bounds it below; `h1` makes it negative.
  have hs1 : z.re ^ 2 < 13 / 20 := by linarith
  have hs2 : (24 : ℝ) / 250 < z.re ^ 2 := by
    by_contra hle
    rw [not_lt] at hle
    have h904 : z.re ^ 2 ≤ 904 / 1000 := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hle) (sub_nonneg.mpr h904)]
  have hneg : z.re < -(3 / 10) := by
    by_contra hge
    rw [not_lt] at hge
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ z.re + 3 / 10)
      (by linarith : (0 : ℝ) ≤ 3 / 10 - z.re)]
  -- `Re z` cannot reach `-81/100`, since that would push its square past `13/20`.
  have hx81 : -(81 / 100 : ℝ) < z.re := by
    nlinarith [sq_nonneg (z.re + 81 / 100)]
  -- `4x³ - 3x - 3/10 = (x + 81/100)(4x² - (81/25)x - 939/2500) + 53/12500`.
  nlinarith [mul_pos (by linarith : (0 : ℝ) < z.re + 81 / 100)
    (by nlinarith [sq_nonneg z.re] :
      (0 : ℝ) < 4 * z.re ^ 2 - (81 / 25) * z.re - 939 / 2500)]


/-! ## Which scalars remain available -/

/-- A fourth root of unity other than `1` has nonpositive real part. -/
theorem re_nonpos_of_pow_four_eq_one {z : ℂ} (h4 : z ^ 4 = 1) (hne : z ≠ 1) :
    z.re ≤ 0 := by
  have hfac : (z - 1) * ((z + 1) * (z ^ 2 + 1)) = 0 := by linear_combination h4
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd (by linear_combination h : z = 1) hne
  rcases mul_eq_zero.mp h with h | h
  · have hz : z = -1 := by linear_combination h
    rw [hz]; simp
  · rw [Complex.ext_iff] at h
    obtain ⟨hre0, him0⟩ := h
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
      Complex.zero_re, Complex.zero_im, pow_two, Complex.mul_re,
      Complex.mul_im] at hre0 him0
    have him : z.re * z.im = 0 := by linear_combination him0 / 2
    have hre : z.re ^ 2 - z.im ^ 2 = -1 := by linear_combination hre0
    rcases mul_eq_zero.mp him with hx | hy
    · exact le_of_eq hx
    · exfalso
      rw [hy] at hre
      nlinarith [sq_nonneg z.re]

/-- A cube root of unity other than `1` has real part `-1/2`, in particular
nonpositive. -/
theorem re_nonpos_of_pow_three_eq_one {z : ℂ} (h3 : z ^ 3 = 1) (hne : z ≠ 1) :
    z.re ≤ 0 := by
  have hfac : (z - 1) * (z ^ 2 + z + 1) = 0 := by linear_combination h3
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd (by linear_combination h : z = 1) hne
  · rw [Complex.ext_iff] at h
    obtain ⟨hre0, him0⟩ := h
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
      Complex.zero_re, Complex.zero_im, pow_two, Complex.mul_re,
      Complex.mul_im] at hre0 him0
    have him : z.im * (2 * z.re + 1) = 0 := by linear_combination him0
    rcases mul_eq_zero.mp him with hy | hx
    · exfalso
      have hre : z.re ^ 2 + z.re + 1 = 0 := by
        linear_combination hre0 + z.im * hy
      nlinarith [sq_nonneg (z.re + 1 / 2)]
    · linarith

end NonsoficGroupsExist
