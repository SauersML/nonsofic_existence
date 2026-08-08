import NonsoficGroupsExist.Sofic.HyperlinearAmplification

/-!
# How far a unitary is from a scalar, measured by its trace

`Sofic.HyperlinearAmplification` leaves one hypothesis standing: the conjugate
double amplifies a unitary model exactly when `|τ(u_g u_h^*)| < 1`, and the
extreme case `|τ| = 1` is the scalar case.  This file makes that dichotomy
quantitative, with an identity rather than an estimate:

  `‖U - c·1‖²  =  1 - 2 Re(c̄ τ(U)) + |c|²`   (`hsNormSq_sub_smul_one`),

for every unitary `U` and every scalar `c`, in the normalized Hilbert--Schmidt
norm.  Minimizing over `c` -- the minimum is at `c = τ(U)` -- gives

  `‖U - τ(U)·1‖²  =  1 - |τ(U)|²`   (`hsNormSq_sub_normTrace_smul`),

so the trace defect `1 - |τ(U)|²` **is** the squared distance from `U` to the
scalars.  Two consequences fall out immediately: `|τ(U)| ≤ 1` always
(`normSq_normTrace_le_one`), and `|τ(U)| = 1` exactly when `U` is the scalar
`τ(U)·1` (`eq_smul_one_iff_normSq_normTrace_eq_one`).

The point is that this converts a *statement about phases* into a *distance*.
An element of a unitary model with `|τ| ≥ 1 - δ` is within `√δ` of a scalar, so
the phase obstruction can be propagated through products: if `u_w ≈ ζ·1` then
`u_{w^l} ≈ ζ^l·1`, and separation at every power constrains `ζ` -- which is how
one shows a strong model cannot put a phase on an element of large order.
`hsNormSq_mul_left` and `hsNormSq_add_le` are the two transport lemmas that
propagation needs; both are proved here in squared form, so no square roots and
no norm instance are involved anywhere.
-/

namespace NonsoficGroupsExist

open Matrix

/-! ## The normalized squared Hilbert--Schmidt norm -/

/-- Normalized squared Hilbert--Schmidt norm.  `hsDistSq Y A B` is definitionally
`hsNormSq Y (A - B)`, so the two are interchangeable by `rfl`. -/
noncomputable def hsNormSq (Y : FiniteModel) (A : Matrix Y Y ℂ) : ℝ :=
  (∑ i : Y, ∑ j : Y, Complex.normSq (A i j)) / Fintype.card Y

theorem hsNormSq_nonneg (Y : FiniteModel) (A : Matrix Y Y ℂ) :
    0 ≤ hsNormSq Y A :=
  div_nonneg
    (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦
      Complex.normSq_nonneg _)
    (Nat.cast_nonneg _)

/-- The squared Frobenius mass of a matrix is the trace of `A Aᴴ`. -/
theorem ofReal_sum_normSq (Y : FiniteModel) (A : Matrix Y Y ℂ) :
    (((∑ i : Y, ∑ j : Y, Complex.normSq (A i j)) : ℝ) : ℂ)
      = Matrix.trace (A * Aᴴ) := by
  rw [Complex.ofReal_sum]
  show (∑ i : Y, ((∑ j : Y, Complex.normSq (A i j) : ℝ) : ℂ))
      = ∑ i : Y, (A * Aᴴ) i i
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Complex.ofReal_sum, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Matrix.conjTranspose_apply]
  exact (Complex.mul_conj (A i j)).symm

/-- The normalized squared norm as a normalized trace. -/
theorem ofReal_hsNormSq (Y : FiniteModel) (A : Matrix Y Y ℂ) :
    ((hsNormSq Y A : ℝ) : ℂ) = normTrace Y (A * Aᴴ) := by
  rw [hsNormSq, Complex.ofReal_div, ofReal_sum_normSq]
  show _ = Matrix.trace (A * Aᴴ) / ((Fintype.card Y : ℕ) : ℂ)
  norm_num

/-! ## The distance from a unitary to a scalar -/

/-- **The exact expansion.**  For unitary `U` and any scalar `c`, the squared
distance to `c·1` is `1 - 2 Re(c̄ τ(U)) + |c|²`. -/
theorem hsNormSq_sub_smul_one (Y : FiniteModel) {U : Matrix Y Y ℂ}
    (hU : U ∈ Matrix.unitaryGroup Y ℂ) (hY : 0 < Fintype.card Y) (c : ℂ) :
    hsNormSq Y (U - c • 1)
      = 1 - 2 * (((starRingEnd ℂ) c) * normTrace Y U).re + Complex.normSq c := by
  have hUU : U * Uᴴ = 1 := by
    have h := hU
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at h
    exact h
  have hc : ((Fintype.card Y : ℕ) : ℂ) ≠ 0 := by
    simpa using (Nat.cast_ne_zero (R := ℂ)).mpr hY.ne'
  have hconj : (U - c • (1 : Matrix Y Y ℂ))ᴴ
      = Uᴴ - ((starRingEnd ℂ) c) • 1 := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one]
    rfl
  have hexp : (U - c • (1 : Matrix Y Y ℂ)) * (U - c • (1 : Matrix Y Y ℂ))ᴴ
      = 1 - ((starRingEnd ℂ) c) • U - c • Uᴴ
        + (c * (starRingEnd ℂ) c) • (1 : Matrix Y Y ℂ) := by
    rw [hconj, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hUU]
    simp [smul_smul, mul_comm]
    abel
  have htrU : Matrix.trace U = ((Fintype.card Y : ℕ) : ℂ) * normTrace Y U := by
    rw [normTrace]
    field_simp
  have htr : Matrix.trace ((U - c • (1 : Matrix Y Y ℂ))
      * (U - c • (1 : Matrix Y Y ℂ))ᴴ)
      = ((Fintype.card Y : ℕ) : ℂ)
        * (1 - ((starRingEnd ℂ) c) * normTrace Y U
            - c * (starRingEnd ℂ) (normTrace Y U)
          + c * (starRingEnd ℂ) c) := by
    rw [hexp]
    rw [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_smul,
      Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one,
      Matrix.trace_conjTranspose, htrU]
    have hstar : star (((Fintype.card Y : ℕ) : ℂ) * normTrace Y U)
        = ((Fintype.card Y : ℕ) : ℂ) * (starRingEnd ℂ) (normTrace Y U) := by
      simp
    simp only [smul_eq_mul, hstar]
    ring
  have hkey : ((hsNormSq Y (U - c • 1) : ℝ) : ℂ)
      = 1 - ((starRingEnd ℂ) c) * normTrace Y U
          - c * (starRingEnd ℂ) (normTrace Y U) + c * (starRingEnd ℂ) c := by
    rw [ofReal_hsNormSq, normTrace, htr]
    field_simp
  have hre := congrArg Complex.re hkey
  rw [Complex.ofReal_re] at hre
  rw [hre]
  have h1 : (c * (starRingEnd ℂ) (normTrace Y U)).re
      = (((starRingEnd ℂ) c) * normTrace Y U).re := by
    simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  simp only [Complex.sub_re, Complex.add_re, Complex.one_re, h1,
    Complex.mul_conj]
  simp [Complex.normSq_apply]
  ring

/-- **The trace defect is the distance to the scalars.**  Taking `c = τ(U)` in
`hsNormSq_sub_smul_one`, which is where the expansion is minimized. -/
theorem hsNormSq_sub_normTrace_smul (Y : FiniteModel) {U : Matrix Y Y ℂ}
    (hU : U ∈ Matrix.unitaryGroup Y ℂ) (hY : 0 < Fintype.card Y) :
    hsNormSq Y (U - (normTrace Y U) • 1)
      = 1 - Complex.normSq (normTrace Y U) := by
  rw [hsNormSq_sub_smul_one Y hU hY (normTrace Y U)]
  have h : (((starRingEnd ℂ) (normTrace Y U)) * normTrace Y U).re
      = Complex.normSq (normTrace Y U) := by
    rw [mul_comm, Complex.mul_conj]
    simp
  rw [h]
  ring

/-- The normalized trace of a unitary lies in the closed unit disc -- because a
squared distance is nonnegative. -/
theorem normSq_normTrace_le_one (Y : FiniteModel) {U : Matrix Y Y ℂ}
    (hU : U ∈ Matrix.unitaryGroup Y ℂ) (hY : 0 < Fintype.card Y) :
    Complex.normSq (normTrace Y U) ≤ 1 := by
  have h := hsNormSq_nonneg Y (U - (normTrace Y U) • 1)
  rw [hsNormSq_sub_normTrace_smul Y hU hY] at h
  linarith

/-- **Equality is exactly the scalar case.**  `|τ(U)| = 1` iff `U` is the
scalar `τ(U)·1`; this is the phase collapse of
`Sofic.HyperlinearAmplification` in its sharpest form. -/
theorem eq_smul_one_iff_normSq_normTrace_eq_one (Y : FiniteModel)
    {U : Matrix Y Y ℂ} (hU : U ∈ Matrix.unitaryGroup Y ℂ)
    (hY : 0 < Fintype.card Y) :
    U = (normTrace Y U) • 1 ↔ Complex.normSq (normTrace Y U) = 1 := by
  constructor
  · intro hUs
    have h : hsNormSq Y (U - (normTrace Y U) • 1) = 0 := by
      rw [← hUs, sub_self]
      simp [hsNormSq]
    rw [hsNormSq_sub_normTrace_smul Y hU hY] at h
    linarith
  · intro hns
    have h : hsNormSq Y (U - (normTrace Y U) • 1) = 0 := by
      rw [hsNormSq_sub_normTrace_smul Y hU hY, hns]
      ring
    have hzero : ∀ i j : Y, (U - (normTrace Y U) • 1) i j = 0 := by
      intro i j
      have hnn : ∀ i : Y, 0 ≤ ∑ j : Y,
          Complex.normSq ((U - (normTrace Y U) • 1) i j) :=
        fun i ↦ Finset.sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _
      have hsum : (∑ i : Y, ∑ j : Y,
          Complex.normSq ((U - (normTrace Y U) • 1) i j)) = 0 := by
        have hc : (Fintype.card Y : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hY.ne'
        rw [hsNormSq, div_eq_zero_iff] at h
        rcases h with h | h
        · exact h
        · exact absurd h hc
      have hi := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ hnn i).mp hsum i
        (Finset.mem_univ i)
      have hj := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦
        Complex.normSq_nonneg _).mp hi j (Finset.mem_univ j)
      exact Complex.normSq_eq_zero.mp hj
    ext i j
    have := hzero i j
    rw [Matrix.sub_apply] at this
    linear_combination this

/-! ## Transport lemmas, in squared form -/

/-- Multiplying by a unitary on the left does not move the norm. -/
theorem hsNormSq_mul_left (Y : FiniteModel) {V : Matrix Y Y ℂ}
    (hV : V ∈ Matrix.unitaryGroup Y ℂ) (hY : 0 < Fintype.card Y)
    (A : Matrix Y Y ℂ) : hsNormSq Y (V * A) = hsNormSq Y A := by
  have hVV : Vᴴ * V = 1 := by
    have h := hV
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at h
    exact h
  have hc : ((Fintype.card Y : ℕ) : ℂ) ≠ 0 := by
    simpa using (Nat.cast_ne_zero (R := ℂ)).mpr hY.ne'
  have htr : Matrix.trace ((V * A) * (V * A)ᴴ) = Matrix.trace (A * Aᴴ) := by
    rw [Matrix.conjTranspose_mul]
    have hassoc : V * A * (Aᴴ * Vᴴ) = V * (A * Aᴴ * Vᴴ) := by
      simp [Matrix.mul_assoc]
    rw [hassoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hVV, Matrix.mul_one]
  have h := congrArg Complex.re
    (by rw [ofReal_hsNormSq, ofReal_hsNormSq, normTrace, normTrace, htr] :
      ((hsNormSq Y (V * A) : ℝ) : ℂ) = ((hsNormSq Y A : ℝ) : ℂ))
  simpa using h

/-- The crude triangle inequality, in squared form: `|x + y|² ≤ 2|x|² + 2|y|²`
summed over entries.  No square roots, and a factor `2` per step is harmless
whenever the number of steps is fixed before the accuracy is chosen. -/
theorem hsNormSq_add_le (Y : FiniteModel) (A B : Matrix Y Y ℂ) :
    hsNormSq Y (A + B) ≤ 2 * hsNormSq Y A + 2 * hsNormSq Y B := by
  have hentry : ∀ i j : Y, Complex.normSq ((A + B) i j)
      ≤ 2 * Complex.normSq (A i j) + 2 * Complex.normSq (B i j) := by
    intro i j
    show Complex.normSq (A i j + B i j) ≤ _
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
    nlinarith [sq_nonneg ((A i j).re - (B i j).re),
      sq_nonneg ((A i j).im - (B i j).im)]
  have hsum : (∑ i : Y, ∑ j : Y, Complex.normSq ((A + B) i j))
      ≤ 2 * (∑ i : Y, ∑ j : Y, Complex.normSq (A i j))
        + 2 * (∑ i : Y, ∑ j : Y, Complex.normSq (B i j)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ ↦ hentry i j
  simp only [hsNormSq]
  rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]
  gcongr

end NonsoficGroupsExist
