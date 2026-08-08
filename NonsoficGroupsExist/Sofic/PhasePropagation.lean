import NonsoficGroupsExist.Sofic.PhaseOrder

/-!
# A near-scalar unitary is exposed by one of its first four powers

`Sofic.HyperlinearScalar` turns a statement about phases into a statement about
distance: `‖U - τ(U)·1‖² = 1 - |τ(U)|²`, so a unitary whose trace is close to
the unit circle is close to a scalar.  `Sofic.PhaseOrder` supplies the
arithmetic that a scalar cannot evade: no point of the unit circle keeps all of
`ζ, ζ², ζ³, ζ⁴` in the left half plane.  This file chains the two.

  **If `|τ(U)|² ≥ 1 - 10⁻⁶` then `Re τ(U^l) ≥ 1/4` for some `1 ≤ l ≤ 4`.**

The chain is four multiplications long, and each step costs a factor `2` from
the crude triangle inequality `‖A + B‖² ≤ 2‖A‖² + 2‖B‖²`.  Four steps is a
fixed number, chosen before the accuracy is, so the factor `2⁵` is harmless and
no square roots are needed anywhere: the propagation identity is

  `U^{l+1} - τ^{l+1}·1 = U^l (U - τ·1) + τ (U^l - τ^l·1)`,

and left multiplication by the unitary `U^l` and scaling by `τ` (of modulus at
most one) are both norm-nonincreasing, giving `a_{l+1} ≤ 2a_1 + 2a_l` and hence
`a_4 ≤ 22 a_1 = 22(1 - |τ(U)|²)`.

The reading for Pestov's Question 3.4 is `not_forall_re_normTrace_pow_lt`: in a
model separated in the sense of `HyperlinearModel`, every `u_{w^l}` with
`w^l ≠ 1` has `Re τ ≤ ε/2`, so once `ε < 1/2` no element with `w, w², w³, w⁴`
all nontrivial can be sent within `10⁻⁶` of a scalar.  Combined with
`re_nonpos_of_pow_three_eq_one` and `re_nonpos_of_pow_four_eq_one`, which say
the scalars that *do* survive are exactly the roots of unity of order at most
four, the phase obstruction is confined to small torsion.
-/

namespace NonsoficGroupsExist

open Matrix

/-! ## Two computations with the normalized trace -/

theorem normTrace_smul_one (Y : FiniteModel) (hY : 0 < Fintype.card Y) (c : ℂ) :
    normTrace Y (c • (1 : Matrix Y Y ℂ)) = c := by
  have hc : ((Fintype.card Y : ℕ) : ℂ) ≠ 0 := by
    simpa using (Nat.cast_ne_zero (R := ℂ)).mpr hY.ne'
  show Matrix.trace (c • (1 : Matrix Y Y ℂ)) / ((Fintype.card Y : ℕ) : ℂ) = c
  rw [Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
  field_simp

theorem normTrace_sub (Y : FiniteModel) (A B : Matrix Y Y ℂ) :
    normTrace Y (A - B) = normTrace Y A - normTrace Y B := by
  show Matrix.trace (A - B) / _ = _
  rw [Matrix.trace_sub, sub_div]
  rfl

/-! ## Propagation of the scalar defect through powers -/

/-- One step of the propagation, from the identity
`U^{l+1} - τ^{l+1}·1 = U^l (U - τ·1) + τ (U^l - τ^l·1)`. -/
theorem hsNormSq_pow_succ_sub_le (Y : FiniteModel) {U : Matrix Y Y ℂ}
    (hU : U ∈ Matrix.unitaryGroup Y ℂ) (hY : 0 < Fintype.card Y) (l : ℕ) :
    hsNormSq Y (U ^ (l + 1) - (normTrace Y U) ^ (l + 1) • 1)
      ≤ 2 * hsNormSq Y (U - (normTrace Y U) • 1)
        + 2 * hsNormSq Y (U ^ l - (normTrace Y U) ^ l • 1) := by
  set τ : ℂ := normTrace Y U with hτ
  have hsplit : U ^ (l + 1) - τ ^ (l + 1) • (1 : Matrix Y Y ℂ)
      = U ^ l * (U - τ • 1) + τ • (U ^ l - τ ^ l • 1) := by
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, smul_sub, smul_smul,
      pow_succ, pow_succ, mul_comm (τ ^ l) τ]
    abel
  have hUl : U ^ l ∈ Matrix.unitaryGroup Y ℂ := Submonoid.pow_mem _ hU l
  have hτle : Complex.normSq τ ≤ 1 := normSq_normTrace_le_one Y hU hY
  calc hsNormSq Y (U ^ (l + 1) - τ ^ (l + 1) • 1)
      = hsNormSq Y (U ^ l * (U - τ • 1) + τ • (U ^ l - τ ^ l • 1)) := by
        rw [hsplit]
    _ ≤ 2 * hsNormSq Y (U ^ l * (U - τ • 1))
        + 2 * hsNormSq Y (τ • (U ^ l - τ ^ l • 1)) := hsNormSq_add_le _ _ _
    _ = 2 * hsNormSq Y (U - τ • 1)
        + 2 * (Complex.normSq τ * hsNormSq Y (U ^ l - τ ^ l • 1)) := by
        rw [hsNormSq_mul_left Y hUl hY, hsNormSq_smul]
    _ ≤ 2 * hsNormSq Y (U - τ • 1) + 2 * hsNormSq Y (U ^ l - τ ^ l • 1) := by
        have hnn : 0 ≤ hsNormSq Y (U ^ l - τ ^ l • 1) := hsNormSq_nonneg _ _
        nlinarith [hτle, hnn]

/-- **The defect after four multiplications.**  `a_4 ≤ 22 a_1`, where
`a_1 = 1 - |τ(U)|²`. -/
theorem hsNormSq_pow_four_sub_le (Y : FiniteModel) {U : Matrix Y Y ℂ}
    (hU : U ∈ Matrix.unitaryGroup Y ℂ) (hY : 0 < Fintype.card Y) :
    hsNormSq Y (U ^ 4 - (normTrace Y U) ^ 4 • 1)
      ≤ 22 * (1 - Complex.normSq (normTrace Y U)) := by
  set τ : ℂ := normTrace Y U with hτ
  have h1 : hsNormSq Y (U - τ • 1) = 1 - Complex.normSq τ :=
    hsNormSq_sub_normTrace_smul Y hU hY
  have h0 : hsNormSq Y (U ^ 0 - τ ^ 0 • (1 : Matrix Y Y ℂ)) = 0 := by
    simp [hsNormSq]
  have s1 := hsNormSq_pow_succ_sub_le Y hU hY 0
  have s2 := hsNormSq_pow_succ_sub_le Y hU hY 1
  have s3 := hsNormSq_pow_succ_sub_le Y hU hY 2
  have s4 := hsNormSq_pow_succ_sub_le Y hU hY 3
  rw [← hτ] at s1 s2 s3 s4
  rw [h0] at s1
  norm_num at s1 s2 s3 s4 ⊢
  linarith [s1, s2, s3, s4, h1]

/-! ## The perturbed circle bound -/

/-- `re_pow_max_ge` for a complex number of modulus merely *close* to one. -/
theorem exists_re_pow_ge_of_normSq_near_one {z : ℂ}
    (hle : Complex.normSq z ≤ 1) (hge : 1 - 1 / 1000 ≤ Complex.normSq z) :
    ∃ l : ℕ, 1 ≤ l ∧ l ≤ 4 ∧ (299 : ℝ) / 1000 ≤ (z ^ l).re := by
  set s : ℝ := Complex.normSq z with hs
  have hspos : (0 : ℝ) < s := by linarith
  set r : ℝ := Real.sqrt s with hr
  have hrpos : (0 : ℝ) < r := Real.sqrt_pos.mpr hspos
  have hrsq : r ^ 2 = s := Real.sq_sqrt (le_of_lt hspos)
  have hrle : r ≤ 1 := by
    nlinarith [hrsq, hrpos, hle]
  set w : ℂ := z / (r : ℂ) with hw
  have hrne : ((r : ℝ) : ℂ) ≠ 0 := by
    simpa using ne_of_gt hrpos
  have hwn : Complex.normSq w = 1 := by
    rw [hw, Complex.normSq_div, Complex.normSq_ofReal, ← hs]
    field_simp
    nlinarith [hrsq]
  have hzw : z = (r : ℂ) * w := by
    rw [hw]; field_simp
  have hmax := re_pow_max_ge w hwn
  have hstep : ∀ l : ℕ, 1 ≤ l → l ≤ 4 → (3 : ℝ) / 10 ≤ (w ^ l).re →
      (299 : ℝ) / 1000 ≤ (z ^ l).re := by
    intro l hl1 hl4 hwl
    have hzl : (z ^ l).re = r ^ l * (w ^ l).re := by
      have h : z ^ l = ((r ^ l : ℝ) : ℂ) * w ^ l := by
        rw [hzw, mul_pow, Complex.ofReal_pow]
      rw [h, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      ring
    have hpow : r ^ 4 ≤ r ^ l := pow_le_pow_of_le_one (le_of_lt hrpos) hrle hl4
    have hr4 : r ^ 4 = s ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hrsq]
    have hs2 : (998001 : ℝ) / 1000000 ≤ s ^ 2 := by nlinarith [hge, hspos]
    rw [hzl]
    nlinarith [hpow, hr4, hs2, hwl, hrpos]
  rcases le_max_iff.mp hmax with h | h
  · rcases le_max_iff.mp h with h' | h'
    · exact ⟨1, le_refl 1, by norm_num, hstep 1 (le_refl 1) (by norm_num)
        (by simpa using h')⟩
    · exact ⟨2, by norm_num, by norm_num, hstep 2 (by norm_num) (by norm_num) h'⟩
  · rcases le_max_iff.mp h with h' | h'
    · exact ⟨3, by norm_num, by norm_num, hstep 3 (by norm_num) (by norm_num) h'⟩
    · exact ⟨4, by norm_num, by norm_num, hstep 4 (by norm_num) (by norm_num) h'⟩

/-! ## The propagation theorem -/

/-- **A near-scalar unitary is exposed by one of its first four powers.**  If
the normalized trace of `U` has modulus within `10⁻⁶` of one, then one of
`U, U², U³, U⁴` has normalized trace with real part at least `1/4`. -/
theorem exists_re_normTrace_pow_ge (Y : FiniteModel) {U : Matrix Y Y ℂ}
    (hU : U ∈ Matrix.unitaryGroup Y ℂ) (hY : 0 < Fintype.card Y)
    (hnear : 1 - 1 / 1000000 ≤ Complex.normSq (normTrace Y U)) :
    ∃ l : ℕ, 1 ≤ l ∧ l ≤ 4 ∧ (1 : ℝ) / 4 ≤ (normTrace Y (U ^ l)).re := by
  set τ : ℂ := normTrace Y U with hτ
  have hle : Complex.normSq τ ≤ 1 := normSq_normTrace_le_one Y hU hY
  obtain ⟨l, hl1, hl4, hzl⟩ :=
    exists_re_pow_ge_of_normSq_near_one hle (by linarith)
  refine ⟨l, hl1, hl4, ?_⟩
  -- the power's trace is within `1/200` of `τ^l`
  have hdefect : hsNormSq Y (U ^ l - τ ^ l • 1)
      ≤ 22 * (1 - Complex.normSq τ) := by
    have h4 := hsNormSq_pow_four_sub_le Y hU hY
    rw [← hτ] at h4
    have s1 := hsNormSq_pow_succ_sub_le Y hU hY 0
    have s2 := hsNormSq_pow_succ_sub_le Y hU hY 1
    have s3 := hsNormSq_pow_succ_sub_le Y hU hY 2
    rw [← hτ] at s1 s2 s3
    have h0 : hsNormSq Y (U ^ 0 - τ ^ 0 • (1 : Matrix Y Y ℂ)) = 0 := by
      simp [hsNormSq]
    rw [h0] at s1
    have h1 : hsNormSq Y (U - τ • 1) = 1 - Complex.normSq τ :=
      hsNormSq_sub_normTrace_smul Y hU hY
    interval_cases l
    · rw [pow_one, pow_one]; linarith
    · norm_num at s1 s2 ⊢; linarith
    · norm_num at s1 s2 s3 ⊢; linarith
    · exact h4
  have htr : Complex.normSq (normTrace Y (U ^ l) - τ ^ l)
      ≤ 22 * (1 - Complex.normSq τ) := by
    have hsub : normTrace Y (U ^ l) - τ ^ l
        = normTrace Y (U ^ l - τ ^ l • 1) := by
      rw [normTrace_sub, normTrace_smul_one Y hY]
    rw [hsub]
    exact le_trans (normSq_normTrace_le_hsNormSq Y _) hdefect
  have hre : ((normTrace Y (U ^ l) - τ ^ l).re) ^ 2
      ≤ 22 * (1 - Complex.normSq τ) := by
    refine le_trans ?_ htr
    rw [Complex.normSq_apply]
    nlinarith [sq_nonneg (normTrace Y (U ^ l) - τ ^ l).im]
  have hsmall : (22 : ℝ) * (1 - Complex.normSq τ) ≤ 22 / 1000000 := by
    linarith
  have hgap : -(1 : ℝ) / 200 ≤ (normTrace Y (U ^ l)).re - (τ ^ l).re := by
    have : ((normTrace Y (U ^ l) - τ ^ l).re) ^ 2 ≤ 22 / 1000000 := by linarith
    have hdiff : (normTrace Y (U ^ l) - τ ^ l).re
        = (normTrace Y (U ^ l)).re - (τ ^ l).re := by
      rw [Complex.sub_re]
    rw [hdiff] at this
    nlinarith [this]
  linarith [hzl, hgap]

/-! ## The model-level statement -/

variable {G : Type*} [Group G]

/-- One step of the comparison between `u_{w^{l+1}}` and `u_w^{l+1}`: the model's
own multiplicative defect, plus the previous step transported by a unitary. -/
theorem hsNormSq_map_pow_step {F : Finset G} {ε : ℝ}
    (M : HyperlinearModel G F ε) {w : G} (hw : w ∈ F) (l : ℕ)
    (hl : w ^ l ∈ F) :
    hsNormSq M.carrier (M.map (w ^ (l + 1)) - (M.map w) ^ (l + 1))
      ≤ 2 * ε + 2 * hsNormSq M.carrier (M.map (w ^ l) - (M.map w) ^ l) := by
  have hsplit : M.map (w ^ (l + 1)) - (M.map w) ^ (l + 1)
      = (M.map (w ^ l * w) - M.map (w ^ l) * M.map w)
        + (M.map (w ^ l) - (M.map w) ^ l) * M.map w := by
    rw [Matrix.sub_mul, pow_succ, pow_succ]
    abel
  have hmul : hsNormSq M.carrier
      (M.map (w ^ l * w) - M.map (w ^ l) * M.map w) ≤ ε :=
    M.multiplicative (w ^ l) hl w hw
  have hright : hsNormSq M.carrier
      ((M.map (w ^ l) - (M.map w) ^ l) * M.map w)
      = hsNormSq M.carrier (M.map (w ^ l) - (M.map w) ^ l) :=
    hsNormSq_mul_right M.carrier (M.isUnitary w) _
  calc hsNormSq M.carrier (M.map (w ^ (l + 1)) - (M.map w) ^ (l + 1))
      = hsNormSq M.carrier ((M.map (w ^ l * w) - M.map (w ^ l) * M.map w)
          + (M.map (w ^ l) - (M.map w) ^ l) * M.map w) := by rw [hsplit]
    _ ≤ 2 * hsNormSq M.carrier (M.map (w ^ l * w) - M.map (w ^ l) * M.map w)
        + 2 * hsNormSq M.carrier
          ((M.map (w ^ l) - (M.map w) ^ l) * M.map w) := hsNormSq_add_le _ _ _
    _ ≤ 2 * ε + 2 * hsNormSq M.carrier (M.map (w ^ l) - (M.map w) ^ l) := by
        rw [hright]; linarith

/-- The model sends `1` close to `1`: unitarity turns the multiplicative defect
at `(1, 1)` into a bound on the distance to the identity. -/
theorem hsNormSq_one_sub_map_one {F : Finset G} {ε : ℝ}
    (M : HyperlinearModel G F ε) (h1F : (1 : G) ∈ F) :
    hsNormSq M.carrier (1 - M.map 1) ≤ ε := by
  have hdef : hsNormSq M.carrier (M.map (1 * 1) - M.map 1 * M.map 1) ≤ ε :=
    M.multiplicative 1 h1F 1 h1F
  have hfact : M.map (1 * 1) - M.map 1 * M.map 1
      = M.map 1 * (1 - M.map 1) := by
    rw [Matrix.mul_sub, Matrix.mul_one, one_mul]
  rw [hfact, hsNormSq_mul_left M.carrier (M.isUnitary 1) M.nonempty] at hdef
  exact hdef

/-- **No phase on an element of order at least five.**  In a model separated in
the sense of `HyperlinearModel`, if `w, w², w³, w⁴` are all in the test set and
all nontrivial, then `u_w` is not within `10⁻⁶` of a scalar. -/
theorem normSq_normTrace_lt_of_separated {F : Finset G} {ε : ℝ}
    (M : HyperlinearModel G F ε) (hε : 0 < ε) (hεle : ε ≤ 1 / 10000)
    {w : G} (hwF : ∀ l : ℕ, 1 ≤ l → l ≤ 4 → w ^ l ∈ F)
    (h1F : (1 : G) ∈ F) (hwne : ∀ l : ℕ, 1 ≤ l → l ≤ 4 → w ^ l ≠ 1) :
    Complex.normSq (normTrace M.carrier (M.map w)) < 1 - 1 / 1000000 := by
  by_contra hcon
  rw [not_lt] at hcon
  have hw1 : w ∈ F := by simpa using hwF 1 (le_refl 1) (by norm_num)
  have hz : hsNormSq M.carrier (0 : Matrix M.carrier M.carrier ℂ) = 0 := by
    simp [hsNormSq]
  obtain ⟨l, hl1, hl4, hpow⟩ :=
    exists_re_normTrace_pow_ge M.carrier (M.isUnitary w) M.nonempty hcon
  have hlF : w ^ l ∈ F := hwF l hl1 hl4
  have hlne : w ^ l ≠ 1 := hwne l hl1 hl4
  have e1 : hsNormSq M.carrier (M.map (w ^ 1) - (M.map w) ^ 1) = 0 := by
    rw [pow_one, pow_one, sub_self, hz]
  have s1 := hsNormSq_map_pow_step M hw1 1 (by rwa [pow_one])
  have s2 := hsNormSq_map_pow_step M hw1 2 (hwF 2 (by norm_num) (by norm_num))
  have s3 := hsNormSq_map_pow_step M hw1 3 (hwF 3 (by norm_num) (by norm_num))
  rw [show (1 : ℕ) + 1 = 2 from rfl, e1] at s1
  rw [show (2 : ℕ) + 1 = 3 from rfl] at s2
  rw [show (3 : ℕ) + 1 = 4 from rfl] at s3
  have hb : hsNormSq M.carrier (M.map (w ^ l) - (M.map w) ^ l) ≤ 14 * ε := by
    interval_cases l
    · rw [e1]; linarith
    · linarith
    · linarith
    · linarith
  have htr : Complex.normSq (normTrace M.carrier (M.map (w ^ l))
      - normTrace M.carrier ((M.map w) ^ l)) ≤ 14 * ε := by
    rw [← normTrace_sub]
    exact le_trans (normSq_normTrace_le_hsNormSq M.carrier _) hb
  have hlow : (21 : ℝ) / 100 ≤ (normTrace M.carrier (M.map (w ^ l))).re := by
    have hre : ((normTrace M.carrier (M.map (w ^ l))
        - normTrace M.carrier ((M.map w) ^ l)).re) ^ 2 ≤ 14 * ε := by
      refine le_trans ?_ htr
      rw [Complex.normSq_apply]
      nlinarith [sq_nonneg (normTrace M.carrier (M.map (w ^ l))
        - normTrace M.carrier ((M.map w) ^ l)).im]
    rw [Complex.sub_re] at hre
    nlinarith [hre, hpow, hεle]
  have hsep := M.separated (w ^ l) hlF 1 h1F hlne
  rw [hsDistSq_of_unitary M.carrier (M.isUnitary (w ^ l)) (M.isUnitary 1)
    M.nonempty] at hsep
  have hM1 : hsNormSq M.carrier (1 - M.map 1) ≤ ε :=
    hsNormSq_one_sub_map_one M h1F
  have hcmp : Complex.normSq (normTrace M.carrier (M.map (w ^ l))
      - normTrace M.carrier (M.map (w ^ l) * (M.map 1)ᴴ)) ≤ ε := by
    have hfact : M.map (w ^ l) - M.map (w ^ l) * (M.map 1)ᴴ
        = M.map (w ^ l) * (1 - (M.map 1)ᴴ) := by
      rw [Matrix.mul_sub, Matrix.mul_one]
    rw [← normTrace_sub, hfact]
    refine le_trans (normSq_normTrace_le_hsNormSq M.carrier _) ?_
    rw [hsNormSq_mul_left M.carrier (M.isUnitary (w ^ l)) M.nonempty]
    have hct : (1 : Matrix M.carrier M.carrier ℂ) - (M.map 1)ᴴ
        = ((1 : Matrix M.carrier M.carrier ℂ) - M.map 1)ᴴ := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
    rw [hct, hsNormSq_conjTranspose]
    exact hM1
  have hhigh : (normTrace M.carrier (M.map (w ^ l))).re ≤ ε / 2 + 1 / 100 := by
    have hre : ((normTrace M.carrier (M.map (w ^ l))
        - normTrace M.carrier (M.map (w ^ l) * (M.map 1)ᴴ)).re) ^ 2 ≤ ε := by
      refine le_trans ?_ hcmp
      rw [Complex.normSq_apply]
      nlinarith [sq_nonneg (normTrace M.carrier (M.map (w ^ l))
        - normTrace M.carrier (M.map (w ^ l) * (M.map 1)ᴴ)).im]
    rw [Complex.sub_re] at hre
    nlinarith [hre, hsep, hεle]
  linarith [hlow, hhigh, hεle]

end NonsoficGroupsExist