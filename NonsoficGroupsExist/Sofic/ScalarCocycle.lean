import NonsoficGroupsExist.Sofic.MonomialModel

/-!
# Exact infeasibility is a determinant, and it is not a gap

A recurring hope in the search for a nonhyperlinear group is that emptiness of
the *exact* solution locus at every matrix size is half of a non-closure
profile, so that only robustness remains to be shown.  The scalar commutation
relation shows that inference fails, and shows it with the cheapest possible
witness.

For unitaries `U, V` on a model of size `n`, the relation

  `U V = c · (V U)`

forces `c^n = 1`, by taking determinants: `det U det V = c^n det V det U` and
the determinants are nonzero.  So for `c` not a root of unity the exact locus
is **empty at every dimension**, proved in one line
(`pow_card_eq_one_of_scalarCommute`).

Yet the relation is *exactly* solvable whenever `c` is a `q`-th root of unity,
on a model of size `q`, by the clock-and-shift pair
(`exists_scalarCommute_of_pow_eq_one`).  Since roots of unity are dense in the
circle, a `c` off the circle's rational points is a limit of exactly solvable
instances, and the defect of the corresponding pairs tends to zero.  Emptiness
of every exact locus therefore gives no dimension-independent gap for the
relaxed loci.

Two further things are worth noticing, and both point at
`Sofic.HyperlinearAmplification`.  First, the witness is a **monomial** pair:
the shift is a permutation matrix and the clock is a diagonal of phases, so the
whole phenomenon lives in `T_Y ⋊ Sym Y`, the same group as Thom's microstates.
Second, the obstruction it evades is a *scalar* cocycle -- exactly the
configuration the phase collapse says tensor amplification cannot remove, and
exactly the configuration `hammingDistance_wreathPerm` prices at the whole of
`Y` when one tries to untwist it.
-/

namespace NonsoficGroupsExist

open Matrix

/-! ## The determinant obstruction -/

/-- **Exact infeasibility is a determinant.**  If two unitaries commute up to
the scalar `c` on a model of size `n`, then `c^n = 1`. -/
theorem pow_card_eq_one_of_scalarCommute (Y : FiniteModel) {U V : Matrix Y Y ℂ}
    (hU : U ∈ Matrix.unitaryGroup Y ℂ) (hV : V ∈ Matrix.unitaryGroup Y ℂ)
    {c : ℂ} (h : U * V = c • (V * U)) :
    c ^ Fintype.card Y = 1 := by
  have hUd : Matrix.det U ≠ 0 := by
    intro hcon
    have h1 : U * Uᴴ = 1 := by
      have hh := hU
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hh
      exact hh
    have := congrArg Matrix.det h1
    rw [Matrix.det_mul, hcon, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hVd : Matrix.det V ≠ 0 := by
    intro hcon
    have h1 : V * Vᴴ = 1 := by
      have hh := hV
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hh
      exact hh
    have := congrArg Matrix.det h1
    rw [Matrix.det_mul, hcon, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hdet := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_mul] at hdet
  have hne : Matrix.det V * Matrix.det U ≠ 0 := mul_ne_zero hVd hUd
  have : Matrix.det U * Matrix.det V = Matrix.det V * Matrix.det U := by ring
  rw [this] at hdet
  field_simp at hdet
  exact hdet.symm

/-! ## The clock-and-shift solution -/

/-- A root of unity absorbs reduction of the exponent modulo `q`. -/
theorem pow_val_add_one {q : ℕ} (hq : 1 < q) {ζ : ℂ} (hζ : ζ ^ q = 1)
    (i : ZMod q) : ζ ^ ((i + 1).val) = ζ * ζ ^ (i.val) := by
  haveI : NeZero q := ⟨by omega⟩
  haveI : Fact (1 < q) := ⟨hq⟩
  have hmod : ∀ a : ℕ, ζ ^ (a % q) = ζ ^ a := by
    intro a
    conv_rhs => rw [← Nat.mod_add_div a q]
    rw [pow_add, pow_mul, hζ, one_pow, mul_one]
  rw [ZMod.val_add, ZMod.val_one, hmod, pow_succ, mul_comm]

/-- **The relation is exactly solvable at the root-of-unity dimensions.**  The
shift and the clock satisfy `U V = ζ · (V U)` on a model of size `q` whenever
`ζ^q = 1`.  Both are monomial: the shift is a permutation, the clock a diagonal
of phases. -/
theorem exists_scalarCommute_of_pow_eq_one (q : ℕ) (hq : 1 < q) {ζ : ℂ}
    (hζ : ζ ^ q = 1) (hζn : Complex.normSq ζ = 1) :
    ∃ (Y : FiniteModel) (U V : Matrix Y Y ℂ),
      Fintype.card Y = q ∧
      U ∈ Matrix.unitaryGroup Y ℂ ∧ V ∈ Matrix.unitaryGroup Y ℂ ∧
      U * V = ζ • (V * U) := by
  classical
  haveI : NeZero q := ⟨by omega⟩
  refine ⟨⟨ZMod q, inferInstance, inferInstance⟩,
    (fun i j : ZMod q ↦ if j = i + 1 then (1 : ℂ) else 0),
    (fun i j : ZMod q ↦ if j = i then ζ ^ (ZMod.val i) else 0),
    ZMod.card q, ?_, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    ext i k
    rw [Matrix.mul_apply]
    have hterm : ∀ j : ZMod q,
        (if j = i + 1 then (1 : ℂ) else 0)
          * (starRingEnd ℂ) (if j = k + 1 then (1 : ℂ) else 0)
        = if j = i + 1 then (if j = k + 1 then (1 : ℂ) else 0) else 0 := by
      intro j
      by_cases h1 : j = i + 1 <;> by_cases h2 : j = k + 1 <;> simp [h1, h2]
    simp only [Matrix.conjTranspose_apply, RCLike.star_def]
    rw [Finset.sum_congr rfl fun j _ ↦ hterm j,
      Finset.sum_ite_eq' Finset.univ (i + 1)]
    simp only [Finset.mem_univ, if_true]
    by_cases hik : i = k
    · subst hik; simp [Matrix.one_apply_eq]
    · rw [Matrix.one_apply_ne hik, if_neg (fun hc ↦ hik (by
        exact add_right_cancel hc))]
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    ext i k
    rw [Matrix.mul_apply]
    have hterm : ∀ j : ZMod q,
        (if j = i then ζ ^ (ZMod.val i) else 0)
          * (starRingEnd ℂ) (if j = k then ζ ^ (ZMod.val k) else 0)
        = if j = i then (if i = k then
            ζ ^ (ZMod.val i) * (starRingEnd ℂ) (ζ ^ (ZMod.val k)) else 0)
          else 0 := by
      intro j
      by_cases h1 : j = i
      · rw [if_pos h1, if_pos h1]
        by_cases h2 : i = k
        · rw [if_pos h2, if_pos (h1.trans h2)]
        · rw [if_neg h2, if_neg (fun hc ↦ h2 (h1.symm.trans hc)), map_zero,
            mul_zero]
      · rw [if_neg h1, if_neg h1, zero_mul]
    simp only [Matrix.conjTranspose_apply, RCLike.star_def]
    rw [Finset.sum_congr rfl fun j _ ↦ hterm j,
      Finset.sum_ite_eq' Finset.univ i]
    simp only [Finset.mem_univ, if_true]
    by_cases hik : i = k
    · subst hik
      rw [if_pos rfl, Matrix.one_apply_eq, Complex.mul_conj, map_pow, hζn,
        one_pow]
      norm_num
    · rw [if_neg hik, Matrix.one_apply_ne hik]
  · ext i k
    rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
    have hUV : ∀ j : ZMod q,
        (if j = i + 1 then (1 : ℂ) else 0) * (if k = j then ζ ^ (ZMod.val j)
          else 0)
        = if j = i + 1 then (if k = j then ζ ^ (ZMod.val j) else 0) else 0 := by
      intro j
      by_cases h1 : j = i + 1 <;> simp [h1]
    have hVU : ∀ j : ZMod q,
        (if j = i then ζ ^ (ZMod.val i) else 0) * (if k = j + 1 then (1 : ℂ)
          else 0)
        = if j = i then (if k = j + 1 then ζ ^ (ZMod.val i) else 0) else 0 := by
      intro j
      by_cases h1 : j = i <;> simp [h1]
    rw [Finset.sum_congr rfl fun j _ ↦ hUV j,
      Finset.sum_congr rfl fun j _ ↦ hVU j,
      Finset.sum_ite_eq' Finset.univ (i + 1), Finset.sum_ite_eq' Finset.univ i]
    simp only [Finset.mem_univ, if_true]
    by_cases hk : k = i + 1
    · rw [if_pos hk, if_pos hk, pow_val_add_one hq hζ i]
    · rw [if_neg hk, if_neg hk, mul_zero]

end NonsoficGroupsExist
