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

/-! ## The two prices of a scalar -/

/-- **A scalar costs Hilbert--Schmidt only `|1 - ζ|²`.**  Multiplying every
phase of a monomial matrix by `ζ` moves it by exactly that much, which is
arbitrarily small for `ζ` near one. -/
theorem hsDistSq_monomial_const (Y : FiniteModel) {d : Y → ℂ}
    (hd : ∀ i, Complex.normSq (d i) = 1) (σ : Equiv.Perm Y) (ζ : ℂ)
    (hY : 0 < Fintype.card Y) :
    hsDistSq Y (monomialMatrix Y d σ) (monomialMatrix Y (fun y ↦ ζ * d y) σ)
      = Complex.normSq (1 - ζ) := by
  classical
  have hc : (Fintype.card Y : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hY.ne'
  have hrow : ∀ i : Y, (∑ j : Y, Complex.normSq (monomialMatrix Y d σ i j
      - monomialMatrix Y (fun y ↦ ζ * d y) σ i j))
      = Complex.normSq (1 - ζ) := by
    intro i
    have hterm : ∀ j : Y, Complex.normSq (monomialMatrix Y d σ i j
        - monomialMatrix Y (fun y ↦ ζ * d y) σ i j)
        = if σ i = j then Complex.normSq (1 - ζ) else 0 := by
      intro j
      rw [monomialMatrix_apply, monomialMatrix_apply]
      by_cases h : σ i = j
      · rw [if_pos h, if_pos h, if_pos h]
        have : d i - ζ * d i = (1 - ζ) * d i := by ring
        rw [this, Complex.normSq_mul, hd i, mul_one]
      · rw [if_neg h, if_neg h, if_neg h, sub_zero]
        simp
    rw [Finset.sum_congr rfl fun j _ ↦ hterm j,
      Finset.sum_ite_eq Finset.univ (σ i)]
    simp
  rw [hsDistSq, Finset.sum_congr rfl fun i _ ↦ hrow i, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_comm, mul_div_assoc, div_self hc,
    mul_one]

/-- **A scalar costs untwisting the whole model.**  Shifting every phase by a
nonzero constant leaves the permutation part untouched and changes the second
coordinate everywhere, so the untwisted permutations disagree at every point.
This is why the scalar cocycle of a projective model cannot be untwisted: it is
invisible to the Hilbert--Schmidt metric and maximal in Hamming. -/
theorem hammingDistance_wreathPerm_const (Y : FiniteModel) (m : ℕ) [NeZero m]
    (d : Y → ZMod m) (σ : Equiv.Perm Y) {c : ZMod m} (hc : c ≠ 0)
    (hY : 0 < Fintype.card Y) :
    hammingDistance (wreathModel Y m) (wreathPerm Y m d σ)
      (wreathPerm Y m (fun y ↦ d y + c) σ) = 1 := by
  classical
  rw [hammingDistance_wreathPerm]
  have hall : (Finset.univ.filter fun y : Y ↦ ¬ (σ y = σ y ∧ d y = d y + c))
      = Finset.univ := by
    ext y
    constructor
    · intro _
      exact Finset.mem_univ y
    · intro _
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ y, ?_⟩
      intro hcon
      exact hc (by linear_combination -hcon.2)
  rw [hall, Finset.card_univ]
  field_simp

/-- **Maximal metric separation with zero combinatorial separation.**  On any
nonempty model the monomial matrices with the same permutation part and phases
`1` and `-1` sit at the *maximal* Hilbert--Schmidt distance `4`, while their
permutation parts are equal, so their untwisted permutations coincide and no
model derived from them separates the pair at all.

This is the obstruction in one line.  Hilbert--Schmidt separation, which is
what hyperlinearity supplies, gives no Hamming separation whatever, which is
what soficity demands: by `isSofic_iff_monomial` the passage from hyperlinear
to sofic is exactly the passage from metric to combinatorial agreement of
phases, and here a pair is metrically as far apart as a pair can be while
combinatorially identical. -/
theorem hsDistSq_max_of_equal_perm (Y : FiniteModel) (hY : 0 < Fintype.card Y)
    (σ : Equiv.Perm Y) :
    hsDistSq Y (monomialMatrix Y (fun _ ↦ 1) σ)
        (monomialMatrix Y (fun _ ↦ -1) σ) = 4
      ∧ hammingDistance Y σ σ = 0 := by
  constructor
  · have hd : ∀ i : Y, Complex.normSq ((fun _ : Y ↦ (1 : ℂ)) i) = 1 := by
      intro i; simp
    have hrw : (fun _ : Y ↦ (-1 : ℂ))
        = fun y : Y ↦ (-1 : ℂ) * (fun _ : Y ↦ (1 : ℂ)) y := by
      funext y; ring
    rw [hrw, hsDistSq_monomial_const Y hd σ (-1) hY]
    simp [Complex.normSq_apply]
    norm_num
  · exact hammingDistance_self Y σ

end NonsoficGroupsExist
