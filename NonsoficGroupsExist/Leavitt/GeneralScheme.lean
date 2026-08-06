import NonsoficGroupsExist.Leavitt.GeneralRankWords
import NonsoficGroupsExist.Leavitt.LeavittMatrixCompression
import NonsoficGroupsExist.Leavitt.FamilyRankFour

/-!
# The compression scheme in adjacent ranks, at every rank

The manuscript's scheme section works with a nontrivial unital ring `A`
carrying a binary Leavitt family, `m ≥ 2`, `n = m + 1`, and the two matrices
`u` (the comb compressor) and `z` (the involution) of the displayed
definitions.  This module formalizes the algebraic layer of that section at
full generality, characteristic-free:

* `uUnit` — the comb compressor as an explicit unit, with the displayed
  inverse `u'`; `u u' = u' u = 1` is the printed inverse lemma, including
  the telescoping identity `∑ αᵢαᵢ* = 1 − α_nα_n*`;
* `zUnit` — the involution as a self-inverse unit;
* `uMatrix_mul_single` / `single_mul_uMatrix` — conjugation by `u`
  implements the corner compression `b ↦ s₀bt₀` on core transvections;
* `zMatrix_mul_compressed_single` — `z` centralizes compressed core
  transvections;
* `zMatrix_mul_lastRow_single`, `zMatrix_mul_lastColumn_single` —
  conjugation by `z` produces the last-row and last-column roots used for
  generation.

Every identity is a row or column computation against the sparse forms; no
rank-specific case exhaustion appears.  `GeneralCornerTheorem` assembles the
corner theorem from these parts.
-/

namespace NonsoficGroupsExist
namespace GeneralScheme

open GeneralRank

variable {R : Type*} [Ring R] (L : LeavittFamily R) {m : ℕ}

/-! ### Single-entry product helpers -/

section SingleHelpers

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem mul_single_apply (M : Matrix ι ι R) (i j : ι) (a : R) (r c : ι) :
    (M * Matrix.single i j a) r c = if c = j then M r i * a else 0 := by
  classical
  rw [Matrix.mul_apply]
  by_cases hcj : c = j
  · rw [if_pos hcj, Finset.sum_eq_single i]
    · rw [Matrix.single_apply, if_pos ⟨rfl, hcj.symm⟩]
    · intro k _ hki
      rw [Matrix.single_apply, if_neg fun h => hki h.1.symm, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  · rw [if_neg hcj]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Matrix.single_apply, if_neg fun h => hcj h.2.symm, mul_zero]

theorem single_mul_apply (i j : ι) (a : R) (M : Matrix ι ι R) (r c : ι) :
    (Matrix.single i j a * M) r c = if r = i then a * M j c else 0 := by
  classical
  rw [Matrix.mul_apply]
  by_cases hri : r = i
  · rw [if_pos hri, Finset.sum_eq_single j]
    · rw [Matrix.single_apply, if_pos ⟨hri.symm, rfl⟩]
    · intro k _ hkj
      rw [Matrix.single_apply, if_neg fun h => hkj h.2.symm, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ j) h
  · rw [if_neg hri]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Matrix.single_apply, if_neg fun h => hri h.1.symm, zero_mul]

end SingleHelpers

/-! ### Power-collapse identities -/

theorem t0_pow_mul_s0_pow_mul (n : ℕ) (x : R) :
    L.t0 ^ n * (L.s0 ^ n * x) = x := by
  rw [← mul_assoc, L.t0_pow_mul_s0_pow, one_mul]

theorem t1_mul_s0_pow_succ (k : ℕ) : L.t1 * L.s0 ^ (k + 1) = 0 := by
  rw [pow_succ', ← mul_assoc, L.t1_s0, zero_mul]

theorem t1_mul_s0_pow_succ_mul (k : ℕ) (x : R) :
    L.t1 * (L.s0 ^ (k + 1) * x) = 0 := by
  rw [← mul_assoc, t1_mul_s0_pow_succ, zero_mul]

theorem t0_pow_succ_mul_s1 (k : ℕ) : L.t0 ^ (k + 1) * L.s1 = 0 := by
  rw [pow_succ, mul_assoc, L.t0_s1, mul_zero]

theorem t0_pow_succ_mul_s1_mul (k : ℕ) (x : R) :
    L.t0 ^ (k + 1) * (L.s1 * x) = 0 := by
  rw [← mul_assoc, t0_pow_succ_mul_s1, zero_mul]

theorem t0_mul_s1t1_mul (x : R) : L.t0 * (L.s1 * L.t1 * x) = 0 := by
  rw [← mul_assoc, ← mul_assoc, L.t0_s1, zero_mul, zero_mul]

theorem s1t1_mul_s0_mul (x : R) : L.s1 * L.t1 * (L.s0 * x) = 0 := by
  rw [mul_assoc L.s1, ← mul_assoc L.t1, L.t1_s0, zero_mul, mul_zero]

/-- The cross collapse `(s₁t₁t₀^i)(s₀^j s₁t₁)`: one when the powers agree,
zero otherwise. -/
theorem tailCross (i j : ℕ) :
    L.s1 * L.t1 * L.t0 ^ i * (L.s0 ^ j * (L.s1 * L.t1)) =
      if i = j then L.s1 * L.t1 else 0 := by
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [if_neg (Nat.ne_of_lt hij)]
    obtain ⟨d, rfl⟩ : ∃ d, j = i + (d + 1) := ⟨j - i - 1, by omega⟩
    rw [mul_assoc (L.s1 * L.t1), pow_add,
      show L.s0 ^ i * L.s0 ^ (d + 1) * (L.s1 * L.t1) =
        L.s0 ^ i * (L.s0 ^ (d + 1) * (L.s1 * L.t1)) from by
      rw [mul_assoc]]
    rw [t0_pow_mul_s0_pow_mul]
    rw [mul_assoc L.s1, t1_mul_s0_pow_succ_mul, mul_zero]
  · rw [if_pos rfl]
    rw [mul_assoc (L.s1 * L.t1), t0_pow_mul_s0_pow_mul]
    rw [mul_assoc L.s1, show L.t1 * (L.s1 * L.t1) = L.t1 from by
      rw [← mul_assoc, L.t1_s1, one_mul]]
  · rw [if_neg (Nat.ne_of_gt hij)]
    obtain ⟨d, rfl⟩ : ∃ d, i = (d + 1) + j := ⟨i - j - 1, by omega⟩
    rw [pow_add, mul_assoc (L.s1 * L.t1),
      show L.t0 ^ (d + 1) * L.t0 ^ j * (L.s0 ^ j * (L.s1 * L.t1)) =
        L.t0 ^ (d + 1) * (L.t0 ^ j * (L.s0 ^ j * (L.s1 * L.t1))) from by
      rw [mul_assoc]]
    rw [t0_pow_mul_s0_pow_mul, t0_pow_succ_mul_s1_mul, mul_zero]

/-! ### The compressor and its displayed inverse -/

/-- The comb-compressor matrix `u` of the displayed definition. -/
def uMatrix : Matrix (Fin (m + 1)) (Fin (m + 1)) R := combMatrix L m

/-- The displayed inverse `u'`: diagonal `t₀`, last row `s₀^j(s₁t₁)`, corner
`s₀^m`. -/
def uPrimeMatrix : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  Matrix.of fun r c =>
    if r = last m then
      (if c = last m then L.s0 ^ m else L.s0 ^ (c : ℕ) * (L.s1 * L.t1))
    else if c = r then L.t0 else 0

/-! Entry values of `u` and `u'`. -/

theorem uMatrix_apply_core (i : Fin m) (c : Fin (m + 1)) :
    uMatrix L i.castSucc c =
      if c = i.castSucc then L.s0
      else if c = last m then L.s1 * L.t1 * L.t0 ^ (i : ℕ) else 0 := by
  have hi : (i.castSucc : Fin (m + 1)) ≠ last m := castSucc_ne_last i
  simp [uMatrix, combMatrix, hi]

theorem uMatrix_apply_last (c : Fin (m + 1)) :
    uMatrix L (last m) c = if c = last m then L.t0 ^ m else 0 := by
  simp [uMatrix, combMatrix]

theorem uPrimeMatrix_apply_core (i : Fin m) (c : Fin (m + 1)) :
    uPrimeMatrix L i.castSucc c = if c = i.castSucc then L.t0 else 0 := by
  have hi : (i.castSucc : Fin (m + 1)) ≠ last m := castSucc_ne_last i
  simp [uPrimeMatrix, hi]

theorem uPrimeMatrix_apply_last (c : Fin (m + 1)) :
    uPrimeMatrix L (last m) c =
      if c = last m then L.s0 ^ m else L.s0 ^ (c : ℕ) * (L.s1 * L.t1) := by
  simp [uPrimeMatrix]

/-- Rows of `u` at core coordinates are supported on the diagonal entry and
the last column; every product row sum collapses to two terms. -/
theorem uMatrix_row_core_sum (i : Fin m) (f : Fin (m + 1) → R) :
    ∑ k, uMatrix L i.castSucc k * f k =
      L.s0 * f i.castSucc +
        L.s1 * L.t1 * L.t0 ^ (i : ℕ) * f (last m) := by
  rw [sum_split i.castSucc (last m) (castSucc_ne_last i)]
  have h1 : uMatrix L i.castSucc i.castSucc = L.s0 := by
    rw [uMatrix_apply_core, if_pos rfl]
  have h2 : uMatrix L i.castSucc (last m) =
      L.s1 * L.t1 * L.t0 ^ (i : ℕ) := by
    rw [uMatrix_apply_core, if_neg (Ne.symm (castSucc_ne_last i)),
      if_pos rfl]
  have htail : ∑ k ∈ (Finset.univ.erase i.castSucc).erase (last m),
      uMatrix L i.castSucc k * f k = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    have hk1 := Finset.mem_erase.mp hk
    have hk2 := Finset.mem_erase.mp hk1.2
    rw [uMatrix_apply_core, if_neg hk2.1, if_neg hk1.1, zero_mul]
  rw [h1, h2, htail, add_zero]

/-- Rows of `u` at the last coordinate see only the corner. -/
theorem uMatrix_row_last_sum (f : Fin (m + 1) → R) :
    ∑ k, uMatrix L (last m) k * f k = L.t0 ^ m * f (last m) := by
  have hk : ∀ k, uMatrix L (last m) k * f k =
      if k = last m then L.t0 ^ m * f (last m) else 0 := by
    intro k
    rw [uMatrix_apply_last]
    by_cases hk : k = last m
    · subst hk; simp
    · simp [hk]
  rw [Finset.sum_congr rfl fun k _ => hk k]
  simp

/-- Rows of `u'` at core coordinates see only the diagonal. -/
theorem uPrimeMatrix_row_core_sum (i : Fin m) (f : Fin (m + 1) → R) :
    ∑ k, uPrimeMatrix L i.castSucc k * f k = L.t0 * f i.castSucc := by
  have hk : ∀ k, uPrimeMatrix L i.castSucc k * f k =
      if k = i.castSucc then L.t0 * f i.castSucc else 0 := by
    intro k
    rw [uPrimeMatrix_apply_core]
    by_cases hk : k = i.castSucc
    · subst hk; simp
    · simp [hk]
  rw [Finset.sum_congr rfl fun k _ => hk k]
  simp

/-- Rows of `u'` at the last coordinate: the printed row
`(α₁t₁, …, α_mt₁, α_n)`, split off the corner term. -/
theorem uPrimeMatrix_row_last_sum (f : Fin (m + 1) → R) :
    ∑ k, uPrimeMatrix L (last m) k * f k =
      (∑ j : Fin m, L.s0 ^ (j : ℕ) * (L.s1 * L.t1) * f j.castSucc) +
        L.s0 ^ m * f (last m) := by
  rw [Fin.sum_univ_castSucc
    (f := fun k : Fin (m + 1) => uPrimeMatrix L (last m) k * f k)]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [uPrimeMatrix_apply_last, if_neg (castSucc_ne_last j)]
    rfl
  · rw [uPrimeMatrix_apply_last, if_pos rfl]

/-! ### The inverse lemma: `u u' = u' u = 1` -/

/-- `u u' = 1`.  The diagonal collapses by `t₀s₀ = 1`, the tails by the
cross collapse. -/
theorem uMatrix_mul_uPrimeMatrix :
    uMatrix L * uPrimeMatrix L (m := m) = 1 := by
  ext r c
  rw [Matrix.mul_apply]
  refine Fin.lastCases ?_ ?_ r
  · rw [uMatrix_row_last_sum]
    refine Fin.lastCases ?_ ?_ c
    · rw [uPrimeMatrix_apply_last, if_pos rfl, L.t0_pow_mul_s0_pow,
        Matrix.one_apply_eq]
    · intro j
      rw [uPrimeMatrix_apply_last, if_neg (castSucc_ne_last j)]
      obtain ⟨d, hd⟩ : ∃ d, m = (d + 1) + (j : ℕ) :=
        ⟨m - (j : ℕ) - 1, by omega⟩
      rw [show L.t0 ^ m = L.t0 ^ ((d + 1) + (j : ℕ)) from by rw [← hd]]
      rw [pow_add, mul_assoc, Fin.val_castSucc, t0_pow_mul_s0_pow_mul,
        t0_pow_succ_mul_s1_mul,
        Matrix.one_apply_ne (Ne.symm (castSucc_ne_last j))]
  · intro i
    rw [uMatrix_row_core_sum]
    refine Fin.lastCases ?_ ?_ c
    · rw [uPrimeMatrix_apply_core, if_neg (Ne.symm (castSucc_ne_last i)),
        mul_zero, zero_add, uPrimeMatrix_apply_last, if_pos rfl]
      obtain ⟨d, hd⟩ : ∃ d, m = (i : ℕ) + (d + 1) :=
        ⟨m - (i : ℕ) - 1, by omega⟩
      rw [show L.s0 ^ m = L.s0 ^ ((i : ℕ) + (d + 1)) from by rw [← hd]]
      rw [pow_add, mul_assoc (L.s1 * L.t1), t0_pow_mul_s0_pow_mul,
        mul_assoc L.s1, t1_mul_s0_pow_succ, mul_zero,
        Matrix.one_apply_ne (castSucc_ne_last i)]
    · intro j
      rw [uPrimeMatrix_apply_core, uPrimeMatrix_apply_last,
        if_neg (castSucc_ne_last j), tailCross]
      simp only [Fin.val_castSucc]
      by_cases hji : j = i
      · subst hji
        rw [if_pos rfl, if_pos rfl, Matrix.one_apply_eq]
        exact L.sum_range
      · have hcast : (j.castSucc : Fin (m + 1)) ≠ i.castSucc :=
          fun h => hji (Fin.castSucc_inj.mp h)
        rw [if_neg hcast, mul_zero, zero_add,
          if_neg (fun h : (i : ℕ) = (j : ℕ) => hji (Fin.ext h.symm)),
          Matrix.one_apply_ne (fun h => hji (Fin.castSucc_inj.mp h.symm))]

/-- `u' u = 1`.  Core rows collapse by `t₀s₀ = 1`; the last row is the
printed telescoping identity `∑ αᵢαᵢ* + α_nα_n* = 1`. -/
theorem uPrimeMatrix_mul_uMatrix :
    uPrimeMatrix L * uMatrix L (m := m) = 1 := by
  ext r c
  rw [Matrix.mul_apply]
  refine Fin.lastCases ?_ ?_ r
  · rw [uPrimeMatrix_row_last_sum]
    refine Fin.lastCases ?_ ?_ c
    · -- the telescoping entry
      have hterm : ∀ j : Fin m,
          L.s0 ^ (j : ℕ) * (L.s1 * L.t1) * uMatrix L j.castSucc (last m) =
            L.s0 ^ (j : ℕ) * L.t0 ^ (j : ℕ) -
              L.s0 ^ ((j : ℕ) + 1) * L.t0 ^ ((j : ℕ) + 1) := by
        intro j
        rw [uMatrix_apply_core, if_neg (Ne.symm (castSucc_ne_last j)),
          if_pos rfl]
        have hmid : L.s1 * L.t1 * (L.s1 * L.t1 * L.t0 ^ (j : ℕ)) =
            L.s1 * L.t1 * L.t0 ^ (j : ℕ) := by
          rw [← mul_assoc, mul_assoc L.s1, ← mul_assoc L.t1, L.t1_s1,
            one_mul]
        rw [mul_assoc, hmid]
        have hq : L.s1 * L.t1 = 1 - L.s0 * L.t0 :=
          eq_sub_of_add_eq' L.sum_range
        rw [hq, sub_mul, one_mul, mul_sub]
        congr 1
        rw [pow_succ, pow_succ']
        rw [mul_assoc]
        rw [show L.s0 ^ (j : ℕ) * (L.s0 * (L.t0 * L.t0 ^ (j : ℕ))) =
            L.s0 ^ (j : ℕ) * L.s0 * (L.t0 * L.t0 ^ (j : ℕ)) from by
          rw [mul_assoc]]
        rw [show L.s0 ^ (j : ℕ) * L.s0 * (L.t0 * L.t0 ^ (j : ℕ)) =
            L.s0 ^ (j : ℕ) * L.s0 * L.t0 * L.t0 ^ (j : ℕ) from by
          rw [mul_assoc (L.s0 ^ (j : ℕ) * L.s0)]]
        rw [mul_assoc (L.s0 ^ (j : ℕ) * L.s0)]
      rw [Finset.sum_congr rfl fun j _ => hterm j]
      rw [uMatrix_apply_last, if_pos rfl]
      rw [Fin.sum_univ_eq_sum_range
        (fun j => L.s0 ^ j * L.t0 ^ j - L.s0 ^ (j + 1) * L.t0 ^ (j + 1)) m]
      rw [Finset.sum_range_sub'
        (fun j => L.s0 ^ j * L.t0 ^ j) m]
      simp [Matrix.one_apply_eq]
    · intro j
      have hsum : ∀ k : Fin m,
          L.s0 ^ (k : ℕ) * (L.s1 * L.t1) *
              uMatrix L k.castSucc j.castSucc =
            if k = j then L.s0 ^ (j : ℕ) * (L.s1 * L.t1) * L.s0 else 0 := by
        intro k
        rw [uMatrix_apply_core]
        by_cases hkj : k = j
        · subst hkj
          rw [if_pos rfl, if_pos rfl]
        · rw [if_neg (fun h => hkj (Fin.castSucc_inj.mp h.symm)),
            if_neg (castSucc_ne_last j), mul_zero, if_neg hkj]
      rw [Finset.sum_congr rfl fun k _ => hsum k]
      rw [uMatrix_apply_last, if_neg (castSucc_ne_last j), mul_zero,
        add_zero]
      rw [Finset.sum_ite_eq' Finset.univ j
        (fun _ => L.s0 ^ (j : ℕ) * (L.s1 * L.t1) * L.s0),
        if_pos (Finset.mem_univ j)]
      rw [mul_assoc (L.s0 ^ (j : ℕ)), mul_assoc L.s1, L.t1_s0, mul_zero,
        mul_zero]
      rw [Matrix.one_apply_ne (Ne.symm (castSucc_ne_last j))]
  · intro i
    rw [uPrimeMatrix_row_core_sum]
    refine Fin.lastCases ?_ ?_ c
    · rw [uMatrix_apply_core, if_neg (Ne.symm (castSucc_ne_last i)),
        if_pos rfl, t0_mul_s1t1_mul,
        Matrix.one_apply_ne (castSucc_ne_last i)]
    · intro j
      rw [uMatrix_apply_core]
      by_cases hji : j = i
      · subst hji
        rw [if_pos rfl, L.t0_s0, Matrix.one_apply_eq]
      · rw [if_neg (fun h => hji (Fin.castSucc_inj.mp h)),
          if_neg (castSucc_ne_last j), mul_zero,
          Matrix.one_apply_ne (fun h => hji (Fin.castSucc_inj.mp h.symm))]

/-- The comb compressor as an explicit unit, with the displayed inverse. -/
def uUnit : (Matrix (Fin (m + 1)) (Fin (m + 1)) R)ˣ where
  val := uMatrix L
  inv := uPrimeMatrix L
  val_inv := uMatrix_mul_uPrimeMatrix L
  inv_val := uPrimeMatrix_mul_uMatrix L

/-- The involution matrix `z`, characteristic-free. -/
def zMatrix (_hm : 0 < m) : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  planeMatrix 0 (last m) !![L.p0, L.s1; L.t1, 0]

theorem zMatrix_mul_self (hm : 0 < m) :
    zMatrix L hm * zMatrix L hm = 1 := by
  rw [zMatrix, planeMatrix_mul _ _ (zero_ne_last hm),
    twoByTwo_involution_sq L, planeMatrix_one _ _ (zero_ne_last hm)]

/-- The involution as a self-inverse unit, characteristic-free. -/
def zUnit (hm : 0 < m) : (Matrix (Fin (m + 1)) (Fin (m + 1)) R)ˣ where
  val := zMatrix L hm
  inv := zMatrix L hm
  val_inv := zMatrix_mul_self L hm
  inv_val := zMatrix_mul_self L hm

/-! ### Entries of the involution -/

theorem zMatrix_apply_col_zero (hm : 0 < m) (r : Fin (m + 1)) :
    zMatrix L hm r 0 =
      if r = 0 then L.p0 else if r = last m then L.t1 else 0 := by
  by_cases hr0 : r = 0
  · subst hr0
    rw [if_pos rfl]
    exact planeMatrix_apply_ii 0 (last m) _
  · rw [if_neg hr0]
    by_cases hrl : r = last m
    · subst hrl
      rw [if_pos rfl]
      exact planeMatrix_apply_ji 0 (last m) _ (zero_ne_last hm)
    · rw [if_neg hrl, zMatrix,
        planeMatrix_apply_off 0 (last m) _ hr0 hrl, if_neg hr0]

theorem zMatrix_apply_col_core (hm : 0 < m) {p : Fin (m + 1)} (hp0 : p ≠ 0)
    (hpl : p ≠ last m) (r : Fin (m + 1)) :
    zMatrix L hm r p = if r = p then 1 else 0 := by
  by_cases hr0 : r = 0
  · subst hr0
    rw [zMatrix, planeMatrix_apply_row_i 0 (last m) _ hp0 hpl,
      if_neg (fun h => hp0 h.symm)]
  · by_cases hrl : r = last m
    · subst hrl
      rw [zMatrix, planeMatrix_apply_row_j 0 (last m) _ (zero_ne_last hm) hp0 hpl,
        if_neg (fun h => hpl h.symm)]
    · rw [zMatrix, planeMatrix_apply_off 0 (last m) _ hr0 hrl]

theorem zMatrix_apply_row_zero (hm : 0 < m) (c : Fin (m + 1)) :
    zMatrix L hm 0 c =
      if c = 0 then L.p0 else if c = last m then L.s1 else 0 := by
  by_cases hc0 : c = 0
  · subst hc0
    rw [if_pos rfl]
    exact planeMatrix_apply_ii 0 (last m) _
  · rw [if_neg hc0]
    by_cases hcl : c = last m
    · subst hcl
      rw [if_pos rfl]
      exact planeMatrix_apply_ij 0 (last m) _ (zero_ne_last hm)
    · rw [if_neg hcl, zMatrix, planeMatrix]
      simp [hc0, hcl]

theorem zMatrix_apply_row_last (hm : 0 < m) (c : Fin (m + 1)) :
    zMatrix L hm (last m) c = if c = 0 then L.t1 else 0 := by
  by_cases hc0 : c = 0
  · subst hc0
    rw [if_pos rfl]
    exact planeMatrix_apply_ji 0 (last m) _ (zero_ne_last hm)
  · rw [if_neg hc0]
    by_cases hcl : c = last m
    · subst hcl
      exact planeMatrix_apply_jj 0 (last m) _ (zero_ne_last hm)
    · rw [zMatrix, planeMatrix_apply_row_j 0 (last m) _ (zero_ne_last hm)
        hc0 hcl]

theorem zMatrix_apply_row_core (hm : 0 < m) {p : Fin (m + 1)} (hp0 : p ≠ 0)
    (hpl : p ≠ last m) (c : Fin (m + 1)) :
    zMatrix L hm p c = if p = c then 1 else 0 := by
  rw [zMatrix, planeMatrix_apply_off 0 (last m) _ hp0 hpl]

/-! ### Conjugation by the compressor: coefficient compression -/

/-- Multiplying a core single past `u` compresses the coefficient. -/
theorem uMatrix_mul_single (i j : Fin m) (b : R) :
    uMatrix L * Matrix.single i.castSucc j.castSucc b =
      Matrix.single i.castSucc j.castSucc (L.s0 * b * L.t0) * uMatrix L := by
  ext r c
  rw [mul_single_apply, single_mul_apply]
  by_cases hri : r = i.castSucc
  · subst hri
    by_cases hcj : c = j.castSucc
    · subst hcj
      rw [if_pos rfl, if_pos rfl]
      have h1 : uMatrix L i.castSucc i.castSucc = L.s0 := by
        rw [uMatrix_apply_core, if_pos rfl]
      have h2 : uMatrix L j.castSucc j.castSucc = L.s0 := by
        rw [uMatrix_apply_core, if_pos rfl]
      rw [h1, h2, mul_assoc (L.s0 * b), L.t0_s0, mul_one]
    · rw [if_neg hcj, if_pos rfl]
      by_cases hcl : c = last m
      · subst hcl
        have h2 : uMatrix L j.castSucc (last m) =
            L.s1 * L.t1 * L.t0 ^ (j : ℕ) := by
          rw [uMatrix_apply_core, if_neg (Ne.symm (castSucc_ne_last j)),
            if_pos rfl]
        have hzero : L.t0 * (L.s1 * L.t1 * L.t0 ^ (j : ℕ)) = 0 := by
          rw [← mul_assoc, ← mul_assoc, L.t0_s1, zero_mul, zero_mul]
        rw [h2, mul_assoc, mul_assoc, hzero, mul_zero, mul_zero]
      · have h2 : uMatrix L j.castSucc c = 0 := by
          rw [uMatrix_apply_core, if_neg hcj, if_neg hcl]
        rw [h2, mul_zero]
  · rw [if_neg hri]
    by_cases hcj : c = j.castSucc
    · rw [if_pos hcj]
      have h1 : uMatrix L r i.castSucc = 0 := by
        rcases Fin.eq_castSucc_or_eq_last r with ⟨k, rfl⟩ | rfl
        · rw [uMatrix_apply_core, if_neg (fun h => hri h.symm),
            if_neg (castSucc_ne_last i)]
        · rw [uMatrix_apply_last, if_neg (castSucc_ne_last i)]
      rw [h1, zero_mul]
    · rw [if_neg hcj]

/-- Conjugation by the compressor unit implements coefficient compression on
core transvections, in mul-past form. -/
theorem uUnit_mul_elementaryUnit (i j : Fin m)
    (hij : i.castSucc ≠ (j.castSucc : Fin (m + 1))) (b : R) :
    uUnit L * elementaryUnit i.castSucc j.castSucc hij b =
      elementaryUnit i.castSucc j.castSucc hij (L.s0 * b * L.t0) *
        uUnit L := by
  apply Units.ext
  show uMatrix L * (1 + Matrix.single i.castSucc j.castSucc b) =
    (1 + Matrix.single i.castSucc j.castSucc (L.s0 * b * L.t0)) * uMatrix L
  rw [mul_add, add_mul, mul_one, one_mul, uMatrix_mul_single]

/-! ### The involution centralizes the compressed core -/

/-- The involution fixes every compressed single on the left. -/
theorem zMatrix_mul_compressed_single (hm : 0 < m) (i j : Fin m) (b : R) :
    zMatrix L hm * Matrix.single i.castSucc j.castSucc (L.s0 * b * L.t0) =
      Matrix.single i.castSucc j.castSucc (L.s0 * b * L.t0) := by
  ext r c
  rw [mul_single_apply, Matrix.single_apply]
  by_cases hcj : c = j.castSucc
  · rw [if_pos hcj]
    have hcol : zMatrix L hm r i.castSucc * (L.s0 * b * L.t0) =
        if i.castSucc = r then L.s0 * b * L.t0 else 0 := by
      by_cases hi0 : (i.castSucc : Fin (m + 1)) = 0
      · rw [hi0]
        rw [zMatrix_apply_col_zero]
        by_cases hr0 : r = 0
        · subst hr0
          rw [if_pos rfl, if_pos rfl]
          rw [show L.p0 * (L.s0 * b * L.t0) = L.s0 * b * L.t0 from by
            rw [LeavittFamily.p0, mul_assoc L.s0, ← mul_assoc L.t0,
              L.t0_s0, one_mul, ← mul_assoc]]
        · rw [if_neg hr0, if_neg (fun h => hr0 h.symm)]
          by_cases hrl : r = last m
          · rw [if_pos hrl]
            rw [show L.t1 * (L.s0 * b * L.t0) = 0 from by
              rw [← mul_assoc, L.t1_s0, zero_mul, zero_mul]]
          · rw [if_neg hrl, zero_mul]
      · rw [zMatrix_apply_col_core L hm hi0 (castSucc_ne_last i)]
        by_cases hri : r = i.castSucc
        · rw [if_pos hri, if_pos hri.symm, one_mul]
        · rw [if_neg hri, if_neg (fun h => hri h.symm), zero_mul]
    rw [hcol]
    by_cases hic : (i.castSucc : Fin (m + 1)) = r
    · rw [if_pos hic, if_pos ⟨hic, hcj.symm⟩]
    · rw [if_neg hic, if_neg (fun h => hic h.1)]
  · rw [if_neg hcj, if_neg (fun h => hcj h.2.symm)]

/-- The involution fixes every compressed single on the right. -/
theorem compressed_single_mul_zMatrix (hm : 0 < m) (i j : Fin m) (b : R) :
    Matrix.single i.castSucc j.castSucc (L.s0 * b * L.t0) * zMatrix L hm =
      Matrix.single i.castSucc j.castSucc (L.s0 * b * L.t0) := by
  ext r c
  rw [single_mul_apply, Matrix.single_apply]
  by_cases hri : r = i.castSucc
  · rw [if_pos hri]
    have hrow : L.s0 * b * L.t0 * zMatrix L hm j.castSucc c =
        if j.castSucc = c then L.s0 * b * L.t0 else 0 := by
      by_cases hj0 : (j.castSucc : Fin (m + 1)) = 0
      · rw [hj0, zMatrix_apply_row_zero]
        by_cases hc0 : c = 0
        · subst hc0
          rw [if_pos rfl, if_pos hj0]
          rw [show L.s0 * b * L.t0 * L.p0 = L.s0 * b * L.t0 from by
            rw [LeavittFamily.p0, mul_assoc (L.s0 * b), ← mul_assoc L.t0,
              L.t0_s0, one_mul, ← mul_assoc]]
        · rw [if_neg hc0, if_neg (fun h => hc0 (hj0 ▸ h))]
          by_cases hcl : c = last m
          · rw [if_pos hcl]
            rw [show L.s0 * b * L.t0 * L.s1 = 0 from by
              rw [mul_assoc (L.s0 * b), L.t0_s1, mul_zero]]
          · rw [if_neg hcl, mul_zero]
      · rw [zMatrix_apply_row_core L hm hj0 (castSucc_ne_last j)]
        by_cases hjc : (j.castSucc : Fin (m + 1)) = c
        · rw [if_pos hjc, if_pos hjc, mul_one]
        · rw [if_neg hjc, if_neg hjc, mul_zero]
    rw [hrow]
    by_cases hjc : (j.castSucc : Fin (m + 1)) = c
    · rw [if_pos hjc, if_pos ⟨hri.symm, hjc⟩]
    · rw [if_neg hjc, if_neg (fun h => hjc h.2)]
  · rw [if_neg hri, if_neg (fun h => hri h.1.symm)]

/-- **The involution centralizes the compressed core**, at the level of
transvections and in every characteristic. -/
theorem zUnit_commute_compressed (hm : 0 < m) (i j : Fin m)
    (hij : i.castSucc ≠ (j.castSucc : Fin (m + 1))) (b : R) :
    Commute (zUnit L hm)
      (elementaryUnit i.castSucc j.castSucc hij (L.s0 * b * L.t0)) := by
  apply Units.ext
  show zMatrix L hm *
      (1 + Matrix.single i.castSucc j.castSucc (L.s0 * b * L.t0)) =
    (1 + Matrix.single i.castSucc j.castSucc (L.s0 * b * L.t0)) *
      zMatrix L hm
  rw [mul_add, add_mul, mul_one, one_mul, zMatrix_mul_compressed_single,
    compressed_single_mul_zMatrix]

/-! ### Conjugation by the involution: the last-row and last-column roots -/

/-- `z · x₀ⱼ(s₁a) = x_{nⱼ}(a) · z` for a core column `j` with
`j.castSucc ≠ 0`. -/
theorem zMatrix_mul_lastRow_single (hm : 0 < m) (j : Fin m)
    (hj0 : (j.castSucc : Fin (m + 1)) ≠ 0) (a : R) :
    zMatrix L hm * Matrix.single 0 j.castSucc (L.s1 * a) =
      Matrix.single (last m) j.castSucc a * zMatrix L hm := by
  ext r c
  rw [mul_single_apply, single_mul_apply]
  by_cases hcj : c = j.castSucc
  · rw [if_pos hcj]
    rw [zMatrix_apply_col_zero]
    by_cases hrl : r = last m
    · rw [if_pos hrl, if_neg (fun h : r = 0 => by
        rw [h] at hrl
        exact (zero_ne_last hm) hrl), if_pos rfl]
      rw [zMatrix_apply_row_core L hm hj0 (castSucc_ne_last j),
        if_pos hcj.symm, mul_one, ← mul_assoc, L.t1_s1, one_mul]
    · rw [if_neg hrl]
      by_cases hr0 : r = 0
      · rw [if_pos hr0, if_neg hrl]
        rw [show L.p0 * (L.s1 * a) = 0 from by
          rw [LeavittFamily.p0, mul_assoc L.s0, ← mul_assoc L.t0,
            L.t0_s1, zero_mul, mul_zero]]
      · rw [if_neg hr0, if_neg hrl, zero_mul]
  · rw [if_neg hcj]
    by_cases hrl : r = last m
    · rw [if_pos hrl]
      rw [zMatrix_apply_row_core L hm hj0 (castSucc_ne_last j),
        if_neg (fun h => hcj h.symm), mul_zero]
    · rw [if_neg hrl]

/-- `z · xᵢ₀(at₁) = x_{iₙ}(a) · z` for a core row `i` with
`i.castSucc ≠ 0`. -/
theorem zMatrix_mul_lastColumn_single (hm : 0 < m) (i : Fin m)
    (hi0 : (i.castSucc : Fin (m + 1)) ≠ 0) (a : R) :
    zMatrix L hm * Matrix.single i.castSucc 0 (a * L.t1) =
      Matrix.single i.castSucc (last m) a * zMatrix L hm := by
  ext r c
  rw [mul_single_apply, single_mul_apply]
  by_cases hri : r = i.castSucc
  · rw [if_pos hri]
    by_cases hc0 : c = 0
    · rw [if_pos hc0]
      rw [zMatrix_apply_col_core L hm hi0 (castSucc_ne_last i),
        if_pos hri.symm, one_mul]
      rw [zMatrix_apply_row_last, if_pos hc0, ← mul_assoc]
    · rw [if_neg hc0]
      rw [zMatrix_apply_row_last, if_neg hc0, mul_zero]
  · rw [if_neg hri]
    by_cases hc0 : c = 0
    · rw [if_pos hc0,
        zMatrix_apply_col_core L hm hi0 (castSucc_ne_last i),
        if_neg hri, zero_mul]
    · rw [if_neg hc0]

/-- Conjugation form of the last-row identity: `z x₀ⱼ(s₁a) z = x_{nⱼ}(a)`,
using `z² = 1`. -/
theorem zUnit_conj_lastRow (hm : 0 < m) (j : Fin m)
    (hj0 : (j.castSucc : Fin (m + 1)) ≠ 0)
    (h0j : (0 : Fin (m + 1)) ≠ j.castSucc)
    (hlj : (last m : Fin (m + 1)) ≠ j.castSucc) (a : R) :
    zUnit L hm * elementaryUnit 0 j.castSucc h0j (L.s1 * a) * zUnit L hm =
      elementaryUnit (last m) j.castSucc hlj a := by
  apply Units.ext
  show zMatrix L hm * (1 + Matrix.single 0 j.castSucc (L.s1 * a)) *
      zMatrix L hm = 1 + Matrix.single (last m) j.castSucc a
  rw [mul_add, mul_one, zMatrix_mul_lastRow_single L hm j hj0, add_mul,
    mul_assoc, zMatrix_mul_self, mul_one, zMatrix_mul_self]

/-- Conjugation form of the last-column identity:
`z xᵢ₀(at₁) z = x_{iₙ}(a)`. -/
theorem zUnit_conj_lastColumn (hm : 0 < m) (i : Fin m)
    (hi0 : (i.castSucc : Fin (m + 1)) ≠ 0)
    (hil : (i.castSucc : Fin (m + 1)) ≠ last m) (a : R) :
    zUnit L hm * elementaryUnit i.castSucc 0 hi0 (a * L.t1) * zUnit L hm =
      elementaryUnit i.castSucc (last m) hil a := by
  apply Units.ext
  show zMatrix L hm * (1 + Matrix.single i.castSucc 0 (a * L.t1)) *
      zMatrix L hm = 1 + Matrix.single i.castSucc (last m) a
  rw [mul_add, mul_one, zMatrix_mul_lastColumn_single L hm i hi0, add_mul,
    mul_assoc, zMatrix_mul_self, mul_one, zMatrix_mul_self]

end GeneralScheme
end NonsoficGroupsExist
