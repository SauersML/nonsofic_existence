import NonsoficGroupsExist.Leavitt.PlaneEmbedding
import NonsoficGroupsExist.Leavitt.Leavitt

/-!
# The comb compressor and the involution at every rank

The manuscript's explicit factorizations, at their printed generality.  Fix
`m ≥ 1`, put `n = m + 1`, and work in characteristic two, where the displays
live.  In the coordinates `(i, n)`:

  `Uᵢ = x_{ni}(1+t₀) · x_{in}(1) · x_{ni}(1+s₀) · x_{in}(t₀)`,

a product of four elementary transvections whose value is the two-by-two
compressor block `[[s₀, s₁t₁], [0, t₀]]` in the plane `(i, n)`; and

  `u = U_m · U_{m-1} ⋯ U_1`,

whose value is computed by the printed row induction:

  `P_k = ∑_{i≤k} (s₀E_{ii} + s₁t₁t₀^{i-1}E_{in}) + ∑_{k<i≤m} E_{ii} + t₀^k E_{nn}`.

Likewise the involution

  `z = x_{1n}(s₁) · x_{n1}(t₁) · x_{1n}(s₁)`

has value `[[p₀, s₁], [t₁, 0]]` in the plane `(1, n)` and squares to the
identity.  All matrix computations go through `PlaneEmbedding`: the
two-by-two identities are verified by finite enumeration, and the plane
embedding transports them to every rank at once — no rank-specific case
exhaustion appears anywhere.
-/

namespace NonsoficGroupsExist
namespace GeneralRank

variable {R : Type*} [Ring R] (L : LeavittFamily R) {m : ℕ}

/-- The last coordinate. -/
abbrev last (m : ℕ) : Fin (m + 1) := Fin.last m

theorem castSucc_ne_last (i : Fin m) : (i.castSucc : Fin (m + 1)) ≠ last m :=
  (Fin.castSucc_lt_last i).ne

/-! ### The two-by-two identities, in characteristic two -/

section TwoByTwo

variable [CharP R 2]

/-- In characteristic two a repeated summand cancels through a right-nested
sum, which is the shape `simp` leaves the block products in. -/
private theorem add_add_cancel_left (a b : R) : a + (a + b) = b := by
  rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

omit [CharP R 2] in
/-- `p₀ = s₀t₀` is idempotent, in the association `simp` produces. -/
private theorem s0t0_mul_s0t0 : L.s0 * (L.t0 * (L.s0 * L.t0)) = L.s0 * L.t0 := by
  rw [← mul_assoc L.t0, L.t0_s0, one_mul]

omit [CharP R 2] in
/-- `t₀s₁ = 0`, in the association `simp` produces. -/
private theorem t0_mul_s1t1 : L.t0 * (L.s1 * L.t1) = 0 := by
  rw [← mul_assoc, L.t0_s1, zero_mul]

omit [CharP R 2] in
/-- `t₁s₀ = 0`, in the association `simp` produces. -/
private theorem t1_mul_s0t0 : L.t1 * (L.s0 * L.t0) = 0 := by
  rw [← mul_assoc, L.t1_s0, zero_mul]

/-- The four-transvection product is the compressor block: printed
Lemma (b) of the characteristic-two section, reassociated for the plane
embedding. -/
theorem twoByTwo_comb :
    (!![1, 0; 1 + L.t0, 1] : Matrix (Fin 2) (Fin 2) R) *
        (!![1, (1 : R); 0, 1] *
          (!![1, 0; 1 + L.s0, 1] * !![1, L.t0; 0, 1])) =
      !![L.s0, L.s1 * L.t1; 0, L.t0] := by
  have hts : L.t0 * L.s0 = 1 := L.t0_s0
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, mul_add, add_mul, hts,
      L.s0t0_add_one, CharTwo.add_self_eq_zero, add_add_cancel_left,
      add_assoc, add_comm, add_left_comm, t0_mul_s1t1]

/-- The three-transvection product is the involution block: printed
Lemma (a) of the characteristic-two section, reassociated for the plane
embedding. -/
theorem twoByTwo_involution :
    (!![1, L.s1; 0, 1] : Matrix (Fin 2) (Fin 2) R) *
        (!![1, 0; L.t1, 1] * !![1, L.s1; 0, 1]) =
      !![L.p0, L.s1; L.t1, 0] := by
  have hts : L.t1 * L.s1 = 1 := L.t1_s1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hts, LeavittFamily.p0,
      L.one_add_s1t1, CharTwo.add_self_eq_zero, add_comm]

omit [CharP R 2] in
/-- The involution block squares to the identity, in every characteristic. -/
theorem twoByTwo_involution_sq :
    (!![L.p0, L.s1; L.t1, 0] : Matrix (Fin 2) (Fin 2) R) *
        !![L.p0, L.s1; L.t1, 0] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, LeavittFamily.p0,
      mul_assoc, L.t0_s1, L.t1_s1, s0t0_mul_s0t0, t1_mul_s0t0,
      L.sum_range]

end TwoByTwo

/-! ### The pieces -/

section Pieces

variable [CharP R 2]

/-- The printed piece `Uᵢ = x_{ni}(1+t₀) x_{in}(1) x_{ni}(1+s₀) x_{in}(t₀)`,
as a product of four elementary transvections at rank `m + 1`. -/
def piece (i : Fin m) : (Matrix (Fin (m + 1)) (Fin (m + 1)) R)ˣ :=
  elementaryUnit (last m) i.castSucc (castSucc_ne_last i).symm (1 + L.t0) *
    (elementaryUnit i.castSucc (last m) (castSucc_ne_last i) 1 *
      (elementaryUnit (last m) i.castSucc (castSucc_ne_last i).symm (1 + L.s0) *
        elementaryUnit i.castSucc (last m) (castSucc_ne_last i) L.t0))

omit [CharP R 2] in
theorem piece_mem (i : Fin m) :
    piece L i ∈ elementaryGroup (Fin (m + 1)) R := by
  refine Subgroup.mul_mem _ (elementaryUnit_mem _ _ _ _)
    (Subgroup.mul_mem _ (elementaryUnit_mem _ _ _ _)
      (Subgroup.mul_mem _ (elementaryUnit_mem _ _ _ _)
        (elementaryUnit_mem _ _ _ _)))

/-- The value of a piece: the compressor block in the plane `(i, n)`. -/
theorem piece_val (i : Fin m) :
    ((piece L i : (Matrix (Fin (m + 1)) (Fin (m + 1)) R)ˣ) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) R) =
      planeMatrix i.castSucc (last m) !![L.s0, L.s1 * L.t1; 0, L.t0] := by
  have hne := castSucc_ne_last i
  rw [piece]
  rw [Units.val_mul, Units.val_mul, Units.val_mul]
  rw [elementaryUnit_val_planeMatrix' i.castSucc (last m) hne (1 + L.t0)]
  rw [elementaryUnit_val_planeMatrix i.castSucc (last m) hne 1]
  rw [elementaryUnit_val_planeMatrix' i.castSucc (last m) hne (1 + L.s0)]
  rw [elementaryUnit_val_planeMatrix i.castSucc (last m) hne L.t0]
  rw [planeMatrix_mul _ _ hne, planeMatrix_mul _ _ hne,
    planeMatrix_mul _ _ hne]
  rw [twoByTwo_comb L]

end Pieces

/-! ### The comb and the printed row induction -/

section Comb

variable [CharP R 2]

/-- The partial products `P_k = U_k ⋯ U_1` (zero-indexed:
`partialComb (k+1) = Uₖ · partialComb k`). -/
def partialComb : ℕ → (Matrix (Fin (m + 1)) (Fin (m + 1)) R)ˣ
  | 0 => 1
  | k + 1 =>
      if h : k < m then piece L ⟨k, h⟩ * partialComb k else partialComb k

/-- The comb compressor `u = U_m ⋯ U_1`. -/
def comb : (Matrix (Fin (m + 1)) (Fin (m + 1)) R)ˣ := partialComb L m

omit [CharP R 2] in
theorem partialComb_mem (k : ℕ) :
    partialComb L k ∈ elementaryGroup (Fin (m + 1)) R := by
  induction k with
  | zero => exact Subgroup.one_mem _
  | succ k ih =>
      rw [partialComb]
      split
      · exact Subgroup.mul_mem _ (piece_mem L _) ih
      · exact ih

omit [CharP R 2] in
/-- **The comb compressor is elementary at every rank**: `u ∈ EL_{m+1}(R)`,
as a product of `4m` explicit transvections. -/
theorem comb_mem : comb L (m := m) ∈ elementaryGroup (Fin (m + 1)) R :=
  partialComb_mem L m

/-- The printed partial-product matrix
`P_k = ∑_{i<k} (s₀Eᵢᵢ + s₁t₁t₀^{i}E_{i,n}) + ∑_{k≤i<m} Eᵢᵢ + t₀^k E_{nn}`,
written entrywise (indices zero-based). -/
def combMatrix (k : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  Matrix.of fun r c =>
    if r = last m then (if c = last m then L.t0 ^ k else 0)
    else if (r : ℕ) < k then
      (if c = r then L.s0
        else if c = last m then L.s1 * L.t1 * L.t0 ^ (r : ℕ) else 0)
    else if c = r then 1 else 0

omit [CharP R 2] in
theorem combMatrix_zero : combMatrix L (m := m) 0 = 1 := by
  ext r c
  by_cases hr : r = last m
  · rw [hr]
    by_cases hc : c = last m
    · rw [hc]
      simp [combMatrix]
    · simp [combMatrix, hc, eq_comm]
  · simp [combMatrix, hr, Matrix.one_apply, eq_comm]

/-- The printed row induction, in one step: multiplying `P_k` by `U_k`
compresses row `k`, scales the last row by `t₀`, and fixes every other
row. -/
theorem partialComb_val (k : ℕ) (hk : k ≤ m) :
    ((partialComb L k : (Matrix (Fin (m + 1)) (Fin (m + 1)) R)ˣ) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) R) = combMatrix L k := by
  induction k with
  | zero =>
      rw [partialComb, combMatrix_zero]
      rfl
  | succ k ih =>
      have hklt : k < m := lt_of_lt_of_le (Nat.lt_succ_self k) hk
      have hkle : k ≤ m := le_of_lt hklt
      rw [partialComb, dif_pos hklt, Units.val_mul, piece_val, ih hkle]
      set p : Fin (m + 1) := (⟨k, hklt⟩ : Fin m).castSucc with hp
      have hpval : (p : ℕ) = k := rfl
      have hpne : p ≠ last m := castSucc_ne_last _
      ext r c
      by_cases hrlast : r = last m
      · subst hrlast
        rw [planeMatrix_mul_apply_j p (last m) hpne _ _ c]
        have h1 : (combMatrix L k) p c = if c = p then 1 else 0 := by
          simp [combMatrix, hpne, hpval]
        have h2 : (combMatrix L k) (last m) c =
            if c = last m then L.t0 ^ k else 0 := by
          simp [combMatrix]
        rw [h1, h2]
        by_cases hc : c = last m
        · subst hc
          simp [combMatrix, pow_succ']
        · simp [combMatrix, hc, mul_ite, mul_zero, mul_one]
      · by_cases hrp : r = p
        · subst hrp
          rw [planeMatrix_mul_apply_i p (last m) hpne _ _ c]
          have h1 : (combMatrix L k) p c = if c = p then 1 else 0 := by
            simp [combMatrix, hrlast, hpval]
          have h2 : (combMatrix L k) (last m) c =
              if c = last m then L.t0 ^ k else 0 := by
            simp [combMatrix]
          rw [h1, h2]
          by_cases hc : c = p
          · subst hc
            simp [combMatrix, hrlast, hpval]
          · by_cases hclast : c = last m
            · subst hclast
              simp [combMatrix, hrlast, hpval, hc,
                mul_assoc]
            · simp [combMatrix, hrlast, hpval, hc, hclast]
        · rw [planeMatrix_mul_apply_off p (last m) _ _ hrp hrlast c]
          have hrk : (r : ℕ) ≠ k := by
            intro hcon
            exact hrp (Fin.ext (by rw [hcon, hpval]))
          by_cases hrlt : (r : ℕ) < k
          · simp [combMatrix, hrlast, hrlt]
            exact fun h => absurd h (by omega)
          · simp [combMatrix, hrlast, hrlt]
            exact fun h => absurd h (by omega)

/-- **The printed value of the comb compressor**: `u = P_m`, the matrix of
`(eq:udef)` with `t₀`-power tails. -/
theorem comb_val :
    ((comb L (m := m) : (Matrix (Fin (m + 1)) (Fin (m + 1)) R)ˣ) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) R) = combMatrix L m :=
  partialComb_val L m le_rfl

end Comb

/-! ### The involution at every rank -/

section Involution

variable [CharP R 2] (hm : 0 < m)

/-- `0` and the last coordinate are distinct in rank at least two. -/
theorem zero_ne_last (hm : 0 < m) : (0 : Fin (m + 1)) ≠ last m := by
  intro hcon
  have := congrArg Fin.val hcon
  simp only [Fin.val_zero, last, Fin.val_last] at this
  omega

/-- The printed involution `z = x_{1n}(s₁) x_{n1}(t₁) x_{1n}(s₁)`, at rank
`m + 1` (coordinates zero-based: the plane is `(0, n)`). -/
def involutionWord : (Matrix (Fin (m + 1)) (Fin (m + 1)) R)ˣ :=
  elementaryUnit 0 (last m) (zero_ne_last hm) L.s1 *
    (elementaryUnit (last m) 0 (zero_ne_last hm).symm L.t1 *
      elementaryUnit 0 (last m) (zero_ne_last hm) L.s1)

omit [CharP R 2] in
theorem involutionWord_mem :
    involutionWord L hm ∈ elementaryGroup (Fin (m + 1)) R :=
  Subgroup.mul_mem _ (elementaryUnit_mem _ _ _ _)
    (Subgroup.mul_mem _ (elementaryUnit_mem _ _ _ _)
      (elementaryUnit_mem _ _ _ _))

/-- The value of the involution word: the involution block in the plane
`(0, n)`. -/
theorem involutionWord_val :
    ((involutionWord L hm : (Matrix (Fin (m + 1)) (Fin (m + 1)) R)ˣ) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) R) =
      planeMatrix 0 (last m) !![L.p0, L.s1; L.t1, 0] := by
  have hne := zero_ne_last (m := m) hm
  rw [involutionWord, Units.val_mul, Units.val_mul]
  rw [elementaryUnit_val_planeMatrix 0 (last m) hne L.s1]
  rw [elementaryUnit_val_planeMatrix' 0 (last m) hne L.t1]
  rw [planeMatrix_mul _ _ hne, planeMatrix_mul _ _ hne]
  rw [twoByTwo_involution L]

/-- **The involution squares to the identity at every rank.** -/
theorem involutionWord_sq :
    involutionWord L hm * involutionWord L hm = 1 := by
  apply Units.ext
  rw [Units.val_mul, involutionWord_val, planeMatrix_mul _ _
    (zero_ne_last hm), twoByTwo_involution_sq L,
    planeMatrix_one _ _ (zero_ne_last hm)]
  rfl

end Involution

end GeneralRank
end NonsoficGroupsExist
