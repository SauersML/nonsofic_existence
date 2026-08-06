import NonsoficGroupsExist.Leavitt.ElementaryGroup
import Mathlib.Tactic.FinCases

/-!
# Coordinate-plane embeddings of two-by-two identities

The manuscript's explicit factorizations are two-by-two identities read in a
pair of coordinates `(i, j)` of a larger matrix ring: a matrix that agrees
with the identity outside `{i, j}` is determined by its `2×2` block, and
products of such matrices multiply blockwise.  At rank four the library
verified this by exhausting the sixteen cells; at a general rank exhaustion
is unavailable, so this file provides the transfer once and for all:

* `planeMatrix i j B` — the matrix with `2×2` block `B` in the plane
  `(i, j)` and identity elsewhere;
* `planeMatrix_mul` — the embedding is multiplicative in `B`;
* row and column action lemmas — multiplying an arbitrary matrix by a plane
  matrix touches only the two rows (columns) of the plane;
* `elementaryUnit_val_planeMatrix` — transvections are plane matrices of the
  two-by-two elementary blocks.

Everything is stated over an arbitrary ring and an arbitrary (decidable,
finite) index type; nothing here mentions Leavitt families.
-/

namespace NonsoficGroupsExist

variable {R : Type*} [Ring R]
variable {ι : Type*} [DecidableEq ι]

/-- The matrix with two-by-two block `B` in the coordinate plane `(i, j)` and
the identity outside it. -/
def planeMatrix (i j : ι) (B : Matrix (Fin 2) (Fin 2) R) : Matrix ι ι R :=
  Matrix.of fun r c =>
    if r = i then (if c = i then B 0 0 else if c = j then B 0 1 else 0)
    else if r = j then (if c = i then B 1 0 else if c = j then B 1 1 else 0)
    else if r = c then 1 else 0

section Entries

variable (i j : ι) (B : Matrix (Fin 2) (Fin 2) R)

@[simp] theorem planeMatrix_apply_ii : planeMatrix i j B i i = B 0 0 := by
  simp [planeMatrix]

theorem planeMatrix_apply_ij (hij : i ≠ j) :
    planeMatrix i j B i j = B 0 1 := by
  simp [planeMatrix, hij.symm]

theorem planeMatrix_apply_ji (hij : i ≠ j) :
    planeMatrix i j B j i = B 1 0 := by
  simp [planeMatrix, hij.symm]

theorem planeMatrix_apply_jj (hij : i ≠ j) :
    planeMatrix i j B j j = B 1 1 := by
  simp [planeMatrix, hij.symm]

theorem planeMatrix_apply_row_i {c : ι} (hci : c ≠ i) (hcj : c ≠ j) :
    planeMatrix i j B i c = 0 := by
  simp [planeMatrix, hci, hcj]

theorem planeMatrix_apply_row_j (hij : i ≠ j) {c : ι} (hci : c ≠ i)
    (hcj : c ≠ j) :
    planeMatrix i j B j c = 0 := by
  simp [planeMatrix, hij.symm, hci, hcj]

theorem planeMatrix_apply_off {r c : ι} (hri : r ≠ i) (hrj : r ≠ j) :
    planeMatrix i j B r c = if r = c then 1 else 0 := by
  simp [planeMatrix, hri, hrj]

end Entries

/-- The identity block embeds to the identity. -/
theorem planeMatrix_one (i j : ι) (hij : i ≠ j) :
    planeMatrix i j (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  ext r c
  by_cases hri : r = i
  · subst hri
    by_cases hci : c = i
    · subst hci
      simp [planeMatrix, Matrix.one_apply]
    · by_cases hcj : c = j
      · subst hcj
        simp [planeMatrix, Matrix.one_apply, hij, Matrix.one_apply_ne hij]
      · simp [planeMatrix, hci, hcj, Matrix.one_apply,
          Ne.symm hci]
  · by_cases hrj : r = j
    · subst hrj
      by_cases hci : c = i
      · subst hci
        simp [planeMatrix, hri, Matrix.one_apply, Ne.symm hri]
      · by_cases hcj : c = j
        · subst hcj
          simp [planeMatrix, hij, Matrix.one_apply]
        · simp [planeMatrix, hij, hci, hcj, Matrix.one_apply, Ne.symm hcj]
    · rw [planeMatrix_apply_off i j _ hri hrj, Matrix.one_apply]

/-! ### Row splitting

Sums over the index type split into the two plane coordinates and the rest,
and a plane matrix is supported on the plane in its plane rows. -/

variable [Fintype ι]

theorem sum_split (i j : ι) (hij : i ≠ j) (f : ι → R) :
    ∑ k, f k = f i + f j + ∑ k ∈ (Finset.univ.erase i).erase j, f k := by
  have hj : j ∈ Finset.univ.erase i :=
    Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
  rw [← Finset.add_sum_erase _ f (Finset.mem_univ i)]
  rw [← Finset.add_sum_erase _ f hj]
  ring

/-! ### The multiplicative law -/

/-- Multiplying by a plane matrix on the left touches only the two plane
rows: row `i` of `planeMatrix i j B * M` is the `B`-combination of rows `i`
and `j` of `M`. -/
theorem planeMatrix_mul_apply_i (i j : ι) (hij : i ≠ j)
    (B : Matrix (Fin 2) (Fin 2) R) (M : Matrix ι ι R) (c : ι) :
    (planeMatrix i j B * M) i c = B 0 0 * M i c + B 0 1 * M j c := by
  rw [Matrix.mul_apply, sum_split i j hij]
  rw [planeMatrix_apply_ii, planeMatrix_apply_ij i j B hij]
  have htail : ∑ k ∈ (Finset.univ.erase i).erase j,
      planeMatrix i j B i k * M k c = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    obtain ⟨hkj, hki, -⟩ :=
      Finset.mem_erase.mp hk |>.imp id (Finset.mem_erase.mp)
    rw [planeMatrix_apply_row_i i j B hki.1 hkj, zero_mul]
  rw [htail, add_zero]

theorem planeMatrix_mul_apply_j (i j : ι) (hij : i ≠ j)
    (B : Matrix (Fin 2) (Fin 2) R) (M : Matrix ι ι R) (c : ι) :
    (planeMatrix i j B * M) j c = B 1 0 * M i c + B 1 1 * M j c := by
  rw [Matrix.mul_apply, sum_split i j hij]
  rw [planeMatrix_apply_ji i j B hij, planeMatrix_apply_jj i j B hij]
  have htail : ∑ k ∈ (Finset.univ.erase i).erase j,
      planeMatrix i j B j k * M k c = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    obtain ⟨hkj, hki, -⟩ :=
      Finset.mem_erase.mp hk |>.imp id (Finset.mem_erase.mp)
    rw [planeMatrix_apply_row_j i j B hij hki.1 hkj, zero_mul]
  rw [htail, add_zero]

/-- Rows outside the plane are untouched. -/
theorem planeMatrix_mul_apply_off (i j : ι)
    (B : Matrix (Fin 2) (Fin 2) R) (M : Matrix ι ι R) {r : ι} (hri : r ≠ i)
    (hrj : r ≠ j) (c : ι) :
    (planeMatrix i j B * M) r c = M r c := by
  rw [Matrix.mul_apply]
  rw [show ∀ k, planeMatrix i j B r k * M k c =
      (if r = k then 1 else 0) * M k c from fun k => by
    rw [planeMatrix_apply_off i j B hri hrj]]
  simp

/-- Columns outside the plane are untouched by right multiplication. -/
theorem mul_planeMatrix_apply_off (i j : ι)
    (B : Matrix (Fin 2) (Fin 2) R) (M : Matrix ι ι R) (r : ι) {c : ι}
    (hci : c ≠ i) (hcj : c ≠ j) :
    (M * planeMatrix i j B) r c = M r c := by
  rw [Matrix.mul_apply]
  rw [show ∀ k, M r k * planeMatrix i j B k c =
      M r k * (if k = c then 1 else 0) from fun k => by
    congr 1
    by_cases hki : k = i
    · subst hki
      rw [planeMatrix_apply_row_i i j B hci.symm hcj.symm,
        if_neg (fun h => hci h.symm)]
    · by_cases hkj : k = j
      · subst hkj
        by_cases hij : k = i
        · exact absurd hij hki
        · rw [planeMatrix_apply_row_j i j B ?_ hci.symm hcj.symm,
            if_neg (fun h => hcj h.symm)]
          intro h
          exact hki (h ▸ rfl)
      · rw [planeMatrix_apply_off i j B hki hkj]]
  simp

/-- Column `i` of `M * planeMatrix i j B` is the `B`-combination of columns
`i` and `j` of `M`. -/
theorem mul_planeMatrix_apply_i (i j : ι) (hij : i ≠ j)
    (B : Matrix (Fin 2) (Fin 2) R) (M : Matrix ι ι R) (r : ι) :
    (M * planeMatrix i j B) r i = M r i * B 0 0 + M r j * B 1 0 := by
  rw [Matrix.mul_apply, sum_split i j hij]
  rw [planeMatrix_apply_ii, planeMatrix_apply_ji i j B hij]
  have htail : ∑ k ∈ (Finset.univ.erase i).erase j,
      M r k * planeMatrix i j B k i = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    obtain ⟨hkj, hki, -⟩ :=
      Finset.mem_erase.mp hk |>.imp id (Finset.mem_erase.mp)
    rw [planeMatrix_apply_off i j B hki.1 hkj, if_neg hki.1, mul_zero]
  rw [htail, add_zero]

theorem mul_planeMatrix_apply_j (i j : ι) (hij : i ≠ j)
    (B : Matrix (Fin 2) (Fin 2) R) (M : Matrix ι ι R) (r : ι) :
    (M * planeMatrix i j B) r j = M r i * B 0 1 + M r j * B 1 1 := by
  rw [Matrix.mul_apply, sum_split i j hij]
  rw [planeMatrix_apply_ij i j B hij, planeMatrix_apply_jj i j B hij]
  have htail : ∑ k ∈ (Finset.univ.erase i).erase j,
      M r k * planeMatrix i j B k j = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    obtain ⟨hkj, hki, -⟩ :=
      Finset.mem_erase.mp hk |>.imp id (Finset.mem_erase.mp)
    rw [planeMatrix_apply_off i j B hki.1 hkj, if_neg hkj, mul_zero]
  rw [htail, add_zero]

/-- **Plane matrices multiply blockwise.** -/
theorem planeMatrix_mul (i j : ι) (hij : i ≠ j)
    (B C : Matrix (Fin 2) (Fin 2) R) :
    planeMatrix i j B * planeMatrix i j C = planeMatrix i j (B * C) := by
  ext r c
  by_cases hri : r = i
  · subst hri
    rw [planeMatrix_mul_apply_i r j hij B _ c]
    by_cases hci : c = r
    · subst hci
      rw [planeMatrix_apply_ii, planeMatrix_apply_ji r j C hij,
        planeMatrix_apply_ii, Matrix.mul_apply, Fin.sum_univ_two]
    · by_cases hcj : c = j
      · subst hcj
        rw [planeMatrix_apply_ij r c C hij, planeMatrix_apply_jj r c C hij,
          planeMatrix_apply_ij r c _ hij, Matrix.mul_apply, Fin.sum_univ_two]
      · rw [planeMatrix_apply_row_i r j C (fun h => hci h) hcj,
          planeMatrix_apply_row_j r j C hij (fun h => hci h) hcj,
          planeMatrix_apply_row_i r j _ (fun h => hci h) hcj,
          mul_zero, mul_zero, add_zero]
  · by_cases hrj : r = j
    · subst hrj
      rw [planeMatrix_mul_apply_j i r hij B _ c]
      by_cases hci : c = i
      · subst hci
        rw [planeMatrix_apply_ii, planeMatrix_apply_ji c r C hij,
          planeMatrix_apply_ji c r _ hij, Matrix.mul_apply, Fin.sum_univ_two]
      · by_cases hcj : c = r
        · subst hcj
          rw [planeMatrix_apply_ij i c C hij, planeMatrix_apply_jj i c C hij,
            planeMatrix_apply_jj i c _ hij, Matrix.mul_apply,
            Fin.sum_univ_two]
        · rw [planeMatrix_apply_row_i i r C hci (fun h => hcj h),
            planeMatrix_apply_row_j i r C hij hci (fun h => hcj h),
            planeMatrix_apply_row_j i r _ hij hci (fun h => hcj h),
            mul_zero, mul_zero, add_zero]
    · rw [planeMatrix_mul_apply_off i j B _ hri hrj,
        planeMatrix_apply_off i j C hri hrj,
        planeMatrix_apply_off i j _ hri hrj]

/-! ### Transvections are plane matrices -/

theorem elementaryUnit_val_planeMatrix (i j : ι) (hij : i ≠ j) (a : R) :
    ((elementaryUnit i j hij a : (Matrix ι ι R)ˣ) : Matrix ι ι R) =
      planeMatrix i j !![1, a; 0, 1] := by
  ext r c
  by_cases hri : r = i
  · subst hri
    by_cases hci : c = r
    · subst hci
      simp [elementaryUnit, planeMatrix, Matrix.one_apply,
        Matrix.single_apply, hij]
    · by_cases hcj : c = j
      · subst hcj
        simp [elementaryUnit, planeMatrix, Matrix.one_apply,
          Matrix.single_apply, hij, Ne.symm hij]
      · simp [elementaryUnit, planeMatrix, Matrix.one_apply,
          Matrix.single_apply, Ne.symm hci, hcj, fun h : j = c => hcj h.symm]
  · by_cases hrj : r = j
    · subst hrj
      by_cases hci : c = i
      · subst hci
        simp [elementaryUnit, planeMatrix, Matrix.one_apply,
          Matrix.single_apply, hij, Ne.symm hri, fun h : r = c => hri h.symm]
      · by_cases hcj : c = r
        · subst hcj
          simp [elementaryUnit, planeMatrix, Matrix.one_apply,
            Matrix.single_apply, hij, Ne.symm hij]
        · simp [elementaryUnit, planeMatrix, Matrix.one_apply,
            Matrix.single_apply, hij, hci, Ne.symm hcj,
            fun h : r = c => hcj h.symm]
    · simp [elementaryUnit, planeMatrix, Matrix.one_apply,
        Matrix.single_apply, hri, hrj, fun h : i = r => hri h.symm]

/-- The opposite transvection, in the same plane orientation. -/
theorem elementaryUnit_val_planeMatrix' (i j : ι) (hij : i ≠ j) (a : R) :
    ((elementaryUnit j i hij.symm a : (Matrix ι ι R)ˣ) : Matrix ι ι R) =
      planeMatrix i j !![1, 0; a, 1] := by
  ext r c
  by_cases hri : r = i
  · subst hri
    by_cases hci : c = r
    · subst hci
      simp [elementaryUnit, planeMatrix, Matrix.one_apply,
        Matrix.single_apply, Ne.symm hij]
    · by_cases hcj : c = j
      · subst hcj
        simp [elementaryUnit, planeMatrix, Matrix.one_apply,
          Matrix.single_apply, hij, Ne.symm hij, fun h : j = r => hij h.symm]
      · simp [elementaryUnit, planeMatrix, Matrix.one_apply,
          Matrix.single_apply, Ne.symm hci, hcj, fun h : r = c => hci h.symm]
  · by_cases hrj : r = j
    · subst hrj
      by_cases hci : c = i
      · subst hci
        simp [elementaryUnit, planeMatrix, Matrix.one_apply,
          Matrix.single_apply, hij, Ne.symm hri, fun h : r = c => hri h.symm]
      · by_cases hcj : c = r
        · subst hcj
          simp [elementaryUnit, planeMatrix, Matrix.one_apply,
            Matrix.single_apply, hij, Ne.symm hij]
        · simp [elementaryUnit, planeMatrix, Matrix.one_apply,
            Matrix.single_apply, hij, hci, Ne.symm hcj,
            fun h : r = c => hcj h.symm]
    · simp [elementaryUnit, planeMatrix, Matrix.one_apply,
        Matrix.single_apply, hri, hrj, fun h : j = r => hrj h.symm]

end NonsoficGroupsExist
