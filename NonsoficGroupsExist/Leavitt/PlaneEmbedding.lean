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

/-- The identity block embeds to the identity.

The cases are driven by rewriting the goal at `r` and `c` rather than by
`subst`, which would eliminate the plane coordinates `i`, `j` themselves and
leave the entry lemmas unstatable. -/
theorem planeMatrix_one (i j : ι) (hij : i ≠ j) :
    planeMatrix i j (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  ext r c
  by_cases hri : r = i
  · by_cases hci : c = i
    · rw [hri, hci, planeMatrix_apply_ii, Matrix.one_apply_eq,
        Matrix.one_apply_eq]
    · by_cases hcj : c = j
      · rw [hri, hcj, planeMatrix_apply_ij i j _ hij,
          Matrix.one_apply_ne hij,
          Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1)]
      · rw [hri, planeMatrix_apply_row_i i j _ hci hcj,
          Matrix.one_apply_ne (Ne.symm hci)]
  · by_cases hrj : r = j
    · by_cases hci : c = i
      · rw [hrj, hci, planeMatrix_apply_ji i j _ hij,
          Matrix.one_apply_ne (Ne.symm hij),
          Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)]
      · by_cases hcj : c = j
        · rw [hrj, hcj, planeMatrix_apply_jj i j _ hij, Matrix.one_apply_eq,
            Matrix.one_apply_eq]
        · rw [hrj, planeMatrix_apply_row_j i j _ hij hci hcj,
            Matrix.one_apply_ne (Ne.symm hcj)]
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
  exact (add_assoc _ _ _).symm

/-- Membership in the doubly punctured index set, unpacked in the orientation
the entry lemmas ask for. -/
theorem ne_of_mem_erase_erase {i j k : ι}
    (hk : k ∈ (Finset.univ.erase i).erase j) : k ≠ i ∧ k ≠ j := by
  obtain ⟨hkj, hk'⟩ := Finset.mem_erase.mp hk
  obtain ⟨hki, -⟩ := Finset.mem_erase.mp hk'
  exact ⟨hki, hkj⟩

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
    obtain ⟨hki, hkj⟩ := ne_of_mem_erase_erase hk
    rw [planeMatrix_apply_row_i i j B hki hkj, zero_mul]
  rw [htail, add_zero]

theorem planeMatrix_mul_apply_j (i j : ι) (hij : i ≠ j)
    (B : Matrix (Fin 2) (Fin 2) R) (M : Matrix ι ι R) (c : ι) :
    (planeMatrix i j B * M) j c = B 1 0 * M i c + B 1 1 * M j c := by
  rw [Matrix.mul_apply, sum_split i j hij]
  rw [planeMatrix_apply_ji i j B hij, planeMatrix_apply_jj i j B hij]
  have htail : ∑ k ∈ (Finset.univ.erase i).erase j,
      planeMatrix i j B j k * M k c = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    obtain ⟨hki, hkj⟩ := ne_of_mem_erase_erase hk
    rw [planeMatrix_apply_row_j i j B hij hki hkj, zero_mul]
  rw [htail, add_zero]

/-- Rows outside the plane are untouched. -/
theorem planeMatrix_mul_apply_off (i j : ι)
    (B : Matrix (Fin 2) (Fin 2) R) (M : Matrix ι ι R) {r : ι} (hri : r ≠ i)
    (hrj : r ≠ j) (c : ι) :
    (planeMatrix i j B * M) r c = M r c := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_congr rfl fun k _ =>
    congrArg (fun x => x * M k c) (planeMatrix_apply_off i j B hri hrj)]
  simp

/-- Columns outside the plane are untouched by right multiplication. -/
theorem mul_planeMatrix_apply_off (i j : ι)
    (B : Matrix (Fin 2) (Fin 2) R) (M : Matrix ι ι R) (r : ι) {c : ι}
    (hci : c ≠ i) (hcj : c ≠ j) :
    (M * planeMatrix i j B) r c = M r c := by
  have hentry : ∀ k : ι, planeMatrix i j B k c = if k = c then 1 else 0 := by
    intro k
    by_cases hki : k = i
    · rw [hki, planeMatrix_apply_row_i i j B hci hcj, if_neg (Ne.symm hci)]
    · by_cases hkj : k = j
      · -- `i = j` would put `k` at `i`, which this branch excludes
        have hij : i ≠ j := fun h => hki (hkj.trans h.symm)
        rw [hkj, planeMatrix_apply_row_j i j B hij hci hcj,
          if_neg (Ne.symm hcj)]
      · rw [planeMatrix_apply_off i j B hki hkj]
  rw [Matrix.mul_apply]
  rw [Finset.sum_congr rfl fun k _ => congrArg (fun x => M r k * x) (hentry k)]
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
    obtain ⟨hki, hkj⟩ := ne_of_mem_erase_erase hk
    rw [planeMatrix_apply_off i j B hki hkj, if_neg hki, mul_zero]
  rw [htail, add_zero]

theorem mul_planeMatrix_apply_j (i j : ι) (hij : i ≠ j)
    (B : Matrix (Fin 2) (Fin 2) R) (M : Matrix ι ι R) (r : ι) :
    (M * planeMatrix i j B) r j = M r i * B 0 1 + M r j * B 1 1 := by
  rw [Matrix.mul_apply, sum_split i j hij]
  rw [planeMatrix_apply_ij i j B hij, planeMatrix_apply_jj i j B hij]
  have htail : ∑ k ∈ (Finset.univ.erase i).erase j,
      M r k * planeMatrix i j B k j = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    obtain ⟨hki, hkj⟩ := ne_of_mem_erase_erase hk
    rw [planeMatrix_apply_off i j B hki hkj, if_neg hkj, mul_zero]
  rw [htail, add_zero]

/-- **Plane matrices multiply blockwise.** -/
theorem planeMatrix_mul (i j : ι) (hij : i ≠ j)
    (B C : Matrix (Fin 2) (Fin 2) R) :
    planeMatrix i j B * planeMatrix i j C = planeMatrix i j (B * C) := by
  ext r c
  by_cases hri : r = i
  · rw [hri, planeMatrix_mul_apply_i i j hij B _ c]
    by_cases hci : c = i
    · rw [hci, planeMatrix_apply_ii, planeMatrix_apply_ji i j C hij,
        planeMatrix_apply_ii, Matrix.mul_apply, Fin.sum_univ_two]
    · by_cases hcj : c = j
      · rw [hcj, planeMatrix_apply_ij i j C hij,
          planeMatrix_apply_jj i j C hij, planeMatrix_apply_ij i j _ hij,
          Matrix.mul_apply, Fin.sum_univ_two]
      · rw [planeMatrix_apply_row_i i j C hci hcj,
          planeMatrix_apply_row_j i j C hij hci hcj,
          planeMatrix_apply_row_i i j _ hci hcj, mul_zero, mul_zero, add_zero]
  · by_cases hrj : r = j
    · rw [hrj, planeMatrix_mul_apply_j i j hij B _ c]
      by_cases hci : c = i
      · rw [hci, planeMatrix_apply_ii, planeMatrix_apply_ji i j C hij,
          planeMatrix_apply_ji i j _ hij, Matrix.mul_apply, Fin.sum_univ_two]
      · by_cases hcj : c = j
        · rw [hcj, planeMatrix_apply_ij i j C hij,
            planeMatrix_apply_jj i j C hij, planeMatrix_apply_jj i j _ hij,
            Matrix.mul_apply, Fin.sum_univ_two]
        · rw [planeMatrix_apply_row_i i j C hci hcj,
            planeMatrix_apply_row_j i j C hij hci hcj,
            planeMatrix_apply_row_j i j _ hij hci hcj, mul_zero, mul_zero,
            add_zero]
    · rw [planeMatrix_mul_apply_off i j B _ hri hrj,
        planeMatrix_apply_off i j C hri hrj,
        planeMatrix_apply_off i j _ hri hrj]

/-! ### Transvections are plane matrices -/

/-- The entries of a transvection, with the guards written in the orientation
`planeMatrix` uses, so that a case split on `r` and `c` against the plane
coordinates discharges both sides. -/
theorem elementaryUnit_val_apply (i j : ι) (hij : i ≠ j) (a : R) (r c : ι) :
    ((elementaryUnit i j hij a : (Matrix ι ι R)ˣ) : Matrix ι ι R) r c =
      (if c = r then 1 else 0) + (if r = i ∧ c = j then a else 0) := by
  have hone : (1 : Matrix ι ι R) r c = if c = r then 1 else 0 := by
    rw [Matrix.one_apply]
    by_cases h : r = c
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg fun hc => h hc.symm]
  change (1 + Matrix.single i j a) r c = _
  rw [Matrix.add_apply, hone, Matrix.single_apply]
  congr 1
  by_cases h : r = i ∧ c = j
  · rw [if_pos ⟨h.1.symm, h.2.symm⟩, if_pos h]
  · rw [if_neg fun hh => h ⟨hh.1.symm, hh.2.symm⟩, if_neg h]

theorem elementaryUnit_val_planeMatrix (i j : ι) (hij : i ≠ j) (a : R) :
    ((elementaryUnit i j hij a : (Matrix ι ι R)ˣ) : Matrix ι ι R) =
      planeMatrix i j !![1, a; 0, 1] := by
  ext r c
  rw [elementaryUnit_val_apply]
  by_cases hri : r = i <;> by_cases hrj : r = j <;>
    by_cases hci : c = i <;> by_cases hcj : c = j <;>
    simp_all [planeMatrix] <;>
    first
      | exact if_congr eq_comm rfl rfl
      | exact fun h => absurd h.symm (by assumption)

/-- The opposite transvection, in the same plane orientation. -/
theorem elementaryUnit_val_planeMatrix' (i j : ι) (hij : i ≠ j) (a : R) :
    ((elementaryUnit j i hij.symm a : (Matrix ι ι R)ˣ) : Matrix ι ι R) =
      planeMatrix i j !![1, 0; a, 1] := by
  ext r c
  rw [elementaryUnit_val_apply]
  by_cases hri : r = i <;> by_cases hrj : r = j <;>
    by_cases hci : c = i <;> by_cases hcj : c = j <;>
    simp_all [planeMatrix] <;>
    first
      | exact if_congr eq_comm rfl rfl
      | exact fun h => absurd h.symm (by assumption)

end NonsoficGroupsExist
