import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing

/-!
# The finite Leavitt-algebra calculations

This file formalizes the relations used throughout Sections 5--8 of the
manuscript and kernel-checks the two characteristic-two block factorizations
of Lemma `lem:chartwo`.  It deliberately works over an arbitrary possibly
noncommutative ring carrying a binary Leavitt family.
-/

namespace NonsoficGroupsExist

/-- Four elements satisfying the defining relations of the binary Leavitt
algebra.  Keeping this as data over an arbitrary ring makes every theorem
below applicable to every unital copy of the Leavitt algebra. -/
structure LeavittFamily (A : Type*) [NonAssocRing A] where
  s0 : A
  s1 : A
  t0 : A
  t1 : A
  t0_s0 : t0 * s0 = 1
  t0_s1 : t0 * s1 = 0
  t1_s0 : t1 * s0 = 0
  t1_s1 : t1 * s1 = 1
  sum_range : s0 * t0 + s1 * t1 = 1

namespace LeavittFamily

variable {A : Type*} [Ring A] (L : LeavittFamily A)

open scoped CharTwo
open scoped commutatorElement

attribute [simp] t0_s0 t0_s1 t1_s0 t1_s1

def p0 : A := L.s0 * L.t0
def p1 : A := L.s1 * L.t1

@[simp] theorem p0_add_p1 : L.p0 + L.p1 = 1 := L.sum_range

@[simp] theorem p0_add_s1t1 : L.p0 + L.s1 * L.t1 = 1 := L.sum_range

@[simp] theorem p0_mul_p0 : L.p0 * L.p0 = L.p0 := by
  calc
    (L.s0 * L.t0) * (L.s0 * L.t0) = L.s0 * ((L.t0 * L.s0) * L.t0) := by
      simp only [mul_assoc]
    _ = L.s0 * L.t0 := by rw [L.t0_s0, one_mul]

@[simp] theorem p1_mul_p1 : L.p1 * L.p1 = L.p1 := by
  calc
    (L.s1 * L.t1) * (L.s1 * L.t1) = L.s1 * ((L.t1 * L.s1) * L.t1) := by
      simp only [mul_assoc]
    _ = L.s1 * L.t1 := by rw [L.t1_s1, one_mul]

@[simp] theorem p0_mul_p1 : L.p0 * L.p1 = 0 := by
  calc
    (L.s0 * L.t0) * (L.s1 * L.t1) = L.s0 * ((L.t0 * L.s1) * L.t1) := by
      simp only [mul_assoc]
    _ = 0 := by rw [L.t0_s1, zero_mul, mul_zero]

@[simp] theorem p1_mul_p0 : L.p1 * L.p0 = 0 := by
  calc
    (L.s1 * L.t1) * (L.s0 * L.t0) = L.s1 * ((L.t1 * L.s0) * L.t0) := by
      simp only [mul_assoc]
    _ = 0 := by rw [L.t1_s0, zero_mul, mul_zero]

@[simp] theorem p0_mul_s1 : L.p0 * L.s1 = 0 := by
  simp [p0, mul_assoc]

@[simp] theorem t1_mul_p0 : L.t1 * L.p0 = 0 := by
  calc
    L.t1 * (L.s0 * L.t0) = (L.t1 * L.s0) * L.t0 := by rw [mul_assoc]
    _ = 0 := by rw [L.t1_s0, zero_mul]

@[simp] theorem p1_mul_s0 : L.p1 * L.s0 = 0 := by
  simp [p1, mul_assoc]

@[simp] theorem t0_mul_p1 : L.t0 * L.p1 = 0 := by
  calc
    L.t0 * (L.s1 * L.t1) = (L.t0 * L.s1) * L.t1 := by rw [mul_assoc]
    _ = 0 := by rw [L.t0_s1, zero_mul]

@[simp] theorem p0_mul_s0 : L.p0 * L.s0 = L.s0 := by
  simp [p0, mul_assoc]

@[simp] theorem t0_mul_p0 : L.t0 * L.p0 = L.t0 := by
  simp [p0, ← mul_assoc]

@[simp] theorem p1_mul_s1 : L.p1 * L.s1 = L.s1 := by
  simp [p1, mul_assoc]

@[simp] theorem t1_mul_p1 : L.t1 * L.p1 = L.t1 := by
  simp [p1, ← mul_assoc]

@[simp] theorem p0_mul_s0t1 : L.p0 * (L.s0 * L.t1) = L.s0 * L.t1 := by
  rw [← mul_assoc, L.p0_mul_s0]

@[simp] theorem p1_mul_s0t1 : L.p1 * (L.s0 * L.t1) = 0 := by
  rw [← mul_assoc, L.p1_mul_s0, zero_mul]

@[simp] theorem p0_mul_s1t0 : L.p0 * (L.s1 * L.t0) = 0 := by
  rw [← mul_assoc, L.p0_mul_s1, zero_mul]

@[simp] theorem p1_mul_s1t0 : L.p1 * (L.s1 * L.t0) = L.s1 * L.t0 := by
  rw [← mul_assoc, L.p1_mul_s1]

@[simp] theorem s0t1_mul_p0 : (L.s0 * L.t1) * L.p0 = 0 := by
  rw [mul_assoc, L.t1_mul_p0, mul_zero]

@[simp] theorem s0t1_mul_p1 : (L.s0 * L.t1) * L.p1 = L.s0 * L.t1 := by
  rw [mul_assoc, L.t1_mul_p1]

@[simp] theorem s1t0_mul_p0 : (L.s1 * L.t0) * L.p0 = L.s1 * L.t0 := by
  rw [mul_assoc, L.t0_mul_p0]

@[simp] theorem s1t0_mul_p1 : (L.s1 * L.t0) * L.p1 = 0 := by
  rw [mul_assoc, L.t0_mul_p1, mul_zero]

@[simp] theorem s0t1_sq : (L.s0 * L.t1) * (L.s0 * L.t1) = 0 := by
  calc
    (L.s0 * L.t1) * (L.s0 * L.t1) =
        L.s0 * ((L.t1 * L.s0) * L.t1) := by noncomm_ring
    _ = 0 := by rw [L.t1_s0]; simp

@[simp] theorem s1t0_sq : (L.s1 * L.t0) * (L.s1 * L.t0) = 0 := by
  calc
    (L.s1 * L.t0) * (L.s1 * L.t0) =
        L.s1 * ((L.t0 * L.s1) * L.t0) := by noncomm_ring
    _ = 0 := by rw [L.t0_s1]; simp

@[simp] theorem s0t1_mul_s1t0 :
    (L.s0 * L.t1) * (L.s1 * L.t0) = L.p0 := by
  calc
    (L.s0 * L.t1) * (L.s1 * L.t0) =
        L.s0 * ((L.t1 * L.s1) * L.t0) := by noncomm_ring
    _ = L.p0 := by rw [L.t1_s1]; simp [p0]

@[simp] theorem s1t0_mul_s0t1 :
    (L.s1 * L.t0) * (L.s0 * L.t1) = L.p1 := by
  calc
    (L.s1 * L.t0) * (L.s0 * L.t1) =
        L.s1 * ((L.t0 * L.s0) * L.t1) := by noncomm_ring
    _ = L.p1 := by rw [L.t0_s0]; simp [p1]

/-! ### A characteristic-free sign commutator -/

/-- The unit which is `-1` on the `p₀` corner and `1` on the `p₁` corner. -/
def cornerSign : Aˣ where
  val := -L.p0 + L.p1
  inv := -L.p0 + L.p1
  val_inv := by
    change (-L.p0 + L.p1) * (-L.p0 + L.p1) = 1
    calc
      (-L.p0 + L.p1) * (-L.p0 + L.p1) = L.p0 + L.p1 := by
        noncomm_ring [L.p0_mul_p0, L.p1_mul_p1,
          L.p0_mul_p1, L.p1_mul_p0]
      _ = 1 := L.p0_add_p1
  inv_val := by
    change (-L.p0 + L.p1) * (-L.p0 + L.p1) = 1
    calc
      (-L.p0 + L.p1) * (-L.p0 + L.p1) = L.p0 + L.p1 := by
        noncomm_ring [L.p0_mul_p0, L.p1_mul_p1,
          L.p0_mul_p1, L.p1_mul_p0]
      _ = 1 := L.p0_add_p1

/-- The unit interchanging the two Leavitt corners. -/
def cornerSwap : Aˣ where
  val := L.s0 * L.t1 + L.s1 * L.t0
  inv := L.s0 * L.t1 + L.s1 * L.t0
  val_inv := by
    change (L.s0 * L.t1 + L.s1 * L.t0) *
      (L.s0 * L.t1 + L.s1 * L.t0) = 1
    calc
      (L.s0 * L.t1 + L.s1 * L.t0) *
          (L.s0 * L.t1 + L.s1 * L.t0) = L.p0 + L.p1 := by
        noncomm_ring [L.s0t1_sq, L.s1t0_sq,
          L.s0t1_mul_s1t0, L.s1t0_mul_s0t1]
      _ = 1 := L.p0_add_p1
  inv_val := by
    change (L.s0 * L.t1 + L.s1 * L.t0) *
      (L.s0 * L.t1 + L.s1 * L.t0) = 1
    calc
      (L.s0 * L.t1 + L.s1 * L.t0) *
          (L.s0 * L.t1 + L.s1 * L.t0) = L.p0 + L.p1 := by
        noncomm_ring [L.s0t1_sq, L.s1t0_sq,
          L.s0t1_mul_s1t0, L.s1t0_mul_s0t1]
      _ = 1 := L.p0_add_p1

/-- The scalar `-1` is one explicit commutator in the unit group of every
ring carrying a binary Leavitt family. -/
theorem cornerSign_commutator_cornerSwap :
    ⁅L.cornerSign, L.cornerSwap⁆ = (-1 : Aˣ) := by
  apply Units.ext
  change (-L.p0 + L.p1) * (L.s0 * L.t1 + L.s1 * L.t0) *
      (-L.p0 + L.p1) * (L.s0 * L.t1 + L.s1 * L.t0) = -1
  have hsignSwap :
      (-L.p0 + L.p1) * (L.s0 * L.t1 + L.s1 * L.t0) =
        -L.s0 * L.t1 + L.s1 * L.t0 := by
    change (-(L.s0 * L.t0) + L.s1 * L.t1) *
      (L.s0 * L.t1 + L.s1 * L.t0) =
        -L.s0 * L.t1 + L.s1 * L.t0
    change (-L.p0 + L.p1) *
      (L.s0 * L.t1 + L.s1 * L.t0) =
        -L.s0 * L.t1 + L.s1 * L.t0
    noncomm_ring [L.p0_mul_s0t1, L.p0_mul_s1t0,
      L.p1_mul_s0t1, L.p1_mul_s1t0]
  rw [hsignSwap]
  have hswapSign :
      (-L.s0 * L.t1 + L.s1 * L.t0) * (-L.p0 + L.p1) =
        -(L.s0 * L.t1 + L.s1 * L.t0) := by
    change (-L.s0 * L.t1 + L.s1 * L.t0) *
      (-(L.s0 * L.t0) + L.s1 * L.t1) =
        -(L.s0 * L.t1 + L.s1 * L.t0)
    change (-L.s0 * L.t1 + L.s1 * L.t0) * (-L.p0 + L.p1) =
      -(L.s0 * L.t1 + L.s1 * L.t0)
    noncomm_ring [L.s0t1_mul_p0, L.s0t1_mul_p1,
      L.s1t0_mul_p0, L.s1t0_mul_p1]
  rw [hswapSign, neg_mul]
  exact congrArg Neg.neg (L.cornerSwap.val_inv)

theorem negOne_mem_commutator (L : LeavittFamily A) :
    (-1 : Aˣ) ∈ commutator Aˣ := by
  rw [← cornerSign_commutator_cornerSwap L]
  exact Subgroup.commutator_mem_commutator (by simp) (by simp)

theorem t0_pow_mul_s0_pow (n : ℕ) : L.t0 ^ n * L.s0 ^ n = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        L.t0 ^ (n + 1) * L.s0 ^ (n + 1) =
            (L.t0 ^ n * L.t0) * (L.s0 * L.s0 ^ n) := by
              rw [pow_succ, pow_succ']
        _ = L.t0 ^ n * ((L.t0 * L.s0) * L.s0 ^ n) := by
          simp only [mul_assoc]
        _ = 1 := by rw [L.t0_s0, one_mul, ih]

theorem t1_mul_s0_pow_succ (n : ℕ) : L.t1 * L.s0 ^ (n + 1) = 0 := by
  rw [pow_succ']
  simp only [← mul_assoc, L.t1_s0, zero_mul]

/-- Distinct powers of the first prefix generator remain distinct in every
nontrivial binary Leavitt family. -/
theorem s0_pow_injective [Nontrivial A] :
    Function.Injective (fun n : ℕ ↦ L.s0 ^ n) := by
  have eq_of_le {n m : ℕ} (hnm : n ≤ m) (hpow : L.s0 ^ n = L.s0 ^ m) : n = m := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    rw [pow_add] at hpow
    have hk : (1 : A) = L.s0 ^ k := by
      calc
        (1 : A) = L.t0 ^ n * L.s0 ^ n := (L.t0_pow_mul_s0_pow n).symm
        _ = L.t0 ^ n * (L.s0 ^ n * L.s0 ^ k) := congrArg (L.t0 ^ n * ·) hpow
        _ = (L.t0 ^ n * L.s0 ^ n) * L.s0 ^ k := by rw [mul_assoc]
        _ = L.s0 ^ k := by rw [L.t0_pow_mul_s0_pow, one_mul]
    cases k with
    | zero => simp
    | succ k =>
        have ht1 : L.t1 = 0 := by
          calc
            L.t1 = L.t1 * 1 := (mul_one L.t1).symm
            _ = L.t1 * L.s0 ^ (k + 1) := by rw [hk]
            _ = 0 := L.t1_mul_s0_pow_succ k
        have hzero : (1 : A) = 0 := by
          calc
            (1 : A) = L.t1 * L.s1 := L.t1_s1.symm
            _ = 0 := by rw [ht1, zero_mul]
        exact (one_ne_zero hzero).elim
  intro n m hpow
  rcases le_total n m with hnm | hmn
  · exact eq_of_le hnm hpow
  · exact (eq_of_le hmn hpow.symm).symm

/-- Every nontrivial ring carrying a binary Leavitt family is infinite. -/
theorem infinite (L : LeavittFamily A) [Nontrivial A] : Infinite A := by
  let f : ℕ → A := fun n ↦ L.s0 ^ n
  exact Infinite.of_injective f (s0_pow_injective L)

@[simp] theorem one_add_s1t1 [CharP A 2] :
    (1 : A) + L.s1 * L.t1 = L.s0 * L.t0 := by
  rw [← L.sum_range]
  exact CharTwo.add_cancel_right (L.s0 * L.t0) (L.s1 * L.t1)

@[simp] theorem s0t0_add_one [CharP A 2] :
    L.s0 * L.t0 + (1 : A) = L.s1 * L.t1 := by
  rw [← L.sum_range]
  exact CharTwo.add_cancel_left (L.s0 * L.t0) (L.s1 * L.t1)

/-- The elementary upper transvection used in Lemma `lem:chartwo`. -/
def x12 (a : A) : Matrix (Fin 2) (Fin 2) A := !![1, a; 0, 1]

/-- The elementary lower transvection used in Lemma `lem:chartwo`. -/
def x21 (a : A) : Matrix (Fin 2) (Fin 2) A := !![1, 0; a, 1]

@[simp] theorem x12_apply (a : A) :
    x12 a = !![1, a; 0, 1] := rfl

@[simp] theorem x21_apply (a : A) :
    x21 a = !![1, 0; a, 1] := rfl

/-- Lemma `lem:chartwo` (a): the involution is an explicit product of three
elementary matrices. -/
theorem characteristicTwo_involution
    [CharP A 2] :
    x12 L.s1 * x21 L.t1 * x12 L.s1 =
      !![L.p0, L.s1; L.t1, 0] := by
  unfold x12 x21
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [p0, mul_assoc]

/-- Lemma `lem:chartwo` (b): the two-by-two compressor block is an explicit
product of four elementary matrices. -/
theorem characteristicTwo_compressor
    [CharP A 2] :
    x21 (1 + L.t0) * x12 1 * x21 (1 + L.s0) * x12 L.t0 =
      !![L.s0, L.s1 * L.t1; 0, L.t0] := by
  have hcancel (a : A) : 1 + a + 1 = a := by
    rw [add_comm 1 a]
    exact CharTwo.add_cancel_right a 1
  have hzero (a : A) : 1 + a + (a + 1) = 0 := by
    rw [add_assoc, CharTwo.add_cancel_left a 1, CharTwo.add_self_eq_zero]
  unfold x12 x21
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hcancel, hzero, mul_add]

/-- The compressor block has a four-elementary factorization in every
characteristic.  In characteristic two this specializes to the word above. -/
theorem compressor_factorization :
    x21 (L.t0 - 1) * x12 1 * x21 (L.s0 - 1) * x12 (-L.t0) =
      !![L.s0, L.p1; 0, L.t0] := by
  have hp1 : -L.p0 + 1 = L.p1 := by
    rw [← L.p0_add_p1]
    abel
  have hzero : L.t0 - 1 + L.t0 * (L.s0 - 1) = 0 := by
    noncomm_ring [L.t0_s0]
  unfold x12 x21
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · simp
  · simpa [p0] using hp1
  · simpa using hzero
  · simp [hzero]

/-- The two-by-two matrix called `z` in both the adjacent-rank and rank-two
constructions. -/
def z : Matrix (Fin 2) (Fin 2) A := !![L.p0, L.s1; L.t1, 0]

/-- Lemma `lem:zinv` on the nontrivial two-by-two block. -/
theorem z_sq : L.z * L.z = 1 := by
  change !![L.p0, L.s1; L.t1, 0] * !![L.p0, L.s1; L.t1, 0] = 1
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end LeavittFamily
end NonsoficGroupsExist
