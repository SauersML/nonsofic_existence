import Mathlib.Data.Matrix.Basic
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

def p0 : A := L.s0 * L.t0
def p1 : A := L.s1 * L.t1

@[simp] theorem p0_add_p1 : L.p0 + L.p1 = 1 := L.sum_range

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
  simp [p0, mul_assoc, L.t0_s1]

@[simp] theorem t1_mul_p0 : L.t1 * L.p0 = 0 := by
  calc
    L.t1 * (L.s0 * L.t0) = (L.t1 * L.s0) * L.t0 := by rw [mul_assoc]
    _ = 0 := by rw [L.t1_s0, zero_mul]

@[simp] theorem p1_mul_s0 : L.p1 * L.s0 = 0 := by
  simp [p1, mul_assoc, L.t1_s0]

@[simp] theorem t0_mul_p1 : L.t0 * L.p1 = 0 := by
  calc
    L.t0 * (L.s1 * L.t1) = (L.t0 * L.s1) * L.t1 := by rw [mul_assoc]
    _ = 0 := by rw [L.t0_s1, zero_mul]

@[simp] theorem p0_mul_s0 : L.p0 * L.s0 = L.s0 := by
  simp [p0, mul_assoc, L.t0_s0]

@[simp] theorem t0_mul_p0 : L.t0 * L.p0 = L.t0 := by
  simp [p0, ← mul_assoc, L.t0_s0]

@[simp] theorem p1_mul_s1 : L.p1 * L.s1 = L.s1 := by
  simp [p1, mul_assoc, L.t1_s1]

@[simp] theorem t1_mul_p1 : L.t1 * L.p1 = L.t1 := by
  simp [p1, ← mul_assoc, L.t1_s1]

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
  have hneg : -(1 : A) = 1 := CharTwo.neg_eq 1
  have htwo : (1 : A) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have hcorner : (1 : A) + L.p1 = L.p0 := by
    rw [← hneg, ← L.p0_add_p1]
    noncomm_ring
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [x12, x21, p0, p1, hcorner, htwo, L.t1_s1, mul_assoc]

/-- Lemma `lem:chartwo` (b): the two-by-two compressor block is an explicit
product of four elementary matrices. -/
theorem characteristicTwo_compressor
    [CharP A 2] :
    x21 (1 + L.t0) * x12 1 * x21 (1 + L.s0) * x12 L.t0 =
      !![L.s0, L.s1 * L.t1; 0, L.t0] := by
  have hneg : -(1 : A) = 1 := CharTwo.neg_eq 1
  have htwo : (1 : A) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have hcorner : L.p0 + (1 : A) = L.p1 := by
    rw [← hneg, ← L.p0_add_p1]
    noncomm_ring
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [x12, x21, p0, p1, htwo, hcorner, L.t0_s0, mul_assoc]
  all_goals noncomm_ring

/-- The two-by-two matrix called `z` in both the adjacent-rank and rank-two
constructions. -/
def z : Matrix (Fin 2) (Fin 2) A := !![L.p0, L.s1; L.t1, 0]

/-- Lemma `lem:zinv` on the nontrivial two-by-two block. -/
theorem z_sq : L.z * L.z = 1 := by
  change !![L.p0, L.s1; L.t1, 0] * !![L.p0, L.s1; L.t1, 0] = 1
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [z, p0, p1,
      L.t0_s0, L.t0_s1, L.t1_s0, L.t1_s1, L.sum_range,
      mul_assoc]

end LeavittFamily
end NonsoficGroupsExist
