import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Data.Matrix.Basic

/-!
# Matrix self-similarity from a complete family

This is the finite algebraic core of Proposition `prop:selfsim`.  It works over
an arbitrary possibly noncommutative ring and uses exactly the two complete-leaf
relations from Lemma `lem:leaf`.
-/

namespace NonsoficGroupsExist

open scoped BigOperators

/-- A finite family satisfying the two relations used by the manuscript's
matrix self-similarity argument. -/
structure CompleteMatrixFamily (A : Type*) [Ring A] (ι : Type*) [Fintype ι]
    [DecidableEq ι] where
  left : ι → A
  right : ι → A
  orthogonal : ∀ i j, right i * left j = if i = j then 1 else 0
  complete : ∑ i, left i * right i = 1

namespace CompleteMatrixFamily

variable {A : Type*} [Ring A] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (F : CompleteMatrixFamily A ι)

/-- The inverse formula `x ↦ (αᵢ*x*αⱼ*)ᵢⱼ` from Proposition `prop:selfsim`. -/
def toMatrix (x : A) : Matrix ι ι A := fun i j => F.right i * x * F.left j

/-- The formula `M ↦ ∑ᵢⱼ αᵢ*Mᵢⱼ*αⱼ*` from Proposition `prop:selfsim`. -/
def fromMatrix (M : Matrix ι ι A) : A :=
  ∑ i, ∑ j, F.left i * M i j * F.right j

theorem toMatrix_add (x y : A) : F.toMatrix (x + y) = F.toMatrix x + F.toMatrix y := by
  ext i j
  simp [toMatrix, mul_add, add_mul]

theorem toMatrix_mul (x y : A) : F.toMatrix (x * y) = F.toMatrix x * F.toMatrix y := by
  classical
  ext i j
  change F.right i * (x * y) * F.left j =
    ∑ k, (F.right i * x * F.left k) * (F.right k * y * F.left j)
  calc
    F.right i * (x * y) * F.left j =
        F.right i * x * 1 * y * F.left j := by simp [mul_assoc]
    _ = F.right i * x * (∑ k, F.left k * F.right k) * y * F.left j := by
      rw [F.complete]
    _ = ∑ k, (F.right i * x * F.left k) * (F.right k * y * F.left j) := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      simp only [mul_assoc]

theorem fromMatrix_toMatrix (x : A) : F.fromMatrix (F.toMatrix x) = x := by
  classical
  unfold fromMatrix toMatrix
  calc
    (∑ i, ∑ j, F.left i * (F.right i * x * F.left j) * F.right j) =
        ∑ i, (F.left i * F.right i * x) *
          (∑ j, F.left j * F.right j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [mul_assoc]
    _ = ∑ i, F.left i * F.right i * x := by rw [F.complete]; simp
    _ = (∑ i, F.left i * F.right i) * x := by rw [Finset.sum_mul]
    _ = x := by rw [F.complete, one_mul]

theorem toMatrix_fromMatrix (M : Matrix ι ι A) : F.toMatrix (F.fromMatrix M) = M := by
  classical
  ext i j
  change F.right i * (∑ p, ∑ q, F.left p * M p q * F.right q) * F.left j = M i j
  calc
    F.right i * (∑ p, ∑ q, F.left p * M p q * F.right q) * F.left j =
        ∑ p, ∑ q,
          (F.right i * F.left p) * M p q * (F.right q * F.left j) := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      simp only [mul_assoc]
    _ = M i j := by simp [F.orthogonal]

/-- Proposition `prop:selfsim`, oriented from the ring to its matrix ring. -/
def ringEquivMatrix : A ≃+* Matrix ι ι A where
  toFun := F.toMatrix
  invFun := F.fromMatrix
  left_inv := F.fromMatrix_toMatrix
  right_inv := F.toMatrix_fromMatrix
  map_add' := F.toMatrix_add
  map_mul' := F.toMatrix_mul

/-- Proposition `prop:selfsim` in the orientation displayed in the manuscript. -/
def matrixRingEquiv : Matrix ι ι A ≃+* A := F.ringEquivMatrix.symm

/-- The unit-group isomorphism `GLᵣ(A) ≃* Aˣ` stated in
Proposition `prop:selfsim`. -/
def unitsEquiv : (Matrix ι ι A)ˣ ≃* Aˣ :=
  Units.mapEquiv F.matrixRingEquiv.toMulEquiv

@[simp] theorem matrixRingEquiv_apply (M : Matrix ι ι A) :
    F.matrixRingEquiv M = ∑ i, ∑ j, F.left i * M i j * F.right j := rfl

@[simp] theorem matrixRingEquiv_symm_apply (x : A) (i j : ι) :
    F.matrixRingEquiv.symm x i j = F.right i * x * F.left j := rfl

@[simp] theorem unitsEquiv_apply_val (M : (Matrix ι ι A)ˣ) :
    ↑(F.unitsEquiv M) = F.matrixRingEquiv (↑M) := rfl

end CompleteMatrixFamily
end NonsoficGroupsExist
