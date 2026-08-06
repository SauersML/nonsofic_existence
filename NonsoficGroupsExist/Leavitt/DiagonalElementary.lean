import NonsoficGroupsExist.Leavitt.ElementaryGroup
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-!
# Diagonal commutators in rank three

The Whitehead identity is implemented directly in the unit group of
`M₃(R)`.  It sends every element of the commutator subgroup of `Rˣ` to a
first-coordinate diagonal matrix in `EL₃(R)`.
-/

namespace NonsoficGroupsExist

open scoped commutatorElement

namespace DiagonalElementary

variable {R : Type*} [Ring R]

/-- A unit-valued function supported at the first coordinate. -/
def firstDiagonalFunctionUnit (u : Rˣ) : (Fin 3 → R)ˣ where
  val i := if i = 0 then (↑u : R) else 1
  inv i := if i = 0 then (↑u⁻¹ : R) else 1
  val_inv := by
    funext i
    by_cases hi : i = 0 <;> simp [hi]
  inv_val := by
    funext i
    by_cases hi : i = 0 <;> simp [hi]

/-- The first-coordinate diagonal construction as a homomorphism of unit
groups. -/
def firstDiagonalFunctionUnitHom : Rˣ →* (Fin 3 → R)ˣ where
  toFun := firstDiagonalFunctionUnit
  map_one' := by
    apply Units.ext
    funext i
    by_cases hi : i = 0 <;> simp [firstDiagonalFunctionUnit, hi]
  map_mul' u v := by
    apply Units.ext
    funext i
    by_cases hi : i = 0 <;> simp [firstDiagonalFunctionUnit, hi]

/-- Put a coefficient unit in the first diagonal position of `GL₃(R)`. -/
def firstDiagonalUnitHom : Rˣ →* (Matrix (Fin 3) (Fin 3) R)ˣ :=
  (Units.map (Matrix.diagonalRingHom (Fin 3) R).toMonoidHom).comp
    firstDiagonalFunctionUnitHom

@[simp] theorem firstDiagonalUnitHom_apply (u : Rˣ) (i j : Fin 3) :
    ((↑(firstDiagonalUnitHom u) : Matrix (Fin 3) (Fin 3) R) i j) =
      if i = j then if i = 0 then (↑u : R) else 1 else 0 := by
  simp [firstDiagonalUnitHom, firstDiagonalFunctionUnitHom,
    firstDiagonalFunctionUnit, Matrix.diagonal_apply]

theorem firstDiagonalUnitHom_injective :
    Function.Injective (firstDiagonalUnitHom (R := R)) := by
  intro u v huv
  apply Units.ext
  have h := congrArg
    (fun M : (Matrix (Fin 3) (Fin 3) R)ˣ ↦
      ((↑M : Matrix (Fin 3) (Fin 3) R) 0 0)) huv
  simpa using h

/-- The three-transvection Whitehead word in coordinates `0,1`. -/
def w (u : Rˣ) : (Matrix (Fin 3) (Fin 3) R)ˣ :=
  elementaryUnit 0 1 (by decide) (↑u : R) *
    elementaryUnit 1 0 (by decide) (-(↑u⁻¹ : R)) *
      elementaryUnit 0 1 (by decide) (↑u : R)

theorem w_mem (u : Rˣ) : w u ∈ elementaryGroup (Fin 3) R := by
  exact (elementaryGroup (Fin 3) R).mul_mem
    ((elementaryGroup (Fin 3) R).mul_mem
      (elementaryUnit_mem 0 1 (by decide) (↑u : R))
      (elementaryUnit_mem 1 0 (by decide) (-(↑u⁻¹ : R))))
    (elementaryUnit_mem 0 1 (by decide) (↑u : R))

theorem w_val (u : Rˣ) :
    (↑(w u) : Matrix (Fin 3) (Fin 3) R) =
      !![0, (↑u : R), 0; -(↑u⁻¹ : R), 0, 0; 0, 0, 1] := by
  unfold w
  change (1 + Matrix.single 0 1 (↑u : R)) *
      (1 + Matrix.single 1 0 (-(↑u⁻¹ : R))) *
        (1 + Matrix.single 0 1 (↑u : R)) = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

/-- The balanced Whitehead diagonal `diag(u,u⁻¹,1)`. -/
def balanced (u : Rˣ) : (Matrix (Fin 3) (Fin 3) R)ˣ :=
  w u * w (-1 : Rˣ)

theorem balanced_mem (u : Rˣ) : balanced u ∈ elementaryGroup (Fin 3) R :=
  (elementaryGroup (Fin 3) R).mul_mem (w_mem u) (w_mem (-1 : Rˣ))

theorem balanced_val (u : Rˣ) :
    (↑(balanced u) : Matrix (Fin 3) (Fin 3) R) =
      !![(↑u : R), 0, 0; 0, (↑u⁻¹ : R), 0; 0, 0, 1] := by
  unfold balanced
  change (↑(w u) : Matrix (Fin 3) (Fin 3) R) *
      (↑(w (-1 : Rˣ)) : Matrix (Fin 3) (Fin 3) R) = _
  rw [w_val, w_val, Matrix.mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem firstDiagonalUnit_commutator (a b : Rˣ) :
    firstDiagonalUnitHom ⁅a, b⁆ =
      balanced a * balanced b * balanced ((b * a)⁻¹) := by
  apply Units.ext
  change (↑(firstDiagonalUnitHom ⁅a, b⁆) : Matrix (Fin 3) (Fin 3) R) =
    (↑(balanced a) : Matrix (Fin 3) (Fin 3) R) *
      (↑(balanced b) : Matrix (Fin 3) (Fin 3) R) *
        (↑(balanced ((b * a)⁻¹)) : Matrix (Fin 3) (Fin 3) R)
  rw [balanced_val, balanced_val, balanced_val]
  ext i j
  rw [firstDiagonalUnitHom_apply]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, commutatorElement_def, mul_assoc]

theorem firstDiagonalUnit_commutator_mem (a b : Rˣ) :
    firstDiagonalUnitHom ⁅a, b⁆ ∈ elementaryGroup (Fin 3) R := by
  rw [firstDiagonalUnit_commutator]
  exact (elementaryGroup (Fin 3) R).mul_mem
    ((elementaryGroup (Fin 3) R).mul_mem (balanced_mem a) (balanced_mem b))
    (balanced_mem ((b * a)⁻¹))

/-- Whitehead's identity on the entire commutator subgroup. -/
theorem firstDiagonalUnit_mem_of_mem_commutator {u : Rˣ}
    (hu : u ∈ commutator Rˣ) :
    firstDiagonalUnitHom u ∈ elementaryGroup (Fin 3) R := by
  rw [commutator_eq_closure] at hu
  induction hu using Subgroup.closure_induction with
  | mem z hz =>
      obtain ⟨a, b, rfl⟩ := hz
      exact firstDiagonalUnit_commutator_mem a b
  | one => simpa only [map_one] using (elementaryGroup (Fin 3) R).one_mem
  | mul x y _ _ hx hy =>
      simpa only [map_mul] using (elementaryGroup (Fin 3) R).mul_mem hx hy
  | inv x _ hx =>
      simpa only [map_inv] using (elementaryGroup (Fin 3) R).inv_mem hx

end DiagonalElementary
end NonsoficGroupsExist
