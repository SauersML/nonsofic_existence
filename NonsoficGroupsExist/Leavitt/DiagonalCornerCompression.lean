import NonsoficGroupsExist.Leavitt.DiagonalElementary
import NonsoficGroupsExist.Leavitt.LeavittMatrixCompression
import Mathlib.Tactic.FinCases

/-!
# Diagonal corner units and matrix compression

The complementary Leavitt corner, placed in the first diagonal coordinate,
commutes with coefficient compression on three-by-three matrices.  Moreover,
the two images have trivial intersection.  These are the matrix-level bridge
statements needed by the concrete compression construction.
-/

namespace NonsoficGroupsExist
namespace LeavittFamily

variable {A : Type*} [Ring A]

/-- A first-coordinate complementary-corner unit commutes with every
compressed three-by-three matrix. -/
theorem matrixCompression_commutes_firstDiagonalCorner
    (L : LeavittFamily A) (M : Matrix (Fin 3) (Fin 3) A) (u : Aˣ) :
    L.matrixCompression M *
        (↑(DiagonalElementary.firstDiagonalUnitHom (L.cornerHom u)) :
          Matrix (Fin 3) (Fin 3) A) =
      (↑(DiagonalElementary.firstDiagonalUnitHom (L.cornerHom u)) :
          Matrix (Fin 3) (Fin 3) A) * L.matrixCompression M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixCompression_apply,
      DiagonalElementary.firstDiagonalUnitHom_apply, Matrix.mul_apply,
      Fin.sum_univ_succ, cornerHom, cornerUnit, p1, add_mul, mul_add,
      mul_assoc, add_comm]

/-- A compressed matrix can equal a first-coordinate complementary-corner
diagonal only when both source elements are identities. -/
theorem matrixCompression_eq_firstDiagonalCorner_iff
    (L : LeavittFamily A) (M : Matrix (Fin 3) (Fin 3) A) (u : Aˣ) :
    L.matrixCompression M =
        (↑(DiagonalElementary.firstDiagonalUnitHom (L.cornerHom u)) :
          Matrix (Fin 3) (Fin 3) A) ↔
      M = 1 ∧ u = 1 := by
  constructor
  · intro h
    have hsandwich := congrArg
      (fun N : Matrix (Fin 3) (Fin 3) A ↦
        scalarDiagonal (ι := Fin 3) L.t0 * N *
          scalarDiagonal (ι := Fin 3) L.s0) h
    have hright :
        scalarDiagonal (ι := Fin 3) L.t0 *
              (↑(DiagonalElementary.firstDiagonalUnitHom (L.cornerHom u)) :
                Matrix (Fin 3) (Fin 3) A) *
            scalarDiagonal (ι := Fin 3) L.s0 = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [scalarDiagonal_apply,
          DiagonalElementary.firstDiagonalUnitHom_apply, Matrix.mul_apply,
          cornerHom, cornerUnit, mul_add, mul_assoc]
    have hM : M = 1 := by
      rw [matrixCompression_recover] at hsandwich
      exact hsandwich.trans hright
    refine ⟨hM, ?_⟩
    have hdiagMatrix :
        (↑(DiagonalElementary.firstDiagonalUnitHom (L.cornerHom u)) :
          Matrix (Fin 3) (Fin 3) A) = 1 := by
      rw [← h, hM, L.matrixCompression_one]
    have hdiag :
        DiagonalElementary.firstDiagonalUnitHom (L.cornerHom u) = 1 := by
      apply Units.ext
      exact hdiagMatrix
    have hcorner : L.cornerHom u = 1 := by
      apply DiagonalElementary.firstDiagonalUnitHom_injective
      simpa using hdiag
    exact L.cornerHom_injective (by simpa using hcorner)
  · rintro ⟨rfl, rfl⟩
    rw [L.matrixCompression_one]
    simp

end LeavittFamily
end NonsoficGroupsExist
