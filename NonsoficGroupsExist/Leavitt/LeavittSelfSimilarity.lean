import NonsoficGroupsExist.Leavitt.Leavitt
import NonsoficGroupsExist.Leavitt.MatrixSelfSimilarity

/-!
# Binary Leavitt self-similarity

This instantiates Proposition `prop:selfsim` for the complete two-leaf tree.
-/

namespace NonsoficGroupsExist
namespace LeavittFamily

variable {A : Type*} [Ring A]

/-- The complete matrix family `(s₀,s₁)` and `(t₀,t₁)`. -/
def binaryMatrixFamily (L : LeavittFamily A) : CompleteMatrixFamily A (Fin 2) where
  left := ![L.s0, L.s1]
  right := ![L.t0, L.t1]
  orthogonal i j := by
    fin_cases i <;> fin_cases j <;> simp
  complete := by
    simpa [Fin.sum_univ_two] using L.sum_range

/-- Proposition `prop:selfsim` for the binary complete leaf set. -/
def binaryMatrixRingEquiv (L : LeavittFamily A) : Matrix (Fin 2) (Fin 2) A ≃+* A :=
  L.binaryMatrixFamily.matrixRingEquiv

/-- The resulting group isomorphism `GL₂(A) ≃* Aˣ`. -/
def binaryUnitsEquiv (L : LeavittFamily A) :
    (Matrix (Fin 2) (Fin 2) A)ˣ ≃* Aˣ :=
  L.binaryMatrixFamily.unitsEquiv

@[simp] theorem binaryMatrixRingEquiv_apply (L : LeavittFamily A)
    (M : Matrix (Fin 2) (Fin 2) A) :
    L.binaryMatrixRingEquiv M =
      L.s0 * M 0 0 * L.t0 + L.s0 * M 0 1 * L.t1 +
        (L.s1 * M 1 0 * L.t0 + L.s1 * M 1 1 * L.t1) := by
  simp [binaryMatrixRingEquiv, binaryMatrixFamily, CompleteMatrixFamily.matrixRingEquiv_apply,
    Fin.sum_univ_two, add_assoc]

end LeavittFamily
end NonsoficGroupsExist
