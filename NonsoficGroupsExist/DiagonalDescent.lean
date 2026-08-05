import NonsoficGroupsExist.GLIsElementary
import NonsoficGroupsExist.LeavittDiagonalClass

/-!
# Unstable descent for the diagonal class

The bridge from stable to unstable `K₁`-triviality over a binary
Leavitt ring: membership of `diag(u, 1)` in the diagonal class of the
matrix ring descends along the self-similarity isomorphism to the
corner insertion `κ₀(u)`, which is congruent to `u` modulo the
diagonal class.  Consequently the diagonal class group of `L` is
exactly the kernel of `Lˣ → K₁(L)`, and the manuscript's rose-graph
input reduces to the stable vanishing `K₁(L_k(1,2)) = 0`.
-/

namespace NonsoficGroupsExist
namespace MatrixDiagonalization

/-- Pointwise transport of the diagonal class along a ring
isomorphism. -/
theorem mem_stableUnits_map {S R : Type*} [Ring S] [Ring R]
    (e : S ≃+* R) {U : Sˣ} (h : U ∈ stableUnits S) :
    Units.map ((e : S →+* R) : S →* R) U ∈ stableUnits R := by
  rw [mem_stableUnits_iff] at h ⊢
  have himg := elementaryGroup_map_le (ι := Fin 2) (e : S →+* R)
    ⟨diagUnit U, h, rfl⟩
  rwa [elementaryMatrixUnitMap_diagUnit] at himg

end MatrixDiagonalization

namespace LeavittFamily

open MatrixDiagonalization

variable {A : Type*} [Ring A] (L : LeavittFamily A)

/-- The self-similarity isomorphism carries `diag(u, 1)` to the corner
insertion `κ₀(u)`. -/
theorem unitsMap_binaryMatrixRingEquiv_diagUnit (u : Aˣ) :
    Units.map ((L.binaryMatrixRingEquiv :
        Matrix (Fin 2) (Fin 2) A →+* A) :
        (Matrix (Fin 2) (Fin 2) A) →* A) (diagUnit u) =
      L.kappaUnit [0] u := by
  apply Units.ext
  show L.binaryMatrixRingEquiv
    ((diagUnit u : (Matrix (Fin 2) (Fin 2) A)ˣ) :
      Matrix (Fin 2) (Fin 2) A) = (L.kappaUnit [0] u : A)
  rw [binaryMatrixRingEquiv_apply, kappaUnit_val]
  have h00 : ((diagUnit u : (Matrix (Fin 2) (Fin 2) A)ˣ) :
      Matrix (Fin 2) (Fin 2) A) 0 0 = (u : A) := rfl
  have h01 : ((diagUnit u : (Matrix (Fin 2) (Fin 2) A)ˣ) :
      Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := rfl
  have h10 : ((diagUnit u : (Matrix (Fin 2) (Fin 2) A)ˣ) :
      Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := rfl
  have h11 : ((diagUnit u : (Matrix (Fin 2) (Fin 2) A)ˣ) :
      Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := rfl
  rw [h00, h01, h10, h11]
  have hword : L.wordS [0] * (u : A) * L.wordT [0] +
      (1 - L.wordS [0] * L.wordT [0]) =
      L.s 0 * (u : A) * L.t 0 + (1 - L.s 0 * L.t 0) := by
    simp [wordS, wordT]
  rw [hword]
  have hsub : (1 : A) - L.s 0 * L.t 0 = L.s 1 * L.t 1 := by
    have h := L.sum_s_mul_t
    rw [← h]
    abel
  rw [hsub]
  simp

include L in
/-- **Unstable descent, one step**: if `diag(u, 1)` lies in the
diagonal class of the matrix ring, then `u` lies in the diagonal class
of the base ring. -/
theorem mem_stableUnits_of_diagUnit_mem [Nontrivial A]
    (hdiv : ∀ x : A, x ≠ 0 → ∃ p q : A, p * x * q = 1) (u : Aˣ)
    (h : diagUnit u ∈ stableUnits (Matrix (Fin 2) (Fin 2) A)) :
    u ∈ stableUnits A := by
  have h1 := mem_stableUnits_map L.binaryMatrixRingEquiv h
  rw [unitsMap_binaryMatrixRingEquiv_diagUnit] at h1
  have hco := L.kappaUnit_mul_inv_mem_stableUnits [0] hdiv u
  have hmul := mul_mem (inv_mem hco) h1
  rwa [show (L.kappaUnit [0] u * u⁻¹)⁻¹ * L.kappaUnit [0] u = u from by
    group] at hmul

end LeavittFamily
end NonsoficGroupsExist
