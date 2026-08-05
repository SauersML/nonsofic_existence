import NonsoficGroupsExist.PrefixCode
import NonsoficGroupsExist.Kazhdan

/-!
# Leavitt equivalence of ranks three and four

A binary Leavitt family gives complete prefix codes with any positive finite
number of leaves.  The explicit three- and four-leaf codes below identify
`EL₃(R)` and `EL₄(R)` with ranks `3×4` and `4×3`, respectively.  Swapping
the two index factors then gives a genuine group isomorphism between them.
-/

namespace NonsoficGroupsExist
namespace LeavittFamily

universe u

variable {R : Type u} [Ring R]

/-- The complete three-leaf code `0, 10, 11`. -/
def threeLeafCode : BinaryPrefixCode (Fin 3) where
  word := ![[0], [1, 0], [1, 1]]
  prefix_free := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

/-- The complete four-leaf code `0, 10, 110, 111`. -/
def fourLeafCode : BinaryPrefixCode (Fin 4) where
  word := ![[0], [1, 0], [1, 1, 0], [1, 1, 1]]
  prefix_free := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

theorem threeLeafCode_complete (L : LeavittFamily R) :
    L.IsComplete threeLeafCode := by
  unfold IsComplete
  rw [show (∑ i : Fin 3, L.cylinder (threeLeafCode.word i)) =
      L.cylinder [0] + (L.cylinder [1, 0] + L.cylinder [1, 1]) by
    simp [threeLeafCode, Fin.sum_univ_succ]]
  calc
    L.cylinder [0] + (L.cylinder [1, 0] + L.cylinder [1, 1]) =
        L.cylinder [0] + L.cylinder [1] := by
          rw [show L.cylinder [1, 0] + L.cylinder [1, 1] = L.cylinder [1] by
            simpa using (L.cylinder_split [1]).symm]
    _ = L.cylinder [] := by simpa using (L.cylinder_split []).symm
    _ = 1 := by simp [cylinder]

theorem fourLeafCode_complete (L : LeavittFamily R) :
    L.IsComplete fourLeafCode := by
  unfold IsComplete
  rw [show (∑ i : Fin 4, L.cylinder (fourLeafCode.word i)) =
      L.cylinder [0] + (L.cylinder [1, 0] +
        (L.cylinder [1, 1, 0] + L.cylinder [1, 1, 1])) by
    simp [fourLeafCode, Fin.sum_univ_succ]]
  calc
    L.cylinder [0] + (L.cylinder [1, 0] +
        (L.cylinder [1, 1, 0] + L.cylinder [1, 1, 1])) =
        L.cylinder [0] + (L.cylinder [1, 0] + L.cylinder [1, 1]) := by
          rw [show L.cylinder [1, 1, 0] + L.cylinder [1, 1, 1] =
            L.cylinder [1, 1] by simpa using (L.cylinder_split [1, 1]).symm]
    _ = L.cylinder [0] + L.cylinder [1] := by
      rw [show L.cylinder [1, 0] + L.cylinder [1, 1] = L.cylinder [1] by
        simpa using (L.cylinder_split [1]).symm]
    _ = L.cylinder [] := by simpa using (L.cylinder_split []).symm
    _ = 1 := by simp [cylinder]

/-- `EL₃(R) ≃ EL₁₂(R)` obtained by replacing coefficients with their
four-by-four prefix matrices and flattening blocks. -/
def rankThreeToTwelve (L : LeavittFamily R) :
    elementaryGroup (Fin 3) R ≃* elementaryGroup (Fin 3 × Fin 4) R :=
  (elementaryCoefficientEquiv
      (L.prefixRingEquiv fourLeafCode L.fourLeafCode_complete).symm).trans
    elementaryBlockEquiv

/-- `EL₄(R) ≃ EL₁₂(R)` obtained using the three-leaf prefix code. -/
def rankFourToTwelve (L : LeavittFamily R) :
    elementaryGroup (Fin 4) R ≃* elementaryGroup (Fin 4 × Fin 3) R :=
  (elementaryCoefficientEquiv
      (L.prefixRingEquiv threeLeafCode L.threeLeafCode_complete).symm).trans
    elementaryBlockEquiv

/-- The explicit Leavitt self-similarity isomorphism `EL₃(R) ≃ EL₄(R)`. -/
def rankThreeEquivRankFour (L : LeavittFamily R) :
    elementaryGroup (Fin 3) R ≃* elementaryGroup (Fin 4) R :=
  (L.rankThreeToTwelve).trans
    ((elementaryReindexEquiv
      (Equiv.prodComm (Fin 3) (Fin 4))).trans L.rankFourToTwelve.symm)

/-- Consequently property `(T)` in rank three supplies property `(T)` in
rank four; no second EJZ invocation is required. -/
theorem rankFour_propertyT_of_rankThree (L : LeavittFamily R)
    (hT : HasKazhdanPropertyT.{u, 0} (elementaryGroup (Fin 3) R)) :
    HasKazhdanPropertyT.{u, 0} (elementaryGroup (Fin 4) R) :=
  HasKazhdanPropertyT.of_mulEquiv L.rankThreeEquivRankFour.symm hT

end LeavittFamily
end NonsoficGroupsExist
