import NonsoficGroupsExist.PrefixCode
import NonsoficGroupsExist.Kazhdan

/-!
# Leavitt equivalences between all positive ranks

For every `n + 1`, the complete left-comb prefix code identifies
`M_{n+1}(R)` with `R`. Applying this coefficient equivalence inside an
elementary group and flattening block matrices proves that all positive-rank
elementary groups over a binary Leavitt ring are mutually isomorphic.
-/

namespace NonsoficGroupsExist
namespace LeavittFamily

universe u

variable {R : Type u} [Ring R]

private theorem finSuccNontrivial (n : ℕ) (hn : 0 < n) :
    Nontrivial (Fin (n + 1)) :=
  ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by intro h; simpa using congrArg Fin.val h⟩

/-- Replace every coefficient in `EL_{n+1}(R)` by its `(m+1) × (m+1)`
left-comb matrix and flatten the resulting block matrix. -/
def rankSuccToProduct (L : LeavittFamily R) (n m : ℕ) (hn : 0 < n) :
    elementaryGroup (Fin (n + 1)) R ≃*
      elementaryGroup (Fin (n + 1) × Fin (m + 1)) R :=
  letI := finSuccNontrivial n hn
  (elementaryCoefficientEquiv
    (L.prefixRingEquiv (leftCombCode m) (L.leftCombCode_complete m)).symm).trans
      elementaryBlockEquiv

/-- All positive elementary ranks over a binary Leavitt ring are explicitly
isomorphic. -/
def rankSuccEquiv (L : LeavittFamily R) (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    elementaryGroup (Fin (n + 1)) R ≃*
      elementaryGroup (Fin (m + 1)) R :=
  (L.rankSuccToProduct n m hn).trans
    ((elementaryReindexEquiv (R := R)
      (Equiv.prodComm (Fin (n + 1)) (Fin (m + 1)))).trans
        (L.rankSuccToProduct m n hm).symm)

/-- The rank-three/rank-four equivalence used by the concrete compression
argument, now an instance of the all-positive-ranks construction. -/
def rankThreeEquivRankFour (L : LeavittFamily R) :
    elementaryGroup (Fin 3) R ≃* elementaryGroup (Fin 4) R :=
  L.rankSuccEquiv 2 3 (by omega) (by omega)

/-- Property `(T)` transfers between arbitrary positive Leavitt ranks. -/
theorem rankSucc_propertyT_of_rankSucc (L : LeavittFamily R) (n m : ℕ)
    (hn : 0 < n) (hm : 0 < m)
    (hT : HasKazhdanPropertyT.{u, 0} (elementaryGroup (Fin (m + 1)) R)) :
    HasKazhdanPropertyT.{u, 0} (elementaryGroup (Fin (n + 1)) R) :=
  HasKazhdanPropertyT.of_mulEquiv (L.rankSuccEquiv n m hn hm) hT

/-- Consequently property `(T)` in rank three supplies property `(T)` in
rank four; no second free-algebra theorem is required. -/
theorem rankFour_propertyT_of_rankThree (L : LeavittFamily R)
    (hT : HasKazhdanPropertyT.{u, 0} (elementaryGroup (Fin 3) R)) :
    HasKazhdanPropertyT.{u, 0} (elementaryGroup (Fin 4) R) :=
  L.rankSucc_propertyT_of_rankSucc 3 2 (by omega) (by omega) hT

end LeavittFamily
end NonsoficGroupsExist
