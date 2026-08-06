import NonsoficGroupsExist.Leavitt.MatrixSelfSimilarity
import NonsoficGroupsExist.Leavitt.PrefixCode

/-!
# Matrix self-similarity as an equivalence of algebras

The self-similarity proposition of the manuscript states that a complete
matrix family induces an isomorphism `Θ_C : M_r(A) ≅ A` of rings, *and of
unital `k`-algebras when `A` is a `k`-algebra*.  The ring half is
`CompleteMatrixFamily.matrixRingEquiv`; this file supplies the algebra half.

The content of the upgrade is one computation: `Θ_C` carries the scalar
matrix of `c` to the scalar `c`, because central scalars slide out of each
diagonal term and completeness sums the range projections to `1`:

  `∑ᵢ αᵢ (c·1) αᵢ* = c ∑ᵢ αᵢαᵢ* = c·1`.

The prefix-code specialization used throughout the manuscript is
`LeavittFamily.prefixAlgEquiv`.
-/

namespace NonsoficGroupsExist

namespace CompleteMatrixFamily

variable {k : Type*} [CommSemiring k]
variable {A : Type*} [Ring A] [Algebra k A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (F : CompleteMatrixFamily A ι)

/-- `Θ_C` fixes scalars: the image of the scalar matrix of `c` is `c`. -/
theorem matrixRingEquiv_algebraMap (c : k) :
    F.matrixRingEquiv (algebraMap k (Matrix ι ι A) c) = algebraMap k A c := by
  rw [matrixRingEquiv_apply]
  have hdiag : ∀ i j : ι,
      F.left i * algebraMap k (Matrix ι ι A) c i j * F.right j =
        if j = i then algebraMap k A c * (F.left i * F.right i) else 0 := by
    intro i j
    rw [Matrix.algebraMap_matrix_apply]
    rcases eq_or_ne i j with rfl | hij
    · rw [if_pos rfl, if_pos rfl]
      rw [← Algebra.commutes c (F.left i), mul_assoc]
    · rw [if_neg hij, if_neg (Ne.symm hij), mul_zero, zero_mul]
  calc ∑ i, ∑ j, F.left i * algebraMap k (Matrix ι ι A) c i j * F.right j
      = ∑ i, ∑ j, if j = i then
          algebraMap k A c * (F.left i * F.right i) else 0 := by
        exact Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun j _ => hdiag i j
    _ = ∑ i, algebraMap k A c * (F.left i * F.right i) := by
        exact Finset.sum_congr rfl fun i _ => by
          rw [Finset.sum_ite_eq' Finset.univ i
            (fun _ => algebraMap k A c * (F.left i * F.right i))]
          rw [if_pos (Finset.mem_univ i)]
    _ = algebraMap k A c * ∑ i, F.left i * F.right i := by
        rw [Finset.mul_sum]
    _ = algebraMap k A c := by rw [F.complete, mul_one]

/-- **The algebra clause of the self-similarity proposition.**  A complete
matrix family induces an equivalence `M_r(A) ≃ₐ[k] A` of unital
`k`-algebras. -/
def matrixAlgEquiv : Matrix ι ι A ≃ₐ[k] A :=
  AlgEquiv.ofRingEquiv (f := F.matrixRingEquiv)
    (fun c => F.matrixRingEquiv_algebraMap c)

@[simp] theorem matrixAlgEquiv_apply (M : Matrix ι ι A) :
    F.matrixAlgEquiv (k := k) M = F.matrixRingEquiv M := rfl

end CompleteMatrixFamily

namespace LeavittFamily

variable {k : Type*} [CommSemiring k]
variable {A : Type*} [Ring A] [Algebra k A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (L : LeavittFamily A)

/-- The prefix-code self-similarity `Θ_C : M_r(A) ≅ A`, as an equivalence of
unital `k`-algebras. -/
def prefixAlgEquiv (E : BinaryPrefixCode ι) (hE : L.IsComplete E) :
    Matrix ι ι A ≃ₐ[k] A :=
  (L.prefixMatrixFamily E hE).matrixAlgEquiv

@[simp] theorem prefixAlgEquiv_apply (E : BinaryPrefixCode ι)
    (hE : L.IsComplete E) (M : Matrix ι ι A) :
    L.prefixAlgEquiv (k := k) E hE M = L.prefixRingEquiv E hE M := rfl

end LeavittFamily
end NonsoficGroupsExist
