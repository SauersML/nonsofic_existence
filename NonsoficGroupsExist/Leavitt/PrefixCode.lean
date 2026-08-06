import NonsoficGroupsExist.Leavitt.LeavittWords
import NonsoficGroupsExist.Leavitt.MatrixSelfSimilarity
import NonsoficGroupsExist.Leavitt.ElementaryGroup

/-!
# Prefix codes and the isomorphism `Θ_C`

An ordered binary prefix code is a finite family of pairwise incomparable
binary words; it is *complete* when the corresponding cylinders sum to `1`.

Proposition `prop:selfsim` of the manuscript says that a complete prefix code
with `r` leaves induces a ring isomorphism

  `Θ_C : M_r(L) ≅ L`,   `(a_{ij}) ↦ ∑ α_i a_{ij} α_j^*`,

which is equation `eq:Theta-main`.  Here this is obtained by exhibiting the
family `(s_{α_i}, t_{α_i})` as a `CompleteMatrixFamily` and invoking
`CompleteMatrixFamily.matrixRingEquiv`.
-/

namespace NonsoficGroupsExist

open scoped BigOperators

/-- An ordered binary prefix code. -/
structure BinaryPrefixCode (ι : Type*) where
  word : ι → List (Fin 2)
  prefix_free : ∀ ⦃i j⦄, i ≠ j → ¬ word i <+: word j

namespace LeavittFamily

variable {A : Type*} [Ring A] (L : LeavittFamily A)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- The orthogonality relations of a prefix code. -/
theorem prefixCode_orthogonal (E : BinaryPrefixCode ι) (i j : ι) :
    L.wordT (E.word i) * L.wordS (E.word j) = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp [wordT_mul_wordS_self]
  · simp only [hij, if_false]
    exact wordT_mul_wordS_of_incomparable L _ _
      (E.prefix_free hij) (E.prefix_free (Ne.symm hij))

/-- A prefix code is *complete* when its cylinders sum to `1`. -/
def IsComplete (E : BinaryPrefixCode ι) : Prop :=
  ∑ i, L.cylinder (E.word i) = 1

/-- A complete prefix code is a complete matrix family in the sense of
`MatrixSelfSimilarity`. -/
def prefixMatrixFamily (E : BinaryPrefixCode ι) (hE : L.IsComplete E) :
    CompleteMatrixFamily A ι where
  left i := L.wordS (E.word i)
  right i := L.wordT (E.word i)
  orthogonal := L.prefixCode_orthogonal E
  complete := hE

/-- **Proposition `prop:selfsim` / equation `eq:Theta-main`.**  A complete prefix
code with `r` leaves induces `Θ_C : M_r(A) ≅ A`. -/
def prefixRingEquiv (E : BinaryPrefixCode ι) (hE : L.IsComplete E) :
    Matrix ι ι A ≃+* A :=
  (L.prefixMatrixFamily E hE).matrixRingEquiv

@[simp] theorem prefixRingEquiv_apply (E : BinaryPrefixCode ι)
    (hE : L.IsComplete E) (M : Matrix ι ι A) :
    L.prefixRingEquiv E hE M =
      ∑ i, ∑ j, L.wordS (E.word i) * M i j * L.wordT (E.word j) := rfl

/-- The induced isomorphism of unit groups, `GL_r(A) ≅ Aˣ`. -/
def prefixUnitsEquiv (E : BinaryPrefixCode ι) (hE : L.IsComplete E) :
    (Matrix ι ι A)ˣ ≃* Aˣ :=
  (L.prefixMatrixFamily E hE).unitsEquiv

/-- Under prefix self-similarity, an elementary matrix is the corresponding
off-diagonal prefix root. -/
@[simp] theorem prefixUnitsEquiv_elementaryUnit_val (E : BinaryPrefixCode ι)
    (hE : L.IsComplete E) (i j : ι) (hij : i ≠ j) (a : A) :
    (↑(L.prefixUnitsEquiv E hE (elementaryUnit i j hij a)) : A) =
      1 + L.wordS (E.word i) * a * L.wordT (E.word j) := by
  classical
  change (∑ p, ∑ q, L.wordS (E.word p) *
      (1 + Matrix.single i j a) p q * L.wordT (E.word q)) = _
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  simp_rw [mul_add, add_mul, Finset.sum_add_distrib]
  rw [show (∑ p, ∑ q, L.wordS (E.word p) * (if p = q then 1 else 0) *
      L.wordT (E.word q)) = 1 by
    simpa [IsComplete, cylinder] using hE]
  congr 1
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro q _ hq
      have hjq : j ≠ q := fun h => hq h.symm
      simp [hjq]
    · simp
  · intro p _ hp
    simp [hp.symm]
  · simp

/-- The corner idempotent attached to an arbitrary (not necessarily complete)
prefix code. -/
def prefixIdempotent (E : BinaryPrefixCode ι) : A :=
  ∑ i, L.cylinder (E.word i)

omit [DecidableEq ι] in
theorem prefixIdempotent_eq_one_iff_complete (E : BinaryPrefixCode ι) :
    L.prefixIdempotent E = 1 ↔ L.IsComplete E := Iff.rfl

/-- The one-leaf code, used to insert a unit into a single cylinder. -/
def singletonPrefixCode (a : List (Fin 2)) : BinaryPrefixCode (Fin 1) where
  word _ := a
  prefix_free := by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim

@[simp] theorem singletonPrefixCode_idempotent (a : List (Fin 2)) :
    L.prefixIdempotent (singletonPrefixCode a) = L.cylinder a := by
  simp [prefixIdempotent, singletonPrefixCode]

end LeavittFamily

/-! ### Complete left-comb codes of every positive size -/

/-- The `i`th leaf in the left-comb binary tree with `n + 1` leaves:
`0, 10, 110, ..., 1ⁿ`. -/
def leftCombWord (n : ℕ) (i : Fin (n + 1)) : List (Fin 2) :=
  List.replicate i.val 1 ++ if i.val < n then [0] else []

@[simp] theorem leftCombWord_zero (n : ℕ) :
    leftCombWord (n + 1) 0 = [0] := by
  simp [leftCombWord]

@[simp] theorem leftCombWord_succ (n : ℕ) (i : Fin (n + 1)) :
    leftCombWord (n + 1) i.succ = 1 :: leftCombWord n i := by
  by_cases hi : i.val < n
  · have hi' : i.val + 1 < n + 1 := by omega
    simp [leftCombWord, hi, hi', List.replicate_succ]
  · have hin : i.val = n := by omega
    simp [leftCombWord, hin, List.replicate_succ]

/-- The ordered complete left-comb code with `n + 1` leaves. -/
def leftCombCode (n : ℕ) : BinaryPrefixCode (Fin (n + 1)) where
  word := leftCombWord n
  prefix_free := by
    intro i j hij hp
    have hijv : i.val ≠ j.val := by
      intro h
      exact hij (Fin.ext h)
    rcases lt_or_gt_of_ne hijv with hlt | hgt
    · have hin : i.val < n := by omega
      have hiLen : i.val < (leftCombWord n i).length := by
        simp [leftCombWord, hin]
      have heq := hp.getElem hiLen
      simp [leftCombWord, hin, hlt] at heq
    · have hjn : j.val < n := by omega
      have hjLen : j.val < (leftCombWord n i).length := by
        simp [leftCombWord]
        split_ifs <;> omega
      have heq := hp.getElem hjLen
      simp [leftCombWord, hjn, hgt] at heq

namespace LeavittFamily

variable {A : Type*} [Ring A] (L : LeavittFamily A)

theorem cylinder_cons_one (w : List (Fin 2)) :
    L.cylinder (1 :: w) = L.s1 * L.cylinder w * L.t1 := by
  simp [cylinder, wordS, wordT, mul_assoc]

/-- Every positive natural number occurs as the size of an explicit complete
binary prefix code. -/
theorem leftCombCode_complete (n : ℕ) :
    L.IsComplete (leftCombCode n) := by
  induction n with
  | zero =>
      simp [IsComplete, leftCombCode, leftCombWord, cylinder]
  | succ n ih =>
      have hsum : ∑ i : Fin (n + 1), L.cylinder (leftCombWord n i) = 1 := by
        simpa [IsComplete, leftCombCode] using ih
      unfold IsComplete
      rw [Fin.sum_univ_succ]
      simp only [leftCombCode, leftCombWord_zero, leftCombWord_succ]
      calc
        L.cylinder [0] + ∑ i : Fin (n + 1), L.cylinder (1 :: leftCombWord n i) =
            L.cylinder [0] + L.s1 *
              (∑ i : Fin (n + 1), L.cylinder (leftCombWord n i)) * L.t1 := by
                simp_rw [L.cylinder_cons_one]
                rw [Finset.mul_sum, Finset.sum_mul]
        _ = L.cylinder [0] + L.s1 * 1 * L.t1 := by
          rw [hsum]
        _ = 1 := by
          simpa [cylinder] using (L.cylinder_split []).symm

end LeavittFamily
end NonsoficGroupsExist
