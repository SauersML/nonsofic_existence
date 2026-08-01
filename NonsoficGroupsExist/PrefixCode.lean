import NonsoficGroupsExist.LeavittWords
import NonsoficGroupsExist.MatrixSelfSimilarity

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
end NonsoficGroupsExist
