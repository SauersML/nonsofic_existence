import NonsoficGroupsExist.Leavitt.MatrixSelfSimilarity
import NonsoficGroupsExist.Leavitt.UniversalLeavittOver

/-!
# Universal `d`-ary Leavitt algebras over arbitrary fields

For a field `k` and `d ≥ 1`, `AryLeavitt.Algebra k d` is the quotient of the
free associative `k`-algebra on `s₀,…,s_{d-1},t₀,…,t_{d-1}` by exactly the
relations

  `tᵢsⱼ = δᵢⱼ`,   `∑ᵢ sᵢtᵢ = 1`,

the `d`-ary analogue of the two Leavitt relations `(eq:leavitt)` of the
manuscript.  The images of the generators form a `CompleteMatrixFamily` over
`Fin d` — the repository's packaging of a `d`-ary Leavitt family.

The quotient is nontrivial because it acts on `k`-valued functions on
infinite `d`-ary streams by prefixing and deleting initial letters
(the shift representation).  Faithfulness of this
representation is neither claimed nor needed.  Countability over a countable
field and finite type over `k` are inherited from the free algebra.
-/

namespace NonsoficGroupsExist
namespace AryLeavitt

variable (k : Type*) [Field k] (d : ℕ)

/-- Generator names: `Sum.inl i` is `sᵢ`, `Sum.inr i` is `tᵢ`. -/
abbrev Generator := Fin d ⊕ Fin d

abbrev Free := FreeAlgebra k (Generator d)

/-- The generator `sᵢ` of the free algebra. -/
def freeS (i : Fin d) : Free k d := FreeAlgebra.ι k (Sum.inl i)

/-- The generator `tᵢ` of the free algebra. -/
def freeT (i : Fin d) : Free k d := FreeAlgebra.ι k (Sum.inr i)

/-- The defining relations `tᵢsⱼ = δᵢⱼ` and `∑ᵢ sᵢtᵢ = 1`. -/
inductive Relation : Free k d → Free k d → Prop
  | orthogonal (i j : Fin d) :
      Relation (freeT k d i * freeS k d j) (if i = j then 1 else 0)
  | complete :
      Relation (∑ i : Fin d, freeS k d i * freeT k d i) 1

/-- The universal `d`-ary Leavitt algebra `L_k(1,d)`. -/
abbrev AryLeavittAlgebra := RingQuot (Relation k d)

/-- The quotient map from noncommutative polynomials. -/
def quotientMap : Free k d →ₐ[k] AryLeavittAlgebra k d :=
  RingQuot.mkAlgHom k (Relation k d)

/-- The image of `sᵢ` in the universal quotient. -/
def genS (i : Fin d) : AryLeavittAlgebra k d :=
  quotientMap k d (freeS k d i)

/-- The image of `tᵢ` in the universal quotient. -/
def genT (i : Fin d) : AryLeavittAlgebra k d :=
  quotientMap k d (freeT k d i)

/-- The canonical `d`-ary Leavitt family in the presented quotient. -/
def family : CompleteMatrixFamily (AryLeavittAlgebra k d) (Fin d) where
  left := genS k d
  right := genT k d
  orthogonal i j := by
    have h := RingQuot.mkAlgHom_rel k (Relation.orthogonal (k := k) (d := d) i j)
    rcases eq_or_ne i j with rfl | hij
    · simpa [genS, genT, quotientMap] using h
    · simpa [genS, genT, quotientMap, hij] using h
  complete := by
    have h := RingQuot.mkAlgHom_rel k (Relation.complete (k := k) (d := d))
    simpa [genS, genT, quotientMap] using h

/-! ### The `d`-ary shift representation -/

abbrev AryStream := ℕ → Fin d

abbrev StreamSpace := AryStream d → k

/-- Prepend one letter to a stream. -/
def prepend (i : Fin d) (w : AryStream d) : AryStream d
  | 0 => i
  | n + 1 => w n

/-- Delete the first letter of a stream. -/
def tail (w : AryStream d) : AryStream d := fun n => w (n + 1)

@[simp] theorem tail_prepend (i : Fin d) (w : AryStream d) :
    tail d (prepend d i w) = w := by
  funext n
  rfl

@[simp] theorem prepend_head_tail (w : AryStream d) :
    prepend d (w 0) (tail d w) = w := by
  funext n
  cases n <;> rfl

@[simp] theorem prepend_zero (i : Fin d) (w : AryStream d) :
    prepend d i w 0 = i := rfl

/-- The operator `sᵢ`: supported on streams beginning with `i`. -/
def prefixOperator (i : Fin d) : Module.End k (StreamSpace k d) where
  toFun f w := if w 0 = i then f (tail d w) else 0
  map_add' _ _ := by
    funext w
    by_cases h : w 0 = i <;> simp [h]
  map_smul' _ _ := by
    funext w
    by_cases h : w 0 = i <;> simp [h]

/-- The operator `tᵢ`: delete the letter `i` in front. -/
def deleteOperator (i : Fin d) : Module.End k (StreamSpace k d) where
  toFun f w := f (prepend d i w)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem delete_mul_prefix (i j : Fin d) :
    deleteOperator k d i * prefixOperator k d j =
      if i = j then 1 else 0 := by
  rcases eq_or_ne i j with rfl | hij
  · rw [if_pos rfl]
    ext f w
    simp [deleteOperator, prefixOperator]
  · rw [if_neg hij]
    ext f w
    simp [deleteOperator, prefixOperator, hij]

theorem prefix_delete_sum :
    ∑ i : Fin d, prefixOperator k d i * deleteOperator k d i = 1 := by
  ext f w
  have hsum :
      (∑ i : Fin d, prefixOperator k d i * deleteOperator k d i) f w =
        ∑ i : Fin d,
          (if w 0 = i then f (prepend d i (tail d w)) else 0) := by
    rw [LinearMap.sum_apply]
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => rfl
  rw [hsum, Finset.sum_ite_eq]
  simp

/-- The stream family: a `d`-ary Leavitt family on endomorphisms of the
stream space. -/
def streamFamily : CompleteMatrixFamily (Module.End k (StreamSpace k d)) (Fin d) where
  left := prefixOperator k d
  right := deleteOperator k d
  orthogonal := delete_mul_prefix k d
  complete := prefix_delete_sum k d

/-! ### Evaluation and the universal map -/

section Lift

variable {k d}
variable {A : Type*} [Ring A] [Algebra k A]

/-- Evaluation of the free presentation at any `d`-ary family. -/
noncomputable def evaluation (F : CompleteMatrixFamily A (Fin d)) :
    Free k d →ₐ[k] A :=
  FreeAlgebra.lift k (Sum.elim F.left F.right)

private theorem evaluation_respects (F : CompleteMatrixFamily A (Fin d)) :
    ∀ {x y : Free k d}, Relation k d x y → evaluation F x = evaluation F y := by
  intro x y h
  cases h with
  | orthogonal i j =>
      rcases eq_or_ne i j with rfl | hij
      · simpa [evaluation, freeS, freeT] using F.orthogonal i i
      · simpa [evaluation, freeS, freeT, hij] using F.orthogonal i j
  | complete =>
      simpa [evaluation, freeS, freeT] using F.complete

/-- The universal map from `L_k(1,d)` to any `k`-algebra carrying a
`d`-ary Leavitt family. -/
noncomputable def lift (F : CompleteMatrixFamily A (Fin d)) :
    AryLeavittAlgebra k d →ₐ[k] A :=
  RingQuot.liftAlgHom k
    ⟨evaluation F, fun {_ _} h => evaluation_respects F h⟩

@[simp] theorem lift_genS (F : CompleteMatrixFamily A (Fin d)) (i : Fin d) :
    lift F (genS k d i) = F.left i := by
  simp [lift, genS, quotientMap, evaluation, freeS]

@[simp] theorem lift_genT (F : CompleteMatrixFamily A (Fin d)) (i : Fin d) :
    lift F (genT k d i) = F.right i := by
  simp [lift, genT, quotientMap, evaluation, freeT]

end Lift

/-- The canonical (not asserted faithful) stream representation. -/
noncomputable def streamRepresentation :
    AryLeavittAlgebra k d →ₐ[k] Module.End k (StreamSpace k d) :=
  lift (streamFamily k d)

noncomputable instance [NeZero d] : Nontrivial (AryLeavittAlgebra k d) := by
  refine ⟨0, 1, ?_⟩
  intro h
  have hmap := congrArg (streamRepresentation k d) h
  rw [map_zero, map_one] at hmap
  exact zero_ne_one hmap

noncomputable instance [Countable k] : Countable (AryLeavittAlgebra k d) :=
  (RingQuot.mkAlgHom_surjective k (Relation k d)).countable

instance : Algebra.FiniteType k (AryLeavittAlgebra k d) :=
  Algebra.FiniteType.of_surjective (quotientMap k d)
    (RingQuot.mkAlgHom_surjective k (Relation k d))

end AryLeavitt
end NonsoficGroupsExist
