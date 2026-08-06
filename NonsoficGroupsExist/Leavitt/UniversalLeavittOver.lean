import NonsoficGroupsExist.Leavitt.Leavitt
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.RingQuot
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Finsupp.Encodable
import Mathlib.RingTheory.FiniteType
import Mathlib.SetTheory.Cardinal.Free
import Mathlib.Tactic.FinCases

/-!
# Universal binary Leavitt algebras over arbitrary fields

For a field `k`, `BinaryLeavitt.Algebra k` is the quotient of the free
associative `k`-algebra on `s₀,s₁,t₀,t₁` by exactly the five relations

`tᵢsⱼ = δᵢⱼ`,  `s₀t₀ + s₁t₁ = 1`.

The quotient is nontrivial because it acts on `k`-valued functions on infinite
binary streams by prefixing and deleting initial bits. Faithfulness of this
representation is neither claimed nor needed.
-/

namespace NonsoficGroupsExist
namespace BinaryLeavitt

/-- Names of the four generators `s₀,s₁,t₀,t₁`. -/
abbrev Generator := Fin 4

def s0 : Generator := 0
def s1 : Generator := 1
def t0 : Generator := 2
def t1 : Generator := 3

abbrev Free (k : Type*) [Field k] := FreeAlgebra k Generator

/-- The five equations in the presentation of `L_k(1,2)`. -/
inductive Relation (k : Type*) [Field k] : Free k → Free k → Prop
  | t0_s0 : Relation k
      (FreeAlgebra.ι k t0 * FreeAlgebra.ι k s0) 1
  | t0_s1 : Relation k
      (FreeAlgebra.ι k t0 * FreeAlgebra.ι k s1) 0
  | t1_s0 : Relation k
      (FreeAlgebra.ι k t1 * FreeAlgebra.ι k s0) 0
  | t1_s1 : Relation k
      (FreeAlgebra.ι k t1 * FreeAlgebra.ι k s1) 1
  | sum_range : Relation k
      (FreeAlgebra.ι k s0 * FreeAlgebra.ι k t0 +
        FreeAlgebra.ι k s1 * FreeAlgebra.ι k t1) 1

/-- The universal binary Leavitt algebra `L_k(1,2)`. -/
abbrev BinaryLeavittAlgebra (k : Type*) [Field k] := RingQuot (Relation k)

/-- The quotient map from noncommutative polynomials. -/
def quotientMap (k : Type*) [Field k] : Free k →ₐ[k] BinaryLeavittAlgebra k :=
  RingQuot.mkAlgHom k (Relation k)

/-- A named generator in the universal quotient. -/
def generator (k : Type*) [Field k] (g : Generator) : BinaryLeavittAlgebra k :=
  quotientMap k (FreeAlgebra.ι k g)

/-- The canonical Leavitt family in the presented quotient. -/
def family (k : Type*) [Field k] : LeavittFamily (BinaryLeavittAlgebra k) where
  s0 := generator k s0
  s1 := generator k s1
  t0 := generator k t0
  t1 := generator k t1
  t0_s0 := by
    simpa [generator, quotientMap] using
      (RingQuot.mkAlgHom_rel k (Relation.t0_s0 (k := k)))
  t0_s1 := by
    simpa [generator, quotientMap] using
      (RingQuot.mkAlgHom_rel k (Relation.t0_s1 (k := k)))
  t1_s0 := by
    simpa [generator, quotientMap] using
      (RingQuot.mkAlgHom_rel k (Relation.t1_s0 (k := k)))
  t1_s1 := by
    simpa [generator, quotientMap] using
      (RingQuot.mkAlgHom_rel k (Relation.t1_s1 (k := k)))
  sum_range := by
    simpa [generator, quotientMap] using
      (RingQuot.mkAlgHom_rel k (Relation.sum_range (k := k)))

/-- Evaluation of the universal presentation in an arbitrary `k`-algebra
carrying a binary Leavitt family. -/
noncomputable def evaluation {k A : Type*} [Field k] [Ring A] [Algebra k A]
    (L : LeavittFamily A) : Free k →ₐ[k] A :=
  FreeAlgebra.lift k ![L.s0, L.s1, L.t0, L.t1]

private theorem evaluation_respects {k A : Type*} [Field k] [Ring A]
    [Algebra k A] (L : LeavittFamily A) :
    ∀ {x y : Free k}, Relation k x y → evaluation L x = evaluation L y := by
  intro x y h
  cases h <;> simp [evaluation, s0, s1, t0, t1, L.t0_s0, L.t0_s1,
    L.t1_s0, L.t1_s1, L.sum_range]

/-- The universal map from `L_k(1,2)` to any `k`-algebra carrying a binary
Leavitt family. -/
noncomputable def lift {k A : Type*} [Field k] [Ring A] [Algebra k A]
    (L : LeavittFamily A) : BinaryLeavittAlgebra k →ₐ[k] A :=
  RingQuot.liftAlgHom k
    ⟨evaluation L, fun {_ _} h ↦ evaluation_respects L h⟩

@[simp] theorem lift_generator {k A : Type*} [Field k] [Ring A] [Algebra k A]
    (L : LeavittFamily A) (g : Generator) :
    lift L (generator k g) = ![L.s0, L.s1, L.t0, L.t1] g := by
  simp [lift, generator, quotientMap, evaluation]

/-! ### A nonzero stream representation -/

abbrev BinaryStream := ℕ → Fin 2
abbrev StreamSpace (k : Type*) := BinaryStream → k

def prepend (i : Fin 2) (w : BinaryStream) : BinaryStream
  | 0 => i
  | n + 1 => w n

def tail (w : BinaryStream) : BinaryStream := fun n ↦ w (n + 1)

@[simp] theorem tail_prepend (i : Fin 2) (w : BinaryStream) :
    tail (prepend i w) = w := by
  funext n
  rfl

@[simp] theorem prepend_head_tail (w : BinaryStream) :
    prepend (w 0) (tail w) = w := by
  funext n
  cases n <;> rfl

@[simp] theorem prepend_zero (i : Fin 2) (w : BinaryStream) :
    prepend i w 0 = i := rfl

def prefixOperator (k : Type*) [Field k] (i : Fin 2) :
    Module.End k (StreamSpace k) where
  toFun f w := if w 0 = i then f (tail w) else 0
  map_add' _ _ := by
    funext w
    by_cases h : w 0 = i <;> simp [h]
  map_smul' _ _ := by
    funext w
    by_cases h : w 0 = i <;> simp [h]

def deleteOperator (k : Type*) [Field k] (i : Fin 2) :
    Module.End k (StreamSpace k) where
  toFun f w := f (prepend i w)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem delete_mul_prefix_same (k : Type*) [Field k] (i : Fin 2) :
    deleteOperator k i * prefixOperator k i = 1 := by
  ext f w
  simp [deleteOperator, prefixOperator]

theorem delete_mul_prefix_ne (k : Type*) [Field k] {i j : Fin 2} (hij : i ≠ j) :
    deleteOperator k i * prefixOperator k j = 0 := by
  ext f w
  simp [deleteOperator, prefixOperator, hij]

theorem prefix_delete_sum (k : Type*) [Field k] :
    prefixOperator k 0 * deleteOperator k 0 +
      prefixOperator k 1 * deleteOperator k 1 = 1 := by
  ext f w
  have hw : w 0 = 0 ∨ w 0 = 1 := by omega
  rcases hw with hw | hw
  · simpa [prefixOperator, deleteOperator, hw] using congrArg f (prepend_head_tail w)
  · simpa [prefixOperator, deleteOperator, hw] using congrArg f (prepend_head_tail w)

def streamFamily (k : Type*) [Field k] :
    LeavittFamily (Module.End k (StreamSpace k)) where
  s0 := prefixOperator k 0
  s1 := prefixOperator k 1
  t0 := deleteOperator k 0
  t1 := deleteOperator k 1
  t0_s0 := delete_mul_prefix_same k 0
  t0_s1 := delete_mul_prefix_ne k (by decide : (0 : Fin 2) ≠ 1)
  t1_s0 := delete_mul_prefix_ne k (by decide : (1 : Fin 2) ≠ 0)
  t1_s1 := delete_mul_prefix_same k 1
  sum_range := prefix_delete_sum k

/-- The canonical (not asserted faithful) stream representation. -/
noncomputable def streamRepresentation (k : Type*) [Field k] :
    BinaryLeavittAlgebra k →ₐ[k] Module.End k (StreamSpace k) :=
  lift (streamFamily k)

noncomputable instance (k : Type*) [Field k] :
    Nontrivial (BinaryLeavittAlgebra k) := by
  refine ⟨0, 1, ?_⟩
  intro h
  have hmap := congrArg (streamRepresentation k) h
  rw [map_zero, map_one] at hmap
  exact zero_ne_one hmap

noncomputable instance countableFreeAlgebra (k X : Type*) [Field k]
    [Countable k] [Countable X] : Countable (FreeAlgebra k X) := by
  letI : Countable (FreeMonoid X) :=
    Countable.of_equiv (List X) (FreeMonoid.ofList (α := X))
  letI : Countable (MonoidAlgebra k (FreeMonoid X)) :=
    Countable.of_equiv ((FreeMonoid X) →₀ k)
      (MonoidAlgebra.coeffEquiv (R := k) (M := FreeMonoid X)).symm
  exact Countable.of_equiv (MonoidAlgebra k (FreeMonoid X))
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := k) (X := X)).symm.toEquiv

noncomputable instance (k : Type*) [Field k] [Countable k] :
    Countable (BinaryLeavittAlgebra k) := by
  exact (RingQuot.mkAlgHom_surjective k (Relation k)).countable

instance (k : Type*) [Field k] :
    Algebra.FiniteType k (BinaryLeavittAlgebra k) :=
  Algebra.FiniteType.of_surjective (quotientMap k)
    (RingQuot.mkAlgHom_surjective k (Relation k))

noncomputable instance (k : Type*) [Field k] :
    Infinite (BinaryLeavittAlgebra k) :=
  (family k).infinite

end BinaryLeavitt
end NonsoficGroupsExist
