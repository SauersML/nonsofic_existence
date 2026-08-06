import NonsoficGroupsExist.Leavitt.Leavitt
import NonsoficGroupsExist.Leavitt.UniversalLeavittOver
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.RingQuot

/-!
# Universal binary Leavitt algebras over arbitrary commutative rings

`UniversalLeavittOver` presents `L_k(1,2)` over a field `k`.  Nothing in that
presentation uses inverses of scalars: the generators, the five relations,
the universal property, and the stream representation that witnesses
nontriviality are all defined over an arbitrary commutative ring of
coefficients.  This module restates the construction at that generality.
The case `R = ℤ` is the *integral* binary Leavitt algebra `L_ℤ(1,2)`, the
coefficient ring for which the property-`(T)` input of
Ershov–Jaikin-Zapirain is stated in the literature but not yet formalized
in this library; `IntegralConditional` consumes the algebra built here.

Concretely, `CommRingLeavitt.LeavittAlgebra R` is the quotient of the free
associative `R`-algebra on `s₀,s₁,t₀,t₁` by exactly

  `tᵢsⱼ = δᵢⱼ`,   `s₀t₀ + s₁t₁ = 1`.

It is nontrivial whenever `R` is (the shift representation on `R`-valued
functions on binary streams is nonzero), countable whenever `R` is, and of
finite type over `R` by construction.
-/

namespace NonsoficGroupsExist
namespace CommRingLeavitt

/-- Names of the four generators `s₀,s₁,t₀,t₁`. -/
abbrev Generator := Fin 4

def s0 : Generator := 0
def s1 : Generator := 1
def t0 : Generator := 2
def t1 : Generator := 3

variable (R : Type*) [CommRing R]

abbrev Free := FreeAlgebra R Generator

/-- The five equations in the presentation of `L_R(1,2)`. -/
inductive Relation : Free R → Free R → Prop
  | t0_s0 : Relation
      (FreeAlgebra.ι R t0 * FreeAlgebra.ι R s0) 1
  | t0_s1 : Relation
      (FreeAlgebra.ι R t0 * FreeAlgebra.ι R s1) 0
  | t1_s0 : Relation
      (FreeAlgebra.ι R t1 * FreeAlgebra.ι R s0) 0
  | t1_s1 : Relation
      (FreeAlgebra.ι R t1 * FreeAlgebra.ι R s1) 1
  | sum_range : Relation
      (FreeAlgebra.ι R s0 * FreeAlgebra.ι R t0 +
        FreeAlgebra.ι R s1 * FreeAlgebra.ι R t1) 1

/-- The universal binary Leavitt algebra `L_R(1,2)` over the commutative
ring `R`. -/
abbrev LeavittAlgebra := RingQuot (Relation R)

/-- The quotient map from noncommutative polynomials. -/
def quotientMap : Free R →ₐ[R] LeavittAlgebra R :=
  RingQuot.mkAlgHom R (Relation R)

/-- A named generator in the universal quotient. -/
def generator (g : Generator) : LeavittAlgebra R :=
  quotientMap R (FreeAlgebra.ι R g)

/-- The canonical binary Leavitt family in the presented quotient. -/
def family : LeavittFamily (LeavittAlgebra R) where
  s0 := generator R s0
  s1 := generator R s1
  t0 := generator R t0
  t1 := generator R t1
  t0_s0 := by
    simpa [generator, quotientMap] using
      (RingQuot.mkAlgHom_rel R (Relation.t0_s0 (R := R)))
  t0_s1 := by
    simpa [generator, quotientMap] using
      (RingQuot.mkAlgHom_rel R (Relation.t0_s1 (R := R)))
  t1_s0 := by
    simpa [generator, quotientMap] using
      (RingQuot.mkAlgHom_rel R (Relation.t1_s0 (R := R)))
  t1_s1 := by
    simpa [generator, quotientMap] using
      (RingQuot.mkAlgHom_rel R (Relation.t1_s1 (R := R)))
  sum_range := by
    simpa [generator, quotientMap] using
      (RingQuot.mkAlgHom_rel R (Relation.sum_range (R := R)))

/-! ### Evaluation and the universal map -/

section Lift

variable {R}
variable {A : Type*} [Ring A] [Algebra R A]

/-- Evaluation of the universal presentation in an arbitrary `R`-algebra
carrying a binary Leavitt family. -/
noncomputable def evaluation (L : LeavittFamily A) : Free R →ₐ[R] A :=
  FreeAlgebra.lift R ![L.s0, L.s1, L.t0, L.t1]

private theorem evaluation_respects (L : LeavittFamily A) :
    ∀ {x y : Free R}, Relation R x y → evaluation L x = evaluation L y := by
  intro x y h
  cases h <;> simp [evaluation, s0, s1, t0, t1, L.t0_s0, L.t0_s1,
    L.t1_s0, L.t1_s1, L.sum_range]

/-- The universal map from `L_R(1,2)` to any `R`-algebra carrying a binary
Leavitt family. -/
noncomputable def lift (L : LeavittFamily A) : LeavittAlgebra R →ₐ[R] A :=
  RingQuot.liftAlgHom R
    ⟨evaluation L, fun {_ _} h => evaluation_respects L h⟩

@[simp] theorem lift_generator (L : LeavittFamily A) (g : Generator) :
    lift L (generator R g) = ![L.s0, L.s1, L.t0, L.t1] g := by
  simp [lift, generator, quotientMap, evaluation]

end Lift

/-! ### The stream representation and nontriviality

The operators are those of `UniversalLeavittOver`, with values in `R`
rather than in a field: `sᵢ` is supported on streams beginning with `i` and
deletes nothing, `tᵢ` prepends the letter `i`.  The relations hold by the
same two-line computations, and the representation of `1` is nonzero as
soon as `R` is nontrivial. -/

abbrev StreamSpace := BinaryLeavitt.BinaryStream → R

/-- The operator `sᵢ` on `R`-valued stream functions. -/
def prefixOperator (i : Fin 2) : Module.End R (StreamSpace R) where
  toFun f w := if w 0 = i then f (BinaryLeavitt.tail w) else 0
  map_add' _ _ := by
    funext w
    by_cases h : w 0 = i <;> simp [h]
  map_smul' _ _ := by
    funext w
    by_cases h : w 0 = i <;> simp [h]

/-- The operator `tᵢ` on `R`-valued stream functions. -/
def deleteOperator (i : Fin 2) : Module.End R (StreamSpace R) where
  toFun f w := f (BinaryLeavitt.prepend i w)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem delete_mul_prefix_same (i : Fin 2) :
    deleteOperator R i * prefixOperator R i = 1 := by
  ext f w
  simp [deleteOperator, prefixOperator]

theorem delete_mul_prefix_ne {i j : Fin 2} (hij : i ≠ j) :
    deleteOperator R i * prefixOperator R j = 0 := by
  ext f w
  simp [deleteOperator, prefixOperator, hij]

theorem prefix_delete_sum :
    prefixOperator R 0 * deleteOperator R 0 +
      prefixOperator R 1 * deleteOperator R 1 = 1 := by
  ext f w
  have hw : w 0 = 0 ∨ w 0 = 1 := by omega
  rcases hw with hw | hw
  · simpa [prefixOperator, deleteOperator, hw] using
      congrArg f (BinaryLeavitt.prepend_head_tail w)
  · simpa [prefixOperator, deleteOperator, hw] using
      congrArg f (BinaryLeavitt.prepend_head_tail w)

/-- The stream family over `R`. -/
def streamFamily : LeavittFamily (Module.End R (StreamSpace R)) where
  s0 := prefixOperator R 0
  s1 := prefixOperator R 1
  t0 := deleteOperator R 0
  t1 := deleteOperator R 1
  t0_s0 := delete_mul_prefix_same R 0
  t0_s1 := delete_mul_prefix_ne R (by decide : (0 : Fin 2) ≠ 1)
  t1_s0 := delete_mul_prefix_ne R (by decide : (1 : Fin 2) ≠ 0)
  t1_s1 := delete_mul_prefix_same R 1
  sum_range := prefix_delete_sum R

/-- The canonical (not asserted faithful) stream representation. -/
noncomputable def streamRepresentation :
    LeavittAlgebra R →ₐ[R] Module.End R (StreamSpace R) :=
  lift (streamFamily R)

noncomputable instance [Nontrivial R] : Nontrivial (LeavittAlgebra R) := by
  refine ⟨0, 1, ?_⟩
  intro h
  have hmap := congrArg (streamRepresentation R) h
  rw [map_zero, map_one] at hmap
  exact zero_ne_one hmap

/-! ### Countability and finite type -/

noncomputable instance countableFree [Countable R] : Countable (Free R) := by
  letI : Countable (FreeMonoid Generator) :=
    Countable.of_equiv (List Generator) (FreeMonoid.ofList (α := Generator))
  letI : Countable (MonoidAlgebra R (FreeMonoid Generator)) :=
    Countable.of_equiv ((FreeMonoid Generator) →₀ R)
      (MonoidAlgebra.coeffEquiv (R := R) (M := FreeMonoid Generator)).symm
  exact Countable.of_equiv (MonoidAlgebra R (FreeMonoid Generator))
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid
      (R := R) (X := Generator)).symm.toEquiv

noncomputable instance [Countable R] : Countable (LeavittAlgebra R) :=
  (RingQuot.mkAlgHom_surjective R (Relation R)).countable

instance : Algebra.FiniteType R (LeavittAlgebra R) :=
  Algebra.FiniteType.of_surjective (quotientMap R)
    (RingQuot.mkAlgHom_surjective R (Relation R))

/-! ### The integral algebra -/

/-- The integral binary Leavitt algebra `L_ℤ(1,2)`. -/
noncomputable abbrev IntegralLeavittAlgebra := LeavittAlgebra ℤ

/-- Its canonical binary Leavitt family. -/
noncomputable abbrev integralFamily : LeavittFamily IntegralLeavittAlgebra :=
  family ℤ

end CommRingLeavitt
end NonsoficGroupsExist
