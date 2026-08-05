import NonsoficGroupsExist.ConcreteLeavitt
import Mathlib.Algebra.RingQuot
import Mathlib.RingTheory.FiniteType

/-!
# The universal binary Leavitt algebra over `ZMod 2`

This module defines the algebra denoted `L_{𝔽₂}(1,2)` in the manuscript as
the quotient of the free associative algebra on four generators by exactly the
five binary Leavitt relations.  Unlike the represented stream-operator
algebra, this quotient has the required universal property by construction.

The quotient is proved nontrivial by its canonical surjection onto the concrete
stream-operator representation.  Faithfulness of that representation is not
needed: all compression and cylinder arguments are valid in every ring carrying
a binary Leavitt family and will be instantiated directly on this universal
quotient.
-/

namespace NonsoficGroupsExist
namespace UniversalLeavitt

/-- Names of the four generators `s₀,s₁,t₀,t₁`. -/
abbrev Generator := Fin 4

def s0 : Generator := 0
def s1 : Generator := 1
def t0 : Generator := 2
def t1 : Generator := 3

abbrev Free := FreeAlgebra (ZMod 2) Generator

/-- The five equations in the presentation of `L_{𝔽₂}(1,2)`. -/
inductive Relation : Free → Free → Prop
  | t0_s0 : Relation
      (FreeAlgebra.ι (ZMod 2) t0 * FreeAlgebra.ι (ZMod 2) s0) 1
  | t0_s1 : Relation
      (FreeAlgebra.ι (ZMod 2) t0 * FreeAlgebra.ι (ZMod 2) s1) 0
  | t1_s0 : Relation
      (FreeAlgebra.ι (ZMod 2) t1 * FreeAlgebra.ι (ZMod 2) s0) 0
  | t1_s1 : Relation
      (FreeAlgebra.ι (ZMod 2) t1 * FreeAlgebra.ι (ZMod 2) s1) 1
  | sum_range : Relation
      (FreeAlgebra.ι (ZMod 2) s0 * FreeAlgebra.ι (ZMod 2) t0 +
        FreeAlgebra.ι (ZMod 2) s1 * FreeAlgebra.ι (ZMod 2) t1) 1

/-- The universal binary Leavitt algebra `L_{𝔽₂}(1,2)`. -/
abbrev BinaryLeavittAlgebra := RingQuot Relation

/-- The quotient map from noncommutative polynomials. -/
def quotientMap : Free →ₐ[ZMod 2] BinaryLeavittAlgebra :=
  RingQuot.mkAlgHom (ZMod 2) Relation

/-- A named generator in the universal quotient. -/
def generator (g : Generator) : BinaryLeavittAlgebra :=
  quotientMap (FreeAlgebra.ι (ZMod 2) g)

/-- The canonical Leavitt family in the presented quotient. -/
def family : LeavittFamily BinaryLeavittAlgebra where
  s0 := generator s0
  s1 := generator s1
  t0 := generator t0
  t1 := generator t1
  t0_s0 := by
    simpa [generator, quotientMap] using
      (RingQuot.mkAlgHom_rel (ZMod 2) Relation.t0_s0)
  t0_s1 := by
    simpa [generator, quotientMap] using
      (RingQuot.mkAlgHom_rel (ZMod 2) Relation.t0_s1)
  t1_s0 := by
    simpa [generator, quotientMap] using
      (RingQuot.mkAlgHom_rel (ZMod 2) Relation.t1_s0)
  t1_s1 := by
    simpa [generator, quotientMap] using
      (RingQuot.mkAlgHom_rel (ZMod 2) Relation.t1_s1)
  sum_range := by
    simpa [generator, quotientMap] using
      (RingQuot.mkAlgHom_rel (ZMod 2) Relation.sum_range)

/-- Evaluation of the universal presentation in an arbitrary
`ZMod 2`-algebra carrying a binary Leavitt family. -/
noncomputable def evaluation {A : Type*} [Ring A] [Algebra (ZMod 2) A]
    (L : LeavittFamily A) : Free →ₐ[ZMod 2] A :=
  FreeAlgebra.lift (ZMod 2) ![L.s0, L.s1, L.t0, L.t1]

private theorem evaluation_respects {A : Type*} [Ring A] [Algebra (ZMod 2) A]
    (L : LeavittFamily A) : ∀ {x y : Free}, Relation x y →
    evaluation L x = evaluation L y := by
  intro x y h
  cases h <;> simp [evaluation, s0, s1, t0, t1, L.t0_s0, L.t0_s1,
    L.t1_s0, L.t1_s1, L.sum_range]

/-- The universal map from `L_{𝔽₂}(1,2)` to any algebra carrying a binary
Leavitt family. -/
noncomputable def lift {A : Type*} [Ring A] [Algebra (ZMod 2) A]
    (L : LeavittFamily A) : BinaryLeavittAlgebra →ₐ[ZMod 2] A :=
  RingQuot.liftAlgHom (ZMod 2)
    ⟨evaluation L, fun {_ _} h ↦ evaluation_respects L h⟩

@[simp] theorem lift_generator {A : Type*} [Ring A] [Algebra (ZMod 2) A]
    (L : LeavittFamily A) (g : Generator) :
    lift L (generator g) = ![L.s0, L.s1, L.t0, L.t1] g := by
  simp [lift, generator, quotientMap, evaluation]

/-- The canonical map to the stream-operator representation. -/
noncomputable def streamRepresentation :
    BinaryLeavittAlgebra →ₐ[ZMod 2] ConcreteLeavitt.StreamOperatorAlgebra :=
  lift ConcreteLeavitt.family

private theorem concrete_evaluation_eq_presentation :
    evaluation ConcreteLeavitt.family = ConcreteLeavitt.presentation := by
  apply FreeAlgebra.hom_ext
  funext g
  fin_cases g <;> apply Subtype.ext
  all_goals
    simp only [Function.comp_apply]
    dsimp [evaluation, ConcreteLeavitt.presentation]
    simp [ConcreteLeavitt.evaluation, ConcreteLeavitt.family,
      ConcreteLeavitt.generator, ConcreteLeavitt.generatorOperator,
      ConcreteLeavitt.s0, ConcreteLeavitt.s1, ConcreteLeavitt.t0,
      ConcreteLeavitt.t1]

theorem streamRepresentation_surjective :
    Function.Surjective streamRepresentation := by
  intro y
  obtain ⟨p, rfl⟩ := ConcreteLeavitt.presentation_surjective y
  refine ⟨quotientMap p, ?_⟩
  change lift ConcreteLeavitt.family (quotientMap p) =
    ConcreteLeavitt.presentation p
  rw [← concrete_evaluation_eq_presentation]
  exact
    (RingQuot.liftAlgHom_mkAlgHom_apply (ZMod 2)
      (evaluation ConcreteLeavitt.family)
      (fun {_ _} h ↦ evaluation_respects ConcreteLeavitt.family h) p)

noncomputable instance : Nontrivial BinaryLeavittAlgebra :=
  Function.Surjective.nontrivial streamRepresentation_surjective

noncomputable instance : Countable BinaryLeavittAlgebra := by
  exact (RingQuot.mkAlgHom_surjective (ZMod 2) Relation).countable

instance : Algebra.FiniteType (ZMod 2) BinaryLeavittAlgebra :=
  Algebra.FiniteType.of_surjective quotientMap
    (RingQuot.mkAlgHom_surjective (ZMod 2) Relation)

noncomputable instance : Infinite BinaryLeavittAlgebra := family.infinite

end UniversalLeavitt
end NonsoficGroupsExist
