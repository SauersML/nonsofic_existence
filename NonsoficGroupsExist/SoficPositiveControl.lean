import NonsoficGroupsExist.Sofic
import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Positive control: the soficity definition is satisfiable

Every other use of `IsSofic` in this development is negative.  It appears as a
hypothesis to be refuted (`not_isSofic_of_not_isLEF`), as a hypothesis to be
transported (`SoficTransfer`), or as the conclusion of the two headline
theorems under a `¬`.  Before this module, nothing anywhere in the library
exhibited a single group satisfying `IsSofic`, and `SoficModel` was never once
constructed.

That is a gap in the same shape as a detector that has never been shown to
fire.  A scan that reports nothing is indistinguishable from a clean corpus
until a planted defect proves it can report something; likewise `¬ IsSofic G`
is indistinguishable from `IsSofic` being unsatisfiable -- a definition
accidentally so strong that no group at all meets it -- until some group is
shown to meet it.  Under an unsatisfiable definition every theorem in this
repository would still be true, every proof would still be kernel-checked, the
axiom audit would still be clean, and the result would be worth nothing.

So: the left regular representation of a finite group is an exact permutation
model, and finite groups are sofic.  `scripts/Audit.lean` pins this theorem
alongside the headline results, so the control cannot be deleted while the
negative results remain.

This closes the vacuity question only for finite groups.  The natural next
control is an infinite one -- `Multiplicative ℤ`, or residually finite implies
sofic -- and until one exists, what is ruled out is a definition unsatisfiable
outright, not a definition that is accidentally too strong on infinite groups.
-/

namespace NonsoficGroupsExist

/-- A finite group, viewed as a permutation model of itself. -/
abbrev regularModel (G : Type) [Group G] [Fintype G] [DecidableEq G] : FiniteModel :=
  ⟨G, inferInstance, inferInstance⟩

@[simp] theorem regularModel_carrier (G : Type) [Group G] [Fintype G] [DecidableEq G] :
    (regularModel G).carrier = G := rfl

/-- The left regular representation is an exact homomorphism, so the model is
multiplicative with error `0` rather than merely `ε`. -/
theorem mulLeft_mul (G : Type) [Group G] (g h : G) :
    (Equiv.mulLeft (g * h) : Equiv.Perm G) = Equiv.mulLeft g * Equiv.mulLeft h := by
  ext x
  simp [Equiv.Perm.mul_apply]

/-- Left translation by distinct elements disagrees *everywhere*: the model
separates with error `0` rather than merely `1 - ε`. -/
theorem hammingDistance_mulLeft (G : Type) [Group G] [Fintype G] [DecidableEq G]
    {g h : G} (hgh : g ≠ h) :
    hammingDistance (regularModel G) (Equiv.mulLeft g : Equiv.Perm G)
      (Equiv.mulLeft h : Equiv.Perm G) = 1 := by
  have hpos : 0 < Fintype.card G := Fintype.card_pos_iff.mpr ⟨1⟩
  have hcard : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
  have hfilter :
      (Finset.univ.filter fun y : G ↦ (Equiv.mulLeft g) y ≠ (Equiv.mulLeft h) y)
        = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro y _
    simp only [Equiv.coe_mulLeft, ne_eq]
    intro hy
    exact hgh (mul_right_cancel hy)
  unfold hammingDistance
  change
    ((Finset.univ.filter fun y : G ↦
      (Equiv.mulLeft g) y ≠ (Equiv.mulLeft h) y).card : ℝ) /
        Fintype.card G = 1
  rw [hfilter, Finset.card_univ]
  exact div_self hcard

/-- **Positive control.**  Every finite group is sofic, witnessed by its own
left regular representation.  `IsSofic` is therefore satisfiable, and the
negative results elsewhere in this development are statements about groups
rather than about an empty predicate. -/
theorem isSofic_of_fintype (G : Type) [Group G] [Fintype G] [DecidableEq G] :
    IsSofic G := by
  intro F ε hε
  refine ⟨{ carrier := regularModel G
            nonempty := ?_
            map := fun g ↦ Equiv.mulLeft g
            multiplicative := ?_
            separated := ?_ }⟩
  · show 0 < Fintype.card G
    exact Fintype.card_pos_iff.mpr ⟨1⟩
  · intro g _ h _
    rw [mulLeft_mul, hammingDistance_self]
    exact hε.le
  · intro g _ h _ hgh
    rw [hammingDistance_mulLeft G hgh]
    exact sub_le_self 1 hε.le

end NonsoficGroupsExist
