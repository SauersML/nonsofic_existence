import NonsoficGroupsExist.Sofic
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Positive control: the soficity definition is satisfiable

Before this control module, every use of `IsSofic` in the development was
negative.  It appears elsewhere as a
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

The left regular representation proves every finite group sofic.  Cyclic
quotients give an exact local model of the infinite cyclic group
`Multiplicative ℤ`.  `scripts/Audit.lean` pins both controls alongside the
headline results, so neither can be deleted while the negative results remain.
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
  unfold hammingDisagreement
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

/-- Every finite group is sofic without requiring callers to choose a
`Fintype` enumeration or decidable equality. -/
theorem isSofic_of_finite (G : Type) [Group G] [Finite G] : IsSofic G := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  exact isSofic_of_fintype G

/-- The infinite cyclic group is sofic.  On a prescribed finite set, reduce
integers modulo an odd modulus larger than twice every absolute value in the
set, then use the exact left regular action of that cyclic quotient. -/
theorem isSofic_multiplicative_int : IsSofic (Multiplicative ℤ) := by
  classical
  intro F ε hε
  let M : ℕ := F.sup fun g ↦ g.toAdd.natAbs
  let N : ℕ := 2 * M + 1
  have hN : N ≠ 0 := by simp [N]
  letI : NeZero N := ⟨hN⟩
  let φ : Multiplicative ℤ →* Multiplicative (ZMod N) :=
    AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod N))
  let H := Multiplicative (ZMod N)
  letI : Fintype H := inferInstance
  letI : DecidableEq H := inferInstance
  refine ⟨{ carrier := regularModel H
            nonempty := ?_
            map := fun g ↦ Equiv.mulLeft (φ g)
            multiplicative := ?_
            separated := ?_ }⟩
  · exact Fintype.card_pos_iff.mpr ⟨1⟩
  · intro g _ h _
    rw [map_mul, mulLeft_mul, hammingDistance_self]
    exact hε.le
  · intro g hg h hh hgh
    rw [hammingDistance_mulLeft H]
    · exact sub_le_self 1 hε.le
    · intro hφ
      have hcast : (g.toAdd : ZMod N) = (h.toAdd : ZMod N) := by
        simpa [φ] using congrArg Multiplicative.toAdd hφ
      have hdvd : (N : ℤ) ∣ h.toAdd - g.toAdd :=
        (ZMod.intCast_eq_intCast_iff_dvd_sub g.toAdd h.toAdd N).mp hcast
      have hdiff : h.toAdd - g.toAdd ≠ 0 := by
        intro hz
        apply hgh
        have heq : h.toAdd = g.toAdd := sub_eq_zero.mp hz
        exact congrArg Multiplicative.ofAdd heq.symm
      have hlower : N ≤ (h.toAdd - g.toAdd).natAbs := by
        simpa only [Int.natAbs_natCast] using
          Int.natAbs_le_of_dvd_ne_zero hdvd hdiff
      have hgM : g.toAdd.natAbs ≤ M := by
        exact Finset.le_sup hg
      have hhM : h.toAdd.natAbs ≤ M := by
        exact Finset.le_sup hh
      have hupper := Int.natAbs_sub_le h.toAdd g.toAdd
      omega

end NonsoficGroupsExist
