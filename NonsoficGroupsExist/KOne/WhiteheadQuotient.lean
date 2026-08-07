import NonsoficGroupsExist.KOne.RefineLoopDischarge
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# `K₁(L_k(1,2))` as a quotient group

The `K₁` chain of `RefineLoopDischarge` closes the statement
`stableUnits_eq_top_holds`: *every* unit of `L_k(1,2)` has elementary diagonal
stabilization.  Stated that way it is a membership fact about a subgroup.  This
module packages it as the group it names.

`stableUnits R ≤ Rˣ` is the subgroup of units whose `2 × 2` diagonal
stabilization `diag(u, 1)` is elementary; it is normal
(`MatrixDiagonalization.stableUnits_normal`).  The quotient

  `Lˣ / stableUnits L`

is `K₁(L)` **in Whitehead form** — the Whitehead group of the diagonal class
construction of `DiagonalClassGroup`.  Here it is proved trivial.

What this is *not*: the classical `K₁(L) = colim_n GL_n(L)/E_n(L)` is a direct
limit over the ranks, and that colimit object is **not** constructed anywhere in
this library.  What the library does prove is the two facts that, taken
together, compute the classical group: this Whitehead quotient is trivial, and
`BinaryLeavitt.elementaryGroup_eq_top` (via `glAll_eq_elementary`) gives
`GL_r(L) = EL_r(L)` at *every* rank `r ≥ 2`, so every term of the direct system
is already trivial.  Deducing `K₁(L) = 0` from those two inputs is a one-line
argument about colimits which is left to the reader; it is not formalized.
-/

namespace NonsoficGroupsExist

open MatrixDiagonalization

/-- **The Whitehead subgroup is everything.**  Subgroup form of
`BinaryLeavitt.stableUnits_eq_top_holds` (`= BinaryLeavitt.K1_trivial`). -/
theorem binaryLeavittStableUnits_eq_top (k : Type) [Field k] :
    stableUnits (BinaryLeavitt.BinaryLeavittAlgebra k) = ⊤ := by
  rw [eq_top_iff]
  intro u _
  exact BinaryLeavitt.stableUnits_eq_top_holds k u

/-- `K₁(L_k(1,2))` in Whitehead form: the unit group modulo the normal subgroup
of units with elementary diagonal stabilization. -/
noncomputable abbrev BinaryLeavittWhiteheadK1 (k : Type) [Field k] : Type :=
  (BinaryLeavitt.BinaryLeavittAlgebra k)ˣ ⧸
    stableUnits (BinaryLeavitt.BinaryLeavittAlgebra k)

/-- **`K₁(L_k(1,2))` in Whitehead form is trivial**, over every field. -/
instance binaryLeavittWhiteheadK1_subsingleton (k : Type) [Field k] :
    Subsingleton (BinaryLeavittWhiteheadK1 k) := by
  constructor
  intro x y
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  have ha : (QuotientGroup.mk a : BinaryLeavittWhiteheadK1 k) = 1 :=
    (QuotientGroup.eq_one_iff a).mpr (BinaryLeavitt.stableUnits_eq_top_holds k a)
  have hb : (QuotientGroup.mk b : BinaryLeavittWhiteheadK1 k) = 1 :=
    (QuotientGroup.eq_one_iff b).mpr (BinaryLeavitt.stableUnits_eq_top_holds k b)
  rw [ha, hb]

/-- The trivial group structure on the Whitehead `K₁`, in `Unique` form. -/
noncomputable def binaryLeavittWhiteheadK1Unique (k : Type) [Field k] :
    Unique (BinaryLeavittWhiteheadK1 k) where
  default := 1
  uniq a := Subsingleton.elim a 1

end NonsoficGroupsExist
