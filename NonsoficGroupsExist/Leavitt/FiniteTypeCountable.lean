import NonsoficGroupsExist.Leavitt.UniversalLeavittOver
import Mathlib.RingTheory.FiniteType

/-!
# Finite type over a finite field forces countability

`FamilyRankFour` states its endpoints for a nontrivial **countable** finite-type
algebra `A` over a finite field `k`.  Over a finite field the countability
hypothesis is redundant: `Algebra.FiniteType k A` presents `A` as a quotient of
a free algebra on finitely many generators over `k`
(`Algebra.FiniteType.iff_quotient_freeAlgebra`), and that free algebra is
countable when `k` is (`BinaryLeavitt.countableFreeAlgebra`).

This module proves exactly that implication, so that the manuscript's
Corollary `cor:fgring` can be stated with the hypotheses it prints —
"a nontrivial finite-type algebra over a finite field carrying a binary Leavitt
family" — and no countability side condition.

The ring/algebra classes match `FamilyRankFour` verbatim: `A` is an arbitrary
(possibly noncommutative) `Ring` with `[Algebra k A]`, which is why the
noncommutative `FreeAlgebra` route is used rather than `MvPolynomial`.
-/

namespace NonsoficGroupsExist

/-- **A finite-type algebra over a finite field is countable.**  The
`FreeAlgebra` presentation of `Algebra.FiniteType` has countably many elements,
and `A` is a surjective image of it. -/
theorem countable_of_finiteType (k A : Type) [Field k] [Finite k] [Ring A]
    [Algebra k A] (h : Algebra.FiniteType k A) : Countable A := by
  classical
  obtain ⟨s, f, hf⟩ :=
    (Algebra.FiniteType.iff_quotient_freeAlgebra (R := k) (A := A)).mp h
  haveI : Countable k := Finite.to_countable
  haveI : Countable (FreeAlgebra k { x // x ∈ s }) :=
    BinaryLeavitt.countableFreeAlgebra k { x // x ∈ s }
  exact hf.countable

/-- The same statement with the finite-type hypothesis taken as an instance.
This is deliberately *not* an `instance`: the coefficient field `k` occurs in no
index of the conclusion, so instance search could not determine it. -/
theorem countable_of_finiteType' (k A : Type) [Field k] [Finite k] [Ring A]
    [Algebra k A] [Algebra.FiniteType k A] : Countable A :=
  countable_of_finiteType k A inferInstance

end NonsoficGroupsExist
