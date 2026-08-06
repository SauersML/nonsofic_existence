import NonsoficGroupsExist.Endpoint.MainResults
import NonsoficGroupsExist.Covers.KazhdanCover
import NonsoficGroupsExist.Kazhdan.ShalomFinitePresentation
import NonsoficGroupsExist.Kun.KunDecomposition
import NonsoficGroupsExist.KunThom.KunThomTheorem
import NonsoficGroupsExist.KOne.RefineLoopDischarge
import NonsoficGroupsExist.Kazhdan.KazhdanTextbook

/-!
# The public results

The library is organized by the order the mathematics was discovered, which is
not the order anyone should read it in.  This module is the reading path: the
declarations a referee actually needs, each named against the theorem of
`nonsofic_groups_exist.tex` it establishes, and nothing else.  Follow the
imports downward from here.

Nothing is proved in this module.  It re-exports, so that `#check` on any name
below lands on the real statement and its module.

The full statement-by-statement correspondence is `docs/CLAIM_MAP.md`,
generated from the manuscript's margin notes; this module is the short list.

## The headline

* `nonsofic_groups_exist` -- a nonsofic group exists.  Theorem A.
* `universalLeavittEL4_not_isSofic` -- the explicit witness: `EL₄` over the
  universal binary Leavitt algebra `L_{𝔽₂}(1,2)`.
* `ambient_full_profile` -- that group is countable, finitely generated,
  infinite, Kazhdan, and not sofic.
* `exists_finitelyPresented_nonsofic_group` -- Theorem C, first assertion.
* `exists_infinite_finitelyPresented_nonsofic_ambient_cover` -- and it covers
  the explicit ambient group.

## The external inputs that are proved here rather than cited

Every theorem the paper cites for its own proofs is proved outright here, so
these are inputs to the *paper* and not to the *library*.

* `KunDecomposition.exists_expanderDecomposition` -- Kun's expander
  decomposition, Theorem 2.9, in the one-way full-sequence form used.
* `KunThomTheorem.isLEF_of_exactProductExpansion` -- the Kun--Thom centralizer
  obstruction, Theorem 2.10.
* `Shalom.exists_finitelyPresented_kazhdan_cover` -- Shalom's theorem: every
  finitely generated Kazhdan group is a quotient of a finitely presented one.
* `finiteFieldElementaryThree_hasKazhdanPropertyT` (in
  `PropertyT/FiniteFieldElementaryPropertyT`)
  -- property `(T)` at rank three, Theorem 5.7, for finite-type algebras over
  every finite field, with the explicit Kazhdan pair of
  `FreeElementaryPropertyT`.  This is the case the paper states and consumes;
  `LeavittRankEquivalence.rankSuccEquiv` spreads it to every rank.  The
  Ershov--Jaikin-Zapirain theorem over an arbitrary finitely generated ring is
  *not* formalized, and nothing here needs it.

The non-LEF witness is likewise internal: no simplicity or finite-presentation
theorem for Thompson's `V` is used (`ThompsonFObstruction`,
`ThompsonWitness`).

## The `K₁` chain

Elementary and unconditional, replacing the localization-sequence input.
Appendix A of the manuscript is this chain written out.

* `BinaryLeavitt.K1_trivial` -- `K₁(L_k(1,2)) = 0` in Whitehead form.
* `BinaryLeavitt.narrowReduction_holds` -- the two-exit elimination behind it.
* `BinaryLeavitt.glTwo_eq_elementary_holds`,
  `BinaryLeavitt.glFour_eq_elementary_holds` -- `GL = EL` at ranks two and four.

## What the definitions mean

An audit of axioms says nothing about whether the statement proved is the
statement intended.  These two discharge the definitional questions that carry
the most weight, as theorems rather than as caveats.

* `hasKazhdanPropertyT_iff_textbook` -- the real-orthogonal, own-universe
  property `(T)` used throughout is the textbook complex-unitary property
  quantified over every universe.
* `isLEF_iff_textbook` -- likewise for local embeddability.

## Trust surface

`NonsoficGroupsExist.Audit` prints the axiom report for these on an ordinary
build.  `scripts/Audit.lean` independently walks the transitive axiom closure
of the whole namespace and fails on anything beyond `propext`,
`Classical.choice`, and `Quot.sound`.
-/

namespace NonsoficGroupsExist.Public

open NonsoficGroupsExist

/-! ### The headline -/

export NonsoficGroupsExist (nonsofic_groups_exist universalLeavittEL4_not_isSofic
  ambient_full_profile exists_finitelyPresented_nonsofic_group
  exists_infinite_finitelyPresented_nonsofic_ambient_cover)

/-! ### Reach of the construction -/

export NonsoficGroupsExist (universalLeavitt_profile binaryLeavitt_finiteField_profile
  binaryLeavittUnits_not_isSofic binaryLeavittGL_not_isSofic
  universalLeavittEL3_not_isSofic)

/-! ### Inputs proved rather than cited -/

export NonsoficGroupsExist.KunDecomposition (exists_expanderDecomposition)
export NonsoficGroupsExist.KunThomTheorem (isLEF_of_exactProductExpansion)
export NonsoficGroupsExist.Shalom (exists_finitelyPresented_kazhdan_cover)
export NonsoficGroupsExist (finiteFieldElementaryThree_hasKazhdanPropertyT)
export NonsoficGroupsExist (exists_kazhdan_finitelyPresented_cover_of_not_isSofic)

/-! ### The `K₁` chain -/

export NonsoficGroupsExist.BinaryLeavitt (K1_trivial narrowReduction_holds
  glTwo_eq_elementary_holds glFour_eq_elementary_holds)

/-! ### The definitions are the textbook ones -/

export NonsoficGroupsExist (hasKazhdanPropertyT_iff_textbook isLEF_iff_textbook)

end NonsoficGroupsExist.Public
