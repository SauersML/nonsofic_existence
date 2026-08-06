import NonsoficGroupsExist.MainResults
import NonsoficGroupsExist.KazhdanUniverse

/-!
# The witnesses have property `(T)` in its textbook form

`MainResults` proves `HasKazhdanPropertyT.{0, 0}` for the witness groups: the
real orthogonal form of property `(T)`, quantified over Hilbert spaces in
universe `0`.  `KazhdanComplex` and `KazhdanUniverse` show that this is the
textbook property `(T)` -- unitary representations on complex Hilbert spaces
of *every* universe -- and this module records the conclusion for the
witnesses themselves, so downstream citations need no translation step.
-/

namespace NonsoficGroupsExist

universe w

/-- The explicit ambient witness `EL₄(L_{𝔽₂}(1,2))` has property `(T)` in the
textbook sense: every unitary representation on a complex Hilbert space of any
universe with a `(Q,ε)`-almost invariant unit vector has a nonzero invariant
vector. -/
theorem ambient_hasKazhdanPropertyTComplex :
    HasKazhdanPropertyTComplex.{0, w} UniversalRankFour.Ambient :=
  hasKazhdanPropertyT_iff_textbook.mp UniversalRankFour.ambient_hasKazhdanPropertyT

/-- **Theorem A with textbook property `(T)`.** For every `m ≥ 1`,
`EL_{m+1}(L_{𝔽₂}(1,2))` is finitely generated, infinite, nonsofic, and has
property `(T)` for unitary representations on complex Hilbert spaces of every
universe. -/
theorem universalLeavitt_profile_textbook (m : ℕ) (hm : 1 ≤ m) :
    Group.FG (UniversalLeavittEL m) ∧
      Infinite (UniversalLeavittEL m) ∧
      HasKazhdanPropertyTComplex.{0, w} (UniversalLeavittEL m) ∧
      ¬ IsSofic (UniversalLeavittEL m) := by
  obtain ⟨hfg, hinf, hT, hns⟩ := universalLeavitt_profile m hm
  exact ⟨hfg, hinf, hasKazhdanPropertyT_iff_textbook.mp hT, hns⟩

end NonsoficGroupsExist
