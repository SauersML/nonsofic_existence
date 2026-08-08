import NonsoficGroupsExist.Sofic.Sofic
import Mathlib.GroupTheory.OrderOfElement

/-!
# Divisible subgroups are invisible to finite quotients

A step used informally elsewhere in this development, and used by several
external analyses of the hyperlinear question, deserves to be checked: a
divisible group has no nontrivial homomorphism to a finite group.  The proof is
two lines -- write `d = e^{|B|}` and apply Lagrange -- but the conclusion is
what makes the candidate groups of Remark `rem:thomK` behave the way they do.

The consequence in that setting: for Thom's group `K = K₀(ℤ[1/p])/ℤ`, whose
centre contains the Prüfer group `ℤ(p^∞)`, *every* finite quotient kills that
centre.  Hence no finite-dimensional unitary representation obtained from a
finite quotient separates the central elements, and (with Malcev, since a
finitely generated linear group is residually finite and a residually finite
divisible abelian group is trivial by the same argument) no finite-dimensional
representation does.  That is why the approximations for such a group are
forced to be projective, and why their matrix models land in the monomial group
of `Sofic.MonomialModel` rather than anywhere more general.

Nothing here is about soficity; it is the arithmetic behind a structural claim
that the manuscript makes, isolated so that the claim does not rest on prose.
-/

namespace NonsoficGroupsExist

/-- **A divisible group has no nontrivial homomorphism to a finite group.**
Write `d = e ^ |B|` and apply Lagrange to `f e`. -/
theorem map_eq_one_of_divisible {D B : Type*} [Group D] [Group B] [Finite B]
    (hdiv : ∀ n : ℕ, 0 < n → ∀ d : D, ∃ e : D, e ^ n = d)
    (f : D →* B) (d : D) : f d = 1 := by
  classical
  haveI := Fintype.ofFinite B
  obtain ⟨e, he⟩ := hdiv (Fintype.card B) Fintype.card_pos d
  rw [← he, map_pow, pow_card_eq_one]

/-- The additive form. -/
theorem map_eq_zero_of_divisible {D B : Type*} [AddGroup D] [AddGroup B]
    [Finite B] (hdiv : ∀ n : ℕ, 0 < n → ∀ d : D, ∃ e : D, n • e = d)
    (f : D →+ B) (d : D) : f d = 0 := by
  classical
  haveI := Fintype.ofFinite B
  obtain ⟨e, he⟩ := hdiv (Fintype.card B) Fintype.card_pos d
  rw [← he, map_nsmul, card_nsmul_eq_zero]

/-- **A finite divisible group is trivial**: apply the above to the identity. -/
theorem eq_one_of_finite_divisible {D : Type*} [Group D] [Finite D]
    (hdiv : ∀ n : ℕ, 0 < n → ∀ d : D, ∃ e : D, e ^ n = d) (d : D) : d = 1 :=
  map_eq_one_of_divisible hdiv (MonoidHom.id D) d

/-- The rationals are divisible. -/
theorem rat_divisible (n : ℕ) (hn : 0 < n) (q : ℚ) : ∃ r : ℚ, n • r = q := by
  refine ⟨q / n, ?_⟩
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [nsmul_eq_mul]
  field_simp

/-- Positive control: every homomorphism from the rationals to a finite group is
trivial, so the statement is not vacuous. -/
theorem rat_map_eq_zero {B : Type*} [AddGroup B] [Finite B] (f : ℚ →+ B)
    (q : ℚ) : f q = 0 :=
  map_eq_zero_of_divisible rat_divisible f q

/-! ## The concrete centre -/

/-- Divisibility passes to quotients. -/
theorem divisible_quotient {A : Type*} [AddCommGroup A] (B : AddSubgroup A)
    (hdiv : ∀ n : ℕ, 0 < n → ∀ a : A, ∃ b : A, n • b = a) (n : ℕ) (hn : 0 < n)
    (a : A ⧸ B) : ∃ b : A ⧸ B, n • b = a := by
  refine QuotientAddGroup.induction_on a fun x ↦ ?_
  obtain ⟨y, hy⟩ := hdiv n hn x
  exact ⟨QuotientAddGroup.mk y, by rw [← QuotientAddGroup.mk_nsmul, hy]⟩

/-- `ℚ/ℤ` is divisible.  The centre of Thom's group is the Prüfer group
`ℤ[1/p]/ℤ`, a subgroup of this one and divisible for the same reason. -/
theorem ratCircle_divisible (n : ℕ) (hn : 0 < n)
    (a : ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ)) :
    ∃ b : ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ), n • b = a :=
  divisible_quotient _ rat_divisible n hn a

/-- **The circle group of rationals is invisible to every finite quotient.**
This is the shape of the obstruction in Remark `rem:thomK`: a divisible centre
that no finite quotient, hence no finite-dimensional representation, can see. -/
theorem ratCircle_map_eq_zero {B : Type*} [AddGroup B] [Finite B]
    (f : (ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ)) →+ B)
    (a : ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ)) : f a = 0 :=
  map_eq_zero_of_divisible ratCircle_divisible f a

end NonsoficGroupsExist
