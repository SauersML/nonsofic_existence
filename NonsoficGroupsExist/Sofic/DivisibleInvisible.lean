import NonsoficGroupsExist.Sofic.Sofic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Int.GCD

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

/-! ## The Prüfer centre itself -/

/-- `ℤ[1/p]` as an additive subgroup of `ℚ`, written multiplicatively so that
no division appears: `q` lies in it when some `p`-power clears its denominator. -/
def invPowSubgroup (p : ℕ) : AddSubgroup ℚ where
  carrier := {q : ℚ | ∃ (c : ℤ) (N : ℕ), (p : ℚ) ^ N * q = (c : ℚ)}
  zero_mem' := ⟨0, 0, by simp⟩
  add_mem' := by
    rintro a b ⟨c, N, hc⟩ ⟨d, M, hd⟩
    refine ⟨c * (p : ℤ) ^ M + d * (p : ℤ) ^ N, N + M, ?_⟩
    have : (p : ℚ) ^ (N + M) * (a + b)
        = (p : ℚ) ^ M * ((p : ℚ) ^ N * a) + (p : ℚ) ^ N * ((p : ℚ) ^ M * b) := by
      rw [pow_add]; ring
    rw [this, hc, hd]
    push_cast
    ring
  neg_mem' := by
    rintro a ⟨c, N, hc⟩
    exact ⟨-c, N, by push_cast; rw [mul_neg, hc]⟩

theorem mem_invPowSubgroup {p : ℕ} {q : ℚ} :
    q ∈ invPowSubgroup p ↔ ∃ (c : ℤ) (N : ℕ), (p : ℚ) ^ N * q = (c : ℚ) :=
  Iff.rfl

/-- Division by `p` stays inside `ℤ[1/p]`, exactly. -/
theorem invPowSubgroup_div_p {p : ℕ} (hp : p ≠ 0) {q : ℚ}
    (hq : q ∈ invPowSubgroup p) :
    ∃ y ∈ invPowSubgroup p, (p : ℚ) * y = q := by
  obtain ⟨c, N, hc⟩ := hq
  have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  refine ⟨q / p, ⟨c, N + 1, ?_⟩, by field_simp⟩
  rw [pow_succ]
  field_simp
  linarith [hc]

/-- Division by anything prime to `p` is possible *modulo `ℤ`*, by Bézout. -/
theorem invPowSubgroup_div_coprime {p n : ℕ} (hcop : Nat.Coprime n p) {q : ℚ}
    (hq : q ∈ invPowSubgroup p) :
    ∃ y ∈ invPowSubgroup p, (n : ℚ) * y - q ∈ AddSubgroup.zmultiples (1 : ℚ) := by
  obtain ⟨c, N, hc⟩ := hq
  have hcopN : Nat.gcd n (p ^ N) = 1 := hcop.pow_right N
  have huv : (1 : ℤ) = (n : ℤ) * Nat.gcdA n (p ^ N) + ((p : ℤ) ^ N) * Nat.gcdB n (p ^ N) := by
    have := Nat.gcd_eq_gcd_ab n (p ^ N)
    rw [hcopN] at this
    push_cast at this ⊢
    linarith [this]
  set u : ℤ := Nat.gcdA n (p ^ N) with hu
  set v : ℤ := Nat.gcdB n (p ^ N) with hv
  refine ⟨(u : ℚ) * q, ⟨u * c, N, ?_⟩, ?_⟩
  · push_cast
    rw [show (p : ℚ) ^ N * ((u : ℚ) * q) = (u : ℚ) * ((p : ℚ) ^ N * q) by ring, hc]
  · refine ⟨-(v * c), ?_⟩
    have hq' : (1 : ℚ) = (n : ℚ) * (u : ℚ) + (p : ℚ) ^ N * (v : ℚ) := by
      have := congrArg (fun z : ℤ ↦ (z : ℚ)) huv
      push_cast at this
      linarith [this]
    have hexp : q = ((n : ℚ) * (u : ℚ) + (p : ℚ) ^ N * (v : ℚ)) * q := by
      rw [← hq', one_mul]
    have hsplit : (n : ℚ) * ((u : ℚ) * q) - q = -((v : ℚ) * ((p : ℚ) ^ N * q)) := by
      nlinarith [hexp]
    rw [hc] at hsplit
    simp only [zsmul_eq_mul, mul_one]
    push_cast
    linarith [hsplit]

/-- **`ℤ[1/p]/ℤ` is divisible.**  Strong induction on `n`: the `p`-part is
divided off exactly, one factor at a time, and what remains is prime to `p` and
handled by Bezout.  Only these two moves are needed, and neither leaves the
subgroup. -/
theorem invPowSubgroup_divisible_mod_int {p : ℕ} (hp : p.Prime) :
    ∀ n : ℕ, 0 < n → ∀ q ∈ invPowSubgroup p,
      ∃ y ∈ invPowSubgroup p, (n : ℚ) * y - q ∈ AddSubgroup.zmultiples (1 : ℚ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn q hq
    by_cases hdvd : p ∣ n
    · obtain ⟨n', rfl⟩ := hdvd
      have hn' : 0 < n' := by
        rcases Nat.eq_zero_or_pos n' with h | h
        · simp [h] at hn
        · exact h
      have hlt : n' < p * n' := by
        have h2 := hp.one_lt
        nlinarith
      obtain ⟨z, hz, hzq⟩ := ih n' hlt hn' q hq
      obtain ⟨y, hy, hpy⟩ := invPowSubgroup_div_p hp.ne_zero hz
      refine ⟨y, hy, ?_⟩
      have : ((p * n' : ℕ) : ℚ) * y = (n' : ℚ) * ((p : ℚ) * y) := by push_cast; ring
      rw [this, hpy]
      exact hzq
    · exact invPowSubgroup_div_coprime
        ((Nat.Prime.coprime_iff_not_dvd hp).mpr hdvd).symm hq

/-- **The Prüfer group `ℤ(p^∞)`**, realized as the image of `ℤ[1/p]` in `ℚ/ℤ`.
This is the centre of Thom's group `K`. -/
def pruferSubgroup (p : ℕ) : AddSubgroup (ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ)) :=
  (invPowSubgroup p).map (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ)))

/-- **The Prüfer group is divisible.** -/
theorem pruferSubgroup_divisible {p : ℕ} (hp : p.Prime) (n : ℕ) (hn : 0 < n)
    (a : pruferSubgroup p) : ∃ b : pruferSubgroup p, n • b = a := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨q, hq, rfl⟩ := ha
  obtain ⟨y, hy, hyq⟩ := invPowSubgroup_divisible_mod_int hp n hn q hq
  refine ⟨⟨QuotientAddGroup.mk' _ y, ⟨y, hy, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  show n • (QuotientAddGroup.mk y : ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ))
    = QuotientAddGroup.mk q
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq]
  simpa [nsmul_eq_mul, neg_add_eq_sub] using
    (AddSubgroup.neg_mem _ hyq)

/-- **The Prüfer group is invisible to every finite quotient.**  This is the
obstruction of Remark `rem:thomK` made concrete: no finite group, hence no
finite-dimensional representation factoring through one, sees the centre of `K`. -/
theorem prufer_map_eq_zero {B : Type*} [AddGroup B] [Finite B] {p : ℕ}
    (hp : p.Prime) (f : pruferSubgroup p →+ B) (a : pruferSubgroup p) : f a = 0 :=
  map_eq_zero_of_divisible (fun n hn a ↦ pruferSubgroup_divisible hp n hn a) f a

/-- The Prüfer group is nontrivial, so the previous statement is not vacuous:
`1/p` is in `ℤ[1/p]` and is not an integer. -/
theorem pruferSubgroup_nontrivial {p : ℕ} (hp : p.Prime) :
    ∃ a : pruferSubgroup p, a ≠ 0 := by
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.pos
  have hmem : (1 / p : ℚ) ∈ invPowSubgroup p := ⟨1, 1, by rw [pow_one]; push_cast; field_simp⟩
  refine ⟨⟨QuotientAddGroup.mk' _ (1 / p : ℚ), ⟨_, hmem, rfl⟩⟩, ?_⟩
  intro hzero
  have h : (QuotientAddGroup.mk (1 / p : ℚ) : ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ)) = 0 :=
    congrArg Subtype.val hzero
  rw [QuotientAddGroup.eq_zero_iff] at h
  obtain ⟨k, hk⟩ := h
  have hk : (k : ℚ) = 1 / p := by simpa using hk
  have hlow : (0 : ℚ) < (k : ℚ) := by rw [hk]; positivity
  have hhigh : (k : ℚ) < 1 := by
    rw [hk]
    rw [div_lt_one hp0]
    exact_mod_cast hp.one_lt
  have hk1 : (1 : ℤ) ≤ k := by exact_mod_cast hlow
  have : (1 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk1
  linarith

/-! ## What a candidate for Question 3.4 needs, and what is cheap

The Pr\"ufer computations above are instances of one statement, worth isolating
because it says which half of a candidate's profile is easy.

A nontrivial *divisible* subgroup obstructs residual finiteness outright: every
homomorphism to a finite group kills it, so no finite quotient separates any of
its elements from the identity.  Nothing about centres or about the ambient
group is used.

So for a group to fail residual finiteness -- which it must, to be a candidate,
since residually finite groups are sofic -- it is enough to plant a divisible
subgroup, and a divisible centre is the cheapest way.  That is what Thom's `K`
does and what `Heis ℤ[1/p] / ℤ` does.  What such a group must *also* be is
non-amenable, since amenable groups are sofic; and that is the expensive
ingredient, the one Cornulier's Kazhdan property supplies and a Heisenberg group
cannot.  The second half is quoted, not proved here.
-/

/-- **A divisible subgroup is invisible to every finite quotient of the ambient
group.**  So a nontrivial divisible subgroup obstructs residual finiteness. -/
theorem map_eq_one_of_mem_divisible_subgroup {G : Type*} [Group G]
    (D : Subgroup G) (hdiv : ∀ n : ℕ, 0 < n → ∀ d : D, ∃ e : D, e ^ n = d)
    {B : Type*} [Group B] [Finite B] (f : G →* B) (d : D) :
    f (d : G) = 1 :=
  map_eq_one_of_divisible hdiv (f.comp D.subtype) d

/-- Stated as the obstruction: no finite quotient separates an element of a
divisible subgroup from the identity, so the ambient group is not residually
finite.  The statement is vacuous for `d = 1`; the case of interest is `d ≠ 1`,
where it is exactly a failure of residual finiteness. -/
theorem not_residuallyFinite_of_divisible_subgroup {G : Type*} [Group G]
    (D : Subgroup G) (hdiv : ∀ n : ℕ, 0 < n → ∀ d : D, ∃ e : D, e ^ n = d)
    (d : D) :
    ¬ ∃ (B : Type) (_ : Group B) (_ : Finite B) (f : G →* B), f (d : G) ≠ 1 := by
  rintro ⟨B, _, _, f, hf⟩
  exact hf (map_eq_one_of_mem_divisible_subgroup D hdiv f d)

end NonsoficGroupsExist
