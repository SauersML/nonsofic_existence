import NonsoficGroupsExist.Sofic.DivisibleInvisible
import Mathlib.Algebra.Ring.Subring.Defs

/-!
# The Heisenberg group over a ring, and its centre

Remark `rem:thomK` rests on a group whose centre is a copy of the coefficient
ring, so that quotienting by a copy of `ℤ` inside it leaves a *divisible* centre
-- the Prüfer group, invisible to every finite quotient by
`prufer_map_eq_zero`.  That structure is quoted there from de Cornulier and
Thom.  This file builds the simplest group with it, from scratch, so that the
shape of the argument does not depend on the literature.

For a commutative ring `R` the Heisenberg group `Heis R` is `R³` with

    (a,b,c) · (a',b',c') = (a+a', b+b', c+c'+ab'),

the unitriangular `3×3` matrices in disguise.  Its centre is exactly the third
coordinate (`mem_center_iff`), so `Heis R` has centre `(R,+)`: the coefficient
ring appears as the centre on the nose.

Two things this is not.  It is not de Cornulier's `K₀(ℤ[1/p])`, which is more
elaborate because it must also be finitely presented and Kazhdan.  And nothing
in the first half computes the quotient by `ℤ`.  Why the group here is no
candidate for Question 3.4 is taken up at the end, and the reason is not the
obvious one.  What it does supply is the
centre computation itself, which is the part `rem:thomK` uses structurally and
which no longer has to be taken on trust.
-/

namespace NonsoficGroupsExist

/-- The Heisenberg group over a commutative ring: `R³` with the unitriangular
multiplication. -/
@[ext]
structure Heis (R : Type*) [CommRing R] where
  /-- First superdiagonal entry. -/
  a : R
  /-- Second superdiagonal entry. -/
  b : R
  /-- Corner entry; this coordinate is the centre. -/
  c : R

namespace Heis

variable {R : Type*} [CommRing R]

instance : Mul (Heis R) :=
  ⟨fun x y ↦ ⟨x.a + y.a, x.b + y.b, x.c + y.c + x.a * y.b⟩⟩

instance : One (Heis R) := ⟨⟨0, 0, 0⟩⟩

instance : Inv (Heis R) :=
  ⟨fun x ↦ ⟨-x.a, -x.b, -x.c + x.a * x.b⟩⟩

@[simp] theorem mul_a (x y : Heis R) : (x * y).a = x.a + y.a := rfl
@[simp] theorem mul_b (x y : Heis R) : (x * y).b = x.b + y.b := rfl
@[simp] theorem mul_c (x y : Heis R) : (x * y).c = x.c + y.c + x.a * y.b := rfl
@[simp] theorem one_a : (1 : Heis R).a = 0 := rfl
@[simp] theorem one_b : (1 : Heis R).b = 0 := rfl
@[simp] theorem one_c : (1 : Heis R).c = 0 := rfl
@[simp] theorem inv_a (x : Heis R) : x⁻¹.a = -x.a := rfl
@[simp] theorem inv_b (x : Heis R) : x⁻¹.b = -x.b := rfl
@[simp] theorem inv_c (x : Heis R) : x⁻¹.c = -x.c + x.a * x.b := rfl

instance : Group (Heis R) where
  mul_assoc x y z := by
    ext <;> simp <;> ring
  one_mul x := by ext <;> simp
  mul_one x := by ext <;> simp
  inv_mul_cancel x := by
    ext
    · simp
    · simp
    · simp

/-- **The centre of the Heisenberg group is exactly its third coordinate.**
Commuting with `(0,1,0)` forces the first coordinate to vanish and commuting
with `(1,0,0)` forces the second; conversely those two vanishing make the
commutator term `ab' - a'b` vanish identically. -/
theorem mem_center_iff (x : Heis R) :
    x ∈ Subgroup.center (Heis R) ↔ x.a = 0 ∧ x.b = 0 := by
  constructor
  · intro hx
    rw [Subgroup.mem_center_iff] at hx
    refine ⟨?_, ?_⟩
    · simpa using congrArg Heis.c (hx ⟨0, 1, 0⟩)
    · simpa using congrArg Heis.c (hx ⟨1, 0, 0⟩)
  · rintro ⟨ha, hb⟩
    rw [Subgroup.mem_center_iff]
    intro y
    ext
    · simp [add_comm]
    · simp [add_comm]
    · simp [ha, hb, add_comm]

/-- So the centre is the coefficient ring: `(0,0,c)` is central for every `c`. -/
theorem mk_zero_zero_mem_center (c : R) :
    (⟨0, 0, c⟩ : Heis R) ∈ Subgroup.center (Heis R) :=
  (mem_center_iff _).mpr ⟨rfl, rfl⟩

/-- and the assignment `c ↦ (0,0,c)` is a homomorphism from `(R,+)`, so the
centre contains a copy of the additive group of the ring. -/
theorem mk_zero_zero_mul (c d : R) :
    (⟨0, 0, c⟩ : Heis R) * ⟨0, 0, d⟩ = ⟨0, 0, c + d⟩ := by
  ext <;> simp

/-- The centre is not larger than the third coordinate: an element with a
nonzero first coordinate fails to commute with `(0,1,0)`. -/
theorem not_mem_center_of_a_ne_zero (x : Heis R) (hx : x.a ≠ 0) :
    x ∉ Subgroup.center (Heis R) := by
  intro hmem
  exact hx ((mem_center_iff x).mp hmem).1


/-! ## The centre is the ring, and survives a central quotient

Two further steps are what `rem:thomK` uses.  First, the centre is not merely
described by the third coordinate but *is* the additive group of `R`: the map
`c ↦ (0,0,c)` is injective, turns addition into multiplication, and has the
centre as its exact range.  Second, central elements stay central in a quotient
by a central subgroup, so the centre of `Heis R / Z` contains `(R,+)/Z`.

With `R = ℤ[1/p]` and `Z` the copy of `ℤ`, that is the Prüfer group, which
`prufer_map_eq_zero` shows every finite quotient kills.  The identification of
`(R,+)/Z` with `pruferSubgroup p` is not carried out here; what is, is that the
centre is the ring and that centrality survives the quotient.
-/

/-- The coordinate embedding of the ring into the Heisenberg group is
injective. -/
theorem mk_zero_zero_injective :
    Function.Injective (fun c : R ↦ (⟨0, 0, c⟩ : Heis R)) := by
  intro c d h
  exact congrArg Heis.c h

/-- **The centre is exactly the range of the ring.**  Together with
`mk_zero_zero_mul` and `mk_zero_zero_injective`, the centre of `Heis R` is
`(R,+)`. -/
theorem center_eq_range :
    (Subgroup.center (Heis R) : Set (Heis R))
      = Set.range (fun c : R ↦ (⟨0, 0, c⟩ : Heis R)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨ha, hb⟩ := (mem_center_iff x).mp hx
    exact ⟨x.c, by ext <;> simp [ha, hb]⟩
  · rintro ⟨c, rfl⟩
    exact mk_zero_zero_mem_center c

end Heis

/-- **Central elements stay central in a central quotient.**  Nothing about the
Heisenberg group is used; this is the step that carries a centre through
`G ⧸ Z`. -/
theorem mk_mem_center_of_mem_center {G : Type*} [Group G] (Z : Subgroup G)
    [Z.Normal] (x : G) (hx : x ∈ Subgroup.center G) :
    (QuotientGroup.mk' Z x) ∈ Subgroup.center (G ⧸ Z) := by
  rw [Subgroup.mem_center_iff]
  intro y
  refine QuotientGroup.induction_on y fun g ↦ ?_
  rw [Subgroup.mem_center_iff] at hx
  show (QuotientGroup.mk' Z g) * (QuotientGroup.mk' Z x)
    = (QuotientGroup.mk' Z x) * (QuotientGroup.mk' Z g)
  rw [← map_mul, ← map_mul, hx g]

/-- So the centre of a Heisenberg quotient by a central subgroup contains the
image of the ring: `Heis R ⧸ Z` has `(R,+)/Z` inside its centre. -/
theorem Heis.mk_zero_zero_mem_center_quotient {R : Type*} [CommRing R]
    (Z : Subgroup (Heis R)) [Z.Normal] (c : R) :
    (QuotientGroup.mk' Z (⟨0, 0, c⟩ : Heis R)) ∈ Subgroup.center (Heis R ⧸ Z) :=
  mk_mem_center_of_mem_center Z _ (Heis.mk_zero_zero_mem_center c)


/-! ## The Prüfer centre, realized in a group

Putting the pieces together needs `ℤ[1/p]` as a *ring*, since `Heis` takes a
commutative ring; `invPowSubgroup` was only an additive subgroup.  It is closed
under multiplication -- `p^N q = c` and `p^M r = d` give `p^{N+M}(qr) = cd` --
so it is a subring, and `Heis` of it makes sense.

Then the point of the construction appears.  The centre is `ℤ[1/p]`, which is
*not* divisible; quotienting by the copy of `ℤ` inside it makes it divisible,
because dividing by `p` stays inside and dividing by anything prime to `p` works
modulo `ℤ` (`invPowSubgroup_divisible_mod_int`).  So every homomorphism from the
quotient to a finite group kills the image of the centre -- by Lagrange, exactly
as in `map_eq_one_of_divisible`, and with no representation theory anywhere.

This is the mechanism of `rem:thomK` in a genuine group, end to end.  The group
is not Thom's: `Heis ℤ[1/p]` is residually finite and neither finitely
presented nor Kazhdan, so it is no candidate for Question 3.4.  What it shows is
that the mechanism is real and needs nothing quoted.
-/

/-- `ℤ[1/p]` as a subring of `ℚ`, so that `Heis` can take it as coefficients. -/
def invPowSubring (p : ℕ) : Subring ℚ where
  __ := invPowSubgroup p
  one_mem' := ⟨1, 0, by norm_num⟩
  mul_mem' := by
    rintro a b ⟨c, N, hc⟩ ⟨d, M, hd⟩
    refine ⟨c * d, N + M, ?_⟩
    have : (p : ℚ) ^ (N + M) * (a * b)
        = ((p : ℚ) ^ N * a) * ((p : ℚ) ^ M * b) := by
      rw [pow_add]; ring
    rw [this, hc, hd]
    push_cast
    ring

namespace Heis

/-- The copy of `ℤ` sitting inside the centre of `Heis R`. -/
def intCentre (R : Type*) [CommRing R] : Subgroup (Heis R) where
  carrier := {x | x.a = 0 ∧ x.b = 0 ∧ ∃ n : ℤ, x.c = (n : R)}
  one_mem' := ⟨rfl, rfl, 0, by simp⟩
  mul_mem' := by
    rintro x y ⟨hxa, hxb, n, hn⟩ ⟨hya, hyb, k, hk⟩
    refine ⟨by simp [hxa, hya], by simp [hxb, hyb], n + k, ?_⟩
    simp [hn, hk, hxa]
  inv_mem' := by
    rintro x ⟨hxa, hxb, n, hn⟩
    refine ⟨by simp [hxa], by simp [hxb], -n, ?_⟩
    simp [hn, hxa, hxb]

/-- It is central, hence normal. -/
instance intCentre_normal (R : Type*) [CommRing R] : (intCentre R).Normal where
  conj_mem := by
    rintro x ⟨hxa, hxb, n, hn⟩ g
    have hcen : x ∈ Subgroup.center (Heis R) := (mem_center_iff x).mpr ⟨hxa, hxb⟩
    rw [Subgroup.mem_center_iff] at hcen
    have : g * x * g⁻¹ = x := by
      rw [hcen g, mul_assoc, mul_inv_cancel, mul_one]
    rw [this]
    exact ⟨hxa, hxb, n, hn⟩

end Heis

/-- Powers of a central element multiply the coordinate. -/
theorem Heis.mk_zero_zero_pow {R : Type*} [CommRing R] (c : R) (n : ℕ) :
    (⟨0, 0, c⟩ : Heis R) ^ n = ⟨0, 0, (n : R) * c⟩ := by
  induction n with
  | zero => ext <;> simp
  | succ k ih =>
      rw [pow_succ, ih]
      ext
      · simp
      · simp
      · simp
        ring

/-- **The centre of `Heis ℤ[1/p]` modulo `ℤ` is killed by every homomorphism to
a finite group.**  This is `rem:thomK`'s mechanism in a group built here: the
centre is `ℤ[1/p]`, not divisible; the quotient by `ℤ` makes it divisible; and
Lagrange finishes.  No representation theory anywhere. -/
theorem heis_centre_map_eq_one {p : ℕ} (hp : p.Prime) {B : Type*} [Group B]
    [Finite B]
    (f : (Heis (invPowSubring p) ⧸ Heis.intCentre (invPowSubring p)) →* B)
    (q : invPowSubring p) :
    f (QuotientGroup.mk' _ (⟨0, 0, q⟩ : Heis (invPowSubring p))) = 1 := by
  classical
  haveI := Fintype.ofFinite B
  obtain ⟨y, hy, hdiff⟩ :=
    invPowSubgroup_divisible_mod_int hp (Fintype.card B) Fintype.card_pos
      (q : ℚ) q.2
  obtain ⟨k, hk⟩ := hdiff
  -- the two central elements differ by an integer, so agree in the quotient
  have hsame : QuotientGroup.mk' (Heis.intCentre (invPowSubring p))
      (⟨0, 0, q⟩ : Heis (invPowSubring p))
      = QuotientGroup.mk' _ (⟨0, 0, ⟨y, hy⟩⟩ : Heis (invPowSubring p))
        ^ Fintype.card B := by
    rw [← map_pow, Heis.mk_zero_zero_pow]
    refine (QuotientGroup.mk'_eq_mk' _).mpr ⟨⟨0, 0, ⟨(k : ℚ), ?_⟩⟩, ⟨rfl, rfl, k, ?_⟩, ?_⟩
    · exact ⟨k, 0, by norm_num⟩
    · rfl
    · ext
      · simp
      · simp
      · have hq : (k : ℚ) = ((Fintype.card B : ℕ) : ℚ) * y - (q : ℚ) := by
          simpa [zsmul_eq_mul] using hk
        simp only [Heis.mul_c, zero_mul, add_zero]
        push_cast
        linarith [hq]
  rw [hsame, map_pow, pow_card_eq_one]


/-! ## Why this group is not a candidate, and what the right reason is

It would be easy to write that `Heis ℤ[1/p] / ℤ` is not a candidate for
Question 3.4 because it is residually finite.  That is false, and
`heis_centre_map_eq_one` is the proof: every homomorphism to a finite group
kills the image of the centre, which is nontrivial, so the group is *not*
residually finite.  It has exactly the failure of residual finiteness that makes
Thom's `K` interesting.

The real reason is different and simpler.  `Heis R` is `2`-step nilpotent -- the
commutator of any two elements is central (`commutator_mem_center`) -- and
nilpotent groups are amenable, hence sofic.  So the group is sofic for reasons
having nothing to do with its centre, and is no test of anything.

That is also what distinguishes Cornulier's `K₀(ℤ[1/p])`: being Kazhdan, it is
as far from amenable as a group can be, which is precisely why its central
quotient can be a candidate when this one cannot.  The obstruction to using a
Heisenberg group here is nilpotence, not residual finiteness.
-/

/-- **`Heis R` is `2`-step nilpotent**: every commutator is central.  The first
two coordinates are additive, so they cancel in `xyx⁻¹y⁻¹`, leaving an element
of the centre by `mem_center_iff`. -/
theorem Heis.commutator_mem_center {R : Type*} [CommRing R] (x y : Heis R) :
    x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center (Heis R) := by
  refine (Heis.mem_center_iff _).mpr ⟨?_, ?_⟩
  · simp
  · simp


/-! ### The extension is non-split, and that is visible in one commutator

The profile a candidate needs asks for the central extension to be non-split:
if `G` were `(G/Z) × Z` the divisible centre would split off and buy nothing.
For the Heisenberg group that is settled by a computation rather than an
argument -- the centre is *generated by commutators*:

    [(1,0,0), (0,1,0)] = (0,0,1),

so the central element `1` is a commutator (`commutator_generators`).  Hence the
centre meets the commutator subgroup nontrivially whenever `1 ≠ 0` in `R`, and
no direct-product decomposition can separate it off.

This is the one part of the candidate profile that the Heisenberg construction
does supply.  What it does not supply is non-amenability, by
`commutator_mem_center`; a group meeting the whole profile has to get the centre
this way while failing to be nilpotent.
-/

/-- **The centre is generated by commutators**: the two basic generators have
commutator `(0,0,1)`.  This is what makes the central extension non-split. -/
theorem Heis.commutator_generators {R : Type*} [CommRing R] :
    (⟨1, 0, 0⟩ : Heis R) * ⟨0, 1, 0⟩ * (⟨1, 0, 0⟩ : Heis R)⁻¹
        * (⟨0, 1, 0⟩ : Heis R)⁻¹
      = ⟨0, 0, 1⟩ := by
  ext <;> simp

/-- So `Heis R` is non-abelian as soon as `R` is nontrivial, and the witness is
explicit. -/
theorem Heis.not_commute {R : Type*} [CommRing R] [Nontrivial R] :
    (⟨1, 0, 0⟩ : Heis R) * ⟨0, 1, 0⟩ ≠ (⟨0, 1, 0⟩ : Heis R) * ⟨1, 0, 0⟩ := by
  intro h
  have hc := congrArg Heis.c h
  simp at hc

end NonsoficGroupsExist
