import NonsoficGroupsExist.Sofic.DivisibleInvisible

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
elaborate because it must also be finitely presented and Kazhdan; `Heis ℤ[1/p]`
is neither, and is residually finite, so it is no candidate for Question 3.4.
And nothing here computes the quotient by `ℤ`.  What it does supply is the
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

end Heis

end NonsoficGroupsExist
