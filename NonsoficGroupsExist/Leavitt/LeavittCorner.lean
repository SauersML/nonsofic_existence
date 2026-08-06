import NonsoficGroupsExist.Leavitt.Leavitt

/-!
# The complementary Leavitt corner

This file formalizes the ring-theoretic content of Lemma `lem:corner`.  The
Thompson-group embedding used in the manuscript can be composed with this
injective homomorphism of unit groups.
-/

namespace NonsoficGroupsExist
namespace LeavittFamily

variable {A : Type*} [Ring A]
variable (L : LeavittFamily A)

@[simp] theorem p0_mul_s1_mul (x : A) : L.p0 * (L.s1 * x) = 0 := by
  rw [← mul_assoc, L.p0_mul_s1, zero_mul]

@[simp] theorem t1_mul_s1_mul (x : A) : L.t1 * (L.s1 * x) = x := by
  rw [← mul_assoc, L.t1_s1, one_mul]

@[simp] theorem t0_mul_s1_mul (x : A) : L.t0 * (L.s1 * x) = 0 := by
  rw [← mul_assoc, L.t0_s1, zero_mul]

/-- The unit `p₀ + s₁*u*t₁`, with its inverse written explicitly. -/
def cornerUnit (u : Aˣ) : Aˣ where
  val := L.p0 + L.s1 * (↑u : A) * L.t1
  inv := L.p0 + L.s1 * (↑(u⁻¹) : A) * L.t1
  val_inv := by
    simp [add_mul, mul_add, mul_assoc]
  inv_val := by
    simp [add_mul, mul_add, mul_assoc]

@[simp] theorem cornerUnit_val (u : Aˣ) :
    ↑(L.cornerUnit u) = L.p0 + L.s1 * (↑u : A) * L.t1 := rfl

@[simp] theorem cornerUnit_one : L.cornerUnit 1 = 1 := by
  apply Units.ext
  simp [cornerUnit]

@[simp] theorem cornerUnit_mul (u v : Aˣ) :
    L.cornerUnit (u * v) = L.cornerUnit u * L.cornerUnit v := by
  apply Units.ext
  simp [cornerUnit, add_mul, mul_add, mul_assoc]

/-- The corner construction as a unit-group homomorphism. -/
def cornerHom : Aˣ →* Aˣ where
  toFun := L.cornerUnit
  map_one' := L.cornerUnit_one
  map_mul' := L.cornerUnit_mul

@[simp] theorem t1_cornerHom_s1 (u : Aˣ) :
    L.t1 * (↑(L.cornerHom u) : A) * L.s1 = (↑u : A) := by
  simp [cornerHom, cornerUnit, mul_add, mul_assoc]

@[simp] theorem cornerHom_s0 (u : Aˣ) :
    (↑(L.cornerHom u) : A) * L.s0 = L.s0 := by
  simp [cornerHom, cornerUnit, add_mul, mul_assoc]

@[simp] theorem t0_cornerHom (u : Aˣ) :
    L.t0 * (↑(L.cornerHom u) : A) = L.t0 := by
  simp [cornerHom, cornerUnit, mul_add, mul_assoc]

theorem cornerHom_injective : Function.Injective L.cornerHom := by
  intro u v huv
  apply Units.ext
  have h := congrArg (fun x : Aˣ ↦ L.t1 * (↑x : A) * L.s1) huv
  simpa using h

@[simp] theorem p1_mul_s0_mul (x : A) : L.p1 * (L.s0 * x) = 0 := by
  rw [← mul_assoc, L.p1_mul_s0, zero_mul]

@[simp] theorem t0_mul_s0_mul (x : A) : L.t0 * (L.s0 * x) = x := by
  rw [← mul_assoc, L.t0_s0, one_mul]

@[simp] theorem t1_mul_s0_mul (x : A) : L.t1 * (L.s0 * x) = 0 := by
  rw [← mul_assoc, L.t1_s0, zero_mul]

@[simp] theorem p1_add_p0 : L.p1 + L.p0 = 1 := by
  calc
    L.p1 + L.p0 = L.p0 + L.p1 := add_comm _ _
    _ = 1 := L.p0_add_p1

@[simp] theorem p1_add_s0t0 : L.p1 + L.s0 * L.t0 = 1 := by
  change L.p1 + L.p0 = 1
  exact L.p1_add_p0

@[simp] theorem p1_mul_s1_mul (x : A) : L.p1 * (L.s1 * x) = L.s1 * x := by
  rw [← mul_assoc, L.p1_mul_s1]

@[simp] theorem p0_mul_s0_mul (x : A) : L.p0 * (L.s0 * x) = L.s0 * x := by
  rw [← mul_assoc, L.p0_mul_s0]

/-- The unit `p₁ + s₀*u*t₀` occupying the complementary corner. -/
def compressedUnit (u : Aˣ) : Aˣ where
  val := L.p1 + L.s0 * (↑u : A) * L.t0
  inv := L.p1 + L.s0 * (↑(u⁻¹) : A) * L.t0
  val_inv := by
    simp [add_mul, mul_add, mul_assoc]
  inv_val := by
    simp [add_mul, mul_add, mul_assoc]

@[simp] theorem compressedUnit_one : L.compressedUnit 1 = 1 := by
  apply Units.ext
  change L.p1 + L.s0 * (1 : A) * L.t0 = 1
  simp

@[simp] theorem compressedUnit_mul (u v : Aˣ) :
    L.compressedUnit (u * v) = L.compressedUnit u * L.compressedUnit v := by
  apply Units.ext
  simp [compressedUnit, add_mul, mul_add, mul_assoc]

/-- The compressed complementary-corner homomorphism. -/
def compressedHom : Aˣ →* Aˣ where
  toFun := L.compressedUnit
  map_one' := L.compressedUnit_one
  map_mul' := L.compressedUnit_mul

@[simp] theorem t0_compressedHom_s0 (u : Aˣ) :
    L.t0 * (↑(L.compressedHom u) : A) * L.s0 = (↑u : A) := by
  simp [compressedHom, compressedUnit, mul_add, mul_assoc]

@[simp] theorem compressedHom_s1 (u : Aˣ) :
    (↑(L.compressedHom u) : A) * L.s1 = L.s1 := by
  simp [compressedHom, compressedUnit, add_mul, mul_assoc]

@[simp] theorem t1_compressedHom (u : Aˣ) :
    L.t1 * (↑(L.compressedHom u) : A) = L.t1 := by
  simp [compressedHom, compressedUnit, mul_add, mul_assoc]

theorem compressedHom_injective : Function.Injective L.compressedHom := by
  intro u v huv
  apply Units.ext
  have h := congrArg (fun x : Aˣ ↦ L.t0 * (↑x : A) * L.s0) huv
  simpa using h

/-- The complementary corner images commute elementwise. -/
theorem compressedHom_commutes_cornerHom (u v : Aˣ) :
    L.compressedHom u * L.cornerHom v = L.cornerHom v * L.compressedHom u := by
  apply Units.ext
  simp [compressedHom, compressedUnit, cornerHom, cornerUnit, add_mul, mul_add, mul_assoc,
    add_comm]

/-- Equality of elements in the two complementary corner images is trivial. -/
theorem compressedHom_eq_cornerHom_iff (u v : Aˣ) :
    L.compressedHom u = L.cornerHom v ↔ u = 1 ∧ v = 1 := by
  constructor
  · intro huv
    constructor
    · apply Units.ext
      have h := congrArg (fun x : Aˣ ↦ L.t0 * (↑x : A) * L.s0) huv
      simpa using h
    · apply Units.ext
      have h := congrArg (fun x : Aˣ ↦ L.t1 * (↑x : A) * L.s1) huv
      simpa using h.symm
  · rintro ⟨rfl, rfl⟩
    simp

end LeavittFamily
end NonsoficGroupsExist
