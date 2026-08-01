import NonsoficGroupsExist.Leavitt

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

end LeavittFamily
end NonsoficGroupsExist
