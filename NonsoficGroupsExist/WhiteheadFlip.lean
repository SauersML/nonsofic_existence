import NonsoficGroupsExist.DiagonalClassGroup

/-!
# The Whitehead flip: `1 + xy` and `1 + yx` agree modulo the diagonal class

If `1 + xy` is a unit then so is `1 + yx`, with inverse
`1 - y(1+xy)⁻¹x`, and `diag(1+xy, (1+yx)⁻¹)` factors into four
elementary matrices
`E₁₂(x)·E₂₁(y)·E₁₂(-(1+xy)⁻¹x)·E₂₁(-(1+yx)y)`.
Consequently `(1+xy)·(1+yx)⁻¹` lies in the diagonal class group — the
`K₁` flip identity `[1+xy] = [1+yx]`, the depth-crossing move of the
residual-class endgame.
-/

namespace NonsoficGroupsExist
namespace MatrixDiagonalization

variable {A : Type*} [Ring A]

/-- The flipped unit `1 + yx`, given that `1 + xy` is a unit. -/
def flipUnit (x y : A) (u : Aˣ) (hu : (u : A) = 1 + x * y) : Aˣ where
  val := 1 + y * x
  inv := 1 - y * ((u⁻¹ : Aˣ) : A) * x
  val_inv := by
    have h1 : (1 + y * x) * (1 - y * ((u⁻¹ : Aˣ) : A) * x) =
        1 + y * x - y * ((1 + x * y) * ((u⁻¹ : Aˣ) : A)) * x := by
      noncomm_ring
    rw [h1, ← hu, Units.mul_inv]
    noncomm_ring
  inv_val := by
    have h1 : (1 - y * ((u⁻¹ : Aˣ) : A) * x) * (1 + y * x) =
        1 + y * x - y * (((u⁻¹ : Aˣ) : A) * (1 + x * y)) * x := by
      noncomm_ring
    rw [h1, ← hu, Units.inv_mul]
    noncomm_ring

@[simp] theorem flipUnit_val (x y : A) (u : Aˣ)
    (hu : (u : A) = 1 + x * y) :
    (flipUnit x y u hu : A) = 1 + y * x := rfl

@[simp] theorem flipUnit_inv_val (x y : A) (u : Aˣ)
    (hu : (u : A) = 1 + x * y) :
    (((flipUnit x y u hu)⁻¹ : Aˣ) : A) =
      1 - y * ((u⁻¹ : Aˣ) : A) * x := rfl

/-- Product of complementary triangular two-by-two matrices. -/
theorem tri_mul_tri (p q : A) :
    (!![1, p; 0, 1] : Matrix (Fin 2) (Fin 2) A) * !![1, 0; q, 1] =
      !![1 + p * q, p; q, 1] := by
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The elementary units with entries at `(0,1)` and `(1,0)` are the
triangular matrices. -/
theorem elementaryUnit01_tri (p : A) :
    ((elementaryUnit (0 : Fin 2) 1 (by decide) p :
      (Matrix (Fin 2) (Fin 2) A)ˣ) : Matrix (Fin 2) (Fin 2) A) =
      !![1, p; 0, 1] := by
  show (1 : Matrix (Fin 2) (Fin 2) A) + Matrix.single 0 1 p = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.single_apply_same]

theorem elementaryUnit10_tri (q : A) :
    ((elementaryUnit (1 : Fin 2) 0 (by decide) q :
      (Matrix (Fin 2) (Fin 2) A)ˣ) : Matrix (Fin 2) (Fin 2) A) =
      !![1, 0; q, 1] := by
  show (1 : Matrix (Fin 2) (Fin 2) A) + Matrix.single 1 0 q = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.single_apply_same]

/-- **The flip factorization**: `diag(1+xy, (1+yx)⁻¹)` is a product of
four elementary matrices. -/
theorem diagPair_flipUnit_inv_mem (x y : A) (u : Aˣ)
    (hu : (u : A) = 1 + x * y) :
    diagPair u (flipUnit x y u hu)⁻¹ ∈ elementaryGroup (Fin 2) A := by
  set v : A := ((u⁻¹ : Aˣ) : A) with hv
  have huv : (1 + x * y) * v = 1 := by
    rw [hv, ← hu, Units.mul_inv]
  have hwv : (1 - y * v * x) * (1 + y * x) = 1 :=
    Units.inv_mul (flipUnit x y u hu)
  have h5 : y * v * x * (1 + y * x) = y * x := by
    have h6 : (1 + y * x) - y * v * x * (1 + y * x) = 1 := by
      calc (1 + y * x) - y * v * x * (1 + y * x)
          = (1 - y * v * x) * (1 + y * x) := by noncomm_ring
        _ = 1 := hwv
    have h7 := congrArg (fun z ↦ (1 + y * x) - z) h6
    calc y * v * x * (1 + y * x)
        = (1 + y * x) - ((1 + y * x) - y * v * x * (1 + y * x)) := by
          abel
      _ = (1 + y * x) - 1 := h7
      _ = y * x := by abel
  have hprod : elementaryUnit (0 : Fin 2) 1 (by decide) x *
      elementaryUnit (1 : Fin 2) 0 (by decide) y *
      (elementaryUnit (0 : Fin 2) 1 (by decide) (-(v * x)) *
        elementaryUnit (1 : Fin 2) 0 (by decide)
          (-((1 + y * x) * y))) =
      diagPair u (flipUnit x y u hu)⁻¹ := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul,
      elementaryUnit01_tri, elementaryUnit10_tri, elementaryUnit01_tri,
      elementaryUnit10_tri, tri_mul_tri, tri_mul_tri]
    show _ = !![(u : A), 0; 0, 1 - y * v * x]
    rw [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j
    · show (1 + x * y) * (1 + -(v * x) * -((1 + y * x) * y)) +
        x * -((1 + y * x) * y) = (u : A)
      calc (1 + x * y) * (1 + -(v * x) * -((1 + y * x) * y)) +
            x * -((1 + y * x) * y)
          = (1 + x * y) +
            ((1 + x * y) * v) * (x * ((1 + y * x) * y)) -
            x * ((1 + y * x) * y) := by noncomm_ring
        _ = (1 + x * y) + 1 * (x * ((1 + y * x) * y)) -
            x * ((1 + y * x) * y) := by rw [huv]
        _ = 1 + x * y := by noncomm_ring
        _ = (u : A) := hu.symm
    · show (1 + x * y) * -(v * x) + x * 1 = 0
      calc (1 + x * y) * -(v * x) + x * 1
          = -(((1 + x * y) * v) * x) + x := by noncomm_ring
        _ = -(1 * x) + x := by rw [huv]
        _ = 0 := by noncomm_ring
    · show y * (1 + -(v * x) * -((1 + y * x) * y)) +
        1 * -((1 + y * x) * y) = 0
      calc y * (1 + -(v * x) * -((1 + y * x) * y)) +
            1 * -((1 + y * x) * y)
          = (y * v * x * (1 + y * x)) * y + y -
            (1 + y * x) * y := by noncomm_ring
        _ = (y * x) * y + y - (1 + y * x) * y := by rw [h5]
        _ = 0 := by noncomm_ring
    · show y * -(v * x) + 1 * 1 = 1 - y * v * x
      noncomm_ring
  rw [← hprod]
  exact mul_mem (mul_mem (elementaryUnit_mem _ _ _ _)
      (elementaryUnit_mem _ _ _ _))
    (mul_mem (elementaryUnit_mem _ _ _ _) (elementaryUnit_mem _ _ _ _))

theorem diagPair_one_eq_diagUnit (w : Aˣ) :
    diagPair w 1 = diagUnit w := by
  apply Units.ext
  show !![(w : A), 0; 0, ((1 : Aˣ) : A)] = !![(w : A), 0; 0, 1]
  rw [Units.val_one]

/-- **The Whitehead flip in the unit group**: `(1+xy)·(1+yx)⁻¹` lies
in the diagonal class group. -/
theorem mul_flipUnit_inv_mem_stableUnits (x y : A) (u : Aˣ)
    (hu : (u : A) = 1 + x * y) :
    u * (flipUnit x y u hu)⁻¹ ∈ stableUnits A := by
  rw [mem_stableUnits_iff]
  have h1 := diagPair_flipUnit_inv_mem x y u hu
  have h2 : diagPair (flipUnit x y u hu) (flipUnit x y u hu)⁻¹ ∈
      elementaryGroup (Fin 2) A :=
    diagPair_inv_self_mem (flipUnit x y u hu)
  have h3 := mul_mem h1 (inv_mem h2)
  have h4 : diagPair u (flipUnit x y u hu)⁻¹ *
      (diagPair (flipUnit x y u hu) (flipUnit x y u hu)⁻¹)⁻¹ =
      diagUnit (u * (flipUnit x y u hu)⁻¹) := by
    rw [diagPair_inv, diagPair_mul, inv_inv,
      inv_mul_cancel, diagPair_one_eq_diagUnit]
  rwa [h4] at h3

end MatrixDiagonalization
end NonsoficGroupsExist
