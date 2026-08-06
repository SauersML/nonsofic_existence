import NonsoficGroupsExist.ResidualNormalForm
import NonsoficGroupsExist.LeavittBalancedUnits

/-!
# The move calculus on canonical residuals

A canonical residual is a unit of value `c + s₁w` with `c, w`
balanced.  Three families of class-preserving moves act on the data
`(c, w)`:

* right multiplication by a balanced unit `h`: `(c, w) ↦ (ch, wh)`;
* left multiplication by a block-diagonal balanced unit
  `g = s₀g₀t₀ + s₁g₁t₁`: `(c, w) ↦ (gc, g₁w)`;
* the kill family `1 + s₁(As₀)t₀`: `(c, w) ↦ (c, w + A·(p₀c))`.

Each mover lies in the diagonal class group, so the class of the
residual is unchanged.
-/

namespace NonsoficGroupsExist
namespace LeavittFamily

open MatrixDiagonalization

variable {A : Type*} [Ring A] (L : LeavittFamily A)

/-- Block-diagonal balanced units `s₀g₀t₀ + s₁g₁t₁` from a pair of
units of the base ring. -/
def blockDiagUnit (g₀ g₁ : Aˣ) : Aˣ where
  val := L.s 0 * (g₀ : A) * L.t 0 + L.s 1 * (g₁ : A) * L.t 1
  inv := L.s 0 * ((g₀⁻¹ : Aˣ) : A) * L.t 0 +
    L.s 1 * ((g₁⁻¹ : Aˣ) : A) * L.t 1
  val_inv := by
    have h00 : L.t 0 * L.s 0 = 1 := by rw [t_mul_s]; simp
    have h11 : L.t 1 * L.s 1 = 1 := by rw [t_mul_s]; simp
    have h01 : L.t 0 * L.s 1 = 0 := by rw [t_mul_s]; simp
    have h10 : L.t 1 * L.s 0 = 0 := by rw [t_mul_s]; simp
    have e1 : L.s 0 * (g₀ : A) * L.t 0 *
        (L.s 0 * ((g₀⁻¹ : Aˣ) : A) * L.t 0) =
        L.s 0 * L.t 0 := by
      rw [show L.s 0 * (g₀ : A) * L.t 0 *
        (L.s 0 * ((g₀⁻¹ : Aˣ) : A) * L.t 0) =
        L.s 0 * ((g₀ : A) * (L.t 0 * L.s 0) * ((g₀⁻¹ : Aˣ) : A)) *
          L.t 0 from by noncomm_ring, h00, mul_one, Units.mul_inv]
      noncomm_ring
    have e2 : L.s 0 * (g₀ : A) * L.t 0 *
        (L.s 1 * ((g₁⁻¹ : Aˣ) : A) * L.t 1) = 0 := by
      rw [show L.s 0 * (g₀ : A) * L.t 0 *
        (L.s 1 * ((g₁⁻¹ : Aˣ) : A) * L.t 1) =
        L.s 0 * (g₀ : A) * (L.t 0 * L.s 1) *
          (((g₁⁻¹ : Aˣ) : A) * L.t 1) from by noncomm_ring, h01]
      noncomm_ring
    have e3 : L.s 1 * (g₁ : A) * L.t 1 *
        (L.s 0 * ((g₀⁻¹ : Aˣ) : A) * L.t 0) = 0 := by
      rw [show L.s 1 * (g₁ : A) * L.t 1 *
        (L.s 0 * ((g₀⁻¹ : Aˣ) : A) * L.t 0) =
        L.s 1 * (g₁ : A) * (L.t 1 * L.s 0) *
          (((g₀⁻¹ : Aˣ) : A) * L.t 0) from by noncomm_ring, h10]
      noncomm_ring
    have e4 : L.s 1 * (g₁ : A) * L.t 1 *
        (L.s 1 * ((g₁⁻¹ : Aˣ) : A) * L.t 1) =
        L.s 1 * L.t 1 := by
      rw [show L.s 1 * (g₁ : A) * L.t 1 *
        (L.s 1 * ((g₁⁻¹ : Aˣ) : A) * L.t 1) =
        L.s 1 * ((g₁ : A) * (L.t 1 * L.s 1) * ((g₁⁻¹ : Aˣ) : A)) *
          L.t 1 from by noncomm_ring, h11, mul_one, Units.mul_inv]
      noncomm_ring
    calc (L.s 0 * (g₀ : A) * L.t 0 + L.s 1 * (g₁ : A) * L.t 1) *
          (L.s 0 * ((g₀⁻¹ : Aˣ) : A) * L.t 0 +
            L.s 1 * ((g₁⁻¹ : Aˣ) : A) * L.t 1)
        = L.s 0 * (g₀ : A) * L.t 0 *
            (L.s 0 * ((g₀⁻¹ : Aˣ) : A) * L.t 0) +
          L.s 0 * (g₀ : A) * L.t 0 *
            (L.s 1 * ((g₁⁻¹ : Aˣ) : A) * L.t 1) +
          (L.s 1 * (g₁ : A) * L.t 1 *
            (L.s 0 * ((g₀⁻¹ : Aˣ) : A) * L.t 0) +
          L.s 1 * (g₁ : A) * L.t 1 *
            (L.s 1 * ((g₁⁻¹ : Aˣ) : A) * L.t 1)) := by noncomm_ring
      _ = L.s 0 * L.t 0 + 0 + (0 + L.s 1 * L.t 1) := by
          rw [e1, e2, e3, e4]
      _ = 1 := by rw [← L.sum_s_mul_t]; abel
  inv_val := by
    have h00 : L.t 0 * L.s 0 = 1 := by rw [t_mul_s]; simp
    have h11 : L.t 1 * L.s 1 = 1 := by rw [t_mul_s]; simp
    have h01 : L.t 0 * L.s 1 = 0 := by rw [t_mul_s]; simp
    have h10 : L.t 1 * L.s 0 = 0 := by rw [t_mul_s]; simp
    have e1 : L.s 0 * ((g₀⁻¹ : Aˣ) : A) * L.t 0 *
        (L.s 0 * (g₀ : A) * L.t 0) = L.s 0 * L.t 0 := by
      rw [show L.s 0 * ((g₀⁻¹ : Aˣ) : A) * L.t 0 *
        (L.s 0 * (g₀ : A) * L.t 0) =
        L.s 0 * (((g₀⁻¹ : Aˣ) : A) * (L.t 0 * L.s 0) * (g₀ : A)) *
          L.t 0 from by noncomm_ring, h00, mul_one, Units.inv_mul]
      noncomm_ring
    have e2 : L.s 0 * ((g₀⁻¹ : Aˣ) : A) * L.t 0 *
        (L.s 1 * (g₁ : A) * L.t 1) = 0 := by
      rw [show L.s 0 * ((g₀⁻¹ : Aˣ) : A) * L.t 0 *
        (L.s 1 * (g₁ : A) * L.t 1) =
        L.s 0 * ((g₀⁻¹ : Aˣ) : A) * (L.t 0 * L.s 1) *
          ((g₁ : A) * L.t 1) from by noncomm_ring, h01]
      noncomm_ring
    have e3 : L.s 1 * ((g₁⁻¹ : Aˣ) : A) * L.t 1 *
        (L.s 0 * (g₀ : A) * L.t 0) = 0 := by
      rw [show L.s 1 * ((g₁⁻¹ : Aˣ) : A) * L.t 1 *
        (L.s 0 * (g₀ : A) * L.t 0) =
        L.s 1 * ((g₁⁻¹ : Aˣ) : A) * (L.t 1 * L.s 0) *
          ((g₀ : A) * L.t 0) from by noncomm_ring, h10]
      noncomm_ring
    have e4 : L.s 1 * ((g₁⁻¹ : Aˣ) : A) * L.t 1 *
        (L.s 1 * (g₁ : A) * L.t 1) = L.s 1 * L.t 1 := by
      rw [show L.s 1 * ((g₁⁻¹ : Aˣ) : A) * L.t 1 *
        (L.s 1 * (g₁ : A) * L.t 1) =
        L.s 1 * (((g₁⁻¹ : Aˣ) : A) * (L.t 1 * L.s 1) * (g₁ : A)) *
          L.t 1 from by noncomm_ring, h11, mul_one, Units.inv_mul]
      noncomm_ring
    calc (L.s 0 * ((g₀⁻¹ : Aˣ) : A) * L.t 0 +
          L.s 1 * ((g₁⁻¹ : Aˣ) : A) * L.t 1) *
          (L.s 0 * (g₀ : A) * L.t 0 + L.s 1 * (g₁ : A) * L.t 1)
        = L.s 0 * ((g₀⁻¹ : Aˣ) : A) * L.t 0 *
            (L.s 0 * (g₀ : A) * L.t 0) +
          L.s 0 * ((g₀⁻¹ : Aˣ) : A) * L.t 0 *
            (L.s 1 * (g₁ : A) * L.t 1) +
          (L.s 1 * ((g₁⁻¹ : Aˣ) : A) * L.t 1 *
            (L.s 0 * (g₀ : A) * L.t 0) +
          L.s 1 * ((g₁⁻¹ : Aˣ) : A) * L.t 1 *
            (L.s 1 * (g₁ : A) * L.t 1)) := by noncomm_ring
      _ = L.s 0 * L.t 0 + 0 + (0 + L.s 1 * L.t 1) := by
          rw [e1, e2, e3, e4]
      _ = 1 := by rw [← L.sum_s_mul_t]; abel

/-- The left block-diagonal move: `g·(c + s₁w) = gc + s₁(g₁w)`. -/
theorem blockDiagUnit_mul_residual (g₀ g₁ : Aˣ) (c w : A) :
    ((L.blockDiagUnit g₀ g₁ : Aˣ) : A) * (c + L.s 1 * w) =
      ((L.blockDiagUnit g₀ g₁ : Aˣ) : A) * c +
        L.s 1 * ((g₁ : A) * w) := by
  have h01 : L.t 0 * L.s 1 = 0 := by rw [t_mul_s]; simp
  have h11 : L.t 1 * L.s 1 = 1 := by rw [t_mul_s]; simp
  show (L.s 0 * (g₀ : A) * L.t 0 + L.s 1 * (g₁ : A) * L.t 1) *
    (c + L.s 1 * w) = _
  have e1 : (L.s 0 * (g₀ : A) * L.t 0 + L.s 1 * (g₁ : A) * L.t 1) *
      (L.s 1 * w) = L.s 1 * ((g₁ : A) * w) := by
    calc (L.s 0 * (g₀ : A) * L.t 0 + L.s 1 * (g₁ : A) * L.t 1) *
          (L.s 1 * w)
        = L.s 0 * (g₀ : A) * (L.t 0 * L.s 1) * w +
          L.s 1 * (g₁ : A) * (L.t 1 * L.s 1) * w := by noncomm_ring
      _ = L.s 1 * ((g₁ : A) * w) := by
          rw [h01, h11]
          noncomm_ring
  calc (L.s 0 * (g₀ : A) * L.t 0 + L.s 1 * (g₁ : A) * L.t 1) *
        (c + L.s 1 * w)
      = (L.s 0 * (g₀ : A) * L.t 0 + L.s 1 * (g₁ : A) * L.t 1) * c +
        (L.s 0 * (g₀ : A) * L.t 0 + L.s 1 * (g₁ : A) * L.t 1) *
          (L.s 1 * w) := by noncomm_ring
    _ = _ := by rw [e1]

/-- The kill move: `(1 + s₁(As₀)t₀)·(c + s₁w) = c + s₁(w + A·(s₀t₀c))`
— it changes `w` by `A·p₀·c` and lies in the diagonal class group. -/
theorem kill_move_residual (a c w : A) :
    (1 + L.s 1 * (a * L.s 0) * L.t 0) * (c + L.s 1 * w) =
      c + L.s 1 * (w + a * (L.s 0 * L.t 0 * c)) := by
  have h01 : L.t 0 * L.s 1 = 0 := by rw [t_mul_s]; simp
  calc (1 + L.s 1 * (a * L.s 0) * L.t 0) * (c + L.s 1 * w)
      = c + L.s 1 * w + L.s 1 * (a * L.s 0) * (L.t 0 * L.s 1) * w +
        L.s 1 * (a * (L.s 0 * L.t 0 * c)) := by noncomm_ring
    _ = c + L.s 1 * (w + a * (L.s 0 * L.t 0 * c)) := by
        rw [h01]
        noncomm_ring

/-- The kill mover lies in the diagonal class group. -/
theorem kill_mover_mem (a : A) (u : Aˣ)
    (hu : (u : A) = 1 + L.s 1 * (a * L.s 0) * L.t 0) :
    u ∈ stableUnits A := by
  have h01 : L.t 0 * L.s 1 = 0 := by rw [t_mul_s]; simp
  refine mem_stableUnits_of_val_unipotent (L.s 1 * (a * L.s 0))
    (L.t 0) ?_ (by rw [hu, mul_assoc])
  rw [← mul_assoc, h01, zero_mul]

end LeavittFamily
end NonsoficGroupsExist
