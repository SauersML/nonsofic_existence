import NonsoficGroupsExist.LeavittGradingSpans
import NonsoficGroupsExist.WhiteheadFlip

/-!
# The residual normal form `1 + s₁·z`

Two transport steps for the residual-class loop.  First, for a unit
of value `1 + s₁z` the free unipotent family `1 + s₁Xt₀` replaces `z`
by any representative modulo the right ideal `L·t₀`; in particular by
`(z·s₁)·t₁`.  Second, the corner identity `1 + s₁βt₁ = κ₁(1+β)`
transports the class to `1 + β`: the corner inverse `t₁u⁻¹s₁` makes
`1 + β` a unit, and the corner-insertion coset identity applies.
-/

namespace NonsoficGroupsExist
namespace LeavittFamily

open MatrixDiagonalization

variable {A : Type*} [Ring A] (L : LeavittFamily A)

/-- **Prefix kill**: a unit of value `1 + s₁z` is congruent modulo the
diagonal class group to one of value `1 + s₁(zs₁)t₁`. -/
theorem exists_prefix_kill (z : A) (u : Aˣ)
    (hu : (u : A) = 1 + L.s 1 * z) :
    ∃ u' : Aˣ, u' * u⁻¹ ∈ stableUnits A ∧
      (u' : A) = 1 + L.s 1 * (z * L.s 1 * L.t 1) := by
  have ht0s1 : L.t 0 * L.s 1 = 0 := by rw [t_mul_s]; simp
  set X : A := -(z * L.s 0) with hX
  have hmove : ∀ w : Aˣ, (w : A) = 1 + (L.s 1 * X) * L.t 0 →
      w ∈ stableUnits A := fun w h ↦
    mem_stableUnits_of_val_unipotent (L.s 1 * X) (L.t 0)
      (by rw [← mul_assoc, ht0s1, zero_mul]) h
  have hz : L.s 1 * X * L.t 0 * (L.s 1 * X * L.t 0) = 0 := by
    rw [show L.s 1 * X * L.t 0 * (L.s 1 * X * L.t 0) =
      L.s 1 * X * (L.t 0 * L.s 1) * (X * L.t 0) from by noncomm_ring,
      ht0s1]
    noncomm_ring
  set E : Aˣ := ⟨1 + L.s 1 * X * L.t 0, 1 - L.s 1 * X * L.t 0,
    by
      calc (1 + L.s 1 * X * L.t 0) * (1 - L.s 1 * X * L.t 0)
          = 1 - L.s 1 * X * L.t 0 * (L.s 1 * X * L.t 0) := by
            noncomm_ring
        _ = 1 := by rw [hz, sub_zero],
    by
      calc (1 - L.s 1 * X * L.t 0) * (1 + L.s 1 * X * L.t 0)
          = 1 - L.s 1 * X * L.t 0 * (L.s 1 * X * L.t 0) := by
            noncomm_ring
        _ = 1 := by rw [hz, sub_zero]⟩ with hE
  refine ⟨E * u, ?_, ?_⟩
  · have hEmem : E ∈ stableUnits A := hmove E (by
      show (1 : A) + L.s 1 * X * L.t 0 = 1 + L.s 1 * X * L.t 0
      rw [mul_assoc])
    have : E * u * u⁻¹ = E := by group
    rwa [this]
  · show (E : A) * (u : A) = 1 + L.s 1 * (z * L.s 1 * L.t 1)
    rw [hu]
    show (1 + L.s 1 * X * L.t 0) * (1 + L.s 1 * z) = _
    have hexp : (1 + L.s 1 * X * L.t 0) * (1 + L.s 1 * z) =
        1 + L.s 1 * z + L.s 1 * X * L.t 0 +
          L.s 1 * X * (L.t 0 * L.s 1) * z := by
      noncomm_ring
    rw [hexp, ht0s1]
    have hsplit : z = z * L.s 0 * L.t 0 + z * L.s 1 * L.t 1 := by
      have h1 := L.sum_s_mul_t
      calc z = z * 1 := by rw [mul_one]
        _ = z * (L.s 0 * L.t 0 + L.s 1 * L.t 1) := by rw [h1]
        _ = z * L.s 0 * L.t 0 + z * L.s 1 * L.t 1 := by noncomm_ring
    rw [hX]
    calc 1 + L.s 1 * z + L.s 1 * -(z * L.s 0) * L.t 0 +
          L.s 1 * -(z * L.s 0) * 0 * z
        = 1 + L.s 1 * (z - z * L.s 0 * L.t 0) := by noncomm_ring
      _ = 1 + L.s 1 * (z * L.s 1 * L.t 1) := by
          congr 2
          calc z - z * L.s 0 * L.t 0
              = (z * L.s 0 * L.t 0 + z * L.s 1 * L.t 1) -
                z * L.s 0 * L.t 0 := by rw [← hsplit]
            _ = z * L.s 1 * L.t 1 := by abel

/-- **Corner transport**: if `1 + s₁βt₁` is a unit, then `1 + β` is a
unit and the two are congruent modulo the diagonal class group. -/
theorem exists_corner_transport [Nontrivial A]
    (hdiv : ∀ x : A, x ≠ 0 → ∃ p q : A, p * x * q = 1)
    (β : A) (u : Aˣ) (hu : (u : A) = 1 + L.s 1 * β * L.t 1) :
    ∃ w : Aˣ, (w : A) = 1 + β ∧ u * w⁻¹ ∈ stableUnits A := by
  have ht1s1 : L.t 1 * L.s 1 = 1 := by rw [t_mul_s]; simp
  -- the corner inverse
  set x : A := L.t 1 * ((u⁻¹ : Aˣ) : A) * L.s 1 with hx
  have hright : (1 + β) * x = 1 := by
    have h1 : ((u⁻¹ : Aˣ) : A) = 1 - L.s 1 * β * L.t 1 *
        ((u⁻¹ : Aˣ) : A) := by
      have h2 : (u : A) * ((u⁻¹ : Aˣ) : A) = 1 := Units.mul_inv u
      rw [hu] at h2
      calc ((u⁻¹ : Aˣ) : A)
          = (1 + L.s 1 * β * L.t 1) * ((u⁻¹ : Aˣ) : A) -
            L.s 1 * β * L.t 1 * ((u⁻¹ : Aˣ) : A) := by noncomm_ring
        _ = 1 - L.s 1 * β * L.t 1 * ((u⁻¹ : Aˣ) : A) := by rw [h2]
    have h3 : x = 1 - β * x := by
      calc x = L.t 1 * ((u⁻¹ : Aˣ) : A) * L.s 1 := hx
        _ = L.t 1 * (1 - L.s 1 * β * L.t 1 * ((u⁻¹ : Aˣ) : A)) *
            L.s 1 := by rw [← h1]
        _ = L.t 1 * L.s 1 - (L.t 1 * L.s 1) * β *
            (L.t 1 * ((u⁻¹ : Aˣ) : A) * L.s 1) := by noncomm_ring
        _ = 1 - β * x := by rw [ht1s1, hx]; noncomm_ring
    calc (1 + β) * x = x + β * x := by noncomm_ring
      _ = (1 - β * x) + β * x := by rw [← h3]
      _ = 1 := by abel
  have hleft : x * (1 + β) = 1 := by
    have h1 : ((u⁻¹ : Aˣ) : A) = 1 - ((u⁻¹ : Aˣ) : A) *
        (L.s 1 * β * L.t 1) := by
      have h2 : ((u⁻¹ : Aˣ) : A) * (u : A) = 1 := Units.inv_mul u
      rw [hu] at h2
      calc ((u⁻¹ : Aˣ) : A)
          = ((u⁻¹ : Aˣ) : A) * (1 + L.s 1 * β * L.t 1) -
            ((u⁻¹ : Aˣ) : A) * (L.s 1 * β * L.t 1) := by noncomm_ring
        _ = 1 - ((u⁻¹ : Aˣ) : A) * (L.s 1 * β * L.t 1) := by rw [h2]
    have h3 : x = 1 - x * β := by
      calc x = L.t 1 * ((u⁻¹ : Aˣ) : A) * L.s 1 := hx
        _ = L.t 1 * (1 - ((u⁻¹ : Aˣ) : A) * (L.s 1 * β * L.t 1)) *
            L.s 1 := by rw [← h1]
        _ = L.t 1 * L.s 1 - (L.t 1 * ((u⁻¹ : Aˣ) : A) * L.s 1) * β *
            (L.t 1 * L.s 1) := by noncomm_ring
        _ = 1 - x * β := by rw [ht1s1, hx]; noncomm_ring
    calc x * (1 + β) = x + x * β := by noncomm_ring
      _ = (1 - x * β) + x * β := by rw [← h3]
      _ = 1 := by abel
  set w : Aˣ := ⟨1 + β, x, hright.symm ▸ hright, hleft⟩ with hw
  refine ⟨w, rfl, ?_⟩
  have hval : u = pairKappaUnit (L.s 1) (L.t 1) ht1s1 w := by
    apply Units.ext
    rw [pairKappaUnit_val, hu]
    show 1 + L.s 1 * β * L.t 1 =
      L.s 1 * (1 + β) * L.t 1 + (1 - L.s 1 * L.t 1)
    noncomm_ring
  rw [hval]
  exact pairKappaUnit_mul_inv_mem_stableUnits (L.s 1) (L.t 1) ht1s1
    hdiv w

end LeavittFamily
end NonsoficGroupsExist
