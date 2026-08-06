import NonsoficGroupsExist.KOne.NilpotentTailKill
import NonsoficGroupsExist.Leavitt.WhiteheadFlip
import NonsoficGroupsExist.Leavitt.LeavittBalancedUnits

/-!
# The γ-elimination chain

Given a normal-form unit `1 + s₁(zneg + z₀)` whose γ-invariant
`1 + znegs₁` is invertible with balanced inverse, two Whitehead flips
and one balanced factorization reduce the class to a pure tail
`1 + s₁(g⁻¹z₀)`; if that tail is nilpotent the nilpotent-tail kill
finishes.  The two side conditions — γ-invertibility (lemma (G)) and
nilpotency of the pure tail — are explicit hypotheses here, to be
discharged separately.
-/

namespace NonsoficGroupsExist
namespace LeavittFamily

open MatrixDiagonalization

variable {A : Type*} [Ring A] (L : LeavittFamily A)
variable {k : Type*} [Field k] [Algebra k A]

/-- **γ-elimination**: if the γ-invariant of a normal-form unit is
invertible with balanced inverse, and the resulting pure tail is
nilpotent, the unit lies in the diagonal class group. -/
theorem gamma_reduction [Nontrivial A]
    (hdiv : ∀ x : A, x ≠ 0 → ∃ p q : A, p * x * q = 1) {zneg z₀ : A}
    (hzm : zneg ∈ Submodule.span k (L.degreeMonomials (-1) (-1)))
    (hz₀ : z₀ ∈ Submodule.span k (L.degreeMonomials 0 0))
    (g : Aˣ) (hgv : (g : A) = 1 + zneg * L.s 1)
    (hginv : ((g⁻¹ : Aˣ) : A) ∈
      Submodule.span k (L.degreeMonomials 0 0))
    (D : ℕ)
    (hnil : (L.s 1 * (((g⁻¹ : Aˣ) : A) * z₀)) ^ D = 0)
    (u : Aˣ) (hu : (u : A) = 1 + L.s 1 * (zneg + z₀)) :
    u ∈ stableUnits A := by
  -- flip 1: [u] = [1 + (zneg + z₀)s₁]
  set v : Aˣ := flipUnit (L.s 1) (zneg + z₀) u hu with hv
  have hflip1 : u * v⁻¹ ∈ stableUnits A :=
    mul_flipUnit_inv_mem_stableUnits (L.s 1) (zneg + z₀) u hu
  have hvval : (v : A) = 1 + zneg * L.s 1 + z₀ * L.s 1 := by
    rw [hv, flipUnit_val]
    noncomm_ring
  -- factor out γ = g: w := g⁻¹·v has value 1 + (g⁻¹z₀)·s₁
  set Y : A := ((g⁻¹ : Aˣ) : A) * z₀ with hY
  set w : Aˣ := g⁻¹ * v with hw
  have hwval : (w : A) = 1 + Y * L.s 1 := by
    show ((g⁻¹ : Aˣ) : A) * (v : A) = _
    rw [hvval]
    have h1 : ((g⁻¹ : Aˣ) : A) * (1 + zneg * L.s 1) = 1 := by
      rw [← hgv, Units.inv_mul]
    calc ((g⁻¹ : Aˣ) : A) * (1 + zneg * L.s 1 + z₀ * L.s 1)
        = ((g⁻¹ : Aˣ) : A) * (1 + zneg * L.s 1) +
          ((g⁻¹ : Aˣ) : A) * z₀ * L.s 1 := by noncomm_ring
      _ = 1 + Y * L.s 1 := by
          rw [h1, hY]
  -- g is a balanced-valued unit, hence in the diagonal class group
  have hgmem : g ∈ stableUnits A := by
    have hval : (g : A) ∈
        Submodule.span k (L.degreeMonomials 0 0) := by
      rw [hgv]
      refine Submodule.add_mem _ (L.one_mem_window (k := k)) ?_
      have := L.window_mul_mem_span hzm (L.s_one_mem_window (k := k))
      refine L.span_degreeMonomials_mono ?_ ?_ this <;> omega
    obtain ⟨n, hlvl⟩ := L.span_degree_zero_le_levelSpan hval
    exact L.mem_stableUnits_of_val_mem_levelSpan hdiv n g hlvl
  -- flip 2: [w] = [1 + s₁·Y]
  set w2 : Aˣ := flipUnit Y (L.s 1) w hwval with hw2
  have hflip2 : w * w2⁻¹ ∈ stableUnits A :=
    mul_flipUnit_inv_mem_stableUnits Y (L.s 1) w hwval
  have hw2val : (w2 : A) = 1 + L.s 1 * Y := by
    rw [hw2, flipUnit_val]
  -- the pure tail dies
  have hYwin : Y ∈ Submodule.span k (L.degreeMonomials 0 0) := by
    have := L.window_mul_mem_span hginv hz₀
    refine L.span_degreeMonomials_mono ?_ ?_ this <;> omega
  have hw2mem : w2 ∈ stableUnits A :=
    L.nilpotent_tail_mem_stableUnits D hYwin hnil w2 hw2val
  -- assemble: u = (u·v⁻¹)·g·(w·w2⁻¹)·w2
  have hassemble : u = (u * v⁻¹) * (g * ((w * w2⁻¹) * w2)) := by
    have hgw : g * w = v := by
      rw [hw]
      group
    calc u = (u * v⁻¹) * v := by group
      _ = (u * v⁻¹) * (g * w) := by rw [hgw]
      _ = (u * v⁻¹) * (g * ((w * w2⁻¹) * w2)) := by group
  rw [hassemble]
  exact mul_mem hflip1 (mul_mem hgmem (mul_mem hflip2 hw2mem))

end LeavittFamily
end NonsoficGroupsExist
