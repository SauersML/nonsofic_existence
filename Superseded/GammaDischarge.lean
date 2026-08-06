import NonsoficGroupsExist.ZeroKOne
import NonsoficGroupsExist.PureTailNilpotency
import NonsoficGroupsExist.RankNormalForm
import Superseded.GammaReduction
import NonsoficGroupsExist.LeavittSimplicity

/-!
# The γ-hypotheses discharge: normal-form units lie in the class group

The γ-elimination chain (`GammaReduction`) reduced normal-form units
`1 + s₁(z₋ + z₀)` to three side conditions.  All three are now
theorems: the γ-invariant `1 + s₁z₋` is the balanced part of the
`[0,1]`-window value of the unit itself, hence invertible by the
keystone (`ZeroKOne`); its flip partner has balanced inverse by the
rank normal form; and the residual pure tail is nilpotent by
`PureTailNilpotency` applied to the double flip.  Conclusion: every
unit of the binary Leavitt algebra with value `1 + s₁·(degree
`[-1,0]` window)` lies in the diagonal class group.
-/

namespace NonsoficGroupsExist
namespace BinaryLeavitt

open LeavittFamily MatrixDiagonalization

variable (k : Type) [Field k]

/-- **Normal-form units lie in the diagonal class group.** -/
theorem sOneTail_mem_stableUnits [Nontrivial (BinaryLeavittAlgebra k)]
    {zneg z₀ : BinaryLeavittAlgebra k}
    (hzm : zneg ∈
      Submodule.span k ((family k).degreeMonomials (-1) (-1)))
    (hz₀ : z₀ ∈ Submodule.span k ((family k).degreeMonomials 0 0))
    (u : (BinaryLeavittAlgebra k)ˣ)
    (hu : (u : BinaryLeavittAlgebra k) =
      1 + (family k).s 1 * (zneg + z₀)) :
    u ∈ stableUnits (BinaryLeavittAlgebra k) := by
  classical
  set L : LeavittFamily (BinaryLeavittAlgebra k) := family k with hL
  have hdiv : ∀ x : BinaryLeavittAlgebra k, x ≠ 0 →
      ∃ p q : BinaryLeavittAlgebra k, p * x * q = 1 :=
    fun x hx ↦ exists_mul_mul_eq_one k hx
  -- the keystone: the γ-invariant is invertible
  have hs1w : L.s 1 ∈ Submodule.span k (L.degreeMonomials 1 1) :=
    L.s_one_mem_window (k := k)
  have hcw : (1 : BinaryLeavittAlgebra k) + L.s 1 * zneg ∈
      Submodule.span k (L.degreeMonomials 0 0) := by
    refine Submodule.add_mem _ (L.one_mem_window (k := k)) ?_
    have h1 := L.window_mul_mem_span (k := k) hs1w hzm
    refine L.span_degreeMonomials_mono ?_ ?_ h1 <;> omega
  have hζw : L.s 1 * z₀ ∈
      Submodule.span k (L.degreeMonomials 1 1) := by
    have h1 := L.window_mul_mem_span (k := k) hs1w hz₀
    refine L.span_degreeMonomials_mono ?_ ?_ h1 <;> omega
  have hval' : (u : BinaryLeavittAlgebra k) =
      (1 + L.s 1 * zneg) + L.s 1 * z₀ := by
    rw [hu]
    noncomm_ring
  have hγ' : IsUnit (1 + L.s 1 * zneg) :=
    balanced_component_isUnit k hcw hζw u hval'
  obtain ⟨γ', hγ'val⟩ := hγ'
  -- flip to the γ-partner with value `1 + z₋·s₁`
  set g : (BinaryLeavittAlgebra k)ˣ :=
    flipUnit (L.s 1) zneg γ' hγ'val with hg
  have hgval : (g : BinaryLeavittAlgebra k) = 1 + zneg * L.s 1 := by
    rw [hg, flipUnit_val]
  -- balanced inverse of the γ-partner
  have hgw : (g : BinaryLeavittAlgebra k) ∈
      Submodule.span k (L.degreeMonomials 0 0) := by
    rw [hgval]
    refine Submodule.add_mem _ (L.one_mem_window (k := k)) ?_
    have h1 := L.window_mul_mem_span (k := k) hzm hs1w
    refine L.span_degreeMonomials_mono ?_ ?_ h1 <;> omega
  obtain ⟨q, hgq⟩ := L.span_degree_zero_le_levelSpan hgw
  have hginvq : ((g⁻¹ : (BinaryLeavittAlgebra k)ˣ) :
      BinaryLeavittAlgebra k) ∈
      Submodule.span k (L.levelMonomials q) :=
    L.inv_mem_levelSpan_of_val_mem g hgq
  have hginv : ((g⁻¹ : (BinaryLeavittAlgebra k)ˣ) :
      BinaryLeavittAlgebra k) ∈
      Submodule.span k (L.degreeMonomials 0 0) :=
    L.span_levelMonomials_le_degree q hginvq
  -- expose the residual pure tail through the double flip
  set v : (BinaryLeavittAlgebra k)ˣ :=
    flipUnit (L.s 1) (zneg + z₀) u hu with hv
  have hvval : (v : BinaryLeavittAlgebra k) =
      1 + zneg * L.s 1 + z₀ * L.s 1 := by
    rw [hv, flipUnit_val]
    noncomm_ring
  set Y : BinaryLeavittAlgebra k :=
    ((g⁻¹ : (BinaryLeavittAlgebra k)ˣ) : BinaryLeavittAlgebra k) * z₀
    with hY
  set w : (BinaryLeavittAlgebra k)ˣ := g⁻¹ * v with hw
  have hwval : (w : BinaryLeavittAlgebra k) = 1 + Y * L.s 1 := by
    show ((g⁻¹ : (BinaryLeavittAlgebra k)ˣ) : BinaryLeavittAlgebra k) *
      (v : BinaryLeavittAlgebra k) = 1 + Y * L.s 1
    rw [hvval]
    have h1 : ((g⁻¹ : (BinaryLeavittAlgebra k)ˣ) :
        BinaryLeavittAlgebra k) * (1 + zneg * L.s 1) = 1 := by
      rw [← hgval, Units.inv_mul]
    calc ((g⁻¹ : (BinaryLeavittAlgebra k)ˣ) : BinaryLeavittAlgebra k) *
          (1 + zneg * L.s 1 + z₀ * L.s 1)
        = ((g⁻¹ : (BinaryLeavittAlgebra k)ˣ) :
            BinaryLeavittAlgebra k) * (1 + zneg * L.s 1) +
          ((g⁻¹ : (BinaryLeavittAlgebra k)ˣ) :
            BinaryLeavittAlgebra k) * z₀ * L.s 1 := by noncomm_ring
      _ = 1 + Y * L.s 1 := by rw [h1, hY]
  set w2 : (BinaryLeavittAlgebra k)ˣ :=
    flipUnit Y (L.s 1) w hwval with hw2
  have hw2val : (w2 : BinaryLeavittAlgebra k) = 1 + L.s 1 * Y := by
    rw [hw2, flipUnit_val]
  have hYw : L.s 1 * Y ∈
      Submodule.span k (L.degreeMonomials 1 1) := by
    have h0 : Y ∈ Submodule.span k (L.degreeMonomials 0 0) := by
      rw [hY]
      have h1 := L.window_mul_mem_span (k := k) hginv hz₀
      refine L.span_degreeMonomials_mono ?_ ?_ h1 <;> omega
    have h1 := L.window_mul_mem_span (k := k) hs1w h0
    refine L.span_degreeMonomials_mono ?_ ?_ h1 <;> omega
  obtain ⟨D, hD⟩ := pure_tail_nilpotent k hYw w2 hw2val
  -- discharge the γ-elimination chain
  exact L.gamma_reduction hdiv hzm hz₀ g hgval hginv D
    (by rw [← hY]; exact hD) u hu

end BinaryLeavitt
end NonsoficGroupsExist
