import NonsoficGroupsExist.KOne.ZeroKOne
import NonsoficGroupsExist.KOne.PureTailNilpotency
import NonsoficGroupsExist.Leavitt.RankNormalForm
import NonsoficGroupsExist.Leavitt.LeavittSimplicity
import NonsoficGroupsExist.KOne.ResidualNormalForm

/-!
# Every `[0,1]`-window unit lies in the diagonal class group

The assembly of the keystone: a unit valued in the span of degrees
`{0, 1}` has invertible balanced part (`ZeroKOne`), the balanced part
is a balanced-valued unit with balanced inverse (`RankNormalForm`),
the residual tail `1 + η` has nilpotent `η` (`PureTailNilpotency`),
the `κ₁`-corner transport turns it into `1 + s₁·(η t₁)` with balanced
`η t₁` and transported nilpotency, and the nilpotent-tail kill
finishes.  Simplicity supplies the division hypothesis.
-/

namespace NonsoficGroupsExist
namespace BinaryLeavitt

open LeavittFamily MatrixDiagonalization

variable (k : Type) [Field k]

/-- **Width-two reduction**: every unit of the binary Leavitt algebra
whose value lies in the `[0,1]` degree window belongs to the diagonal
class group. -/
theorem window_zero_one_mem_stableUnits
    [Nontrivial (BinaryLeavittAlgebra k)]
    (u : (BinaryLeavittAlgebra k)ˣ)
    (hu : (u : BinaryLeavittAlgebra k) ∈
      Submodule.span k ((family k).degreeMonomials 0 1)) :
    u ∈ stableUnits (BinaryLeavittAlgebra k) := by
  classical
  set L : LeavittFamily (BinaryLeavittAlgebra k) := family k with hL
  have hdiv : ∀ x : BinaryLeavittAlgebra k, x ≠ 0 →
      ∃ p q : BinaryLeavittAlgebra k, p * x * q = 1 :=
    fun x hx ↦ exists_mul_mul_eq_one k hx
  -- split into the balanced part and the degree-one tail
  obtain ⟨y, hymem, hysupp, hysum⟩ := exists_components k hu
  have hIcc : Finset.Icc (0 : ℤ) 1 = {0, 1} := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hval : (u : BinaryLeavittAlgebra k) = y 0 + y 1 := by
    rw [hysum, hIcc, Finset.sum_insert (by simp), Finset.sum_singleton]
  -- the balanced part is invertible
  have hcu : IsUnit (y 0) :=
    balanced_component_isUnit k (hymem 0) (hymem 1) u hval
  obtain ⟨uc, hucv⟩ := hcu
  obtain ⟨q, hcq⟩ := L.span_degree_zero_le_levelSpan (hymem 0)
  have hucval : (uc : BinaryLeavittAlgebra k) ∈
      Submodule.span k (L.levelMonomials q) := by
    rw [hucv]
    exact hcq
  have hucmem : uc ∈ stableUnits (BinaryLeavittAlgebra k) :=
    L.mem_stableUnits_of_val_mem_levelSpan hdiv q uc hucval
  have hucinv : ((uc⁻¹ : (BinaryLeavittAlgebra k)ˣ) :
      BinaryLeavittAlgebra k) ∈
      Submodule.span k (L.levelMonomials q) :=
    L.inv_mem_levelSpan_of_val_mem uc hucval
  -- the residual tail unit
  set v : (BinaryLeavittAlgebra k)ˣ := uc⁻¹ * u with hv
  set η : BinaryLeavittAlgebra k :=
    ((uc⁻¹ : (BinaryLeavittAlgebra k)ˣ) : BinaryLeavittAlgebra k) * y 1
    with hη
  have hvval : (v : BinaryLeavittAlgebra k) = 1 + η := by
    rw [hv]
    show ((uc⁻¹ : (BinaryLeavittAlgebra k)ˣ) : BinaryLeavittAlgebra k) *
      (u : BinaryLeavittAlgebra k) = 1 + η
    rw [hval, mul_add, hη]
    congr 1
    rw [show y 0 = (uc : BinaryLeavittAlgebra k) from hucv.symm,
      Units.inv_mul]
  have hηd : η ∈ Submodule.span k (L.degreeMonomials 1 1) := by
    rw [hη]
    have h1 := L.window_mul_mem_span (k := k)
      (L.span_levelMonomials_le_degree q hucinv) (hymem 1)
    refine L.span_degreeMonomials_mono ?_ ?_ h1 <;> omega
  obtain ⟨D, hD⟩ := pure_tail_nilpotent k hηd v hvval
  -- corner transport into the `s₁·balanced·t₁` normal form
  have ht1s1 : L.t 1 * L.s 1 = 1 := by
    rw [t_mul_s]
    simp
  set κ : (BinaryLeavittAlgebra k)ˣ :=
    pairKappaUnit (L.s 1) (L.t 1) ht1s1 v with hκ
  have hκval : (κ : BinaryLeavittAlgebra k) =
      1 + L.s 1 * (η * L.t 1) := by
    rw [hκ]
    show L.s 1 * (v : BinaryLeavittAlgebra k) * L.t 1 +
      (1 - L.s 1 * L.t 1) = 1 + L.s 1 * (η * L.t 1)
    rw [hvval]
    noncomm_ring
  have hzt : η * L.t 1 ∈
      Submodule.span k (L.degreeMonomials 0 0) := by
    have h1 := L.window_mul_mem_span (k := k) hηd
      (L.t_one_mem_window (k := k))
    refine L.span_degreeMonomials_mono ?_ ?_ h1 <;> omega
  -- transported nilpotency
  have hpow : ∀ m : ℕ,
      (L.s 1 * (η * L.t 1)) ^ (m + 1) = L.s 1 * (η ^ (m + 1) * L.t 1)
      := by
    intro m
    induction m with
    | zero => rw [pow_one, pow_one]
    | succ m ih =>
        rw [pow_succ, ih]
        rw [show L.s 1 * (η ^ (m + 1) * L.t 1) *
            (L.s 1 * (η * L.t 1)) =
          L.s 1 * (η ^ (m + 1) * (L.t 1 * L.s 1) * (η * L.t 1))
          from by noncomm_ring, ht1s1]
        rw [show L.s 1 * (η ^ (m + 1) * 1 * (η * L.t 1)) =
          L.s 1 * (η ^ (m + 1) * η * L.t 1) from by noncomm_ring,
          ← pow_succ]
  have hnil : (L.s 1 * (η * L.t 1)) ^ (D + 1) = 0 := by
    rw [hpow D, pow_succ, hD, zero_mul, zero_mul, mul_zero]
  have hκmem : κ ∈ stableUnits (BinaryLeavittAlgebra k) :=
    L.nilpotent_tail_mem_stableUnits (D + 1) hzt hnil κ hκval
  -- the transport itself is in the class group
  have hκtrans : κ * v⁻¹ ∈ stableUnits (BinaryLeavittAlgebra k) := by
    rw [hκ]
    exact pairKappaUnit_mul_inv_mem_stableUnits (L.s 1) (L.t 1) ht1s1
      hdiv v
  -- assemble
  have hassemble : u = uc * ((κ * v⁻¹)⁻¹ * κ) := by
    have h1 : (κ * v⁻¹)⁻¹ * κ = v := by group
    rw [h1, hv]
    group
  rw [hassemble]
  exact mul_mem hucmem (mul_mem (inv_mem hκtrans) hκmem)

end BinaryLeavitt
end NonsoficGroupsExist
