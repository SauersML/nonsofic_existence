import NonsoficGroupsExist.ZeroKOne
import NonsoficGroupsExist.PureTailNilpotency
-- `Mathlib.Algebra.GeomSum` was split; `geom_sum_mul` lives in the Ring file.
import Mathlib.Algebra.Ring.GeomSum

/-!
# Structure theorem for nonnegative narrow units

Every unit with value in the `[0,1]` window factors as an invertible
balanced element times a unipotent `1 + η` with `η` nilpotent of pure
degree one: the keystone shows the balanced part is invertible, the
rank normal form gives it a balanced inverse, and the pure-tail
nilpotency bounds the unipotent factor.  Consequently the inverse of
such a unit again has a nonnegative window — the rigorous
upper-triangular leg of the Birkhoff factorization.
-/

namespace NonsoficGroupsExist
namespace BinaryLeavitt

open LeavittFamily

variable (k : Type) [Field k]

/-- **Structure theorem**: a unit with `[0,1]`-window value is an
invertible balanced element times a unipotent with nilpotent pure
degree-one tail. -/
theorem nonneg_narrow_unit_structure
    [Nontrivial (BinaryLeavittAlgebra k)]
    (u : (BinaryLeavittAlgebra k)ˣ)
    (hu : (u : BinaryLeavittAlgebra k) ∈
      Submodule.span k ((family k).degreeMonomials 0 1)) :
    ∃ (c cinv η : BinaryLeavittAlgebra k) (D : ℕ),
      c ∈ Submodule.span k ((family k).degreeMonomials 0 0) ∧
      cinv ∈ Submodule.span k ((family k).degreeMonomials 0 0) ∧
      c * cinv = 1 ∧ cinv * c = 1 ∧
      η ∈ Submodule.span k ((family k).degreeMonomials 1 1) ∧
      η ^ D = 0 ∧
      (u : BinaryLeavittAlgebra k) = c * (1 + η) := by
  classical
  set L : LeavittFamily (BinaryLeavittAlgebra k) := family k with hL
  obtain ⟨y, hymem, -, hysum⟩ := exists_components k hu
  have hval : (u : BinaryLeavittAlgebra k) = y 0 + y 1 := by
    rw [hysum]
    have hIcc : Finset.Icc (0 : ℤ) 1 = {0, 1} := by
      ext d
      simp only [Finset.mem_Icc, Finset.mem_insert,
        Finset.mem_singleton]
      omega
    rw [hIcc, Finset.sum_insert (by simp), Finset.sum_singleton]
  have hcu : IsUnit (y 0) :=
    balanced_component_isUnit k (hymem 0) (hymem 1) u hval
  obtain ⟨cu, hcuval⟩ := hcu
  -- the balanced inverse
  obtain ⟨n, hcn⟩ := L.span_degree_zero_le_levelSpan (hymem 0)
  have hculvl : (cu : BinaryLeavittAlgebra k) ∈
      Submodule.span k (L.levelMonomials n) := by
    rw [hcuval]
    exact hcn
  have hinvw : ((cu⁻¹ : (BinaryLeavittAlgebra k)ˣ) :
      BinaryLeavittAlgebra k) ∈
      Submodule.span k (L.degreeMonomials 0 0) :=
    L.span_levelMonomials_le_degree (k := k) n
      (L.inv_mem_levelSpan_of_val_mem cu hculvl)
  have hinvc : ((cu⁻¹ : (BinaryLeavittAlgebra k)ˣ) :
      BinaryLeavittAlgebra k) * y 0 = 1 := by
    rw [← hcuval]
    exact cu.inv_mul
  have hcinv : y 0 * ((cu⁻¹ : (BinaryLeavittAlgebra k)ˣ) :
      BinaryLeavittAlgebra k) = 1 := by
    rw [← hcuval]
    exact cu.mul_inv
  -- the unipotent factor
  have hηw : ((cu⁻¹ : (BinaryLeavittAlgebra k)ˣ) :
      BinaryLeavittAlgebra k) * y 1 ∈
      Submodule.span k (L.degreeMonomials 1 1) := by
    have h1 := L.window_mul_mem_span (k := k) hinvw (hymem 1)
    refine L.span_degreeMonomials_mono ?_ ?_ h1 <;> omega
  have hunit1 : ((cu⁻¹ * u : (BinaryLeavittAlgebra k)ˣ) :
      BinaryLeavittAlgebra k) =
      1 + ((cu⁻¹ : (BinaryLeavittAlgebra k)ˣ) :
        BinaryLeavittAlgebra k) * y 1 := by
    rw [Units.val_mul, hval, mul_add, hinvc]
  obtain ⟨D, hD⟩ := pure_tail_nilpotent k hηw (cu⁻¹ * u) hunit1
  refine ⟨y 0, _, _, D, hymem 0, hinvw, hcinv, hinvc, hηw, hD, ?_⟩
  rw [show u = cu * (cu⁻¹ * u) from by group, Units.val_mul, hcuval,
    hunit1]

/-- **Inverse-window control**: the inverse of a `[0,1]`-window unit
has a nonnegative window. -/
theorem nonneg_narrow_unit_inv_window
    [Nontrivial (BinaryLeavittAlgebra k)]
    (u : (BinaryLeavittAlgebra k)ˣ)
    (hu : (u : BinaryLeavittAlgebra k) ∈
      Submodule.span k ((family k).degreeMonomials 0 1)) :
    ∃ K : ℕ, ((u⁻¹ : (BinaryLeavittAlgebra k)ˣ) :
      BinaryLeavittAlgebra k) ∈
      Submodule.span k ((family k).degreeMonomials 0 (K : ℤ)) := by
  classical
  obtain ⟨c, cinv, η, D, -, hcinvw, -, hcinvc, hηw, hD, hval⟩ :=
    nonneg_narrow_unit_structure k u hu
  refine ⟨D, ?_⟩
  set S : BinaryLeavittAlgebra k :=
    ∑ i ∈ Finset.range D, (-η) ^ i with hSdef
  -- the truncated geometric series inverts the unipotent factor
  have hgeom : S * (1 + η) = 1 := by
    have h1 : S * ((-η) - 1) = (-η) ^ D - 1 := geom_sum_mul (-η) D
    -- Give `neg_pow` its arguments: bare `rw [neg_pow]` fails to unify the
    -- pattern `(-?a) ^ ?n` against `(-η) ^ D` here.
    have h2 : (-η) ^ D = 0 := by
      rw [neg_pow η D, hD, mul_zero]
    -- Route through `neg_injective` rather than asking `noncomm_ring` to
    -- reconcile `-1 • (S * -1 • η)` with `S * η`.
    rw [h2, zero_sub] at h1
    have h3 : (-η) - 1 = -(1 + η) := by abel
    -- Explicit arguments again: bare `mul_neg` will not unify `?a * -?b`
    -- against `S * -(1 + η)` in this quotient ring.
    rw [h3, mul_neg S (1 + η)] at h1
    exact neg_injective h1
  have hone : S * cinv * (u : BinaryLeavittAlgebra k) = 1 := by
    rw [hval,
      show S * cinv * (c * (1 + η)) = S * (cinv * c) * (1 + η) from
        by noncomm_ring,
      hcinvc, mul_one, hgeom]
  have hxinv : ((u⁻¹ : (BinaryLeavittAlgebra k)ˣ) :
      BinaryLeavittAlgebra k) = S * cinv := by
    calc ((u⁻¹ : (BinaryLeavittAlgebra k)ˣ) : BinaryLeavittAlgebra k)
        = 1 * ((u⁻¹ : (BinaryLeavittAlgebra k)ˣ) :
            BinaryLeavittAlgebra k) := (one_mul _).symm
      _ = S * cinv * (u : BinaryLeavittAlgebra k) *
          ((u⁻¹ : (BinaryLeavittAlgebra k)ˣ) :
            BinaryLeavittAlgebra k) := by rw [hone]
      _ = S * cinv * ((u : BinaryLeavittAlgebra k) *
          ((u⁻¹ : (BinaryLeavittAlgebra k)ˣ) :
            BinaryLeavittAlgebra k)) := by rw [mul_assoc]
      _ = S * cinv := by rw [Units.mul_inv, mul_one]
  rw [hxinv]
  -- window bookkeeping for the geometric series
  have hpow : ∀ j : ℕ, (-η) ^ j ∈
      Submodule.span k ((family k).degreeMonomials 0 (j : ℤ)) := by
    intro j
    induction j with
    | zero => simpa using (family k).one_mem_window (k := k)
    | succ m ih =>
        rw [pow_succ]
        have h1 := (family k).window_mul_mem_span (k := k) ih
          (Submodule.neg_mem _ hηw)
        -- `refine <;> push_cast` leaves a single goal, so `omega` sequences
        -- after the whole thing rather than running per-branch.
        refine (family k).span_degreeMonomials_mono ?_ ?_ h1 <;>
          push_cast
        omega
  have hS : S ∈ Submodule.span k
      ((family k).degreeMonomials 0 (D : ℤ)) := by
    rw [hSdef]
    refine Submodule.sum_mem _ fun i hi ↦ ?_
    have hiD : i < D := Finset.mem_range.mp hi
    refine (family k).span_degreeMonomials_mono (le_refl _) ?_
      (hpow i)
    omega
  have h2 := (family k).window_mul_mem_span (k := k) hS hcinvw
  refine (family k).span_degreeMonomials_mono ?_ ?_ h2 <;> omega

end BinaryLeavitt
end NonsoficGroupsExist
