import NonsoficGroupsExist.WidthTwoReduction
import NonsoficGroupsExist.IncomparableUnipotents
import NonsoficGroupsExist.GradedComponents

/-!
# The rank-one normal form for narrow units

The stable block move `diag(u, I) ~ [[u - PQ, -P], [Q, I]]` with
`P := A` (the degree `-1` part of the value) and `Q := 1` compresses
the entire negative part of a narrow unit into the single universal
monomial `s₁ t₀₀`: through the mixed-depth code `{00, 01, 1}` the
`-P` slot lands in degree `0` and the `Q` slot is the fixed monomial
`s₁ t₀₀`.  No invertibility or rank hypotheses enter — both
elementary factors are incomparable unipotents.  Every narrow unit is
therefore equivalent modulo the diagonal class group to one of value
`w + s₁ t₀₀` with `w` in the `[0, 1]` window.
-/

namespace NonsoficGroupsExist
namespace BinaryLeavitt

open LeavittFamily MatrixDiagonalization

variable (k : Type) [Field k]

/-- **Rank-one normal form**: every narrow unit is equivalent in the
diagonal class group to a unit whose value is a `[0,1]`-window
element plus the fixed monomial `s₁ t₀₀`. -/
theorem exists_rank_one_normal_form
    [Nontrivial (BinaryLeavittAlgebra k)]
    (u : (BinaryLeavittAlgebra k)ˣ)
    (hu : (u : BinaryLeavittAlgebra k) ∈
      Submodule.span k ((family k).degreeMonomials (-1) 1)) :
    ∃ (u' : (BinaryLeavittAlgebra k)ˣ) (w : BinaryLeavittAlgebra k),
      w ∈ Submodule.span k ((family k).degreeMonomials 0 1) ∧
      (u' : BinaryLeavittAlgebra k) =
        w + (family k).wordS [1] * (family k).wordT [0, 0] ∧
      (u ∈ stableUnits (BinaryLeavittAlgebra k) ↔
        u' ∈ stableUnits (BinaryLeavittAlgebra k)) := by
  classical
  set L : LeavittFamily (BinaryLeavittAlgebra k) := family k with hL
  have hdiv : ∀ x : BinaryLeavittAlgebra k, x ≠ 0 →
      ∃ p q : BinaryLeavittAlgebra k, p * x * q = 1 :=
    fun x hx ↦ exists_mul_mul_eq_one k hx
  -- split off the degree `-1` part of the value
  obtain ⟨y, hymem, -, hysum⟩ := exists_components k hu
  set a : BinaryLeavittAlgebra k := y (-1) with ha
  have haw : a ∈ Submodule.span k (L.degreeMonomials (-1) (-1)) :=
    hymem _
  have hrest : (u : BinaryLeavittAlgebra k) - a ∈
      Submodule.span k (L.degreeMonomials 0 1) := by
    have h1 : (u : BinaryLeavittAlgebra k) - a = y 0 + y 1 := by
      rw [hysum, ha]
      have hIcc : Finset.Icc (-1 : ℤ) 1 = {-1, 0, 1} := by
        ext d
        simp only [Finset.mem_Icc, Finset.mem_insert,
          Finset.mem_singleton]
        omega
      rw [hIcc, Finset.sum_insert (by simp),
        Finset.sum_insert (by simp), Finset.sum_singleton]
      -- purely additive; `ring` needs commutativity
      abel
    rw [h1]
    exact Submodule.add_mem _
      (L.span_degreeMonomials_mono (by omega) (by omega) (hymem 0))
      (L.span_degreeMonomials_mono (by omega) (by omega) (hymem 1))
  -- the corner embedding at `00`
  have hts : L.wordT [0, 0] * L.wordS [0, 0] = 1 :=
    L.wordT_mul_wordS_self [0, 0]
  set κ : (BinaryLeavittAlgebra k)ˣ :=
    pairKappaUnit (L.wordS [0, 0]) (L.wordT [0, 0]) hts u with hκ
  have hκmem : κ * u⁻¹ ∈ stableUnits (BinaryLeavittAlgebra k) :=
    pairKappaUnit_mul_inv_mem_stableUnits _ _ hts hdiv u
  have hκval : (κ : BinaryLeavittAlgebra k) =
      1 + L.wordS [0, 0] *
        ((u : BinaryLeavittAlgebra k) - 1) * L.wordT [0, 0] := by
    show L.wordS [0, 0] * (u : BinaryLeavittAlgebra k) *
        L.wordT [0, 0] + (1 - L.wordS [0, 0] * L.wordT [0, 0]) = _
    have h1 : L.wordS [0, 0] *
        ((u : BinaryLeavittAlgebra k) - 1) * L.wordT [0, 0] =
        L.wordS [0, 0] * (u : BinaryLeavittAlgebra k) *
          L.wordT [0, 0] -
        L.wordS [0, 0] * L.wordT [0, 0] := by
      -- `noncomm_ring` leaves `A * ((-1 • 1) * B)` against
      -- `-1 • (A * B)`; migrate the scalar outwards.
      noncomm_ring
      simp only [smul_mul_assoc, mul_smul_comm, one_mul]
    rw [h1]
    noncomm_ring
  -- the two incomparable-unipotent block moves
  have hinc₁ : ¬[(1 : Fin 2)] <+: [(0 : Fin 2), 0] := by decide
  have hinc₁' : ¬[(0 : Fin 2), 0] <+: [(1 : Fin 2)] := by decide
  set mR : (BinaryLeavittAlgebra k)ˣ :=
    L.incomparableUnit hinc₁ hinc₁' 1 with hmR
  have hmRval : (mR : BinaryLeavittAlgebra k) =
      1 + L.wordS [1] * 1 * L.wordT [0, 0] := rfl
  have hmRmem : mR ∈ stableUnits (BinaryLeavittAlgebra k) :=
    L.incomparableUnit_mem hinc₁ hinc₁' 1
  have hinc₂ : ¬[(0 : Fin 2), 0] <+: [(1 : Fin 2)] := by decide
  have hinc₂' : ¬[(1 : Fin 2)] <+: [(0 : Fin 2), 0] := by decide
  set mL : (BinaryLeavittAlgebra k)ˣ :=
    L.incomparableUnit hinc₂ hinc₂' (-a) with hmL
  have hmLval : (mL : BinaryLeavittAlgebra k) =
      1 + L.wordS [0, 0] * (-a) * L.wordT [1] := rfl
  have hmLmem : mL ∈ stableUnits (BinaryLeavittAlgebra k) :=
    L.incomparableUnit_mem hinc₂ hinc₂' (-a)
  -- the normal-form unit
  set u' : (BinaryLeavittAlgebra k)ˣ := mL * κ * mR with hu'
  -- word collapses
  have hz₁ : L.wordT [0, 0] * L.wordS [1] = 0 :=
    L.wordT_mul_wordS_of_incomparable _ _ hinc₁' hinc₁
  have hz₂ : L.wordT [1] * L.wordS [0, 0] = 0 :=
    L.wordT_mul_wordS_of_incomparable _ _ hinc₁ hinc₁'
  have hone₁ : L.wordT [1] * L.wordS [1] = 1 :=
    L.wordT_mul_wordS_self _
  -- the value computation
  set z : BinaryLeavittAlgebra k :=
    (u : BinaryLeavittAlgebra k) - 1 with hz
  have hstep₁ : (κ : BinaryLeavittAlgebra k) *
      (mR : BinaryLeavittAlgebra k) =
      1 + L.wordS [0, 0] * z * L.wordT [0, 0] +
        L.wordS [1] * L.wordT [0, 0] := by
    -- No `← hz`: `set` already folded `↑u - 1` into `z`.
    rw [hκval, hmRval]
    have hcross : L.wordS [0, 0] * z * L.wordT [0, 0] *
        (L.wordS [1] * 1 * L.wordT [0, 0]) = 0 := by
      rw [show L.wordS [0, 0] * z * L.wordT [0, 0] *
        (L.wordS [1] * 1 * L.wordT [0, 0]) =
        L.wordS [0, 0] * z * (L.wordT [0, 0] * L.wordS [1]) *
          (1 * L.wordT [0, 0]) from by noncomm_ring, hz₁]
      noncomm_ring
    calc (1 + L.wordS [0, 0] * z * L.wordT [0, 0]) *
          (1 + L.wordS [1] * 1 * L.wordT [0, 0])
        = 1 + L.wordS [0, 0] * z * L.wordT [0, 0] +
          L.wordS [1] * 1 * L.wordT [0, 0] +
          L.wordS [0, 0] * z * L.wordT [0, 0] *
            (L.wordS [1] * 1 * L.wordT [0, 0]) := by noncomm_ring
      _ = 1 + L.wordS [0, 0] * z * L.wordT [0, 0] +
          L.wordS [1] * L.wordT [0, 0] := by
          rw [hcross]
          noncomm_ring
  have hu'val : (u' : BinaryLeavittAlgebra k) =
      (1 + L.wordS [0, 0] * (z - a) * L.wordT [0, 0] -
        L.wordS [0, 0] * a * L.wordT [1]) +
      L.wordS [1] * L.wordT [0, 0] := by
    -- `u' = mL * κ * mR` associates to the *left*, so the `show` must
    -- match that; reassociate afterwards to expose `↑κ * ↑mR` for `hstep₁`.
    show ((mL : BinaryLeavittAlgebra k) * (κ : BinaryLeavittAlgebra k))
      * (mR : BinaryLeavittAlgebra k) = _
    rw [mul_assoc, hstep₁, hmLval]
    have hc₁ : L.wordS [0, 0] * (-a) * L.wordT [1] *
        (L.wordS [0, 0] * z * L.wordT [0, 0]) = 0 := by
      rw [show L.wordS [0, 0] * (-a) * L.wordT [1] *
        (L.wordS [0, 0] * z * L.wordT [0, 0]) =
        L.wordS [0, 0] * (-a) * (L.wordT [1] * L.wordS [0, 0]) *
          (z * L.wordT [0, 0]) from by noncomm_ring, hz₂]
      noncomm_ring
    have hc₂ : L.wordS [0, 0] * (-a) * L.wordT [1] *
        (L.wordS [1] * L.wordT [0, 0]) =
        -(L.wordS [0, 0] * a * L.wordT [0, 0]) := by
      rw [show L.wordS [0, 0] * (-a) * L.wordT [1] *
        (L.wordS [1] * L.wordT [0, 0]) =
        L.wordS [0, 0] * (-a) * (L.wordT [1] * L.wordS [1]) *
          L.wordT [0, 0] from by noncomm_ring, hone₁]
      noncomm_ring
      simp only [smul_mul_assoc, mul_smul_comm]
    calc (1 + L.wordS [0, 0] * (-a) * L.wordT [1]) *
          (1 + L.wordS [0, 0] * z * L.wordT [0, 0] +
            L.wordS [1] * L.wordT [0, 0])
        = 1 + L.wordS [0, 0] * z * L.wordT [0, 0] +
          L.wordS [1] * L.wordT [0, 0] +
          L.wordS [0, 0] * (-a) * L.wordT [1] +
          L.wordS [0, 0] * (-a) * L.wordT [1] *
            (L.wordS [0, 0] * z * L.wordT [0, 0]) +
          L.wordS [0, 0] * (-a) * L.wordT [1] *
            (L.wordS [1] * L.wordT [0, 0]) := by noncomm_ring
      _ = (1 + L.wordS [0, 0] * (z - a) * L.wordT [0, 0] -
            L.wordS [0, 0] * a * L.wordT [1]) +
          L.wordS [1] * L.wordT [0, 0] := by
          rw [hc₁, hc₂]
          noncomm_ring
          -- after migrating the scalars out, the two sides differ only
          -- in the order of the summands
          simp only [smul_mul_assoc, mul_smul_comm]
          abel
  -- the `[0,1]`-window part
  have hs00w : L.wordS [0, 0] ∈ Submodule.span k
      (L.degreeMonomials 2 2) :=
    Submodule.subset_span ⟨[0, 0], [], by simp, by simp, by simp⟩
  have ht00w : L.wordT [0, 0] ∈ Submodule.span k
      (L.degreeMonomials (-2) (-2)) :=
    Submodule.subset_span ⟨[], [0, 0], by simp, by simp, by simp⟩
  have ht1w : L.wordT [1] ∈ Submodule.span k
      (L.degreeMonomials (-1) (-1)) :=
    Submodule.subset_span ⟨[], [1], by simp, by simp, by simp⟩
  have hwmem : (1 : BinaryLeavittAlgebra k) +
      L.wordS [0, 0] * (z - a) * L.wordT [0, 0] -
      L.wordS [0, 0] * a * L.wordT [1] ∈
      Submodule.span k (L.degreeMonomials 0 1) := by
    refine Submodule.sub_mem _ (Submodule.add_mem _
      (L.span_degreeMonomials_mono (by omega) (by omega)
        (L.one_mem_window (k := k))) ?_) ?_
    · have hza : z - a ∈
          Submodule.span k (L.degreeMonomials 0 1) := by
        rw [hz]
        rw [show (u : BinaryLeavittAlgebra k) - 1 - a =
          ((u : BinaryLeavittAlgebra k) - a) - 1 from by abel]
        exact Submodule.sub_mem _ hrest
          (L.span_degreeMonomials_mono (by omega) (by omega)
            (L.one_mem_window (k := k)))
      have h1 := L.window_mul_mem_span (k := k)
        (L.window_mul_mem_span (k := k) hs00w hza) ht00w
      refine L.span_degreeMonomials_mono ?_ ?_ h1 <;> omega
    · have h1 := L.window_mul_mem_span (k := k)
        (L.window_mul_mem_span (k := k) hs00w haw) ht1w
      refine L.span_degreeMonomials_mono ?_ ?_ h1 <;> omega
  refine ⟨u', 1 + L.wordS [0, 0] * (z - a) * L.wordT [0, 0] -
    L.wordS [0, 0] * a * L.wordT [1], hwmem, ?_, ?_⟩
  -- `rw [hu'val]` closes this outright; `L` is reducibly `family k`, so
  -- the follow-up rewrite had no goal left to act on.
  · rw [hu'val]
  · constructor
    · intro huH
      rw [hu']
      have hκH : κ ∈ stableUnits (BinaryLeavittAlgebra k) := by
        have h1 : κ = (κ * u⁻¹) * u := by group
        rw [h1]
        exact mul_mem hκmem huH
      exact mul_mem (mul_mem hmLmem hκH) hmRmem
    · intro hu'H
      have hκH : κ ∈ stableUnits (BinaryLeavittAlgebra k) := by
        have h1 : κ = mL⁻¹ * u' * mR⁻¹ := by
          rw [hu']
          group
        rw [h1]
        exact mul_mem (mul_mem (inv_mem hmLmem) hu'H) (inv_mem hmRmem)
      have h2 : u = (κ * u⁻¹)⁻¹ * κ := by group
      rw [h2]
      exact mul_mem (inv_mem hκmem) hκH

end BinaryLeavitt
end NonsoficGroupsExist
