import NonsoficGroupsExist.EntryStrip
import NonsoficGroupsExist.PencilEntryArith
import NonsoficGroupsExist.GradedComponents
-- `one_mem_window` lives here
import NonsoficGroupsExist.NilpotentTailKill
-- `window_mul_mem_span` lives here
import NonsoficGroupsExist.WindowProductClosure

/-!
# The entrywise kill

For a pencil unit over a code pair, a scalar left inverse of the
stack `[B₀; B₁]` kills every positive-degree component of every entry
`T(Cⱼ)·u⁻¹·S(Rᵢ)` of the inverse: the strip equations
`Σⱼ x_{ij}·y_{ji'} = δᵢᵢ'` decompose degreewise, only the `s`-part
survives at the top, `t_w`-strips turn it into scalar relations
`Σⱼ B_wᵢⱼ·y⁽ᴰ⁾ = 0`, and the scalar inverse combines these to kill
each component.  This is the inner-node replacement for the
top-level window dichotomy, valid at arbitrary mixed-depth codes.
-/

namespace NonsoficGroupsExist
namespace BinaryLeavitt

open LeavittFamily MatrixDiagonalization

variable (k : Type) [Field k]

section StripHelpers

variable {A : Type*} [Ring A] (L : LeavittFamily A)
variable {k' : Type*} [Field k'] [Algebra k' A]

theorem t_zero_strip_scombo (β₀ β₁ : k') (Yv : A) :
    L.t 0 * ((β₀ • L.s 0 + β₁ • L.s 1) * Yv) = β₀ • Yv := by
  rw [add_mul, smul_mul_assoc, smul_mul_assoc, mul_add,
    mul_smul_comm, mul_smul_comm, ← mul_assoc, ← mul_assoc,
    t_mul_s, t_mul_s, if_pos rfl,
    if_neg (show ¬(0 : Fin 2) = 1 by decide), one_mul, zero_mul,
    smul_zero, add_zero]

theorem t_one_strip_scombo (β₀ β₁ : k') (Yv : A) :
    L.t 1 * ((β₀ • L.s 0 + β₁ • L.s 1) * Yv) = β₁ • Yv := by
  rw [add_mul, smul_mul_assoc, smul_mul_assoc, mul_add,
    mul_smul_comm, mul_smul_comm, ← mul_assoc, ← mul_assoc,
    t_mul_s, t_mul_s, if_neg (show ¬(1 : Fin 2) = 0 by decide),
    if_pos rfl, zero_mul, one_mul, smul_zero, zero_add]

end StripHelpers

theorem entry_window_nonpos_of_B_full
    [Nontrivial (BinaryLeavittAlgebra k)]
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (R : BinaryPrefixCode ι) (C : BinaryPrefixCode κ)
    (hC : (family k).IsComplete C)
    (A₀ A₁ Cm B₀ B₁ : ι → κ → k) (u : (BinaryLeavittAlgebra k)ˣ)
    (hu : (u : BinaryLeavittAlgebra k) = ∑ i, ∑ j,
      (family k).wordS (R.word i) *
      (family k).pencilEntry (k := k) (A₀ i j) (A₁ i j) (Cm i j)
        (B₀ i j) (B₁ i j) * (family k).wordT (C.word j))
    (G₀ G₁ : κ → ι → k)
    (hG : ∀ j j' : κ, (∑ i, (G₀ j i * B₀ i j' + G₁ j i * B₁ i j')) =
      if j = j' then 1 else 0) :
    ∃ N : ℕ, ∀ (j : κ) (i : ι),
      (family k).wordT (C.word j) *
        ((u⁻¹ : (BinaryLeavittAlgebra k)ˣ) : BinaryLeavittAlgebra k) *
        (family k).wordS (R.word i) ∈
      Submodule.span k ((family k).degreeMonomials (-(N : ℤ)) 0) := by
  classical
  set L : LeavittFamily (BinaryLeavittAlgebra k) := family k with hL
  set y : κ → ι → BinaryLeavittAlgebra k := fun j i ↦
    L.wordT (C.word j) *
      ((u⁻¹ : (BinaryLeavittAlgebra k)ˣ) : BinaryLeavittAlgebra k) *
      L.wordS (R.word i) with hy
  -- a common window for all entries
  have hex : ∀ p : κ × ι, ∃ n : ℕ, y p.1 p.2 ∈
      Submodule.span k (L.degreeMonomials (-(n : ℤ)) n) := by
    intro p
    obtain ⟨lo, hi, h⟩ := exists_mem_span_degreeMonomials k (y p.1 p.2)
    refine ⟨max lo.natAbs hi.natAbs,
      L.span_degreeMonomials_mono ?_ ?_ h⟩ <;> omega
  choose f hf using hex
  set N : ℕ := Finset.univ.sup f with hNdef
  have hN : ∀ j i, y j i ∈
      Submodule.span k (L.degreeMonomials (-(N : ℤ)) N) := by
    intro j i
    refine L.span_degreeMonomials_mono ?_ ?_ (hf ⟨j, i⟩) <;>
      have := Finset.le_sup (f := f) (Finset.mem_univ (j, i)) <;>
      omega
  -- graded components of every entry
  have hcomp : ∀ p : κ × ι, ∃ Y : ℤ → BinaryLeavittAlgebra k,
      (∀ d, Y d ∈ Submodule.span k (L.degreeMonomials d d)) ∧
      (∀ d, d < -(N : ℤ) ∨ (N : ℤ) < d → Y d = 0) ∧
      y p.1 p.2 = ∑ d ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), Y d :=
    fun p ↦ exists_components k (hN p.1 p.2)
  choose Y hYmem hYsupp hYsum using hcomp
  -- the three pencil-entry parts
  set tP : ι → κ → BinaryLeavittAlgebra k := fun i j ↦
    A₀ i j • L.t 0 + A₁ i j • L.t 1 with htP
  set cP : ι → κ → BinaryLeavittAlgebra k := fun i j ↦
    Cm i j • (1 : BinaryLeavittAlgebra k) with hcP
  set sP : ι → κ → BinaryLeavittAlgebra k := fun i j ↦
    B₀ i j • L.s 0 + B₁ i j • L.s 1 with hsP
  have htPmem : ∀ i j, tP i j ∈
      Submodule.span k (L.degreeMonomials (-1) (-1)) := by
    intro i j
    -- the two summands need *different* letters, so `<;>` cannot serve both:
    -- it would have to solve `L.t ?m = L.t0` and `L.t ?m = L.t1` at one `?m`.
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_)
      (Submodule.smul_mem _ _ ?_)
    · exact Submodule.subset_span ⟨[], [0], by simp, by simp, by simp⟩
    · exact Submodule.subset_span ⟨[], [1], by simp, by simp, by simp⟩
  have hcPmem : ∀ i j, cP i j ∈
      Submodule.span k (L.degreeMonomials 0 0) := fun i j ↦
    Submodule.smul_mem _ _ (L.one_mem_window (k := k))
  have hsPmem : ∀ i j, sP i j ∈
      Submodule.span k (L.degreeMonomials 1 1) := by
    intro i j
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_)
      (Submodule.smul_mem _ _ ?_)
    · exact Submodule.subset_span ⟨[0], [], by simp, by simp, by simp⟩
    · exact Submodule.subset_span ⟨[1], [], by simp, by simp, by simp⟩
  -- the strip equations
  have hstrip : ∀ i i' : ι, (∑ j, (tP i j + cP i j + sP i j) *
      y j i') = if i = i' then (1 : BinaryLeavittAlgebra k) else 0 := by
    intro i i'
    have h1 := L.strip_insert C hC (u : BinaryLeavittAlgebra k)
      ((u⁻¹ : (BinaryLeavittAlgebra k)ˣ) : BinaryLeavittAlgebra k)
      (R.word i) (R.word i')
    rw [Units.mul_inv, mul_one, L.prefixCode_orthogonal R i i'] at h1
    -- `h1 : (if i = i' then 1 else 0) = ∑ j, …`, so the forward direction is
    -- the one that turns the goal's `if` into the sum we can match termwise.
    rw [h1]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    congr 1
    have h2 : L.wordT (R.word i) * (u : BinaryLeavittAlgebra k) *
        L.wordS (C.word j) =
        L.pencilEntry (k := k) (A₀ i j) (A₁ i j) (Cm i j) (B₀ i j)
          (B₁ i j) := by
      rw [hu]
      exact L.wordT_pencilVal_wordS R C _ i j
    rw [h2]
    rfl
  -- degreewise equations
  have hzmem : ∀ (i i' : ι) (D : ℤ),
      (∑ j, (tP i j * Y (j, i') (D + 1) + cP i j * Y (j, i') D +
        sP i j * Y (j, i') (D + (-1)))) ∈
      Submodule.span k (L.degreeMonomials D D) := by
    intro i i' D
    refine Submodule.sum_mem _ fun j _ ↦
      Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · have h := L.window_mul_mem_span (k := k) (htPmem i j)
        (hYmem (j, i') (D + 1))
      refine L.span_degreeMonomials_mono ?_ ?_ h <;> omega
    · have h := L.window_mul_mem_span (k := k) (hcPmem i j)
        (hYmem (j, i') D)
      refine L.span_degreeMonomials_mono ?_ ?_ h <;> omega
    · have h := L.window_mul_mem_span (k := k) (hsPmem i j)
        (hYmem (j, i') (D + (-1)))
      refine L.span_degreeMonomials_mono ?_ ?_ h <;> omega
  have hzsum : ∀ i i' : ι,
      (∑ D ∈ Finset.Icc (-(N : ℤ) - 1) ((N : ℤ) + 1),
        ∑ j, (tP i j * Y (j, i') (D + 1) + cP i j * Y (j, i') D +
          sP i j * Y (j, i') (D + (-1)))) =
      if i = i' then (1 : BinaryLeavittAlgebra k) else 0 := by
    intro i i'
    rw [Finset.sum_comm]
    rw [show (∑ j, ∑ D ∈ Finset.Icc (-(N : ℤ) - 1) ((N : ℤ) + 1),
        (tP i j * Y (j, i') (D + 1) + cP i j * Y (j, i') D +
          sP i j * Y (j, i') (D + (-1)))) =
      ∑ j, (tP i j + cP i j + sP i j) * y j i' from
      Finset.sum_congr rfl fun j _ ↦ ?_]
    · exact hstrip i i'
    -- one code entry: three shifted sums
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    have hsh1 : ∑ D ∈ Finset.Icc (-(N : ℤ) - 1) ((N : ℤ) + 1),
        Y (j, i') (D + 1) = y j i' := by
      have hm := Finset.sum_map (Finset.Icc (-(N : ℤ) - 1) ((N : ℤ) + 1))
        (addRightEmbedding (1 : ℤ)) (Y (j, i'))
      simp only [addRightEmbedding_apply] at hm
      rw [Finset.map_add_right_Icc] at hm
      rw [show -(N : ℤ) - 1 + 1 = -(N : ℤ) from by ring,
        show (N : ℤ) + 1 + 1 = (N : ℤ) + 2 from by ring] at hm
      rw [← hm, hYsum (j, i')]
      exact (Finset.sum_subset
        (Finset.Icc_subset_Icc le_rfl (by omega))
        (fun d hd hd' ↦ hYsupp (j, i') d (Or.inr (by
          rw [Finset.mem_Icc] at hd
          rw [Finset.mem_Icc] at hd'
          omega)))).symm
    have hsh0 : ∑ D ∈ Finset.Icc (-(N : ℤ) - 1) ((N : ℤ) + 1),
        Y (j, i') D = y j i' := by
      rw [hYsum (j, i')]
      exact (Finset.sum_subset
        (Finset.Icc_subset_Icc (by omega) (by omega))
        (fun d hd hd' ↦ hYsupp (j, i') d (by
          rw [Finset.mem_Icc] at hd
          rw [Finset.mem_Icc] at hd'
          omega))).symm
    have hsh2 : ∑ D ∈ Finset.Icc (-(N : ℤ) - 1) ((N : ℤ) + 1),
        Y (j, i') (D + (-1)) = y j i' := by
      have hm := Finset.sum_map (Finset.Icc (-(N : ℤ) - 1) ((N : ℤ) + 1))
        (addRightEmbedding (-1 : ℤ)) (Y (j, i'))
      simp only [addRightEmbedding_apply] at hm
      rw [Finset.map_add_right_Icc] at hm
      rw [show -(N : ℤ) - 1 + (-1) = -(N : ℤ) - 2 from by ring,
        show (N : ℤ) + 1 + (-1) = (N : ℤ) from by ring] at hm
      rw [← hm, hYsum (j, i')]
      exact (Finset.sum_subset
        (Finset.Icc_subset_Icc (by omega) le_rfl)
        (fun d hd hd' ↦ hYsupp (j, i') d (Or.inl (by
          rw [Finset.mem_Icc] at hd
          rw [Finset.mem_Icc] at hd'
          omega)))).symm
    rw [hsh1, hsh0, hsh2, ← add_mul, ← add_mul]
  -- uniqueness gives the degreewise equations
  have huniq : ∀ i i' : ι, ∀ D ∈ Finset.Icc (-(N : ℤ) - 1) ((N : ℤ) + 1),
      (∑ j, (tP i j * Y (j, i') (D + 1) + cP i j * Y (j, i') D +
        sP i j * Y (j, i') (D + (-1)))) =
      (if D = 0 then (if i = i' then (1 : BinaryLeavittAlgebra k)
        else 0) else 0) := by
    intro i i'
    have h := components_unique k
      (D := Finset.Icc (-(N : ℤ) - 1) ((N : ℤ) + 1))
      (y := fun D ↦ ∑ j, (tP i j * Y (j, i') (D + 1) +
        cP i j * Y (j, i') D + sP i j * Y (j, i') (D + (-1))))
      (z := fun D ↦ if D = 0 then
        (if i = i' then (1 : BinaryLeavittAlgebra k) else 0) else 0)
      (fun D _ ↦ hzmem i i' D)
      (fun D _ ↦ by
        split_ifs with h1 h2
        · rw [h1]
          exact L.one_mem_window (k := k)
        · rw [h1]
          exact Submodule.zero_mem _
        · exact Submodule.zero_mem _)
      (by
        rw [hzsum i i']
        rw [Finset.sum_ite_eq' (Finset.Icc (-(N : ℤ) - 1) ((N : ℤ) + 1))
          (0 : ℤ) (fun _ ↦ if i = i' then
            (1 : BinaryLeavittAlgebra k) else 0)]
        rw [if_pos (Finset.mem_Icc.mpr (by omega))])
    intro D hD
    have := h D hD
    beta_reduce at this
    exact this
  -- kill the positive components from the top down
  have hkill : ∀ n : ℕ, ∀ d : ℤ, 1 ≤ d → (N : ℤ) + 1 - n ≤ d →
      ∀ j i', Y (j, i') d = 0 := by
    intro n
    induction n with
    | zero =>
        intro d _ h2 j i'
        exact hYsupp (j, i') d (Or.inr (by omega))
    | succ m ih =>
        intro d hd1 hd2 j₀ i'
        by_cases hcase : (N : ℤ) + 1 - m ≤ d
        · exact ih d hd1 hcase j₀ i'
        · -- the `s`-part relations at degree `d`
          have hsPrel : ∀ i : ι,
              (∑ j, sP i j * Y (j, i') d) = 0 := by
            intro i
            have heq := huniq i i' (d + 1)
              (Finset.mem_Icc.mpr (by omega))
            rw [if_neg (by omega : ¬(d + 1 = 0)),
              show d + 1 + 1 = d + 2 from by ring,
              show d + 1 + (-1) = d from by ring] at heq
            rw [Finset.sum_congr rfl (fun j _ ↦ by
              rw [ih (d + 2) (by omega) (by omega) j i',
                ih (d + 1) (by omega) (by omega) j i', mul_zero,
                mul_zero, zero_add, zero_add])] at heq
            exact heq
          have hBrel₀ : ∀ i : ι,
              (∑ j, B₀ i j • Y (j, i') d) = 0 := by
            intro i
            have h : (family k).t 0 *
                (∑ j, sP i j * Y (j, i') d) = (family k).t 0 * 0 := by
              rw [hsPrel i]
            rw [mul_zero, Finset.mul_sum] at h
            rw [Finset.sum_congr rfl (fun j _ ↦ by
              rw [show sP i j = B₀ i j • (family k).s 0 +
                  B₁ i j • (family k).s 1 from rfl]
              exact (family k).t_zero_strip_scombo _ _ _)] at h
            exact h
          have hBrel₁ : ∀ i : ι,
              (∑ j, B₁ i j • Y (j, i') d) = 0 := by
            intro i
            have h : (family k).t 1 *
                (∑ j, sP i j * Y (j, i') d) = (family k).t 1 * 0 := by
              rw [hsPrel i]
            rw [mul_zero, Finset.mul_sum] at h
            rw [Finset.sum_congr rfl (fun j _ ↦ by
              rw [show sP i j = B₀ i j • (family k).s 0 +
                  B₁ i j • (family k).s 1 from rfl]
              exact (family k).t_one_strip_scombo _ _ _)] at h
            exact h
          -- combine with the scalar left inverse
          calc Y (j₀, i') d
              = ∑ j, (if j₀ = j then (1 : k) else 0) •
                Y (j, i') d := by
                rw [Finset.sum_congr rfl (fun j _ ↦ by
                  split_ifs with h
                  · rw [one_smul]
                  · rw [zero_smul] :
                  ∀ j ∈ Finset.univ, (if j₀ = j then (1 : k) else 0) •
                    Y (j, i') d = if j₀ = j then Y (j, i') d else 0),
                  Finset.sum_ite_eq Finset.univ j₀,
                  if_pos (Finset.mem_univ j₀)]
            _ = ∑ j, (∑ i, (G₀ j₀ i * B₀ i j + G₁ j₀ i * B₁ i j)) •
                Y (j, i') d := by
                refine Finset.sum_congr rfl fun j _ ↦ ?_
                rw [hG j₀ j]
            _ = ∑ i, (G₀ j₀ i • (∑ j, B₀ i j • Y (j, i') d) +
                G₁ j₀ i • (∑ j, B₁ i j • Y (j, i') d)) := by
                rw [Finset.sum_congr rfl (fun j _ ↦ by
                  rw [Finset.sum_smul] :
                  ∀ j ∈ Finset.univ,
                    (∑ i, (G₀ j₀ i * B₀ i j + G₁ j₀ i * B₁ i j)) •
                      Y (j, i') d =
                    ∑ i, (G₀ j₀ i * B₀ i j + G₁ j₀ i * B₁ i j) •
                      Y (j, i') d),
                  Finset.sum_comm]
                refine Finset.sum_congr rfl fun i _ ↦ ?_
                rw [Finset.smul_sum, Finset.smul_sum,
                  ← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl fun j _ ↦ ?_
                rw [add_smul, smul_smul, smul_smul]
            _ = 0 := by
                rw [Finset.sum_congr rfl (fun i _ ↦ by
                  rw [hBrel₀ i, hBrel₁ i, smul_zero, smul_zero,
                    add_zero])]
                exact Finset.sum_const_zero
  -- reassemble the entries
  refine ⟨N, fun j i ↦ ?_⟩
  show y j i ∈ Submodule.span k (L.degreeMonomials (-(N : ℤ)) 0)
  rw [hYsum (j, i)]
  have hsplit : ∑ d ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), Y (j, i) d =
      ∑ d ∈ Finset.Icc (-(N : ℤ)) 0, Y (j, i) d :=
    (Finset.sum_subset (Finset.Icc_subset_Icc le_rfl (by omega))
      (fun d hd hd' ↦ by
        rw [Finset.mem_Icc] at hd
        rw [Finset.mem_Icc] at hd'
        exact hkill ((N : ℤ) + 1 - d).toNat d (by omega) (by omega)
          j i)).symm
  rw [hsplit]
  refine Submodule.sum_mem _ fun d hd ↦ ?_
  rw [Finset.mem_Icc] at hd
  exact L.span_degreeMonomials_mono (by omega) (by omega)
    (hYmem (j, i) d)

end BinaryLeavitt
end NonsoficGroupsExist
