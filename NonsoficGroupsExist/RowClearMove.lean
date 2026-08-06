import NonsoficGroupsExist.PencilEntryArith
import NonsoficGroupsExist.MixedCodeMoves

/-!
# Clearing the atom rows

Once a pencil column `j₀` carries the exact shift atom — `A₀`-column
`= e_{i₁}`, `A₁`-column `= e_{i₂}`, no constant or `s`-content — one
block-unipotent right move erases everything else in rows `i₁, i₂`:
subtract from each other column the atom column times
`x_j := s₀·E(i₁,j) + s₁·E(i₂,j)`; the collapse `t_z s_w = δ` makes the
correction exact, so the resulting data is the original with rows
`i₁, i₂` zeroed outside `j₀` and nothing else touched.  The move is a
block unipotent supported on `{j₀} × (κ \ {j₀})`, hence in `H`.
-/

namespace NonsoficGroupsExist
namespace LeavittFamily

open MatrixDiagonalization

variable {A : Type*} [Ring A] (L : LeavittFamily A)
variable {k : Type*} [Field k] [Algebra k A]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
variable [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] in
/-- The pencil value collapses against a single column word. -/
theorem pencilVal_mul_wordS (R : BinaryPrefixCode ι)
    (C : BinaryPrefixCode κ) (E : ι → κ → A) (j₀ : κ) :
    (∑ i, ∑ j, L.wordS (R.word i) * E i j * L.wordT (C.word j)) *
      L.wordS (C.word j₀) =
    ∑ i, L.wordS (R.word i) * E i j₀ := by
  classical
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_mul]
  calc ∑ j, L.wordS (R.word i) * E i j * L.wordT (C.word j) *
        L.wordS (C.word j₀)
      = ∑ j, (if j = j₀ then L.wordS (R.word i) * E i j else 0) := by
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [mul_assoc, L.prefixCode_orthogonal C j j₀]
        split_ifs with h
        · rw [mul_one]
        · rw [mul_zero]
    _ = L.wordS (R.word i) * E i j₀ := by
        rw [Finset.sum_ite_eq' Finset.univ j₀, if_pos (Finset.mem_univ j₀)]

/-- `t₀` against an `s`-paired correction selects the first row. -/
theorem t_zero_collapse (P Q : A) :
    L.t 0 * (L.s 0 * P + L.s 1 * Q) = P := by
  rw [mul_add, ← mul_assoc, ← mul_assoc, t_mul_s, t_mul_s,
    if_pos rfl, if_neg (show ¬(0 : Fin 2) = 1 by decide), one_mul,
    zero_mul, add_zero]

theorem t_one_collapse (P Q : A) :
    L.t 1 * (L.s 0 * P + L.s 1 * Q) = Q := by
  rw [mul_add, ← mul_assoc, ← mul_assoc, t_mul_s, t_mul_s,
    if_neg (show ¬(1 : Fin 2) = 0 by decide), if_pos rfl, zero_mul,
    one_mul, zero_add]

/-- **The row-clearing move.** -/
theorem row_clear [Nontrivial A]
    (R : BinaryPrefixCode ι) (C : BinaryPrefixCode κ)
    (A₀ A₁ Cm B₀ B₁ : ι → κ → k) (u : Aˣ)
    (hu : (u : A) = ∑ i, ∑ j, L.wordS (R.word i) *
      L.pencilEntry (k := k) (A₀ i j) (A₁ i j) (Cm i j) (B₀ i j)
        (B₁ i j) * L.wordT (C.word j))
    (i₁ i₂ : ι) (hne : i₁ ≠ i₂) (j₀ : κ)
    (hA₀ : ∀ i, A₀ i j₀ = if i = i₁ then 1 else 0)
    (hA₁ : ∀ i, A₁ i j₀ = if i = i₂ then 1 else 0)
    (hC0 : ∀ i, Cm i j₀ = 0) (hB₀0 : ∀ i, B₀ i j₀ = 0)
    (hB₁0 : ∀ i, B₁ i j₀ = 0) :
    ∃ u' : Aˣ, ((u' : A) = ∑ i, ∑ j, L.wordS (R.word i) *
      L.pencilEntry (k := k)
        (if j ≠ j₀ ∧ (i = i₁ ∨ i = i₂) then 0 else A₀ i j)
        (if j ≠ j₀ ∧ (i = i₁ ∨ i = i₂) then 0 else A₁ i j)
        (if j ≠ j₀ ∧ (i = i₁ ∨ i = i₂) then 0 else Cm i j)
        (if j ≠ j₀ ∧ (i = i₁ ∨ i = i₂) then 0 else B₀ i j)
        (if j ≠ j₀ ∧ (i = i₁ ∨ i = i₂) then 0 else B₁ i j) *
      L.wordT (C.word j)) ∧
      (u ∈ stableUnits A ↔ u' ∈ stableUnits A) := by
  classical
  -- the correction elements
  set x : κ → A := fun j ↦
    L.s 0 * L.pencilEntry (k := k) (A₀ i₁ j) (A₁ i₁ j) (Cm i₁ j)
      (B₀ i₁ j) (B₁ i₁ j) +
    L.s 1 * L.pencilEntry (k := k) (A₀ i₂ j) (A₁ i₂ j) (Cm i₂ j)
      (B₀ i₂ j) (B₁ i₂ j) with hx
  set N : A := ∑ j ∈ Finset.univ.erase j₀,
    L.wordS (C.word j₀) * x j * L.wordT (C.word j) with hN
  -- the correction squares to zero
  have hN2 : N * N = 0 := by
    rw [hN, Finset.sum_mul]
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_eq_zero fun j' hj' ↦ ?_
    have hne : j ≠ j₀ := (Finset.mem_erase.mp hj).1
    have horth : L.wordT (C.word j) * L.wordS (C.word j₀) = 0 := by
      have h := L.prefixCode_orthogonal C j j₀
      rw [if_neg hne] at h
      exact h
    rw [show L.wordS (C.word j₀) * x j * L.wordT (C.word j) *
        (L.wordS (C.word j₀) * x j' * L.wordT (C.word j')) =
      L.wordS (C.word j₀) * x j *
        (L.wordT (C.word j) * L.wordS (C.word j₀)) *
        (x j' * L.wordT (C.word j')) from by noncomm_ring,
      horth, mul_zero, zero_mul]
  -- the move as a unit
  set m : Aˣ := ⟨1 - N, 1 + N, by
      rw [mul_add, mul_one, sub_mul, one_mul, hN2]
      noncomm_ring, by
      rw [mul_sub, mul_one, add_mul, one_mul, hN2]
      noncomm_ring⟩ with hm
  have hmmem : m ∈ stableUnits A := by
    -- `S`/`T` are only pinned down by `hu`, which is deferred as `?_`, so
    -- they have to be named here or every downstream metavariable is stuck.
    refine L.code_unipotent_mem C
      (S := ({j₀} : Finset κ)) (T := Finset.univ.erase j₀)
      (Finset.disjoint_left.mpr fun j hj hj' ↦
        (Finset.mem_erase.mp hj').1 (Finset.mem_singleton.mp hj))
      (fun _ j ↦ -(x j)) m ?_
    show (1 : A) - N = 1 + ∑ p ∈ ({j₀} : Finset κ) ×ˢ
      Finset.univ.erase j₀, L.wordS (C.word p.1) * -(x p.2) *
        L.wordT (C.word p.2)
    -- `sum_map` leaves the `Prod.mk j₀` embedding applied, so the summand
    -- is not yet in the shape `sum_neg_distrib` matches.
    rw [Finset.singleton_product, Finset.sum_map, hN]
    -- `sum_map` leaves the `Prod.mk j₀` embedding applied; then pull the
    -- sign out of each summand so the sum itself can be negated.
    simp only [Function.Embedding.coeFn_mk, mul_neg, neg_mul,
      Finset.sum_neg_distrib]
    abel
  -- the atom column of the value
  have hpE0 : (L.pencilEntry (k := k) 0 0 0 0 0 : A) = 0 := by
    unfold pencilEntry
    simp
  have hcol : (u : A) * L.wordS (C.word j₀) =
      L.wordS (R.word i₁) * L.t 0 + L.wordS (R.word i₂) * L.t 1 := by
    rw [hu, L.pencilVal_mul_wordS R C _ j₀,
      ← Finset.add_sum_erase _ _ (Finset.mem_univ i₂),
      ← Finset.add_sum_erase _ _
        (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ i₁⟩)]
    have hzero : ∑ i ∈ (Finset.univ.erase i₂).erase i₁,
        L.wordS (R.word i) * L.pencilEntry (k := k) (A₀ i j₀)
          (A₁ i j₀) (Cm i j₀) (B₀ i j₀) (B₁ i j₀) = 0 := by
      refine Finset.sum_eq_zero fun i hi ↦ ?_
      have hi1 : i ≠ i₁ := (Finset.mem_erase.mp hi).1
      have hi2 : i ≠ i₂ :=
        (Finset.mem_erase.mp (Finset.mem_of_mem_erase hi)).1
      rw [hA₀ i, hA₁ i, hC0 i, hB₀0 i, hB₁0 i, if_neg hi1,
        if_neg hi2, hpE0, mul_zero]
    rw [hzero, add_zero, hA₀ i₂, hA₁ i₂, hC0 i₂, hB₀0 i₂, hB₁0 i₂,
      if_neg (Ne.symm hne), if_pos rfl, hA₀ i₁, hA₁ i₁, hC0 i₁,
      hB₀0 i₁, hB₁0 i₁, if_pos rfl, if_neg hne]
    unfold pencilEntry
    simp only [one_smul, zero_smul, add_zero, zero_add]
    abel
  -- the subtracted correction
  have hK : (u : A) * N = ∑ j ∈ Finset.univ.erase j₀,
      (L.wordS (R.word i₁) * L.pencilEntry (k := k) (A₀ i₁ j)
          (A₁ i₁ j) (Cm i₁ j) (B₀ i₁ j) (B₁ i₁ j) *
        L.wordT (C.word j) +
       L.wordS (R.word i₂) * L.pencilEntry (k := k) (A₀ i₂ j)
          (A₁ i₂ j) (Cm i₂ j) (B₀ i₂ j) (B₁ i₂ j) *
        L.wordT (C.word j)) := by
    rw [hN, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [show (u : A) * (L.wordS (C.word j₀) * x j *
        L.wordT (C.word j)) =
      ((u : A) * L.wordS (C.word j₀)) * x j * L.wordT (C.word j)
        from by noncomm_ring, hcol, hx]
    beta_reduce
    rw [add_mul, mul_assoc (L.wordS (R.word i₁)),
      mul_assoc (L.wordS (R.word i₂)), L.t_zero_collapse,
      L.t_one_collapse, add_mul]
  -- the value of the moved unit
  refine ⟨u * m, ?_, ?_⟩
  · rw [Units.val_mul]
    show (u : A) * (1 - N) = _
    rw [mul_sub, mul_one, hK, sub_eq_iff_eq_add, hu]
    -- expand both double sums by the two distinguished rows
    have hrest : ∀ i : ι, i ≠ i₁ → i ≠ i₂ →
        (∑ j, L.wordS (R.word i) * L.pencilEntry (k := k)
          (if j ≠ j₀ ∧ (i = i₁ ∨ i = i₂) then 0 else A₀ i j)
          (if j ≠ j₀ ∧ (i = i₁ ∨ i = i₂) then 0 else A₁ i j)
          (if j ≠ j₀ ∧ (i = i₁ ∨ i = i₂) then 0 else Cm i j)
          (if j ≠ j₀ ∧ (i = i₁ ∨ i = i₂) then 0 else B₀ i j)
          (if j ≠ j₀ ∧ (i = i₁ ∨ i = i₂) then 0 else B₁ i j) *
          L.wordT (C.word j)) =
        ∑ j, L.wordS (R.word i) * L.pencilEntry (k := k) (A₀ i j)
          (A₁ i j) (Cm i j) (B₀ i j) (B₁ i j) *
          L.wordT (C.word j) := by
      intro i hi1 hi2
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      have hcond : ¬(j ≠ j₀ ∧ (i = i₁ ∨ i = i₂)) :=
        fun h ↦ h.2.elim hi1 hi2
      rw [if_neg hcond, if_neg hcond, if_neg hcond, if_neg hcond,
        if_neg hcond]
    have hatomrow : ∀ i0 : ι, i0 = i₁ ∨ i0 = i₂ →
        (∑ j, L.wordS (R.word i0) * L.pencilEntry (k := k)
          (if j ≠ j₀ ∧ (i0 = i₁ ∨ i0 = i₂) then 0 else A₀ i0 j)
          (if j ≠ j₀ ∧ (i0 = i₁ ∨ i0 = i₂) then 0 else A₁ i0 j)
          (if j ≠ j₀ ∧ (i0 = i₁ ∨ i0 = i₂) then 0 else Cm i0 j)
          (if j ≠ j₀ ∧ (i0 = i₁ ∨ i0 = i₂) then 0 else B₀ i0 j)
          (if j ≠ j₀ ∧ (i0 = i₁ ∨ i0 = i₂) then 0 else B₁ i0 j) *
          L.wordT (C.word j)) =
        L.wordS (R.word i0) * L.pencilEntry (k := k) (A₀ i0 j₀)
          (A₁ i0 j₀) (Cm i0 j₀) (B₀ i0 j₀) (B₁ i0 j₀) *
          L.wordT (C.word j₀) := by
      intro i0 hor
      have hcond : ¬(j₀ ≠ j₀ ∧ (i0 = i₁ ∨ i0 = i₂)) := fun h ↦
        h.1 rfl
      calc (∑ j, L.wordS (R.word i0) * L.pencilEntry (k := k)
            (if j ≠ j₀ ∧ (i0 = i₁ ∨ i0 = i₂) then 0 else A₀ i0 j)
            (if j ≠ j₀ ∧ (i0 = i₁ ∨ i0 = i₂) then 0 else A₁ i0 j)
            (if j ≠ j₀ ∧ (i0 = i₁ ∨ i0 = i₂) then 0 else Cm i0 j)
            (if j ≠ j₀ ∧ (i0 = i₁ ∨ i0 = i₂) then 0 else B₀ i0 j)
            (if j ≠ j₀ ∧ (i0 = i₁ ∨ i0 = i₂) then 0 else B₁ i0 j) *
            L.wordT (C.word j))
          = L.wordS (R.word i0) * L.pencilEntry (k := k)
              (if j₀ ≠ j₀ ∧ (i0 = i₁ ∨ i0 = i₂) then 0 else A₀ i0 j₀)
              (if j₀ ≠ j₀ ∧ (i0 = i₁ ∨ i0 = i₂) then 0 else A₁ i0 j₀)
              (if j₀ ≠ j₀ ∧ (i0 = i₁ ∨ i0 = i₂) then 0 else Cm i0 j₀)
              (if j₀ ≠ j₀ ∧ (i0 = i₁ ∨ i0 = i₂) then 0 else B₀ i0 j₀)
              (if j₀ ≠ j₀ ∧ (i0 = i₁ ∨ i0 = i₂) then 0 else B₁ i0 j₀) *
              L.wordT (C.word j₀) := by
            refine Finset.sum_eq_single j₀ (fun j _ hj ↦ ?_)
              (fun h ↦ absurd (Finset.mem_univ j₀) h)
            rw [if_pos ⟨hj, hor⟩, if_pos ⟨hj, hor⟩, if_pos ⟨hj, hor⟩,
              if_pos ⟨hj, hor⟩, if_pos ⟨hj, hor⟩, hpE0, mul_zero,
              zero_mul]
        _ = L.wordS (R.word i0) * L.pencilEntry (k := k) (A₀ i0 j₀)
              (A₁ i0 j₀) (Cm i0 j₀) (B₀ i0 j₀) (B₁ i0 j₀) *
              L.wordT (C.word j₀) := by
            rw [if_neg hcond, if_neg hcond, if_neg hcond,
              if_neg hcond, if_neg hcond]
    -- split both sides at the distinguished rows and the column `j₀`
    rw [← Finset.add_sum_erase _ (fun i ↦ ∑ j, L.wordS (R.word i) *
        L.pencilEntry (k := k) (A₀ i j) (A₁ i j) (Cm i j) (B₀ i j)
          (B₁ i j) * L.wordT (C.word j)) (Finset.mem_univ i₂),
      ← Finset.add_sum_erase _ (fun i ↦ ∑ j, L.wordS (R.word i) *
        L.pencilEntry (k := k) (A₀ i j) (A₁ i j) (Cm i j) (B₀ i j)
          (B₁ i j) * L.wordT (C.word j))
        (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ i₁⟩),
      ← Finset.add_sum_erase _ (fun j ↦ L.wordS (R.word i₂) *
        L.pencilEntry (k := k) (A₀ i₂ j) (A₁ i₂ j) (Cm i₂ j)
          (B₀ i₂ j) (B₁ i₂ j) * L.wordT (C.word j))
        (Finset.mem_univ j₀),
      ← Finset.add_sum_erase _ (fun j ↦ L.wordS (R.word i₁) *
        L.pencilEntry (k := k) (A₀ i₁ j) (A₁ i₁ j) (Cm i₁ j)
          (B₀ i₁ j) (B₁ i₁ j) * L.wordT (C.word j))
        (Finset.mem_univ j₀),
      ← Finset.add_sum_erase _ (fun i ↦ ∑ j, L.wordS (R.word i) *
        L.pencilEntry (k := k)
          (if j ≠ j₀ ∧ (i = i₁ ∨ i = i₂) then 0 else A₀ i j)
          (if j ≠ j₀ ∧ (i = i₁ ∨ i = i₂) then 0 else A₁ i j)
          (if j ≠ j₀ ∧ (i = i₁ ∨ i = i₂) then 0 else Cm i j)
          (if j ≠ j₀ ∧ (i = i₁ ∨ i = i₂) then 0 else B₀ i j)
          (if j ≠ j₀ ∧ (i = i₁ ∨ i = i₂) then 0 else B₁ i j) *
        L.wordT (C.word j)) (Finset.mem_univ i₂),
      ← Finset.add_sum_erase _ (fun i ↦ ∑ j, L.wordS (R.word i) *
        L.pencilEntry (k := k)
          (if j ≠ j₀ ∧ (i = i₁ ∨ i = i₂) then 0 else A₀ i j)
          (if j ≠ j₀ ∧ (i = i₁ ∨ i = i₂) then 0 else A₁ i j)
          (if j ≠ j₀ ∧ (i = i₁ ∨ i = i₂) then 0 else Cm i j)
          (if j ≠ j₀ ∧ (i = i₁ ∨ i = i₂) then 0 else B₀ i j)
          (if j ≠ j₀ ∧ (i = i₁ ∨ i = i₂) then 0 else B₁ i j) *
        L.wordT (C.word j))
        (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ i₁⟩),
      hatomrow i₂ (Or.inr rfl), hatomrow i₁ (Or.inl rfl),
      show (∑ i ∈ (Finset.univ.erase i₂).erase i₁, ∑ j,
          L.wordS (R.word i) * L.pencilEntry (k := k)
            (if j ≠ j₀ ∧ (i = i₁ ∨ i = i₂) then 0 else A₀ i j)
            (if j ≠ j₀ ∧ (i = i₁ ∨ i = i₂) then 0 else A₁ i j)
            (if j ≠ j₀ ∧ (i = i₁ ∨ i = i₂) then 0 else Cm i j)
            (if j ≠ j₀ ∧ (i = i₁ ∨ i = i₂) then 0 else B₀ i j)
            (if j ≠ j₀ ∧ (i = i₁ ∨ i = i₂) then 0 else B₁ i j) *
          L.wordT (C.word j)) =
        ∑ i ∈ (Finset.univ.erase i₂).erase i₁, ∑ j,
          L.wordS (R.word i) * L.pencilEntry (k := k) (A₀ i j)
            (A₁ i j) (Cm i j) (B₀ i j) (B₁ i j) *
          L.wordT (C.word j) from
        Finset.sum_congr rfl fun i hi ↦ hrest i
          (Finset.mem_erase.mp hi).1
          (Finset.mem_erase.mp (Finset.mem_of_mem_erase hi)).1,
      Finset.sum_add_distrib]
    abel
  · constructor
    · intro hH
      exact mul_mem hH hmmem
    · intro hH
      rw [show u = (u * m) * m⁻¹ from by group]
      exact mul_mem hH (inv_mem hmmem)

end LeavittFamily
end NonsoficGroupsExist
