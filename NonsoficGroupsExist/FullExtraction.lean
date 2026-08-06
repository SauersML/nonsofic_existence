import NonsoficGroupsExist.RowClearMove
import NonsoficGroupsExist.AtomPeel
import NonsoficGroupsExist.GLVectorNormalization
import NonsoficGroupsExist.CompleteCodeSupply

/-!
# The full extraction step

Composition of the normalization toolkit: a kernel vector of the
scalar stack `[B₀; B₁; C]` of a pencil unit yields, after a right
scalar move (kernel vector into a coordinate column), the
independence of the resulting `t`-pair (forced by left invertibility
of the unit's column against the shift rigidity), a left scalar move
(the pair onto standard atoms), the row-clearing block unipotent, and
the atom peel — a pencil unit over one fewer row whose class-group
membership is equivalent.  This is the size-reduction engine of the
master induction.
-/

namespace NonsoficGroupsExist
namespace LeavittFamily

open MatrixDiagonalization

variable {A : Type*} [Ring A] (L : LeavittFamily A)
variable {k : Type*} [Field k] [Algebra k A]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
variable [Fintype κ] [DecidableEq κ]

/-- The pure-`t` pencil entry. -/
theorem pencilEntry_t (a b : k) :
    (L.pencilEntry (k := k) a b 0 0 0 : A) = a • L.t 0 + b • L.t 1 := by
  unfold pencilEntry
  simp

omit [DecidableEq ι] in
/-- Factoring a proportional `t`-column. -/
theorem t_column_factor (R : BinaryPrefixCode ι) (c : ι → k)
    (lam₀ lam₁ : k) :
    (∑ i, L.wordS (R.word i) *
      ((c i * lam₀) • L.t 0 + (c i * lam₁) • L.t 1)) =
    (∑ i, c i • L.wordS (R.word i)) *
      (lam₀ • L.t 0 + lam₁ • L.t 1) := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  -- `smul_add`/`smul_smul` land exactly on the left-hand side; the two
  -- `mul_comm` pairs in the original chain simply undid each other.
  rw [smul_mul_assoc]
  simp only [mul_add, mul_smul_comm, smul_add, smul_smul]

omit [DecidableEq κ] in
/-- **The full extraction step.** -/
theorem full_extraction [Nontrivial A]
    (hdiv : ∀ x : A, x ≠ 0 → ∃ p q : A, p * x * q = 1)
    (R : BinaryPrefixCode ι) (hR : L.IsComplete R)
    (C : BinaryPrefixCode κ) (hC : L.IsComplete C)
    (A₀ A₁ Cm B₀ B₁ : ι → κ → k) (u : Aˣ)
    (hu : (u : A) = ∑ i, ∑ j, L.wordS (R.word i) *
      L.pencilEntry (k := k) (A₀ i j) (A₁ i j) (Cm i j) (B₀ i j)
        (B₁ i j) * L.wordT (C.word j))
    (v₀ : κ → k) (hv₀ : v₀ ≠ 0)
    (hkB₀ : ∀ i, ∑ j, B₀ i j * v₀ j = 0)
    (hkB₁ : ∀ i, ∑ j, B₁ i j * v₀ j = 0)
    (hkC : ∀ i, ∑ j, Cm i j * v₀ j = 0) :
    ∃ (i₂ : ι) (D : {i : ι // i ≠ i₂} → List (Fin 2))
      (A₀' A₁' Cm' B₀' B₁' : {i : ι // i ≠ i₂} → κ → k) (u₂ : Aˣ),
      (∀ ⦃p q : {i : ι // i ≠ i₂}⦄, p ≠ q → ¬D p <+: D q) ∧
      (∑ p, L.cylinder (D p) = 1) ∧
      ((u₂ : A) = ∑ p : {i : ι // i ≠ i₂}, ∑ j,
        L.wordS (D p) * L.pencilEntry (k := k) (A₀' p j) (A₁' p j)
          (Cm' p j) (B₀' p j) (B₁' p j) * L.wordT (C.word j)) ∧
      (u ∈ stableUnits A ↔ u₂ ∈ stableUnits A) := by
  classical
  -- choose the pivot column
  obtain ⟨j₀, -⟩ := Function.ne_iff.mp hv₀
  -- STEP 1: right scalar move putting `v₀` into column `j₀`
  obtain ⟨G, hGu, hGcol⟩ := exists_isUnit_matrix_col hv₀ j₀
  have hGent : ∀ l, G l j₀ = v₀ l := by
    intro l
    have h := congrFun hGcol l
    -- `mulVec_single` leaves an `op 1 •`; reduce it and the `col` projection
    simp only [Matrix.mulVec_single, MulOpposite.op_one, one_smul,
      Matrix.col_apply] at h
    exact h
  -- destructure a copy: a bare `obtain … := hGu` clears `hGu`, which is
  -- still needed by `codeScalar_unit_mem` below.
  obtain ⟨Gm, hGm⟩ := id hGu
  set uG : Aˣ := ⟨L.codeScalar (k := k) C G,
    L.codeScalar (k := k) C ((Gm⁻¹ : (Matrix κ κ k)ˣ) : Matrix κ κ k),
    by rw [L.codeScalar_mul, ← hGm, Units.mul_inv,
      L.codeScalar_one C hC],
    by rw [L.codeScalar_mul, ← hGm, Units.inv_mul,
      L.codeScalar_one C hC]⟩ with huG
  have huGmem : uG ∈ stableUnits A :=
    L.codeScalar_unit_mem hdiv C hC G hGu uG rfl
  set u1 : Aˣ := u * uG with hu1def
  have hu1 : (u1 : A) = ∑ i, ∑ j, L.wordS (R.word i) *
      L.pencilEntry (k := k) (∑ l, A₀ i l * G l j)
        (∑ l, A₁ i l * G l j) (∑ l, Cm i l * G l j)
        (∑ l, B₀ i l * G l j) (∑ l, B₁ i l * G l j) *
      L.wordT (C.word j) := by
    rw [Units.val_mul, hu]
    exact L.pencilVal_mul_codeScalar R C A₀ A₁ Cm B₀ B₁ G
  -- the new `j₀`-column data
  set a : ι → k := fun i ↦ ∑ l, A₀ i l * v₀ l with ha
  set b : ι → k := fun i ↦ ∑ l, A₁ i l * v₀ l with hb
  have hcolA₀ : ∀ i, (∑ l, A₀ i l * G l j₀) = a i := fun i ↦
    Finset.sum_congr rfl fun l _ ↦ by rw [hGent l]
  have hcolA₁ : ∀ i, (∑ l, A₁ i l * G l j₀) = b i := fun i ↦
    Finset.sum_congr rfl fun l _ ↦ by rw [hGent l]
  have hcolC : ∀ i, (∑ l, Cm i l * G l j₀) = 0 := fun i ↦ by
    rw [Finset.sum_congr rfl fun l _ ↦ by rw [hGent l]]
    exact hkC i
  have hcolB₀ : ∀ i, (∑ l, B₀ i l * G l j₀) = 0 := fun i ↦ by
    rw [Finset.sum_congr rfl fun l _ ↦ by rw [hGent l]]
    exact hkB₀ i
  have hcolB₁ : ∀ i, (∑ l, B₁ i l * G l j₀) = 0 := fun i ↦ by
    rw [Finset.sum_congr rfl fun l _ ↦ by rw [hGent l]]
    exact hkB₁ i
  -- STEP 2: independence of the `t`-pair from left invertibility
  have hab : LinearIndependent k ![a, b] := by
    rw [LinearIndependent.pair_iff]
    by_contra hdep
    push Not at hdep
    obtain ⟨s, t, hst, hne0⟩ := hdep
    -- the column of the unit is left invertible
    have hqcol : (u1 : A) * L.wordS (C.word j₀) =
        ∑ i, L.wordS (R.word i) *
          L.pencilEntry (k := k) (a i) (b i) 0 0 0 := by
      rw [hu1, L.pencilVal_mul_wordS R C _ j₀]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [hcolA₀ i, hcolA₁ i, hcolC i, hcolB₀ i, hcolB₁ i]
    have hleft : (L.wordT (C.word j₀) * ((u1⁻¹ : Aˣ) : A)) *
        ((u1 : A) * L.wordS (C.word j₀)) = 1 := by
      calc (L.wordT (C.word j₀) * ((u1⁻¹ : Aˣ) : A)) *
            ((u1 : A) * L.wordS (C.word j₀))
          = L.wordT (C.word j₀) *
            (((u1⁻¹ : Aˣ) : A) * (u1 : A)) *
            L.wordS (C.word j₀) := by noncomm_ring
        _ = 1 := by
            rw [Units.inv_mul, mul_one, L.wordT_mul_wordS_self]
    -- express the column as a proportional `t`-column
    rcases (em (t = 0)) with ht | ht
    · -- `t = 0`, so `s ≠ 0` and `a = 0`
      have hs : s ≠ 0 := fun h ↦ hne0 h ht
      have ha0 : a = 0 := by
        have h1 : s • a = 0 := by
          have := hst
          rw [ht, zero_smul, add_zero] at this
          exact this
        rcases smul_eq_zero.mp h1 with h | h
        · exact absurd h hs
        · exact h
      have hfac : (u1 : A) * L.wordS (C.word j₀) =
          (∑ i, b i • L.wordS (R.word i)) *
            ((0 : k) • L.t 0 + (1 : k) • L.t 1) := by
        rw [hqcol, ← L.t_column_factor R b 0 1]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [L.pencilEntry_t, ha0]
        simp
      exact L.t_combo_not_left_invertible (k := k)
        (Or.inr one_ne_zero)
        ((L.wordT (C.word j₀) * ((u1⁻¹ : Aˣ) : A)) *
          (∑ i, b i • L.wordS (R.word i)))
        (by rw [mul_assoc, ← hfac]; exact hleft)
    · -- `t ≠ 0`, so `b` is proportional to `a`
      have hbval : b = (-(t⁻¹ * s)) • a := by
        have h1 : t • b = -(s • a) := by
          rw [eq_neg_iff_add_eq_zero, add_comm]
          exact hst
        have h2 : b = t⁻¹ • (t • b) := by
          rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
        rw [h2, h1, smul_neg, smul_smul, ← neg_smul]
      have hfac : (u1 : A) * L.wordS (C.word j₀) =
          (∑ i, a i • L.wordS (R.word i)) *
            ((1 : k) • L.t 0 + (-(t⁻¹ * s)) • L.t 1) := by
        rw [hqcol, ← L.t_column_factor R a 1 (-(t⁻¹ * s))]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [L.pencilEntry_t, hbval, mul_one]
        congr 1
        rw [Pi.smul_apply, smul_eq_mul, mul_comm]
      exact L.t_combo_not_left_invertible (k := k)
        (Or.inl one_ne_zero)
        ((L.wordT (C.word j₀) * ((u1⁻¹ : Aˣ) : A)) *
          (∑ i, a i • L.wordS (R.word i)))
        (by rw [mul_assoc, ← hfac]; exact hleft)
  -- two distinct rows
  have hcard : 1 < Fintype.card ι := by
    have h1 := hab.fintype_card_le_finrank
    rw [Module.finrank_pi] at h1
    -- `1 < n` and `2 ≤ n` agree definitionally but `simpa`'s closing match
    -- is syntactic, so name the simplified form and finish arithmetically.
    have h2 : 2 ≤ Fintype.card ι := by simpa using h1
    omega
  obtain ⟨i₁', i₂', hne'⟩ := Fintype.exists_pair_of_one_lt_card hcard
  -- STEP 3: left scalar move putting the pair onto standard atoms
  obtain ⟨G', hG'u, hG'a, hG'b⟩ :=
    exists_isUnit_matrix_mulVec_pair hab i₁' i₂' hne'
  have hG'aent : ∀ i, (∑ l, G' i l * a l) =
      if i = i₁' then 1 else 0 := by
    intro i
    have h := congrFun hG'a i
    rw [Pi.single_apply] at h
    exact h
  have hG'bent : ∀ i, (∑ l, G' i l * b l) =
      if i = i₂' then 1 else 0 := by
    intro i
    have h := congrFun hG'b i
    rw [Pi.single_apply] at h
    exact h
  -- copy again: `hG'u` is still needed by `codeScalar_unit_mem` below
  obtain ⟨G'm, hG'm⟩ := id hG'u
  set uG' : Aˣ := ⟨L.codeScalar (k := k) R G',
    L.codeScalar (k := k) R
      ((G'm⁻¹ : (Matrix ι ι k)ˣ) : Matrix ι ι k),
    by rw [L.codeScalar_mul, ← hG'm, Units.mul_inv,
      L.codeScalar_one R hR],
    by rw [L.codeScalar_mul, ← hG'm, Units.inv_mul,
      L.codeScalar_one R hR]⟩ with huG'
  have huG'mem : uG' ∈ stableUnits A :=
    L.codeScalar_unit_mem hdiv R hR G' hG'u uG' rfl
  set u2 : Aˣ := uG' * u1 with hu2def
  have hu2 : (u2 : A) = ∑ i, ∑ j, L.wordS (R.word i) *
      L.pencilEntry (k := k)
        (∑ l, G' i l * ∑ l', A₀ l l' * G l' j)
        (∑ l, G' i l * ∑ l', A₁ l l' * G l' j)
        (∑ l, G' i l * ∑ l', Cm l l' * G l' j)
        (∑ l, G' i l * ∑ l', B₀ l l' * G l' j)
        (∑ l, G' i l * ∑ l', B₁ l l' * G l' j) *
      L.wordT (C.word j) := by
    rw [Units.val_mul, hu1]
    have h := L.codeScalar_mul_pencilVal R C
      (fun l j ↦ ∑ l', A₀ l l' * G l' j)
      (fun l j ↦ ∑ l', A₁ l l' * G l' j)
      (fun l j ↦ ∑ l', Cm l l' * G l' j)
      (fun l j ↦ ∑ l', B₀ l l' * G l' j)
      (fun l j ↦ ∑ l', B₁ l l' * G l' j) G'
    beta_reduce at h
    exact h
  -- the `j₀`-column of the moved data
  have hc2A₀ : ∀ i, (∑ l, G' i l * ∑ l', A₀ l l' * G l' j₀) =
      if i = i₁' then 1 else 0 := by
    intro i
    rw [Finset.sum_congr rfl fun l _ ↦ by rw [hcolA₀ l]]
    exact hG'aent i
  have hc2A₁ : ∀ i, (∑ l, G' i l * ∑ l', A₁ l l' * G l' j₀) =
      if i = i₂' then 1 else 0 := by
    intro i
    rw [Finset.sum_congr rfl fun l _ ↦ by rw [hcolA₁ l]]
    exact hG'bent i
  have hc2C : ∀ i, (∑ l, G' i l * ∑ l', Cm l l' * G l' j₀) = 0 := by
    intro i
    rw [Finset.sum_congr rfl fun l _ ↦ by rw [hcolC l, mul_zero]]
    exact Finset.sum_const_zero
  have hc2B₀ : ∀ i, (∑ l, G' i l * ∑ l', B₀ l l' * G l' j₀) = 0 := by
    intro i
    rw [Finset.sum_congr rfl fun l _ ↦ by rw [hcolB₀ l, mul_zero]]
    exact Finset.sum_const_zero
  have hc2B₁ : ∀ i, (∑ l, G' i l * ∑ l', B₁ l l' * G l' j₀) = 0 := by
    intro i
    rw [Finset.sum_congr rfl fun l _ ↦ by rw [hcolB₁ l, mul_zero]]
    exact Finset.sum_const_zero
  -- STEP 4: clear the atom rows
  obtain ⟨u3, hu3, hiff3⟩ := L.row_clear R C
    (fun i j ↦ ∑ l, G' i l * ∑ l', A₀ l l' * G l' j)
    (fun i j ↦ ∑ l, G' i l * ∑ l', A₁ l l' * G l' j)
    (fun i j ↦ ∑ l, G' i l * ∑ l', Cm l l' * G l' j)
    (fun i j ↦ ∑ l, G' i l * ∑ l', B₀ l l' * G l' j)
    (fun i j ↦ ∑ l, G' i l * ∑ l', B₁ l l' * G l' j)
    u2 (by exact hu2) i₁' i₂' hne' j₀
    (by exact hc2A₀) (by exact hc2A₁)
    (by exact hc2C) (by exact hc2B₀)
    (by exact hc2B₁)
  -- STEP 5: peel the atom
  haveI : Nonempty {i : ι // i ≠ i₂'} := ⟨⟨i₁', hne'⟩⟩
  obtain ⟨D, hDfree, hDsum⟩ :=
    L.exists_complete_family_of_nonempty {i : ι // i ≠ i₂'}
  -- the cleared entries, in raw form
  set Ecl : ι → κ → A := fun i j ↦ L.pencilEntry (k := k)
    (if j ≠ j₀ ∧ (i = i₁' ∨ i = i₂') then 0
      else ∑ l, G' i l * ∑ l', A₀ l l' * G l' j)
    (if j ≠ j₀ ∧ (i = i₁' ∨ i = i₂') then 0
      else ∑ l, G' i l * ∑ l', A₁ l l' * G l' j)
    (if j ≠ j₀ ∧ (i = i₁' ∨ i = i₂') then 0
      else ∑ l, G' i l * ∑ l', Cm l l' * G l' j)
    (if j ≠ j₀ ∧ (i = i₁' ∨ i = i₂') then 0
      else ∑ l, G' i l * ∑ l', B₀ l l' * G l' j)
    (if j ≠ j₀ ∧ (i = i₁' ∨ i = i₂') then 0
      else ∑ l, G' i l * ∑ l', B₁ l l' * G l' j) with hEcl
  have hpE0' : (L.pencilEntry (k := k) 0 0 0 0 0 : A) = 0 := by
    unfold pencilEntry
    simp
  have hE1 : Ecl i₁' j₀ = L.t 0 := by
    rw [hEcl]
    beta_reduce
    have hcond : ¬(j₀ ≠ j₀ ∧ (i₁' = i₁' ∨ i₁' = i₂')) := fun h ↦
      h.1 rfl
    rw [if_neg hcond, if_neg hcond, if_neg hcond, if_neg hcond,
      if_neg hcond, hc2A₀ i₁', hc2A₁ i₁', hc2C i₁', hc2B₀ i₁',
      hc2B₁ i₁', if_pos rfl, if_neg hne', L.pencilEntry_t]
    simp
  have hE2 : Ecl i₂' j₀ = L.t 1 := by
    rw [hEcl]
    beta_reduce
    have hcond : ¬(j₀ ≠ j₀ ∧ (i₂' = i₁' ∨ i₂' = i₂')) := fun h ↦
      h.1 rfl
    rw [if_neg hcond, if_neg hcond, if_neg hcond, if_neg hcond,
      if_neg hcond, hc2A₀ i₂', hc2A₁ i₂', hc2C i₂', hc2B₀ i₂',
      hc2B₁ i₂', if_neg (Ne.symm hne'), if_pos rfl, L.pencilEntry_t]
    simp
  have hE4 : ∀ j, j ≠ j₀ → Ecl i₁' j = 0 := by
    intro j hj
    rw [hEcl]
    beta_reduce
    have hcond : j ≠ j₀ ∧ (i₁' = i₁' ∨ i₁' = i₂') := ⟨hj, Or.inl rfl⟩
    rw [if_pos hcond, if_pos hcond, if_pos hcond, if_pos hcond,
      if_pos hcond]
    exact hpE0'
  have hE5 : ∀ j, j ≠ j₀ → Ecl i₂' j = 0 := by
    intro j hj
    rw [hEcl]
    beta_reduce
    have hcond : j ≠ j₀ ∧ (i₂' = i₁' ∨ i₂' = i₂') := ⟨hj, Or.inr rfl⟩
    rw [if_pos hcond, if_pos hcond, if_pos hcond, if_pos hcond,
      if_pos hcond]
    exact hpE0'
  obtain ⟨u₄, hu₄val, hiff₄⟩ := L.atom_peel (k := k) hdiv R hR C Ecl u3
    (by rw [hu3, hEcl]) i₁' i₂' hne' j₀ hE1 hE2 hE4 hE5 D hDfree
    hDsum
  -- the residual value as pencil data
  refine ⟨i₂', D,
    (fun p j ↦ if p.1 = i₁' then 0 else
      (if j ≠ j₀ ∧ (p.1 = i₁' ∨ p.1 = i₂') then 0
        else ∑ l, G' p.1 l * ∑ l', A₀ l l' * G l' j)),
    (fun p j ↦ if p.1 = i₁' then 0 else
      (if j ≠ j₀ ∧ (p.1 = i₁' ∨ p.1 = i₂') then 0
        else ∑ l, G' p.1 l * ∑ l', A₁ l l' * G l' j)),
    (fun p j ↦ if p.1 = i₁' then (if j = j₀ then 1 else 0) else
      (if j ≠ j₀ ∧ (p.1 = i₁' ∨ p.1 = i₂') then 0
        else ∑ l, G' p.1 l * ∑ l', Cm l l' * G l' j)),
    (fun p j ↦ if p.1 = i₁' then 0 else
      (if j ≠ j₀ ∧ (p.1 = i₁' ∨ p.1 = i₂') then 0
        else ∑ l, G' p.1 l * ∑ l', B₀ l l' * G l' j)),
    (fun p j ↦ if p.1 = i₁' then 0 else
      (if j ≠ j₀ ∧ (p.1 = i₁' ∨ p.1 = i₂') then 0
        else ∑ l, G' p.1 l * ∑ l', B₁ l l' * G l' j)),
    u₄, hDfree, hDsum, ?_, ?_⟩
  · rw [hu₄val]
    refine Finset.sum_congr rfl fun p _ ↦
      Finset.sum_congr rfl fun j _ ↦ ?_
    beta_reduce
    congr 1
    congr 1
    by_cases hp : p.1 = i₁'
    · rw [if_pos hp, if_pos hp, if_pos hp, if_pos hp, if_pos hp,
        if_pos hp]
      unfold pencilEntry
      by_cases hj : j = j₀
      · rw [if_pos hj, if_pos hj]
        simp
      · rw [if_neg hj, if_neg hj]
        simp
    · rw [if_neg hp, if_neg hp, if_neg hp, if_neg hp, if_neg hp,
        if_neg hp, hEcl]
  · calc u ∈ stableUnits A
        ↔ u1 ∈ stableUnits A := by
          constructor
          · intro h
            exact mul_mem h huGmem
          · intro h
            rw [show u = u1 * uG⁻¹ from by rw [hu1def]; group]
            exact mul_mem h (inv_mem huGmem)
      _ ↔ u2 ∈ stableUnits A := by
          constructor
          · intro h
            exact mul_mem huG'mem h
          · intro h
            rw [show u1 = uG'⁻¹ * u2 from by rw [hu2def]; group]
            exact mul_mem (inv_mem huG'mem) h
      _ ↔ u3 ∈ stableUnits A := hiff3
      _ ↔ u₄ ∈ stableUnits A := hiff₄

end LeavittFamily
end NonsoficGroupsExist
