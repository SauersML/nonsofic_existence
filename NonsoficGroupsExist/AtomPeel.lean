import NonsoficGroupsExist.CodeChangeGlue

/-!
# The atom peel

A pencil-transported unit whose distinguished column is the shift atom
`[t₀; t₁]` — entries `t₀, t₁` at two distinguished rows, zero
elsewhere, with the two rows vanishing outside that column — factors
as a code-change unit times a pencil unit over one fewer row: the
code change re-pairs the row code with the *split* of an intermediate
code `D`, absorbing the atom, and the residual unit `u₂ := u₁⁻¹ · u`
carries the untouched middle block together with a single scalar
pivot.  This is the size-reduction step of the elimination.
-/

namespace NonsoficGroupsExist
namespace LeavittFamily

open MatrixDiagonalization

variable {A : Type*} [Ring A] (L : LeavittFamily A)
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
variable [Fintype κ] [DecidableEq κ]

/-- Collapse of a diagonal code pair to the plain bijection sum. -/
theorem codeDelta_collapse (τ σ : ι → List (Fin 2)) :
    (∑ i, ∑ j, L.wordS (τ i) *
      (if i = j then (1 : A) else 0) * L.wordT (σ j)) =
    ∑ i, L.wordS (τ i) * L.wordT (σ i) := by
  classical
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  calc ∑ j, L.wordS (τ i) * (if i = j then (1 : A) else 0) *
        L.wordT (σ j)
      = ∑ j, (if i = j then L.wordS (τ i) * L.wordT (σ j) else 0) := by
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        split_ifs with h
        · rw [mul_one]
        · rw [mul_zero, zero_mul]
    _ = L.wordS (τ i) * L.wordT (σ i) := by
        rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ i)]

/-- **The atom peel.**  If the pencil data of `u` over `(R, C)` has a
`[t₀; t₁]`-column at `(i₁, i₂; j₀)` and the rows `i₁, i₂` vanish
elsewhere, then along any complete code `D` on the remaining rows
there are a code-change unit `u₁ ∈ H` and a unit `u₂` with
`u = u₁ * u₂`, where `u₂` is the pencil transport over
`(D, C)` of the residual data (the untouched block plus one scalar
pivot). -/
theorem atom_peel [Nontrivial A]
    (hdiv : ∀ x : A, x ≠ 0 → ∃ p q : A, p * x * q = 1)
    (R : BinaryPrefixCode ι) (hR : L.IsComplete R)
    (C : BinaryPrefixCode κ)
    (E : ι → κ → A) (u : Aˣ)
    (hu : (u : A) = ∑ i, ∑ j,
      L.wordS (R.word i) * E i j * L.wordT (C.word j))
    (i₁ i₂ : ι) (hne : i₁ ≠ i₂) (j₀ : κ)
    (h1 : E i₁ j₀ = L.t 0) (h2 : E i₂ j₀ = L.t 1)
    (h4 : ∀ j, j ≠ j₀ → E i₁ j = 0)
    (h5 : ∀ j, j ≠ j₀ → E i₂ j = 0)
    (D : {i : ι // i ≠ i₂} → List (Fin 2))
    (hDfree : ∀ ⦃p q : {i : ι // i ≠ i₂}⦄, p ≠ q → ¬D p <+: D q)
    (hDsum : ∑ p, L.cylinder (D p) = 1) :
    ∃ u₂ : Aˣ,
      (u₂ : A) = ∑ p : {i : ι // i ≠ i₂}, ∑ j,
        L.wordS (D p) *
          (if p.1 = i₁ then (if j = j₀ then 1 else 0) else E p.1 j) *
          L.wordT (C.word j) ∧
      (u ∈ stableUnits A ↔ u₂ ∈ stableUnits A) := by
  classical
  -- the split source family
  set d₁ : {i : ι // i ≠ i₂} := ⟨i₁, hne⟩ with hd₁
  set σ : ι → List (Fin 2) := fun i ↦
    if h : i = i₂ then D d₁ ++ [1]
    else if i = i₁ then D d₁ ++ [0] else D ⟨i, h⟩ with hσ
  -- `rw [hσ]` leaves the redex `(fun i => …) i₁` unreduced so `dif_neg`
  -- finds no `dite`, while `simp only [hσ]` beta-reduces *and* collapses the
  -- decided conditions to `True`, so the follow-up `if_pos rfl` finds no
  -- `if ?m = ?m` either.  Just let `simp` discharge each one outright.
  have hσi₁ : σ i₁ = D d₁ ++ [0] := by simp [hσ, hne]
  have hσi₂ : σ i₂ = D d₁ ++ [1] := by simp [hσ]
  have hσo : ∀ (i : ι) (h2' : i ≠ i₂), i ≠ i₁ → σ i = D ⟨i, h2'⟩ := by
    intro i h2' h1'
    simp [hσ, h2', h1']
  -- prefix-freeness of the split family
  have hσfree : ∀ ⦃i j : ι⦄, i ≠ j → ¬σ i <+: σ j := by
    intro i j hij h
    by_cases hi2 : i = i₂ <;> by_cases hj2 : j = i₂
    · exact hij (hi2.trans hj2.symm)
    · subst hi2
      rw [hσi₂] at h
      by_cases hj1 : j = i₁
      · subst hj1
        rw [hσi₁] at h
        have hlen : (D d₁ ++ [(1 : Fin 2)]).length =
            (D d₁ ++ [(0 : Fin 2)]).length := by simp
        have heq := h.eq_of_length hlen
        have := List.append_inj_right heq rfl
        simp at this
      · rw [hσo j hj2 hj1] at h
        have hpq : d₁ ≠ ⟨j, hj2⟩ := fun hh ↦
          hj1 (congrArg Subtype.val hh).symm
        -- `.2` is `¬ w ++ [z] <+: v`, so `w` must be `D d₁`: pass the
        -- hypotheses the other way round from the `.1` branches below.
        exact (incomparable_append_single (hDfree (Ne.symm hpq))
          (hDfree hpq) 1).2 h
    · subst hj2
      rw [hσi₂] at h
      by_cases hi1 : i = i₁
      · subst hi1
        rw [hσi₁] at h
        have hlen : (D d₁ ++ [(0 : Fin 2)]).length ≤
            (D d₁ ++ [(1 : Fin 2)]).length := by simp
        have heq := h.eq_of_length (by simp)
        have := List.append_inj_right heq rfl
        simp at this
      · rw [hσo i hi2 hi1] at h
        have hpq : ⟨i, hi2⟩ ≠ d₁ := fun hh ↦
          hi1 (congrArg Subtype.val hh)
        exact (incomparable_append_single (hDfree hpq)
          (hDfree (Ne.symm hpq)) 1).1 h
    · by_cases hi1 : i = i₁ <;> by_cases hj1 : j = i₁
      · exact hij (hi1.trans hj1.symm)
      · subst hi1
        rw [hσi₁, hσo j hj2 hj1] at h
        have hpq : d₁ ≠ ⟨j, hj2⟩ := fun hh ↦
          hj1 (congrArg Subtype.val hh).symm
        exact (incomparable_append_single (hDfree (Ne.symm hpq))
          (hDfree hpq) 0).2 h
      · subst hj1
        rw [hσi₁, hσo i hi2 hi1] at h
        have hpq : ⟨i, hi2⟩ ≠ d₁ := fun hh ↦
          hi1 (congrArg Subtype.val hh)
        exact (incomparable_append_single (hDfree hpq)
          (hDfree (Ne.symm hpq)) 0).1 h
      · rw [hσo i hi2 hi1, hσo j hj2 hj1] at h
        have hpq : (⟨i, hi2⟩ : {i : ι // i ≠ i₂}) ≠ ⟨j, hj2⟩ :=
          fun hh ↦ hij (congrArg Subtype.val hh)
        exact hDfree hpq h
  -- completeness of the split family
  have hσsum : ∑ i, L.cylinder (σ i) = 1 := by
    rw [← Finset.add_sum_erase _ (fun i ↦ L.cylinder (σ i))
        (Finset.mem_univ i₂),
      ← Finset.add_sum_erase _ (fun i ↦ L.cylinder (σ i))
        (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ i₁⟩)]
    have hbridge : ∑ i ∈ (Finset.univ.erase i₂).erase i₁,
        L.cylinder (σ i) =
        ∑ p ∈ Finset.univ.erase d₁, L.cylinder (D p) := by
      refine Finset.sum_bij'
        (i := fun i hi ↦ (⟨i, (Finset.mem_erase.mp
          (Finset.mem_of_mem_erase hi)).1⟩ : {i : ι // i ≠ i₂}))
        (j := fun p _ ↦ p.1) ?_ ?_ ?_ ?_ ?_
      · intro i hi
        rw [Finset.mem_erase]
        refine ⟨?_, Finset.mem_univ _⟩
        intro hh
        exact (Finset.mem_erase.mp hi).1 (congrArg Subtype.val hh)
      · intro p hp
        rw [Finset.mem_erase, Finset.mem_erase]
        refine ⟨?_, p.2, Finset.mem_univ _⟩
        intro hh
        exact (Finset.mem_erase.mp hp).1 (Subtype.ext hh)
      · intro i _
        rfl
      · intro p _
        rfl
      · intro i hi
        rw [hσo i (Finset.mem_erase.mp
          (Finset.mem_of_mem_erase hi)).1
          (Finset.mem_erase.mp hi).1]
    rw [hbridge, hσi₂, hσi₁]
    have hsplit := L.cylinder_split (D d₁)
    calc L.cylinder (D d₁ ++ [1]) + (L.cylinder (D d₁ ++ [0]) +
          ∑ p ∈ Finset.univ.erase d₁, L.cylinder (D p))
        = L.cylinder (D d₁) +
          ∑ p ∈ Finset.univ.erase d₁, L.cylinder (D p) := by
          rw [hsplit]
          abel
      _ = 1 := by
          rw [Finset.add_sum_erase _ (fun p ↦ L.cylinder (D p))
            (Finset.mem_univ d₁)]
          exact hDsum
  -- the code-change unit
  set σcode : BinaryPrefixCode ι := ⟨σ, hσfree⟩ with hσcode
  set u₁ : Aˣ := L.codePairUnit R hR σcode hσsum
    (fun i j ↦ if i = j then (1 : A) else 0)
    (fun i j ↦ if i = j then (1 : A) else 0)
    (fun i i' ↦ by
      simp only [ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ i)])
    (fun j j' ↦ by
      simp only [ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ j)]) with hu₁
  have hu₁val : (u₁ : A) = ∑ i, L.wordS (R.word i) *
      L.wordT (σ i) := by
    rw [hu₁, L.codePairUnit_val]
    exact L.codeDelta_collapse R.word σ
  have hu₁mem : u₁ ∈ stableUnits A :=
    L.codeBijection_mem_stableUnits hdiv R.word σ
      (fun i j h ↦ R.prefix_free h) hR hσfree hσsum u₁ hu₁val
  -- the row collapse helper: a word meeting the intermediate code in
  -- exactly one place reduces the residual double sum to one row
  have hrow : ∀ (w : List (Fin 2)) (pstar : {i : ι // i ≠ i₂}) (m : A),
      (∀ p : {i : ι // i ≠ i₂}, L.wordT w * L.wordS (D p) =
        if p = pstar then m else 0) →
      ∀ F : {i : ι // i ≠ i₂} → κ → A,
      L.wordT w * (∑ p : {i : ι // i ≠ i₂}, ∑ j,
        L.wordS (D p) * F p j * L.wordT (C.word j)) =
      ∑ j, m * F pstar j * L.wordT (C.word j) := by
    intro w pstar m hcol F
    rw [Finset.mul_sum]
    calc ∑ p : {i : ι // i ≠ i₂}, L.wordT w *
          ∑ j, L.wordS (D p) * F p j * L.wordT (C.word j)
        = ∑ p : {i : ι // i ≠ i₂}, (if p = pstar then
            ∑ j, m * F p j * L.wordT (C.word j) else 0) := by
          refine Finset.sum_congr rfl fun p _ ↦ ?_
          rw [Finset.mul_sum]
          by_cases hp : p = pstar
          · rw [if_pos hp]
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            rw [show L.wordT w * (L.wordS (D p) * F p j *
                L.wordT (C.word j)) =
              (L.wordT w * L.wordS (D p)) * F p j *
                L.wordT (C.word j) from by noncomm_ring,
              hcol p, if_pos hp]
          · rw [if_neg hp]
            refine Finset.sum_eq_zero fun j _ ↦ ?_
            rw [show L.wordT w * (L.wordS (D p) * F p j *
                L.wordT (C.word j)) =
              (L.wordT w * L.wordS (D p)) * F p j *
                L.wordT (C.word j) from by noncomm_ring,
              hcol p, if_neg hp, zero_mul, zero_mul]
      _ = ∑ j, m * F pstar j * L.wordT (C.word j) := by
          rw [Finset.sum_ite_eq' Finset.univ pstar,
            if_pos (Finset.mem_univ pstar)]
  -- the three collision patterns
  have hcol₂ : ∀ p : {i : ι // i ≠ i₂},
      L.wordT (σ i₂) * L.wordS (D p) =
      if p = d₁ then L.wordT [1] else 0 := by
    intro p
    rw [hσi₂]
    by_cases hp : p = d₁
    · rw [if_pos hp, hp, L.wordT_append_mul_wordS]
    · rw [if_neg hp]
      have hpq : d₁ ≠ p := Ne.symm hp
      exact L.wordT_mul_wordS_of_incomparable _ _
        ((incomparable_append_single (hDfree hpq)
          (hDfree (Ne.symm hpq)) 1).2)
        ((incomparable_append_single (hDfree hpq)
          (hDfree (Ne.symm hpq)) 1).1)
  have hcol₁ : ∀ p : {i : ι // i ≠ i₂},
      L.wordT (σ i₁) * L.wordS (D p) =
      if p = d₁ then L.wordT [0] else 0 := by
    intro p
    rw [hσi₁]
    by_cases hp : p = d₁
    · rw [if_pos hp, hp, L.wordT_append_mul_wordS]
    · rw [if_neg hp]
      have hpq : d₁ ≠ p := Ne.symm hp
      exact L.wordT_mul_wordS_of_incomparable _ _
        ((incomparable_append_single (hDfree hpq)
          (hDfree (Ne.symm hpq)) 0).2)
        ((incomparable_append_single (hDfree hpq)
          (hDfree (Ne.symm hpq)) 0).1)
  have hcolo : ∀ (i : ι) (hi2 : i ≠ i₂), i ≠ i₁ →
      ∀ p : {i : ι // i ≠ i₂},
      L.wordT (σ i) * L.wordS (D p) =
      if p = ⟨i, hi2⟩ then (1 : A) else 0 := by
    intro i hi2 hi1 p
    rw [hσo i hi2 hi1]
    by_cases hp : p = ⟨i, hi2⟩
    · rw [if_pos hp, hp, L.wordT_mul_wordS_self]
    · rw [if_neg hp]
      have hpq : (⟨i, hi2⟩ : {i : ι // i ≠ i₂}) ≠ p := Ne.symm hp
      exact L.wordT_mul_wordS_of_incomparable _ _
        (hDfree hpq) (hDfree (Ne.symm hpq))
  -- the residual data and the factorization
  set F₂ : {i : ι // i ≠ i₂} → κ → A := fun p j ↦
    if p.1 = i₁ then (if j = j₀ then 1 else 0) else E p.1 j with hF₂
  set W : A := ∑ p : {i : ι // i ≠ i₂}, ∑ j,
    L.wordS (D p) * F₂ p j * L.wordT (C.word j) with hW
  have hFd₁ : ∀ j, F₂ d₁ j = if j = j₀ then 1 else 0 := by
    intro j
    rw [hF₂]
    beta_reduce
    rw [if_pos rfl]
  have hFo : ∀ (i : ι) (hi2 : i ≠ i₂), i ≠ i₁ → ∀ j : κ,
      F₂ ⟨i, hi2⟩ j = E i j := by
    intro i hi2 hi1 j
    rw [hF₂]
    beta_reduce
    rw [if_neg hi1]
  -- the factorization `u = u₁ · (residual)`
  have hfact : (u : A) = (u₁ : A) * W := by
    rw [hu, hu₁val, hW, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    by_cases hi2 : i = i₂
    · rw [hi2, mul_assoc, hrow (σ i₂) d₁ (L.wordT [1]) hcol₂ F₂,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      by_cases hj : j = j₀
      · rw [hj, h2, hFd₁ j₀, if_pos rfl]
        simp only [wordT_cons, wordT_nil, one_mul, mul_one]
        noncomm_ring
      · rw [h5 j hj, hFd₁ j, if_neg hj]
        simp only [mul_zero, zero_mul]
    · by_cases hi1 : i = i₁
      · rw [hi1, mul_assoc, hrow (σ i₁) d₁ (L.wordT [0]) hcol₁ F₂,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        by_cases hj : j = j₀
        · rw [hj, h1, hFd₁ j₀, if_pos rfl]
          simp only [wordT_cons, wordT_nil, one_mul, mul_one]
          noncomm_ring
        · rw [h4 j hj, hFd₁ j, if_neg hj]
          simp only [mul_zero, zero_mul]
      · rw [mul_assoc, hrow (σ i) ⟨i, hi2⟩ 1 (hcolo i hi2 hi1) F₂,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [hFo i hi2 hi1 j, one_mul, mul_assoc]
  -- assemble
  refine ⟨u₁⁻¹ * u, ?_, ?_⟩
  · rw [Units.val_mul, hfact, ← mul_assoc, Units.inv_mul, one_mul,
      hW]
  · constructor
    · intro hH
      exact mul_mem (inv_mem hu₁mem) hH
    · intro hH
      rw [show u = u₁ * (u₁⁻¹ * u) from by group]
      exact mul_mem hu₁mem hH

end LeavittFamily
end NonsoficGroupsExist
