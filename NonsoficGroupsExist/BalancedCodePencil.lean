import NonsoficGroupsExist.RefinedCodes
import NonsoficGroupsExist.CodeScalarMoves
import NonsoficGroupsExist.CodeChangeGlue
import NonsoficGroupsExist.EntrywiseKill
import NonsoficGroupsExist.AtomPeel
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Balanced code pencils are in the class group

If every corner entry `T(Cⱼ)·u⁻¹·S(Rᵢ)` of a unit's inverse over a
pair of complete codes is *balanced*, then after padding to a common
level the inverse is the transport of a scalar matrix along the
uniformly refined code pair.  Such a scalar matrix is forced to be
square and invertible — a kernel vector on either side would produce
a vanishing column `u⁻¹·S(w) = 0` or row, impossible for a unit —
and the value then factors as a code bijection times a scalar move,
both in the class group.  This is the terminal node of the master
induction.
-/

namespace NonsoficGroupsExist
namespace BinaryLeavitt

open LeavittFamily MatrixDiagonalization

variable (k : Type) [Field k]

/-- Words of a prefix family are `k`-independent: a vanishing
combination of `wordS`'s has vanishing coefficients. -/
theorem wordS_combo_eq_zero {ι : Type*} [Fintype ι]
    [Nontrivial (BinaryLeavittAlgebra k)]
    (w : ι → List (Fin 2))
    (hfree : ∀ ⦃p q : ι⦄, p ≠ q → ¬w p <+: w q)
    (c : ι → k) (h : (∑ q, c q • (family k).wordS (w q)) = 0) :
    ∀ q, c q = 0 := by
  classical
  intro q₀
  have hstrip : (family k).wordT (w q₀) *
      (∑ q, c q • (family k).wordS (w q)) = 0 := by
    rw [h, mul_zero]
  rw [Finset.mul_sum] at hstrip
  rw [Finset.sum_congr rfl (fun q _ ↦ show
      (family k).wordT (w q₀) * (c q • (family k).wordS (w q)) =
      if q₀ = q then c q • (1 : BinaryLeavittAlgebra k) else 0 from by
    rw [mul_smul_comm]
    by_cases hq : q₀ = q
    · rw [if_pos hq, hq, (family k).wordT_mul_wordS_self]
    · rw [if_neg hq, (family k).wordT_mul_wordS_of_incomparable _ _
        (hfree hq) (hfree (Ne.symm hq)), smul_zero])] at hstrip
  rw [Finset.sum_ite_eq Finset.univ q₀,
    if_pos (Finset.mem_univ q₀)] at hstrip
  rcases smul_eq_zero.mp hstrip with h1 | h1
  · exact h1
  · exact absurd h1 one_ne_zero

/-- Mirror: a vanishing combination of `wordT`'s has vanishing
coefficients. -/
theorem wordT_combo_eq_zero {ι : Type*} [Fintype ι]
    [Nontrivial (BinaryLeavittAlgebra k)]
    (w : ι → List (Fin 2))
    (hfree : ∀ ⦃p q : ι⦄, p ≠ q → ¬w p <+: w q)
    (c : ι → k) (h : (∑ q, c q • (family k).wordT (w q)) = 0) :
    ∀ q, c q = 0 := by
  classical
  intro q₀
  have hstrip : (∑ q, c q • (family k).wordT (w q)) *
      (family k).wordS (w q₀) = 0 := by
    rw [h, zero_mul]
  rw [Finset.sum_mul] at hstrip
  rw [Finset.sum_congr rfl (fun q _ ↦ show
      (c q • (family k).wordT (w q)) * (family k).wordS (w q₀) =
      if q = q₀ then c q • (1 : BinaryLeavittAlgebra k) else 0 from by
    rw [smul_mul_assoc]
    by_cases hq : q = q₀
    · rw [if_pos hq, hq, (family k).wordT_mul_wordS_self]
    · rw [if_neg hq, (family k).wordT_mul_wordS_of_incomparable _ _
        (hfree hq) (hfree (Ne.symm hq)), smul_zero])] at hstrip
  rw [Finset.sum_ite_eq' Finset.univ q₀,
    if_pos (Finset.mem_univ q₀)] at hstrip
  rcases smul_eq_zero.mp hstrip with h1 | h1
  · exact h1
  · exact absurd h1 one_ne_zero


/-- **The terminal node**: a unit whose inverse has balanced corner
entries over a pair of complete codes lies in the class group. -/
theorem balanced_entries_mem_stableUnits
    [Nontrivial (BinaryLeavittAlgebra k)]
    (hdiv : ∀ x : BinaryLeavittAlgebra k, x ≠ 0 →
      ∃ p q : BinaryLeavittAlgebra k, p * x * q = 1)
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (R : BinaryPrefixCode ι) (hR : (family k).IsComplete R)
    (C : BinaryPrefixCode κ) (hC : (family k).IsComplete C)
    (u : (BinaryLeavittAlgebra k)ˣ)
    (hbal : ∀ (j : κ) (i : ι),
      (family k).wordT (C.word j) *
        ((u⁻¹ : (BinaryLeavittAlgebra k)ˣ) : BinaryLeavittAlgebra k) *
        (family k).wordS (R.word i) ∈
      Submodule.span k ((family k).degreeMonomials 0 0)) :
    u ∈ stableUnits (BinaryLeavittAlgebra k) := by
  classical
  set L : LeavittFamily (BinaryLeavittAlgebra k) := family k with hL
  set x : BinaryLeavittAlgebra k :=
    ((u⁻¹ : (BinaryLeavittAlgebra k)ˣ) : BinaryLeavittAlgebra k)
    with hx
  suffices h : u⁻¹ ∈ stableUnits (BinaryLeavittAlgebra k) by
    simpa using inv_mem h
  -- a common level for all entries
  have hex : ∀ p : κ × ι, ∃ n : ℕ,
      L.wordT (C.word p.1) * x * L.wordS (R.word p.2) ∈
        Submodule.span k (L.levelMonomials n) := fun p ↦
    L.span_degree_zero_le_levelSpan (hbal p.1 p.2)
  choose f hf using hex
  set M : ℕ := Finset.univ.sup f with hM
  have hlvl : ∀ (j : κ) (i : ι),
      L.wordT (C.word j) * x * L.wordS (R.word i) ∈
        Submodule.span k (L.levelMonomials M) := fun j i ↦
    L.span_levelMonomials_mono
      (Finset.le_sup (f := f) (Finset.mem_univ (j, i))) (hf (j, i))
  -- the scalar data
  have hWex : ∀ p : κ × ι, ∃ Wp :
      Matrix (Fin M → Fin 2) (Fin M → Fin 2) k,
      L.balancedEmbed (k := k) M Wp =
        L.wordT (C.word p.1) * x * L.wordS (R.word p.2) := fun p ↦
    L.exists_balancedEmbed_eq (hlvl p.1 p.2)
  choose W hW using hWex
  -- the refined codes
  set CM : BinaryPrefixCode (κ × (Fin M → Fin 2)) :=
    ⟨fun p ↦ C.word p.1 ++ List.ofFn p.2, refined_free C M⟩ with hCM
  set RM : BinaryPrefixCode (ι × (Fin M → Fin 2)) :=
    ⟨fun q ↦ R.word q.1 ++ List.ofFn q.2, refined_free R M⟩ with hRM
  have hCMc : L.IsComplete CM := L.refined_sum C hC M
  have hRMc : L.IsComplete RM := L.refined_sum R hR M
  set W' : (κ × (Fin M → Fin 2)) → (ι × (Fin M → Fin 2)) → k :=
    fun p q ↦ W (p.1, q.1) p.2 q.2 with hW'
  -- the scalar form of the inverse
  have hembed : ∀ p : κ × ι, L.balancedEmbed (k := k) M (W p) =
      ∑ α, ∑ β, L.wordS (List.ofFn α) *
        algebraMap k (BinaryLeavittAlgebra k) (W p α β) *
        L.wordT (List.ofFn β) := fun p ↦ rfl
  have h4 : x = ∑ j, ∑ i, ∑ α : Fin M → Fin 2, ∑ β : Fin M → Fin 2,
      L.wordS (C.word j ++ List.ofFn α) *
        algebraMap k (BinaryLeavittAlgebra k) (W (j, i) α β) *
        L.wordT (R.word i ++ List.ofFn β) := by
    calc x = ∑ j, ∑ i, L.wordS (C.word j) *
          (L.wordT (C.word j) * x * L.wordS (R.word i)) *
          L.wordT (R.word i) := L.codePair_partition C hC R hR x
      _ = _ := by
          refine Finset.sum_congr rfl fun j _ ↦
            Finset.sum_congr rfl fun i _ ↦ ?_
          rw [← hW (j, i), hembed (j, i), Finset.mul_sum,
            Finset.sum_mul]
          refine Finset.sum_congr rfl fun α _ ↦ ?_
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun β _ ↦ ?_
          rw [show L.wordS (C.word j) * (L.wordS (List.ofFn α) *
              algebraMap k (BinaryLeavittAlgebra k) (W (j, i) α β) *
              L.wordT (List.ofFn β)) * L.wordT (R.word i) =
            (L.wordS (C.word j) * L.wordS (List.ofFn α)) *
              algebraMap k (BinaryLeavittAlgebra k) (W (j, i) α β) *
              (L.wordT (List.ofFn β) * L.wordT (R.word i)) from by
              noncomm_ring,
            ← wordS_append, ← wordT_append]
  have hval : x = ∑ p : κ × (Fin M → Fin 2),
      ∑ q : ι × (Fin M → Fin 2),
      L.wordS (CM.word p) *
        algebraMap k (BinaryLeavittAlgebra k) (W' p q) *
        L.wordT (RM.word q) := by
    have h6 : (∑ p : κ × (Fin M → Fin 2), ∑ q : ι × (Fin M → Fin 2),
        L.wordS (CM.word p) *
          algebraMap k (BinaryLeavittAlgebra k) (W' p q) *
          L.wordT (RM.word q)) =
        ∑ j, ∑ α : Fin M → Fin 2, ∑ i, ∑ β : Fin M → Fin 2,
        L.wordS (C.word j ++ List.ofFn α) *
          algebraMap k (BinaryLeavittAlgebra k) (W (j, i) α β) *
          L.wordT (R.word i ++ List.ofFn β) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun j _ ↦
        Finset.sum_congr rfl fun α _ ↦ ?_
      rw [Fintype.sum_prod_type]
    rw [h6, h4]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    exact Finset.sum_comm
  -- zero columns are impossible
  have hinj : ∀ v₀ : (ι × (Fin M → Fin 2)) → k,
      (∀ p, ∑ q, W' p q * v₀ q = 0) → v₀ = 0 := by
    intro v₀ hv
    set x₀ : BinaryLeavittAlgebra k :=
      ∑ q, v₀ q • L.wordS (RM.word q) with hx₀def
    have hx₀ : x * x₀ = 0 := by
      rw [hval, hx₀def, Finset.sum_mul]
      refine Finset.sum_eq_zero fun p _ ↦ ?_
      rw [Finset.sum_mul]
      have hcol : ∀ q, (L.wordS (CM.word p) *
          algebraMap k (BinaryLeavittAlgebra k) (W' p q) *
          L.wordT (RM.word q)) * x₀ =
          L.wordS (CM.word p) *
            algebraMap k (BinaryLeavittAlgebra k) (W' p q * v₀ q) := by
        intro q
        rw [hx₀def, Finset.mul_sum]
        rw [Finset.sum_congr rfl (fun q' _ ↦ show
            L.wordS (CM.word p) *
              algebraMap k (BinaryLeavittAlgebra k) (W' p q) *
              L.wordT (RM.word q) * (v₀ q' • L.wordS (RM.word q')) =
            if q = q' then v₀ q' • (L.wordS (CM.word p) *
              algebraMap k (BinaryLeavittAlgebra k) (W' p q)) else 0
            from by
          rw [mul_smul_comm,
            show L.wordS (CM.word p) *
                algebraMap k (BinaryLeavittAlgebra k) (W' p q) *
                L.wordT (RM.word q) * L.wordS (RM.word q') =
              L.wordS (CM.word p) *
                algebraMap k (BinaryLeavittAlgebra k) (W' p q) *
                (L.wordT (RM.word q) * L.wordS (RM.word q')) from by
              noncomm_ring,
            L.prefixCode_orthogonal RM q q']
          split_ifs with h
          · rw [mul_one]
          · rw [mul_zero, smul_zero])]
        -- the summand is `if q = q'` with `q'` bound, which is the unprimed
        -- lemma; `sum_ite_eq'` matches `if q' = q`.
        rw [Finset.sum_ite_eq Finset.univ q, if_pos (Finset.mem_univ q)]
        -- `Algebra.smul_def` on its own lands `algebraMap (v₀ q)` on the
        -- *left* of `wordS`, which no reassociation can undo.  Push the
        -- scalar through the product first, then expand it.
        rw [← mul_smul_comm, Algebra.smul_def, ← map_mul,
          mul_comm (v₀ q)]
      rw [Finset.sum_congr rfl fun q _ ↦ hcol q, ← Finset.mul_sum,
        ← map_sum, hv p, map_zero, mul_zero]
    have hx₀0 : x₀ = 0 := by
      calc x₀ = ((u : BinaryLeavittAlgebra k) * x) * x₀ := by
            rw [hx, Units.mul_inv, one_mul]
        _ = (u : BinaryLeavittAlgebra k) * (x * x₀) := by
            rw [mul_assoc]
        _ = 0 := by rw [hx₀, mul_zero]
    funext q
    exact wordS_combo_eq_zero k RM.word RM.prefix_free v₀
      (by rw [← hx₀def]; exact hx₀0) q
  -- zero rows are impossible
  have hinj' : ∀ u₀ : (κ × (Fin M → Fin 2)) → k,
      (∀ q, ∑ p, u₀ p * W' p q = 0) → u₀ = 0 := by
    intro u₀ hu₀
    set x₁ : BinaryLeavittAlgebra k :=
      ∑ p, u₀ p • L.wordT (CM.word p) with hx₁def
    have hx₁ : x₁ * x = 0 := by
      rw [hval, hx₁def, Finset.sum_mul]
      rw [Finset.sum_congr rfl (fun p₀ _ ↦ show
          (u₀ p₀ • L.wordT (CM.word p₀)) *
            (∑ p, ∑ q, L.wordS (CM.word p) *
              algebraMap k (BinaryLeavittAlgebra k) (W' p q) *
              L.wordT (RM.word q)) =
          ∑ q, algebraMap k (BinaryLeavittAlgebra k)
            (u₀ p₀ * W' p₀ q) * L.wordT (RM.word q) from by
        rw [smul_mul_assoc, Finset.mul_sum]
        rw [Finset.sum_congr rfl (fun p _ ↦ show
            L.wordT (CM.word p₀) * ∑ q, L.wordS (CM.word p) *
              algebraMap k (BinaryLeavittAlgebra k) (W' p q) *
              L.wordT (RM.word q) =
            if p₀ = p then ∑ q,
              algebraMap k (BinaryLeavittAlgebra k) (W' p q) *
              L.wordT (RM.word q) else 0 from by
          rw [Finset.mul_sum]
          rw [Finset.sum_congr rfl (fun q _ ↦ show
              L.wordT (CM.word p₀) * (L.wordS (CM.word p) *
                algebraMap k (BinaryLeavittAlgebra k) (W' p q) *
                L.wordT (RM.word q)) =
              if p₀ = p then
                algebraMap k (BinaryLeavittAlgebra k) (W' p q) *
                  L.wordT (RM.word q) else 0 from by
            rw [show L.wordT (CM.word p₀) * (L.wordS (CM.word p) *
                algebraMap k (BinaryLeavittAlgebra k) (W' p q) *
                L.wordT (RM.word q)) =
              (L.wordT (CM.word p₀) * L.wordS (CM.word p)) *
                (algebraMap k (BinaryLeavittAlgebra k) (W' p q) *
                  L.wordT (RM.word q)) from by noncomm_ring,
              L.prefixCode_orthogonal CM p₀ p]
            split_ifs with h
            · rw [one_mul]
            · rw [zero_mul])]
          split_ifs with h
          · rfl
          · exact Finset.sum_const_zero)]
        rw [Finset.sum_ite_eq Finset.univ p₀,
          if_pos (Finset.mem_univ p₀), Finset.smul_sum]
        refine Finset.sum_congr rfl fun q _ ↦ ?_
        rw [Algebra.smul_def, map_mul, mul_assoc])]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun q _ ↦ ?_
      rw [← Finset.sum_mul, ← map_sum, hu₀ q, map_zero, zero_mul]
    have hx₁0 : x₁ = 0 := by
      calc x₁ = x₁ * (x * (u : BinaryLeavittAlgebra k)) := by
            rw [hx, Units.inv_mul, mul_one]
        _ = (x₁ * x) * (u : BinaryLeavittAlgebra k) := by
            rw [mul_assoc]
        _ = 0 := by rw [hx₁, zero_mul]
    funext p
    exact wordT_combo_eq_zero k CM.word CM.prefix_free u₀
      (by rw [← hx₁def]; exact hx₁0) p
  -- the scalar matrix is square and invertible
  have hcard : Fintype.card (κ × (Fin M → Fin 2)) =
      Fintype.card (ι × (Fin M → Fin 2)) := by
    have hf1 : Function.Injective (Matrix.mulVecLin (Matrix.of W')) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro v hv
      refine hinj v fun p ↦ ?_
      have h := congrFun hv p
      simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
        using h
    have hf2 : Function.Injective
        -- `ᵀ` is scoped notation in `Matrix`, which this file does not open.
        (Matrix.mulVecLin (Matrix.of W').transpose) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro v hv
      refine hinj' v fun q ↦ ?_
      have h := congrFun hv q
      -- `mulVec_transpose` fires before `mulVec` can unfold, so `h` arrives as
      -- a `vecMul`; that head has to be in the simp set too.
      simpa [Matrix.mulVecLin_apply, Matrix.mulVec, Matrix.vecMul,
        dotProduct, Matrix.transpose_apply, mul_comm] using h
    have h1 := LinearMap.finrank_le_finrank_of_injective hf1
    have h2 := LinearMap.finrank_le_finrank_of_injective hf2
    rw [Module.finrank_pi, Module.finrank_pi] at h1
    rw [Module.finrank_pi, Module.finrank_pi] at h2
    omega
  set e : (κ × (Fin M → Fin 2)) ≃ (ι × (Fin M → Fin 2)) :=
    Fintype.equivOfCardEq hcard with he
  -- the code bijection
  set RMe : BinaryPrefixCode (κ × (Fin M → Fin 2)) :=
    ⟨fun p ↦ RM.word (e p), fun p q hpq h ↦
      RM.prefix_free (fun hh ↦ hpq (e.injective hh)) h⟩ with hRMe
  have hRMec : L.IsComplete RMe := by
    show (∑ p, L.cylinder (RM.word (e p))) = 1
    rw [Fintype.sum_equiv e (fun p ↦ L.cylinder (RM.word (e p)))
      (fun q ↦ L.cylinder (RM.word q)) (fun p ↦ rfl)]
    exact hRMc
  set ω : (BinaryLeavittAlgebra k)ˣ := L.codePairUnit RMe hRMec CM hCMc
    (fun p p' ↦ if p = p' then (1 : BinaryLeavittAlgebra k) else 0)
    (fun p p' ↦ if p = p' then (1 : BinaryLeavittAlgebra k) else 0)
    (fun p p' ↦ by
      simp only [ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ p)])
    (fun p p' ↦ by
      simp only [ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ p)]) with hω
  have hωval : (ω : BinaryLeavittAlgebra k) =
      ∑ p, L.wordS (RM.word (e p)) * L.wordT (CM.word p) := by
    rw [hω, L.codePairUnit_val]
    exact L.codeDelta_collapse (fun p ↦ RM.word (e p)) CM.word
  have hωmem : ω ∈ stableUnits (BinaryLeavittAlgebra k) :=
    -- the base field is implicit and no other argument pins it down
    L.codeBijection_mem_stableUnits (k := k) hdiv (fun p ↦ RM.word (e p))
      CM.word
      (fun p q hpq h ↦ RM.prefix_free
        (fun hh ↦ hpq (e.injective hh)) h)
      (by
        rw [Fintype.sum_equiv e (fun p ↦ L.cylinder (RM.word (e p)))
          (fun q ↦ L.cylinder (RM.word q)) (fun p ↦ rfl)]
        exact hRMc)
      (fun p q hpq ↦ CM.prefix_free hpq) hCMc ω hωval
  -- the scalar factor
  have hu₂val : ((ω * u⁻¹ : (BinaryLeavittAlgebra k)ˣ) :
      BinaryLeavittAlgebra k) =
      L.codeScalar (k := k) RM
        (Matrix.of fun q₁ q₂ ↦ W' (e.symm q₁) q₂) := by
    rw [Units.val_mul, hωval, show
      ((u⁻¹ : (BinaryLeavittAlgebra k)ˣ) : BinaryLeavittAlgebra k) =
        x from rfl, hval]
    calc (∑ p, L.wordS (RM.word (e p)) * L.wordT (CM.word p)) *
          (∑ p', ∑ q, L.wordS (CM.word p') *
            algebraMap k (BinaryLeavittAlgebra k) (W' p' q) *
            L.wordT (RM.word q))
        = ∑ p, ∑ q, L.wordS (RM.word (e p)) *
            algebraMap k (BinaryLeavittAlgebra k) (W' p q) *
            L.wordT (RM.word q) := by
          have h := L.codePair_mul CM (fun p ↦ RM.word (e p)) RM.word
            (fun p p' ↦ if p = p' then (1 : BinaryLeavittAlgebra k)
              else 0)
            (fun p' q ↦ algebraMap k (BinaryLeavittAlgebra k)
              (W' p' q))
          beta_reduce at h
          rw [← L.codeDelta_collapse (fun p ↦ RM.word (e p)) CM.word]
          rw [h]
          refine Finset.sum_congr rfl fun p _ ↦
            Finset.sum_congr rfl fun q _ ↦ ?_
          congr 1
          congr 1
          simp only [ite_mul, one_mul, zero_mul]
          rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ p)]
      _ = L.codeScalar (k := k) RM
            (Matrix.of fun q₁ q₂ ↦ W' (e.symm q₁) q₂) := by
          unfold LeavittFamily.codeScalar
          rw [Fintype.sum_equiv e
            (fun p ↦ ∑ q, L.wordS (RM.word (e p)) *
              algebraMap k (BinaryLeavittAlgebra k) (W' p q) *
              L.wordT (RM.word q))
            (fun q₁ ↦ ∑ q, L.wordS (RM.word q₁) *
              algebraMap k (BinaryLeavittAlgebra k)
                (Matrix.of (fun q₁ q₂ ↦ W' (e.symm q₁) q₂) q₁ q) *
              L.wordT (RM.word q))
            (fun p ↦ by
              refine Finset.sum_congr rfl fun q _ ↦ ?_
              rw [show Matrix.of (fun q₁ q₂ ↦ W' (e.symm q₁) q₂)
                  (e p) q = W' (e.symm (e p)) q from rfl,
                Equiv.symm_apply_apply])]
  have hdet : IsUnit (Matrix.of fun q₁ q₂ ↦ W' (e.symm q₁) q₂) := by
    by_contra hns
    have hdet0 : (Matrix.of fun q₁ q₂ ↦ W' (e.symm q₁) q₂).det = 0 := by
      by_contra h0
      exact hns ((Matrix.isUnit_iff_isUnit_det _).mpr
        (isUnit_iff_ne_zero.mpr h0))
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet0
    refine hv0 (hinj v fun p ↦ ?_)
    have h := congrFun hv (e p)
    simpa [Matrix.mulVec, dotProduct, Equiv.symm_apply_apply] using h
  have hu₂mem : (ω * u⁻¹ : (BinaryLeavittAlgebra k)ˣ) ∈
      stableUnits (BinaryLeavittAlgebra k) :=
    L.codeScalar_unit_mem hdiv RM hRMc _ hdet (ω * u⁻¹) hu₂val
  have hfinal : u⁻¹ = ω⁻¹ * (ω * u⁻¹) := by group
  rw [hfinal]
  exact mul_mem (inv_mem hωmem) hu₂mem

end BinaryLeavitt
end NonsoficGroupsExist
