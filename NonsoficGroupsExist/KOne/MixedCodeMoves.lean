import NonsoficGroupsExist.KOne.PencilCore
import NonsoficGroupsExist.KOne.CodeRelativeFullness

/-!
# Mixed-code moves and the shift-column rigidity

Two ingredients of the peel normalization:

* block unipotents with disjoint row/column supports along an
  **arbitrary** prefix code (not just the uniform-depth one) lie in
  the diagonal class group — the cross terms die on the code's own
  orthogonality;
* a nonzero scalar combination `λ₀•t₀ + λ₁•t₁` is not left
  invertible, so a pencil column with linearly dependent `t`-data
  cannot be a column of a unit; contrapositively the shift columns
  produced by the elimination always carry an independent pair.
-/

namespace NonsoficGroupsExist
namespace LeavittFamily

open MatrixDiagonalization

variable {A : Type*} [Ring A] (L : LeavittFamily A)
variable {k : Type*} [Field k] [Algebra k A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- **Block-unipotent moves along any prefix code are in `H`.** -/
theorem code_unipotent_mem (Ccode : BinaryPrefixCode ι)
    {S T : Finset ι} (hST : Disjoint S T)
    (N : ι → ι → A) (u : Aˣ)
    (hu : (u : A) = 1 + ∑ p ∈ S ×ˢ T,
      L.wordS (Ccode.word p.1) * N p.1 p.2 *
        L.wordT (Ccode.word p.2)) :
    u ∈ stableUnits A := by
  classical
  suffices h : ∀ P : Finset (ι × ι),
      P ⊆ S ×ˢ T → ∀ u : Aˣ,
      (u : A) = 1 + ∑ p ∈ P,
        L.wordS (Ccode.word p.1) * N p.1 p.2 *
          L.wordT (Ccode.word p.2) →
      u ∈ stableUnits A from h _ subset_rfl u hu
  intro P
  induction P using Finset.cons_induction with
  | empty =>
      intro _ u hu
      have hone : u = 1 := Units.ext (by
        rw [Units.val_one]
        simpa using hu)
      rw [hone]
      exact one_mem _
  | cons p P hp ih =>
      intro hPsub u hu
      have hpST : p ∈ S ×ˢ T := hPsub (Finset.mem_cons.mpr (Or.inl rfl))
      have hp1S : p.1 ∈ S := (Finset.mem_product.mp hpST).1
      have hp2T : p.2 ∈ T := (Finset.mem_product.mp hpST).2
      have hp12 : p.1 ≠ p.2 := fun h ↦
        (Finset.disjoint_left.mp hST hp1S) (h ▸ hp2T)
      have hinc : ¬Ccode.word p.1 <+: Ccode.word p.2 :=
        Ccode.prefix_free hp12
      have hinc' : ¬Ccode.word p.2 <+: Ccode.word p.1 :=
        Ccode.prefix_free (Ne.symm hp12)
      set ν : Aˣ := L.incomparableUnit hinc hinc' (N p.1 p.2) with hν
      have hνval : (ν : A) = 1 + L.wordS (Ccode.word p.1) *
          N p.1 p.2 * L.wordT (Ccode.word p.2) := rfl
      have hcross : (∑ q ∈ P, L.wordS (Ccode.word q.1) * N q.1 q.2 *
            L.wordT (Ccode.word q.2)) *
          (L.wordS (Ccode.word p.1) * N p.1 p.2 *
            L.wordT (Ccode.word p.2)) = 0 := by
        rw [Finset.sum_mul]
        refine Finset.sum_eq_zero fun q hq ↦ ?_
        have hqST : q ∈ S ×ˢ T := hPsub (Finset.subset_cons hp hq)
        have hq2T : q.2 ∈ T := (Finset.mem_product.mp hqST).2
        have hne : q.2 ≠ p.1 := fun h ↦
          (Finset.disjoint_left.mp hST hp1S) (h ▸ hq2T)
        have horth : L.wordT (Ccode.word q.2) *
            L.wordS (Ccode.word p.1) = 0 := by
          have h := L.prefixCode_orthogonal Ccode q.2 p.1
          rw [if_neg hne] at h
          exact h
        rw [show L.wordS (Ccode.word q.1) * N q.1 q.2 *
            L.wordT (Ccode.word q.2) *
            (L.wordS (Ccode.word p.1) * N p.1 p.2 *
              L.wordT (Ccode.word p.2)) =
          L.wordS (Ccode.word q.1) * N q.1 q.2 *
            (L.wordT (Ccode.word q.2) * L.wordS (Ccode.word p.1)) *
            (N p.1 p.2 * L.wordT (Ccode.word p.2)) from by noncomm_ring,
          horth, mul_zero, zero_mul]
      have hval : (1 + ∑ q ∈ P, L.wordS (Ccode.word q.1) * N q.1 q.2 *
          L.wordT (Ccode.word q.2)) * (ν : A) = (u : A) := by
        rw [hνval, hu, Finset.sum_cons]
        calc (1 + ∑ q ∈ P, L.wordS (Ccode.word q.1) * N q.1 q.2 *
              L.wordT (Ccode.word q.2)) *
            (1 + L.wordS (Ccode.word p.1) * N p.1 p.2 *
              L.wordT (Ccode.word p.2))
            = 1 + (L.wordS (Ccode.word p.1) * N p.1 p.2 *
                L.wordT (Ccode.word p.2) +
              ∑ q ∈ P, L.wordS (Ccode.word q.1) * N q.1 q.2 *
                L.wordT (Ccode.word q.2)) +
              (∑ q ∈ P, L.wordS (Ccode.word q.1) * N q.1 q.2 *
                L.wordT (Ccode.word q.2)) *
              (L.wordS (Ccode.word p.1) * N p.1 p.2 *
                L.wordT (Ccode.word p.2)) := by noncomm_ring
          _ = 1 + (L.wordS (Ccode.word p.1) * N p.1 p.2 *
                L.wordT (Ccode.word p.2) +
              ∑ q ∈ P, L.wordS (Ccode.word q.1) * N q.1 q.2 *
                L.wordT (Ccode.word q.2)) := by
              rw [hcross, add_zero]
      have hu' : ((u * ν⁻¹ : Aˣ) : A) = 1 +
          ∑ q ∈ P, L.wordS (Ccode.word q.1) * N q.1 q.2 *
            L.wordT (Ccode.word q.2) := by
        rw [Units.val_mul, ← hval, mul_assoc, Units.mul_inv, mul_one]
      have hsplit : u = (u * ν⁻¹) * ν := by group
      rw [hsplit]
      exact mul_mem
        (ih (fun q hq ↦ hPsub (Finset.subset_cons hp hq)) (u * ν⁻¹) hu')
        (L.incomparableUnit_mem hinc hinc' (N p.1 p.2))

/-- A nonzero scalar `t`-combination is not left invertible. -/
theorem t_combo_not_left_invertible [Nontrivial A]
    {lam₀ lam₁ : k} (hlam : lam₀ ≠ 0 ∨ lam₁ ≠ 0) (x : A) :
    x * (lam₀ • L.t 0 + lam₁ • L.t 1) ≠ 1 := by
  intro h
  have hs : ∀ z : Fin 2, (lam₀ • L.t 0 + lam₁ • L.t 1) * L.s z =
      algebraMap k A (if z = 0 then lam₀ else lam₁) := by
    intro z
    rw [add_mul, Algebra.smul_def, Algebra.smul_def, mul_assoc,
      mul_assoc, t_mul_s, t_mul_s]
    fin_cases z <;> simp
  have h0 : algebraMap k A lam₀ * x = L.s 0 := by
    have h' : x * ((lam₀ • L.t 0 + lam₁ • L.t 1) * L.s 0) = L.s 0 := by
      rw [← mul_assoc, h, one_mul]
    rw [hs 0, if_pos rfl, ← Algebra.commutes lam₀ x] at h'
    exact h'
  have h1 : algebraMap k A lam₁ * x = L.s 1 := by
    have h' : x * ((lam₀ • L.t 0 + lam₁ • L.t 1) * L.s 1) = L.s 1 := by
      rw [← mul_assoc, h, one_mul]
    rw [hs 1, if_neg (show ¬(1 : Fin 2) = 0 by decide),
      ← Algebra.commutes lam₁ x] at h'
    exact h'
  rcases hlam with hl | hl
  · have hcontr : L.s 1 = algebraMap k A (lam₁ * lam₀⁻¹) * L.s 0 := by
      have hx : x = algebraMap k A lam₀⁻¹ * L.s 0 := by
        rw [← h0, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hl, map_one,
          one_mul]
      rw [← h1, hx, ← mul_assoc, ← map_mul]
    have hone : (1 : A) = 0 := by
      calc (1 : A) = L.t 1 * L.s 1 := by rw [t_mul_s, if_pos rfl]
        _ = L.t 1 * (algebraMap k A (lam₁ * lam₀⁻¹) * L.s 0) := by
            rw [← hcontr]
        _ = algebraMap k A (lam₁ * lam₀⁻¹) * (L.t 1 * L.s 0) := by
            rw [← mul_assoc, ← Algebra.commutes, mul_assoc]
        _ = 0 := by
            rw [t_mul_s, if_neg (show ¬(1 : Fin 2) = 0 by decide),
              mul_zero]
    exact one_ne_zero hone
  · have hcontr : L.s 0 = algebraMap k A (lam₀ * lam₁⁻¹) * L.s 1 := by
      have hx : x = algebraMap k A lam₁⁻¹ * L.s 1 := by
        rw [← h1, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hl, map_one,
          one_mul]
      rw [← h0, hx, ← mul_assoc, ← map_mul]
    have hone : (1 : A) = 0 := by
      calc (1 : A) = L.t 0 * L.s 0 := by rw [t_mul_s, if_pos rfl]
        _ = L.t 0 * (algebraMap k A (lam₀ * lam₁⁻¹) * L.s 1) := by
            rw [← hcontr]
        _ = algebraMap k A (lam₀ * lam₁⁻¹) * (L.t 0 * L.s 1) := by
            rw [← mul_assoc, ← Algebra.commutes, mul_assoc]
        _ = 0 := by
            rw [t_mul_s, if_neg (show ¬(0 : Fin 2) = 1 by decide),
              mul_zero]
    exact one_ne_zero hone

end LeavittFamily
end NonsoficGroupsExist
