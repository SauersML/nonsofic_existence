import NonsoficGroupsExist.KOne.GradedComponents
import NonsoficGroupsExist.KOne.BalancedStableRank
import NonsoficGroupsExist.Leavitt.LeavittWindowReduction
-- `window_mul_mem_span` lives here
import NonsoficGroupsExist.KOne.WindowProductClosure

/-!
# The scalar-pencil form of narrow elements

At a deep enough corner level `m + 1` every narrow element is a
word-indexed matrix whose entries are *scalar* combinations of
`t₀, t₁, 1, s₀, s₁`: the balanced part contributes scalar constants
(`wordT_balancedEmbed_wordS`), while the degree `∓1` parts contribute
scalar multiples of single generators — the `t`-letter peeled from the
row word's last position, the `s`-letter from the column word's last
position, with the balanced residue evaluated one level down.
-/

namespace NonsoficGroupsExist
namespace LeavittFamily

open MatrixDiagonalization

variable {A : Type*} [Ring A] (L : LeavittFamily A)
variable {k : Type*} [Field k] [Algebra k A]

/-- Entry evaluation of the scalar embedding: stripping matching-depth
words off `balancedEmbed` recovers the matrix entry. -/
theorem wordT_balancedEmbed_wordS (m : ℕ)
    (C : Matrix (Fin m → Fin 2) (Fin m → Fin 2) k)
    (i j : Fin m → Fin 2) :
    L.wordT (List.ofFn i) * L.balancedEmbed (k := k) m C *
      L.wordS (List.ofFn j) = algebraMap k A (C i j) := by
  have h : (L.prefixMatrixFamily (fullBinaryCode m)
      (L.fullBinaryCode_complete m)).matrixRingEquiv.symm
      (L.balancedEmbed (k := k) m C) = (algebraMap k A).mapMatrix C := by
    rw [show L.balancedEmbed (k := k) m C =
      (L.prefixMatrixFamily (fullBinaryCode m)
        (L.fullBinaryCode_complete m)).matrixRingEquiv
        ((algebraMap k A).mapMatrix C) from rfl]
    exact RingEquiv.symm_apply_apply _ _
  calc L.wordT (List.ofFn i) * L.balancedEmbed (k := k) m C *
        L.wordS (List.ofFn j)
      = (L.prefixMatrixFamily (fullBinaryCode m)
          (L.fullBinaryCode_complete m)).matrixRingEquiv.symm
          (L.balancedEmbed (k := k) m C) i j := rfl
    -- `mapMatrix` is definitionally `Matrix.map`, so the residual entry
    -- equation is `rfl` -- just not at `rw`'s trailing transparency.
    _ = algebraMap k A (C i j) := by rw [h]; rfl

/-- Split a scalar multiple of a `t`-generator over the two slots. -/
theorem smul_t_expand (z : Fin 2) (α : k) :
    α • L.t z = (if z = 0 then α else 0) • L.t 0 +
      (if z = 1 then α else 0) • L.t 1 := by
  fin_cases z <;> simp

/-- Split a scalar multiple of an `s`-generator over the two slots. -/
theorem smul_s_expand (z : Fin 2) (α : k) :
    α • L.s z = (if z = 0 then α else 0) • L.s 0 +
      (if z = 1 then α else 0) • L.s 1 := by
  fin_cases z <;> simp

/-- The pencil entry of a degree `-1` element: the row word's last
letter pops out as a `t`-generator, the balanced residue is a scalar
entry one level down. -/
theorem pencil_entry_A {m : ℕ}
    (Α₀ Α₁ : Matrix (Fin m → Fin 2) (Fin m → Fin 2) k) (a : A)
    (hsplit : a = L.balancedEmbed (k := k) m Α₀ * L.t 0 +
      L.balancedEmbed (k := k) m Α₁ * L.t 1)
    (i j : Fin (m + 1) → Fin 2) :
    L.wordT (List.ofFn i) * a * L.wordS (List.ofFn j) =
      (if j 0 = 0 then Α₀ (fun r ↦ i r.castSucc) (fun r ↦ j r.succ)
        else Α₁ (fun r ↦ i r.castSucc) (fun r ↦ j r.succ)) •
        L.t (i (Fin.last m)) := by
  have hTi : L.wordT (List.ofFn i) =
      L.t (i (Fin.last m)) *
        L.wordT (List.ofFn fun r ↦ i r.castSucc) := by
    rw [show List.ofFn i =
      (List.ofFn fun r ↦ i r.castSucc) ++ [i (Fin.last m)] from
        (List.ofFn_succ' i).trans List.concat_eq_append,
      wordT_append]
    simp
  have hSj : L.wordS (List.ofFn j) =
      L.s (j 0) * L.wordS (List.ofFn fun r ↦ j r.succ) := by
    rw [List.ofFn_succ, wordS_cons]
  have hterm : ∀ z : Fin 2,
      L.wordT (List.ofFn i) * (L.balancedEmbed (k := k) m
          (if z = 0 then Α₀ else Α₁) * L.t z) *
        L.wordS (List.ofFn j) =
      (if z = j 0 then
        (if z = 0 then Α₀ else Α₁)
          (fun r ↦ i r.castSucc) (fun r ↦ j r.succ) •
          L.t (i (Fin.last m)) else 0) := by
    intro z
    rw [hTi, hSj,
      show L.t (i (Fin.last m)) *
          L.wordT (List.ofFn fun r ↦ i r.castSucc) *
          (L.balancedEmbed (k := k) m (if z = 0 then Α₀ else Α₁) *
            L.t z) *
          (L.s (j 0) * L.wordS (List.ofFn fun r ↦ j r.succ)) =
        L.t (i (Fin.last m)) *
          (L.wordT (List.ofFn fun r ↦ i r.castSucc) *
            L.balancedEmbed (k := k) m (if z = 0 then Α₀ else Α₁)) *
          (L.t z * L.s (j 0)) *
          L.wordS (List.ofFn fun r ↦ j r.succ) from by noncomm_ring,
      t_mul_s]
    by_cases hz : z = j 0
    · rw [if_pos hz, if_pos hz, mul_one,
        show L.t (i (Fin.last m)) *
            (L.wordT (List.ofFn fun r ↦ i r.castSucc) *
              L.balancedEmbed (k := k) m (if z = 0 then Α₀ else Α₁)) *
            L.wordS (List.ofFn fun r ↦ j r.succ) =
          L.t (i (Fin.last m)) *
            (L.wordT (List.ofFn fun r ↦ i r.castSucc) *
              L.balancedEmbed (k := k) m (if z = 0 then Α₀ else Α₁) *
              L.wordS (List.ofFn fun r ↦ j r.succ)) from by noncomm_ring,
        L.wordT_balancedEmbed_wordS (k := k) m _ _ _,
        ← Algebra.commutes, ← Algebra.smul_def]
    · rw [if_neg hz, if_neg hz, mul_zero, zero_mul]
  rw [hsplit, mul_add, add_mul,
    show L.wordT (List.ofFn i) *
        (L.balancedEmbed (k := k) m Α₀ * L.t 0) *
        L.wordS (List.ofFn j) =
      L.wordT (List.ofFn i) * (L.balancedEmbed (k := k) m
        (if (0 : Fin 2) = 0 then Α₀ else Α₁) * L.t 0) *
        L.wordS (List.ofFn j) from by norm_num,
    show L.wordT (List.ofFn i) *
        (L.balancedEmbed (k := k) m Α₁ * L.t 1) *
        L.wordS (List.ofFn j) =
      L.wordT (List.ofFn i) * (L.balancedEmbed (k := k) m
        (if (1 : Fin 2) = 0 then Α₀ else Α₁) * L.t 1) *
        L.wordS (List.ofFn j) from by norm_num,
    hterm 0, hterm 1]
  rcases (by decide : ∀ w : Fin 2, w = 0 ∨ w = 1) (j 0) with hj | hj <;>
    rw [hj] <;> simp

/-- The pencil entry of a degree `+1` element: the column word's last
letter pops out as an `s`-generator. -/
theorem pencil_entry_B {m : ℕ}
    (Β₀ Β₁ : Matrix (Fin m → Fin 2) (Fin m → Fin 2) k) (b : A)
    (hsplit : b = L.s 0 * L.balancedEmbed (k := k) m Β₀ +
      L.s 1 * L.balancedEmbed (k := k) m Β₁)
    (i j : Fin (m + 1) → Fin 2) :
    L.wordT (List.ofFn i) * b * L.wordS (List.ofFn j) =
      (if i 0 = 0 then Β₀ (fun r ↦ i r.succ) (fun r ↦ j r.castSucc)
        else Β₁ (fun r ↦ i r.succ) (fun r ↦ j r.castSucc)) •
        L.s (j (Fin.last m)) := by
  have hTi : L.wordT (List.ofFn i) =
      L.wordT (List.ofFn fun r ↦ i r.succ) * L.t (i 0) := by
    rw [List.ofFn_succ, wordT_cons]
  have hSj : L.wordS (List.ofFn j) =
      L.wordS (List.ofFn fun r ↦ j r.castSucc) *
        L.s (j (Fin.last m)) := by
    rw [show List.ofFn j =
      (List.ofFn fun r ↦ j r.castSucc) ++ [j (Fin.last m)] from
        (List.ofFn_succ' j).trans List.concat_eq_append,
      wordS_append]
    simp
  have hterm : ∀ z : Fin 2,
      L.wordT (List.ofFn i) * (L.s z * L.balancedEmbed (k := k) m
          (if z = 0 then Β₀ else Β₁)) *
        L.wordS (List.ofFn j) =
      (if i 0 = z then
        (if z = 0 then Β₀ else Β₁)
          (fun r ↦ i r.succ) (fun r ↦ j r.castSucc) •
          L.s (j (Fin.last m)) else 0) := by
    intro z
    rw [hTi, hSj,
      show L.wordT (List.ofFn fun r ↦ i r.succ) * L.t (i 0) *
          (L.s z * L.balancedEmbed (k := k) m
            (if z = 0 then Β₀ else Β₁)) *
          (L.wordS (List.ofFn fun r ↦ j r.castSucc) *
            L.s (j (Fin.last m))) =
        L.wordT (List.ofFn fun r ↦ i r.succ) * (L.t (i 0) * L.s z) *
          (L.balancedEmbed (k := k) m (if z = 0 then Β₀ else Β₁) *
            L.wordS (List.ofFn fun r ↦ j r.castSucc)) *
          L.s (j (Fin.last m)) from by noncomm_ring,
      t_mul_s]
    by_cases hz : i 0 = z
    · rw [if_pos hz, if_pos hz,
        show L.wordT (List.ofFn fun r ↦ i r.succ) * 1 *
            (L.balancedEmbed (k := k) m (if z = 0 then Β₀ else Β₁) *
              L.wordS (List.ofFn fun r ↦ j r.castSucc)) *
            L.s (j (Fin.last m)) =
          L.wordT (List.ofFn fun r ↦ i r.succ) *
            L.balancedEmbed (k := k) m (if z = 0 then Β₀ else Β₁) *
            L.wordS (List.ofFn fun r ↦ j r.castSucc) *
            L.s (j (Fin.last m)) from by noncomm_ring,
        L.wordT_balancedEmbed_wordS (k := k) m _ _ _,
        ← Algebra.smul_def]
    · rw [if_neg hz, if_neg hz, mul_zero, zero_mul, zero_mul]
  rw [hsplit, mul_add, add_mul,
    show L.wordT (List.ofFn i) *
        (L.s 0 * L.balancedEmbed (k := k) m Β₀) *
        L.wordS (List.ofFn j) =
      L.wordT (List.ofFn i) * (L.s 0 * L.balancedEmbed (k := k) m
        (if (0 : Fin 2) = 0 then Β₀ else Β₁)) *
        L.wordS (List.ofFn j) from by norm_num,
    show L.wordT (List.ofFn i) *
        (L.s 1 * L.balancedEmbed (k := k) m Β₁) *
        L.wordS (List.ofFn j) =
      L.wordT (List.ofFn i) * (L.s 1 * L.balancedEmbed (k := k) m
        (if (1 : Fin 2) = 0 then Β₀ else Β₁)) *
        L.wordS (List.ofFn j) from by norm_num,
    hterm 0, hterm 1]
  rcases (by decide : ∀ w : Fin 2, w = 0 ∨ w = 1) (i 0) with hi | hi <;>
    rw [hi] <;> simp

end LeavittFamily

namespace BinaryLeavitt

open LeavittFamily

variable (k : Type) [Field k]

/-- **The scalar-pencil form**: every narrow element is, at some corner
level `m + 1`, a word-indexed matrix with entries
`A₀ᵢⱼ•t₀ + A₁ᵢⱼ•t₁ + Cᵢⱼ•1 + B₀ᵢⱼ•s₀ + B₁ᵢⱼ•s₁` for scalar matrices
`A₀, A₁, C, B₀, B₁`. -/
theorem exists_pencil_form (v : BinaryLeavittAlgebra k)
    (hv : v ∈ Submodule.span k ((family k).degreeMonomials (-1) 1)) :
    ∃ (m : ℕ) (A₀ A₁ C B₀ B₁ :
      Matrix (Fin (m + 1) → Fin 2) (Fin (m + 1) → Fin 2) k),
      v = ∑ i, ∑ j, (family k).wordS (List.ofFn i) *
        (A₀ i j • (family k).t 0 + A₁ i j • (family k).t 1 +
          C i j • (1 : BinaryLeavittAlgebra k) +
          (B₀ i j • (family k).s 0 + B₁ i j • (family k).s 1)) *
        (family k).wordT (List.ofFn j) := by
  classical
  set L : LeavittFamily (BinaryLeavittAlgebra k) := family k with hL
  obtain ⟨y, hymem, -, hysum⟩ := exists_components k hv
  have hval : v = y (-1) + (y 0 + y 1) := by
    rw [hysum]
    have hIcc : Finset.Icc (-1 : ℤ) 1 = {-1, 0, 1} := by
      ext d
      simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
      omega
    rw [hIcc, Finset.sum_insert (by simp), Finset.sum_insert (by simp),
      Finset.sum_singleton]
  -- the six balanced pieces
  have hs_mem : ∀ z : Fin 2,
      L.s z ∈ Submodule.span k (L.degreeMonomials 1 1) := fun z ↦
    Submodule.subset_span ⟨[z], [], by simp, by simp, by simp⟩
  have ht_mem : ∀ z : Fin 2,
      L.t z ∈ Submodule.span k (L.degreeMonomials (-1) (-1)) := fun z ↦
    Submodule.subset_span ⟨[], [z], by simp, by simp, by simp⟩
  have haz : ∀ z : Fin 2, y (-1) * L.s z ∈
      Submodule.span k (L.degreeMonomials 0 0) := fun z ↦ by
    have h := L.window_mul_mem_span (k := k) (hymem (-1)) (hs_mem z)
    exact L.span_degreeMonomials_mono (by omega) (by omega) h
  have hbz : ∀ z : Fin 2, L.t z * y 1 ∈
      Submodule.span k (L.degreeMonomials 0 0) := fun z ↦ by
    have h := L.window_mul_mem_span (k := k) (ht_mem z) (hymem 1)
    exact L.span_degreeMonomials_mono (by omega) (by omega) h
  obtain ⟨na0, hna0⟩ := L.span_degree_zero_le_levelSpan (haz 0)
  obtain ⟨na1, hna1⟩ := L.span_degree_zero_le_levelSpan (haz 1)
  obtain ⟨nb0, hnb0⟩ := L.span_degree_zero_le_levelSpan (hbz 0)
  obtain ⟨nb1, hnb1⟩ := L.span_degree_zero_le_levelSpan (hbz 1)
  obtain ⟨nc, hnc⟩ := L.span_degree_zero_le_levelSpan (hymem 0)
  set m : ℕ := max (max (max na0 na1) (max nb0 nb1)) nc with hm
  obtain ⟨Α₀, hΑ₀⟩ := L.exists_balancedEmbed_eq
    (L.span_levelMonomials_mono (show na0 ≤ m by omega) hna0)
  obtain ⟨Α₁, hΑ₁⟩ := L.exists_balancedEmbed_eq
    (L.span_levelMonomials_mono (show na1 ≤ m by omega) hna1)
  obtain ⟨Β₀, hΒ₀⟩ := L.exists_balancedEmbed_eq
    (L.span_levelMonomials_mono (show nb0 ≤ m by omega) hnb0)
  obtain ⟨Β₁, hΒ₁⟩ := L.exists_balancedEmbed_eq
    (L.span_levelMonomials_mono (show nb1 ≤ m by omega) hnb1)
  obtain ⟨Γ, hΓ⟩ := L.exists_balancedEmbed_eq
    (L.span_levelMonomials_mono (show nc ≤ m + 1 by omega) hnc)
  -- the degree `∓1` splits
  have hsplitA : y (-1) = L.balancedEmbed (k := k) m Α₀ * L.t 0 +
      L.balancedEmbed (k := k) m Α₁ * L.t 1 := by
    rw [hΑ₀, hΑ₁]
    calc y (-1) = y (-1) * (L.s 0 * L.t 0 + L.s 1 * L.t 1) := by
          rw [L.sum_s_mul_t, mul_one]
      _ = y (-1) * L.s 0 * L.t 0 + y (-1) * L.s 1 * L.t 1 := by
          noncomm_ring
  have hsplitB : y 1 = L.s 0 * L.balancedEmbed (k := k) m Β₀ +
      L.s 1 * L.balancedEmbed (k := k) m Β₁ := by
    rw [hΒ₀, hΒ₁]
    calc y 1 = (L.s 0 * L.t 0 + L.s 1 * L.t 1) * y 1 := by
          rw [L.sum_s_mul_t, one_mul]
      _ = L.s 0 * (L.t 0 * y 1) + L.s 1 * (L.t 1 * y 1) := by
          noncomm_ring
  refine ⟨m,
    fun i j ↦ if i (Fin.last m) = 0 then
      (if j 0 = 0 then Α₀ (fun r ↦ i r.castSucc) (fun r ↦ j r.succ)
        else Α₁ (fun r ↦ i r.castSucc) (fun r ↦ j r.succ)) else 0,
    fun i j ↦ if i (Fin.last m) = 1 then
      (if j 0 = 0 then Α₀ (fun r ↦ i r.castSucc) (fun r ↦ j r.succ)
        else Α₁ (fun r ↦ i r.castSucc) (fun r ↦ j r.succ)) else 0,
    Γ,
    fun i j ↦ if j (Fin.last m) = 0 then
      (if i 0 = 0 then Β₀ (fun r ↦ i r.succ) (fun r ↦ j r.castSucc)
        else Β₁ (fun r ↦ i r.succ) (fun r ↦ j r.castSucc)) else 0,
    fun i j ↦ if j (Fin.last m) = 1 then
      (if i 0 = 0 then Β₀ (fun r ↦ i r.succ) (fun r ↦ j r.castSucc)
        else Β₁ (fun r ↦ i r.succ) (fun r ↦ j r.castSucc)) else 0,
    ?_⟩
  -- the partition of unity at level `m + 1`
  have hpart : v = ∑ i : Fin (m + 1) → Fin 2, ∑ j : Fin (m + 1) → Fin 2,
      L.wordS (List.ofFn i) *
        (L.wordT (List.ofFn i) * v * L.wordS (List.ofFn j)) *
        L.wordT (List.ofFn j) := by
    have hone := L.sum_cylinder_ofFn (m + 1)
    calc v = 1 * v * 1 := by rw [one_mul, mul_one]
      _ = (∑ i : Fin (m + 1) → Fin 2, L.cylinder (List.ofFn i)) * v *
          (∑ j : Fin (m + 1) → Fin 2, L.cylinder (List.ofFn j)) := by
          rw [hone]
      _ = ∑ i : Fin (m + 1) → Fin 2, ∑ j : Fin (m + 1) → Fin 2,
          L.wordS (List.ofFn i) *
            (L.wordT (List.ofFn i) * v * L.wordS (List.ofFn j)) *
            L.wordT (List.ofFn j) := by
          -- `mul_sum` fires on the outer product first, so the simp leaves
          -- `∑ j, ∑ i, …` -- the opposite nesting to the stated goal.  Swap
          -- the order back before matching the binders, otherwise the two
          -- `sum_congr`s bind crosswise and demand `C j * v * C i = C i * v * C j`.
          simp only [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ ↦
            Finset.sum_congr rfl fun j _ ↦ ?_
          -- pure re-association of the same five factors; `noncomm_ring`
          -- bottoms out in `abel_nf`, which has nothing additive to do
          simp only [cylinder, mul_assoc]
  rw [hpart]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  congr 1
  · congr 1
    beta_reduce
    rw [show L.wordT (List.ofFn i) * v * L.wordS (List.ofFn j) =
        L.wordT (List.ofFn i) * (y (-1) + (y 0 + y 1)) *
          L.wordS (List.ofFn j) from by rw [← hval]]
    simp only [mul_add, add_mul]
    rw [L.pencil_entry_A (k := k) Α₀ Α₁ (y (-1)) hsplitA i j,
      L.pencil_entry_B (k := k) Β₀ Β₁ (y 1) hsplitB i j,
      ← hΓ, L.wordT_balancedEmbed_wordS (k := k) (m + 1) Γ i j,
      Algebra.algebraMap_eq_smul_one,
      L.smul_t_expand (i (Fin.last m)), L.smul_s_expand (j (Fin.last m))]
    abel

end BinaryLeavitt
end NonsoficGroupsExist
