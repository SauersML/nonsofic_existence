import NonsoficGroupsExist.NarrowDischarge
import NonsoficGroupsExist.StrictNegativePencil
import NonsoficGroupsExist.CodeShapeSupply
import NonsoficGroupsExist.PencilReshape
import NonsoficGroupsExist.RefineStep
import NonsoficGroupsExist.GLVectorNormalization
import NonsoficGroupsExist.WindowNonposReduction

/-!
# The refine-loop discharge: `NarrowReduction` holds outright

The session-54 algorithm.  A pencil unit whose row code has `2^r`
words is reduced by a single loop on the column count: while the
column stack `[B₀; B₁]` has a kernel, a scalar column move makes a
`B`-free column and the refinement step splits it, growing the column
code at a *fixed* row code; the loop counter `2^(r+1) − κ` strictly
decreases.  The two ways out are value-window exits: at
`κ ≥ 2^(r+1)` a reshape to a shallow row code and a deep column code
makes the value nonpositive (free exit); when the stack goes full,
strict negativity of the inverse entries makes the *inverse* value
nonpositive over a shallow column code and a deep row code.  Both
land in `window_nonpos_mem_stableUnits`.  No extraction, no
termination measure beyond a bounded counter.
-/

namespace NonsoficGroupsExist
namespace LeavittFamily

variable {A : Type*} [Ring A] (L : LeavittFamily A)
variable {k : Type} [Field k] [Algebra k A]

/-- A pencil entry is a narrow-window element. -/
theorem pencilEntry_mem_window (a₀ a₁ c b₀ b₁ : k) :
    L.pencilEntry (k := k) a₀ a₁ c b₀ b₁ ∈
      Submodule.span k (L.degreeMonomials (-1) 1) := by
  unfold pencilEntry
  refine Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.add_mem _ (Submodule.smul_mem _ _ ?_)
      (Submodule.smul_mem _ _ ?_)) (Submodule.smul_mem _ _ ?_))
    (Submodule.add_mem _ (Submodule.smul_mem _ _ ?_)
      (Submodule.smul_mem _ _ ?_))
  · exact Submodule.subset_span ⟨[], [0], by simp, by simp, by simp⟩
  · exact Submodule.subset_span ⟨[], [1], by simp, by simp, by simp⟩
  · exact L.span_degreeMonomials_mono (by omega) (by omega)
      (L.one_mem_window (k := k))
  · exact Submodule.subset_span ⟨[0], [], by simp, by simp, by simp⟩
  · exact Submodule.subset_span ⟨[1], [], by simp, by simp, by simp⟩

/-- **Code-pair expansion**: any element is the transport of its
corner-entry matrix along a pair of complete codes. -/
theorem codePair_expansion {ι κ : Type*} [Fintype ι] [Fintype κ]
    (C : BinaryPrefixCode κ) (hC : L.IsComplete C)
    (R : BinaryPrefixCode ι) (hR : L.IsComplete R) (x : A) :
    x = ∑ j, ∑ i, L.wordS (C.word j) *
      (L.wordT (C.word j) * x * L.wordS (R.word i)) *
      L.wordT (R.word i) := by
  calc x = (∑ j, L.cylinder (C.word j)) * x *
      (∑ i, L.cylinder (R.word i)) := by
        rw [hC, hR, one_mul, mul_one]
    _ = ∑ j, ∑ i, L.wordS (C.word j) *
        (L.wordT (C.word j) * x * L.wordS (R.word i)) *
        L.wordT (R.word i) := by
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        show L.wordS (C.word j) * L.wordT (C.word j) * x *
          (L.wordS (R.word i) * L.wordT (R.word i)) = _
        noncomm_ring

end LeavittFamily

namespace BinaryLeavitt

open LeavittFamily MatrixDiagonalization

variable (k : Type) [Field k]

/-- **The free exit**: once the column code outweighs the row code by
the aspect threshold, reshaping (shallow rows, deep columns) makes the
pencil value nonpositive, and the window theorem applies. -/
theorem pencil_free_exit [Nontrivial (BinaryLeavittAlgebra k)]
    (hdiv : ∀ x : BinaryLeavittAlgebra k, x ≠ 0 →
      ∃ p q : BinaryLeavittAlgebra k, p * x * q = 1)
    (r : ℕ) {ιT κT : Type} [Fintype ιT] [DecidableEq ιT]
    [Fintype κT] [DecidableEq κT]
    (hι1 : 1 ≤ Fintype.card ιT) (hι : Fintype.card ιT ≤ 2 ^ r)
    (hκ : 2 ^ (r + 1) ≤ Fintype.card κT)
    (R : BinaryPrefixCode ιT) (hR : (family k).IsComplete R)
    (C : BinaryPrefixCode κT) (hC : (family k).IsComplete C)
    (A₀ A₁ Cm B₀ B₁ : ιT → κT → k) (u : (BinaryLeavittAlgebra k)ˣ)
    (hu : (u : BinaryLeavittAlgebra k) = ∑ i, ∑ j,
      (family k).wordS (R.word i) *
      (family k).pencilEntry (k := k) (A₀ i j) (A₁ i j) (Cm i j)
        (B₀ i j) (B₁ i j) * (family k).wordT (C.word j)) :
    u ∈ stableUnits (BinaryLeavittAlgebra k) := by
  classical
  -- shallow row code of the same size
  obtain ⟨Pf, hPfc, hPfd⟩ := (family k).exists_shallow_code r
    (Fintype.card ιT) hι1 hι
  obtain ⟨hPfree, hPsum⟩ := (family k).family_transport
    (Fintype.equivFin ιT) Pf.word Pf.prefix_free hPfc
  set P : BinaryPrefixCode ιT := ⟨Pf.word ∘ Fintype.equivFin ιT,
    hPfree⟩ with hP
  -- deep column code of the same size
  obtain ⟨Qf, hQfc, hQfd⟩ := (family k).exists_deep_code (r + 1)
    (Fintype.card κT) hκ
  obtain ⟨hQfree, hQsum⟩ := (family k).family_transport
    (Fintype.equivFin κT) Qf.word Qf.prefix_free hQfc
  set Q : BinaryPrefixCode κT := ⟨Qf.word ∘ Fintype.equivFin κT,
    hQfree⟩ with hQ
  obtain ⟨v, hv, hiff⟩ := (family k).exists_reshaped_pencil (k := k)
    hdiv R P hR hPsum C Q hC hQsum
    (fun i j ↦ (family k).pencilEntry (k := k) (A₀ i j) (A₁ i j)
      (Cm i j) (B₀ i j) (B₁ i j)) u hu
  refine hiff.mpr ?_
  set N : ℕ := Finset.univ.sup fun j : κT ↦ (Q.word j).length with hN
  refine window_nonpos_mem_stableUnits k N v ?_
  rw [hv]
  refine (family k).pencilVal_window_mem (k := k)
    (a := -1) (b := 1) P Q _
    (fun i j ↦ (family k).pencilEntry_mem_window (k := k) _ _ _ _ _)
    ?_ ?_
  · intro i j
    have h1 : (Q.word j).length ≤ N :=
      Finset.le_sup (Finset.mem_univ j)
    omega
  · intro i j
    have h1 : (P.word i).length ≤ r :=
      hPfd (Fintype.equivFin ιT i)
    have h2 : r + 1 ≤ (Q.word j).length :=
      hQfd (Fintype.equivFin κT j)
    omega

/-- **The full-stack exit**: a scalar left inverse of `[B₀; B₁]` pins
the inverse entries strictly negative; reshaping the inverse (shallow
columns, deep rows) makes its value nonpositive. -/
theorem pencil_full_exit [Nontrivial (BinaryLeavittAlgebra k)]
    (hdiv : ∀ x : BinaryLeavittAlgebra k, x ≠ 0 →
      ∃ p q : BinaryLeavittAlgebra k, p * x * q = 1)
    (r : ℕ) {ιT κT : Type} [Fintype ιT] [DecidableEq ιT]
    [Fintype κT] [DecidableEq κT]
    (hι : 2 ^ r ≤ Fintype.card ιT)
    (hκ1 : 1 ≤ Fintype.card κT)
    (hκ : Fintype.card κT ≤ 2 ^ (r + 1))
    (R : BinaryPrefixCode ιT) (hR : (family k).IsComplete R)
    (C : BinaryPrefixCode κT) (hC : (family k).IsComplete C)
    (A₀ A₁ Cm B₀ B₁ : ιT → κT → k) (u : (BinaryLeavittAlgebra k)ˣ)
    (hu : (u : BinaryLeavittAlgebra k) = ∑ i, ∑ j,
      (family k).wordS (R.word i) *
      (family k).pencilEntry (k := k) (A₀ i j) (A₁ i j) (Cm i j)
        (B₀ i j) (B₁ i j) * (family k).wordT (C.word j))
    (G₀ G₁ : κT → ιT → k)
    (hG : ∀ j j' : κT, (∑ i, (G₀ j i * B₀ i j' + G₁ j i * B₁ i j')) =
      if j = j' then 1 else 0) :
    u ∈ stableUnits (BinaryLeavittAlgebra k) := by
  classical
  obtain ⟨N, hX⟩ := entry_window_negative_of_B_full k R C hC
    A₀ A₁ Cm B₀ B₁ u hu G₀ G₁ hG
  have hexp := (family k).codePair_expansion C hC R hR
    ((u⁻¹ : (BinaryLeavittAlgebra k)ˣ) : BinaryLeavittAlgebra k)
  -- shallow column code, deep row code
  obtain ⟨Qf, hQfc, hQfd⟩ := (family k).exists_shallow_code (r + 1)
    (Fintype.card κT) hκ1 hκ
  obtain ⟨hQfree, hQsum⟩ := (family k).family_transport
    (Fintype.equivFin κT) Qf.word Qf.prefix_free hQfc
  set Q : BinaryPrefixCode κT := ⟨Qf.word ∘ Fintype.equivFin κT,
    hQfree⟩ with hQ
  obtain ⟨Pf, hPfc, hPfd⟩ := (family k).exists_deep_code r
    (Fintype.card ιT) hι
  obtain ⟨hPfree, hPsum⟩ := (family k).family_transport
    (Fintype.equivFin ιT) Pf.word Pf.prefix_free hPfc
  set P : BinaryPrefixCode ιT := ⟨Pf.word ∘ Fintype.equivFin ιT,
    hPfree⟩ with hP
  obtain ⟨v, hv, hiff⟩ := (family k).exists_reshaped_pencil (k := k)
    hdiv C Q hC hQsum R P hR hPsum
    (fun j i ↦ (family k).wordT (C.word j) *
      ((u⁻¹ : (BinaryLeavittAlgebra k)ˣ) : BinaryLeavittAlgebra k) *
      (family k).wordS (R.word i)) u⁻¹ hexp
  refine inv_mem_iff.mp (hiff.mpr ?_)
  set M : ℕ := Finset.univ.sup fun i : ιT ↦ (P.word i).length with hM
  refine window_nonpos_mem_stableUnits k (N + M) v ?_
  rw [hv]
  refine (family k).pencilVal_window_mem (k := k)
    (a := -(N : ℤ)) (b := -1) Q P _ (fun j i ↦ hX j i) ?_ ?_
  · intro j i
    have h1 : (P.word i).length ≤ M :=
      Finset.le_sup (Finset.mem_univ i)
    push_cast
    omega
  · intro j i
    have h1 : (Q.word j).length ≤ r + 1 :=
      hQfd (Fintype.equivFin κT j)
    have h2 : r ≤ (P.word i).length :=
      hPfd (Fintype.equivFin ιT i)
    omega

/-- **The refine loop**: every pencil unit whose row code has `2^r`
words lies in the diagonal class group. -/
theorem pencil_unit_mem_pow [Nontrivial (BinaryLeavittAlgebra k)]
    (hdiv : ∀ x : BinaryLeavittAlgebra k, x ≠ 0 →
      ∃ p q : BinaryLeavittAlgebra k, p * x * q = 1) (r : ℕ) :
    ∀ n : ℕ, ∀ {κT : Type} [Fintype κT] [DecidableEq κT],
    2 ^ (r + 1) ≤ Fintype.card κT + n →
    ∀ {ιT : Type} [Fintype ιT] [DecidableEq ιT],
    Fintype.card ιT = 2 ^ r →
    ∀ (R : BinaryPrefixCode ιT), (family k).IsComplete R →
    ∀ (C : BinaryPrefixCode κT), (family k).IsComplete C →
    ∀ (A₀ A₁ Cm B₀ B₁ : ιT → κT → k) (u : (BinaryLeavittAlgebra k)ˣ),
    (u : BinaryLeavittAlgebra k) = (∑ i, ∑ j,
      (family k).wordS (R.word i) *
      (family k).pencilEntry (k := k) (A₀ i j) (A₁ i j) (Cm i j)
        (B₀ i j) (B₁ i j) * (family k).wordT (C.word j)) →
    u ∈ stableUnits (BinaryLeavittAlgebra k) := by
  intro n
  induction n with
  | zero =>
      intro κT _ _ hn ιT _ _ hι R hR C hC A₀ A₁ Cm B₀ B₁ u hu
      exact pencil_free_exit k hdiv r
        (by rw [hι]; exact Nat.one_le_two_pow) (le_of_eq hι)
        (by omega) R hR C hC A₀ A₁ Cm B₀ B₁ u hu
  | succ m ih =>
      intro κT _ _ hn ιT _ _ hι R hR C hC A₀ A₁ Cm B₀ B₁ u hu
      classical
      by_cases hbig : 2 ^ (r + 1) ≤ Fintype.card κT
      · exact pencil_free_exit k hdiv r
          (by rw [hι]; exact Nat.one_le_two_pow) (le_of_eq hι)
          hbig R hR C hC A₀ A₁ Cm B₀ B₁ u hu
      by_cases hκ0 : Fintype.card κT = 0
      · exfalso
        have hu0 : (u : BinaryLeavittAlgebra k) = 0 := by
          rw [hu]
          refine Finset.sum_eq_zero fun i _ ↦
            Finset.sum_eq_zero fun j _ ↦ ?_
          exact (Fintype.card_eq_zero_iff.mp hκ0).elim j
        exact one_ne_zero (by rw [← u.mul_inv, hu0, zero_mul])
      rcases stack_left_inverse_or_kernel B₀ B₁ with
        ⟨G₀, G₁, hG⟩ | ⟨v₀, hv₀, hkB₀, hkB₁⟩
      · -- full stack: strict-negativity exit
        exact pencil_full_exit k hdiv r (le_of_eq hι.symm)
          (by omega) (by omega) R hR C hC A₀ A₁ Cm B₀ B₁ u hu G₀ G₁
          hG
      · -- kernel: normalize a `B`-free column and refine
        set L : LeavittFamily (BinaryLeavittAlgebra k) := family k
          with hL
        obtain ⟨j₀, -⟩ := Function.ne_iff.mp hv₀
        obtain ⟨G, hGu, hGcol⟩ := exists_isUnit_matrix_col hv₀ j₀
        have hGent : ∀ l, G l j₀ = v₀ l := by
          intro l
          have h := congrFun hGcol l
          simp only [Matrix.mulVec_single, MulOpposite.op_one,
            one_smul, Matrix.col_apply] at h
          exact h
        obtain ⟨Gm, hGm⟩ := id hGu
        set uG : (BinaryLeavittAlgebra k)ˣ :=
          ⟨L.codeScalar (k := k) C G,
           L.codeScalar (k := k) C
             ((Gm⁻¹ : (Matrix κT κT k)ˣ) : Matrix κT κT k),
           by rw [L.codeScalar_mul, ← hGm, Units.mul_inv,
             L.codeScalar_one C hC],
           by rw [L.codeScalar_mul, ← hGm, Units.inv_mul,
             L.codeScalar_one C hC]⟩ with huG
        have huGmem : uG ∈ stableUnits (BinaryLeavittAlgebra k) :=
          L.codeScalar_unit_mem hdiv C hC G hGu uG rfl
        set u1 : (BinaryLeavittAlgebra k)ˣ := u * uG with hu1def
        have hu1 : (u1 : BinaryLeavittAlgebra k) =
            ∑ i, ∑ j, L.wordS (R.word i) *
            L.pencilEntry (k := k) (∑ l, A₀ i l * G l j)
              (∑ l, A₁ i l * G l j) (∑ l, Cm i l * G l j)
              (∑ l, B₀ i l * G l j) (∑ l, B₁ i l * G l j) *
            L.wordT (C.word j) := by
          rw [Units.val_mul, hu]
          exact L.pencilVal_mul_codeScalar R C A₀ A₁ Cm B₀ B₁ G
        -- the normalized column is `B`-free
        have hB₀col : ∀ i, (∑ l, B₀ i l * G l j₀) = 0 := by
          intro i
          rw [Finset.sum_congr rfl fun l _ ↦ by rw [hGent l]]
          exact hkB₀ i
        have hB₁col : ∀ i, (∑ l, B₁ i l * G l j₀) = 0 := by
          intro i
          rw [Finset.sum_congr rfl fun l _ ↦ by rw [hGent l]]
          exact hkB₁ i
        -- refine the column
        have hrc := L.refine_column R C
          (fun i j ↦ ∑ l, A₀ i l * G l j)
          (fun i j ↦ ∑ l, A₁ i l * G l j)
          (fun i j ↦ ∑ l, Cm i l * G l j)
          (fun i j ↦ ∑ l, B₀ i l * G l j)
          (fun i j ↦ ∑ l, B₁ i l * G l j) j₀ hB₀col hB₁col
        beta_reduce at hrc
        set C' : BinaryPrefixCode (Fin 2 ⊕ {j : κT // j ≠ j₀}) :=
          ⟨Sum.elim (fun z ↦ C.word j₀ ++ [z]) (fun q ↦ C.word q.1),
           split_family_free C.word C.prefix_free j₀⟩ with hC'def
        have hC' : L.IsComplete C' :=
          L.split_family_sum C.word hC j₀
        set A₀' : ιT → (Fin 2 ⊕ {j : κT // j ≠ j₀}) → k :=
          fun i p ↦ Sum.elim (fun _ ↦ 0)
            (fun q ↦ ∑ l, A₀ i l * G l q.1) p with hA₀'
        set A₁' : ιT → (Fin 2 ⊕ {j : κT // j ≠ j₀}) → k :=
          fun i p ↦ Sum.elim (fun _ ↦ 0)
            (fun q ↦ ∑ l, A₁ i l * G l q.1) p with hA₁'
        set Cm' : ιT → (Fin 2 ⊕ {j : κT // j ≠ j₀}) → k :=
          fun i p ↦ Sum.elim (fun z ↦ if z = 0 then
              (∑ l, A₀ i l * G l j₀) else (∑ l, A₁ i l * G l j₀))
            (fun q ↦ ∑ l, Cm i l * G l q.1) p with hCm'
        set B₀' : ιT → (Fin 2 ⊕ {j : κT // j ≠ j₀}) → k :=
          fun i p ↦ Sum.elim (fun z ↦ if z = 0 then
              (∑ l, Cm i l * G l j₀) else 0)
            (fun q ↦ ∑ l, B₀ i l * G l q.1) p with hB₀'
        set B₁' : ιT → (Fin 2 ⊕ {j : κT // j ≠ j₀}) → k :=
          fun i p ↦ Sum.elim (fun z ↦ if z = 0 then 0 else
              (∑ l, Cm i l * G l j₀))
            (fun q ↦ ∑ l, B₁ i l * G l q.1) p with hB₁'
        have hu1' : (u1 : BinaryLeavittAlgebra k) =
            ∑ i, ∑ p, L.wordS (R.word i) *
            L.pencilEntry (k := k) (A₀' i p) (A₁' i p) (Cm' i p)
              (B₀' i p) (B₁' i p) * L.wordT (C'.word p) := by
          rw [hu1, hrc]
          refine Finset.sum_congr rfl fun i _ ↦
            Finset.sum_congr rfl fun p _ ↦ ?_
          rcases p with z | q <;> rfl
        have hcard : Fintype.card (Fin 2 ⊕ {j : κT // j ≠ j₀}) =
            Fintype.card κT + 1 := by
          rw [Fintype.card_sum, Fintype.card_subtype_compl,
            Fintype.card_subtype_eq]
          simp only [Fintype.card_fin]
          omega
        have hmem1 : u1 ∈ stableUnits (BinaryLeavittAlgebra k) := by
          refine ih (κT := Fin 2 ⊕ {j : κT // j ≠ j₀})
            (by rw [hcard]; omega) hι R hR C' hC'
            A₀' A₁' Cm' B₀' B₁' u1 hu1'
        have hueq : u = u1 * uG⁻¹ := by
          rw [hu1def]
          group
        rw [hueq]
        exact mul_mem hmem1 (inv_mem huGmem)

/-- **The narrow reduction holds unconditionally**: the entire
`K₁`-vanishing chain closes with no residual hypothesis. -/
theorem narrowReduction_holds
    [Nontrivial (BinaryLeavittAlgebra k)] : NarrowReduction k := by
  intro u hu
  have hdiv : ∀ x : BinaryLeavittAlgebra k, x ≠ 0 →
      ∃ p q : BinaryLeavittAlgebra k, p * x * q = 1 :=
    fun x hx ↦ exists_mul_mul_eq_one k hx
  obtain ⟨m, A₀, A₁, Cm, B₀, B₁, hval⟩ := exists_pencil_form k _ hu
  have hcard : Fintype.card (Fin (m + 1) → Fin 2) = 2 ^ (m + 1) := by
    simp [Fintype.card_fun]
  have hmem : u ∈ stableUnits (BinaryLeavittAlgebra k) := by
    refine pencil_unit_mem_pow k hdiv (m + 1) (2 ^ (m + 2))
      (by rw [hcard]; omega) hcard
      (fullBinaryCode (m + 1))
      ((family k).fullBinaryCode_complete (m + 1))
      (fullBinaryCode (m + 1))
      ((family k).fullBinaryCode_complete (m + 1))
      A₀ A₁ Cm B₀ B₁ u ?_
    rw [hval]
    rfl
  exact stableUnits_le_centralClassGroup hmem

/-- The stuck-branch reduction of the master induction follows a
fortiori — its hypotheses are simply not needed. -/
theorem stuckReduction_from_loop
    [Nontrivial (BinaryLeavittAlgebra k)]
    {ιT κT : Type} [Fintype ιT] [DecidableEq ιT]
    [Fintype κT] [DecidableEq κT]
    (hι : ∃ r : ℕ, Fintype.card ιT = 2 ^ r)
    (hdiv : ∀ x : BinaryLeavittAlgebra k, x ≠ 0 →
      ∃ p q : BinaryLeavittAlgebra k, p * x * q = 1)
    (R : BinaryPrefixCode ιT) (hR : (family k).IsComplete R)
    (C : BinaryPrefixCode κT) (hC : (family k).IsComplete C)
    (A₀ A₁ Cm B₀ B₁ : ιT → κT → k) (u : (BinaryLeavittAlgebra k)ˣ)
    (hu : (u : BinaryLeavittAlgebra k) = ∑ i, ∑ j,
      (family k).wordS (R.word i) *
      (family k).pencilEntry (k := k) (A₀ i j) (A₁ i j) (Cm i j)
        (B₀ i j) (B₁ i j) * (family k).wordT (C.word j)) :
    u ∈ stableUnits (BinaryLeavittAlgebra k) := by
  obtain ⟨r, hr⟩ := hι
  exact pencil_unit_mem_pow k hdiv r (2 ^ (r + 1)) (by omega) hr
    R hR C hC A₀ A₁ Cm B₀ B₁ u hu

/-- **`ScalarReduction` holds unconditionally** — the manuscript's
`K₁ = 0` input, closed. -/
theorem scalarReduction_holds [Nontrivial (BinaryLeavittAlgebra k)] :
    ScalarReduction (BinaryLeavittAlgebra k) :=
  scalarReduction_of_narrowReduction k (narrowReduction_holds k)

/-- **Checkpoint `B4` holds unconditionally**: every unit is
stable. -/
theorem stableUnits_eq_top_holds
    [Nontrivial (BinaryLeavittAlgebra k)] :
    ∀ u : (BinaryLeavittAlgebra k)ˣ,
      u ∈ stableUnits (BinaryLeavittAlgebra k) :=
  stableUnits_eq_top_of_narrowReduction k (narrowReduction_holds k)

/-- **`GL₂ = EL₂` holds unconditionally.** -/
theorem glTwo_eq_elementary_holds
    [Nontrivial (BinaryLeavittAlgebra k)]
    (M : (Matrix (Fin 2) (Fin 2) (BinaryLeavittAlgebra k))ˣ) :
    M ∈ elementaryGroup (Fin 2) (BinaryLeavittAlgebra k) :=
  glTwo_eq_elementary_of_narrowReduction k (narrowReduction_holds k) M

/-- **`GL₄ = EL₄` holds unconditionally.** -/
theorem glFour_eq_elementary_holds
    [Nontrivial (BinaryLeavittAlgebra k)]
    (M : (Matrix (Fin 4) (Fin 4) (BinaryLeavittAlgebra k))ˣ) :
    M ∈ elementaryGroup (Fin 4) (BinaryLeavittAlgebra k) :=
  glFour_eq_elementary_of_narrowReduction k (narrowReduction_holds k)
    M

end BinaryLeavitt
end NonsoficGroupsExist
