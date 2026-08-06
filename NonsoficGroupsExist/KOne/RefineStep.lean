import NonsoficGroupsExist.KOne.PencilEntryArith
import NonsoficGroupsExist.KOne.CodeChangeGlue

/-!
# The refinement step

A pencil column with no `s`-content splits into its two children:
the same element, over the column code with one word replaced by its
two extensions, carries pencil data in which the split column's
`t`-coefficients descend to constants and its constant coefficients
to `s`-coefficients — the Wiener–Hopf index shift, realized as pure
re-indexing with no multiplication.  This is the move of the stuck
branch.
-/

namespace NonsoficGroupsExist
namespace LeavittFamily

variable {A : Type*} [Ring A] (L : LeavittFamily A)
variable {k : Type*} [Field k] [Algebra k A]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
variable [Fintype κ] [DecidableEq κ]

/-- The split entry identity: a `B`-free pencil entry times `s_z`
is again a pencil entry, with coefficients shifted down. -/
theorem pencilEntry_mul_s (a₀ a₁ c : k) :
    ∀ z : Fin 2,
    (L.pencilEntry (k := k) a₀ a₁ c 0 0 : A) * L.s z =
      L.pencilEntry (k := k) 0 0 (if z = 0 then a₀ else a₁)
        (if z = 0 then c else 0) (if z = 0 then 0 else c) := by
  intro z
  unfold pencilEntry
  -- `pencilEntry` is a four-fold sum, so four `add_mul`s are needed before
  -- the five `smul_mul_assoc`s all have something to match.  `fin_cases`
  -- leaves `z` as `(fun i => i) ⟨0, _⟩`, so the `if_pos`/`if_neg` witnesses
  -- no longer match syntactically; let `simp` discharge the conditions.
  fin_cases z <;>
    rw [add_mul, add_mul, add_mul, add_mul, smul_mul_assoc,
      smul_mul_assoc, smul_mul_assoc, smul_mul_assoc,
      smul_mul_assoc] <;>
    simp

omit [DecidableEq ι] in
/-- **The refinement step**: the pencil value over `(R, C)` with a
`B`-free column `j₀` equals the pencil value over the column code
split at `j₀`, indexed by `Fin 2 ⊕ {j // j ≠ j₀}`, with the shifted
data on the children. -/
theorem refine_column (R : BinaryPrefixCode ι)
    (C : BinaryPrefixCode κ)
    (A₀ A₁ Cm B₀ B₁ : ι → κ → k) (j₀ : κ)
    (hB₀ : ∀ i, B₀ i j₀ = 0) (hB₁ : ∀ i, B₁ i j₀ = 0) :
    (∑ i, ∑ j, L.wordS (R.word i) *
      L.pencilEntry (k := k) (A₀ i j) (A₁ i j) (Cm i j) (B₀ i j)
        (B₁ i j) * L.wordT (C.word j)) =
    ∑ i, ∑ p : Fin 2 ⊕ {j : κ // j ≠ j₀},
      L.wordS (R.word i) *
      (Sum.elim
        (fun z ↦ L.pencilEntry (k := k) 0 0
          (if z = 0 then A₀ i j₀ else A₁ i j₀)
          (if z = 0 then Cm i j₀ else 0)
          (if z = 0 then 0 else Cm i j₀))
        (fun q ↦ L.pencilEntry (k := k) (A₀ i q.1) (A₁ i q.1)
          (Cm i q.1) (B₀ i q.1) (B₁ i q.1)) p) *
      L.wordT ((Sum.elim (fun z ↦ C.word j₀ ++ [z])
        (fun q ↦ C.word q.1)) p) := by
  classical
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  -- split the `j₀`-term off the left side
  rw [← Finset.add_sum_erase _ (fun j ↦ L.wordS (R.word i) *
      L.pencilEntry (k := k) (A₀ i j) (A₁ i j) (Cm i j) (B₀ i j)
        (B₁ i j) * L.wordT (C.word j)) (Finset.mem_univ j₀),
    Fintype.sum_sum_type]
  -- the `j₀`-term splits into the two children
  have hsplit : L.wordS (R.word i) *
      L.pencilEntry (k := k) (A₀ i j₀) (A₁ i j₀) (Cm i j₀) (B₀ i j₀)
        (B₁ i j₀) * L.wordT (C.word j₀) =
      ∑ z : Fin 2, L.wordS (R.word i) *
        L.pencilEntry (k := k) 0 0
          (if z = 0 then A₀ i j₀ else A₁ i j₀)
          (if z = 0 then Cm i j₀ else 0)
          (if z = 0 then 0 else Cm i j₀) *
        L.wordT (C.word j₀ ++ [z]) := by
    have hT : ∀ z : Fin 2, L.wordT (C.word j₀ ++ [z]) =
        L.t z * L.wordT (C.word j₀) := by
      intro z
      rw [wordT_append]
      simp
    rw [Fin.sum_univ_two, hT 0, hT 1, hB₀ i, hB₁ i]
    rw [← L.pencilEntry_mul_s (A₀ i j₀) (A₁ i j₀) (Cm i j₀) 0,
      ← L.pencilEntry_mul_s (A₀ i j₀) (A₁ i j₀) (Cm i j₀) 1]
    calc L.wordS (R.word i) *
          L.pencilEntry (k := k) (A₀ i j₀) (A₁ i j₀) (Cm i j₀) 0 0 *
          L.wordT (C.word j₀)
        = L.wordS (R.word i) *
            (L.pencilEntry (k := k) (A₀ i j₀) (A₁ i j₀) (Cm i j₀) 0 0 *
              ((L.s 0 * L.t 0 + L.s 1 * L.t 1) *
                L.wordT (C.word j₀))) := by
          rw [L.sum_s_mul_t, one_mul, mul_assoc]
      _ = L.wordS (R.word i) *
            (L.pencilEntry (k := k) (A₀ i j₀) (A₁ i j₀) (Cm i j₀) 0 0 *
              L.s 0) * (L.t 0 * L.wordT (C.word j₀)) +
          L.wordS (R.word i) *
            (L.pencilEntry (k := k) (A₀ i j₀) (A₁ i j₀) (Cm i j₀) 0 0 *
              L.s 1) * (L.t 1 * L.wordT (C.word j₀)) := by
          noncomm_ring
  rw [hsplit]
  -- match the two summand families
  -- `Sum.elim … (inl z)` reduces, so `congr 1` closes the `Fin 2` family by
  -- `rfl` on its own and leaves only the `erase j₀` vs subtype reindexing.
  congr 1
  · refine (Finset.sum_bij' (i := fun (q : {j : κ // j ≠ j₀}) _ ↦ q.1)
      (j := fun j hj ↦ (⟨j, (Finset.mem_erase.mp hj).1⟩ :
        {j : κ // j ≠ j₀})) ?_ ?_ ?_ ?_ ?_).symm
    · intro q _
      exact Finset.mem_erase.mpr ⟨q.2, Finset.mem_univ _⟩
    · intro j _
      exact Finset.mem_univ _
    · intro q _
      rfl
    · intro j _
      rfl
    · intro q _
      rfl

end LeavittFamily
end NonsoficGroupsExist
