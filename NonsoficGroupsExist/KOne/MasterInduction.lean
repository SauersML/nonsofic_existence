import NonsoficGroupsExist.KOne.FullExtraction
import NonsoficGroupsExist.KOne.MirrorExtraction
import NonsoficGroupsExist.KOne.EntrywiseKillMirror
import NonsoficGroupsExist.KOne.BalancedCodePencil
import NonsoficGroupsExist.KOne.StackDichotomy

/-!
# The master induction

Strong induction on the total code size.  At each pencil unit:
if a kernel vector of the column stack `[B₀; B₁; C]` exists, the
extraction step removes a row; mirror for the row stack; if the
`C`-less column stack admits a scalar left inverse *and* the `C`-less
row stack a scalar right inverse, the two entrywise kills pin the
inverse's entries to the balanced span and the terminal theorem
applies.  The single remaining configuration — a `C`-less kernel
whose every extension meets the constant data — is the refinement
branch, isolated here as the named hypothesis `StuckReduction`.
-/

namespace NonsoficGroupsExist
namespace BinaryLeavitt

open LeavittFamily MatrixDiagonalization

variable (k : Type) [Field k]

/-- **The stuck-branch reduction** (to be discharged by the
refinement termination argument): a pencil unit admitting no
extraction on either side lies in the class group. -/
def StuckReduction : Prop :=
  ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ],
  ∀ (R : BinaryPrefixCode ι), (family k).IsComplete R →
  ∀ (C : BinaryPrefixCode κ), (family k).IsComplete C →
  ∀ (A₀ A₁ Cm B₀ B₁ : ι → κ → k) (u : (BinaryLeavittAlgebra k)ˣ),
  (u : BinaryLeavittAlgebra k) = (∑ i, ∑ j,
    (family k).wordS (R.word i) *
    (family k).pencilEntry (k := k) (A₀ i j) (A₁ i j) (Cm i j)
      (B₀ i j) (B₁ i j) * (family k).wordT (C.word j)) →
  ¬(∃ v₀ : κ → k, v₀ ≠ 0 ∧ (∀ i, ∑ j, B₀ i j * v₀ j = 0) ∧
    (∀ i, ∑ j, B₁ i j * v₀ j = 0) ∧ (∀ i, ∑ j, Cm i j * v₀ j = 0)) →
  ¬(∃ u₀ : ι → k, u₀ ≠ 0 ∧ (∀ j, ∑ i, A₀ i j * u₀ i = 0) ∧
    (∀ j, ∑ i, A₁ i j * u₀ i = 0) ∧ (∀ j, ∑ i, Cm i j * u₀ i = 0)) →
  ((∃ v₀ : κ → k, v₀ ≠ 0 ∧ (∀ i, ∑ j, B₀ i j * v₀ j = 0) ∧
    (∀ i, ∑ j, B₁ i j * v₀ j = 0)) ∨
   (∃ u₀ : ι → k, u₀ ≠ 0 ∧ (∀ j, ∑ i, A₀ i j * u₀ i = 0) ∧
    (∀ j, ∑ i, A₁ i j * u₀ i = 0))) →
  u ∈ stableUnits (BinaryLeavittAlgebra k)

/-- **The master induction**: every pencil unit over a pair of
complete codes lies in the class group, given the stuck-branch
reduction. -/
theorem pencil_unit_mem [Nontrivial (BinaryLeavittAlgebra k)]
    (hdiv : ∀ x : BinaryLeavittAlgebra k, x ≠ 0 →
      ∃ p q : BinaryLeavittAlgebra k, p * x * q = 1)
    (hstuck : StuckReduction k) :
    ∀ n : ℕ, ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι]
      [Fintype κ] [DecidableEq κ],
    Fintype.card ι + Fintype.card κ ≤ n →
    ∀ (R : BinaryPrefixCode ι), (family k).IsComplete R →
    ∀ (C : BinaryPrefixCode κ), (family k).IsComplete C →
    ∀ (A₀ A₁ Cm B₀ B₁ : ι → κ → k) (u : (BinaryLeavittAlgebra k)ˣ),
    (u : BinaryLeavittAlgebra k) = (∑ i, ∑ j,
      (family k).wordS (R.word i) *
      (family k).pencilEntry (k := k) (A₀ i j) (A₁ i j) (Cm i j)
        (B₀ i j) (B₁ i j) * (family k).wordT (C.word j)) →
    u ∈ stableUnits (BinaryLeavittAlgebra k) := by
  intro n
  induction n with
  | zero =>
      intro ι κ _ _ _ _ hcard R hR C hC A₀ A₁ Cm B₀ B₁ u hu
      -- an empty index type makes the value `0`, impossible for a unit
      exfalso
      have hι : Fintype.card ι = 0 := by omega
      have hu0 : (u : BinaryLeavittAlgebra k) = 0 := by
        rw [hu]
        refine Finset.sum_eq_zero fun i _ ↦ ?_
        -- card zero says `ι` is empty, so the bound `i` is already absurd;
        -- rewriting `univ` to `∅` never applies to `i ∉ univ`.
        exact (Fintype.card_eq_zero_iff.mp hι).elim i
      have h1 : (1 : BinaryLeavittAlgebra k) = 0 := by
        rw [← u.mul_inv, hu0, zero_mul]
      exact one_ne_zero h1
  | succ m ih =>
      intro ι κ _ _ _ _ hcard R hR C hC A₀ A₁ Cm B₀ B₁ u hu
      classical
      -- degenerate sizes
      by_cases hι0 : Fintype.card ι = 0
      · exfalso
        have hu0 : (u : BinaryLeavittAlgebra k) = 0 := by
          rw [hu]
          refine Finset.sum_eq_zero fun i _ ↦ ?_
          exact (Fintype.card_eq_zero_iff.mp hι0).elim i
        exact one_ne_zero (by rw [← u.mul_inv, hu0, zero_mul])
      -- branch 1: column extraction
      by_cases hextT : ∃ v₀ : κ → k, v₀ ≠ 0 ∧
          (∀ i, ∑ j, B₀ i j * v₀ j = 0) ∧
          (∀ i, ∑ j, B₁ i j * v₀ j = 0) ∧
          (∀ i, ∑ j, Cm i j * v₀ j = 0)
      · obtain ⟨v₀, hv₀, hkB₀, hkB₁, hkC⟩ := hextT
        obtain ⟨i₂, D, A₀', A₁', Cm', B₀', B₁', u₂, hDfree, hDsum,
            hval, hiff⟩ :=
          (family k).full_extraction hdiv R hR C hC A₀ A₁ Cm B₀ B₁
            u hu v₀ hv₀ hkB₀ hkB₁ hkC
        refine hiff.mpr ?_
        refine ih (ι := {i : ι // i ≠ i₂}) (κ := κ) ?_
          ⟨D, hDfree⟩ hDsum C hC A₀' A₁' Cm' B₀' B₁' u₂ hval
        have h1 : Fintype.card {i : ι // i ≠ i₂} =
            Fintype.card ι - 1 := by
          rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
        omega
      -- branch 2: row extraction
      by_cases hextS : ∃ u₀ : ι → k, u₀ ≠ 0 ∧
          (∀ j, ∑ i, A₀ i j * u₀ i = 0) ∧
          (∀ j, ∑ i, A₁ i j * u₀ i = 0) ∧
          (∀ j, ∑ i, Cm i j * u₀ i = 0)
      · obtain ⟨u₀, hu₀, hkA₀, hkA₁, hkC⟩ := hextS
        obtain ⟨j₂, D, A₀', A₁', Cm', B₀', B₁', u₂, hDfree, hDsum,
            hval, hiff⟩ :=
          mirror_extraction k hdiv R hR C hC A₀ A₁ Cm B₀ B₁ u hu
            u₀ hu₀ hkA₀ hkA₁ hkC
        refine hiff.mpr ?_
        refine ih (ι := ι) (κ := {j : κ // j ≠ j₂}) ?_
          R hR ⟨D, hDfree⟩ hDsum A₀' A₁' Cm' B₀' B₁' u₂ hval
        have h1 : Fintype.card {j : κ // j ≠ j₂} =
            Fintype.card κ - 1 := by
          rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
        have h2 : 1 ≤ Fintype.card κ := Fintype.card_pos_iff.mpr
          ⟨j₂⟩
        omega
      -- the C-less stack dichotomies
      rcases stack_left_inverse_or_kernel B₀ B₁ with
        ⟨G₀, G₁, hG⟩ | hkerB
      · rcases stack_left_inverse_or_kernel
          (fun (j : κ) (i : ι) ↦ A₀ i j)
          (fun (j : κ) (i : ι) ↦ A₁ i j) with
          ⟨H₀, H₁, hH⟩ | hkerA
        · -- both stacks full: the terminal
          obtain ⟨N, hNpos⟩ := entry_window_nonpos_of_B_full k R C hC
            A₀ A₁ Cm B₀ B₁ u hu G₀ G₁ hG
          -- `stack_left_inverse_or_kernel` on the transposed stack already
          -- produces `∑ j, (H₀ i j * A₀ i' j + …)`, the shape wanted here.
          obtain ⟨N', hNneg⟩ := entry_window_nonneg_of_A_full k R hR C
            A₀ A₁ Cm B₀ B₁ u hu H₀ H₁ hH
          exact balanced_entries_mem_stableUnits k hdiv R hR C hC u
            (fun j i ↦ mem_balanced_of_nonpos_nonneg k
              (hNpos j i) (hNneg j i))
        · -- row kernel without row extraction: stuck
          obtain ⟨u₀, hu₀, hkA₀, hkA₁⟩ := hkerA
          exact hstuck R hR C hC A₀ A₁ Cm B₀ B₁ u hu hextT hextS
            (Or.inr ⟨u₀, hu₀, hkA₀, hkA₁⟩)
      · -- column kernel without column extraction: stuck
        obtain ⟨v₀, hv₀, hkB₀, hkB₁⟩ := hkerB
        exact hstuck R hR C hC A₀ A₁ Cm B₀ B₁ u hu hextT hextS
          (Or.inl ⟨v₀, hv₀, hkB₀, hkB₁⟩)

end BinaryLeavitt
end NonsoficGroupsExist
