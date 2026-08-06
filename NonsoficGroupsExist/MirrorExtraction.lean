import NonsoficGroupsExist.FullExtraction
import NonsoficGroupsExist.ThetaStable

/-!
# The mirrored extraction step

`θ̂` transposes code pencils — rows and columns swap, and the `t`-data
trades places with the `s`-data.  A kernel vector of the *row* stack
`(A₀ | A₁ | C)` of a pencil unit therefore becomes a kernel vector of
the column stack of the transposed pencil, the extraction step applies
there, and transporting back yields a pencil unit over one fewer
column with equivalent class-group membership.
-/

namespace NonsoficGroupsExist
namespace BinaryLeavitt

open LeavittFamily MatrixDiagonalization

variable (k : Type) [Field k]

/-- `θ̂` swaps the `t`- and `s`-coefficients of a pencil entry. -/
theorem thetaHat_pencilEntry (a₀ a₁ c b₀ b₁ : k) :
    thetaHat k ((family k).pencilEntry (k := k) a₀ a₁ c b₀ b₁) =
      (family k).pencilEntry (k := k) b₀ b₁ c a₀ a₁ := by
  unfold LeavittFamily.pencilEntry
  -- `pencilEntry` is a four-fold sum, so four `thetaHat_add`s are needed
  -- before the five `thetaHat_smul`s have anything to match.
  rw [thetaHat_add, thetaHat_add, thetaHat_add, thetaHat_add,
    thetaHat_smul, thetaHat_smul, thetaHat_smul, thetaHat_smul,
    thetaHat_smul,
    thetaHat_t, thetaHat_t, thetaHat_one, thetaHat_s, thetaHat_s]
  abel

/-- `θ̂` transposes pencil values. -/
theorem thetaHat_pencilVal {ι κ : Type*} [Fintype ι] [Fintype κ]
    (R : BinaryPrefixCode ι) (C : BinaryPrefixCode κ)
    (A₀ A₁ Cm B₀ B₁ : ι → κ → k) :
    thetaHat k (∑ i, ∑ j, (family k).wordS (R.word i) *
      (family k).pencilEntry (k := k) (A₀ i j) (A₁ i j) (Cm i j)
        (B₀ i j) (B₁ i j) * (family k).wordT (C.word j)) =
    ∑ j, ∑ i, (family k).wordS (C.word j) *
      (family k).pencilEntry (k := k) (B₀ i j) (B₁ i j) (Cm i j)
        (A₀ i j) (A₁ i j) * (family k).wordT (R.word i) := by
  rw [thetaHat_sum]
  rw [show (∑ i, thetaHat k (∑ j, (family k).wordS (R.word i) *
      (family k).pencilEntry (k := k) (A₀ i j) (A₁ i j) (Cm i j)
        (B₀ i j) (B₁ i j) * (family k).wordT (C.word j))) =
    ∑ i, ∑ j, (family k).wordS (C.word j) *
      (family k).pencilEntry (k := k) (B₀ i j) (B₁ i j) (Cm i j)
        (A₀ i j) (A₁ i j) * (family k).wordT (R.word i) from
    Finset.sum_congr rfl fun i _ ↦ by
      rw [thetaHat_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [thetaHat_mul, thetaHat_mul, thetaHat_wordT,
        thetaHat_wordS, thetaHat_pencilEntry, ← mul_assoc]]
  exact Finset.sum_comm

/-- **The mirrored extraction step**: a kernel vector of the row
stack yields a pencil unit over one fewer column. -/
theorem mirror_extraction [Nontrivial (BinaryLeavittAlgebra k)]
    (hdiv : ∀ x : BinaryLeavittAlgebra k, x ≠ 0 →
      ∃ p q : BinaryLeavittAlgebra k, p * x * q = 1)
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (R : BinaryPrefixCode ι) (hR : (family k).IsComplete R)
    (C : BinaryPrefixCode κ) (hC : (family k).IsComplete C)
    (A₀ A₁ Cm B₀ B₁ : ι → κ → k) (u : (BinaryLeavittAlgebra k)ˣ)
    (hu : (u : BinaryLeavittAlgebra k) = ∑ i, ∑ j,
      (family k).wordS (R.word i) *
      (family k).pencilEntry (k := k) (A₀ i j) (A₁ i j) (Cm i j)
        (B₀ i j) (B₁ i j) * (family k).wordT (C.word j))
    (u₀ : ι → k) (hu₀ : u₀ ≠ 0)
    (hkA₀ : ∀ j, ∑ i, A₀ i j * u₀ i = 0)
    (hkA₁ : ∀ j, ∑ i, A₁ i j * u₀ i = 0)
    (hkC : ∀ j, ∑ i, Cm i j * u₀ i = 0) :
    ∃ (j₂ : κ) (D : {j : κ // j ≠ j₂} → List (Fin 2))
      (A₀' A₁' Cm' B₀' B₁' : ι → {j : κ // j ≠ j₂} → k)
      (u₂ : (BinaryLeavittAlgebra k)ˣ),
      (∀ ⦃p q : {j : κ // j ≠ j₂}⦄, p ≠ q → ¬D p <+: D q) ∧
      (∑ p, (family k).cylinder (D p) = 1) ∧
      ((u₂ : BinaryLeavittAlgebra k) = ∑ i, ∑ p,
        (family k).wordS (R.word i) *
        (family k).pencilEntry (k := k) (A₀' i p) (A₁' i p)
          (Cm' i p) (B₀' i p) (B₁' i p) *
        (family k).wordT (D p)) ∧
      (u ∈ stableUnits (BinaryLeavittAlgebra k) ↔
        u₂ ∈ stableUnits (BinaryLeavittAlgebra k)) := by
  classical
  -- the transposed pencil value
  have hθ : ((thetaUnit k u : (BinaryLeavittAlgebra k)ˣ) :
      BinaryLeavittAlgebra k) = ∑ j, ∑ i,
      (family k).wordS (C.word j) *
      (family k).pencilEntry (k := k) (B₀ i j) (B₁ i j) (Cm i j)
        (A₀ i j) (A₁ i j) * (family k).wordT (R.word i) := by
    rw [thetaUnit_val, hu]
    exact thetaHat_pencilVal k R C A₀ A₁ Cm B₀ B₁
  -- extract on the transposed side
  obtain ⟨j₂, D, A₀θ, A₁θ, Cmθ, B₀θ, B₁θ, u₂θ, hDfree, hDsum, hval,
      hiff⟩ :=
    (family k).full_extraction hdiv C hC R hR
      (fun j i ↦ B₀ i j) (fun j i ↦ B₁ i j) (fun j i ↦ Cm i j)
      (fun j i ↦ A₀ i j) (fun j i ↦ A₁ i j)
      (thetaUnit k u) (by exact hθ) u₀ hu₀
      (by exact hkA₀) (by exact hkA₁)
      (by exact hkC)
  -- transport back
  set Dcode : BinaryPrefixCode {j : κ // j ≠ j₂} := ⟨D, hDfree⟩
    with hDcode
  refine ⟨j₂, D,
    (fun i p ↦ B₀θ p i), (fun i p ↦ B₁θ p i), (fun i p ↦ Cmθ p i),
    (fun i p ↦ A₀θ p i), (fun i p ↦ A₁θ p i),
    thetaUnit k u₂θ, hDfree, hDsum, ?_, ?_⟩
  · rw [thetaUnit_val, hval]
    have h := thetaHat_pencilVal k Dcode R A₀θ A₁θ Cmθ B₀θ B₁θ
    rw [show Dcode.word = D from rfl] at h
    rw [h]
  · calc u ∈ stableUnits (BinaryLeavittAlgebra k)
        ↔ thetaUnit k u ∈ stableUnits (BinaryLeavittAlgebra k) :=
          (thetaUnit_mem_stableUnits_iff k u).symm
      _ ↔ u₂θ ∈ stableUnits (BinaryLeavittAlgebra k) := hiff
      _ ↔ thetaUnit k u₂θ ∈ stableUnits (BinaryLeavittAlgebra k) :=
          (thetaUnit_mem_stableUnits_iff k u₂θ).symm

end BinaryLeavitt
end NonsoficGroupsExist
