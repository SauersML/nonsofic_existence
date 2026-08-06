import NonsoficGroupsExist.EntrywiseKill
import NonsoficGroupsExist.MirrorExtraction

/-!
# The mirrored entrywise kill and the window intersection

`θ̂` transposes pencils and flips degree windows, so a scalar right
inverse of the row stack `(A₀ | A₁)` kills every *negative* component
of every inverse entry.  Together with the direct kill this pins the
entries to the balanced span: an element of both a nonpositive and a
nonnegative window is balanced, by uniqueness of graded components.
-/

namespace NonsoficGroupsExist
namespace BinaryLeavitt

open LeavittFamily MatrixDiagonalization

variable (k : Type) [Field k]

/-- An element of both a nonpositive and a nonnegative window is
balanced. -/
theorem mem_balanced_of_nonpos_nonneg {x : BinaryLeavittAlgebra k}
    {N N' : ℕ}
    (h1 : x ∈ Submodule.span k
      ((family k).degreeMonomials (-(N : ℤ)) 0))
    (h2 : x ∈ Submodule.span k
      ((family k).degreeMonomials 0 (N' : ℤ))) :
    x ∈ Submodule.span k ((family k).degreeMonomials 0 0) := by
  classical
  obtain ⟨y, hymem, hysupp, hysum⟩ := exists_components k h1
  obtain ⟨z, hzmem, hzsupp, hzsum⟩ := exists_components k h2
  have hyext : ∑ d ∈ Finset.Icc (-(N : ℤ)) (N' : ℤ), y d = x := by
    rw [hysum]
    exact (Finset.sum_subset
      (Finset.Icc_subset_Icc le_rfl (by omega))
      (fun d hd hd' ↦ hysupp d (by
        rw [Finset.mem_Icc] at hd
        rw [Finset.mem_Icc] at hd'
        omega))).symm
  have hzext : ∑ d ∈ Finset.Icc (-(N : ℤ)) (N' : ℤ), z d = x := by
    rw [hzsum]
    exact (Finset.sum_subset
      (Finset.Icc_subset_Icc (by omega) le_rfl)
      (fun d hd hd' ↦ hzsupp d (by
        rw [Finset.mem_Icc] at hd
        rw [Finset.mem_Icc] at hd'
        omega))).symm
  have huniq := components_unique k
    (D := Finset.Icc (-(N : ℤ)) (N' : ℤ))
    (y := y) (z := z)
    (fun d _ ↦ hymem d) (fun d _ ↦ hzmem d)
    (by rw [hyext, hzext])
  have hzero : ∀ d ∈ Finset.Icc (-(N : ℤ)) (0 : ℤ), d ≠ 0 →
      y d = 0 := by
    intro d hd hne
    rw [Finset.mem_Icc] at hd
    have h := huniq d (Finset.mem_Icc.mpr (by omega))
    rw [h]
    exact hzsupp d (Or.inl (by omega))
  have hx0 : x = y 0 := by
    rw [hysum]
    exact Finset.sum_eq_single 0 hzero
      (fun h ↦ absurd (Finset.mem_Icc.mpr (by omega)) h)
  rw [hx0]
  exact hymem 0

/-- **The mirrored kill**: a scalar right inverse of the row stack
`(A₀ | A₁)` forces every inverse entry into a nonnegative window. -/
theorem entry_window_nonneg_of_A_full
    [Nontrivial (BinaryLeavittAlgebra k)]
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (R : BinaryPrefixCode ι) (hR : (family k).IsComplete R)
    (C : BinaryPrefixCode κ)
    (A₀ A₁ Cm B₀ B₁ : ι → κ → k) (u : (BinaryLeavittAlgebra k)ˣ)
    (hu : (u : BinaryLeavittAlgebra k) = ∑ i, ∑ j,
      (family k).wordS (R.word i) *
      (family k).pencilEntry (k := k) (A₀ i j) (A₁ i j) (Cm i j)
        (B₀ i j) (B₁ i j) * (family k).wordT (C.word j))
    (G₀ G₁ : ι → κ → k)
    (hG : ∀ i i' : ι, (∑ j, (G₀ i j * A₀ i' j + G₁ i j * A₁ i' j)) =
      if i = i' then 1 else 0) :
    ∃ N : ℕ, ∀ (j : κ) (i : ι),
      (family k).wordT (C.word j) *
        ((u⁻¹ : (BinaryLeavittAlgebra k)ˣ) : BinaryLeavittAlgebra k) *
        (family k).wordS (R.word i) ∈
      Submodule.span k ((family k).degreeMonomials 0 (N : ℤ)) := by
  classical
  -- the transposed pencil
  have hθval : ((thetaUnit k u : (BinaryLeavittAlgebra k)ˣ) :
      BinaryLeavittAlgebra k) = ∑ j, ∑ i,
      (family k).wordS (C.word j) *
      (family k).pencilEntry (k := k) (B₀ i j) (B₁ i j) (Cm i j)
        (A₀ i j) (A₁ i j) * (family k).wordT (R.word i) := by
    rw [thetaUnit_val, hu]
    exact thetaHat_pencilVal k R C A₀ A₁ Cm B₀ B₁
  -- the direct kill on the transposed side
  obtain ⟨N, hN⟩ := entry_window_nonpos_of_B_full k C R hR
    (fun j i ↦ B₀ i j) (fun j i ↦ B₁ i j) (fun j i ↦ Cm i j)
    (fun j i ↦ A₀ i j) (fun j i ↦ A₁ i j)
    (thetaUnit k u) (by beta_reduce; exact hθval) G₀ G₁
    (by beta_reduce; exact hG)
  refine ⟨N, fun j i ↦ ?_⟩
  -- transport the window back through `θ̂`
  have hentry : (family k).wordT (R.word i) *
      (((thetaUnit k u)⁻¹ : (BinaryLeavittAlgebra k)ˣ) :
        BinaryLeavittAlgebra k) *
      (family k).wordS (C.word j) =
      thetaHat k ((family k).wordT (C.word j) *
        ((u⁻¹ : (BinaryLeavittAlgebra k)ˣ) : BinaryLeavittAlgebra k) *
        (family k).wordS (R.word i)) := by
    rw [thetaHat_mul, thetaHat_mul, thetaHat_wordT, thetaHat_wordS,
      ← mul_assoc]
    rfl
  have h := hN i j
  rw [hentry] at h
  have h2 := thetaHat_mem_span_degree k h
  rw [thetaHat_thetaHat] at h2
  have h3 : (-(0 : ℤ)) = 0 := by ring
  rw [h3] at h2
  rw [show -(-(N : ℤ)) = (N : ℤ) from by ring] at h2
  exact h2

end BinaryLeavitt
end NonsoficGroupsExist
