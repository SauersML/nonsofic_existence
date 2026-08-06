import NonsoficGroupsExist.KOne.CodePairTransport

/-!
# Code-relative fullness witnesses

If the scalar stack `[B₀; B₁]` of a code-indexed pencil admits a
scalar left inverse, the degree `+1` part of the pencil value is left
invertible in the algebra: the witness is the transport of the scalar
inverse with `t`-generator entries, and the product collapses through
`codePair_mul` and the corner relations `t_z s_w = δ_{zw}`.  Mirror
statement for the degree `-1` part.  These witnesses feed the window
dichotomy at every stage of the code refinement.
-/

namespace NonsoficGroupsExist
namespace LeavittFamily

variable {A : Type*} [Ring A] (L : LeavittFamily A)
variable {k : Type*} [Field k] [Algebra k A]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Scalars pull out of products of scalar multiples. -/
theorem smul_mul_smul' (α β : k) (x y : A) :
    (α • x) * (β • y) = (α * β) • (x * y) := by
  rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul,
    show algebraMap k A α * x * (algebraMap k A β * y) =
      algebraMap k A α * (x * algebraMap k A β) * y from by
        noncomm_ring,
    ← Algebra.commutes β x]
  noncomm_ring

/-- The pencil-entry corner product: a `t`-combination times an
`s`-combination is the scalar pairing. -/
theorem t_combo_mul_s_combo (α₀ α₁ β₀ β₁ : k) :
    (α₀ • L.t 0 + α₁ • L.t 1) * (β₀ • L.s 0 + β₁ • L.s 1) =
      (α₀ * β₀ + α₁ * β₁) • (1 : A) := by
  have h00 : L.t 0 * L.s 0 = 1 := by rw [t_mul_s, if_pos rfl]
  have h01 : L.t 0 * L.s 1 = 0 := by
    rw [t_mul_s, if_neg (by decide)]
  have h10 : L.t 1 * L.s 0 = 0 := by
    rw [t_mul_s, if_neg (by decide)]
  have h11 : L.t 1 * L.s 1 = 1 := by rw [t_mul_s, if_pos rfl]
  -- `smul_mul_smul'` is not a `LeavittFamily` method (nor a Mathlib name);
  -- the fact `(a • b) * (c • d) = (a * c) • (b * d)` is `smul_mul_smul_comm`.
  rw [add_mul, mul_add, mul_add]
  simp only [smul_mul_smul_comm]
  rw [h00, h01, h10, h11, smul_zero, smul_zero, add_zero, zero_add,
    add_smul]

/-- **Left-fullness witness**: a scalar left inverse of the stack
`[B₀; B₁]` transports to a left inverse of the degree `+1` pencil
part. -/
theorem stack_left_inverse_transport [DecidableEq ι] [DecidableEq κ]
    (R : BinaryPrefixCode ι) (C : BinaryPrefixCode κ)
    (hC : L.IsComplete C)
    (B₀ B₁ : ι → κ → k) (G₀ G₁ : κ → ι → k)
    (hG : ∀ j j' : κ, (∑ i, (G₀ j i * B₀ i j' + G₁ j i * B₁ i j')) =
      if j = j' then 1 else 0) :
    (∑ j, ∑ i, L.wordS (C.word j) *
        (G₀ j i • L.t 0 + G₁ j i • L.t 1) * L.wordT (R.word i)) *
      (∑ i, ∑ j, L.wordS (R.word i) *
        (B₀ i j • L.s 0 + B₁ i j • L.s 1) * L.wordT (C.word j)) =
      1 := by
  classical
  have h := L.codePair_mul R C.word C.word
    (fun j i ↦ G₀ j i • L.t 0 + G₁ j i • L.t 1)
    (fun i j ↦ B₀ i j • L.s 0 + B₁ i j • L.s 1)
  beta_reduce at h
  rw [h]
  calc ∑ j, ∑ j', L.wordS (C.word j) *
        (∑ i, (G₀ j i • L.t 0 + G₁ j i • L.t 1) *
          (B₀ i j' • L.s 0 + B₁ i j' • L.s 1)) * L.wordT (C.word j')
      = ∑ j, ∑ j', (if j = j' then
          L.wordS (C.word j) * L.wordT (C.word j') else 0) := by
        refine Finset.sum_congr rfl fun j _ ↦
          Finset.sum_congr rfl fun j' _ ↦ ?_
        have hin : (∑ i, (G₀ j i • L.t 0 + G₁ j i • L.t 1) *
            (B₀ i j' • L.s 0 + B₁ i j' • L.s 1)) =
            (if j = j' then (1 : k) else 0) • (1 : A) := by
          calc ∑ i, (G₀ j i • L.t 0 + G₁ j i • L.t 1) *
                (B₀ i j' • L.s 0 + B₁ i j' • L.s 1)
              = ∑ i, (G₀ j i * B₀ i j' + G₁ j i * B₁ i j') •
                  (1 : A) :=
                Finset.sum_congr rfl fun i _ ↦
                  L.t_combo_mul_s_combo _ _ _ _
            _ = (∑ i, (G₀ j i * B₀ i j' + G₁ j i * B₁ i j')) •
                  (1 : A) := by rw [Finset.sum_smul]
            _ = (if j = j' then (1 : k) else 0) • (1 : A) := by
                rw [hG j j']
        rw [hin]
        split_ifs with hjj
        · rw [one_smul, mul_one]
        · rw [zero_smul, mul_zero, zero_mul]
    _ = ∑ j, L.wordS (C.word j) * L.wordT (C.word j) := by
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ j)]
    _ = 1 := hC

/-- **Right-fullness witness**: a scalar right inverse of the stack
`(A₀ | A₁)` transports to a right inverse of the degree `-1` pencil
part. -/
theorem stack_right_inverse_transport [DecidableEq ι] [DecidableEq κ]
    (R : BinaryPrefixCode ι) (hR : L.IsComplete R)
    (C : BinaryPrefixCode κ)
    (A₀ A₁ : ι → κ → k) (H₀ H₁ : κ → ι → k)
    (hH : ∀ i i' : ι, (∑ j, (A₀ i j * H₀ j i' + A₁ i j * H₁ j i')) =
      if i = i' then 1 else 0) :
    (∑ i, ∑ j, L.wordS (R.word i) *
        (A₀ i j • L.t 0 + A₁ i j • L.t 1) * L.wordT (C.word j)) *
      (∑ j, ∑ i, L.wordS (C.word j) *
        (H₀ j i • L.s 0 + H₁ j i • L.s 1) * L.wordT (R.word i)) =
      1 := by
  classical
  have h := L.codePair_mul C R.word R.word
    (fun i j ↦ A₀ i j • L.t 0 + A₁ i j • L.t 1)
    (fun j i ↦ H₀ j i • L.s 0 + H₁ j i • L.s 1)
  beta_reduce at h
  rw [h]
  calc ∑ i, ∑ i', L.wordS (R.word i) *
        (∑ j, (A₀ i j • L.t 0 + A₁ i j • L.t 1) *
          (H₀ j i' • L.s 0 + H₁ j i' • L.s 1)) * L.wordT (R.word i')
      = ∑ i, ∑ i', (if i = i' then
          L.wordS (R.word i) * L.wordT (R.word i') else 0) := by
        refine Finset.sum_congr rfl fun i _ ↦
          Finset.sum_congr rfl fun i' _ ↦ ?_
        have hin : (∑ j, (A₀ i j • L.t 0 + A₁ i j • L.t 1) *
            (H₀ j i' • L.s 0 + H₁ j i' • L.s 1)) =
            (if i = i' then (1 : k) else 0) • (1 : A) := by
          calc ∑ j, (A₀ i j • L.t 0 + A₁ i j • L.t 1) *
                (H₀ j i' • L.s 0 + H₁ j i' • L.s 1)
              = ∑ j, (A₀ i j * H₀ j i' + A₁ i j * H₁ j i') •
                  (1 : A) :=
                Finset.sum_congr rfl fun j _ ↦
                  L.t_combo_mul_s_combo _ _ _ _
            _ = (∑ j, (A₀ i j * H₀ j i' + A₁ i j * H₁ j i')) •
                  (1 : A) := by rw [Finset.sum_smul]
            _ = (if i = i' then (1 : k) else 0) • (1 : A) := by
                rw [hH i i']
        rw [hin]
        split_ifs with hii
        · rw [one_smul, mul_one]
        · rw [zero_smul, mul_zero, zero_mul]
    _ = ∑ i, L.wordS (R.word i) * L.wordT (R.word i) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ i)]
    _ = 1 := hR

end LeavittFamily
end NonsoficGroupsExist
