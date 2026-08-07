import NonsoficGroupsExist.Sofic.Sofic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Analysis.RCLike.Basic

/-!
# From permutations to unitaries: the metric core of `sofic ⟹ hyperlinear`

Pestov's Question 3.4 asks whether every hyperlinear group is sofic.  One
direction is known -- soficity implies hyperlinearity (Elek--Szabó, Math. Ann.
332 (2005)) -- and this file formalizes its metric content.

A sofic approximation lands in `Sym(Y_n)` with the normalized Hamming metric; a
hyperlinear approximation lands in `U(d_n)` with the normalized Hilbert--Schmidt
metric.  The bridge is the permutation representation, and the whole of the
implication at the metric level is the identity

  `‖P σ − P τ‖_HS² = 2 · |{y : σ y ≠ τ y}|`,

so that after normalizing by `|Y|`,

  `‖P σ − P τ‖²_{HS,norm} = 2 · d_H(σ, τ)`.

(`permMatrix_dist_sq_eq`, `permMatrix_normalized_dist_sq_eq`.)  Every estimate
in Definition `def:sofic` therefore transports: an asymptotically
multiplicative, asymptotically faithful sequence of permutation models becomes
an asymptotically multiplicative, asymptotically faithful sequence of *unitary*
models, with the errors merely doubled and square-rooted.  Nothing else is
needed, because a permutation matrix is unitary and `σ ↦ P σ` is a genuine
homomorphism, so no defect is created by the passage itself.

**The converse is Pestov's Question 3.4 and is open.**  Nothing in this file
bears on it.  What the file records is that the easy direction is easy for a
reason that can be written down in three lines: the two metrics are the same
metric, up to the factor `2` and a square root.
-/

namespace NonsoficGroupsExist

open Matrix

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

omit [Fintype Y] in
/-- Entries of the difference of two permutation matrices.  Row `x` is the
difference of two standard basis vectors, at `σ x` and at `τ x`. -/
theorem permMatrix_sub_entry (σ τ : Equiv.Perm Y) (x y : Y) :
    (σ.permMatrix ℝ - τ.permMatrix ℝ) x y
      = (if σ x = y then (1 : ℝ) else 0) - (if τ x = y then 1 else 0) := by
  simp [Equiv.Perm.permMatrix, Matrix.sub_apply]

/-- A single row of the difference contributes `0` when the permutations agree
there and `2` when they disagree: two distinct standard basis vectors are at
squared distance `2`. -/
theorem permMatrix_row_sq (σ τ : Equiv.Perm Y) (x : Y) :
    (∑ y : Y, ((σ.permMatrix ℝ - τ.permMatrix ℝ) x y) ^ 2)
      = if σ x = τ x then 0 else 2 := by
  classical
  have hentry : (∑ y : Y, ((σ.permMatrix ℝ - τ.permMatrix ℝ) x y) ^ 2)
      = ∑ y : Y, (((if σ x = y then (1 : ℝ) else 0)
          - (if τ x = y then 1 else 0)) ^ 2) := by
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [permMatrix_sub_entry]
  rw [hentry]
  by_cases h : σ x = τ x
  · simp [h]
  · rw [if_neg h]
    have hterm : ∀ y : Y, (((if σ x = y then (1 : ℝ) else 0)
        - (if τ x = y then 1 else 0)) ^ 2)
        = (if σ x = y then (1 : ℝ) else 0) + (if τ x = y then 1 else 0) := by
      intro y
      by_cases h1 : σ x = y <;> by_cases h2 : τ x = y <;> simp_all
    rw [Finset.sum_congr rfl fun y _ ↦ hterm y, Finset.sum_add_distrib]
    norm_num

/-- **The metric identity.**  The squared Hilbert--Schmidt distance between two
permutation matrices is twice the size of the disagreement set.  Dividing by
`|Y|` turns the normalized Hamming metric into the normalized Hilbert--Schmidt
metric, which is the whole of `sofic ⟹ hyperlinear` at the metric level. -/
theorem permMatrix_dist_sq_eq (σ τ : Equiv.Perm Y) :
    (∑ x : Y, ∑ y : Y, ((σ.permMatrix ℝ - τ.permMatrix ℝ) x y) ^ 2)
      = 2 * (hammingDisagreement σ τ).card := by
  classical
  rw [Finset.sum_congr rfl fun x _ ↦ permMatrix_row_sq σ τ x]
  have hrw : ∀ x : Y, (if σ x = τ x then (0 : ℝ) else 2)
      = 2 * (if x ∈ hammingDisagreement σ τ then (1 : ℝ) else 0) := by
    intro x
    by_cases h : σ x = τ x <;> simp [mem_hammingDisagreement, h]
  rw [Finset.sum_congr rfl fun x _ ↦ hrw x, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_ite_mem]
  simp

/-- The normalized form: `‖P σ − P τ‖²_{HS,norm} = 2 · d_H(σ, τ)`.  Every
estimate of Definition `def:sofic` transports to the unitary setting through
this identity, with the error merely doubled and square-rooted. -/
theorem permMatrix_normalized_dist_sq_eq (Y : FiniteModel) (σ τ : Equiv.Perm Y) :
    (∑ x : Y, ∑ y : Y, ((σ.permMatrix ℝ - τ.permMatrix ℝ) x y) ^ 2)
        / Fintype.card Y
      = 2 * hammingDistance Y σ τ := by
  rw [permMatrix_dist_sq_eq, hammingDistance]
  ring

end NonsoficGroupsExist
