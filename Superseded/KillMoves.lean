import NonsoficGroupsExist.KOne.IncomparableUnipotents

/-!
# The unipotent kill move for negative parts

The width-three reduction eliminates the degree `-1` part of a narrow
unit monomial by monomial.  This file provides the workhorse: right
multiplication by the incomparable unipotent `1 - λ·s_x t_y` removes
the term `λ·s_x t_y` from the value exactly, provided the supply
(annihilation) hypotheses hold; the only other effect is a balanced
shift by `-λ·b·s_x t_y`.  The conclusion is an exact value formula,
ready for the terminating induction, and the class relation is an
equivalence through the compiled incomparable-unipotent certificate.
-/

namespace NonsoficGroupsExist
namespace LeavittFamily

open MatrixDiagonalization

variable {A : Type*} [Ring A] (L : LeavittFamily A)
variable {k : Type*} [Field k] [Algebra k A]

/-- **Unipotent kill** (right version): if the supply conditions hold,
right multiplication by the incomparable unipotent `1 - λ s_x t_y`
removes `λ s_x t_y` from the value at the cost of a balanced shift,
within the diagonal class. -/
theorem unipotent_kill_step {x y : List (Fin 2)} (hxy : ¬x <+: y)
    (hyx : ¬y <+: x) (lam : k) {a c b : A} (u : Aˣ)
    (hu : (u : A) = 1 + a + c + b)
    (hasup : a * (L.wordS x * L.wordT y) = 0)
    (hcsup : c * (L.wordS x * L.wordT y) = 0) :
    ∃ u' : Aˣ,
      (u' : A) = 1 + (a - algebraMap k A lam *
          (L.wordS x * L.wordT y)) +
        (c - algebraMap k A lam * (b * (L.wordS x * L.wordT y))) + b ∧
      (u ∈ stableUnits A ↔ u' ∈ stableUnits A) := by
  set ν : A := L.wordS x * (algebraMap k A (-lam)) * L.wordT y with hν
  set m : Aˣ := L.incomparableUnit hxy hyx (algebraMap k A (-lam))
    with hm
  have hmval : (m : A) = 1 + ν := rfl
  have hmmem : m ∈ stableUnits A := L.incomparableUnit_mem hxy hyx _
  refine ⟨u * m, ?_, ?_⟩
  · show (u : A) * (m : A) = _
    rw [hu, hmval]
    have hνform : ν = -(algebraMap k A lam) *
        (L.wordS x * L.wordT y) := by
      -- Pull the sign back *into* the scalar first.  `Algebra.commutes` is
      -- stated for `algebraMap k A (-lam)`, so normalising to
      -- `-(algebraMap k A lam)` up front makes every rewrite below miss.
      rw [hν, ← map_neg, ← Algebra.commutes (-lam) (L.wordS x), mul_assoc]
    have haν : a * ν = 0 := by
      rw [hνform, ← map_neg, ← mul_assoc,
        ← Algebra.commutes (-lam) a, mul_assoc, hasup, mul_zero]
    have hcν : c * ν = 0 := by
      rw [hνform, ← map_neg, ← mul_assoc,
        ← Algebra.commutes (-lam) c, mul_assoc, hcsup, mul_zero]
    have hbν : b * ν = -(algebraMap k A lam) *
        (b * (L.wordS x * L.wordT y)) := by
      have hc : b * algebraMap k A lam = algebraMap k A lam * b :=
        (Algebra.commutes lam b).symm
      rw [hνform]
      calc b * (-(algebraMap k A lam) * (L.wordS x * L.wordT y))
          = -(b * algebraMap k A lam) * (L.wordS x * L.wordT y) := by
            noncomm_ring
        _ = -(algebraMap k A lam * b) * (L.wordS x * L.wordT y) := by
            rw [hc]
        _ = -(algebraMap k A lam) * (b * (L.wordS x * L.wordT y)) := by
            noncomm_ring
    calc (1 + a + c + b) * (1 + ν)
        = 1 + a + c + b + ν + a * ν + c * ν + b * ν := by noncomm_ring
      _ = 1 + a + c + b + ν + b * ν := by
          rw [haν, hcν]
          abel
      _ = 1 + (a - algebraMap k A lam * (L.wordS x * L.wordT y)) +
          (c - algebraMap k A lam * (b * (L.wordS x * L.wordT y))) +
          b := by
          -- `hbν` must fire before `hνform`, otherwise rewriting `ν`
          -- everywhere destroys the `b * ν` occurrence it matches on.
          rw [hbν, hνform]
          simp only [neg_mul]
          abel
  · constructor
    · intro huH
      exact mul_mem huH hmmem
    · intro hu'H
      have : u = (u * m) * m⁻¹ := by group
      rw [this]
      exact mul_mem hu'H (inv_mem hmmem)

end LeavittFamily
end NonsoficGroupsExist
