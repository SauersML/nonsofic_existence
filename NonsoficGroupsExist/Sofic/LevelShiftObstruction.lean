import NonsoficGroupsExist.Sofic.Sofic
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Level-shifting permutations lose the top level

A recurring proposal for building finite models of an ascending HNN action is a
*tower*: sites graded into levels `S = S₀ ⊔ ⋯ ⊔ S_m`, with the stable letter
implemented by a permutation that shifts each level up by one.  This file
records why the shape cannot work when the levels grow, and it is a counting
argument with no analysis in it.

A permutation cannot shift the top level anywhere, because there is no level
`m + 1`.  So the set on which the permutation is level-compatible is *disjoint
from the top level* (`levelShift_good_disjoint_top`), and therefore misses at
least `|S_m|` points (`levelShift_card_add_top_le`).  When the levels grow by a
factor `k ≥ 2` — which is what happens for `Y_n = Γ/(φⁿ(Γ)K)` with
`k = [Γ : φ(Γ)]` — the top level carries a `(k−1)/k` fraction of everything
(`geometric_sum_eq`, `geometric_top_heavy`), so the incompatible mass is
`Θ(1)`, not `o(1)`, and no choice of tower height `m` improves it.

That is fatal in the presence of exponential amplification: a site defect of
constant density becomes a multiplicativity defect of constant size in the
configuration models these towers are built to feed.

**The calibration.**  The same count applies verbatim to `BS(1,2)`, where
`Γ = ℤ`, `φ(γ) = 2γ`, and `k = 2`.  There the wreath product *is* sofic, since
`BS(1,2)` is amenable — but its models come from Følner sets of the group, not
from a level-shifted tower.  So the tower shape fails even where the conclusion
is known to hold, which is the sharpest evidence that the obstruction is in the
architecture rather than in the group.
-/

namespace NonsoficGroupsExist

variable {S : Type*} [Fintype S] [DecidableEq S]

omit [Fintype S] [DecidableEq S] in
/-- **A level-shifting permutation is never compatible on the top level.**
There is no level `m + 1` for it to land in. -/
theorem levelShift_good_disjoint_top (m : ℕ) (level : S → ℕ)
    (hbound : ∀ x, level x ≤ m) (σ : Equiv.Perm S) (x : S)
    (hgood : level (σ x) = level x + 1) : level x ≠ m := by
  have hσ := hbound (σ x)
  omega

/-- **The counting no-go.**  The level-compatible set and the top level are
disjoint, so together they fit inside `S`: the permutation fails to shift at
least `|S_m|` points. -/
theorem levelShift_card_add_top_le (m : ℕ) (level : S → ℕ)
    (hbound : ∀ x, level x ≤ m) (σ : Equiv.Perm S) :
    (Finset.univ.filter fun x ↦ level (σ x) = level x + 1).card
        + (Finset.univ.filter fun x ↦ level x = m).card
      ≤ Fintype.card S := by
  classical
  have hdisj : Disjoint (Finset.univ.filter fun x ↦ level (σ x) = level x + 1)
      (Finset.univ.filter fun x ↦ level x = m) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    rw [Finset.mem_filter] at hx hy
    exact levelShift_good_disjoint_top m level hbound σ x hx.2 hy.2
  calc (Finset.univ.filter fun x ↦ level (σ x) = level x + 1).card
        + (Finset.univ.filter fun x ↦ level x = m).card
      = ((Finset.univ.filter fun x ↦ level (σ x) = level x + 1) ∪
          (Finset.univ.filter fun x ↦ level x = m)).card :=
        (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ Fintype.card S := Finset.card_le_univ _

/-! ## Geometric levels put almost everything on top -/

/-- The closed form for a geometric tower: `(k−1)·Σ + a₀ = k·a_m`. -/
theorem geometric_sum_eq {k : ℕ} (hk : 1 ≤ k) (a : ℕ → ℕ)
    (hgeo : ∀ n, a (n + 1) = k * a n) (m : ℕ) :
    (k - 1) * (∑ n ∈ Finset.range (m + 1), a n) + a 0 = k * a m := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  induction m with
  | zero => simp; ring
  | succ m ih =>
      rw [Finset.sum_range_succ, Nat.mul_add, add_right_comm, ih, hgeo m]
      ring

/-- **The top level dominates.**  For levels growing by a factor `k ≥ 2`, the
whole tower is smaller than `k/(k−1)` times its top level; equivalently the top
level carries more than a `(k−1)/k` fraction of the mass, uniformly in the
height `m`. -/
theorem geometric_top_heavy {k : ℕ} (hk : 2 ≤ k) (a : ℕ → ℕ) (ha : 0 < a 0)
    (hgeo : ∀ n, a (n + 1) = k * a n) (m : ℕ) :
    (k - 1) * (∑ n ∈ Finset.range (m + 1), a n) < k * a m := by
  have h := geometric_sum_eq (by omega) a hgeo m
  omega

end NonsoficGroupsExist
