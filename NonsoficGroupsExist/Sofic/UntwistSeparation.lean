import NonsoficGroupsExist.Sofic.ScalarCocycle

/-!
# Untwisting cannot manufacture separation

Every result in `PhaseCorrection`, `ScalarClass` and `RationalCharacter` is
about *multiplicativity*: obtaining phases that compose exactly.  None of them
touches the other half of a sofic model, which is **separation** -- that a
nontrivial group element move almost every point.  This file addresses that
half, and the news is negative and quantitative.

The fixed points of the untwisted permutation of `(d, σ)` are the pairs `(y,j)`
with `σy = y` and `d y = 0`, so untwisting separates only to the extent that the
phase avoids `0` on the fixed points of `σ`.  But the fixed point set of `σ` is
partitioned by the `m` classes of `d`, so by pigeonhole some class carries at
least a `1/m` share:

    ∃ c,  density{ y : σy = y and d y = c } ≥ (1/m) · density{ y : σy = y }

(`exists_shift_fixed_ge`).  Re-normalizing the phase by that `c` -- which is a
*scalar* change, and so is invisible to the Hilbert--Schmidt metric by
`hsDistSq_monomial_const` -- produces an untwisted model whose separation is at
most `1 - F/m`, where `F` is the fixed point density of `σ`
(`exists_shift_hamming_le`).

So untwisting cannot manufacture separation.  It can only inherit it, up to a
factor `m`: if the permutation parts of a monomial model are not already almost
fixed point free, no choice of phases repairs that, and no renormalization of
the phases hides it from every scalar.

The extreme case says it without any pigeonhole
(`untwist_separation_undetermined`).  On the *same* permutation `σ`, the
constant phase `1` untwists to a model of separation exactly `1`, and the
constant phase `0` untwists to one of separation exactly `1 - F`.  The two
monomial matrices differ by a scalar, so `hsDistSq_monomial_const` puts them at
Hilbert--Schmidt distance `|1 - ζ|²`, which tends to `0` as `m` grows.  Two
models arbitrarily close in the metric hyperlinearity uses therefore have
untwisted separations `1` and `1 - F` for whatever `F` one likes.

*The metric data does not determine the untwisted separation.*  That is the
separation-side counterpart of `ScalarCocycle`, and it is why none of the
correction machinery bears on this half of the problem.  Question 3.4 is not
decided here; what is decided is that it will not be decided by improving the
phases.
-/

namespace NonsoficGroupsExist

open Finset

/-- The fixed point density of a permutation of the model. -/
noncomputable def fixedDensity (Y : FiniteModel) (σ : Equiv.Perm Y) : ℝ :=
  ((univ.filter fun y : Y ↦ σ y = y).card : ℝ) / Fintype.card Y

/-! ## The pigeonhole -/

/-- **Some phase class carries a `1/m` share of the fixed points.**  The fixed
point set of `σ` is partitioned by the `m` classes of `d`, so one class is at
least average. -/
theorem exists_shift_fixed_ge (Y : FiniteModel) (m : ℕ) [NeZero m]
    (d : Y → ZMod m) (σ : Equiv.Perm Y) :
    ∃ c : ZMod m,
      ((univ.filter fun y : Y ↦ σ y = y).card : ℝ)
        ≤ m * ((univ.filter fun y : Y ↦ σ y = y ∧ d y = c).card : ℝ) := by
  classical
  have hfib : (univ.filter fun y : Y ↦ σ y = y).card
      = ∑ c : ZMod m,
          ((univ.filter fun y : Y ↦ σ y = y).filter fun y ↦ d y = c).card :=
    Finset.card_eq_sum_card_fiberwise (fun y _ ↦ Finset.mem_univ (d y))
  have hrefine : ∀ c : ZMod m,
      ((univ.filter fun y : Y ↦ σ y = y).filter fun y ↦ d y = c)
        = univ.filter fun y : Y ↦ σ y = y ∧ d y = c := by
    intro c
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_contra hcon
  have hall : ∀ c : ZMod m,
      (m : ℝ) * ((univ.filter fun y : Y ↦ σ y = y ∧ d y = c).card : ℝ)
        < ((univ.filter fun y : Y ↦ σ y = y).card : ℝ) := by
    intro c
    by_contra hc
    exact hcon ⟨c, le_of_not_gt hc⟩
  have hsum : ((univ.filter fun y : Y ↦ σ y = y).card : ℝ)
      = ∑ c : ZMod m,
          ((univ.filter fun y : Y ↦ σ y = y ∧ d y = c).card : ℝ) := by
    rw [show ((univ.filter fun y : Y ↦ σ y = y).card : ℝ)
        = (((univ.filter fun y : Y ↦ σ y = y).card : ℕ) : ℝ) from rfl, hfib]
    push_cast
    exact Finset.sum_congr rfl fun c _ ↦ by rw [hrefine c]
  have hmpos : (0 : ℝ) < m := by
    have : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
    exact_mod_cast this
  have hstrict : (m : ℝ) * ((univ.filter fun y : Y ↦ σ y = y).card : ℝ)
      < (m : ℝ) * ((univ.filter fun y : Y ↦ σ y = y).card : ℝ) := by
    calc (m : ℝ) * ((univ.filter fun y : Y ↦ σ y = y).card : ℝ)
        = ∑ _c : ZMod m, ((univ.filter fun y : Y ↦ σ y = y).card : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ZMod.card]
      _ > ∑ c : ZMod m,
            (m : ℝ) * ((univ.filter fun y : Y ↦ σ y = y ∧ d y = c).card : ℝ) := by
          refine Finset.sum_lt_sum_of_nonempty ?_ fun c _ ↦ hall c
          exact Finset.univ_nonempty
      _ = (m : ℝ) * ∑ c : ZMod m,
            ((univ.filter fun y : Y ↦ σ y = y ∧ d y = c).card : ℝ) := by
          rw [Finset.mul_sum]
      _ = (m : ℝ) * ((univ.filter fun y : Y ↦ σ y = y).card : ℝ) := by rw [← hsum]
  exact lt_irrefl _ hstrict

/-! ## What that costs the untwisted model -/

/-- **Untwisting cannot manufacture separation.**  Some scalar renormalization
of the phases leaves the untwisted model with separation at most `1 - F/m`,
where `F` is the fixed point density of the permutation part.  A scalar change
is invisible to the Hilbert--Schmidt metric (`hsDistSq_monomial_const`), so the
metric offers no way to rule this normalization out. -/
theorem exists_shift_hamming_le (Y : FiniteModel) (m : ℕ) [NeZero m]
    (d : Y → ZMod m) (σ : Equiv.Perm Y) (hY : 0 < Fintype.card Y) :
    ∃ c : ZMod m,
      hammingDistance (wreathModel Y m) (wreathPerm Y m (fun y ↦ d y - c) σ) 1
        ≤ 1 - fixedDensity Y σ / m := by
  classical
  obtain ⟨c, hc⟩ := exists_shift_fixed_ge Y m d σ
  refine ⟨c, ?_⟩
  have hYR : (0 : ℝ) < Fintype.card Y := by exact_mod_cast hY
  have hmpos : (0 : ℝ) < m := by
    have : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
    exact_mod_cast this
  rw [hammingDistance_wreathPerm_one]
  have hcompl : (univ.filter fun y : Y ↦ ¬ (σ y = y ∧ d y - c = 0)).card
      = Fintype.card Y - (univ.filter fun y : Y ↦ σ y = y ∧ d y = c).card := by
    have hsame : (univ.filter fun y : Y ↦ σ y = y ∧ d y - c = 0)
        = univ.filter fun y : Y ↦ σ y = y ∧ d y = c := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, sub_eq_zero]
    have := Finset.card_filter_add_card_filter_not
      (s := (univ : Finset Y)) (fun y : Y ↦ σ y = y ∧ d y - c = 0)
    rw [hsame, Finset.card_univ] at this
    omega
  have hle : (univ.filter fun y : Y ↦ σ y = y ∧ d y = c).card ≤ Fintype.card Y := by
    calc (univ.filter fun y : Y ↦ σ y = y ∧ d y = c).card
        ≤ (univ : Finset Y).card := Finset.card_filter_le _ _
      _ = Fintype.card Y := Finset.card_univ
  rw [hcompl, Nat.cast_sub hle]
  rw [fixedDensity, div_le_iff₀ hYR]
  have hstep : ((univ.filter fun y : Y ↦ σ y = y).card : ℝ) / m
      ≤ ((univ.filter fun y : Y ↦ σ y = y ∧ d y = c).card : ℝ) := by
    rw [div_le_iff₀ hmpos]
    linarith [hc]
  have hdiv : ((univ.filter fun y : Y ↦ σ y = y).card : ℝ) / Fintype.card Y / m
      * Fintype.card Y
      = ((univ.filter fun y : Y ↦ σ y = y).card : ℝ) / m := by
    field_simp
  rw [sub_mul, one_mul, hdiv]
  linarith [hstep]

/-! ## The metric does not determine the separation -/

/-- **The extreme case, with no pigeonhole.**  On the same permutation part, the
constant phase `1` untwists to a model of separation exactly `1`, and the
constant phase `0` untwists to one of separation exactly `1 - F`.  The two
monomial matrices differ by a scalar, hence sit at Hilbert--Schmidt distance
`|1 - ζ|²` by `hsDistSq_monomial_const`, which tends to `0` as `m` grows.

So two models arbitrarily close in the metric that hyperlinearity uses can have
untwisted separations `1` and `1 - F` for any `F` whatever: *the metric data
does not determine the untwisted separation.* -/
theorem untwist_separation_undetermined (Y : FiniteModel) (m : ℕ) [NeZero m]
    (hm : 2 ≤ m) (σ : Equiv.Perm Y) (hY : 0 < Fintype.card Y) :
    hammingDistance (wreathModel Y m) (wreathPerm Y m (fun _ ↦ (1 : ZMod m)) σ) 1 = 1
      ∧ hammingDistance (wreathModel Y m)
          (wreathPerm Y m (fun _ ↦ (0 : ZMod m)) σ) 1 = 1 - fixedDensity Y σ := by
  classical
  have hYR : (0 : ℝ) < Fintype.card Y := by exact_mod_cast hY
  haveI : Fact (1 < m) := ⟨lt_of_lt_of_le (by norm_num) hm⟩
  constructor
  · rw [hammingDistance_wreathPerm_one]
    have hall : (univ.filter fun y : Y ↦ ¬ (σ y = y ∧ (1 : ZMod m) = 0))
        = (univ : Finset Y) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      intro hcon
      exact one_ne_zero hcon.2
    rw [hall, Finset.card_univ]
    field_simp
  · rw [hammingDistance_wreathPerm_one]
    have hcompl : (univ.filter fun y : Y ↦ ¬ (σ y = y ∧ (0 : ZMod m) = 0)).card
        = Fintype.card Y - (univ.filter fun y : Y ↦ σ y = y).card := by
      have hsame : (univ.filter fun y : Y ↦ σ y = y ∧ (0 : ZMod m) = 0)
          = univ.filter fun y : Y ↦ σ y = y := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_true]
      have := Finset.card_filter_add_card_filter_not
        (s := (univ : Finset Y)) (fun y : Y ↦ σ y = y ∧ (0 : ZMod m) = 0)
      rw [hsame, Finset.card_univ] at this
      omega
    have hle : (univ.filter fun y : Y ↦ σ y = y).card ≤ Fintype.card Y := by
      calc (univ.filter fun y : Y ↦ σ y = y).card
          ≤ (univ : Finset Y).card := Finset.card_filter_le _ _
        _ = Fintype.card Y := Finset.card_univ
    rw [hcompl, Nat.cast_sub hle, fixedDensity]
    field_simp

end NonsoficGroupsExist
