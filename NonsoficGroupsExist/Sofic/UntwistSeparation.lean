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


/-! ## Torsion pins the phase, and an involution keeps half its fixed points

The results above depend on a choice of scalar normalization.  For a torsion
element there is no such freedom, because the phases restrict to a
*homomorphism* on the stabilizer of a point: if `σ_g y = y` and `σ_h y = y` then
`d_{gh}(y) = d_g(y) + d_h(y)`.  For an involution this pins `d_g(y)` to the
`2`-torsion of `ℤ/m`, so it takes at most two values on `Fix(σ_g)`, and a small
trace then *forces* the two classes to be balanced rather than merely permitting
it.  The untwisted model keeps half the fixed points, unconditionally.
-/

/-- **At a fixed point the phase of a square is twice the phase.**  This is the
statement that the phases restrict to a homomorphism on the stabilizer of a
point, in the case that is needed below. -/
theorem phase_double_at_fixed (Y : FiniteModel) (m : ℕ)
    (d e : Y → ZMod m) (σ : Equiv.Perm Y)
    (hsq : ∀ y, e y = d (σ y) + d y) (y : Y) (hy : σ y = y) :
    e y = 2 * d y := by
  rw [hsq y, hy]
  ring

/-- **The phase of an involution at a fixed point is `2`-torsion.**  So it takes
at most `gcd(2,m)` values there, rather than the `m` values a general phase may
take. -/
theorem phase_two_torsion (Y : FiniteModel) (m : ℕ)
    (d e : Y → ZMod m) (σ : Equiv.Perm Y)
    (hsq : ∀ y, e y = d (σ y) + d y) (htriv : ∀ y, e y = 0)
    (y : Y) (hy : σ y = y) : 2 * d y = 0 := by
  rw [← phase_double_at_fixed Y m d e σ hsq y hy, htriv y]

/-- **A balanced two-class count keeps half.**  If the fixed points carry only
two phase values and the two classes differ in size by at most `E` -- which is
what a trace bound says, since the two values contribute opposite signs -- then
the `0` class holds at least half the fixed points, less `E/2`. -/
theorem card_zero_class_ge (Y : FiniteModel) (m : ℕ)
    (d : Y → ZMod m) (σ : Equiv.Perm Y) {c : ZMod m} (hc : c ≠ 0)
    (htwo : ∀ y, σ y = y → d y = 0 ∨ d y = c) {E : ℝ}
    (hbal : ((univ.filter fun y : Y ↦ σ y = y ∧ d y = c).card : ℝ)
              - ((univ.filter fun y : Y ↦ σ y = y ∧ d y = 0).card : ℝ) ≤ E) :
    ((univ.filter fun y : Y ↦ σ y = y).card : ℝ) - E
      ≤ 2 * ((univ.filter fun y : Y ↦ σ y = y ∧ d y = 0).card : ℝ) := by
  classical
  have hdisj : Disjoint (univ.filter fun y : Y ↦ σ y = y ∧ d y = 0)
      (univ.filter fun y : Y ↦ σ y = y ∧ d y = c) := by
    rw [Finset.disjoint_left]
    intro y hy0 hyc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy0 hyc
    exact hc (hyc.2 ▸ hy0.2 ▸ rfl)
  have hpart : (univ.filter fun y : Y ↦ σ y = y).card
      = (univ.filter fun y : Y ↦ σ y = y ∧ d y = 0).card
        + (univ.filter fun y : Y ↦ σ y = y ∧ d y = c).card := by
    rw [← Finset.card_union_of_disjoint hdisj]
    congr 1
    ext y
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hy
      rcases htwo y hy with h | h
      · exact Or.inl ⟨hy, h⟩
      · exact Or.inr ⟨hy, h⟩
    · rintro (⟨hy, _⟩ | ⟨hy, _⟩) <;> exact hy
  have hpartR : ((univ.filter fun y : Y ↦ σ y = y).card : ℝ)
      = ((univ.filter fun y : Y ↦ σ y = y ∧ d y = 0).card : ℝ)
        + ((univ.filter fun y : Y ↦ σ y = y ∧ d y = c).card : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ ↦ (n : ℝ)) hpart
  linarith [hpartR, hbal]

/-- **An involution's untwisted model keeps half its fixed points.**  No scalar
normalization enters: the phase is pinned to two values by torsion, and a trace
bound `E` forces those two classes to be balanced.  So

    separation of the untwisted model  ≤  1 - (F - E/|Y|)/2,

where `F` is the fixed point density of the permutation part.  Untwisting an
involution therefore inherits its separation and halves it -- it cannot create
it. -/
theorem involution_untwist_hamming_le (Y : FiniteModel) (m : ℕ) [NeZero m]
    (d : Y → ZMod m) (σ : Equiv.Perm Y) {c : ZMod m} (hc : c ≠ 0)
    (htwo : ∀ y, σ y = y → d y = 0 ∨ d y = c) {E : ℝ}
    (hbal : ((univ.filter fun y : Y ↦ σ y = y ∧ d y = c).card : ℝ)
              - ((univ.filter fun y : Y ↦ σ y = y ∧ d y = 0).card : ℝ) ≤ E)
    (hY : 0 < Fintype.card Y) :
    hammingDistance (wreathModel Y m) (wreathPerm Y m d σ) 1
      ≤ 1 - (fixedDensity Y σ - E / Fintype.card Y) / 2 := by
  classical
  have hYR : (0 : ℝ) < Fintype.card Y := by exact_mod_cast hY
  have hkey := card_zero_class_ge Y m d σ hc htwo hbal
  rw [hammingDistance_wreathPerm_one]
  have hcompl : (univ.filter fun y : Y ↦ ¬ (σ y = y ∧ d y = 0)).card
      = Fintype.card Y - (univ.filter fun y : Y ↦ σ y = y ∧ d y = 0).card := by
    have := Finset.card_filter_add_card_filter_not
      (s := (univ : Finset Y)) (fun y : Y ↦ σ y = y ∧ d y = 0)
    rw [Finset.card_univ] at this
    omega
  have hle : (univ.filter fun y : Y ↦ σ y = y ∧ d y = 0).card ≤ Fintype.card Y := by
    calc (univ.filter fun y : Y ↦ σ y = y ∧ d y = 0).card
        ≤ (univ : Finset Y).card := Finset.card_filter_le _ _
      _ = Fintype.card Y := Finset.card_univ
  rw [hcompl, Nat.cast_sub hle, fixedDensity]
  rw [div_le_iff₀ hYR, sub_mul, one_mul]
  have hexpand : (((univ.filter fun y : Y ↦ σ y = y).card : ℝ)
        / (Fintype.card Y : ℝ) - E / (Fintype.card Y : ℝ)) / 2
        * (Fintype.card Y : ℝ)
      = (((univ.filter fun y : Y ↦ σ y = y).card : ℝ) - E) / 2 := by
    field_simp
  rw [hexpand]
  linarith [hkey]


/-! ## Coprime modulus: the phases cannot cancel at all

The involution bound is the case `n = 2` of something general.  At a fixed point
the phases restrict to a homomorphism on the stabilizer, so iterating gives
`d_{g^k}(y) = k · d_g(y)`; if `g` has order `n` then `n · d_g(y) = 0`, and
`d_g(y)` lies in the `n`-torsion of `ℤ/m`, which has `gcd(n,m)` elements.

When `gcd(n,m) = 1` that subgroup is trivial: the phase is *forced to be zero*
on the whole fixed point set.  Cancellation is then impossible, the trace of the
model equals the fixed point density on the nose, and a trace bound is a
separation bound.  So phases can help only when the modulus shares a factor with
the torsion -- which is exactly what a construction like Thom's arranges, by
taking `p`-power phases against a `p`-power centre.
-/

/-- **Iterating the stabilizer homomorphism.**  If `φ k` is the phase of `g^k`,
then at a point fixed by `g` the phases are multiples: `φ k y = k · φ 1 y`. -/
theorem phase_iterate_at_fixed (Y : FiniteModel) (m : ℕ) (φ : ℕ → Y → ZMod m)
    (σ : Equiv.Perm Y) (hzero : ∀ y, φ 0 y = 0)
    (hstep : ∀ (k : ℕ) (y : Y), φ (k + 1) y = φ k (σ y) + φ 1 y)
    (y : Y) (hy : σ y = y) : ∀ k : ℕ, φ k y = k * φ 1 y := by
  intro k
  induction k with
  | zero => rw [hzero y]; simp
  | succ k ih =>
      rw [hstep k y, hy, ih]
      push_cast
      ring

/-- **A coprime modulus kills the phase.**  If `n · x = 0` in `ℤ/m` and `n` is
prime to `m`, then `x = 0`: `n` is invertible, by Bézout. -/
theorem eq_zero_of_coprime_nsmul (m n : ℕ) (hcop : Nat.Coprime n m) (x : ZMod m)
    (hnx : (n : ZMod m) * x = 0) : x = 0 := by
  have hbez : (1 : ℤ) = (n : ℤ) * Nat.gcdA n m + (m : ℤ) * Nat.gcdB n m := by
    have h := Nat.gcd_eq_gcd_ab n m
    rw [hcop] at h
    push_cast at h ⊢
    linarith [h]
  have hcast : (1 : ZMod m) = (n : ZMod m) * ((Nat.gcdA n m : ℤ) : ZMod m) := by
    have := congrArg (fun z : ℤ ↦ ((z : ZMod m))) hbez
    push_cast at this
    rw [ZMod.natCast_self] at this
    simpa using this
  calc x = (1 : ZMod m) * x := (one_mul x).symm
    _ = ((Nat.gcdA n m : ℤ) : ZMod m) * ((n : ZMod m) * x) := by rw [hcast]; ring
    _ = 0 := by rw [hnx, mul_zero]

/-- **The phase of a torsion element vanishes on its fixed points, when the
modulus is prime to its order.**  So no cancellation is available there. -/
theorem phase_eq_zero_of_coprime (Y : FiniteModel) (m n : ℕ)
    (hcop : Nat.Coprime n m) (φ : ℕ → Y → ZMod m) (σ : Equiv.Perm Y)
    (hzero : ∀ y, φ 0 y = 0)
    (hstep : ∀ (k : ℕ) (y : Y), φ (k + 1) y = φ k (σ y) + φ 1 y)
    (htriv : ∀ y, φ n y = 0) (y : Y) (hy : σ y = y) : φ 1 y = 0 := by
  refine eq_zero_of_coprime_nsmul m n hcop (φ 1 y) ?_
  rw [← phase_iterate_at_fixed Y m φ σ hzero hstep y hy n]
  exact htriv y

/-- **With a coprime modulus, untwisting changes nothing.**  The untwisted model
has exactly the fixed points of the permutation part, so its separation is
exactly `1 - F` and the trace of the model is exactly `F`.  A trace bound is
then a separation bound, and the model is sofic on the nose. -/
theorem coprime_untwist_hamming (Y : FiniteModel) (m : ℕ) [NeZero m]
    (d : Y → ZMod m) (σ : Equiv.Perm Y) (hd : ∀ y, σ y = y → d y = 0)
    (hY : 0 < Fintype.card Y) :
    hammingDistance (wreathModel Y m) (wreathPerm Y m d σ) 1
      = 1 - fixedDensity Y σ := by
  classical
  have hYR : (0 : ℝ) < Fintype.card Y := by exact_mod_cast hY
  rw [hammingDistance_wreathPerm_one]
  have hsame : (univ.filter fun y : Y ↦ σ y = y ∧ d y = 0)
      = univ.filter fun y : Y ↦ σ y = y := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, hd y h⟩⟩
  have hcompl : (univ.filter fun y : Y ↦ ¬ (σ y = y ∧ d y = 0)).card
      = Fintype.card Y - (univ.filter fun y : Y ↦ σ y = y).card := by
    have := Finset.card_filter_add_card_filter_not
      (s := (univ : Finset Y)) (fun y : Y ↦ σ y = y ∧ d y = 0)
    rw [hsame, Finset.card_univ] at this
    omega
  have hle : (univ.filter fun y : Y ↦ σ y = y).card ≤ Fintype.card Y := by
    calc (univ.filter fun y : Y ↦ σ y = y).card
        ≤ (univ : Finset Y).card := Finset.card_filter_le _ _
      _ = Fintype.card Y := Finset.card_univ
  rw [hcompl, Nat.cast_sub hle, fixedDensity]
  field_simp


/-! ## Cancellation can buy everything, if the torsion allows

`monomial_normTrace_zero_of_identity` exhibits a monomial matrix of trace zero
whose permutation part is the identity: the phases `1` and `-1` on two points.
It is tempting to conclude that a trace which vanishes by *cancellation* is
worthless for soficity, since nothing is moved.  That conclusion is false, and
the identity `hammingDistance_wreathPerm_one` says why: the untwisted model is
separated by the scarcity of points that are fixed **and trivially phased**, so
a phase which never vanishes on the fixed points untwists to a fixed point free
permutation, however little the permutation part moves.

The two witnesses below are the same configuration -- identity permutation,
trace zero, two points -- distinguished only by the torsion of the phase.  With
`2`-torsion phases `±1` the untwisted model keeps half its points fixed, exactly
as `involution_untwist_hamming_le` requires.  With `4`-torsion phases `±i` it
keeps none, and untwisting is perfect.  Cancellation buys nothing at order two
and everything at order four.
-/

/-- **A phase that never vanishes on the fixed points untwists to a fixed point
free permutation.**  Separation of the untwisted model is scarcity of
*trivially phased* fixed points, not scarcity of fixed points. -/
theorem untwist_hamming_eq_one_of_phase_ne_zero (Y : FiniteModel) (m : ℕ)
    [NeZero m] (d : Y → ZMod m) (σ : Equiv.Perm Y)
    (hd : ∀ y, σ y = y → d y ≠ 0) (hY : 0 < Fintype.card Y) :
    hammingDistance (wreathModel Y m) (wreathPerm Y m d σ) 1 = 1 := by
  classical
  have hYR : (0 : ℝ) < Fintype.card Y := by exact_mod_cast hY
  rw [hammingDistance_wreathPerm_one]
  have hall : (univ.filter fun y : Y ↦ ¬ (σ y = y ∧ d y = 0)) = (univ : Finset Y) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    rintro ⟨hfix, hzero⟩
    exact hd y hfix hzero
  rw [hall, Finset.card_univ]
  field_simp

/-- **Cancellation buys everything at order four.**  Two points, the identity
permutation, phases `±i`: the trace is zero and the untwisted permutation is
fixed point free, so the untwisted model is maximally separated even though the
permutation part moves nothing at all. -/
theorem untwist_full_separation_witness :
    ∃ (Y : FiniteModel) (d : Y → ℂ) (e : Y → ZMod 4),
      (∀ i, Complex.normSq (d i) = 1) ∧
      normTrace Y (monomialMatrix Y d 1) = 0 ∧
      hammingDistance (wreathModel Y 4) (wreathPerm Y 4 e 1) 1 = 1 := by
  classical
  refine ⟨(⟨Bool, inferInstance, inferInstance⟩ : FiniteModel),
    fun b : Bool ↦ if b = true then Complex.I else -Complex.I,
    fun b : Bool ↦ if b = true then (1 : ZMod 4) else 3, ?_, ?_, ?_⟩
  · intro i
    by_cases h : i = true <;> simp [h]
  · have htr : Matrix.trace
        (monomialMatrix (⟨Bool, inferInstance, inferInstance⟩ : FiniteModel)
          (fun b : Bool ↦ if b = true then Complex.I else -Complex.I) 1) = 0 := by
      show (∑ i : Bool, (if (1 : Equiv.Perm Bool) i = i then
        (if i = true then Complex.I else -Complex.I) else 0)) = 0
      rw [Fintype.sum_bool]
      norm_num
    rw [normTrace, htr, zero_div]
  · refine untwist_hamming_eq_one_of_phase_ne_zero _ 4 _ 1 ?_ (by decide)
    intro y _
    by_cases h : y = true <;> simp [h] <;> decide

/-- **Cancellation buys nothing at order two.**  The same configuration with
`2`-torsion phases keeps half its points fixed after untwisting, which is the
bound of `involution_untwist_hamming_le` attained. -/
theorem untwist_half_separation_witness :
    ∃ (Y : FiniteModel) (d : Y → ℂ) (e : Y → ZMod 2),
      (∀ i, Complex.normSq (d i) = 1) ∧
      normTrace Y (monomialMatrix Y d 1) = 0 ∧
      hammingDistance (wreathModel Y 2) (wreathPerm Y 2 e 1) 1 = 1 / 2 := by
  classical
  refine ⟨(⟨Bool, inferInstance, inferInstance⟩ : FiniteModel),
    fun b : Bool ↦ if b = true then (1 : ℂ) else -1,
    fun b : Bool ↦ if b = true then (0 : ZMod 2) else 1, ?_, ?_, ?_⟩
  · intro i
    by_cases h : i = true <;> simp [h]
  · have htr : Matrix.trace
        (monomialMatrix (⟨Bool, inferInstance, inferInstance⟩ : FiniteModel)
          (fun b : Bool ↦ if b = true then (1 : ℂ) else -1) 1) = 0 := by
      show (∑ i : Bool, (if (1 : Equiv.Perm Bool) i = i then
        (if i = true then (1 : ℂ) else -1) else 0)) = 0
      rw [Fintype.sum_bool]
      norm_num
    rw [normTrace, htr, zero_div]
  · rw [hammingDistance_wreathPerm_one]
    have hfil : (univ.filter fun b : Bool ↦
        ¬ ((1 : Equiv.Perm Bool) b = b ∧ (if b = true then (0 : ZMod 2) else 1) = 0))
        = {false} := by decide
    rw [hfil]
    norm_num
    rw [show Fintype.card
      (⟨Bool, inferInstance, inferInstance⟩ : FiniteModel).carrier = 2 from rfl]
    norm_num

end NonsoficGroupsExist
