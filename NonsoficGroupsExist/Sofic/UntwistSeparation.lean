import NonsoficGroupsExist.Sofic.ScalarCocycle
import NonsoficGroupsExist.Sofic.CharacterCount

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


/-! ## Untwisting always at least halves the fixed points

The witnesses above bracket the question from both sides at particular orders.
There is a general bound, and it is the reason the involution is extremal.

A trivially phased fixed point contributes `+1` to the trace, and every other
fixed point contributes at least `-1`, since the phases are unimodular.  So a
trace bound `ε` forces

    #{ y : σy = y and d y = 1 }  ≤  (#Fix(σ) + ε|Y|) / 2

(`card_trivially_phased_le`) with no hypothesis on the torsion whatever.
Untwisting therefore always removes at least half the fixed points, and by
`involution_untwist_hamming_le` an involution removes exactly half.  The
involution is the worst case, and the two bounds meet there.
-/

/-- **At most half the fixed points of a small-trace monomial matrix are
trivially phased.**  A trivially phased fixed point contributes `+1` to the
trace and every other fixed point at least `-1`, so the trace bound is a
counting bound.  No assumption on the torsion of the phases is used. -/
theorem card_trivially_phased_le (Y : FiniteModel) (d : Y → ℂ)
    (hd : ∀ y, Complex.normSq (d y) = 1) (σ : Equiv.Perm Y)
    (hY : 0 < Fintype.card Y) {ε : ℝ}
    (htr : (normTrace Y (monomialMatrix Y d σ)).re ≤ ε) :
    2 * ((univ.filter fun y : Y ↦ σ y = y ∧ d y = 1).card : ℝ)
      ≤ ((univ.filter fun y : Y ↦ σ y = y).card : ℝ) + ε * Fintype.card Y := by
  classical
  have hYR : (0 : ℝ) < Fintype.card Y := by exact_mod_cast hY
  -- the trace is the sum of the phases over the fixed points
  have htrace : Matrix.trace (monomialMatrix Y d σ)
      = ∑ y ∈ univ.filter fun y : Y ↦ σ y = y, d y := by
    rw [Matrix.trace]
    simp only [Matrix.diag_apply, monomialMatrix_apply]
    rw [Finset.sum_filter]
  -- every phase has real part at least -1
  have hre_ge : ∀ y : Y, (-1 : ℝ) ≤ (d y).re := by
    intro y
    have h := hd y
    rw [Complex.normSq_apply] at h
    nlinarith [sq_nonneg ((d y).im), sq_nonneg ((d y).re + 1)]
  -- split the fixed points into the trivially phased ones and the rest
  set S : Finset Y := univ.filter fun y : Y ↦ σ y = y with hS
  set T : Finset Y := univ.filter fun y : Y ↦ σ y = y ∧ d y = 1 with hT
  have hTS : T ⊆ S := by
    intro y hy
    rw [hT, Finset.mem_filter] at hy
    rw [hS, Finset.mem_filter]
    exact ⟨hy.1, hy.2.1⟩
  have hsplit : ∑ y ∈ S, (d y).re
      = ∑ y ∈ T, (d y).re + ∑ y ∈ S \ T, (d y).re := by
    rw [← Finset.sum_union (Finset.disjoint_sdiff)]
    congr 1
    rw [Finset.union_sdiff_of_subset hTS]
  have hTone : ∑ y ∈ T, (d y).re = (T.card : ℝ) := by
    rw [Finset.sum_congr rfl (fun y hy ↦ ?_), Finset.sum_const, nsmul_eq_mul,
      mul_one]
    rw [hT, Finset.mem_filter] at hy
    rw [hy.2.2]
    rfl
  have hrest : ((S \ T).card : ℝ) * (-1) ≤ ∑ y ∈ S \ T, (d y).re := by
    calc ((S \ T).card : ℝ) * (-1) = ∑ _y ∈ S \ T, (-1 : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ y ∈ S \ T, (d y).re := Finset.sum_le_sum fun y _ ↦ hre_ge y
  have hcard : ((S \ T).card : ℝ) = (S.card : ℝ) - (T.card : ℝ) := by
    have hadd : (S \ T).card + T.card = S.card :=
      Finset.card_sdiff_add_card_eq_card hTS
    have : ((S \ T).card : ℝ) + (T.card : ℝ) = (S.card : ℝ) := by
      exact_mod_cast congrArg (fun n : ℕ ↦ (n : ℝ)) hadd
    linarith [this]
  -- the trace bound
  have hRe : ∑ y ∈ S, (d y).re ≤ ε * Fintype.card Y := by
    have hnt : (normTrace Y (monomialMatrix Y d σ)).re
        = (∑ y ∈ S, (d y).re) / Fintype.card Y := by
      rw [normTrace, htrace, Complex.div_re]
      simp only [Complex.natCast_re, Complex.natCast_im, Complex.normSq_natCast,
        Complex.re_sum]
      by_cases hz : (Fintype.card Y : ℝ) = 0
      · exact absurd hz hYR.ne'
      · field_simp
        ring
    rw [hnt, div_le_iff₀ hYR] at htr
    linarith [htr]
  rw [hsplit] at hRe
  rw [hTone] at hRe
  rw [hcard] at hrest
  linarith [hRe, hrest]


/-! ## Order three also forces retention, so the trichotomy is complete

Order two forces the untwisted model to keep half its fixed points, and order
four allows it to keep none.  Order three is the remaining case, and it forces
retention too -- of a third rather than a half.  The reason is that the three
cube roots of unity are *positively* dependent: `1 + ω + ω² = 0` is their only
relation over `ℝ`, so a nonnegative combination can be small only if all three
coefficients are nearly equal.  At order four the relation `1 + i + (-1) + (-i)`
splits into two independent ones, `1 + (-1)` and `i + (-i)`, and a nonnegative
combination can vanish while missing `1` entirely -- which is exactly the
witness above.

So the trichotomy is: orders two and three force retention of `1/2` and `1/3`;
order four and beyond force nothing.
-/

/-- A primitive cube root of unity, written out so the arithmetic below is
elementary. -/
noncomputable def cubeRoot : ℂ := ⟨-1/2, Real.sqrt 3 / 2⟩

theorem cubeRoot_relation : 1 + cubeRoot + cubeRoot ^ 2 = 0 := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  apply Complex.ext <;>
    simp [cubeRoot, pow_two, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.one_re, Complex.one_im] <;>
    nlinarith [h3]

/-- **The modulus of a real combination of `1` and `ω`.**  This is where the
positive dependence of the cube roots enters: the quadratic form `a² - ab + b²`
is positive definite, so it can be small only if both coefficients are. -/
theorem normSq_cubeRoot_comb (a b : ℝ) :
    Complex.normSq ((a : ℂ) + (b : ℂ) * cubeRoot) = a ^ 2 - a * b + b ^ 2 := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  simp [cubeRoot, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im]
  nlinarith [h3]

/-- **Order three forces retention of a third.**  If the fixed points carry only
the three cube-root phases, with counts `n₀, n₁, n₂`, and the character sum has
modulus at most `E`, then

    n₀ + n₁ + n₂  ≤  3 n₀ + 3√2 · E,

so the trivially phased class holds at least a third of the fixed points, less
an error proportional to the trace bound. -/
theorem card_zero_class_ge_three (n₀ n₁ n₂ E : ℝ) (hE : 0 ≤ E)
    (htr : Complex.normSq ((n₀ : ℂ) + (n₁ : ℂ) * cubeRoot
        + (n₂ : ℂ) * cubeRoot ^ 2) ≤ E ^ 2) :
    n₀ + n₁ + n₂ ≤ 3 * n₀ + 3 * Real.sqrt 2 * E := by
  -- eliminate `ω²` by the relation
  have hsub : (n₀ : ℂ) + (n₁ : ℂ) * cubeRoot + (n₂ : ℂ) * cubeRoot ^ 2
      = ((n₀ - n₂ : ℝ) : ℂ) + ((n₁ - n₂ : ℝ) : ℂ) * cubeRoot := by
    have hw : cubeRoot ^ 2 = -1 - cubeRoot := by
      have := cubeRoot_relation
      linear_combination this
    rw [hw]
    push_cast
    ring
  rw [hsub, normSq_cubeRoot_comb] at htr
  set a : ℝ := n₀ - n₂ with ha
  set b : ℝ := n₁ - n₂ with hb
  -- the form dominates half the square norm
  have hhalf : (a ^ 2 + b ^ 2) / 2 ≤ a ^ 2 - a * b + b ^ 2 := by nlinarith [sq_nonneg (a - b)]
  have hsum : a ^ 2 + b ^ 2 ≤ 2 * E ^ 2 := by linarith [hhalf, htr]
  have hc : (Real.sqrt 2 * E) ^ 2 = 2 * E ^ 2 := by
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    nlinarith [h2]
  have hcpos : 0 ≤ Real.sqrt 2 * E := by positivity
  have hA : |a| ≤ Real.sqrt 2 * E := by
    have : a ^ 2 ≤ (Real.sqrt 2 * E) ^ 2 := by rw [hc]; nlinarith [sq_nonneg b]
    nlinarith [abs_nonneg a, sq_abs a, this, hcpos]
  have hB : |b| ≤ Real.sqrt 2 * E := by
    have : b ^ 2 ≤ (Real.sqrt 2 * E) ^ 2 := by rw [hc]; nlinarith [sq_nonneg a]
    nlinarith [abs_nonneg b, sq_abs b, this, hcpos]
  have hale : -a ≤ |a| := neg_le_abs a
  have hble : b ≤ |b| := le_abs_self b
  -- `n₀ + n₁ + n₂ = 3n₀ - 2a + b`
  have hid : n₀ + n₁ + n₂ = 3 * n₀ - 2 * a + b := by
    rw [ha, hb]; ring
  rw [hid]
  linarith [hA, hB, hale, hble]


/-! ## What actually controls the trichotomy is `gcd(n, m)`

The bounds above were stated by the order `n` of the element, but that is not
quite the invariant.  What the phase of an order-`n` element can do at a fixed
point is decided by the subgroup of `ℤ/m` it is pinned to, namely the
`n`-torsion, and that subgroup has exactly `gcd(m,n)` elements -- a count
already available as `card_annihilator`.

So the trichotomy is really in `gcd(n,m)`:

* `gcd = 1` — the phase is forced to `0`, untwisting gains nothing;
* `gcd = 2` — two values, and the trace forces balance: half is retained;
* `gcd = 3` — three values, positively dependent: a third is retained;
* `gcd ≥ 4` — the relation among the roots is no longer unique, and nothing is
  forced.

This is why an involution against an odd modulus behaves like a coprime element
rather than like an involution: `gcd(2,m) = 1` there, and it is the gcd, not the
order, that the phase sees.
-/

/-- **The `n`-torsion of `ℤ/m` has exactly `gcd(m,n)` elements.**  This is the
annihilator count of `CharacterCount` read with the roles of the two arguments
exchanged, and it is the subgroup the phase of an order-`n` element is pinned
to at any point it fixes. -/
theorem card_torsion_subgroup (m n : ℕ) [NeZero m] :
    (univ.filter fun x : ZMod m ↦ (n : ZMod m) * x = 0).card = Nat.gcd m n := by
  classical
  have hset : (univ.filter fun x : ZMod m ↦ (n : ZMod m) * x = 0)
      = univ.filter fun x : ZMod m ↦ x * (n : ZMod m) = 0 := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mul_comm]
  rw [hset, card_annihilator m ((n : ZMod m)), ZMod.val_natCast,
    Nat.gcd_rec m n]
  exact Nat.gcd_comm _ _

/-- **The phase of an order-`n` element lies in a set of `gcd(m,n)` values.**
With `gcd = 1` this is `phase_eq_zero_of_coprime`; with `gcd = 2` it supplies
the two-value hypothesis of `involution_untwist_hamming_le` rather than assuming
it; with `gcd ≥ 4` it is the room the `±i` witness exploits. -/
theorem phase_mem_torsion (Y : FiniteModel) (m n : ℕ) [NeZero m]
    (φ : ℕ → Y → ZMod m) (σ : Equiv.Perm Y)
    (hzero : ∀ y, φ 0 y = 0)
    (hstep : ∀ (k : ℕ) (y : Y), φ (k + 1) y = φ k (σ y) + φ 1 y)
    (htriv : ∀ y, φ n y = 0) (y : Y) (hy : σ y = y) :
    φ 1 y ∈ univ.filter fun x : ZMod m ↦ (n : ZMod m) * x = 0 := by
  classical
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  have hiter := phase_iterate_at_fixed Y m φ σ hzero hstep y hy n
  rw [← hiter]
  exact htriv y

/-- **The gcd is what the phase sees, not the order.**  An involution against an
odd modulus has `gcd(2,m) = 1`, so its phase is forced to vanish on its fixed
points exactly as a coprime element's is, and untwisting gains nothing at all --
even though the element has order two. -/
theorem phase_eq_zero_of_gcd_eq_one (Y : FiniteModel) (m n : ℕ) [NeZero m]
    (hgcd : Nat.gcd m n = 1) (φ : ℕ → Y → ZMod m) (σ : Equiv.Perm Y)
    (hzero : ∀ y, φ 0 y = 0)
    (hstep : ∀ (k : ℕ) (y : Y), φ (k + 1) y = φ k (σ y) + φ 1 y)
    (htriv : ∀ y, φ n y = 0) (y : Y) (hy : σ y = y) : φ 1 y = 0 := by
  classical
  have hmem := phase_mem_torsion Y m n φ σ hzero hstep htriv y hy
  have hcard := card_torsion_subgroup m n
  rw [hgcd] at hcard
  have hzero_mem : (0 : ZMod m) ∈ univ.filter fun x : ZMod m ↦ (n : ZMod m) * x = 0 := by
    simp
  have := Finset.card_eq_one.mp hcard
  obtain ⟨a, ha⟩ := this
  rw [ha, Finset.mem_singleton] at hmem hzero_mem
  rw [hmem, ← hzero_mem]


/-! ## The `gcd ≥ 4` side is an infinite family, not one example

The `±i` witness settles `gcd = 4`.  The same construction runs at every even
modulus, and needs no root-of-unity analysis: if `ζ^{m/2} = -1` then

    ζ^1 + ζ^{1 + m/2} = ζ(1 + ζ^{m/2}) = 0,

so two phase classes with equal weights cancel while *neither* is the trivial
class.  Untwisting is then fixed point free by
`untwist_hamming_eq_one_of_phase_ne_zero`, and the trace vanishes, on a model of
two points with the identity permutation.

The same idea covers composite `m` generally -- take the classes
`1 + (m/d)j` for `j < d`, whose phases sum to `ζ(1 + ω + ... + ω^{d-1}) = 0` for
`ω = ζ^{m/d}` a primitive `d`-th root -- and the exponents miss `0` exactly when
`d < m`.  Only prime `m ≥ 5` needs genuinely irrational weights; at `m = 5` they
are the golden ratio, which is the same constant that appears in
`re_pow_max_sharp`.  Neither of those generalizations is formalized here; what
is formalized is the even family below.
-/

/-- **A vanishing pair of nontrivial phases at every even modulus.**  Two classes
with equal weights cancel, and neither is the trivial class. -/
theorem phase_pair_cancels (m : ℕ) (ζ : ℂ) (hζ : ζ ^ (m / 2) = -1) :
    ζ ^ 1 + ζ ^ (1 + m / 2) = 0 := by
  rw [pow_add, hζ, pow_one]
  ring

/-- **The order-four witness generalizes to every even modulus.**  Two points,
the identity permutation, phases `ζ` and `-ζ`: the trace is zero and the
untwisted permutation is fixed point free, so the untwisted model is maximally
separated although the permutation part moves nothing.

So `gcd ≥ 4` failing to force anything is an infinite family of witnesses, not a
single accident at `4`. -/
theorem untwist_full_separation_witness_even (m : ℕ) [NeZero m] (hm : 4 ≤ m)
    (hev : 2 ∣ m) (ζ : ℂ) (hnorm : Complex.normSq ζ = 1) :
    ∃ (Y : FiniteModel) (d : Y → ℂ) (e : Y → ZMod m),
      (∀ i, Complex.normSq (d i) = 1) ∧
      normTrace Y (monomialMatrix Y d 1) = 0 ∧
      hammingDistance (wreathModel Y m) (wreathPerm Y m e 1) 1 = 1 := by
  classical
  have hhalf : 0 < m / 2 := by omega
  have hlt : 1 + m / 2 < m := by omega
  -- neither class is the trivial one
  have hne1 : (1 : ZMod m) ≠ 0 := by
    haveI : Fact (1 < m) := ⟨by omega⟩
    exact one_ne_zero
  have hne2 : ((1 + m / 2 : ℕ) : ZMod m) ≠ 0 := by
    intro hcon
    have hval : ((1 + m / 2 : ℕ) : ZMod m).val = 0 := by rw [hcon]; simp
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt] at hval
    omega
  refine ⟨(⟨Bool, inferInstance, inferInstance⟩ : FiniteModel),
    fun b : Bool ↦ if b = true then ζ else -ζ,
    fun b : Bool ↦ if b = true then (1 : ZMod m) else ((1 + m / 2 : ℕ) : ZMod m),
    ?_, ?_, ?_⟩
  · intro i
    by_cases h : i = true <;> simp [h, hnorm]
  · have htr : Matrix.trace
        (monomialMatrix (⟨Bool, inferInstance, inferInstance⟩ : FiniteModel)
          (fun b : Bool ↦ if b = true then ζ else -ζ) 1) = 0 := by
      show (∑ i : Bool, (if (1 : Equiv.Perm Bool) i = i then
        (if i = true then ζ else -ζ) else 0)) = 0
      rw [Fintype.sum_bool]
      simp
    rw [normTrace, htr, zero_div]
  · refine untwist_hamming_eq_one_of_phase_ne_zero _ m _ 1 ?_ (by decide)
    intro y _
    by_cases h : y = true
    · simpa [h] using hne1
    · simpa [h] using hne2


/-! ## The odd moduli too, so `gcd ≥ 4` is settled in general

The even family above is trig-free because `1 + (-1) = 0` does all the work.  At
an odd modulus no two nontrivial classes cancel on their own, and the weights
have to be unequal.  That is not an artifact: for *prime* `m` the numbers
`1, ζ, …, ζ^{m-1}` satisfy only the one rational relation `Σ ζ^k = 0`, which
involves the trivial class, so no rational nonnegative combination of the
nontrivial classes can vanish and irrational weights are forced.

They are easy to write down.  Weight the two classes adjacent to the trivial one
by `1 + 1/(2 Re ζ)` and every other nontrivial class by `1`; since
`Σ_{k=1}^{m-1} ζ^k = -1` and `ζ + ζ^{m-1} = 2 Re ζ`, the total is
`-1 + 2 Re ζ /(2 Re ζ) = 0`.  All weights are positive exactly when `Re ζ > 0`,
which for `ζ = e^{2πi/m}` says `m ≥ 5`.
-/

/-- The nontrivial classes sum to `-1`. -/
theorem geom_nontrivial_sum (m : ℕ) (hm : 1 ≤ m) (ζ : ℂ) (hpow : ζ ^ m = 1)
    (hne : ζ ≠ 1) : ∑ k ∈ Finset.Ico 1 m, ζ ^ k = -1 := by
  have hgeom : ∑ k ∈ Finset.range m, ζ ^ k = 0 := by
    rw [geom_sum_eq hne m, hpow]
    simp
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)] at hgeom
  simp only [pow_zero, zero_add] at hgeom
  linear_combination hgeom

/-- `ζ^{m-1}` is the conjugate of `ζ`, so the two classes adjacent to the trivial
one sum to `2 Re ζ`. -/
theorem adjacent_pair_sum (m : ℕ) (hm : 1 ≤ m) (ζ : ℂ) (hpow : ζ ^ m = 1)
    (hnorm : Complex.normSq ζ = 1) :
    ζ ^ 1 + ζ ^ (m - 1) = 2 * (ζ.re : ℂ) := by
  have hz : ζ ≠ 0 := by
    intro h
    rw [h] at hnorm
    simp at hnorm
  have hsplit : ζ ^ (m - 1) * ζ = 1 := by
    rw [← pow_succ]
    rw [Nat.sub_add_cancel hm]
    exact hpow
  have hconj : ζ ^ (m - 1) = (starRingEnd ℂ) ζ := by
    have hinv : ζ ^ (m - 1) = ζ⁻¹ := eq_inv_of_mul_eq_one_left hsplit
    rw [hinv, Complex.inv_def, hnorm]
    simp
  rw [pow_one, hconj, Complex.add_conj]
  push_cast
  ring

/-- **A vanishing nonnegative combination of the nontrivial classes, at every
modulus with `Re ζ > 0`.**  For `ζ = e^{2πi/m}` that condition is `m ≥ 5`, so
together with the even family it settles `gcd ≥ 4` in general: the trivial class
can always be missed. -/
theorem phase_weights_cancel (m : ℕ) (hm : 2 ≤ m) (ζ : ℂ) (hpow : ζ ^ m = 1)
    (hne : ζ ≠ 1) (hnorm : Complex.normSq ζ = 1) (hre : 0 < ζ.re) :
    ∑ k ∈ Finset.Ico 1 m,
        ((1 : ℝ) + (if k = 1 ∨ k = m - 1 then 1 / (2 * ζ.re) else 0) : ℝ) * ζ ^ k
      = 0 := by
  classical
  have hone : (1 : ℕ) ∈ Finset.Ico 1 m := by simp; omega
  have hlast : (m - 1) ∈ Finset.Ico 1 m := by simp; omega
  have hbase := geom_nontrivial_sum m (by omega) ζ hpow hne
  have hpair := adjacent_pair_sum m (by omega) ζ hpow hnorm
  have hsplit : ∑ k ∈ Finset.Ico 1 m,
      ((1 : ℝ) + (if k = 1 ∨ k = m - 1 then 1 / (2 * ζ.re) else 0) : ℝ) * ζ ^ k
      = (∑ k ∈ Finset.Ico 1 m, ζ ^ k)
        + ∑ k ∈ Finset.Ico 1 m,
            ((if k = 1 ∨ k = m - 1 then (1 : ℝ) / (2 * ζ.re) else 0) : ℝ) * ζ ^ k := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    push_cast
    ring
  rw [hsplit, hbase]
  by_cases hm2 : m = 2
  · exfalso
    subst hm2
    have hz : ζ = -1 := by
      have : (ζ - 1) * (ζ + 1) = 0 := by
        have : ζ ^ 2 = 1 := hpow
        linear_combination this
      rcases mul_eq_zero.mp this with h | h
      · exact absurd (by linear_combination h) hne
      · linear_combination h
    rw [hz] at hre
    norm_num at hre
  · have hdistinct : (1 : ℕ) ≠ m - 1 := by omega
    have hfilter : ∑ k ∈ Finset.Ico 1 m,
        ((if k = 1 ∨ k = m - 1 then (1 : ℝ) / (2 * ζ.re) else 0) : ℝ) * ζ ^ k
        = ((1 : ℝ) / (2 * ζ.re) : ℝ) * (ζ ^ 1 + ζ ^ (m - 1)) := by
      rw [Finset.sum_eq_add_of_mem 1 (m - 1) hone hlast hdistinct (by
        intro k _ hk
        simp [hk.1, hk.2])]
      simp only [true_or, or_true, if_true]
      push_cast
      ring
    rw [hfilter, hpair]
    have hre' : (ζ.re : ℂ) ≠ 0 := by
      simpa using (ne_of_gt hre)
    have hcancel : ((1 / (2 * ζ.re) : ℝ) : ℂ) * (2 * (ζ.re : ℂ)) = 1 := by
      push_cast
      field_simp
    linear_combination hcancel


/-! ## The renormalization freedom is a homomorphism, not a free choice

`exists_shift_hamming_le` produces, for a single element, a scalar `c` whose
class retains a `1/m` share of the fixed points, and scalar changes are
invisible to the Hilbert--Schmidt metric.  It is tempting to read that as *the
metric cannot rule out a bad normalization*.  That reading is too generous to
the adversary, and this section says why.

A renormalization of a whole phase system, `d_g ↦ d_g + β(g)`, has to preserve
multiplicativity, or the renormalized data is not a model at all.  Subtracting
the two multiplicativity identities leaves

    β(gh) = β(g) + β(h),

so `β` is a *homomorphism* `G → ℤ/m` (`renormalization_isHom`), not a free
choice of one constant per element.  Being a homomorphism into an abelian group
it kills commutators (`renormalization_commutator`), so on a group in which
every element is a commutator the only renormalization is the trivial one
(`renormalization_eq_zero_of_commutators`).

For such a group the phase system therefore *does* determine the untwisted
separation: there is no metrically invisible reshuffling to hide behind, and the
`c` supplied by the pigeonhole, while a genuine scalar for that one element, is
not available as a renormalization of the model.
-/

section Renormalization

variable {G : Type*} [Group G] {Y : Type*} {m : ℕ}

/-- **A renormalization preserving multiplicativity is a homomorphism.**
Subtract the two multiplicativity identities at any point of the model. -/
theorem renormalization_isHom (act : G → Equiv.Perm Y) (d : G → Y → ZMod m)
    (β : G → ZMod m) (y : Y)
    (hd : ∀ (g h : G) (z : Y), d (g * h) z = d g (act h z) + d h z)
    (hd' : ∀ (g h : G) (z : Y),
      d (g * h) z + β (g * h) = (d g (act h z) + β g) + (d h z + β h))
    (g h : G) : β (g * h) = β g + β h := by
  have h1 := hd g h y
  have h2 := hd' g h y
  rw [h1] at h2
  linear_combination h2

variable (β : G → ZMod m)

/-- A homomorphism sends the identity to zero. -/
theorem renormalization_one (hβ : ∀ g h : G, β (g * h) = β g + β h) : β 1 = 0 := by
  have h := hβ 1 1
  rw [mul_one] at h
  have h2 : (0 : ZMod m) = β 1 := by linear_combination h
  exact h2.symm

/-- and inverses to negatives. -/
theorem renormalization_inv (hβ : ∀ g h : G, β (g * h) = β g + β h) (g : G) :
    β g⁻¹ = - β g := by
  have h := hβ g g⁻¹
  rw [mul_inv_cancel, renormalization_one β hβ] at h
  linear_combination -h

/-- **A renormalization kills commutators**, being a homomorphism into an
abelian group. -/
theorem renormalization_commutator (hβ : ∀ g h : G, β (g * h) = β g + β h)
    (a b : G) : β (a * b * a⁻¹ * b⁻¹) = 0 := by
  rw [hβ, hβ, hβ, renormalization_inv β hβ, renormalization_inv β hβ]
  ring

/-- **On a group in which every element is a commutator, the only
renormalization is trivial.**  The phase system then determines the untwisted
separation outright: there is no metrically invisible reshuffling available. -/
theorem renormalization_eq_zero_of_commutators
    (hβ : ∀ g h : G, β (g * h) = β g + β h)
    (hcomm : ∀ g : G, ∃ a b : G, g = a * b * a⁻¹ * b⁻¹) (g : G) : β g = 0 := by
  obtain ⟨a, b, rfl⟩ := hcomm g
  exact renormalization_commutator β hβ a b

/-! ### The same argument applies to the phases themselves

Nothing above used that `β` came from a renormalization; only that it was a
`ℤ/m`-valued function turning products into sums.  At a point fixed by *every*
element the phase function `g ↦ d_g(y)` is exactly that, because the action
never moves `y` out of the way.  So on a group in which every element is a
commutator the phase vanishes there identically -- phases are powerless at a
globally fixed point.
-/

/-- **At a globally fixed point the phase is a homomorphism.** -/
theorem phase_isHom_at_global_fixed (act : G → Equiv.Perm Y) (d : G → Y → ZMod m)
    (hd : ∀ (g h : G) (z : Y), d (g * h) z = d g (act h z) + d h z)
    (y : Y) (hfix : ∀ g : G, act g y = y) (g h : G) :
    d (g * h) y = d g y + d h y := by
  rw [hd g h y, hfix h]

/-- **On a perfect group the phase vanishes at a globally fixed point.**  A
point the model never moves carries no phase at all, so it survives untwisting
as a fixed point: phases cannot rescue it. -/
theorem phase_eq_zero_at_global_fixed (act : G → Equiv.Perm Y)
    (d : G → Y → ZMod m)
    (hd : ∀ (g h : G) (z : Y), d (g * h) z = d g (act h z) + d h z)
    (y : Y) (hfix : ∀ g : G, act g y = y)
    (hcomm : ∀ g : G, ∃ a b : G, g = a * b * a⁻¹ * b⁻¹) (g : G) : d g y = 0 :=
  renormalization_eq_zero_of_commutators (fun g ↦ d g y)
    (phase_isHom_at_global_fixed act d hd y hfix) hcomm g

/-! ### The local form, which is what a model can supply

The statement above quantifies over the whole group, and a model does not have a
whole group -- it has a finite window and an approximate action, so no genuine
stabilizer subgroup.  The argument survives anyway, because it is local: to kill
the phase of a commutator `[a,b]` at a point `y` one needs only that `a`, `b`
and their inverses fix `y`.  Perfection of `G` is not used, and neither is any
closure property of the window beyond naming the four elements involved.

So in *any* monomial model, at any point fixed by `a`, `b`, `a⁻¹`, `b⁻¹`, the
commutator `[a,b]` is trivially phased.  On a group whose elements are
commutators, that is a statement about the elements one actually has to separate.
-/

/-- The phase of the identity vanishes. -/
theorem phase_one_eq_zero (act : G → Equiv.Perm Y) (d : G → Y → ZMod m)
    (hd : ∀ (g h : G) (z : Y), d (g * h) z = d g (act h z) + d h z)
    (y : Y) (h1 : act 1 y = y) : d 1 y = 0 := by
  have h := hd 1 1 y
  rw [mul_one, h1] at h
  have h2 : (0 : ZMod m) = d 1 y := by linear_combination h
  exact h2.symm

/-- The phase of an inverse is the negative, at a point both fix. -/
theorem phase_inv (act : G → Equiv.Perm Y) (d : G → Y → ZMod m)
    (hd : ∀ (g h : G) (z : Y), d (g * h) z = d g (act h z) + d h z)
    (y : Y) (h1 : act 1 y = y) (g : G) (hgi : act g⁻¹ y = y) :
    d g⁻¹ y = - d g y := by
  have h := hd g g⁻¹ y
  rw [mul_inv_cancel, hgi, phase_one_eq_zero act d hd y h1] at h
  linear_combination -h

/-- **A commutator is trivially phased at any point fixing its constituents.**
Entirely local: only `a`, `b`, `a⁻¹`, `b⁻¹` need fix `y`, and nothing is assumed
about the group or about the rest of the window. -/
theorem phase_commutator_local (act : G → Equiv.Perm Y) (d : G → Y → ZMod m)
    (hd : ∀ (g h : G) (z : Y), d (g * h) z = d g (act h z) + d h z)
    (y : Y) (h1 : act 1 y = y) (a b : G)
    (hb : act b y = y) (hai : act a⁻¹ y = y) (hbi : act b⁻¹ y = y) :
    d (a * b * a⁻¹ * b⁻¹) y = 0 := by
  have e1 : d (a * b * a⁻¹ * b⁻¹) y = d (a * b * a⁻¹) y + d b⁻¹ y := by
    rw [hd (a * b * a⁻¹) b⁻¹ y, hbi]
  have e2 : d (a * b * a⁻¹) y = d (a * b) y + d a⁻¹ y := by
    rw [hd (a * b) a⁻¹ y, hai]
  have e3 : d (a * b) y = d a y + d b y := by
    rw [hd a b y, hb]
  have ea : d a⁻¹ y = - d a y := phase_inv act d hd y h1 a hai
  have eb : d b⁻¹ y = - d b y := phase_inv act d hd y h1 b hbi
  rw [e1, e2, e3, ea, eb]
  ring

end Renormalization

/-- A point the permutation fixes and the phase does not see stays fixed after
untwisting, in every fibre. -/
theorem wreathPerm_fixes (Y : FiniteModel) (m : ℕ) [NeZero m] (d : Y → ZMod m)
    (σ : Equiv.Perm Y) (y : Y) (hy : σ y = y) (hd : d y = 0) (j : ZMod m) :
    wreathPerm Y m d σ (y, j) = (y, j) := by
  show (σ y, j + d y) = (y, j)
  rw [hy, hd, add_zero]



/-! ## The counting step: how many points fix both

`phase_commutator_local` needs a point fixed by `b`, `a⁻¹` and `b⁻¹`.  Since a
permutation and its inverse have the same fixed points, that is a point fixed by
`a` and by `b`, and Bonferroni bounds those from below by `F_a + F_b - 1`.

So the untwisted model retains at least `F_a + F_b - 1` of its points as fixed
points of `[a,b]`, and its separation there is at most `2 - F_a - F_b`.  Read the
other way: if the untwisted model separates `[a,b]` to within `ε`, then
`F_a + F_b ≤ 1 + ε`, so at most one element of the window can fix more than half
the model.  This is the quantitative form of "untwisting only inherits
separation", now in terms of the permutation parts alone.

The one thing here that a genuinely approximate model does not supply for free
is that `act` is a homomorphism; that is where such a model pays its defect.
-/

/-- Fixed points of a permutation and of its inverse coincide. -/
theorem fixed_inv_iff (Y : FiniteModel) (σ : Equiv.Perm Y) (y : Y) :
    σ⁻¹ y = y ↔ σ y = y := by
  rw [Equiv.Perm.inv_eq_iff_eq, eq_comm]

/-- **Bonferroni.**  Two large fixed sets must meet. -/
theorem card_inter_fixed_ge (Y : FiniteModel) (σ τ : Equiv.Perm Y) :
    ((univ.filter fun y : Y ↦ σ y = y).card : ℝ)
        + ((univ.filter fun y : Y ↦ τ y = y).card : ℝ) - Fintype.card Y
      ≤ ((univ.filter fun y : Y ↦ σ y = y ∧ τ y = y).card : ℝ) := by
  classical
  have hunion := Finset.card_union_add_card_inter
    (univ.filter fun y : Y ↦ σ y = y) (univ.filter fun y : Y ↦ τ y = y)
  have hle : ((univ.filter fun y : Y ↦ σ y = y)
      ∪ (univ.filter fun y : Y ↦ τ y = y)).card ≤ Fintype.card Y := by
    calc ((univ.filter fun y : Y ↦ σ y = y)
        ∪ (univ.filter fun y : Y ↦ τ y = y)).card
        ≤ (univ : Finset Y).card := Finset.card_le_card (Finset.subset_univ _)
      _ = Fintype.card Y := Finset.card_univ
  have hinter : ((univ.filter fun y : Y ↦ σ y = y)
      ∩ (univ.filter fun y : Y ↦ τ y = y))
      = univ.filter fun y : Y ↦ σ y = y ∧ τ y = y := by
    ext y
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hinter] at hunion
  have hleR : (((univ.filter fun y : Y ↦ σ y = y)
      ∪ (univ.filter fun y : Y ↦ τ y = y)).card : ℝ) ≤ Fintype.card Y := by
    exact_mod_cast hle
  have hunionR : (((univ.filter fun y : Y ↦ σ y = y)
        ∪ (univ.filter fun y : Y ↦ τ y = y)).card : ℝ)
      + ((univ.filter fun y : Y ↦ σ y = y ∧ τ y = y).card : ℝ)
      = ((univ.filter fun y : Y ↦ σ y = y).card : ℝ)
        + ((univ.filter fun y : Y ↦ τ y = y).card : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ ↦ (n : ℝ)) hunion
  linarith [hleR, hunionR]

/-- **The untwisted model retains the commutator's fixed points.**  Every point
fixed by `a` and by `b` is fixed by `[a,b]` and trivially phased there, so it
survives untwisting; Bonferroni counts them.  Hence

    separation of the untwisted `[a,b]`  ≤  2 - F_a - F_b,

and if that separation is within `ε` then `F_a + F_b ≤ 1 + ε`: at most one
element of the window fixes more than half the model. -/
theorem untwist_retains_commutator {G : Type*} [Group G] (Y : FiniteModel)
    (m : ℕ) [NeZero m] (act : G → Equiv.Perm Y) (d : G → Y → ZMod m)
    (hact : ∀ g h : G, act (g * h) = act g * act h)
    (hd : ∀ (g h : G) (z : Y), d (g * h) z = d g (act h z) + d h z)
    (a b : G) (hY : 0 < Fintype.card Y) :
    hammingDistance (wreathModel Y m)
        (wreathPerm Y m (d (a * b * a⁻¹ * b⁻¹)) (act (a * b * a⁻¹ * b⁻¹))) 1
      ≤ 2 - fixedDensity Y (act a) - fixedDensity Y (act b) := by
  classical
  have hYR : (0 : ℝ) < Fintype.card Y := by exact_mod_cast hY
  have hone : act 1 = 1 := by
    have h := hact 1 1
    rw [mul_one] at h
    have h2 : act 1 * 1 = act 1 * act 1 := by rw [mul_one]; exact h
    exact (mul_left_cancel h2).symm
  have hinv : ∀ g : G, act g⁻¹ = (act g)⁻¹ := by
    intro g
    have h := hact g g⁻¹
    rw [mul_inv_cancel, hone] at h
    exact (inv_eq_of_mul_eq_one_right h.symm).symm
  -- the common fixed points are trivially phased fixed points of the commutator
  have hkey : ∀ y : Y, act a y = y → act b y = y →
      act (a * b * a⁻¹ * b⁻¹) y = y ∧ d (a * b * a⁻¹ * b⁻¹) y = 0 := by
    intro y hay hby
    have hai : act a⁻¹ y = y := by
      rw [hinv]; exact (fixed_inv_iff Y (act a) y).mpr hay
    have hbi : act b⁻¹ y = y := by
      rw [hinv]; exact (fixed_inv_iff Y (act b) y).mpr hby
    constructor
    · rw [hact, hact, hact]
      show act a (act b (act a⁻¹ (act b⁻¹ y))) = y
      rw [hbi, hai, hby, hay]
    · exact phase_commutator_local act d hd y (by rw [hone]; rfl) a b hby hai hbi
  -- so the untwisted permutation fixes them in every fibre
  rw [hammingDistance_wreathPerm_one]
  have hsub : (univ.filter fun y : Y ↦ act a y = y ∧ act b y = y)
      ⊆ univ.filter fun y : Y ↦ act (a * b * a⁻¹ * b⁻¹) y = y
        ∧ d (a * b * a⁻¹ * b⁻¹) y = 0 := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact hkey y hy.1 hy.2
  have hcount := card_inter_fixed_ge Y (act a) (act b)
  have hmono : ((univ.filter fun y : Y ↦ act a y = y ∧ act b y = y).card : ℝ)
      ≤ ((univ.filter fun y : Y ↦ act (a * b * a⁻¹ * b⁻¹) y = y
          ∧ d (a * b * a⁻¹ * b⁻¹) y = 0).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hcompl : (univ.filter fun y : Y ↦
      ¬ (act (a * b * a⁻¹ * b⁻¹) y = y ∧ d (a * b * a⁻¹ * b⁻¹) y = 0)).card
      = Fintype.card Y - (univ.filter fun y : Y ↦
          act (a * b * a⁻¹ * b⁻¹) y = y ∧ d (a * b * a⁻¹ * b⁻¹) y = 0).card := by
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset Y))
      (fun y : Y ↦ act (a * b * a⁻¹ * b⁻¹) y = y ∧ d (a * b * a⁻¹ * b⁻¹) y = 0)
    rw [Finset.card_univ] at this
    omega
  have hle : (univ.filter fun y : Y ↦ act (a * b * a⁻¹ * b⁻¹) y = y
      ∧ d (a * b * a⁻¹ * b⁻¹) y = 0).card ≤ Fintype.card Y := by
    calc _ ≤ (univ : Finset Y).card := Finset.card_filter_le _ _
      _ = Fintype.card Y := Finset.card_univ
  rw [hcompl, Nat.cast_sub hle, fixedDensity, fixedDensity, div_le_iff₀ hYR]
  have hexpand : (2 - ((univ.filter fun y : Y ↦ act a y = y).card : ℝ)
        / Fintype.card Y
      - ((univ.filter fun y : Y ↦ act b y = y).card : ℝ) / Fintype.card Y)
      * Fintype.card Y
      = 2 * Fintype.card Y - ((univ.filter fun y : Y ↦ act a y = y).card : ℝ)
        - ((univ.filter fun y : Y ↦ act b y = y).card : ℝ) := by
    field_simp
  rw [hexpand]
  linarith [hcount, hmono, hYR]

end NonsoficGroupsExist
