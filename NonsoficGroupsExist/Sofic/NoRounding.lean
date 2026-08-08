import NonsoficGroupsExist.Sofic.DivisibleInvisible
import NonsoficGroupsExist.Sofic.ScalarCocycle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# No pointwise rounding turns metric phases into combinatorial ones

The characterization of `MonomialModel` says that soficity is *combinatorial*
monomial approximability: the phases must agree as elements of `ℤ/m` outside a
small set.  Hyperlinearity supplies only *metric* agreement.  So the obvious
strategy for closing the gap is to round: replace each phase, which lives in the
circle, by a nearby `m`-th root of unity, and hope that multiplicativity
survives.

It cannot, and the reason is a fork with two horns, both of which are proved
here.

* If the rounding is **multiplicative**, it is trivial.  The circle is divisible
  and `ℤ/m` is finite, so every homomorphism between them is zero
  (`circle_map_eq_zero`).  A multiplicative rounding therefore sends *every*
  phase to `1`, and two monomial data differing only in their phases become the
  same permutation (`additiveRounding_collapses`): the rounding separates
  nothing at all, so no model built through it can be sofic.

* If the rounding is **nearest-point**, it is not multiplicative, at every `m`
  and however fine (`roundMod_not_additive`).  The witness is uniform in `m`:
  `3/(10m)` rounds down to `0` and its double rounds up to `1`.

The two horns exhaust the pointwise rules: a pointwise rule either respects the
group law or does not.  So the passage from a metric phase system to a
combinatorial one, if it exists at all, cannot be pointwise -- it has to use the
group being modelled and the model itself.  This is the same shape as the
failure of tensor amplification in `HyperlinearAmplification`: not a difficulty
in carrying out a strategy, but a proof that the strategy does not exist.

Nothing here bears on whether the passage is possible by other means, and
nothing here decides Question 3.4.
-/

namespace NonsoficGroupsExist

open Finset

/-! ## The circle is divisible -/

/-- The reals are divisible. -/
theorem real_divisible (n : ℕ) (hn : 0 < n) (x : ℝ) : ∃ y : ℝ, n • y = x := by
  refine ⟨x / n, ?_⟩
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [nsmul_eq_mul]
  field_simp

/-- The circle group `ℝ/ℤ`, the group the phases of a monomial model live in. -/
abbrev CircleGroup := ℝ ⧸ AddSubgroup.zmultiples (1 : ℝ)

/-- **The circle is divisible.** -/
theorem circle_divisible (n : ℕ) (hn : 0 < n) (a : CircleGroup) :
    ∃ b : CircleGroup, n • b = a :=
  divisible_quotient _ real_divisible n hn a

/-- **Every homomorphism from the circle to a finite group is zero.**  This is
the first horn: a *multiplicative* rounding of phases is necessarily trivial. -/
theorem circle_map_eq_zero {B : Type*} [AddGroup B] [Finite B]
    (f : CircleGroup →+ B) (a : CircleGroup) : f a = 0 :=
  map_eq_zero_of_divisible circle_divisible f a

/-! ## The first horn: a multiplicative rounding erases every phase -/

/-- **A multiplicative rounding collapses all phase data.**  Whatever phase
systems `D` and `E` a model carries, an additive rounding sends both to the
same untwisted permutation: the rounding cannot tell them apart. -/
theorem additiveRounding_collapses (Y : FiniteModel) (m : ℕ) [NeZero m]
    (f : CircleGroup →+ ZMod m) (D E : Y → CircleGroup) (σ : Equiv.Perm Y) :
    wreathPerm Y m (fun y ↦ f (D y)) σ = wreathPerm Y m (fun y ↦ f (E y)) σ := by
  have h : (fun y ↦ f (D y)) = fun y ↦ f (E y) := by
    funext y
    rw [circle_map_eq_zero f (D y), circle_map_eq_zero f (E y)]
  rw [h]

/-- The separation a multiplicative rounding provides is exactly zero, for every
pair of phase systems and every permutation part. -/
theorem additiveRounding_no_separation (Y : FiniteModel) (m : ℕ) [NeZero m]
    (f : CircleGroup →+ ZMod m) (D E : Y → CircleGroup) (σ : Equiv.Perm Y) :
    hammingDistance (wreathModel Y m)
        (wreathPerm Y m (fun y ↦ f (D y)) σ)
        (wreathPerm Y m (fun y ↦ f (E y)) σ) = 0 := by
  rw [additiveRounding_collapses Y m f D E σ, hammingDistance_self]

/-! ## The second horn: nearest-point rounding is not multiplicative -/

/-- Nearest-point rounding of a phase to an `m`-th root of unity, written
additively: `x` in the circle goes to the nearest multiple of `1/m`. -/
noncomputable def roundMod (m : ℕ) (x : ℝ) : ZMod m := (round ((m : ℝ) * x) : ℤ)

/-- The rounding is well defined on the circle: shifting by an integer shifts
the rounded value by a multiple of `m`. -/
theorem roundMod_add_int (m : ℕ) (x : ℝ) (k : ℤ) :
    roundMod m (x + k) = roundMod m x := by
  have hexp : (m : ℝ) * (x + k) = (m : ℝ) * x + ((m * k : ℤ) : ℝ) := by
    push_cast; ring
  simp only [roundMod, hexp, round_add_intCast]
  push_cast
  simp

/-- **Nearest-point rounding is never additive.**  The witness does not depend
on `m`: `3/(10m)` rounds down to `0`, and its double rounds up to `1`.  So the
failure is uniform in the fineness of the rounding, and no choice of `m` --
however large -- makes a pointwise nearest-point rule multiplicative. -/
theorem roundMod_not_additive (m : ℕ) (hm : 2 ≤ m) :
    ∃ x y : ℝ, roundMod m (x + y) ≠ roundMod m x + roundMod m y := by
  have hm0 : (m : ℝ) ≠ 0 := by
    have : 0 < m := lt_of_lt_of_le (by norm_num) hm
    exact Nat.cast_ne_zero.mpr this.ne'
  refine ⟨3 / (10 * m), 3 / (10 * m), ?_⟩
  have hsmall : (m : ℝ) * (3 / (10 * m)) = 3 / 10 := by field_simp
  have hdouble : (m : ℝ) * (3 / (10 * m) + 3 / (10 * m)) = 6 / 10 := by
    field_simp
    ring
  have h1 : roundMod m (3 / (10 * m)) = 0 := by
    simp only [roundMod, hsmall]
    norm_num [round_eq]
  have h2 : roundMod m (3 / (10 * m) + 3 / (10 * m)) = 1 := by
    simp only [roundMod, hdouble]
    norm_num [round_eq]
  rw [h1, h2, add_zero]
  have : ((1 : ZMod m)) ≠ 0 := by
    haveI : Fact (1 < m) := ⟨lt_of_lt_of_le (by norm_num) hm⟩
    exact one_ne_zero
  exact this

/-- **The fork.**  For every `m ≥ 2` there is no pointwise rule that is both
multiplicative and nontrivial: multiplicativity forces the rounding to erase
every phase, and the nearest-point rule -- the only canonical nontrivial
candidate -- is not multiplicative.  Both statements are recorded together
because it is their conjunction that closes the strategy. -/
theorem no_pointwise_rounding (m : ℕ) [NeZero m] (hm : 2 ≤ m) :
    (∀ (f : CircleGroup →+ ZMod m) (a : CircleGroup), f a = 0) ∧
      (∃ x y : ℝ, roundMod m (x + y) ≠ roundMod m x + roundMod m y) :=
  ⟨fun f a ↦ circle_map_eq_zero f a, roundMod_not_additive m hm⟩

end NonsoficGroupsExist
