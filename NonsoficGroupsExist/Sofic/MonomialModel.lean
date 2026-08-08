import NonsoficGroupsExist.Sofic.HyperlinearScalar

/-!
# Monomial models: where a hyperlinear model keeps its permutation

A hyperlinear model that is not visibly sofic is usually not shapeless.  Thom's
microstates for the group `K = K_0(Z[1/p])/Z` -- finitely presented, Kazhdan,
not residually finite, hyperlinear, soficity open -- lie in the **monomial
group** `T_Y ⋊ Sym Y ⊆ U(Y)`: a permutation matrix carrying a diagonal of
phases.  They arise that way for a reason.  Every finite-dimensional unitary
representation of `K` kills its divisible centre, so genuine representations
cannot see the central data at all and the approximations are forced to be
projective; a projective representation of a finite group is exactly a monomial
matrix in the regular basis.

This file measures the gap between such a model and a sofic one.  Two
inequalities do it, and they pull in opposite directions.

* `hammingDistance_le_hsDistSq_monomial`: the underlying permutations inherit
  the multiplicative defect, `2 · d_Hamm(σ, τ) ≤ ‖A - B‖²`.  So the permutation
  part of a monomial model is an approximately multiplicative map into `Sym Y`
  with no loss.
* `normSq_normTrace_monomial_le`: the trace is bounded by the underlying
  permutation's fixed-point fraction,
  `|τ(A)|² ≤ (1 - d_Hamm(σ, 1))²`.  So a small trace is *permitted* by many
  fixed points but not *caused* by them.

Together: **a monomial model is a sofic model exactly when its underlying
permutations are already almost fixed-point free.**  What a monomial model may
do instead is let the phases cancel over the fixed points, and
`monomial_normTrace_zero_of_identity` exhibits that in its purest form -- the
identity permutation, phases `1` and `-1`, trace `0`.  Nothing is separated;
the trace vanishes by cancellation.

That is the whole of the gap for `K`, and it is the same gap as in
`Sofic.HyperlinearAmplification`: a trace that vanishes by cancellation versus
one that vanishes by disagreement.  Taking all phases equal to `1` recovers the
permutation case, where `normTrace_permMatrix` says the trace *is* the
fixed-point fraction and no cancellation is available.
-/

namespace NonsoficGroupsExist

open Matrix

/-! ## Monomial matrices -/

/-- A monomial matrix: the permutation `σ` with the phase `d i` on row `i`. -/
def monomialMatrix (Y : FiniteModel) (d : Y → ℂ) (σ : Equiv.Perm Y) :
    Matrix Y Y ℂ :=
  fun i j ↦ if σ i = j then d i else 0

@[simp] theorem monomialMatrix_apply (Y : FiniteModel) (d : Y → ℂ)
    (σ : Equiv.Perm Y) (i j : Y) :
    monomialMatrix Y d σ i j = if σ i = j then d i else 0 := rfl

/-- With all phases `1` a monomial matrix is a permutation matrix. -/
theorem monomialMatrix_one (Y : FiniteModel) (σ : Equiv.Perm Y) :
    monomialMatrix Y (fun _ ↦ 1) σ = σ.permMatrix ℂ := by
  ext i j
  rw [monomialMatrix_apply, permMatrixC_entry]

/-- A monomial matrix with unimodular phases is unitary. -/
theorem monomialMatrix_mem_unitaryGroup (Y : FiniteModel) {d : Y → ℂ}
    (hd : ∀ i, Complex.normSq (d i) = 1) (σ : Equiv.Perm Y) :
    monomialMatrix Y d σ ∈ Matrix.unitaryGroup Y ℂ := by
  classical
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  ext i k
  rw [Matrix.mul_apply]
  have hterm : ∀ j : Y, monomialMatrix Y d σ i j
      * (monomialMatrix Y d σ)ᴴ j k
      = if σ i = j then (if σ k = j then d i * (starRingEnd ℂ) (d k) else 0)
        else 0 := by
    intro j
    rw [Matrix.conjTranspose_apply, monomialMatrix_apply, monomialMatrix_apply]
    by_cases h1 : σ i = j
    · by_cases h2 : σ k = j <;> simp [h1, h2]
    · simp [h1]
  rw [Finset.sum_congr rfl fun j _ ↦ hterm j, Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  by_cases hik : i = k
  · subst hik
    have h : d i * (starRingEnd ℂ) (d i) = 1 := by
      rw [Complex.mul_conj, hd i]; norm_num
    rw [if_pos rfl, h, Matrix.one_apply_eq]
  · have hne : σ k ≠ σ i := fun h ↦ hik (σ.injective h).symm
    rw [if_neg hne, Matrix.one_apply_ne hik]

/-! ## The permutation part inherits the multiplicative defect -/

/-- **The underlying permutations are as multiplicative as the matrices.**
Two monomial matrices whose permutations disagree at `i` differ in two entries
of row `i`, each of modulus one. -/
theorem hammingDistance_le_hsDistSq_monomial (Y : FiniteModel) {d e : Y → ℂ}
    (hd : ∀ i, Complex.normSq (d i) = 1) (he : ∀ i, Complex.normSq (e i) = 1)
    (σ τ : Equiv.Perm Y) :
    2 * hammingDistance Y σ τ
      ≤ hsDistSq Y (monomialMatrix Y d σ) (monomialMatrix Y e τ) := by
  classical
  have hrow : ∀ i : Y, (if σ i = τ i then (0 : ℝ) else 2)
      ≤ ∑ j : Y, Complex.normSq
        (monomialMatrix Y d σ i j - monomialMatrix Y e τ i j) := by
    intro i
    by_cases h : σ i = τ i
    · rw [if_pos h]
      exact Finset.sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _
    · rw [if_neg h]
      have hsplit : (2 : ℝ)
          ≤ Complex.normSq
              (monomialMatrix Y d σ i (σ i) - monomialMatrix Y e τ i (σ i))
            + Complex.normSq
              (monomialMatrix Y d σ i (τ i) - monomialMatrix Y e τ i (τ i)) := by
        rw [monomialMatrix_apply, monomialMatrix_apply, monomialMatrix_apply,
          monomialMatrix_apply, if_pos rfl, if_neg (Ne.symm h), if_neg h,
          if_pos rfl]
        rw [sub_zero, zero_sub, Complex.normSq_neg, hd i, he i]
        norm_num
      have hsub : ({σ i, τ i} : Finset Y) ⊆ Finset.univ := Finset.subset_univ _
      calc (2 : ℝ)
          ≤ ∑ j ∈ ({σ i, τ i} : Finset Y), Complex.normSq
              (monomialMatrix Y d σ i j - monomialMatrix Y e τ i j) := by
            rw [Finset.sum_pair h]
            exact hsplit
        _ ≤ ∑ j : Y, Complex.normSq
              (monomialMatrix Y d σ i j - monomialMatrix Y e τ i j) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub
              fun _ _ _ ↦ Complex.normSq_nonneg _
  have hsum : (∑ i : Y, (if σ i = τ i then (0 : ℝ) else 2))
      ≤ ∑ i : Y, ∑ j : Y, Complex.normSq
        (monomialMatrix Y d σ i j - monomialMatrix Y e τ i j) :=
    Finset.sum_le_sum fun i _ ↦ hrow i
  have hleft : (∑ i : Y, (if σ i = τ i then (0 : ℝ) else 2))
      = 2 * ((hammingDisagreement σ τ).card : ℝ) := by
    have hrw : ∀ i : Y, (if σ i = τ i then (0 : ℝ) else 2)
        = 2 * (if i ∈ hammingDisagreement σ τ then (1 : ℝ) else 0) := by
      intro i
      by_cases h : σ i = τ i <;> simp [mem_hammingDisagreement, h]
    rw [Finset.sum_congr rfl fun i _ ↦ hrw i, ← Finset.mul_sum,
      Finset.sum_ite_mem]
    simp
  rw [hleft] at hsum
  rw [hsDistSq, hammingDistance, ← mul_div_assoc]
  rcases Nat.eq_zero_or_pos (Fintype.card Y) with h0 | hpos
  · simp [h0]
  · have hn : (0 : ℝ) < (Fintype.card Y : ℝ) := by exact_mod_cast hpos
    gcongr

/-! ## The trace is bounded by the fixed-point fraction -/

/-- **A monomial trace cannot exceed the underlying permutation's fixed-point
fraction.**  So a small trace is permitted by many fixed points, never caused
by them: the deficit is exactly phase cancellation. -/
theorem normSq_normTrace_monomial_le (Y : FiniteModel) {d : Y → ℂ}
    (hd : ∀ i, Complex.normSq (d i) = 1) (σ : Equiv.Perm Y) :
    Complex.normSq (normTrace Y (monomialMatrix Y d σ))
      ≤ (1 - hammingDistance Y σ 1) ^ 2 := by
  classical
  rcases Nat.eq_zero_or_pos (Fintype.card Y) with h0 | hpos
  · haveI : IsEmpty Y := Fintype.card_eq_zero_iff.mp h0
    simp [normTrace, hammingDistance]
  have hn : (0 : ℝ) < (Fintype.card Y : ℝ) := by exact_mod_cast hpos
  set F : Finset Y := Finset.univ.filter fun i : Y ↦ σ i = i with hFdef
  have htr : Matrix.trace (monomialMatrix Y d σ) = ∑ i ∈ F, d i := by
    show (∑ i : Y, monomialMatrix Y d σ i i) = _
    rw [hFdef, Finset.sum_filter]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [monomialMatrix_apply]
  have hcs : Complex.normSq (∑ i ∈ F, d i) ≤ ((F.card : ℝ)) ^ 2 := by
    have h := normSq_sum_le_card_mul_sum_normSq F d
    have hone : (∑ i ∈ F, Complex.normSq (d i)) = (F.card : ℝ) := by
      rw [Finset.sum_congr rfl fun i _ ↦ hd i]
      simp
    rw [hone] at h
    nlinarith [h]
  have hfix : (F.card : ℝ) / (Fintype.card Y : ℝ) = 1 - hammingDistance Y σ 1 := by
    have hdis : hammingDisagreement σ (1 : Equiv.Perm Y)
        = Finset.univ.filter fun i : Y ↦ ¬ (σ i = i) := by
      ext y; simp
    have hsplit : F.card + (hammingDisagreement σ (1 : Equiv.Perm Y)).card
        = Fintype.card Y := by
      rw [hFdef, hdis, Finset.card_filter_add_card_filter_not, Finset.card_univ]
    have hF : (F.card : ℝ) = (Fintype.card Y : ℝ)
        - ((hammingDisagreement σ (1 : Equiv.Perm Y)).card : ℝ) := by
      have := congrArg (fun n : ℕ ↦ (n : ℝ)) hsplit
      push_cast at this
      linarith
    rw [hammingDistance, hF]
    field_simp
  have hnt : Complex.normSq (normTrace Y (monomialMatrix Y d σ))
      = Complex.normSq (∑ i ∈ F, d i) / (Fintype.card Y : ℝ) ^ 2 := by
    show Complex.normSq
      (Matrix.trace (monomialMatrix Y d σ) / ((Fintype.card Y : ℕ) : ℂ)) = _
    rw [Complex.normSq_div, htr]
    have h2 : Complex.normSq (((Fintype.card Y : ℕ) : ℂ))
        = (Fintype.card Y : ℝ) ^ 2 := by
      simp [Complex.normSq_apply, sq]
    rw [h2]
  rw [hnt, ← hfix, div_pow]
  gcongr

/-! ## Cancellation is real -/

/-- **The purest cancellation.**  On a two-point model the identity permutation
carries the phases `1` and `-1`; the trace is `0` although nothing at all is
moved.  This is the configuration a permutation model cannot imitate, by
`normTrace_permMatrix`, and it is the mechanism of Thom's microstates. -/
theorem monomial_normTrace_zero_of_identity :
    ∃ (Y : FiniteModel) (d : Y → ℂ),
      (∀ i, Complex.normSq (d i) = 1) ∧
      hammingDistance Y (1 : Equiv.Perm Y) 1 = 0 ∧
      normTrace Y (monomialMatrix Y d 1) = 0 := by
  classical
  refine ⟨(⟨Bool, inferInstance, inferInstance⟩ : FiniteModel),
    fun b : Bool ↦ if b = true then (1 : ℂ) else -1, ?_, ?_, ?_⟩
  · intro i
    by_cases h : i = true <;> simp [h]
  · simp
  · have htr : Matrix.trace
        (monomialMatrix (⟨Bool, inferInstance, inferInstance⟩ : FiniteModel)
          (fun b : Bool ↦ if b = true then (1 : ℂ) else -1) 1) = 0 := by
      show (∑ i : Bool, (if (1 : Equiv.Perm Bool) i = i then
        (if i = true then (1 : ℂ) else -1) else 0)) = 0
      rw [Fintype.sum_bool]
      norm_num
    rw [normTrace, htr, zero_div]

/-! ## Untwisting: a discrete torus can always be turned into more points -/

/-- The model on `Y × ℤ/m`, on which a monomial matrix with `m`-th root of
unity phases acts by an honest permutation. -/
abbrev wreathModel (Y : FiniteModel) (m : ℕ) [NeZero m] : FiniteModel :=
  ⟨Y × ZMod m, inferInstance, inferInstance⟩

/-- **The untwisting permutation.**  Phases valued in `ℤ/m` are absorbed as a
shift of a second coordinate: `(y, j) ↦ (σ y, j + d y)`.  This is the standard
embedding of the monomial group `(ℤ/m)^Y ⋊ Sym Y` into `Sym (Y × ℤ/m)`. -/
def wreathPerm (Y : FiniteModel) (m : ℕ) [NeZero m] (d : Y → ZMod m)
    (σ : Equiv.Perm Y) : Equiv.Perm (Y × ZMod m) where
  toFun p := (σ p.1, p.2 + d p.1)
  invFun p := (σ⁻¹ p.1, p.2 - d (σ⁻¹ p.1))
  left_inv p := by simp
  right_inv p := by simp

@[simp] theorem wreathPerm_apply (Y : FiniteModel) (m : ℕ) [NeZero m]
    (d : Y → ZMod m) (σ : Equiv.Perm Y) (p : Y × ZMod m) :
    wreathPerm Y m d σ p = (σ p.1, p.2 + d p.1) := rfl

theorem wreathPerm_one (Y : FiniteModel) (m : ℕ) [NeZero m] :
    wreathPerm Y m (fun _ ↦ 0) 1 = 1 := by
  ext p <;> simp

/-- **What untwisting costs, exactly.**  The Hamming distance between two
untwisted permutations is the density of the set where the monomial data
differ -- in the *permutation part or the phase*.  Fine phase differences that
are invisible to the Hilbert--Schmidt metric are fully visible here; that is
the whole price. -/
theorem hammingDistance_wreathPerm (Y : FiniteModel) (m : ℕ) [NeZero m]
    (d e : Y → ZMod m) (σ τ : Equiv.Perm Y) :
    hammingDistance (wreathModel Y m) (wreathPerm Y m d σ) (wreathPerm Y m e τ)
      = ((Finset.univ.filter fun y : Y ↦ ¬ (σ y = τ y ∧ d y = e y)).card : ℝ)
        / Fintype.card Y := by
  classical
  set D : Finset Y := Finset.univ.filter fun y : Y ↦ ¬ (σ y = τ y ∧ d y = e y)
    with hDdef
  have hdis : hammingDisagreement (wreathPerm Y m d σ) (wreathPerm Y m e τ)
      = D ×ˢ (Finset.univ : Finset (ZMod m)) := by
    ext p
    rw [mem_hammingDisagreement, Finset.mem_product, hDdef, Finset.mem_filter]
    constructor
    · intro h
      refine ⟨⟨Finset.mem_univ _, ?_⟩, Finset.mem_univ _⟩
      intro hcon
      apply h
      rw [wreathPerm_apply, wreathPerm_apply, hcon.1, hcon.2]
    · rintro ⟨⟨-, h⟩, -⟩ hcon
      apply h
      rw [wreathPerm_apply, wreathPerm_apply, Prod.mk.injEq] at hcon
      exact ⟨hcon.1, add_left_cancel hcon.2⟩
  have hcard : (hammingDisagreement (wreathPerm Y m d σ)
      (wreathPerm Y m e τ)).card = D.card * m := by
    rw [hdis, Finset.card_product, Finset.card_univ, ZMod.card]
  have hmodel : Fintype.card (wreathModel Y m) = Fintype.card Y * m := by
    show Fintype.card (Y × ZMod m) = _
    rw [Fintype.card_prod, ZMod.card]
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  rw [hammingDistance, hcard, hmodel]
  push_cast
  rw [mul_div_mul_right _ _ hm]

/-- **What untwisting buys, exactly.**  The untwisted permutation moves
everything except the points where `σ` fixes and the phase is trivial.  So the
separation a sofic model needs is exactly scarcity of *trivially phased* fixed
points, and phase cancellation -- which is what makes a monomial trace small
without moving anything -- buys nothing here. -/
theorem hammingDistance_wreathPerm_one (Y : FiniteModel) (m : ℕ) [NeZero m]
    (d : Y → ZMod m) (σ : Equiv.Perm Y) :
    hammingDistance (wreathModel Y m) (wreathPerm Y m d σ) 1
      = ((Finset.univ.filter fun y : Y ↦ ¬ (σ y = y ∧ d y = 0)).card : ℝ)
        / Fintype.card Y := by
  classical
  rw [← wreathPerm_one Y m, hammingDistance_wreathPerm]
  rfl

/-! ## Untwisting as a criterion for soficity -/

/-- Untwisting is a homomorphism: the monomial group law is
`(d, σ) · (e, τ) = (y ↦ e y + d (τ y), σ τ)`. -/
theorem wreathPerm_mul (Y : FiniteModel) (m : ℕ) [NeZero m]
    (d e : Y → ZMod m) (σ τ : Equiv.Perm Y) :
    wreathPerm Y m (fun y ↦ e y + d (τ y)) (σ * τ)
      = wreathPerm Y m d σ * wreathPerm Y m e τ := by
  ext p
  · simp [Equiv.Perm.mul_apply]
  · show p.2 + (e p.1 + d (τ p.1)) = p.2 + e p.1 + d (τ p.1)
    rw [add_assoc]

/-- A monomial model whose multiplicative defect is measured *combinatorially*
-- permutation and phase must agree outside a set of density `ε` -- and whose
separation is scarcity of pairs agreeing in both.  These are exactly the two
quantities `hammingDistance_wreathPerm` computes. -/
structure MonomialSoficData (G : Type*) [Group G] (F : Finset G) (ε : ℝ)
    (m : ℕ) where
  carrier : FiniteModel
  nonempty : 0 < Fintype.card carrier
  perm : G → Equiv.Perm carrier
  phase : G → carrier → ZMod m
  multiplicative : ∀ g ∈ F, ∀ h ∈ F,
    ((Finset.univ.filter fun y : carrier ↦
        ¬ (perm (g * h) y = (perm g * perm h) y ∧
           phase (g * h) y = phase h y + phase g (perm h y))).card : ℝ)
      / Fintype.card carrier ≤ ε
  separated : ∀ g ∈ F, ∀ h ∈ F, g ≠ h →
    ((Finset.univ.filter fun y : carrier ↦
        perm g y = perm h y ∧ phase g y = phase h y).card : ℝ)
      / Fintype.card carrier ≤ ε

/-- A closed inhabitant, so `MonomialSoficData` is not a certificate nothing
satisfies: the one-point model of the trivial group with a single phase. -/
noncomputable def trivialMonomialSoficData (F : Finset PUnit) :
    MonomialSoficData PUnit F 0 1 where
  carrier := ⟨PUnit, inferInstance, inferInstance⟩
  nonempty := by simp
  perm := fun _ ↦ 1
  phase := fun _ _ ↦ 0
  multiplicative := by
    intro g _ h _
    simp
  separated := by
    intro g _ h _ hne
    exact absurd (Subsingleton.elim g h) hne

/-- **The untwisting criterion.**  A monomial model whose data are
combinatorially multiplicative and combinatorially separated *is* a permutation
model, on `m` times as many points.  This is the positive half of the
untwisting story: the torus can always be removed, and this is exactly what a
model must satisfy for the removal to preserve both laws. -/
theorem soficModel_of_monomial {G : Type*} [Group G] {F : Finset G} {ε : ℝ}
    {m : ℕ} [NeZero m] (D : MonomialSoficData G F ε m) :
    Nonempty (SoficModel G F ε) := by
  classical
  refine ⟨{
    carrier := wreathModel D.carrier m
    nonempty := ?_
    map := fun g ↦ wreathPerm D.carrier m (D.phase g) (D.perm g)
    multiplicative := ?_
    separated := ?_ }⟩
  · show 0 < Fintype.card (D.carrier × ZMod m)
    rw [Fintype.card_prod, ZMod.card]
    exact Nat.mul_pos D.nonempty (Nat.pos_of_ne_zero (NeZero.ne m))
  · intro g hg h hh
    have hmul : wreathPerm D.carrier m (D.phase g) (D.perm g)
        * wreathPerm D.carrier m (D.phase h) (D.perm h)
        = wreathPerm D.carrier m
            (fun y ↦ D.phase h y + D.phase g (D.perm h y))
            (D.perm g * D.perm h) := (wreathPerm_mul _ _ _ _ _ _).symm
    rw [hmul, hammingDistance_wreathPerm]
    exact D.multiplicative g hg h hh
  · intro g hg h hh hne
    rw [hammingDistance_wreathPerm]
    have hsplit : (Finset.univ.filter fun y : D.carrier ↦
          ¬ (D.perm g y = D.perm h y ∧ D.phase g y = D.phase h y)).card
        + (Finset.univ.filter fun y : D.carrier ↦
          D.perm g y = D.perm h y ∧ D.phase g y = D.phase h y).card
        = Fintype.card D.carrier := by
      rw [add_comm, Finset.card_filter_add_card_filter_not, Finset.card_univ]
    have hc : (0 : ℝ) < (Fintype.card D.carrier : ℝ) := by
      exact_mod_cast D.nonempty
    have hsep := D.separated g hg h hh hne
    rw [div_le_iff₀ hc] at hsep
    rw [le_div_iff₀ hc]
    have hcast := congrArg (fun n : ℕ ↦ (n : ℝ)) hsplit
    push_cast at hcast
    linarith

end NonsoficGroupsExist
