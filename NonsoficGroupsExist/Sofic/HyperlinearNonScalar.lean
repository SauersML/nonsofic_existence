import NonsoficGroupsExist.Sofic.HyperlinearAmplification

/-!
# A class between sofic and hyperlinear

`Sofic.HyperlinearAmplification` shows that the tensor-power argument which
makes the sofic separation constant a convention does not transport to unitary
models: scalars are raised to the `k`-th power, so `1` and `i\cdot1` are
maximally separated with equal fourth tensor powers.  What survives is the
conjugate double `A \otimes \bar A`, whose normalized trace is `|\tau(A)|^2`,
and it amplifies exactly when the trace is bounded off the unit circle.

That bound is a property a model may or may not have, so it names a class.
Call a unitary model **non-scalar** when

  `|\tau(u_g u_h^*)|^2 \le 1 - \delta`   for distinct `g, h` in the test set,

with `\delta` depending on the test set alone.  This is strictly more than the
separation `2 - \eps` of `HyperlinearModel`, which controls only the *real
part* of the trace and so tolerates `u_g u_h^* \approx \pm i`.  The two main
theorems here place the resulting class:

* `isHyperlinearNonScalar_of_isSofic` -- soficity gives non-scalar models,
  because the trace of a permutation matrix is the proportion of its fixed
  points, a *real* number in `[0,1]`, and separation makes it small.
* `isHyperlinear_of_isHyperlinearNonScalar` -- non-scalar models amplify, by
  `hsDistSq_conjDoubleTensorPow`, to models of every accuracy and separation
  `2 - \eps`.

So

  sofic  ==>  non-scalar hyperlinear  ==>  hyperlinear,

and Pestov's Question 3.4 splits along the middle class: does hyperlinearity
imply the non-scalar form, and does the non-scalar form imply soficity?  The
phase collapse is exactly the obstruction to answering the first by the
argument that answers the sofic analogue.

The endpoint reading is `not_isSofic_of_not_isHyperlinearNonScalar`, which is a
*weaker* hypothesis than refuting hyperlinearity outright and therefore an
easier target: refuting the middle class already refutes soficity.
-/

namespace NonsoficGroupsExist

open Matrix

variable {G : Type*} [Group G]

/-! ## The trace of a permutation matrix is its proportion of fixed points -/

/-- Conjugate transposition inverts a permutation matrix. -/
theorem permMatrixC_conjTranspose (Y : FiniteModel) (σ : Equiv.Perm Y) :
    (σ.permMatrix ℂ)ᴴ = (σ⁻¹).permMatrix ℂ := by
  ext i j
  simp [Equiv.Perm.permMatrix, Matrix.conjTranspose_apply, eq_comm,
    Equiv.eq_symm_apply]

/-- **The normalized trace of a permutation matrix is real**, and equals one
minus the normalized Hamming length.  This is what permutation models have and
general unitary models do not: the trace cannot hide a phase. -/
theorem normTrace_permMatrix (Y : FiniteModel) (σ : Equiv.Perm Y)
    (hY : 0 < Fintype.card Y) :
    normTrace Y (σ.permMatrix ℂ)
      = ((1 - hammingDistance Y σ 1 : ℝ) : ℂ) := by
  classical
  have hcR : (Fintype.card Y : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hY.ne'
  have hfix : Matrix.trace (σ.permMatrix ℂ)
      = (((Finset.univ.filter fun y : Y ↦ σ y = y).card : ℕ) : ℂ) := by
    show (∑ x : Y, (σ.permMatrix ℂ) x x) = _
    rw [Finset.sum_congr rfl fun x _ ↦ permMatrixC_entry Y σ x x,
      Finset.sum_boole]
  have hdis : hammingDisagreement σ (1 : Equiv.Perm Y)
      = Finset.univ.filter fun y : Y ↦ ¬ (σ y = y) := by
    ext y; simp
  have hsplit : (Finset.univ.filter fun y : Y ↦ σ y = y).card
      + (hammingDisagreement σ (1 : Equiv.Perm Y)).card = Fintype.card Y := by
    rw [hdis, Finset.card_filter_add_card_filter_not, Finset.card_univ]
  have hreal : (((Finset.univ.filter fun y : Y ↦ σ y = y).card : ℕ) : ℝ)
      / (Fintype.card Y : ℝ) = 1 - hammingDistance Y σ 1 := by
    have hF : (((Finset.univ.filter fun y : Y ↦ σ y = y).card : ℕ) : ℝ)
        = (Fintype.card Y : ℝ)
          - ((hammingDisagreement σ (1 : Equiv.Perm Y)).card : ℝ) := by
      have := congrArg (fun n : ℕ ↦ (n : ℝ)) hsplit
      push_cast at this
      linarith
    rw [hammingDistance, hF]
    field_simp
  show Matrix.trace (σ.permMatrix ℂ) / ((Fintype.card Y : ℕ) : ℂ) = _
  rw [hfix, ← hreal]
  push_cast
  ring

/-! ## Non-scalar models -/

/-- A unitary model whose pairwise traces are bounded off the unit circle.
The bound `1 - δ` is on `|τ(u_g u_h^*)|²`, not on its real part, and that is
the whole difference from `HyperlinearModel`. -/
structure NonScalarModel (G : Type*) [Group G] (F : Finset G) (ε δ : ℝ) where
  carrier : FiniteModel
  nonempty : 0 < Fintype.card carrier
  map : G → Matrix carrier carrier ℂ
  isUnitary : ∀ g, map g ∈ Matrix.unitaryGroup carrier ℂ
  multiplicative : ∀ g ∈ F, ∀ h ∈ F,
    hsDistSq carrier (map (g * h)) (map g * map h) ≤ ε
  nonScalar : ∀ g ∈ F, ∀ h ∈ F, g ≠ h →
    Complex.normSq (normTrace carrier (map g * (map h)ᴴ)) ≤ 1 - δ

/-- Non-scalar hyperlinearity: models of every accuracy, with a trace bound
depending on the test set alone. -/
def IsHyperlinearNonScalar (G : Type*) [Group G] : Prop :=
  ∀ F : Finset G, ∃ δ : ℝ, 0 < δ ∧
    ∀ ε : ℝ, 0 < ε → Nonempty (NonScalarModel G F ε δ)

/-- A closed non-scalar model, so the structure is not a certificate nothing
satisfies: the one-point model of the trivial group. -/
noncomputable def trivialNonScalarModel (F : Finset PUnit) (δ : ℝ) :
    NonScalarModel PUnit F 0 δ where
  carrier := ⟨PUnit, inferInstance, inferInstance⟩
  nonempty := by simp
  map := fun _ ↦ 1
  isUnitary := fun _ ↦ Submonoid.one_mem _
  multiplicative := by
    intro g _ h _
    simp [hsDistSq]
  nonScalar := by
    intro g _ h _ hne
    exact absurd (Subsingleton.elim g h) hne

/-! ## Soficity gives non-scalar models -/

/-- **Soficity implies the middle class.**  Transporting a sofic model by
`σ ↦ P_{σ⁻¹}` gives `τ(u_g u_h^*) = 1 - d(\varphi h, \varphi g)`, a real number
in `[0,1]` which separation forces to be small.  Permutation models cannot put
a phase in the trace, which is exactly the property the class isolates. -/
theorem isHyperlinearNonScalar_of_isSofic (h : IsSofic G) :
    IsHyperlinearNonScalar G := by
  classical
  intro F
  refine ⟨3 / 4, by norm_num, ?_⟩
  intro ε hε
  obtain ⟨M⟩ := h F (min (ε / 2) (1 / 2)) (by positivity)
  have hle1 : min (ε / 2) (1 / 2) ≤ 1 / 2 := min_le_right _ _
  have hle2 : min (ε / 2) (1 / 2) ≤ ε / 2 := min_le_left _ _
  refine ⟨{
    carrier := M.carrier
    nonempty := M.nonempty
    map := fun g ↦ (M.map g)⁻¹.permMatrix ℂ
    isUnitary := fun g ↦ permMatrix_mem_unitaryGroup M.carrier _
    multiplicative := ?_
    nonScalar := ?_ }⟩
  · intro g hg h' hh'
    have hhom : ((M.map g)⁻¹.permMatrix ℂ) * ((M.map h')⁻¹.permMatrix ℂ)
        = ((M.map g * M.map h')⁻¹).permMatrix ℂ := by
      rw [_root_.mul_inv_rev, Matrix.permMatrix_mul]
    rw [hhom, permMatrix_hsDistSq, hammingDistance_inv]
    have hmul := M.multiplicative g hg h' hh'
    linarith
  · intro g hg h' hh' hne
    have hprod : ((M.map g)⁻¹.permMatrix ℂ) * (((M.map h')⁻¹.permMatrix ℂ))ᴴ
        = (M.map h' * (M.map g)⁻¹).permMatrix ℂ := by
      rw [permMatrixC_conjTranspose, inv_inv, Matrix.permMatrix_mul]
    have hlen : hammingDistance M.carrier (M.map h' * (M.map g)⁻¹) 1
        = hammingDistance M.carrier (M.map h') (M.map g) := by
      have := hammingDistance_right_invariant M.carrier (M.map h') (M.map g)
        (M.map g)⁻¹
      rwa [mul_inv_cancel] at this
    have hsep := M.separated g hg h' hh' hne
    have hsep' : hammingDistance M.carrier (M.map h') (M.map g)
        ≥ 1 - min (ε / 2) (1 / 2) := by
      rw [hammingDistance_comm]; linarith
    have hle := hammingDistance_le_one M.carrier (M.map h') (M.map g)
    rw [hprod, normTrace_permMatrix _ _ M.nonempty, hlen]
    rw [Complex.normSq_ofReal]
    nlinarith

/-- Positive control: finite groups are non-scalar hyperlinear.  Without this
`IsHyperlinearNonScalar` would be a predicate nothing is known to satisfy, and
refuting it would be equally consistent with its being unsatisfiable. -/
theorem isHyperlinearNonScalar_of_finite (G : Type) [Group G] [Finite G] :
    IsHyperlinearNonScalar G :=
  isHyperlinearNonScalar_of_isSofic (isSofic_of_finite G)

/-! ## Non-scalar models amplify -/

/-- **The middle class is hyperlinear.**  Tensoring `k` conjugate doubles turns
a trace bound `1 - δ` into separation `2 - ε`, and costs the multiplicative
accuracy only a factor `2k`, which asking for `ε / 2(k+1)` at the outset
absorbs. -/
theorem isHyperlinear_of_isHyperlinearNonScalar
    (h : IsHyperlinearNonScalar G) : IsHyperlinear G := by
  classical
  intro F ε hε
  obtain ⟨δ, hδ, hmod⟩ := h F
  have hlt : (1 : ℝ) - δ < 1 := by linarith
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < ε / 2 by linarith) hlt
  set ε₀ : ℝ := min (ε / (2 * (k + 1))) 1 with hε₀def
  have hε₀pos : 0 < ε₀ := by
    refine lt_min (by positivity) (by norm_num)
  have hε₀le1 : ε₀ ≤ 1 := min_le_right _ _
  have hε₀small : (k : ℝ) * ε₀ * 2 ≤ ε := by
    have h1 : ε₀ ≤ ε / (2 * (k + 1)) := min_le_left _ _
    have h2 : (0 : ℝ) < 2 * (k + 1) := by positivity
    have h3 : (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
    calc (k : ℝ) * ε₀ * 2 ≤ (k : ℝ) * (ε / (2 * ((k : ℝ) + 1))) * 2 := by
          have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
          nlinarith
      _ = ε * (k : ℝ) / ((k : ℝ) + 1) := by field_simp
      _ ≤ ε := by
          rw [div_le_iff₀ (by positivity)]
          nlinarith
  obtain ⟨M⟩ := hmod ε₀ hε₀pos
  refine ⟨{
    carrier := tensorModel (doubleModel M.carrier) k
    nonempty := ?_
    map := fun g ↦ tensorPow (conjDouble (M.map g)) k
    isUnitary := fun g ↦
      tensorPow_mem_unitaryGroup (conjDouble_mem_unitaryGroup (M.isUnitary g)) k
    multiplicative := ?_
    separated := ?_ }⟩
  · rw [card_tensorModel, card_doubleModel]
    exact pow_pos (Nat.mul_pos M.nonempty M.nonempty) k
  · intro g hg h' hh'
    have hB : M.map g * M.map h' ∈ Matrix.unitaryGroup M.carrier ℂ :=
      Submonoid.mul_mem _ (M.isUnitary g) (M.isUnitary h')
    have hcomb : tensorPow (conjDouble (M.map g)) k
        * tensorPow (conjDouble (M.map h')) k
        = tensorPow (conjDouble (M.map g * M.map h')) k := by
      rw [← tensorPow_mul, ← conjDouble_mul]
    rw [hcomb, hsDistSq_conjDoubleTensorPow M.carrier (M.isUnitary (g * h')) hB
      M.nonempty k]
    -- the source trace is close to `1`, so its `k`-th power is close to `1`
    set z : ℂ := normTrace M.carrier
      (M.map (g * h') * (M.map g * M.map h')ᴴ) with hzdef
    have hsrc : hsDistSq M.carrier (M.map (g * h')) (M.map g * M.map h') ≤ ε₀ :=
      M.multiplicative g hg h' hh'
    rw [hsDistSq_of_unitary M.carrier (M.isUnitary (g * h')) hB M.nonempty]
      at hsrc
    have hre : 1 - ε₀ / 2 ≤ z.re := by rw [hzdef]; linarith
    have hre0 : (0 : ℝ) ≤ 1 - ε₀ / 2 := by linarith
    have hnsq : (1 - ε₀ / 2) ^ 2 ≤ Complex.normSq z := by
      have hsq : (1 - ε₀ / 2) ^ 2 ≤ z.re ^ 2 := by nlinarith
      have : z.re ^ 2 ≤ Complex.normSq z := by
        rw [Complex.normSq_apply]; nlinarith [sq_nonneg z.im]
      linarith
    have hpow : ((1 - ε₀ / 2) ^ 2) ^ k ≤ (Complex.normSq z) ^ k := by
      gcongr
    have hbern : 1 - (k : ℝ) * ε₀ ≤ ((1 - ε₀ / 2) ^ 2) ^ k := by
      have hb := one_add_mul_le_pow
        (a := -(ε₀ / 2)) (by linarith) (2 * k)
      rw [pow_mul] at hb
      have hbase : ((1 : ℝ) + -(ε₀ / 2)) = 1 - ε₀ / 2 := by ring
      have hcast : (1 : ℝ) + ((2 * k : ℕ) : ℝ) * -(ε₀ / 2) = 1 - (k : ℝ) * ε₀ := by
        push_cast; ring
      rw [hbase, hcast] at hb
      exact hb
    linarith
  · intro g hg h' hh' hne
    rw [hsDistSq_conjDoubleTensorPow M.carrier (M.isUnitary g) (M.isUnitary h')
      M.nonempty k]
    have hns := M.nonScalar g hg h' hh' hne
    have hnn : (0 : ℝ) ≤ Complex.normSq
      (normTrace M.carrier (M.map g * (M.map h')ᴴ)) := Complex.normSq_nonneg _
    have hpow : (Complex.normSq
        (normTrace M.carrier (M.map g * (M.map h')ᴴ))) ^ k ≤ (1 - δ) ^ k := by
      gcongr
    linarith

/-- The endpoint reading.  Refuting the middle class already refutes soficity,
and is a weaker hypothesis than refuting hyperlinearity. -/
theorem not_isSofic_of_not_isHyperlinearNonScalar
    (h : ¬ IsHyperlinearNonScalar G) : ¬ IsSofic G :=
  fun hs ↦ h (isHyperlinearNonScalar_of_isSofic hs)

/-- The middle class sits inside hyperlinearity, so refuting hyperlinearity
refutes it too. -/
theorem not_isHyperlinearNonScalar_of_not_isHyperlinear
    (h : ¬ IsHyperlinear G) : ¬ IsHyperlinearNonScalar G :=
  fun hn ↦ h (isHyperlinear_of_isHyperlinearNonScalar hn)

end NonsoficGroupsExist
