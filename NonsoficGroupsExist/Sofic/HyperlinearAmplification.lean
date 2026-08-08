import NonsoficGroupsExist.Sofic.Hyperlinear
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators

/-!
# Tensor powers amplify soficity but not hyperlinearity

For permutation models the separation constant is a convention: the `k`-fold
tensor power sends Hamming distance `d` to `1 - (1 - d)^k`, so a fixed
separation runs to `1` while a small multiplicative defect grows only by a
factor `k` (`Sofic.SoficAmplification`).  One expects the same for unitary
models, and the algebra transports perfectly:

  `τ(A^{⊗k} (B^{⊗k})*) = τ(A B*)^k`   (`normTrace_tensorPow`),

so the squared normalized Hilbert--Schmidt distance obeys the exact law

  `hsDistSq (A^{⊗k}) (B^{⊗k}) = 2 - 2 Re (τ(A B*)^k)`   (`hsDistSq_tensorPow`).

**The amplification nevertheless fails**, and `tensorPow_phase_collapse` says so
with a witness: on any nonempty model `1` and `i · 1` are unitary and separated
by the full `hsDistSq = 2`, yet their fourth tensor powers are *equal*.  The
mechanism is `tensorPow_smul`: a scalar `c` becomes `c^k`, so the `k`-th tensor
power identifies any two unitaries differing by a `k`-th root of unity.
Permutation matrices carry no phases, which is exactly why the sofic argument
works and this one does not.  A trace can be small because it *cancels* rather
than because the matrices are far apart, and tensoring recombines the
cancellation.

The repair is to tensor with the conjugate rather than with a further copy.
`conjDouble A = A ⊗ Ā` is again multiplicative and unitary, and its normalized
trace is `|τ(A)|²` -- a *nonnegative real*, so there is no phase left to
recombine.  `hsDistSq_conjDoubleTensorPow` gives the exact law

  `hsDistSq ((A ⊗ Ā)^{⊗k}) ((B ⊗ B̄)^{⊗k}) = 2 - 2 |τ(A B*)|^{2k}`,

and `exists_conjDouble_separation` turns any bound `|τ(A B*)|² ≤ 1 - δ` into
separation `2 - ε`.  That hypothesis is not removable: `|τ(U)|² ≤ 1` always, with equality exactly
for scalars -- the phase collapse again.  `Sofic.HyperlinearScalar` proves both
facts from one identity, `‖U - τ(U)·1‖² = 1 - |τ(U)|²`.  So for unitary models the separation constant is a convention
*relative to a scalar-freeness hypothesis*, and not otherwise -- an asymmetry
between the two sides of Pestov's Question 3.4 that the permutation picture
hides.

`tensorPow A k` is the `k`-fold Kronecker power written directly on the index
type `Fin k → Y`: its `(f, g)` entry is `∏ i, A (f i) (g i)`.  Both the trace
identity and multiplicativity (`tensorPow_mul`) are instances of the
distributive law `∑_h ∏_i F i (h i) = ∏_i ∑_y F i y`.
-/

namespace NonsoficGroupsExist

open Matrix

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-! ## The tensor power of a matrix -/

/-- The `k`-fold tensor (Kronecker) power, on the index type `Fin k → Y`. -/
def tensorPow (A : Matrix Y Y ℂ) (k : ℕ) :
    Matrix (Fin k → Y) (Fin k → Y) ℂ :=
  fun f g ↦ ∏ i : Fin k, A (f i) (g i)

omit [Fintype Y] [DecidableEq Y] in
@[simp] theorem tensorPow_apply (A : Matrix Y Y ℂ) (k : ℕ)
    (f g : Fin k → Y) : tensorPow A k f g = ∏ i : Fin k, A (f i) (g i) := rfl

omit [DecidableEq Y] in
/-- **Tensor powers multiply.**  This and the trace identity are both the
distributive law `∑_h ∏_i F i (h i) = ∏_i ∑_y F i y`. -/
theorem tensorPow_mul (A B : Matrix Y Y ℂ) (k : ℕ) :
    tensorPow (A * B) k = tensorPow A k * tensorPow B k := by
  classical
  ext f g
  simp only [tensorPow_apply, Matrix.mul_apply]
  rw [Finset.prod_univ_sum]
  simp [Finset.prod_mul_distrib, Fintype.piFinset_univ]

omit [Fintype Y] in
/-- The tensor power of the identity is the identity: a product of Kronecker
deltas is the Kronecker delta of the tuples. -/
theorem tensorPow_one (k : ℕ) : tensorPow (1 : Matrix Y Y ℂ) k = 1 := by
  classical
  ext f g
  by_cases h : f = g
  · subst h
    simp [Matrix.one_apply_eq]
  · rw [Matrix.one_apply_ne h, tensorPow_apply]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Matrix.one_apply_ne hi)

omit [Fintype Y] [DecidableEq Y] in
/-- Conjugate transposition passes through the tensor power. -/
theorem tensorPow_conjTranspose (A : Matrix Y Y ℂ) (k : ℕ) :
    (tensorPow A k)ᴴ = tensorPow Aᴴ k := by
  ext f g
  simp [Matrix.conjTranspose_apply]

/-- A tensor power of a unitary is unitary. -/
theorem tensorPow_mem_unitaryGroup {A : Matrix Y Y ℂ}
    (hA : A ∈ Matrix.unitaryGroup Y ℂ) (k : ℕ) :
    tensorPow A k ∈ Matrix.unitaryGroup (Fin k → Y) ℂ := by
  have h1 : A * Aᴴ = 1 := by
    have h := hA
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at h
    exact h
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    tensorPow_conjTranspose, ← tensorPow_mul, h1, tensorPow_one]

omit [Fintype Y] [DecidableEq Y] in
/-- **Scalars are raised to the `k`-th power.**  This one line is the whole
obstruction to unitary amplification. -/
theorem tensorPow_smul (c : ℂ) (A : Matrix Y Y ℂ) (k : ℕ) :
    tensorPow (c • A) k = (c ^ k) • tensorPow A k := by
  ext f g
  simp [Finset.prod_mul_distrib]

omit [DecidableEq Y] in
/-- **The trace identity.**  `tr(A^{⊗k}) = (tr A)^k`, unnormalized. -/
theorem trace_tensorPow (A : Matrix Y Y ℂ) (k : ℕ) :
    Matrix.trace (tensorPow A k) = (Matrix.trace A) ^ k := by
  classical
  have hconst : ∏ _i : Fin k, (∑ y : Y, A y y) = (∑ y : Y, A y y) ^ k := by
    simp
  simp only [Matrix.trace, Matrix.diag, tensorPow_apply]
  rw [← hconst, Finset.prod_univ_sum]
  simp [Fintype.piFinset_univ]

omit [DecidableEq Y] in
/-- The index type of a tensor power has the expected cardinality. -/
@[simp] theorem card_tensorPow_index (k : ℕ) :
    Fintype.card (Fin k → Y) = Fintype.card Y ^ k := by
  rw [Fintype.card_fun, Fintype.card_fin]

/-! ## The normalized trace, and how the tensor power acts on it -/

/-- Normalized trace of a matrix indexed by a finite model. -/
noncomputable def normTrace (Y : FiniteModel) (A : Matrix Y Y ℂ) : ℂ :=
  Matrix.trace A / Fintype.card Y

/-- The model on `k` tensor slots.  Reducible, so that `rw` can see through
`(tensorModel Y k).carrier` to `Fin k → Y`. -/
abbrev tensorModel (Y : FiniteModel) (k : ℕ) : FiniteModel :=
  ⟨Fin k → Y, inferInstance, inferInstance⟩

@[simp] theorem card_tensorModel (Y : FiniteModel) (k : ℕ) :
    Fintype.card (tensorModel Y k) = Fintype.card Y ^ k := by
  show Fintype.card (Fin k → Y) = _
  rw [Fintype.card_fun, Fintype.card_fin]

/-- **The normalized trace is multiplicative under tensor powers.**  This is the
whole content of unitary amplification. -/
theorem normTrace_tensorPow (Y : FiniteModel) (A : Matrix Y Y ℂ) (k : ℕ) :
    normTrace (tensorModel Y k) (tensorPow A k) = (normTrace Y A) ^ k := by
  have htr : Matrix.trace (tensorPow A k) = (Matrix.trace A) ^ k :=
    trace_tensorPow A k
  have hcard : ((Fintype.card (tensorModel Y k) : ℕ) : ℂ)
      = ((Fintype.card Y : ℂ)) ^ k := by
    rw [card_tensorModel]; push_cast; ring
  show Matrix.trace (tensorPow A k) / ((Fintype.card (tensorModel Y k) : ℕ) : ℂ)
      = (Matrix.trace A / ((Fintype.card Y : ℕ) : ℂ)) ^ k
  rw [htr, hcard, div_pow]

/-! ## The Hilbert--Schmidt distance between unitaries is a trace -/

/-- Dividing by a nonzero natural commutes with taking the real part. -/
theorem div_natCast_re (z : ℂ) {n : ℕ} (hn : n ≠ 0) :
    (z / (n : ℂ)).re = z.re / (n : ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  simp only [Complex.div_re, Complex.natCast_re, Complex.natCast_im,
    Complex.normSq_apply]
  field_simp
  ring

/-- Polarization: `|z - w|² = |z|² + |w|² - 2 Re(z w̄)`. -/
theorem normSq_sub_expand (z w : ℂ) :
    Complex.normSq (z - w)
      = Complex.normSq z + Complex.normSq w
        - 2 * (z * (starRingEnd ℂ) w).re := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The entrywise Hermitian pairing of two matrices is the trace of `A Bᴴ`. -/
theorem trace_mul_conjTranspose (Y : FiniteModel) (A B : Matrix Y Y ℂ) :
    Matrix.trace (A * Bᴴ)
      = ∑ i : Y, ∑ j : Y, A i j * (starRingEnd ℂ) (B i j) := by
  show (∑ i : Y, (A * Bᴴ) i i) = _
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Matrix.mul_apply]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [Matrix.conjTranspose_apply]; rfl

/-- Each row of a unitary matrix is a unit vector. -/
theorem row_normSq_of_unitary (Y : FiniteModel) {A : Matrix Y Y ℂ}
    (hA : A ∈ Matrix.unitaryGroup Y ℂ) (i : Y) :
    (∑ j : Y, Complex.normSq (A i j)) = 1 := by
  have h1 : A * Aᴴ = 1 := by
    have h := hA
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at h
    exact h
  have hrow : ((∑ j : Y, Complex.normSq (A i j) : ℝ) : ℂ) = (A * Aᴴ) i i := by
    rw [Complex.ofReal_sum, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Matrix.conjTranspose_apply]
    exact (Complex.mul_conj (A i j)).symm
  rw [h1, Matrix.one_apply_eq] at hrow
  exact_mod_cast hrow

/-- A unitary matrix has total squared entry mass equal to its size. -/
theorem sum_normSq_of_unitary (Y : FiniteModel) {A : Matrix Y Y ℂ}
    (hA : A ∈ Matrix.unitaryGroup Y ℂ) :
    (∑ i : Y, ∑ j : Y, Complex.normSq (A i j)) = Fintype.card Y := by
  rw [Finset.sum_congr rfl fun i _ ↦ row_normSq_of_unitary Y hA i]
  simp

/-- **The Hilbert--Schmidt distance between unitaries is a trace.**  This is the
identity that turns every later computation into a computation about one
complex number. -/
theorem hsDistSq_of_unitary (Y : FiniteModel) {A B : Matrix Y Y ℂ}
    (hA : A ∈ Matrix.unitaryGroup Y ℂ) (hB : B ∈ Matrix.unitaryGroup Y ℂ)
    (hY : 0 < Fintype.card Y) :
    hsDistSq Y A B = 2 - 2 * (normTrace Y (A * Bᴴ)).re := by
  have hc : (Fintype.card Y : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hY.ne'
  have hstep : ∀ i : Y, (∑ j : Y, Complex.normSq (A i j - B i j))
      = (∑ j : Y, Complex.normSq (A i j)) + (∑ j : Y, Complex.normSq (B i j))
        - 2 * ∑ j : Y, (A i j * (starRingEnd ℂ) (B i j)).re := by
    intro i
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ normSq_sub_expand _ _
  have hre : (∑ i : Y, ∑ j : Y, (A i j * (starRingEnd ℂ) (B i j)).re)
      = (Matrix.trace (A * Bᴴ)).re := by
    rw [trace_mul_conjTranspose, Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ ↦ (Complex.re_sum _ _).symm
  have hnum : (∑ i : Y, ∑ j : Y, Complex.normSq (A i j - B i j))
      = 2 * (Fintype.card Y : ℝ) - 2 * (Matrix.trace (A * Bᴴ)).re := by
    rw [Finset.sum_congr rfl fun i _ ↦ hstep i, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, hre,
      sum_normSq_of_unitary Y hA, sum_normSq_of_unitary Y hB]
    ring
  rw [hsDistSq, hnum, normTrace, div_natCast_re _ hY.ne']
  field_simp

/-- **The exact amplification law.**  Tensoring `k` times raises the trace to
the `k`-th power, and nothing else happens. -/
theorem hsDistSq_tensorPow (Y : FiniteModel) {A B : Matrix Y Y ℂ}
    (hA : A ∈ Matrix.unitaryGroup Y ℂ) (hB : B ∈ Matrix.unitaryGroup Y ℂ)
    (hY : 0 < Fintype.card Y) (k : ℕ) :
    hsDistSq (tensorModel Y k) (tensorPow A k) (tensorPow B k)
      = 2 - 2 * ((normTrace Y (A * Bᴴ)) ^ k).re := by
  have hYk : 0 < Fintype.card (tensorModel Y k) := by
    rw [card_tensorModel]; exact pow_pos hY k
  have hprod : tensorPow A k * (tensorPow B k)ᴴ = tensorPow (A * Bᴴ) k := by
    rw [tensorPow_conjTranspose, tensorPow_mul]
  rw [hsDistSq_of_unitary (tensorModel Y k) (tensorPow_mem_unitaryGroup hA k)
    (tensorPow_mem_unitaryGroup hB k) hYk, hprod, normTrace_tensorPow]

/-! ## Tensor powers do not amplify: the scalar-phase obstruction -/

/-- Equal matrices are at distance zero. -/
@[simp] theorem hsDistSq_self (Y : FiniteModel) (A : Matrix Y Y ℂ) :
    hsDistSq Y A A = 0 := by
  simp [hsDistSq]

/-- **Tensor powers destroy separation.**  On any nonempty model, `1` and
`i · 1` are unitary and sit at the full Hilbert--Schmidt separation `2`, and
their fourth tensor powers are *equal*.  The sofic amplification argument
survives the passage to matrices only because permutation matrices have no
phases. -/
theorem tensorPow_phase_collapse (Y : FiniteModel) (hY : 0 < Fintype.card Y) :
    (Complex.I • (1 : Matrix Y Y ℂ)) ∈ Matrix.unitaryGroup Y ℂ ∧
    hsDistSq Y 1 (Complex.I • 1) = 2 ∧
    tensorPow (Complex.I • (1 : Matrix Y Y ℂ)) 4
      = tensorPow (1 : Matrix Y Y ℂ) 4 := by
  classical
  have hc : (Fintype.card Y : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hY.ne'
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.mul_smul,
      Matrix.smul_mul, one_mul, smul_smul]
    norm_num [Complex.star_def, Complex.conj_I, Complex.I_mul_I]
  · have hrow : ∀ i : Y, (∑ j : Y, Complex.normSq
        ((1 : Matrix Y Y ℂ) i j - (Complex.I • (1 : Matrix Y Y ℂ)) i j))
        = 2 := by
      intro i
      rw [Finset.sum_eq_single i]
      · show Complex.normSq ((1 : Matrix Y Y ℂ) i i
          - Complex.I * (1 : Matrix Y Y ℂ) i i) = 2
        rw [Matrix.one_apply_eq]
        norm_num [Complex.normSq_apply]
      · intro j _ hj
        show Complex.normSq ((1 : Matrix Y Y ℂ) i j
          - Complex.I * (1 : Matrix Y Y ℂ) i j) = 0
        rw [Matrix.one_apply_ne (Ne.symm hj)]
        simp
      · intro h
        exact absurd (Finset.mem_univ i) h
    rw [hsDistSq, Finset.sum_congr rfl fun i _ ↦ hrow i, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_comm, mul_div_assoc, div_self hc,
      mul_one]
  · rw [tensorPow_smul]
    have hI : Complex.I ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Complex.I_sq]
      norm_num
    rw [hI, one_smul]

/-! ## The repair: tensoring with the conjugate -/

/-- `A ⊗ Ā`, written directly on the index type `Y × Y`. -/
def conjDouble (A : Matrix Y Y ℂ) : Matrix (Y × Y) (Y × Y) ℂ :=
  fun p q ↦ A p.1 q.1 * (starRingEnd ℂ) (A p.2 q.2)

omit [Fintype Y] [DecidableEq Y] in
@[simp] theorem conjDouble_apply (A : Matrix Y Y ℂ) (p q : Y × Y) :
    conjDouble A p q = A p.1 q.1 * (starRingEnd ℂ) (A p.2 q.2) := rfl

omit [DecidableEq Y] in
/-- `A ↦ A ⊗ Ā` is multiplicative: entrywise conjugation is a ring map. -/
theorem conjDouble_mul (A B : Matrix Y Y ℂ) :
    conjDouble (A * B) = conjDouble A * conjDouble B := by
  ext p q
  simp only [conjDouble_apply, Matrix.mul_apply, map_sum]
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun y _ ↦ ?_
  simp only [map_mul]
  ring

omit [Fintype Y] in
/-- The conjugate double of the identity is the identity. -/
theorem conjDouble_one : conjDouble (1 : Matrix Y Y ℂ) = 1 := by
  classical
  ext p q
  by_cases h : p = q
  · subst h; simp [Matrix.one_apply_eq]
  · rw [Matrix.one_apply_ne h, conjDouble_apply]
    by_cases h1 : p.1 = q.1
    · have h2 : p.2 ≠ q.2 := fun h2 ↦ h (Prod.ext_iff.mpr ⟨h1, h2⟩)
      simp [Matrix.one_apply_ne h2]
    · simp [Matrix.one_apply_ne h1]

omit [Fintype Y] [DecidableEq Y] in
/-- Conjugate transposition passes through `conjDouble`. -/
theorem conjDouble_conjTranspose (A : Matrix Y Y ℂ) :
    conjDouble (Aᴴ) = (conjDouble A)ᴴ := by
  ext p q
  simp [Matrix.conjTranspose_apply, mul_comm]

/-- `A ⊗ Ā` is unitary when `A` is. -/
theorem conjDouble_mem_unitaryGroup {A : Matrix Y Y ℂ}
    (hA : A ∈ Matrix.unitaryGroup Y ℂ) :
    conjDouble A ∈ Matrix.unitaryGroup (Y × Y) ℂ := by
  have h1 : A * Aᴴ = 1 := by
    have h := hA
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at h
    exact h
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    ← conjDouble_conjTranspose, ← conjDouble_mul, h1, conjDouble_one]

omit [DecidableEq Y] in
/-- **The trace of `A ⊗ Ā` is `|tr A|²`**: no phase survives. -/
theorem trace_conjDouble (A : Matrix Y Y ℂ) :
    Matrix.trace (conjDouble A)
      = Matrix.trace A * (starRingEnd ℂ) (Matrix.trace A) := by
  have h1 : Matrix.trace (conjDouble A)
      = ∑ a : Y, ∑ b : Y, A a a * (starRingEnd ℂ) (A b b) := by
    show (∑ p : Y × Y, conjDouble A p p) = _
    rw [Fintype.sum_prod_type]
    simp
  rw [h1]
  show _ = (∑ a : Y, A a a) * (starRingEnd ℂ) (∑ b : Y, A b b)
  rw [map_sum, Finset.sum_mul_sum]

/-- The doubled model.  Reducible for the same reason as `tensorModel`. -/
abbrev doubleModel (Y : FiniteModel) : FiniteModel :=
  ⟨Y × Y, inferInstance, inferInstance⟩

@[simp] theorem card_doubleModel (Y : FiniteModel) :
    Fintype.card (doubleModel Y) = Fintype.card Y * Fintype.card Y := by
  show Fintype.card (Y × Y) = _
  rw [Fintype.card_prod]

/-- **The phase is gone.**  The normalized trace of `A ⊗ Ā` is `|τ(A)|²`, a
nonnegative real. -/
theorem normTrace_conjDouble (Y : FiniteModel) (A : Matrix Y Y ℂ) :
    normTrace (doubleModel Y) (conjDouble A)
      = (Complex.normSq (normTrace Y A) : ℂ) := by
  have hc : ((Fintype.card (doubleModel Y) : ℕ) : ℂ)
      = ((Fintype.card Y : ℕ) : ℂ) * ((Fintype.card Y : ℕ) : ℂ) := by
    rw [card_doubleModel]; push_cast; ring
  have hconj : (starRingEnd ℂ) (normTrace Y A)
      = (starRingEnd ℂ) (Matrix.trace A) / ((Fintype.card Y : ℕ) : ℂ) := by
    rw [normTrace, map_div₀, Complex.conj_natCast]
  show Matrix.trace (conjDouble A)
      / ((Fintype.card (doubleModel Y) : ℕ) : ℂ) = _
  rw [← Complex.mul_conj, hconj, normTrace, trace_conjDouble, hc]
  ring

/-- **The repaired amplification law.**  Tensoring `k` copies of `A ⊗ Ā` sends
the separation to `2 - 2 |τ(A B*)|^{2k}`: the base is a nonnegative real, so
there is no phase left to recombine. -/
theorem hsDistSq_conjDoubleTensorPow (Y : FiniteModel) {A B : Matrix Y Y ℂ}
    (hA : A ∈ Matrix.unitaryGroup Y ℂ) (hB : B ∈ Matrix.unitaryGroup Y ℂ)
    (hY : 0 < Fintype.card Y) (k : ℕ) :
    hsDistSq (tensorModel (doubleModel Y) k)
        (tensorPow (conjDouble A) k) (tensorPow (conjDouble B) k)
      = 2 - 2 * (Complex.normSq (normTrace Y (A * Bᴴ))) ^ k := by
  have hYd : 0 < Fintype.card (doubleModel Y) := by
    rw [card_doubleModel]; exact Nat.mul_pos hY hY
  have hprod : conjDouble A * (conjDouble B)ᴴ = conjDouble (A * Bᴴ) := by
    rw [← conjDouble_conjTranspose, ← conjDouble_mul]
  rw [hsDistSq_tensorPow (doubleModel Y) (conjDouble_mem_unitaryGroup hA)
    (conjDouble_mem_unitaryGroup hB) hYd k, hprod, normTrace_conjDouble,
    ← Complex.ofReal_pow, Complex.ofReal_re]

/-- **Conditional amplification.**  A trace bounded off the unit circle can be
amplified to full separation `2 - ε`, by tensoring enough copies of the
conjugate double. -/
theorem exists_conjDouble_separation (Y : FiniteModel) {A B : Matrix Y Y ℂ}
    (hA : A ∈ Matrix.unitaryGroup Y ℂ) (hB : B ∈ Matrix.unitaryGroup Y ℂ)
    (hY : 0 < Fintype.card Y) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hz : Complex.normSq (normTrace Y (A * Bᴴ)) ≤ 1 - δ) :
    ∃ k : ℕ, 2 - ε ≤ hsDistSq (tensorModel (doubleModel Y) k)
      (tensorPow (conjDouble A) k) (tensorPow (conjDouble B) k) := by
  have hz0 : (0 : ℝ) ≤ Complex.normSq (normTrace Y (A * Bᴴ)) :=
    Complex.normSq_nonneg _
  have hlt : (1 : ℝ) - δ < 1 := by linarith
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (by linarith : (0 : ℝ) < ε / 2) hlt
  refine ⟨k, ?_⟩
  rw [hsDistSq_conjDoubleTensorPow Y hA hB hY k]
  have hpow : (Complex.normSq (normTrace Y (A * Bᴴ))) ^ k ≤ (1 - δ) ^ k := by
    gcongr
  linarith

end NonsoficGroupsExist
