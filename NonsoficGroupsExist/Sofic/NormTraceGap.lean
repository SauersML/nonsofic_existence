import NonsoficGroupsExist.Sofic.HyperlinearAmplification
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# The norm–trace interface: operator-norm approximation carries no trace

Hyperlinearity is approximation in the *normalized Hilbert–Schmidt* metric.
The operator-norm world — matricial approximation of the kind studied under
weak-MF and strong-convergence headings — looks adjacent, and a route to a
negative answer to Question 3.4 has been proposed through it: find a nonsofic
group, prove it operator-norm approximable, conclude hyperlinear.  This file
formalizes the exact interface between the two metrics, and both halves of it
are one-sided in the same direction.

* **The domination** (`hsDistSq_le_sq_l2_opNorm`): the squared normalized
  Hilbert–Schmidt distance is at most the squared operator-norm distance,
  *independently of dimension*.  So operator-norm multiplicativity defects
  transfer to Hilbert–Schmidt defects for free, on any model of any size.

* **The bridge** (`NormModel.toHyperlinearModel`): consequently an
  operator-norm model becomes a hyperlinear model the moment its normalized
  traces separate.  The trace clause is the *entire* active hypothesis: the
  norm clause supplies multiplicativity and nothing else.

* **The gap** (`NormModel.exists_hs_collapse`): the trace clause is not free.
  Padding a model with an identity block of vanishing relative dimension
  preserves every operator-norm distance exactly
  (`l2_opNorm_cornerPad`) while collapsing every Hilbert–Schmidt
  distance below any prescribed bound.  Operator-norm approximation can be one
  hundred percent trace-invisible, so no implication from norm approximability
  to hyperlinearity exists at the level of models, and the proposed route is
  closed at its second arrow unless a trace hypothesis is supplied separately.

* **The tradeoff, corrected** (`norm_normTrace_sub_one_le`,
  `phase_deviation_no_amplification`, `norm_normTrace_tensorPow`): deviation
  supported on a corner of vanishing density forces the normalized trace to
  `1`, so exact or corner-supported data cannot trace-separate — that is the
  padding phenomenon restated pointwise.  But the support of `u - 1` is the
  *wrong* invariant for the converse: `i·1` has invertible deviation — full
  support, full rank — and every tensor power of it has normalized trace of
  modulus one.  The invariant amplification actually drives is
  `1 - ‖normTrace u‖`, the distance to the scalars: the normalized trace is
  exactly multiplicative under tensor powers, so separation amplifies at an
  exponential rate precisely on the non-scalar part.  This is the scalar-phase
  obstruction of `tensorPow_phase_collapse` recurring on the trace side.

What this file does **not** prove, and does not claim: that any group is or is
not operator-norm approximable; any spectral-gap correction of almost
representations; any simplicity statement for the nonsofic witness.  Those are
the open or unformalized parts of the proposed route, and they are quoted
nowhere in this development.
-/

namespace NonsoficGroupsExist

open Matrix
open scoped Matrix.Norms.L2Operator

/-! ## The Euclidean toolkit

Three bridge lemmas between the entrywise `normSq` sums this development
computes with and Mathlib's `L2` operator norm on matrices.  Everything later
goes through these; no other statement mentions `EuclideanSpace`.
-/

/-- The squared Euclidean norm of a vector is its entrywise `normSq` sum. -/
theorem euclidean_norm_sq (Y : FiniteModel) (w : Y → ℂ) :
    ‖(EuclideanSpace.equiv Y ℂ).symm w‖ ^ 2 = ∑ i : Y, Complex.normSq (w i) := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  exact Finset.sum_congr rfl fun i _ ↦ (Complex.normSq_eq_norm_sq _).symm

/-- The operator norm bounds every matrix–vector product, in `normSq` form. -/
theorem sum_normSq_mulVec_le (Y : FiniteModel) (C : Matrix Y Y ℂ) (x : Y → ℂ) :
    ∑ i : Y, Complex.normSq ((C *ᵥ x) i)
      ≤ ‖C‖ ^ 2 * ∑ i : Y, Complex.normSq (x i) := by
  have h : ‖(EuclideanSpace.equiv Y ℂ).symm (C *ᵥ x)‖
      ≤ ‖C‖ * ‖(EuclideanSpace.equiv Y ℂ).symm x‖ :=
    Matrix.l2_opNorm_mulVec C ((EuclideanSpace.equiv Y ℂ).symm x)
  have hL := euclidean_norm_sq Y (C *ᵥ x)
  have hR := euclidean_norm_sq Y x
  have hsq : ‖(EuclideanSpace.equiv Y ℂ).symm (C *ᵥ x)‖ ^ 2
      ≤ (‖C‖ * ‖(EuclideanSpace.equiv Y ℂ).symm x‖) ^ 2 := by
    have h0 : (0 : ℝ) ≤ ‖(EuclideanSpace.equiv Y ℂ).symm (C *ᵥ x)‖ :=
      norm_nonneg _
    nlinarith [norm_nonneg ((EuclideanSpace.equiv Y ℂ).symm x), norm_nonneg C]
  calc ∑ i : Y, Complex.normSq ((C *ᵥ x) i)
      = ‖(EuclideanSpace.equiv Y ℂ).symm (C *ᵥ x)‖ ^ 2 := hL.symm
    _ ≤ (‖C‖ * ‖(EuclideanSpace.equiv Y ℂ).symm x‖) ^ 2 := hsq
    _ = ‖C‖ ^ 2 * ∑ i : Y, Complex.normSq (x i) := by rw [mul_pow, hR]

/-- The converse criterion: a uniform `normSq` bound on matrix–vector products
bounds the operator norm. -/
theorem l2_opNorm_le_of_sum_normSq (Y : FiniteModel) (C : Matrix Y Y ℂ)
    {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ x : Y → ℂ, ∑ i : Y, Complex.normSq ((C *ᵥ x) i)
      ≤ M ^ 2 * ∑ i : Y, Complex.normSq (x i)) :
    ‖C‖ ≤ M := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hM fun x ↦ ?_
  have hL : ‖(EuclideanSpace.equiv Y ℂ).symm (C *ᵥ x)‖ ^ 2
      = ∑ i : Y, Complex.normSq ((C *ᵥ x) i) := euclidean_norm_sq Y _
  have hR : ‖(EuclideanSpace.equiv Y ℂ).symm x‖ ^ 2
      = ∑ i : Y, Complex.normSq (x i) := euclidean_norm_sq Y x
  have hval : ‖(LinearEquiv.trans (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Y) (n := Y))
      LinearMap.toContinuousLinearMap C) x‖
      = ‖(EuclideanSpace.equiv Y ℂ).symm (C *ᵥ x)‖ := rfl
  rw [hval]
  have hx : ‖(EuclideanSpace.equiv Y ℂ).symm (C *ᵥ x)‖ ^ 2 ≤ (M * ‖x‖) ^ 2 := by
    rw [hL, mul_pow]
    have hxx : ‖x‖ ^ 2 = ∑ i : Y, Complex.normSq (x i) := hR
    rw [hxx]
    exact h x
  have h1 : ‖(EuclideanSpace.equiv Y ℂ).symm (C *ᵥ x)‖
      = Real.sqrt (‖(EuclideanSpace.equiv Y ℂ).symm (C *ᵥ x)‖ ^ 2) :=
    (Real.sqrt_sq (norm_nonneg _)).symm
  have h2 : Real.sqrt ((M * ‖x‖) ^ 2) = M * ‖x‖ :=
    Real.sqrt_sq (mul_nonneg hM (norm_nonneg _))
  rw [h1, ← h2]
  exact Real.sqrt_le_sqrt hx

/-- Every entry is bounded by the operator norm. -/
theorem normSq_entry_le_sq_l2_opNorm (Y : FiniteModel) (C : Matrix Y Y ℂ)
    (i j : Y) : Complex.normSq (C i j) ≤ ‖C‖ ^ 2 := by
  classical
  have h := sum_normSq_mulVec_le Y C (Pi.single j 1)
  have hcol : ∀ k : Y, (C *ᵥ Pi.single j (1 : ℂ)) k = C k j := by
    intro k
    rw [Matrix.mulVec_single_one]
    rfl
  have hx : ∑ k : Y, Complex.normSq ((Pi.single j (1 : ℂ) : Y → ℂ) k) = 1 := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hterm : Complex.normSq (C i j)
      ≤ ∑ k : Y, Complex.normSq ((C *ᵥ Pi.single j (1 : ℂ)) k) := by
    have hmem : Complex.normSq ((C *ᵥ Pi.single j (1 : ℂ)) i)
        ≤ ∑ k : Y, Complex.normSq ((C *ᵥ Pi.single j (1 : ℂ)) k) :=
      Finset.single_le_sum (fun k _ ↦ Complex.normSq_nonneg _)
        (Finset.mem_univ i)
    rwa [hcol i] at hmem
  rw [hx, mul_one] at h
  exact hterm.trans h

/-! ## The domination: Hilbert–Schmidt below operator norm, at every size -/

/-- **Operator-norm defects dominate normalized Hilbert–Schmidt defects,
independently of dimension.**  Column by column: each column of `C` is a
matrix–vector product against a basis vector, so its mass is at most `‖C‖²`,
and the normalization divides by exactly the number of columns. -/
theorem hsDistSq_le_sq_l2_opNorm (Y : FiniteModel) (A B : Matrix Y Y ℂ) :
    hsDistSq Y A B ≤ ‖A - B‖ ^ 2 := by
  classical
  set C := A - B with hC
  have hcol : ∀ j : Y, ∑ i : Y, Complex.normSq (C i j) ≤ ‖C‖ ^ 2 := by
    intro j
    have h := sum_normSq_mulVec_le Y C (Pi.single j 1)
    have hx : ∑ k : Y, Complex.normSq ((Pi.single j (1 : ℂ) : Y → ℂ) k) = 1 := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb
        simp [hb]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    have hcolv : ∀ k : Y, (C *ᵥ Pi.single j (1 : ℂ)) k = C k j := by
      intro k
      rw [Matrix.mulVec_single_one]
      rfl
    rw [hx, mul_one] at h
    calc ∑ i : Y, Complex.normSq (C i j)
        = ∑ i : Y, Complex.normSq ((C *ᵥ Pi.single j (1 : ℂ)) i) :=
          Finset.sum_congr rfl fun i _ ↦ by rw [hcolv i]
      _ ≤ ‖C‖ ^ 2 := h
  have hsum : ∑ i : Y, ∑ j : Y, Complex.normSq (C i j)
      ≤ (Fintype.card Y : ℝ) * ‖C‖ ^ 2 := by
    rw [Finset.sum_comm]
    calc ∑ j : Y, ∑ i : Y, Complex.normSq (C i j)
        ≤ ∑ _j : Y, ‖C‖ ^ 2 := Finset.sum_le_sum fun j _ ↦ hcol j
      _ = (Fintype.card Y : ℝ) * ‖C‖ ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  show (∑ i : Y, ∑ j : Y, Complex.normSq (A i j - B i j)) / Fintype.card Y
      ≤ ‖A - B‖ ^ 2
  by_cases hY : Fintype.card Y = 0
  · rw [hY]
    simp only [Nat.cast_zero, div_zero]
    positivity
  · have hYpos : (0 : ℝ) < Fintype.card Y := by
      exact_mod_cast Nat.pos_of_ne_zero hY
    rw [div_le_iff₀ hYpos]
    calc ∑ i : Y, ∑ j : Y, Complex.normSq (A i j - B i j)
        ≤ (Fintype.card Y : ℝ) * ‖C‖ ^ 2 := hsum
      _ = ‖A - B‖ ^ 2 * (Fintype.card Y : ℝ) := by rw [hC]; ring

/-! ## Operator-norm models

The operator-norm analogue of `HyperlinearModel`: unitary matrices,
multiplicativity and separation both measured in operator norm.  This is the
shape of matricial approximation the weak-MF literature quantifies over, in
the same local finite-test-set format as every other model in this
development.  `δ` is the separation constant and `ε` the multiplicative
accuracy; the separation is pinned at a constant because the operator norm,
unlike the Hilbert–Schmidt norm on unitaries, has no canonical maximal
separation to normalize to.
-/

/-- A finite unitary model with both laws measured in operator norm. -/
structure NormModel (G : Type*) [Group G] (F : Finset G) (δ ε : ℝ) where
  carrier : FiniteModel
  nonempty : 0 < Fintype.card carrier
  map : G → Matrix carrier carrier ℂ
  isUnitary : ∀ g, map g ∈ Matrix.unitaryGroup carrier ℂ
  multiplicative : ∀ g ∈ F, ∀ h ∈ F, ‖map (g * h) - map g * map h‖ ≤ ε
  separated : ∀ g ∈ F, ∀ h ∈ F, g ≠ h → δ ≤ ‖map g - map h‖

/-- Operator-norm approximability with separation pinned at `δ`. -/
def IsNormApproximable (G : Type*) [Group G] (δ : ℝ) : Prop :=
  ∀ (F : Finset G) (ε : ℝ), 0 < ε → Nonempty (NormModel G F δ ε)

/-- **Positive control: finite groups are norm-approximable at separation
`1`**, by the regular representation — an exact homomorphism, with distinct
permutation matrices separated because they differ by `1` in some entry. -/
theorem isNormApproximable_of_finite (G : Type) [Group G] [Finite G] :
    IsNormApproximable G 1 := by
  classical
  intro F ε hε
  letI : Fintype G := Fintype.ofFinite G
  set Y : FiniteModel := ⟨G, inferInstance, inferInstance⟩ with hY
  refine ⟨{
    carrier := Y
    nonempty := Fintype.card_pos_iff.mpr ⟨(1 : G)⟩
    map := fun g ↦ ((MulAction.toPermHom G G g)⁻¹).permMatrix ℂ
    isUnitary := fun g ↦ permMatrix_mem_unitaryGroup Y _
    multiplicative := ?_
    separated := ?_ }⟩
  · intro g _ h _
    have hhom : ((MulAction.toPermHom G G g)⁻¹).permMatrix ℂ
          * ((MulAction.toPermHom G G h)⁻¹).permMatrix ℂ
        = ((MulAction.toPermHom G G (g * h))⁻¹).permMatrix ℂ := by
      rw [map_mul, _root_.mul_inv_rev, Matrix.permMatrix_mul]
    rw [hhom, sub_self, norm_zero]
    exact hε.le
  · intro g _ h _ hne
    have hg1 : (MulAction.toPermHom G G g)⁻¹ (1 : G) = g⁻¹ := by
      simp [MulAction.toPermHom]
    have hh1 : ¬ (MulAction.toPermHom G G h)⁻¹ (1 : G) = g⁻¹ := by
      have : (MulAction.toPermHom G G h)⁻¹ (1 : G) = h⁻¹ := by
        simp [MulAction.toPermHom]
      rw [this]
      exact fun hcon ↦ hne (inv_injective hcon).symm
    have hPent := permMatrixC_entry Y ((MulAction.toPermHom G G g)⁻¹)
      (1 : G) g⁻¹
    have hQent := permMatrixC_entry Y ((MulAction.toPermHom G G h)⁻¹)
      (1 : G) g⁻¹
    rw [if_pos hg1] at hPent
    rw [if_neg hh1] at hQent
    have hentry : Complex.normSq
        ((((MulAction.toPermHom G G g)⁻¹).permMatrix ℂ
          - ((MulAction.toPermHom G G h)⁻¹).permMatrix ℂ) (1 : G) g⁻¹) = 1 := by
      rw [Matrix.sub_apply, hPent, hQent, sub_zero]
      simp
    have hle := normSq_entry_le_sq_l2_opNorm Y
      (((MulAction.toPermHom G G g)⁻¹).permMatrix ℂ
        - ((MulAction.toPermHom G G h)⁻¹).permMatrix ℂ) (1 : G) g⁻¹
    rw [hentry] at hle
    nlinarith [norm_nonneg (((MulAction.toPermHom G G g)⁻¹).permMatrix ℂ
      - ((MulAction.toPermHom G G h)⁻¹).permMatrix ℂ)]

/-- A closed witness, so `IsNormApproximable` is not a certificate nothing
satisfies. -/
theorem isNormApproximable_trivial : IsNormApproximable (PUnit : Type) 1 :=
  isNormApproximable_of_finite PUnit

/-! ## The bridge: the trace clause is the entire active hypothesis -/

/-- **An operator-norm model with separating traces is a hyperlinear model.**
The multiplicativity transfers through the domination inequality with no loss
of dimension; the separation is exactly the trace hypothesis, through the
trace identity for the Hilbert–Schmidt distance of unitaries.  Nothing else
about the operator-norm structure is used: the norm clause contributes
multiplicativity and nothing more. -/
noncomputable def NormModel.toHyperlinearModel {G : Type*} [Group G]
    {F : Finset G} {δ η ε : ℝ} (M : NormModel G F δ η) (hmul : η ^ 2 ≤ ε)
    (htr : ∀ g ∈ F, ∀ h ∈ F, g ≠ h →
      (normTrace M.carrier (M.map g * (M.map h)ᴴ)).re ≤ ε / 2) :
    HyperlinearModel G F ε where
  carrier := M.carrier
  nonempty := M.nonempty
  map := M.map
  isUnitary := M.isUnitary
  multiplicative := by
    intro g hg h hh
    have hd := M.multiplicative g hg h hh
    have hsq : ‖M.map (g * h) - M.map g * M.map h‖ ^ 2 ≤ η ^ 2 := by
      nlinarith [norm_nonneg (M.map (g * h) - M.map g * M.map h)]
    exact le_trans (hsDistSq_le_sq_l2_opNorm M.carrier _ _) (hsq.trans hmul)
  separated := by
    intro g hg h hh hne
    rw [hsDistSq_of_unitary M.carrier (M.isUnitary g) (M.isUnitary h)
      M.nonempty]
    have := htr g hg h hh hne
    linarith

/-- The bridge at the level of the properties: norm models whose traces
separate witness hyperlinearity. -/
theorem isHyperlinear_of_traced_normModels {G : Type*} [Group G]
    (h : ∀ (F : Finset G) (ε : ℝ), 0 < ε →
      ∃ (δ η : ℝ) (M : NormModel G F δ η), η ^ 2 ≤ ε ∧
        ∀ g ∈ F, ∀ h' ∈ F, g ≠ h' →
          (normTrace M.carrier (M.map g * (M.map h')ᴴ)).re ≤ ε / 2) :
    IsHyperlinear G := by
  intro F ε hε
  obtain ⟨δ, η, M, hmul, htr⟩ := h F ε hε
  exact ⟨M.toHyperlinearModel hmul htr⟩

/-! ## The corner padding

The block-diagonal extension of a model by an identity block.  It preserves
units, products, adjoints, and — the point — every operator-norm distance
exactly, while diluting every Hilbert–Schmidt quantity by the relative
dimension of the original block.
-/

/-- The padded model: the original carrier plus `m` fresh points. -/
abbrev padModel (Y : FiniteModel) (m : ℕ) : FiniteModel :=
  ⟨Y ⊕ Fin m, inferInstance, inferInstance⟩

@[simp] theorem card_padModel (Y : FiniteModel) (m : ℕ) :
    Fintype.card (padModel Y m) = Fintype.card Y + m := by
  show Fintype.card (Y ⊕ Fin m) = _
  rw [Fintype.card_sum, Fintype.card_fin]

/-- The padded matrix: the original in the corner, the identity outside. -/
def padMatrix (Y : FiniteModel) (m : ℕ) (A : Matrix Y Y ℂ) :
    Matrix (padModel Y m) (padModel Y m) ℂ :=
  Matrix.fromBlocks A 0 0 1

theorem padMatrix_mul (Y : FiniteModel) (m : ℕ) (A B : Matrix Y Y ℂ) :
    padMatrix Y m A * padMatrix Y m B = padMatrix Y m (A * B) := by
  unfold padMatrix
  rw [Matrix.fromBlocks_multiply]
  congr 1 <;> simp

theorem padMatrix_one (Y : FiniteModel) (m : ℕ) :
    padMatrix Y m (1 : Matrix Y Y ℂ) = 1 := by
  unfold padMatrix
  exact Matrix.fromBlocks_one

theorem padMatrix_conjTranspose (Y : FiniteModel) (m : ℕ) (A : Matrix Y Y ℂ) :
    (padMatrix Y m A)ᴴ = padMatrix Y m Aᴴ := by
  unfold padMatrix
  rw [Matrix.fromBlocks_conjTranspose]
  congr 1 <;> simp

theorem padMatrix_mem_unitaryGroup (Y : FiniteModel) (m : ℕ)
    {A : Matrix Y Y ℂ} (hA : A ∈ Matrix.unitaryGroup Y ℂ) :
    padMatrix Y m A ∈ Matrix.unitaryGroup (padModel Y m) ℂ := by
  have h1 : A * Aᴴ = 1 := by
    have h := hA
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at h
    exact h
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    padMatrix_conjTranspose, padMatrix_mul, h1, padMatrix_one]

theorem padMatrix_sub (Y : FiniteModel) (m : ℕ) (A B : Matrix Y Y ℂ) :
    padMatrix Y m A - padMatrix Y m B
      = Matrix.fromBlocks (A - B) 0 0 0 := by
  unfold padMatrix
  ext p q
  cases p <;> cases q <;>
    simp [Matrix.fromBlocks, Matrix.sub_apply]

/-- **The corner block has the full operator norm.**  Both inequalities go
through the vector criterion: a vector for the corner extends by zero, and a
vector for the whole splits with the complement contributing nothing. -/
theorem l2_opNorm_cornerPad (Y : FiniteModel) (m : ℕ) (C : Matrix Y Y ℂ) :
    ‖(Matrix.fromBlocks C 0 0 0 :
        Matrix (padModel Y m) (padModel Y m) ℂ)‖ = ‖C‖ := by
  classical
  set F : Matrix (padModel Y m) (padModel Y m) ℂ :=
    Matrix.fromBlocks C 0 0 0 with hF
  have hmv : ∀ x : (Y ⊕ Fin m) → ℂ,
      F *ᵥ x = Sum.elim (C *ᵥ (x ∘ Sum.inl)) 0 := by
    intro x
    rw [hF, Matrix.fromBlocks_mulVec]
    congr 1 <;> simp
  apply le_antisymm
  · refine l2_opNorm_le_of_sum_normSq (padModel Y m) F (norm_nonneg C)
      fun x ↦ ?_
    have hsplit : ∑ p : Y ⊕ Fin m, Complex.normSq ((F *ᵥ x) p)
        = ∑ i : Y, Complex.normSq ((C *ᵥ (x ∘ Sum.inl)) i) := by
      rw [Fintype.sum_sum_type]
      have h1 : ∀ i : Y, Complex.normSq ((F *ᵥ x) (Sum.inl i))
          = Complex.normSq ((C *ᵥ (x ∘ Sum.inl)) i) := by
        intro i
        rw [hmv]
        rfl
      have h2 : ∀ j : Fin m, Complex.normSq ((F *ᵥ x) (Sum.inr j)) = 0 := by
        intro j
        rw [hmv]
        simp
      rw [Finset.sum_congr rfl fun i _ ↦ h1 i,
        Finset.sum_congr rfl fun j _ ↦ h2 j]
      simp
    rw [hsplit]
    calc ∑ i : Y, Complex.normSq ((C *ᵥ (x ∘ Sum.inl)) i)
        ≤ ‖C‖ ^ 2 * ∑ i : Y, Complex.normSq ((x ∘ Sum.inl) i) :=
          sum_normSq_mulVec_le Y C _
      _ ≤ ‖C‖ ^ 2 * ∑ p : Y ⊕ Fin m, Complex.normSq (x p) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          rw [Fintype.sum_sum_type]
          have : (0 : ℝ) ≤ ∑ j : Fin m, Complex.normSq (x (Sum.inr j)) :=
            Finset.sum_nonneg fun j _ ↦ Complex.normSq_nonneg _
          have hle : ∑ i : Y, Complex.normSq ((x ∘ Sum.inl) i)
              = ∑ i : Y, Complex.normSq (x (Sum.inl i)) := rfl
          linarith [hle.le]
  · refine l2_opNorm_le_of_sum_normSq Y C (norm_nonneg F) fun x ↦ ?_
    set xhat : (Y ⊕ Fin m) → ℂ := Sum.elim x 0 with hxhat
    have hcomp : xhat ∘ Sum.inl = x := rfl
    have hval : ∀ i : Y, (C *ᵥ x) i = (F *ᵥ xhat) (Sum.inl i) := by
      intro i
      rw [hmv, hcomp]
      rfl
    have hxsum : ∑ p : Y ⊕ Fin m, Complex.normSq (xhat p)
        = ∑ i : Y, Complex.normSq (x i) := by
      rw [Fintype.sum_sum_type]
      have h2 : ∀ j : Fin m, Complex.normSq (xhat (Sum.inr j)) = 0 := by
        intro j
        simp [hxhat]
      rw [Finset.sum_congr rfl fun j _ ↦ h2 j]
      simp [hxhat]
    calc ∑ i : Y, Complex.normSq ((C *ᵥ x) i)
        = ∑ i : Y, Complex.normSq ((F *ᵥ xhat) (Sum.inl i)) :=
          Finset.sum_congr rfl fun i _ ↦ by rw [hval i]
      _ ≤ ∑ p : Y ⊕ Fin m, Complex.normSq ((F *ᵥ xhat) p) := by
          rw [Fintype.sum_sum_type]
          have : (0 : ℝ) ≤ ∑ j : Fin m,
              Complex.normSq ((F *ᵥ xhat) (Sum.inr j)) :=
            Finset.sum_nonneg fun j _ ↦ Complex.normSq_nonneg _
          linarith
      _ ≤ ‖F‖ ^ 2 * ∑ p : Y ⊕ Fin m, Complex.normSq (xhat p) :=
          sum_normSq_mulVec_le (padModel Y m) F xhat
      _ = ‖F‖ ^ 2 * ∑ i : Y, Complex.normSq (x i) := by rw [hxsum]

/-- Padding dilutes the Hilbert–Schmidt mass by the relative dimension. -/
theorem hsDistSq_padMatrix (Y : FiniteModel) (m : ℕ) (A B : Matrix Y Y ℂ) :
    hsDistSq (padModel Y m) (padMatrix Y m A) (padMatrix Y m B)
      = (∑ i : Y, ∑ j : Y, Complex.normSq (A i j - B i j))
          / (Fintype.card Y + m) := by
  have hnum : ∑ p : Y ⊕ Fin m, ∑ q : Y ⊕ Fin m,
      Complex.normSq ((padMatrix Y m A) p q - (padMatrix Y m B) p q)
      = ∑ i : Y, ∑ j : Y, Complex.normSq (A i j - B i j) := by
    have hentry : ∀ p q : Y ⊕ Fin m,
        (padMatrix Y m A) p q - (padMatrix Y m B) p q
          = (Matrix.fromBlocks (A - B) 0 0 0 :
              Matrix (padModel Y m) (padModel Y m) ℂ) p q := by
      intro p q
      rw [← Matrix.sub_apply, padMatrix_sub]
    rw [Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ by
      rw [hentry p q]]
    rw [Fintype.sum_sum_type]
    have hrowl : ∀ i : Y, ∑ q : Y ⊕ Fin m, Complex.normSq
        ((Matrix.fromBlocks (A - B) 0 0 0 :
          Matrix (padModel Y m) (padModel Y m) ℂ) (Sum.inl i) q)
        = ∑ j : Y, Complex.normSq (A i j - B i j) := by
      intro i
      rw [Fintype.sum_sum_type]
      have h1 : ∀ j : Y, (Matrix.fromBlocks (A - B) 0 0 0 :
          Matrix (padModel Y m) (padModel Y m) ℂ) (Sum.inl i) (Sum.inl j)
          = A i j - B i j := fun j ↦ rfl
      have h2 : ∀ j : Fin m, Complex.normSq ((Matrix.fromBlocks (A - B) 0 0 0 :
          Matrix (padModel Y m) (padModel Y m) ℂ) (Sum.inl i) (Sum.inr j))
          = 0 := by
        intro j
        show Complex.normSq ((0 : Matrix Y (Fin m) ℂ) i j) = 0
        simp
      rw [Finset.sum_congr rfl fun j _ ↦ by rw [h1 j],
        Finset.sum_congr rfl fun j _ ↦ h2 j]
      simp
    have hrowr : ∀ p : Fin m, ∑ q : Y ⊕ Fin m, Complex.normSq
        ((Matrix.fromBlocks (A - B) 0 0 0 :
          Matrix (padModel Y m) (padModel Y m) ℂ) (Sum.inr p) q) = 0 := by
      intro p
      rw [Fintype.sum_sum_type]
      have h1 : ∀ j : Y, Complex.normSq ((Matrix.fromBlocks (A - B) 0 0 0 :
          Matrix (padModel Y m) (padModel Y m) ℂ) (Sum.inr p) (Sum.inl j))
          = 0 := by
        intro j
        show Complex.normSq ((0 : Matrix (Fin m) Y ℂ) p j) = 0
        simp
      have h2 : ∀ j : Fin m, Complex.normSq ((Matrix.fromBlocks (A - B) 0 0 0 :
          Matrix (padModel Y m) (padModel Y m) ℂ) (Sum.inr p) (Sum.inr j))
          = 0 := by
        intro j
        show Complex.normSq ((0 : Matrix (Fin m) (Fin m) ℂ) p j) = 0
        simp
      rw [Finset.sum_congr rfl fun j _ ↦ h1 j,
        Finset.sum_congr rfl fun j _ ↦ h2 j]
      simp
    rw [Finset.sum_congr rfl fun i _ ↦ hrowl i,
      Finset.sum_congr rfl fun p _ ↦ hrowr p]
    simp
  show (∑ p : Y ⊕ Fin m, ∑ q : Y ⊕ Fin m,
      Complex.normSq ((padMatrix Y m A) p q - (padMatrix Y m B) p q))
      / Fintype.card (padModel Y m) = _
  rw [hnum, card_padModel]
  push_cast
  ring_nf

/-! ## Trace bounds for unitaries -/

/-- The normalized trace of a unitary has modulus at most one. -/
theorem norm_normTrace_le_one (Y : FiniteModel) {A : Matrix Y Y ℂ}
    (hA : A ∈ Matrix.unitaryGroup Y ℂ) (hY : 0 < Fintype.card Y) :
    ‖normTrace Y A‖ ≤ 1 := by
  have hdiag : ∀ i : Y, ‖A i i‖ ≤ 1 := by
    intro i
    have hrow := row_normSq_of_unitary Y hA i
    have hle : Complex.normSq (A i i) ≤ 1 := by
      have := Finset.single_le_sum
        (fun j (_ : j ∈ Finset.univ) ↦ Complex.normSq_nonneg (A i j))
        (Finset.mem_univ i)
      linarith [hrow ▸ this]
    have hsq : ‖A i i‖ ^ 2 ≤ 1 := by
      rwa [← Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (A i i)]
  have htr : ‖Matrix.trace A‖ ≤ (Fintype.card Y : ℝ) := by
    calc ‖Matrix.trace A‖ = ‖∑ i : Y, A i i‖ := rfl
      _ ≤ ∑ i : Y, ‖A i i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Y, (1 : ℝ) := Finset.sum_le_sum fun i _ ↦ hdiag i
      _ = (Fintype.card Y : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hc : (0 : ℝ) < (Fintype.card Y : ℝ) := by exact_mod_cast hY
  rw [normTrace, norm_div, Complex.norm_natCast]
  rw [div_le_one hc]
  exact htr

/-- Between unitaries the Hilbert–Schmidt distance is at most `4`. -/
theorem hsDistSq_le_four_of_unitary (Y : FiniteModel) {A B : Matrix Y Y ℂ}
    (hA : A ∈ Matrix.unitaryGroup Y ℂ) (hB : B ∈ Matrix.unitaryGroup Y ℂ)
    (hY : 0 < Fintype.card Y) : hsDistSq Y A B ≤ 4 := by
  have hBH : Bᴴ ∈ Matrix.unitaryGroup Y ℂ := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.star_mem hB
  have hAB : A * Bᴴ ∈ Matrix.unitaryGroup Y ℂ := mul_mem hA hBH
  have h1 := norm_normTrace_le_one Y hAB hY
  have hre : |(normTrace Y (A * Bᴴ)).re| ≤ 1 :=
    le_trans (Complex.abs_re_le_norm _) h1
  rw [hsDistSq_of_unitary Y hA hB hY]
  have := abs_le.mp hre
  linarith [this.1]

/-! ## The corner-hiding theorem: norm data is trace-invisible

Padding preserves the operator-norm structure of a model exactly and dilutes
its Hilbert–Schmidt geometry to nothing.  So operator-norm approximability
places no constraint whatever on the Hilbert–Schmidt side: the trace clause of
the bridge is not a convenience but the entire content, and no argument from
norm approximation to hyperlinearity can avoid supplying it separately.
-/

/-- **Every norm model collapses below any Hilbert–Schmidt bound with its
operator-norm data intact.**  The padded model has the same multiplicative
defect and the same separation, and all its pairwise Hilbert–Schmidt
distances are below the prescribed `η`. -/
theorem NormModel.exists_hs_collapse {G : Type*} [Group G] {F : Finset G}
    {δ ε : ℝ} (M : NormModel G F δ ε) {η : ℝ} (hη : 0 < η) :
    ∃ M' : NormModel G F δ ε,
      ∀ g ∈ F, ∀ h ∈ F,
        hsDistSq M'.carrier (M'.map g) (M'.map h) ≤ η := by
  classical
  obtain ⟨m, hm⟩ := exists_nat_gt (4 * (Fintype.card M.carrier : ℝ) / η)
  refine ⟨{
    carrier := padModel M.carrier m
    nonempty := by
      rw [card_padModel]
      exact lt_of_lt_of_le M.nonempty (Nat.le_add_right _ _)
    map := fun g ↦ padMatrix M.carrier m (M.map g)
    isUnitary := fun g ↦ padMatrix_mem_unitaryGroup M.carrier m (M.isUnitary g)
    multiplicative := ?_
    separated := ?_ }, ?_⟩
  · intro g hg h hh
    have hmul := M.multiplicative g hg h hh
    rw [padMatrix_mul, padMatrix_sub, l2_opNorm_cornerPad]
    exact hmul
  · intro g hg h hh hne
    have hsep := M.separated g hg h hh hne
    rw [padMatrix_sub, l2_opNorm_cornerPad]
    exact hsep
  · intro g hg h hh
    have hcpos : (0 : ℝ) < (Fintype.card M.carrier : ℝ) := by
      exact_mod_cast M.nonempty
    have hbound : hsDistSq M.carrier (M.map g) (M.map h) ≤ 4 :=
      hsDistSq_le_four_of_unitary M.carrier (M.isUnitary g) (M.isUnitary h)
        M.nonempty
    have hnum : (∑ i : M.carrier, ∑ j : M.carrier,
        Complex.normSq (M.map g i j - M.map h i j))
        ≤ 4 * (Fintype.card M.carrier : ℝ) := by
      have hdef : hsDistSq M.carrier (M.map g) (M.map h)
          = (∑ i : M.carrier, ∑ j : M.carrier,
              Complex.normSq (M.map g i j - M.map h i j))
            / (Fintype.card M.carrier : ℝ) := rfl
      rw [hdef, div_le_iff₀ hcpos] at hbound
      linarith
    rw [hsDistSq_padMatrix]
    have hden : (0 : ℝ) < (Fintype.card M.carrier : ℝ) + (m : ℝ) := by
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    rw [div_le_iff₀ hden]
    have hη4 : 4 * (Fintype.card M.carrier : ℝ)
        ≤ η * ((Fintype.card M.carrier : ℝ) + (m : ℝ)) := by
      have h2 : 4 * (Fintype.card M.carrier : ℝ) < η * m := by
        rw [div_lt_iff₀ hη] at hm
        linarith
      nlinarith [hη.le, hcpos.le]
    linarith

/-! ## Corner-supported deviation cannot trace-separate -/

/-- **Deviation of vanishing density is trace-invisible.**  A unitary whose
diagonal is `1` outside a set of density `ρ` has normalized trace within `2ρ`
of `1`.  Exact data — deviation supported on a corner of vanishing relative
dimension — therefore cannot separate anything from the identity in trace, in
operator norm or otherwise: the separation has to be manufactured by the
inexactness itself. -/
theorem norm_normTrace_sub_one_le (Y : FiniteModel) {A : Matrix Y Y ℂ}
    (hA : A ∈ Matrix.unitaryGroup Y ℂ) (hY : 0 < Fintype.card Y)
    (S : Finset Y) (hS : ∀ i ∉ S, A i i = 1) :
    ‖normTrace Y A - 1‖ ≤ 2 * S.card / Fintype.card Y := by
  classical
  have hc : (0 : ℝ) < (Fintype.card Y : ℝ) := by exact_mod_cast hY
  have hdiag : ∀ i : Y, ‖A i i - 1‖ ≤ 2 := by
    intro i
    have hrow := row_normSq_of_unitary Y hA i
    have hle : Complex.normSq (A i i) ≤ 1 := by
      have := Finset.single_le_sum
        (fun j (_ : j ∈ Finset.univ) ↦ Complex.normSq_nonneg (A i j))
        (Finset.mem_univ i)
      linarith [hrow ▸ this]
    have hnorm : ‖A i i‖ ≤ 1 := by
      have hsq : ‖A i i‖ ^ 2 ≤ 1 := by rwa [← Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg (A i i)]
    calc ‖A i i - 1‖ ≤ ‖A i i‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by
          rw [norm_one]
          linarith
      _ = 2 := by norm_num
  have hsum : Matrix.trace A - Fintype.card Y = ∑ i ∈ S, (A i i - 1) := by
    have h1 : Matrix.trace A = ∑ i : Y, A i i := rfl
    have h2 : ((Fintype.card Y : ℕ) : ℂ) = ∑ _i : Y, (1 : ℂ) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [h1, h2, ← Finset.sum_sub_distrib]
    rw [← Finset.sum_subset (Finset.subset_univ S)]
    intro i _ hiS
    rw [hS i hiS, sub_self]
  have hnorm : ‖Matrix.trace A - Fintype.card Y‖ ≤ 2 * S.card := by
    rw [hsum]
    calc ‖∑ i ∈ S, (A i i - 1)‖ ≤ ∑ i ∈ S, ‖A i i - 1‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ S, (2 : ℝ) := Finset.sum_le_sum fun i _ ↦ hdiag i
      _ = 2 * S.card := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
  have hdiv : normTrace Y A - 1
      = (Matrix.trace A - Fintype.card Y) / Fintype.card Y := by
    rw [normTrace, sub_div, div_self]
    exact_mod_cast hc.ne'
  rw [hdiv, norm_div, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right hnorm hc.le

/-- The padding instance: the padded unitary is trace-invisible at rate
exactly the relative dimension of the original block. -/
theorem norm_normTrace_padMatrix_sub_one_le (Y : FiniteModel) (m : ℕ)
    {A : Matrix Y Y ℂ} (hA : A ∈ Matrix.unitaryGroup Y ℂ)
    (hY : 0 < Fintype.card Y) :
    ‖normTrace (padModel Y m) (padMatrix Y m A) - 1‖
      ≤ 2 * Fintype.card Y / (Fintype.card Y + m) := by
  classical
  have hpad := padMatrix_mem_unitaryGroup Y m hA
  have hYpad : 0 < Fintype.card (padModel Y m) := by
    rw [card_padModel]
    exact lt_of_lt_of_le hY (Nat.le_add_right _ _)
  set S : Finset (padModel Y m) :=
    Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩ with hSdef
  have hS : ∀ p ∉ S, (padMatrix Y m A) p p = 1 := by
    intro p hp
    match p with
    | Sum.inl i =>
        exfalso
        apply hp
        rw [hSdef]
        exact Finset.mem_map_of_mem _ (Finset.mem_univ i)
    | Sum.inr j =>
        show (1 : Matrix (Fin m) (Fin m) ℂ) j j = 1
        rw [Matrix.one_apply_eq]
  have h := norm_normTrace_sub_one_le (padModel Y m) hpad hYpad S hS
  have hcardS : S.card = Fintype.card Y := by
    rw [hSdef, Finset.card_map, Finset.card_univ]
  rw [hcardS, card_padModel] at h
  exact_mod_cast h

/-! ## Amplification drives distance to the scalars, not deviation rank -/

/-- The normalized trace is exactly multiplicative under tensor powers, in
modulus. -/
theorem norm_normTrace_tensorPow (Y : FiniteModel) (A : Matrix Y Y ℂ)
    (k : ℕ) :
    ‖normTrace (tensorModel Y k) (tensorPow A k)‖ = ‖normTrace Y A‖ ^ k := by
  rw [normTrace_tensorPow, norm_pow]

/-- **The deviation-rank invariant is the wrong one.**  The unitary `i·1` has
*invertible* deviation `i·1 - 1` — full support, full rank — yet every tensor
power of it has normalized trace of modulus one, so amplification never
separates it from a scalar.  Any tradeoff along the lines of "defects small
against the rank of `u - 1` upgrades norm data to trace data" fails on this
witness; the invariant amplification drives is `1 - ‖normTrace u‖`, the
distance to the scalars.  This is the scalar-phase obstruction of
`tensorPow_phase_collapse`, recurring on the trace side. -/
theorem phase_deviation_no_amplification (Y : FiniteModel)
    (hY : 0 < Fintype.card Y) :
    IsUnit ((Complex.I • (1 : Matrix Y Y ℂ)) - 1) ∧
    ∀ k : ℕ, ‖normTrace (tensorModel Y k)
      (tensorPow (Complex.I • (1 : Matrix Y Y ℂ)) k)‖ = 1 := by
  have hne : Complex.I - 1 ≠ 0 := by
    intro hcon
    have h1 : Complex.I = 1 := sub_eq_zero.mp hcon
    have h2 := congrArg Complex.im h1
    simp at h2
  constructor
  · refine ⟨⟨(Complex.I - 1) • 1, (Complex.I - 1)⁻¹ • 1, ?_, ?_⟩, ?_⟩
    · rw [Matrix.smul_mul, Matrix.mul_smul, one_mul, smul_smul,
        mul_inv_cancel₀ hne, one_smul]
    · rw [Matrix.smul_mul, Matrix.mul_smul, one_mul, smul_smul,
        inv_mul_cancel₀ hne, one_smul]
    · show (Complex.I - 1) • (1 : Matrix Y Y ℂ) = Complex.I • 1 - 1
      rw [sub_smul, one_smul]
  · intro k
    rw [norm_normTrace_tensorPow]
    have htr : normTrace Y (Complex.I • (1 : Matrix Y Y ℂ)) = Complex.I := by
      have hc : ((Fintype.card Y : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast hY.ne'
      rw [normTrace, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul,
        mul_div_assoc, div_self hc, mul_one]
    rw [htr, Complex.norm_I, one_pow]

/-- The positive direction, stated with the correct invariant: distance to the
scalars amplifies exponentially. -/
theorem norm_normTrace_tensorPow_le (Y : FiniteModel) {A : Matrix Y Y ℂ}
    {c : ℝ} (hc : ‖normTrace Y A‖ ≤ c) (k : ℕ) :
    ‖normTrace (tensorModel Y k) (tensorPow A k)‖ ≤ c ^ k := by
  rw [norm_normTrace_tensorPow]
  exact pow_le_pow_left₀ (norm_nonneg _) hc k

end NonsoficGroupsExist
