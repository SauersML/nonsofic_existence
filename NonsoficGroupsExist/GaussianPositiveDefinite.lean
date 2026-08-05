import NonsoficGroupsExist.KazhdanFiniteModel
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Gaussian kernels are positive-definite

The Delorme direction of the Delorme–Guichardet theorem feeds the
functions `g ↦ exp (-t * ‖b g‖ ^ 2)` — for `b` the orbit map of an
affine isometric action — into the GNS construction.  This module proves
they are positive-definite in the repository's finite-quadratic-form
sense.  The route is through matrices: Gram matrices are positive
semidefinite, entrywise powers stay positive semidefinite by the Schur
product theorem (`Matrix.PosSemidef.hadamard`), entrywise exponentials
follow by summing the exponential series, and the Gaussian kernel is an
entrywise exponential of a Gram matrix conjugated by a positive
diagonal.
-/

open scoped Matrix InnerProductSpace Nat

namespace NonsoficGroupsExist
namespace GaussianKernel

variable {ι : Type*} [Fintype ι]

/-- The real quadratic form of a matrix, written as a double sum. -/
private theorem star_dotProduct_eq (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    dotProduct (star x) (A.mulVec x) =
      ∑ i, ∑ j, x i * x j * A i j := by
  simp only [star_trivial, dotProduct, Matrix.mulVec,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦
    Finset.sum_congr rfl fun j _ ↦ by ring

/-- Build positive semidefiniteness from symmetry and nonnegativity of
all real quadratic forms. -/
private theorem posSemidef_of_quadForm (A : Matrix ι ι ℝ)
    (hsymm : ∀ i j, A i j = A j i)
    (h : ∀ x : ι → ℝ, 0 ≤ ∑ i, ∑ j, x i * x j * A i j) :
    A.PosSemidef := by
  have hAH : Aᴴ = A := by
    ext i j
    rw [Matrix.conjTranspose_apply, star_trivial]
    exact hsymm j i
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hAH fun x ↦ ?_
  rw [star_dotProduct_eq]
  exact h x

/-- Extract nonnegativity of real quadratic forms from positive
semidefiniteness. -/
private theorem quadForm_nonneg_of_posSemidef {A : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (x : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, x i * x j * A i j := by
  rw [← star_dotProduct_eq]
  exact hA.dotProduct_mulVec_nonneg x

/-- Entrywise powers of a positive semidefinite real matrix are positive
semidefinite: the Schur product theorem, iterated. -/
theorem posSemidef_pow_entry {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (n : ℕ) :
    Matrix.PosSemidef (Matrix.of fun i j ↦ A i j ^ n) := by
  induction n with
  | zero =>
    refine posSemidef_of_quadForm _ (fun i j ↦ by simp) fun x ↦ ?_
    have hsum : ∑ i, ∑ j,
        x i * x j * (Matrix.of fun i j ↦ A i j ^ 0) i j =
        (∑ i, x i) * (∑ i, x i) := by
      rw [Finset.sum_mul_sum]
      simp
    rw [hsum]
    exact mul_self_nonneg _
  | succ n ih =>
    have hstep := ih.hadamard hA
    have hentry : (Matrix.of fun i j ↦ A i j ^ (n + 1)) =
        Matrix.hadamard (Matrix.of fun i j ↦ A i j ^ n) A := by
      ext i j
      simp [Matrix.hadamard_apply, pow_succ]
    rw [hentry]
    exact hstep

section Gram

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Gram matrices are positive semidefinite: the quadratic form is the
squared norm of the corresponding linear combination. -/
theorem posSemidef_gram (v : ι → H) :
    Matrix.PosSemidef (Matrix.of fun i j ↦ ⟪v i, v j⟫_ℝ) := by
  refine posSemidef_of_quadForm _
    (fun i j ↦ by simp [Matrix.of_apply, real_inner_comm]) fun x ↦ ?_
  have hsum : ∑ i, ∑ j,
      x i * x j * (Matrix.of fun i j ↦ ⟪v i, v j⟫_ℝ) i j =
      ⟪∑ i, x i • v i, ∑ j, x j • v j⟫_ℝ := by
    rw [sum_inner]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [real_inner_smul_left, real_inner_smul_right]
    simp only [Matrix.of_apply]
    ring
  rw [hsum]
  exact real_inner_self_nonneg

end Gram

/-- Entrywise exponentials of positive semidefinite real matrices are
positive semidefinite: expand the exponential series and use the
entrywise-power case termwise. -/
theorem posSemidef_exp_entry {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    Matrix.PosSemidef (Matrix.of fun i j ↦ Real.exp (A i j)) := by
  have hsymmA : ∀ i j, A i j = A j i := by
    intro i j
    have h := congrFun (congrFun hA.1 i) j
    rw [Matrix.conjTranspose_apply, star_trivial] at h
    exact h.symm
  refine posSemidef_of_quadForm _
    (fun i j ↦ by simp [Matrix.of_apply, hsymmA i j]) fun x ↦ ?_
  simp only [Matrix.of_apply]
  -- Every partial sum of the series has nonnegative quadratic form.
  have hpartial : ∀ N : ℕ, 0 ≤ ∑ i, ∑ j,
      x i * x j * ∑ n ∈ Finset.range N, A i j ^ n / n ! := by
    intro N
    have hswap : ∑ i, ∑ j,
        x i * x j * ∑ n ∈ Finset.range N, A i j ^ n / n ! =
        ∑ n ∈ Finset.range N,
          ((n ! : ℝ))⁻¹ * ∑ i, ∑ j, x i * x j * A i j ^ n := by
      calc ∑ i, ∑ j, x i * x j * ∑ n ∈ Finset.range N, A i j ^ n / n !
          = ∑ i, ∑ j, ∑ n ∈ Finset.range N,
              x i * x j * (A i j ^ n / n !) := by
            refine Finset.sum_congr rfl fun i _ ↦
              Finset.sum_congr rfl fun j _ ↦ ?_
            rw [Finset.mul_sum]
        _ = ∑ i, ∑ n ∈ Finset.range N, ∑ j,
              x i * x j * (A i j ^ n / n !) :=
            Finset.sum_congr rfl fun i _ ↦ Finset.sum_comm
        _ = ∑ n ∈ Finset.range N, ∑ i, ∑ j,
              x i * x j * (A i j ^ n / n !) := Finset.sum_comm
        _ = ∑ n ∈ Finset.range N,
              ((n ! : ℝ))⁻¹ * ∑ i, ∑ j, x i * x j * A i j ^ n := by
            refine Finset.sum_congr rfl fun n _ ↦ ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            rw [div_eq_mul_inv]
            ring
    rw [hswap]
    refine Finset.sum_nonneg fun n _ ↦ mul_nonneg
      (inv_nonneg.mpr (Nat.cast_nonneg _)) ?_
    have hq := quadForm_nonneg_of_posSemidef (posSemidef_pow_entry hA n) x
    simpa [Matrix.of_apply] using hq
  -- The quadratic forms of the partial sums converge to that of the
  -- entrywise exponential.
  have hlim : Filter.Tendsto (fun N : ℕ ↦ ∑ i, ∑ j,
      x i * x j * ∑ n ∈ Finset.range N, A i j ^ n / n !)
      Filter.atTop
      (nhds (∑ i, ∑ j, x i * x j * Real.exp (A i j))) := by
    refine tendsto_finsetSum _ fun i _ ↦ tendsto_finsetSum _ fun j _ ↦ ?_
    have hexp : HasSum (fun n : ℕ ↦ A i j ^ n / n !)
        (Real.exp (A i j)) := by
      rw [Real.exp_eq_exp_ℝ]
      exact NormedSpace.expSeries_div_hasSum_exp (A i j)
    exact hexp.tendsto_sum_nat.const_mul (x i * x j)
  exact ge_of_tendsto' hlim hpartial

section Group

variable {G : Type*} [Group G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **Gaussian kernels along a cocycle are positive-definite.**  If
`b : G → H` satisfies the orbit-map identity
`‖b (g⁻¹ * h)‖ = ‖b h - b g‖` — as the orbit map of any affine isometric
action does — then `g ↦ exp (-t * ‖b g‖ ^ 2)` is positive-definite for
every `t ≥ 0`.  This is the input Schoenberg's theorem provides to the
Delorme direction of the Delorme–Guichardet theorem.  The factorization
`exp (-t * ‖b_j - b_i‖ ^ 2) =
  exp (-t * ‖b_i‖ ^ 2) * exp (⟪√(2t) b_i, √(2t) b_j⟫) *
  exp (-t * ‖b_j‖ ^ 2)`
reduces the quadratic form to that of the entrywise exponential of a
Gram matrix at rescaled coefficients. -/
theorem isPositiveDefinite_exp_neg_norm_sq (b : G → H)
    (hb : ∀ g h : G, ‖b (g⁻¹ * h)‖ = ‖b h - b g‖) {t : ℝ} (ht : 0 ≤ t) :
    KazhdanFiniteModel.IsPositiveDefinite
      (fun g ↦ Real.exp (-t * ‖b g‖ ^ 2)) := by
  constructor
  · intro g h
    rw [hb g h, hb h g, norm_sub_rev]
  · intro F c
    classical
    have hfact : ∀ i j : G, Real.exp (-t * ‖b (i⁻¹ * j)‖ ^ 2) =
        Real.exp (-t * ‖b i‖ ^ 2) *
          Real.exp (⟪Real.sqrt (2 * t) • b i,
            Real.sqrt (2 * t) • b j⟫_ℝ) *
          Real.exp (-t * ‖b j‖ ^ 2) := by
      intro i j
      rw [hb i j, norm_sub_sq_real, real_inner_smul_left,
        real_inner_smul_right, ← Real.exp_add, ← Real.exp_add]
      congr 1
      rw [← mul_assoc, Real.mul_self_sqrt (by linarith), real_inner_comm]
      ring
    have h0 : 0 ≤ ∑ p : F, ∑ q : F,
        (c p * Real.exp (-t * ‖b p‖ ^ 2)) *
          (c q * Real.exp (-t * ‖b q‖ ^ 2)) *
          Real.exp (⟪Real.sqrt (2 * t) • b p,
            Real.sqrt (2 * t) • b q⟫_ℝ) := by
      have hq := quadForm_nonneg_of_posSemidef
        (posSemidef_exp_entry
          (posSemidef_gram fun p : F ↦ Real.sqrt (2 * t) • b p))
        (fun p : F ↦ c p * Real.exp (-t * ‖b p‖ ^ 2))
      simpa [Matrix.of_apply] using hq
    have heq : ∑ i ∈ F, ∑ j ∈ F,
        c i * c j * Real.exp (-t * ‖b (i⁻¹ * j)‖ ^ 2) =
        ∑ p : F, ∑ q : F,
          (c p * Real.exp (-t * ‖b p‖ ^ 2)) *
            (c q * Real.exp (-t * ‖b q‖ ^ 2)) *
            Real.exp (⟪Real.sqrt (2 * t) • b p,
              Real.sqrt (2 * t) • b q⟫_ℝ) := by
      rw [← Finset.sum_coe_sort F]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      rw [← Finset.sum_coe_sort F]
      refine Finset.sum_congr rfl fun q _ ↦ ?_
      rw [hfact]
      ring
    rw [heq]
    exact h0

/-- Positive-definiteness descends along surjective homomorphisms: the
finite quadratic forms of the quotient function are among those of the
pullback, via any set-theoretic section. -/
theorem isPositiveDefinite_of_comp_surjective {G' : Type*} [Group G']
    (f : G →* G') (hf : Function.Surjective f) {φ : G' → ℝ}
    (h : KazhdanFiniteModel.IsPositiveDefinite (fun g ↦ φ (f g))) :
    KazhdanFiniteModel.IsPositiveDefinite φ := by
  classical
  constructor
  · intro a b
    obtain ⟨x, rfl⟩ := hf a
    obtain ⟨y, rfl⟩ := hf b
    have hsymm := h.1 x y
    simpa [map_mul, map_inv] using hsymm
  · intro F c
    set s : G' → G := Function.surjInv hf with hs
    have hsinj : Function.Injective s := Function.injective_surjInv hf
    have hform := h.2 (F.image s) (c ∘ f)
    simp only [Function.comp_apply] at hform
    have key : ∑ a ∈ F, ∑ b ∈ F, c a * c b * φ (a⁻¹ * b) =
        ∑ i ∈ F.image s, ∑ j ∈ F.image s,
          c (f i) * c (f j) * φ (f (i⁻¹ * j)) := by
      rw [Finset.sum_image (fun x _ y _ hxy ↦ hsinj hxy)]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [Finset.sum_image (fun x _ y _ hxy ↦ hsinj hxy)]
      refine Finset.sum_congr rfl fun b _ ↦ ?_
      rw [map_mul, map_inv, Function.surjInv_eq hf a,
        Function.surjInv_eq hf b]
    rw [key]
    exact hform

end Group

end GaussianKernel
end NonsoficGroupsExist
