import NonsoficGroupsExist.KazhdanFiniteModel
import Mathlib.Topology.Algebra.LinearMapCompletion

/-!
# GNS representation of a positive-definite group function

This module uses mathlib's Moore--Aronszajn construction to turn the
positive-definite limiting correlation into a genuine complete real Hilbert
space and an orthogonal group representation.
-/

namespace NonsoficGroupsExist
namespace KazhdanGNS

open KazhdanFiniteModel
open scoped InnerProductSpace

universe u

variable {G : Type u} [Group G]

/-- The scalar-valued translation-invariant kernel associated to a real
function on a group. -/
noncomputable def scalarKernel (f : G → ℝ) :
    Matrix G G (ℝ →L[ℝ] ℝ) :=
  Matrix.of fun x y ↦
    ContinuousLinearMap.lsmul ℝ ℝ (f (y⁻¹ * x))

@[simp] theorem scalarKernel_apply (f : G → ℝ) (x y : G) (r : ℝ) :
    scalarKernel f x y r = f (y⁻¹ * x) * r := rfl

/-- Symmetry of a positive-definite function makes its scalar kernel
Hermitian. -/
theorem scalarKernel_isHermitian {f : G → ℝ} (hf : IsPositiveDefinite f) :
    (scalarKernel f).IsHermitian := by
  ext x y
  change star (ContinuousLinearMap.lsmul ℝ ℝ (f (x⁻¹ * y))) 1 =
    f (y⁻¹ * x) * 1
  rw [hf.1 y x, mul_one]
  rw [ContinuousLinearMap.star_eq_adjoint]
  refine ext_inner_right ℝ fun r ↦ ?_
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp [mul_comm]

/-- The scalar kernel of a positive-definite group function is positive
semidefinite in mathlib's operator-valued kernel sense. -/
theorem scalarKernel_posSemidef {f : G → ℝ} (hf : IsPositiveDefinite f) :
    (scalarKernel f).PosSemidef := by
  apply (RKHS.posSemidef_tfae.out 2 0).mp
  refine ⟨scalarKernel_isHermitian hf, ?_⟩
  intro v
  have hquad := hf.2 v.support v
  simpa [scalarKernel, Finsupp.sum, mul_assoc, mul_comm, mul_left_comm] using hquad

/-- A real positive-definite function, bundled only so that its proved
positivity can supply mathlib's kernel instance. -/
structure PositiveDefiniteFunction (G : Type u) [Group G] where
  toFun : G → ℝ
  isPositiveDefinite : IsPositiveDefinite toFun

instance : CoeFun (PositiveDefiniteFunction G) (fun _ ↦ G → ℝ) :=
  ⟨PositiveDefiniteFunction.toFun⟩

noncomputable instance scalarKernelFact (p : PositiveDefiniteFunction G) :
    Fact (scalarKernel p.toFun).PosSemidef :=
  ⟨scalarKernel_posSemidef p.isPositiveDefinite⟩

/-- The complete real Hilbert space produced by the Moore--Aronszajn
construction from a positive-definite group function. -/
abbrev HilbertSpace (p : PositiveDefiniteFunction G) :=
  RKHS.OfKernel (scalarKernel p.toFun)

/-- The finitely supported pre-Hilbert space whose completion is the GNS
Hilbert space. -/
abbrev PreHilbertSpace (p : PositiveDefiniteFunction G) :=
  RKHS.H₀ (scalarKernel p.toFun)

@[reducible] noncomputable def preHilbertSeminormed
    (p : PositiveDefiniteFunction G) :
    SeminormedAddCommGroup (PreHilbertSpace p) :=
  RKHS.instSeminormedAddCommGroupH₀ (K := scalarKernel p.toFun)

@[reducible] noncomputable def preHilbertInnerProduct
    (p : PositiveDefiniteFunction G) :
    InnerProductSpace ℝ (PreHilbertSpace p) :=
  RKHS.instInnerProductSpaceH₀ (K := scalarKernel p.toFun)

/-- The kernel vector indexed by a group element, explicitly realized as a
free generator in the Hilbert completion. -/
noncomputable def kernelVector (p : PositiveDefiniteFunction G) (g : G) :
    HilbertSpace p := by
  letI : SeminormedAddCommGroup (PreHilbertSpace p) :=
    preHilbertSeminormed p
  letI : InnerProductSpace ℝ (PreHilbertSpace p) :=
    preHilbertInnerProduct p
  exact UniformSpace.Completion.coe'
    (Finsupp.single (g, (1 : ℝ)) 1 : PreHilbertSpace p)

/-- The limiting correlation with its positive-definiteness proof. -/
noncomputable def limitingPositiveDefiniteFunction
    (A : SoficApproximation G) (U : ∀ n, Finset (A.model n)) :
    PositiveDefiniteFunction G where
  toFun := limitingCorrelation A U
  isPositiveDefinite := limitingCorrelation_isPositiveDefinite A U

/-- Left translation on the group coordinate of the free kernel-vector
indexing type. -/
def leftIndexEquiv (s : G) : G × ℝ ≃ G × ℝ where
  toFun x := (s * x.1, x.2)
  invFun x := (s⁻¹ * x.1, x.2)
  left_inv x := by simp
  right_inv x := by simp

/-- Left multiplication as an equivalence of the group index itself. -/
def leftGroupEquiv (s : G) : G ≃ G where
  toFun g := s * g
  invFun g := s⁻¹ * g
  left_inv g := by simp
  right_inv g := by simp

/-- Left translation on finitely supported kernel generators. -/
noncomputable def preTranslationLinearEquiv (p : PositiveDefiniteFunction G) (s : G) :
    PreHilbertSpace p ≃ₗ[ℝ] PreHilbertSpace p :=
  Finsupp.domLCongr (leftIndexEquiv s)

@[simp] theorem preTranslationLinearEquiv_single
    (p : PositiveDefiniteFunction G) (s : G) (i : G × ℝ) (c : ℝ) :
    preTranslationLinearEquiv p s (Finsupp.single i c) =
      Finsupp.single (leftIndexEquiv s i) c := by
  simp [preTranslationLinearEquiv]

/-- Explicit inner product of two free kernel generators. -/
theorem inner_single (p : PositiveDefiniteFunction G)
    (i j : G × ℝ) (c d : ℝ) :
    letI : SeminormedAddCommGroup (PreHilbertSpace p) :=
      preHilbertSeminormed p
    letI : InnerProductSpace ℝ (PreHilbertSpace p) :=
      preHilbertInnerProduct p
    inner ℝ (Finsupp.single i c : PreHilbertSpace p)
        (Finsupp.single j d : PreHilbertSpace p) =
      c * d * (p (i.1⁻¹ * j.1) * i.2 * j.2) := by
  change (Finsupp.single i c).sum (fun yu z ↦
    (Finsupp.single j d).sum (fun xv w ↦
      star z * w * inner ℝ (scalarKernel p.toFun xv.1 yu.1 yu.2) xv.2)) = _
  simp [scalarKernel, mul_assoc, mul_comm, mul_left_comm]

/-- Inner products of kernel vectors recover the original group
coefficient. -/
theorem inner_kernelVector (p : PositiveDefiniteFunction G) (g h : G) :
    inner ℝ (kernelVector p g) (kernelVector p h) = p (g⁻¹ * h) := by
  letI : SeminormedAddCommGroup (PreHilbertSpace p) :=
    preHilbertSeminormed p
  letI : InnerProductSpace ℝ (PreHilbertSpace p) :=
    preHilbertInnerProduct p
  change inner ℝ
    (UniformSpace.Completion.coe'
      (Finsupp.single (g, (1 : ℝ)) 1 : PreHilbertSpace p))
    (UniformSpace.Completion.coe'
      (Finsupp.single (h, (1 : ℝ)) 1 : PreHilbertSpace p)) = _
  rw [UniformSpace.Completion.inner_coe, inner_single]
  simp

/-- Left translation preserves the pre-Hilbert inner product. -/
theorem inner_preTranslationLinearEquiv (p : PositiveDefiniteFunction G)
    (s : G) (f g : PreHilbertSpace p) :
    letI : SeminormedAddCommGroup (PreHilbertSpace p) :=
      preHilbertSeminormed p
    letI : InnerProductSpace ℝ (PreHilbertSpace p) :=
      preHilbertInnerProduct p
    inner ℝ (preTranslationLinearEquiv p s f)
        (preTranslationLinearEquiv p s g) = inner ℝ f g := by
  letI : SeminormedAddCommGroup (PreHilbertSpace p) :=
    preHilbertSeminormed p
  letI : InnerProductSpace ℝ (PreHilbertSpace p) :=
    preHilbertInnerProduct p
  let L := preTranslationLinearEquiv p s
  have hsingle (i : G × ℝ) (c : ℝ) (g : PreHilbertSpace p) :
      inner ℝ (L (Finsupp.single i c)) (L g) =
        inner ℝ (Finsupp.single i c) g := by
    induction g using Finsupp.induction with
    | zero => simp
    | single_add j d g _ _ ih =>
        rw [map_add, inner_add_right, inner_add_right, ih]
        congr 1
        rw [show L (Finsupp.single i c) =
            Finsupp.single (leftIndexEquiv s i) c by
              simp [L, preTranslationLinearEquiv],
          show L (Finsupp.single j d) =
            Finsupp.single (leftIndexEquiv s j) d by
              simp [L, preTranslationLinearEquiv],
          inner_single, inner_single]
        simp [leftIndexEquiv]
  induction f using Finsupp.induction with
  | zero => simp
  | single_add i c f _ _ ih =>
      rw [map_add, inner_add_left, inner_add_left, ih, hsingle]

/-- Left translation as a linear isometric equivalence of the pre-Hilbert
space. -/
noncomputable def preTranslationLinearIsometryEquiv
    (p : PositiveDefiniteFunction G) (s : G) :
    letI : SeminormedAddCommGroup (PreHilbertSpace p) :=
      preHilbertSeminormed p
    letI : InnerProductSpace ℝ (PreHilbertSpace p) :=
      preHilbertInnerProduct p
    PreHilbertSpace p ≃ₗᵢ[ℝ] PreHilbertSpace p := by
  letI : SeminormedAddCommGroup (PreHilbertSpace p) :=
    preHilbertSeminormed p
  letI : InnerProductSpace ℝ (PreHilbertSpace p) :=
    preHilbertInnerProduct p
  refine
    { preTranslationLinearEquiv p s with
      norm_map' := fun f ↦ ?_ }
  have hinner := inner_preTranslationLinearEquiv p s f f
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hinner
  nlinarith [norm_nonneg (preTranslationLinearEquiv p s f), norm_nonneg f]

@[simp] theorem preTranslationLinearEquiv_inv_apply
    (p : PositiveDefiniteFunction G) (s : G) (f : PreHilbertSpace p) :
    preTranslationLinearEquiv p s⁻¹ (preTranslationLinearEquiv p s f) = f := by
  ext i
  simp [preTranslationLinearEquiv, leftIndexEquiv]

@[simp] theorem preTranslationLinearEquiv_apply_inv
    (p : PositiveDefiniteFunction G) (s : G) (f : PreHilbertSpace p) :
    preTranslationLinearEquiv p s (preTranslationLinearEquiv p s⁻¹ f) = f := by
  ext i
  simp [preTranslationLinearEquiv, leftIndexEquiv]

/-- Left translation as a continuous linear map on the seminormed
pre-Hilbert space. -/
noncomputable def preTranslationContinuousLinearMap
    (p : PositiveDefiniteFunction G) (s : G) :
    letI : SeminormedAddCommGroup (PreHilbertSpace p) :=
      preHilbertSeminormed p
    letI : InnerProductSpace ℝ (PreHilbertSpace p) :=
      preHilbertInnerProduct p
    PreHilbertSpace p →L[ℝ] PreHilbertSpace p := by
  letI : SeminormedAddCommGroup (PreHilbertSpace p) :=
    preHilbertSeminormed p
  letI : InnerProductSpace ℝ (PreHilbertSpace p) :=
    preHilbertInnerProduct p
  exact (preTranslationLinearEquiv p s).toLinearMap.mkContinuous 1 fun f ↦ by
    change ‖preTranslationLinearEquiv p s f‖ ≤ 1 * ‖f‖
    have hn := (preTranslationLinearIsometryEquiv p s).norm_map f
    change ‖preTranslationLinearEquiv p s f‖ = ‖f‖ at hn
    rw [hn]
    simp

/-- Left translation extended continuously to the completed RKHS. -/
noncomputable def translationOperator (p : PositiveDefiniteFunction G) (s : G) :
    HilbertSpace p ≃ₗᵢ[ℝ] HilbertSpace p := by
  letI : SeminormedAddCommGroup (PreHilbertSpace p) :=
    preHilbertSeminormed p
  letI : InnerProductSpace ℝ (PreHilbertSpace p) :=
    preHilbertInnerProduct p
  let L := preTranslationContinuousLinearMap p s
  let Linv := preTranslationContinuousLinearMap p s⁻¹
  let T : HilbertSpace p →L[ℝ] HilbertSpace p :=
    L.completion
  let Tinv : HilbertSpace p →L[ℝ] HilbertSpace p :=
    Linv.completion
  refine
    { toFun := T
      invFun := Tinv
      left_inv := fun x ↦ ?_
      right_inv := fun x ↦ ?_
      map_add' := T.map_add
      map_smul' := T.map_smul
      norm_map' := fun x ↦ ?_ }
  · induction x using UniformSpace.Completion.induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih x => simp [T, Tinv, L, Linv, preTranslationContinuousLinearMap]
  · induction x using UniformSpace.Completion.induction_on with
    | hp => apply isClosed_eq <;> fun_prop
    | ih x => simp [T, Tinv, L, Linv, preTranslationContinuousLinearMap]
  · induction x using UniformSpace.Completion.induction_on with
    | hp =>
        change IsClosed {x | ‖T x‖ = ‖x‖}
        exact isClosed_eq (continuous_norm.comp T.continuous) continuous_norm
    | ih x =>
        have hn := (preTranslationLinearIsometryEquiv p s).norm_map x
        change ‖preTranslationLinearEquiv p s x‖ = ‖x‖ at hn
        simpa [T, L, preTranslationContinuousLinearMap] using hn

@[simp] theorem preTranslationLinearEquiv_one
    (p : PositiveDefiniteFunction G) (f : PreHilbertSpace p) :
    preTranslationLinearEquiv p 1 f = f := by
  ext i
  simp [preTranslationLinearEquiv, leftIndexEquiv]

@[simp] theorem preTranslationLinearEquiv_mul
    (p : PositiveDefiniteFunction G) (s t : G) (f : PreHilbertSpace p) :
    preTranslationLinearEquiv p (s * t) f =
      preTranslationLinearEquiv p s (preTranslationLinearEquiv p t f) := by
  ext i
  simp [preTranslationLinearEquiv, leftIndexEquiv, mul_assoc]

/-- The completed translation agrees with the explicit translation on the
dense finitely supported subspace. -/
@[simp] theorem translationOperator_coe
    (p : PositiveDefiniteFunction G) (s : G) (f : PreHilbertSpace p) :
    translationOperator p s (UniformSpace.Completion.coe' f) =
      UniformSpace.Completion.coe' (preTranslationLinearEquiv p s f) := by
  change (preTranslationContinuousLinearMap p s).completion
      (UniformSpace.Completion.coe' f) = _
  simp [preTranslationContinuousLinearMap]

@[simp] theorem translationOperator_one (p : PositiveDefiniteFunction G) :
    translationOperator p 1 = 1 := by
  apply LinearIsometryEquiv.ext
  intro x
  induction x using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih f => simp

@[simp] theorem translationOperator_mul (p : PositiveDefiniteFunction G) (s t : G) :
    translationOperator p (s * t) =
      translationOperator p s * translationOperator p t := by
  apply LinearIsometryEquiv.ext
  intro x
  induction x using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih f => simp

/-- The left-translation representation generated by a positive-definite
function. -/
noncomputable def representation (p : PositiveDefiniteFunction G) :
    G →* (HilbertSpace p ≃ₗᵢ[ℝ] HilbertSpace p) where
  toFun := translationOperator p
  map_one' := translationOperator_one p
  map_mul' := translationOperator_mul p

@[simp] theorem representation_kernelVector
    (p : PositiveDefiniteFunction G) (s g : G) :
    representation p s (kernelVector p g) = kernelVector p (s * g) := by
  letI : SeminormedAddCommGroup (PreHilbertSpace p) :=
    preHilbertSeminormed p
  letI : InnerProductSpace ℝ (PreHilbertSpace p) :=
    preHilbertInnerProduct p
  change translationOperator p s
    (UniformSpace.Completion.coe'
      (Finsupp.single (g, (1 : ℝ)) 1 : PreHilbertSpace p)) =
    UniformSpace.Completion.coe'
      (Finsupp.single (s * g, (1 : ℝ)) 1 : PreHilbertSpace p)
  rw [translationOperator_coe, preTranslationLinearEquiv_single]
  change UniformSpace.Completion.coe'
    (Finsupp.single (s * g, (1 : ℝ)) 1 : PreHilbertSpace p) = _
  rfl

/-- The linear combination of cyclic kernel vectors encoded by a finitely
supported coefficient function on the group. -/
noncomputable def finsuppCombination (p : PositiveDefiniteFunction G) :
    (G →₀ ℝ) →ₗ[ℝ] HilbertSpace p :=
  Finsupp.linearCombination ℝ (kernelVector p)

/-- Left translation of a finitely supported coefficient function. -/
noncomputable def translateCoefficients (s : G) :
    (G →₀ ℝ) ≃ₗ[ℝ] (G →₀ ℝ) :=
  Finsupp.domLCongr (leftGroupEquiv s)

@[simp] theorem translateCoefficients_single (s g : G) (r : ℝ) :
    translateCoefficients s (Finsupp.single g r) =
      Finsupp.single (s * g) r := by
  simp [translateCoefficients, leftGroupEquiv]

/-- The GNS representation translates every finitely supported cyclic
combination by left multiplication of its indices. -/
theorem representation_finsuppCombination
    (p : PositiveDefiniteFunction G) (s : G) (c : G →₀ ℝ) :
    representation p s (finsuppCombination p c) =
      finsuppCombination p (translateCoefficients s c) := by
  induction c using Finsupp.induction with
  | zero => simp
  | single_add g r c _ _ ih =>
      rw [map_add, map_add, ih]
      simp [finsuppCombination, representation_kernelVector]

/-- The finitely supported probability measure obtained by taking `k`
uniform steps in the averaging set. -/
noncomputable def averagingCoefficients (S : Finset G) : ℕ → G →₀ ℝ
  | 0 => Finsupp.single 1 1
  | k + 1 => (S.card : ℝ)⁻¹ •
      ∑ s ∈ S, translateCoefficients s (averagingCoefficients S k)

/-- Applying one GNS orbit average advances the averaging coefficients by
one step. -/
theorem finsuppCombination_averagingCoefficients_succ
    (p : PositiveDefiniteFunction G) (S : Finset G) (k : ℕ) :
    finsuppCombination p (averagingCoefficients S (k + 1)) =
      IsKazhdanPair.orbitAverage S (representation p)
        (finsuppCombination p (averagingCoefficients S k)) := by
  classical
  rw [averagingCoefficients]
  rw [IsKazhdanPair.orbitAverage]
  simp only [map_smul, map_sum]
  simp_rw [representation_finsuppCombination]

/-- The cyclic coefficient of the GNS representation is exactly the
positive-definite function from which it was built. -/
@[simp] theorem representation_cyclicCoefficient
    (p : PositiveDefiniteFunction G) (g : G) :
    inner ℝ (kernelVector p 1) (representation p g (kernelVector p 1)) =
      p g := by
  rw [representation_kernelVector, inner_kernelVector]
  simp

/-- A finite linear combination of cyclic translates in the GNS space. -/
noncomputable def finiteCombination (p : PositiveDefiniteFunction G)
    (F : Finset G) (c : G → ℝ) : HilbertSpace p :=
  ∑ g ∈ F, c g • kernelVector p g

/-- The Gram formula for two finite linear combinations of cyclic
translates. -/
theorem inner_finiteCombination (p : PositiveDefiniteFunction G)
    (F K : Finset G) (c d : G → ℝ) :
    inner ℝ (finiteCombination p F c) (finiteCombination p K d) =
      ∑ g ∈ F, ∑ h ∈ K, c g * d h * p (g⁻¹ * h) := by
  classical
  rw [finiteCombination, finiteCombination]
  simp_rw [sum_inner, inner_sum, real_inner_smul_left,
    real_inner_smul_right, inner_kernelVector]
  simp [mul_assoc]

/-- A finite linear combination whose index type may retain repeated group
words.  This is convenient for powers of an averaging operator. -/
noncomputable def indexedCombination {I : Type*}
    (p : PositiveDefiniteFunction G) (F : Finset I)
    (a : I → G) (c : I → ℝ) : HilbertSpace p :=
  ∑ i ∈ F, c i • kernelVector p (a i)

/-- Squared norms of indexed cyclic combinations are their finite Gram
quadratic forms. -/
theorem norm_indexedCombination_sq {I : Type*}
    (p : PositiveDefiniteFunction G) (F : Finset I)
    (a : I → G) (c : I → ℝ) :
    ‖indexedCombination p F a c‖ ^ 2 =
      ∑ i ∈ F, ∑ j ∈ F, c i * c j * p ((a i)⁻¹ * a j) := by
  classical
  rw [← real_inner_self_eq_norm_sq]
  simp_rw [indexedCombination, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, inner_kernelVector]
  simp [mul_assoc]

/-- A `Finsupp` cyclic combination is its support-indexed finite
combination. -/
theorem finsuppCombination_eq_indexed (p : PositiveDefiniteFunction G)
    (c : G →₀ ℝ) :
    finsuppCombination p c = indexedCombination p c.support id c := by
  classical
  simp [finsuppCombination, indexedCombination,
    Finsupp.linearCombination_apply, Finsupp.sum]

/-- Iterated orbit averaging of the cyclic vector is represented by the
explicit finitely supported convolution coefficients. -/
theorem iterate_orbitAverage_kernelVector
    (p : PositiveDefiniteFunction G) (S : Finset G) (k : ℕ) :
    let A := IsKazhdanPair.orbitAverage S (representation p)
    (A^[k]) (kernelVector p 1) =
      finsuppCombination p (averagingCoefficients S k) := by
  let A := IsKazhdanPair.orbitAverage S (representation p)
  induction k with
  | zero =>
      simp [averagingCoefficients, finsuppCombination]
  | succ k ih =>
      dsimp only
      rw [Function.iterate_succ_apply', ih]
      exact (finsuppCombination_averagingCoefficients_succ p S k).symm

/-- Coefficients of the displacement between two successive averaging
steps. -/
noncomputable def averagingDisplacementCoefficients
    (S : Finset G) (k : ℕ) : G →₀ ℝ :=
  averagingCoefficients S (k + 1) - averagingCoefficients S k

/-- Successive GNS averaging displacement as one explicit cyclic
combination. -/
theorem iterate_orbitAverage_succ_sub_eq_finsuppCombination
    (p : PositiveDefiniteFunction G) (S : Finset G) (k : ℕ) :
    let A := IsKazhdanPair.orbitAverage S (representation p)
    (A^[k + 1]) (kernelVector p 1) -
        (A^[k]) (kernelVector p 1) =
      finsuppCombination p (averagingDisplacementCoefficients S k) := by
  dsimp only
  have hk1 := iterate_orbitAverage_kernelVector p S (k + 1)
  have hk := iterate_orbitAverage_kernelVector p S k
  dsimp only at hk1 hk
  rw [hk1, hk]
  simp [averagingDisplacementCoefficients]

/-- The hyperreal Gram quadratic form associated to a fixed finite cyclic
combination across a sofic approximation. -/
noncomputable def combinationNormSqHyperreal {I : Type*}
    (A : SoficApproximation G) (U : ∀ n, Finset (A.model n))
    (F : Finset I) (a : I → G) (c : I → ℝ) : Hyperreal :=
  ∑ i ∈ F, ∑ j ∈ F,
    ((c i * c j : ℝ) : Hyperreal) * gramCorrelationHyperreal A U (a i) (a j)

/-- The hyperreal Gram form is represented by the sequence of normalized
finite-model squared norms. -/
theorem combinationNormSqHyperreal_eq_ofSeq {I : Type*}
    (A : SoficApproximation G) (U : ∀ n, Finset (A.model n))
    (F : Finset I) (a : I → G) (c : I → ℝ) :
    combinationNormSqHyperreal A U F a c = Hyperreal.ofSeq (fun n ↦
      normalizedCombinationNormSq F c (A.model n) (A.map n) (U n) a) := by
  classical
  change (∑ i ∈ F, ∑ j ∈ F,
      ofSeqRingHom (fun _ ↦ c i * c j) *
        ofSeqRingHom (fun n ↦ normalizedGramCorrelation
          (A.model n) (A.map n) (U n) (a i) (a j))) =
    ofSeqRingHom (fun n ↦ normalizedCombinationNormSq
      F c (A.model n) (A.map n) (U n) a)
  rw [show (fun n ↦ normalizedCombinationNormSq
      F c (A.model n) (A.map n) (U n) a) =
      ∑ i ∈ F, ∑ j ∈ F, fun n ↦ c i * c j *
        normalizedGramCorrelation
          (A.model n) (A.map n) (U n) (a i) (a j) by
        funext n
        rw [normalizedCombinationNormSq_eq_gram]
        simp]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← map_mul]
  congr 1

/-- The hyperreal normalized squared norm is finite. -/
theorem combinationNormSqHyperreal_finite {I : Type*}
    (A : SoficApproximation G) (U : ∀ n, Finset (A.model n))
    (F : Finset I) (a : I → G) (c : I → ℝ) :
    0 ≤ ArchimedeanClass.mk (combinationNormSqHyperreal A U F a c) := by
  apply hyperreal_finset_sum_finite F
  intro i hi
  apply hyperreal_finset_sum_finite F
  intro j hj
  exact hyperreal_mul_finite (hyperreal_coe_finite (c i * c j))
    (gramCorrelationHyperreal_finite A U (a i) (a j))

/-- Standard part of every fixed normalized finite Gram norm is the squared
norm of the corresponding vector in the limiting GNS representation. -/
theorem stdPart_combinationNormSqHyperreal {I : Type*}
    (A : SoficApproximation G) (U : ∀ n, Finset (A.model n))
    (F : Finset I) (a : I → G) (c : I → ℝ) :
    ArchimedeanClass.stdPart (combinationNormSqHyperreal A U F a c) =
      ‖indexedCombination (limitingPositiveDefiniteFunction A U) F a c‖ ^ 2 := by
  classical
  let term : I → I → Hyperreal := fun i j ↦
    ((c i * c j : ℝ) : Hyperreal) *
      gramCorrelationHyperreal A U (a i) (a j)
  have hterm (i j : I) : 0 ≤ ArchimedeanClass.mk (term i j) :=
    hyperreal_mul_finite (hyperreal_coe_finite (c i * c j))
      (gramCorrelationHyperreal_finite A U (a i) (a j))
  have hinner (i : I) :
      0 ≤ ArchimedeanClass.mk (∑ j ∈ F, term i j) :=
    hyperreal_finset_sum_finite F (term i) fun j hj ↦ hterm i j
  rw [norm_indexedCombination_sq]
  change ArchimedeanClass.stdPart
      (∑ i ∈ F, ∑ j ∈ F, term i j) = _
  calc
    ArchimedeanClass.stdPart (∑ i ∈ F, ∑ j ∈ F, term i j) =
        ∑ i ∈ F, ArchimedeanClass.stdPart (∑ j ∈ F, term i j) := by
      exact stdPart_finset_sum F (fun i ↦ ∑ j ∈ F, term i j)
        (fun i hi ↦ hinner i)
    _ = ∑ i ∈ F, ∑ j ∈ F,
        ArchimedeanClass.stdPart (term i j) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact stdPart_finset_sum F (term i) fun j hj ↦ hterm i j
    _ = ∑ i ∈ F, ∑ j ∈ F,
        c i * c j * limitingCorrelation A U ((a i)⁻¹ * a j) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [ArchimedeanClass.stdPart_mul
        (hyperreal_coe_finite (c i * c j))
        (gramCorrelationHyperreal_finite A U (a i) (a j)),
        Hyperreal.stdPart_coe,
        ← limitingCorrelation_inv_mul_eq_stdPart_gram A U (a i) (a j)]

/-- Standard part of the normalized finite-model displacement norm equals
the squared norm of the corresponding successive GNS averages. -/
theorem stdPart_averagingDisplacementNormSq
    (A : SoficApproximation G) (U : ∀ n, Finset (A.model n))
    (S : Finset G) (k : ℕ) :
    let c := averagingDisplacementCoefficients S k
    ArchimedeanClass.stdPart
        (combinationNormSqHyperreal A U c.support id c) =
      ‖((IsKazhdanPair.orbitAverage S
          (representation (limitingPositiveDefiniteFunction A U)))^[k + 1])
          (kernelVector (limitingPositiveDefiniteFunction A U) 1) -
        ((IsKazhdanPair.orbitAverage S
          (representation (limitingPositiveDefiniteFunction A U)))^[k])
          (kernelVector (limitingPositiveDefiniteFunction A U) 1)‖ ^ 2 := by
  let p := limitingPositiveDefiniteFunction A U
  let c := averagingDisplacementCoefficients S k
  dsimp only
  rw [stdPart_combinationNormSqHyperreal]
  rw [← finsuppCombination_eq_indexed]
  have h := iterate_orbitAverage_succ_sub_eq_finsuppCombination p S k
  dsimp only at h ⊢
  rw [h]

/-- The standard parts of normalized finite-model displacement norms obey
the squared iterated Kazhdan contraction. -/
theorem stdPart_averagingDisplacementNormSq_le
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, u} G Q ε)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S) (hεone : ε ≤ 1)
    (A : SoficApproximation G) (U : ∀ n, Finset (A.model n)) (k : ℕ) :
    let ck := averagingDisplacementCoefficients S k
    let c0 := averagingDisplacementCoefficients S 0
    ArchimedeanClass.stdPart
        (combinationNormSqHyperreal A U ck.support id ck) ≤
      (1 - ε ^ 2 / (4 * S.card)) ^ (2 * k) *
        ArchimedeanClass.stdPart
          (combinationNormSqHyperreal A U c0.support id c0) := by
  let p := limitingPositiveDefiniteFunction A U
  let Av := IsKazhdanPair.orbitAverage S (representation p)
  let factor : ℝ := 1 - ε ^ 2 / (4 * S.card)
  have hnorm := KazhdanOrthogonal.norm_iterate_orbitAverage_succ_sub_le
    hQ S hQS hone hεone (representation p) (kernelVector p 1) k
  dsimp only at hnorm
  have hcardNat : 0 < S.card := Finset.card_pos.mpr ⟨1, hone⟩
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hcardNat
  have hεsq : ε ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg ε, hQ.1, hεone]
  have hden : (0 : ℝ) < 4 * S.card := mul_pos (by norm_num) hcard
  have hcardOne : (1 : ℝ) ≤ S.card := by exact_mod_cast hcardNat
  have hdenOne : (1 : ℝ) ≤ 4 * S.card := by nlinarith
  have hfrac : ε ^ 2 / (4 * S.card) ≤ 1 := by
    rw [div_le_one hden]
    exact hεsq.trans hdenOne
  have hfactor : 0 ≤ factor := by
    dsimp [factor]
    linarith
  have hsq :
      ‖(Av^[k + 1]) (kernelVector p 1) -
          (Av^[k]) (kernelVector p 1)‖ ^ 2 ≤
        factor ^ (2 * k) *
          ‖Av (kernelVector p 1) - kernelVector p 1‖ ^ 2 := by
    have hleft : 0 ≤ ‖(Av^[k + 1]) (kernelVector p 1) -
        (Av^[k]) (kernelVector p 1)‖ := norm_nonneg _
    have hright : 0 ≤ factor ^ k *
        ‖Av (kernelVector p 1) - kernelVector p 1‖ := by
      exact mul_nonneg (pow_nonneg hfactor k) (norm_nonneg _)
    have hsquare := (sq_le_sq₀ hleft hright).2 hnorm
    calc
      ‖(Av^[k + 1]) (kernelVector p 1) -
          (Av^[k]) (kernelVector p 1)‖ ^ 2 ≤
          (factor ^ k *
            ‖Av (kernelVector p 1) - kernelVector p 1‖) ^ 2 := hsquare
      _ = factor ^ (2 * k) *
          ‖Av (kernelVector p 1) - kernelVector p 1‖ ^ 2 := by ring
  dsimp only
  rw [stdPart_averagingDisplacementNormSq,
    stdPart_averagingDisplacementNormSq]
  simpa [Av, p] using hsq

/-- The normalized squared norm of the exact group-word displacement in one
finite permutation model. -/
noncomputable def finiteAveragingDisplacementNormSq
    (A : SoficApproximation G) (n : ℕ) (U : Finset (A.model n))
    (S : Finset G) (k : ℕ) : ℝ :=
  let c := averagingDisplacementCoefficients S k
  normalizedCombinationNormSq c.support c
    (A.model n) (A.map n) U id

/-- A finitely supported linear combination of translated centered
indicators in one finite model. -/
noncomputable def finiteFinsuppCombination
    (M : FiniteModel) (τ : G → Equiv.Perm M) (U : Finset M) :
    (G →₀ ℝ) →ₗ[ℝ] EuclideanSpace ℝ M :=
  Finsupp.linearCombination ℝ fun g ↦
    permutationOperator (τ g) (centeredIndicator U)

omit [Group G] in
/-- The finite `Finsupp` combination is its support-indexed sum. -/
theorem finiteFinsuppCombination_eq_sum
    (M : FiniteModel) (τ : G → Equiv.Perm M) (U : Finset M)
    (c : G →₀ ℝ) :
    finiteFinsuppCombination M τ U c =
      ∑ g ∈ c.support,
        c g • permutationOperator (τ g) (centeredIndicator U) := by
  classical
  simp [finiteFinsuppCombination, Finsupp.linearCombination_apply, Finsupp.sum]

/-- Translate a finite-model combination using the permutation assigned to
the exact product `s * g`. -/
noncomputable def finiteExactTranslation
    (M : FiniteModel) (τ : G → Equiv.Perm M) (U : Finset M)
    (s : G) (c : G →₀ ℝ) : EuclideanSpace ℝ M :=
  finiteFinsuppCombination M τ U (translateCoefficients s c)

/-- Translate the same combination by composing the two assigned
permutations.  Approximate multiplicativity will compare this with
`finiteExactTranslation`. -/
noncomputable def finiteComposedTranslation
    (M : FiniteModel) (τ : G → Equiv.Perm M) (U : Finset M)
    (s : G) (c : G →₀ ℝ) : EuclideanSpace ℝ M :=
  Finsupp.linearCombination ℝ (fun g ↦
    permutationOperator (τ s * τ g) (centeredIndicator U)) c

/-- Exact translation expanded over the original coefficient support. -/
theorem finiteExactTranslation_eq_sum
    (M : FiniteModel) (τ : G → Equiv.Perm M) (U : Finset M)
    (s : G) (c : G →₀ ℝ) :
    finiteExactTranslation M τ U s c =
      Finsupp.linearCombination ℝ (fun g ↦
        permutationOperator (τ (s * g)) (centeredIndicator U)) c := by
  induction c using Finsupp.induction with
  | zero => simp [finiteExactTranslation]
  | single_add g r c _ _ ih =>
      rw [show finiteExactTranslation M τ U s (Finsupp.single g r + c) =
          finiteExactTranslation M τ U s (Finsupp.single g r) +
            finiteExactTranslation M τ U s c by
            simp [finiteExactTranslation],
        map_add, ih]
      simp [finiteExactTranslation, finiteFinsuppCombination]

omit [Group G] in
/-- Composed translation is actual application of the assigned permutation
to the finite combination. -/
theorem finiteComposedTranslation_eq_apply
    (M : FiniteModel) (τ : G → Equiv.Perm M) (U : Finset M)
    (s : G) (c : G →₀ ℝ) :
    finiteComposedTranslation M τ U s c =
      permutationOperator (τ s) (finiteFinsuppCombination M τ U c) := by
  induction c using Finsupp.induction with
  | zero => simp [finiteComposedTranslation]
  | single_add g r c _ _ ih =>
      rw [show finiteComposedTranslation M τ U s (Finsupp.single g r + c) =
          finiteComposedTranslation M τ U s (Finsupp.single g r) +
            finiteComposedTranslation M τ U s c by
            simp [finiteComposedTranslation],
        map_add, ih]
      simp [finiteComposedTranslation, finiteFinsuppCombination]

/-- The genuine Markov operator of one finite permutation model.  Unlike the
exact-word combinations above, this operator composes the permutations that
actually occur in the model. -/
noncomputable def finiteModelAverage
    (M : FiniteModel) (τ : G → Equiv.Perm M) (S : Finset G)
    (x : EuclideanSpace ℝ M) : EuclideanSpace ℝ M :=
  (S.card : ℝ)⁻¹ • ∑ s ∈ S, permutationOperator (τ s) x

omit [Group G] in
/-- The finite-model Markov operator is linear on differences. -/
theorem finiteModelAverage_sub
    (M : FiniteModel) (τ : G → Equiv.Perm M) (S : Finset G)
    (x y : EuclideanSpace ℝ M) :
    finiteModelAverage M τ S (x - y) =
      finiteModelAverage M τ S x - finiteModelAverage M τ S y := by
  simp [finiteModelAverage, Finset.sum_sub_distrib, smul_sub]

omit [Group G] in
/-- Averaging a nonempty finite family of orthogonal permutation operators is
norm nonincreasing. -/
theorem norm_finiteModelAverage_le
    (M : FiniteModel) (τ : G → Equiv.Perm M) (S : Finset G)
    (hS : S.Nonempty) (x : EuclideanSpace ℝ M) :
    ‖finiteModelAverage M τ S x‖ ≤ ‖x‖ := by
  have hcardNat : 0 < S.card := Finset.card_pos.mpr hS
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hcardNat
  calc
    ‖finiteModelAverage M τ S x‖ =
        (S.card : ℝ)⁻¹ * ‖∑ s ∈ S, permutationOperator (τ s) x‖ := by
      rw [finiteModelAverage, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hcard)]
    _ ≤ (S.card : ℝ)⁻¹ *
        ∑ s ∈ S, ‖permutationOperator (τ s) x‖ := by
      gcongr
      exact norm_sum_le _ _
    _ = ‖x‖ := by
      simp [hcard.ne']

omit [Group G] in
/-- A Cauchy--Schwarz bound for a finite average of error vectors, normalized
by the size of the ambient finite model. -/
theorem normalized_norm_average_le {I : Type*}
    (M : FiniteModel) (S : Finset I) (hS : S.Nonempty)
    (e : I → EuclideanSpace ℝ M) (δ : ℝ)
    (hcard : (0 : ℝ) < Fintype.card M)
    (he : ∀ i ∈ S, ‖e i‖ ^ 2 / Fintype.card M ≤ δ) :
    ‖(S.card : ℝ)⁻¹ • ∑ i ∈ S, e i‖ ^ 2 /
        Fintype.card M ≤ δ := by
  have hScardNat : 0 < S.card := Finset.card_pos.mpr hS
  have hScard : (0 : ℝ) < S.card := by exact_mod_cast hScardNat
  have he' (i : I) (hi : i ∈ S) :
      ‖e i‖ ^ 2 ≤ δ * Fintype.card M :=
    (div_le_iff₀ hcard).mp (he i hi)
  have hsumSq :
      ∑ i ∈ S, ‖e i‖ ^ 2 ≤
        (S.card : ℝ) * (δ * Fintype.card M) := by
    calc
      ∑ i ∈ S, ‖e i‖ ^ 2 ≤
          ∑ i ∈ S, δ * Fintype.card M :=
        Finset.sum_le_sum fun i hi ↦ he' i hi
      _ = (S.card : ℝ) * (δ * Fintype.card M) := by simp
  have hcauchy :
      (∑ i ∈ S, ‖e i‖) ^ 2 ≤
        (S.card : ℝ) * ∑ i ∈ S, ‖e i‖ ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq S
      (fun _ ↦ (1 : ℝ)) (fun i ↦ ‖e i‖)
  have htriangle :
      ‖(S.card : ℝ)⁻¹ • ∑ i ∈ S, e i‖ ≤
        (S.card : ℝ)⁻¹ * ∑ i ∈ S, ‖e i‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hScard)]
    gcongr
    exact norm_sum_le _ _
  have hsumNonneg : 0 ≤ ∑ i ∈ S, ‖e i‖ :=
    Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hright : 0 ≤ (S.card : ℝ)⁻¹ * ∑ i ∈ S, ‖e i‖ :=
    mul_nonneg (inv_nonneg.mpr hScard.le) hsumNonneg
  have htriangleSq := (sq_le_sq₀ (norm_nonneg _) hright).2 htriangle
  calc
    ‖(S.card : ℝ)⁻¹ • ∑ i ∈ S, e i‖ ^ 2 /
        Fintype.card M ≤
      ((S.card : ℝ)⁻¹ * ∑ i ∈ S, ‖e i‖) ^ 2 /
        Fintype.card M :=
      div_le_div_of_nonneg_right htriangleSq hcard.le
    _ ≤ ((S.card : ℝ)⁻¹ ^ 2 *
        ((S.card : ℝ) * ∑ i ∈ S, ‖e i‖ ^ 2)) /
          Fintype.card M := by
      gcongr
      nlinarith [hcauchy]
    _ ≤ ((S.card : ℝ)⁻¹ ^ 2 *
        ((S.card : ℝ) *
          ((S.card : ℝ) * (δ * Fintype.card M)))) /
            Fintype.card M := by
      gcongr
    _ = δ := by field_simp

/-- The exact group-word combination at the next time is the average of the
exact left translations of the current combination. -/
theorem finiteFinsuppCombination_averagingCoefficients_succ
    (M : FiniteModel) (τ : G → Equiv.Perm M) (U : Finset M)
    (S : Finset G) (k : ℕ) :
    finiteFinsuppCombination M τ U (averagingCoefficients S (k + 1)) =
      (S.card : ℝ)⁻¹ • ∑ s ∈ S,
        finiteExactTranslation M τ U s (averagingCoefficients S k) := by
  rw [averagingCoefficients]
  simp only [map_smul, map_sum]
  rfl

omit [Group G] in
/-- Applying the genuine finite Markov operator to an exact-word combination
is the average of its composed translations. -/
theorem finiteModelAverage_finiteFinsuppCombination
    (M : FiniteModel) (τ : G → Equiv.Perm M) (U : Finset M)
    (S : Finset G) (c : G →₀ ℝ) :
    finiteModelAverage M τ S (finiteFinsuppCombination M τ U c) =
      (S.card : ℝ)⁻¹ • ∑ s ∈ S,
        finiteComposedTranslation M τ U s c := by
  simp_rw [finiteComposedTranslation_eq_apply]
  rfl

/-- The one-step discrepancy between exact group-word averaging and the
genuine finite Markov operator is precisely the average of the individual
approximate-multiplication errors. -/
theorem finiteAveragingStep_sub_eq
    (M : FiniteModel) (τ : G → Equiv.Perm M) (U : Finset M)
    (S : Finset G) (k : ℕ) :
    finiteFinsuppCombination M τ U (averagingCoefficients S (k + 1)) -
        finiteModelAverage M τ S
          (finiteFinsuppCombination M τ U (averagingCoefficients S k)) =
      (S.card : ℝ)⁻¹ • ∑ s ∈ S,
        (finiteExactTranslation M τ U s (averagingCoefficients S k) -
          finiteComposedTranslation M τ U s
            (averagingCoefficients S k)) := by
  rw [finiteFinsuppCombination_averagingCoefficients_succ,
    finiteModelAverage_finiteFinsuppCombination]
  simp [Finset.sum_sub_distrib, smul_sub]

/-- The exact-versus-composed translation error is the finite linear
combination of the individual multiplication errors. -/
theorem finiteTranslation_sub_eq
    (M : FiniteModel) (τ : G → Equiv.Perm M) (U : Finset M)
    (s : G) (c : G →₀ ℝ) :
    finiteExactTranslation M τ U s c -
        finiteComposedTranslation M τ U s c =
      Finsupp.linearCombination ℝ (fun g ↦
        permutationOperator (τ (s * g)) (centeredIndicator U) -
          permutationOperator (τ s * τ g) (centeredIndicator U)) c := by
  rw [finiteExactTranslation_eq_sum]
  induction c using Finsupp.induction with
  | zero => simp [finiteComposedTranslation]
  | single_add g r c _ _ ih =>
      rw [show finiteComposedTranslation M τ U s (Finsupp.single g r + c) =
          finiteComposedTranslation M τ U s (Finsupp.single g r) +
            finiteComposedTranslation M τ U s c by
            simp [finiteComposedTranslation],
        map_add, map_add, add_sub_add_comm, ih]
      simp [finiteComposedTranslation, smul_sub]

/-- Triangle-inequality bound reducing the whole translation error to the
individual approximate-multiplication errors on the coefficient support. -/
theorem norm_finiteTranslation_sub_le
    (M : FiniteModel) (τ : G → Equiv.Perm M) (U : Finset M)
    (s : G) (c : G →₀ ℝ) :
    ‖finiteExactTranslation M τ U s c -
        finiteComposedTranslation M τ U s c‖ ≤
      ∑ g ∈ c.support, |c g| *
        ‖permutationOperator (τ (s * g)) (centeredIndicator U) -
          permutationOperator (τ s * τ g) (centeredIndicator U)‖ := by
  classical
  rw [finiteTranslation_sub_eq, Finsupp.linearCombination_apply, Finsupp.sum]
  calc
    ‖∑ g ∈ c.support, c g •
        (permutationOperator (τ (s * g)) (centeredIndicator U) -
          permutationOperator (τ s * τ g) (centeredIndicator U))‖ ≤
        ∑ g ∈ c.support, ‖c g •
          (permutationOperator (τ (s * g)) (centeredIndicator U) -
            permutationOperator (τ s * τ g) (centeredIndicator U))‖ :=
      norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro g hg
      rw [norm_smul, Real.norm_eq_abs]

/-- Approximate multiplicativity makes every fixed finitely supported
translation error uniformly negligible over all centered indicators. -/
theorem finiteTranslation_hilbert_error_eventually
    (A : SoficApproximation G) (s : G) (c : G →₀ ℝ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ U : Finset (A.model n),
      ‖finiteExactTranslation (A.model n) (A.map n) U s c -
          finiteComposedTranslation (A.model n) (A.map n) U s c‖ ^ 2 /
        Fintype.card (A.model n) < δ := by
  classical
  let R : ℝ := ∑ g ∈ c.support, |c g| ^ 2
  let m : ℝ := c.support.card
  let η : ℝ := δ / (R * m + 1)
  have hR : 0 ≤ R := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hm : 0 ≤ m := by positivity
  have hden : 0 < R * m + 1 := by positivity
  have hη : 0 < η := div_pos hδ hden
  let F := insert s c.support
  obtain ⟨Nerr, hNerr⟩ :=
    sofic_multiplication_hilbert_error_on_finset_eventually A F η hη
  obtain ⟨Ncard, hNcard⟩ := A.card_tendsToInfinity 1
  refine ⟨max Nerr Ncard, fun n hn U ↦ ?_⟩
  have hnerr : Nerr ≤ n := (le_max_left _ _).trans hn
  have hncard : Ncard ≤ n := (le_max_right _ _).trans hn
  have hcardNat : 0 < Fintype.card (A.model n) :=
    Nat.zero_lt_of_lt (hNcard n hncard)
  have hcard : (0 : ℝ) < Fintype.card (A.model n) := by
    exact_mod_cast hcardNat
  let e : G → EuclideanSpace ℝ (A.model n) := fun g ↦
    permutationOperator (A.map n (s * g)) (centeredIndicator U) -
      permutationOperator (A.map n s * A.map n g) (centeredIndicator U)
  have herr (g : G) (hg : g ∈ c.support) :
      ‖e g‖ ^ 2 / Fintype.card (A.model n) ≤ η := by
    exact (hNerr n hnerr s (by simp [F]) g (by simp [F, hg]) U).le
  have herr' (g : G) (hg : g ∈ c.support) :
      ‖e g‖ ^ 2 ≤ η * Fintype.card (A.model n) := by
    exact (div_le_iff₀ hcard).mp (herr g hg)
  have hsumErr :
      (∑ g ∈ c.support, ‖e g‖ ^ 2) ≤
        m * (η * Fintype.card (A.model n)) := by
    calc
      (∑ g ∈ c.support, ‖e g‖ ^ 2) ≤
          ∑ g ∈ c.support, η * Fintype.card (A.model n) :=
        Finset.sum_le_sum fun g hg ↦ herr' g hg
      _ = m * (η * Fintype.card (A.model n)) := by
        simp [m]
  have hcauchy :
      (∑ g ∈ c.support, |c g| * ‖e g‖) ^ 2 ≤
        R * ∑ g ∈ c.support, ‖e g‖ ^ 2 := by
    simpa [R] using Finset.sum_mul_sq_le_sq_mul_sq c.support
      (fun g ↦ |c g|) (fun g ↦ ‖e g‖)
  have htriangle := norm_finiteTranslation_sub_le
    (A.model n) (A.map n) U s c
  change ‖finiteExactTranslation (A.model n) (A.map n) U s c -
      finiteComposedTranslation (A.model n) (A.map n) U s c‖ ≤
        ∑ g ∈ c.support, |c g| * ‖e g‖ at htriangle
  have hsumNonneg : 0 ≤ ∑ g ∈ c.support, |c g| * ‖e g‖ :=
    Finset.sum_nonneg fun _ _ ↦ mul_nonneg (abs_nonneg _) (norm_nonneg _)
  have htriangleSq := (sq_le_sq₀ (norm_nonneg _) hsumNonneg).2 htriangle
  calc
    ‖finiteExactTranslation (A.model n) (A.map n) U s c -
        finiteComposedTranslation (A.model n) (A.map n) U s c‖ ^ 2 /
        Fintype.card (A.model n) ≤
      (∑ g ∈ c.support, |c g| * ‖e g‖) ^ 2 /
        Fintype.card (A.model n) :=
      div_le_div_of_nonneg_right htriangleSq hcard.le
    _ ≤ (R * ∑ g ∈ c.support, ‖e g‖ ^ 2) /
        Fintype.card (A.model n) :=
      div_le_div_of_nonneg_right hcauchy hcard.le
    _ ≤ (R * (m * (η * Fintype.card (A.model n)))) /
        Fintype.card (A.model n) := by
      gcongr
    _ = R * m * η := by field_simp
    _ < δ := by
      dsimp [η]
      calc
        R * m * (δ / (R * m + 1)) =
            (R * m * δ) / (R * m + 1) := by ring
        _ < δ := (div_lt_iff₀ hden).2 (by
          nlinarith [mul_nonneg hR hm])

/-- For every fixed time, exact group-word averaging and one application of
the genuine finite-model Markov operator are uniformly close over all
centered indicators. -/
theorem finiteAveragingStep_hilbert_error_eventually
    (A : SoficApproximation G) (S : Finset G) (hS : S.Nonempty)
    (k : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ U : Finset (A.model n),
      ‖finiteFinsuppCombination (A.model n) (A.map n) U
            (averagingCoefficients S (k + 1)) -
          finiteModelAverage (A.model n) (A.map n) S
            (finiteFinsuppCombination (A.model n) (A.map n) U
              (averagingCoefficients S k))‖ ^ 2 /
        Fintype.card (A.model n) < δ := by
  classical
  let c := averagingCoefficients S k
  let η := δ / 2
  have hη : 0 < η := by dsimp [η]; linarith
  have hηδ : η < δ := by dsimp [η]; linarith
  have hall (T : Finset G) :
      ∃ N : ℕ, ∀ n ≥ N, ∀ s ∈ T, ∀ U : Finset (A.model n),
        ‖finiteExactTranslation (A.model n) (A.map n) U s c -
            finiteComposedTranslation (A.model n) (A.map n) U s c‖ ^ 2 /
          Fintype.card (A.model n) < η := by
    induction T using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | @insert s T hst ih =>
        obtain ⟨Ns, hNs⟩ :=
          finiteTranslation_hilbert_error_eventually A s c η hη
        obtain ⟨NT, hNT⟩ := ih
        refine ⟨max Ns NT, fun n hn t ht U ↦ ?_⟩
        rcases Finset.mem_insert.mp ht with rfl | ht
        · exact hNs n ((le_max_left _ _).trans hn) U
        · exact hNT n ((le_max_right _ _).trans hn) t ht U
  obtain ⟨Nerr, hNerr⟩ := hall S
  obtain ⟨Ncard, hNcard⟩ := A.card_tendsToInfinity 1
  refine ⟨max Nerr Ncard, fun n hn U ↦ ?_⟩
  have hnerr : Nerr ≤ n := (le_max_left _ _).trans hn
  have hncard : Ncard ≤ n := (le_max_right _ _).trans hn
  have hcardNat : 0 < Fintype.card (A.model n) :=
    Nat.zero_lt_of_lt (hNcard n hncard)
  have hcard : (0 : ℝ) < Fintype.card (A.model n) := by
    exact_mod_cast hcardNat
  let e : G → EuclideanSpace ℝ (A.model n) := fun s ↦
    finiteExactTranslation (A.model n) (A.map n) U s c -
      finiteComposedTranslation (A.model n) (A.map n) U s c
  have he (s : G) (hs : s ∈ S) :
      ‖e s‖ ^ 2 / Fintype.card (A.model n) ≤ η :=
    (hNerr n hnerr s hs U).le
  rw [finiteAveragingStep_sub_eq]
  change ‖(S.card : ℝ)⁻¹ • ∑ s ∈ S, e s‖ ^ 2 /
      Fintype.card (A.model n) < δ
  exact (normalized_norm_average_le (A.model n) S hS e η hcard he).trans_lt hηδ

/-- The scalar finite-stage displacement quantity is exactly the normalized
squared norm of its explicit finite vector. -/
theorem finiteAveragingDisplacementNormSq_eq_norm
    (A : SoficApproximation G) (n : ℕ) (U : Finset (A.model n))
    (S : Finset G) (k : ℕ) :
    finiteAveragingDisplacementNormSq A n U S k =
      ‖finiteFinsuppCombination (A.model n) (A.map n) U
        (averagingDisplacementCoefficients S k)‖ ^ 2 /
          Fintype.card (A.model n) := by
  rw [finiteAveragingDisplacementNormSq,
    normalizedCombinationNormSq]
  rw [finiteFinsuppCombination_eq_sum]
  simp

/-- The hyperreal displacement norm is represented by the corresponding
finite-stage normalized norms. -/
theorem combinationNormSqHyperreal_displacement_eq_ofSeq
    (A : SoficApproximation G) (U : ∀ n, Finset (A.model n))
    (S : Finset G) (k : ℕ) :
    let c := averagingDisplacementCoefficients S k
    combinationNormSqHyperreal A U c.support id c =
      Hyperreal.ofSeq (fun n ↦
        finiteAveragingDisplacementNormSq A n (U n) S k) := by
  exact combinationNormSqHyperreal_eq_ofSeq A U
    (averagingDisplacementCoefficients S k).support id
    (averagingDisplacementCoefficients S k)

/-- Finite hyperreals are closed under negation. -/
theorem hyperreal_neg_finite {x : Hyperreal}
    (hx : 0 ≤ ArchimedeanClass.mk x) :
    0 ≤ ArchimedeanClass.mk (-x) := by
  rw [ArchimedeanClass.mk_neg]
  exact hx

/-- Finite hyperreals are closed under subtraction. -/
theorem hyperreal_sub_finite {x y : Hyperreal}
    (hx : 0 ≤ ArchimedeanClass.mk x)
    (hy : 0 ≤ ArchimedeanClass.mk y) :
    0 ≤ ArchimedeanClass.mk (x - y) := by
  rw [sub_eq_add_neg]
  exact hyperreal_add_finite hx (hyperreal_neg_finite hy)

/-- Uniform finite-stage version of Kun's exact-word contraction.  The
proof is the compactness argument: a cofinal sequence of violations would
contradict the GNS standard-part inequality. -/
theorem finiteAveragingDisplacementNormSq_eventually_lt
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, u} G Q ε)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S) (hεone : ε ≤ 1)
    (A : SoficApproximation G) (k : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ U : Finset (A.model n),
      finiteAveragingDisplacementNormSq A n U S k <
        (1 - ε ^ 2 / (4 * S.card)) ^ (2 * k) *
          finiteAveragingDisplacementNormSq A n U S 0 + δ := by
  classical
  by_contra h
  push Not at h
  choose φ hφ U hbad using h
  let B := A.reindex φ hφ
  let U' : ∀ n, Finset (B.model n) := fun n ↦ U n
  let ck := averagingDisplacementCoefficients S k
  let c0 := averagingDisplacementCoefficients S 0
  let factor : ℝ := (1 - ε ^ 2 / (4 * S.card)) ^ (2 * k)
  let Hk : Hyperreal := combinationNormSqHyperreal B U' ck.support id ck
  let H0 : Hyperreal := combinationNormSqHyperreal B U' c0.support id c0
  have hHkfinite : 0 ≤ ArchimedeanClass.mk Hk :=
    combinationNormSqHyperreal_finite B U' ck.support id ck
  have hH0finite : 0 ≤ ArchimedeanClass.mk H0 :=
    combinationNormSqHyperreal_finite B U' c0.support id c0
  have hfactorfinite : 0 ≤ ArchimedeanClass.mk ((factor : ℝ) : Hyperreal) :=
    hyperreal_coe_finite factor
  have hprodFinite :
      0 ≤ ArchimedeanClass.mk (((factor : ℝ) : Hyperreal) * H0) :=
    hyperreal_mul_finite hfactorfinite hH0finite
  have hdiffFinite :
      0 ≤ ArchimedeanClass.mk (Hk - ((factor : ℝ) : Hyperreal) * H0) :=
    hyperreal_sub_finite hHkfinite hprodFinite
  have hhyper : ((δ : ℝ) : Hyperreal) ≤
      Hk - ((factor : ℝ) : Hyperreal) * H0 := by
    rw [show Hk = Hyperreal.ofSeq (fun n ↦
        finiteAveragingDisplacementNormSq B n (U' n) S k) by
          exact combinationNormSqHyperreal_displacement_eq_ofSeq B U' S k,
      show H0 = Hyperreal.ofSeq (fun n ↦
        finiteAveragingDisplacementNormSq B n (U' n) S 0) by
          exact combinationNormSqHyperreal_displacement_eq_ofSeq B U' S 0]
    change Hyperreal.ofSeq (fun _ : ℕ ↦ δ) ≤ Hyperreal.ofSeq (fun n ↦
      finiteAveragingDisplacementNormSq B n (U' n) S k -
        factor * finiteAveragingDisplacementNormSq B n (U' n) S 0)
    rw [Hyperreal.ofSeq_le_ofSeq]
    exact Filter.Eventually.of_forall fun n ↦ by
      have hn := hbad n
      change factor * finiteAveragingDisplacementNormSq B n (U' n) S 0 + δ ≤
        finiteAveragingDisplacementNormSq B n (U' n) S k at hn
      linarith
  have hstdLower : δ ≤ ArchimedeanClass.stdPart
      (Hk - ((factor : ℝ) : Hyperreal) * H0) :=
    ArchimedeanClass.le_stdPart_of_le Hyperreal.coeRingHom hdiffFinite hhyper
  rw [ArchimedeanClass.stdPart_sub hHkfinite hprodFinite,
    ArchimedeanClass.stdPart_mul hfactorfinite hH0finite,
    Hyperreal.stdPart_coe] at hstdLower
  have hlimit := stdPart_averagingDisplacementNormSq_le
    hQ S hQS hone hεone B U' k
  change ArchimedeanClass.stdPart Hk ≤
    factor * ArchimedeanClass.stdPart H0 at hlimit
  linarith

/-- Orbit averaging the cyclic vector is the corresponding uniform finite
linear combination of kernel vectors. -/
theorem orbitAverage_kernelVector (p : PositiveDefiniteFunction G)
    (S : Finset G) :
    IsKazhdanPair.orbitAverage S (representation p) (kernelVector p 1) =
      finiteCombination p S (fun _ ↦ (S.card : ℝ)⁻¹) := by
  classical
  simp [IsKazhdanPair.orbitAverage, finiteCombination, Finset.smul_sum]

/-- Kun's second-difference contraction applied to the actual GNS
representation of a positive-definite function. -/
theorem norm_orbitAverage_sq_sub_le
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, u} G Q ε)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S) (hεone : ε ≤ 1)
    (p : PositiveDefiniteFunction G) :
    ‖IsKazhdanPair.orbitAverage S (representation p)
        (IsKazhdanPair.orbitAverage S (representation p) (kernelVector p 1)) -
      IsKazhdanPair.orbitAverage S (representation p) (kernelVector p 1)‖ ≤
      (1 - ε ^ 2 / (4 * S.card)) *
        ‖IsKazhdanPair.orbitAverage S (representation p) (kernelVector p 1) -
          kernelVector p 1‖ := by
  exact KazhdanOrthogonal.norm_orbitAverage_sq_sub_le
    hQ S hQS hone hεone (representation p) (kernelVector p 1)

/-- The iterated Kun contraction in the concrete cyclic GNS
representation. -/
theorem norm_iterate_orbitAverage_succ_sub_le
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, u} G Q ε)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S) (hεone : ε ≤ 1)
    (p : PositiveDefiniteFunction G) (k : ℕ) :
    let A := IsKazhdanPair.orbitAverage S (representation p)
    ‖(A^[k + 1]) (kernelVector p 1) -
        (A^[k]) (kernelVector p 1)‖ ≤
      (1 - ε ^ 2 / (4 * S.card)) ^ k *
        ‖A (kernelVector p 1) - kernelVector p 1‖ := by
  exact KazhdanOrthogonal.norm_iterate_orbitAverage_succ_sub_le
    hQ S hQS hone hεone (representation p) (kernelVector p 1) k

end KazhdanGNS
end NonsoficGroupsExist
