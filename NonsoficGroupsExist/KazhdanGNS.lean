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

/-- The kernel vector indexed by a group element. -/
noncomputable def kernelVector (p : PositiveDefiniteFunction G) (g : G) :
    HilbertSpace p :=
  RKHS.kerFun (HilbertSpace p) g 1

/-- Inner products of kernel vectors recover the original group
coefficient. -/
theorem inner_kernelVector (p : PositiveDefiniteFunction G) (g h : G) :
    inner ℝ (kernelVector p g) (kernelVector p h) = p (g⁻¹ * h) := by
  have hker := RKHS.kernel_inner (H := HilbertSpace p) h g (1 : ℝ) (1 : ℝ)
  rw [RKHS.OfKernel.kernel_ofKernel] at hker
  simpa [kernelVector, scalarKernel] using hker.symm

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

/-- The finitely supported pre-Hilbert space used by the RKHS completion. -/
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

end KazhdanGNS
end NonsoficGroupsExist
