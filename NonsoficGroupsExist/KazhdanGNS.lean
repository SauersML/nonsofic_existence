import NonsoficGroupsExist.KazhdanFiniteModel

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

end KazhdanGNS
end NonsoficGroupsExist
