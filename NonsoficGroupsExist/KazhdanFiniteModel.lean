import NonsoficGroupsExist.KazhdanOrthogonal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Finite permutation representations

This module turns an exact action on a finite set into its canonical
orthogonal representation on the real square-summable functions.  It is the
finite-dimensional representation used in the spectral part of Kun's
expander-decomposition argument.
-/

namespace NonsoficGroupsExist
namespace KazhdanFiniteModel

open scoped symmDiff

universe u v

variable {G : Type u} [Group G]
variable {Y : Type v} [Fintype Y]

/-- The orthogonal operator on `ℓ²(Y)` induced by a permutation of `Y`. -/
noncomputable def permutationOperator (p : Equiv.Perm Y) :
    EuclideanSpace ℝ Y ≃ₗᵢ[ℝ] EuclideanSpace ℝ Y :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ p

@[simp] theorem permutationOperator_apply (p : Equiv.Perm Y)
    (x : EuclideanSpace ℝ Y) (y : Y) :
    permutationOperator p x y = x (p.symm y) := rfl

@[simp] theorem permutationOperator_one :
    permutationOperator (1 : Equiv.Perm Y) = 1 := by
  ext x y
  change x ((1 : Equiv.Perm Y).symm y) = x y
  rw [show (1 : Equiv.Perm Y).symm = 1 by rfl]
  rfl

@[simp] theorem permutationOperator_mul (p q : Equiv.Perm Y) :
    permutationOperator (p * q) = permutationOperator p * permutationOperator q := by
  ext x y
  change x ((p * q).symm y) = x (q.symm (p.symm y))
  rw [show (p * q).symm = q.symm * p.symm by rfl]
  rfl

/-- The real orthogonal representation induced by an exact finite
permutation action. -/
noncomputable def permutationRepresentation (σ : G →* Equiv.Perm Y) :
    G →* (EuclideanSpace ℝ Y ≃ₗᵢ[ℝ] EuclideanSpace ℝ Y) where
  toFun g := permutationOperator (σ g)
  map_one' := by simp
  map_mul' g h := by simp

@[simp] theorem permutationRepresentation_apply
    (σ : G →* Equiv.Perm Y) (g : G) (x : EuclideanSpace ℝ Y) (y : Y) :
    permutationRepresentation σ g x y = x ((σ g).symm y) := rfl

section

variable [DecidableEq Y]

/-- The characteristic vector of a finite subset, regarded as a vector in
`ℓ²(Y)`. -/
noncomputable def indicator (U : Finset Y) : EuclideanSpace ℝ Y := by
  exact WithLp.toLp 2 fun y ↦ if y ∈ U then 1 else 0

omit [Fintype Y] in
@[simp] theorem indicator_apply (U : Finset Y) (y : Y) :
    indicator U y = if y ∈ U then 1 else 0 := by
  rfl

/-- Permuting a characteristic vector gives the characteristic vector of
the permuted set. -/
theorem permutationOperator_indicator (p : Equiv.Perm Y) (U : Finset Y) :
    permutationOperator p (indicator U) = indicator (U.map p.toEmbedding) := by
  classical
  ext y
  simp [permutationOperator_apply, indicator_apply]

/-- The squared `ℓ²` norm of a characteristic vector is the cardinality of
its support. -/
theorem norm_indicator_sq (U : Finset Y) :
    ‖indicator U‖ ^ 2 = (U.card : ℝ) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [indicator_apply]

/-- The squared distance between two characteristic vectors counts their
symmetric difference. -/
theorem norm_indicator_sub_sq (U V : Finset Y) :
    ‖indicator U - indicator V‖ ^ 2 = ((U ∆ V).card : ℝ) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  classical
  rw [show ((U ∆ V).card : ℝ) =
      ∑ y : Y, if y ∈ U ∆ V then 1 else 0 by simp]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hyU : y ∈ U <;> by_cases hyV : y ∈ V <;>
    simp [indicator_apply, Finset.mem_symmDiff, hyU, hyV]

/-- The displacement of a characteristic vector under a permutation counts
the symmetric difference between the set and its image. -/
theorem norm_permutationOperator_indicator_sub_sq
    (p : Equiv.Perm Y) (U : Finset Y) :
    ‖permutationOperator p (indicator U) - indicator U‖ ^ 2 =
      (((U.map p.toEmbedding) ∆ U).card : ℝ) := by
  rw [permutationOperator_indicator, norm_indicator_sub_sq]

end

end KazhdanFiniteModel
end NonsoficGroupsExist
