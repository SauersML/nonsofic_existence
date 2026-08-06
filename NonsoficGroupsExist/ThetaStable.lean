import NonsoficGroupsExist.OppositeTranspose
import NonsoficGroupsExist.DiagonalClassGroup

/-!
# The transpose anti-automorphism preserves the diagonal class group

The entrywise-`θ̂` transpose of a two-by-two matrix is an
anti-homomorphism sending the transvection `x_{ij}(a)` to
`x_{ji}(θ̂ a)`; since subgroups are closed under reversed products,
the elementary group is stable, and `diag(u,1)` transposes to
`diag(θ̂u, 1)` — hence `θ̂` preserves `stableUnits`, in both
directions since it is an involution.
-/

namespace NonsoficGroupsExist
namespace BinaryLeavitt

open LeavittFamily MatrixDiagonalization

-- `ᵀ` is scoped notation in the `Matrix` namespace; without this the
-- transpose in `thetaMat` below does not parse.  `open scoped` takes the
-- notation only, leaving the explicit `Matrix.*` references unshadowed.
open scoped Matrix

variable (k : Type) [Field k]

/-- Entrywise-`θ̂` transpose on two-by-two matrices. -/
noncomputable def thetaMat
    (M : Matrix (Fin 2) (Fin 2) (BinaryLeavittAlgebra k)) :
    Matrix (Fin 2) (Fin 2) (BinaryLeavittAlgebra k) :=
  (M.map (thetaHat k))ᵀ

theorem thetaHat_sum {ι : Type*} (s : Finset ι)
    (f : ι → BinaryLeavittAlgebra k) :
    thetaHat k (∑ i ∈ s, f i) = ∑ i ∈ s, thetaHat k (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact thetaHat_zero k
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, thetaHat_add, ih]

theorem thetaMat_mul
    (X Y : Matrix (Fin 2) (Fin 2) (BinaryLeavittAlgebra k)) :
    thetaMat k (X * Y) = thetaMat k Y * thetaMat k X := by
  ext i j
  show thetaHat k ((X * Y) j i) = _
  rw [Matrix.mul_apply, thetaHat_sum, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [thetaHat_mul]
  rfl

theorem thetaMat_one :
    thetaMat k (1 : Matrix (Fin 2) (Fin 2) (BinaryLeavittAlgebra k))
      = 1 := by
  ext i j
  show thetaHat k ((1 : Matrix (Fin 2) (Fin 2)
    (BinaryLeavittAlgebra k)) j i) = _
  by_cases h : i = j
  · subst h
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
    exact thetaHat_one k
  · rw [Matrix.one_apply_ne (Ne.symm h), Matrix.one_apply_ne h]
    exact thetaHat_zero k

theorem thetaMat_add
    (X Y : Matrix (Fin 2) (Fin 2) (BinaryLeavittAlgebra k)) :
    thetaMat k (X + Y) = thetaMat k X + thetaMat k Y := by
  ext i j
  show thetaHat k ((X + Y) j i) = _
  rw [Matrix.add_apply, thetaHat_add]
  rfl

theorem thetaMat_single (i j : Fin 2) (a : BinaryLeavittAlgebra k) :
    thetaMat k (Matrix.single i j a) =
      Matrix.single j i (thetaHat k a) := by
  ext i' j'
  show thetaHat k (Matrix.single i j a j' i') = _
  by_cases h1 : j = j'
  · by_cases h2 : i = i'
    · subst h1; subst h2
      rw [Matrix.single_apply_same, Matrix.single_apply_same]
    · rw [Matrix.single_apply_of_ne _ _ _ _ _ (by tauto),
        Matrix.single_apply_of_ne _ _ _ _ _ (by tauto)]
      exact thetaHat_zero k
  · rw [Matrix.single_apply_of_ne _ _ _ _ _ (by tauto),
      Matrix.single_apply_of_ne _ _ _ _ _ (by tauto)]
    exact thetaHat_zero k

/-- The unit induced by the matrix transpose map. -/
noncomputable def thetaMatUnit
    (u : (Matrix (Fin 2) (Fin 2) (BinaryLeavittAlgebra k))ˣ) :
    (Matrix (Fin 2) (Fin 2) (BinaryLeavittAlgebra k))ˣ where
  val := thetaMat k (u : Matrix (Fin 2) (Fin 2)
    (BinaryLeavittAlgebra k))
  inv := thetaMat k ((u⁻¹ : (Matrix (Fin 2) (Fin 2)
    (BinaryLeavittAlgebra k))ˣ) : Matrix (Fin 2) (Fin 2)
    (BinaryLeavittAlgebra k))
  val_inv := by
    rw [← thetaMat_mul, Units.inv_mul, thetaMat_one]
  inv_val := by
    rw [← thetaMat_mul, Units.mul_inv, thetaMat_one]

/-- The transpose map preserves the elementary group. -/
theorem thetaMatUnit_mem_elementaryGroup
    {u : (Matrix (Fin 2) (Fin 2) (BinaryLeavittAlgebra k))ˣ}
    (hu : u ∈ elementaryGroup (Fin 2) (BinaryLeavittAlgebra k)) :
    thetaMatUnit k u ∈
      elementaryGroup (Fin 2) (BinaryLeavittAlgebra k) := by
  induction hu using Subgroup.closure_induction with
  | mem z hz =>
      obtain ⟨i, j, hij, a, rfl⟩ := hz
      have hval : (thetaMatUnit k (elementaryUnit i j hij a) :
          Matrix (Fin 2) (Fin 2) (BinaryLeavittAlgebra k)) =
          ((elementaryUnit j i (Ne.symm hij) (thetaHat k a) :
            (Matrix (Fin 2) (Fin 2) (BinaryLeavittAlgebra k))ˣ) :
            Matrix (Fin 2) (Fin 2) (BinaryLeavittAlgebra k)) := by
        show thetaMat k (1 + Matrix.single i j a) = _
        rw [thetaMat_add, thetaMat_one, thetaMat_single]
        rfl
      have hEq : thetaMatUnit k (elementaryUnit i j hij a) =
          elementaryUnit j i (Ne.symm hij) (thetaHat k a) :=
        Units.ext hval
      rw [hEq]
      exact elementaryUnit_mem _ _ _ _
  | one =>
      have h1 : thetaMatUnit k 1 = 1 := by
        apply Units.ext
        show thetaMat k ((1 : (Matrix (Fin 2) (Fin 2)
          (BinaryLeavittAlgebra k))ˣ) : Matrix (Fin 2) (Fin 2)
          (BinaryLeavittAlgebra k)) = _
        exact thetaMat_one k
      rw [h1]
      exact one_mem _
  | mul x y _ _ hx hy =>
      have hmul : thetaMatUnit k (x * y) =
          thetaMatUnit k y * thetaMatUnit k x := by
        apply Units.ext
        show thetaMat k ((x : Matrix (Fin 2) (Fin 2)
            (BinaryLeavittAlgebra k)) * y) = _
        exact thetaMat_mul k _ _
      rw [hmul]
      exact mul_mem hy hx
  | inv x _ hx =>
      have hinv : thetaMatUnit k x⁻¹ = (thetaMatUnit k x)⁻¹ := by
        apply Units.ext
        rfl
      rw [hinv]
      exact inv_mem hx

/-- The transpose map matches the diagonal stabilization. -/
theorem thetaMatUnit_diagUnit (u : (BinaryLeavittAlgebra k)ˣ) :
    thetaMatUnit k (diagUnit u) = diagUnit (thetaUnit k u) := by
  apply Units.ext
  show thetaMat k
    (!![(u : BinaryLeavittAlgebra k), 0; 0, 1]) = _
  ext i j
  fin_cases i <;> fin_cases j
  · show thetaHat k (u : BinaryLeavittAlgebra k) = _
    rfl
  · show thetaHat k (0 : BinaryLeavittAlgebra k) = _
    simpa using thetaHat_zero k
  · show thetaHat k (0 : BinaryLeavittAlgebra k) = _
    simpa using thetaHat_zero k
  · show thetaHat k (1 : BinaryLeavittAlgebra k) = _
    simpa using thetaHat_one k

/-- **`θ̂` preserves the diagonal class group.** -/
theorem thetaUnit_mem_stableUnits {u : (BinaryLeavittAlgebra k)ˣ}
    (hu : u ∈ stableUnits (BinaryLeavittAlgebra k)) :
    thetaUnit k u ∈ stableUnits (BinaryLeavittAlgebra k) := by
  rw [mem_stableUnits_iff] at hu ⊢
  rw [← thetaMatUnit_diagUnit]
  exact thetaMatUnit_mem_elementaryGroup k hu

/-- `θ̂` on units is an involution. -/
theorem thetaUnit_thetaUnit (u : (BinaryLeavittAlgebra k)ˣ) :
    thetaUnit k (thetaUnit k u) = u := by
  apply Units.ext
  show thetaHat k (thetaHat k (u : BinaryLeavittAlgebra k)) = _
  exact thetaHat_thetaHat k _

/-- Membership transfers in both directions. -/
theorem thetaUnit_mem_stableUnits_iff (u : (BinaryLeavittAlgebra k)ˣ) :
    thetaUnit k u ∈ stableUnits (BinaryLeavittAlgebra k) ↔
      u ∈ stableUnits (BinaryLeavittAlgebra k) := by
  constructor
  · intro h
    have h2 := thetaUnit_mem_stableUnits k h
    rwa [thetaUnit_thetaUnit] at h2
  · exact thetaUnit_mem_stableUnits k

end BinaryLeavitt
end NonsoficGroupsExist
