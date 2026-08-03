import NonsoficGroupsExist.ElementaryGroup
import Mathlib.Data.Matrix.Block

/-!
# Stabilization of elementary groups

This module constructs the block-diagonal inclusion
`EL_ι(R) → EL_(ι ⊕ κ)(R)` directly on matrix units.  In particular, the
map used to regard `EL₃(R)` as the upper-left subgroup of `EL₄(R)` is an
injective group homomorphism with a kernel-checked elementary-membership proof.
-/

namespace NonsoficGroupsExist

variable {ι κ R : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Ring R]

/-- Block-diagonal stabilization of an invertible matrix. -/
def stabilizeUnit : (Matrix ι ι R)ˣ →* (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ where
  toFun u :=
    { val := Matrix.fromBlocks (↑u) 0 0 1
      inv := Matrix.fromBlocks (↑(u⁻¹)) 0 0 1
      val_inv := by
        rw [Matrix.fromBlocks_multiply]
        simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
          Matrix.one_mul]
        rw [Units.mul_inv]
        exact Matrix.fromBlocks_one
      inv_val := by
        rw [Matrix.fromBlocks_multiply]
        simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
          Matrix.one_mul]
        rw [Units.inv_mul]
        exact Matrix.fromBlocks_one }
  map_one' := by
    apply Units.ext
    exact Matrix.fromBlocks_one
  map_mul' u v := by
    apply Units.ext
    change Matrix.fromBlocks
        ((↑u : Matrix ι ι R) * (↑v : Matrix ι ι R)) 0 0 1 =
      Matrix.fromBlocks (↑u : Matrix ι ι R) 0 0 1 *
        Matrix.fromBlocks (↑v : Matrix ι ι R) 0 0 1
    rw [Matrix.fromBlocks_multiply]
    simp

@[simp] theorem stabilizeUnit_val (u : (Matrix ι ι R)ˣ) :
    (↑(stabilizeUnit (κ := κ) u) : Matrix (ι ⊕ κ) (ι ⊕ κ) R) =
      Matrix.fromBlocks (↑u) 0 0 1 := rfl

@[simp] theorem stabilizeUnit_elementaryUnit (i j : ι) (hij : i ≠ j) (a : R) :
    stabilizeUnit (κ := κ) (elementaryUnit i j hij a) =
      elementaryUnit (Sum.inl i) (Sum.inl j) (Sum.inl_injective.ne hij) a := by
  apply Units.ext
  ext x y
  rcases x with x | x <;> rcases y with y | y
  · simp [stabilizeUnit, elementaryUnit, Matrix.fromBlocks, Matrix.single,
      Matrix.one_apply]
  · simp [stabilizeUnit, elementaryUnit, Matrix.fromBlocks]
  · simp [stabilizeUnit, elementaryUnit, Matrix.fromBlocks]
  · simp [stabilizeUnit, elementaryUnit, Matrix.fromBlocks, Matrix.one_apply]

/-- Block-diagonal inclusion of elementary groups. -/
noncomputable def elementaryStabilization :
    elementaryGroup ι R →* elementaryGroup (ι ⊕ κ) R where
  toFun g := ⟨stabilizeUnit (κ := κ) g, by
    have map_mem (x : (Matrix ι ι R)ˣ) (hx : x ∈ elementaryGroup ι R) :
        stabilizeUnit (κ := κ) x ∈ elementaryGroup (ι ⊕ κ) R := by
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
          obtain ⟨i, j, hij, a, rfl⟩ := hx
          rw [stabilizeUnit_elementaryUnit]
          exact elementaryUnit_mem _ _ _ _
      | one => simp
      | mul x y _ _ hx hy => simpa using
          (elementaryGroup (ι ⊕ κ) R).mul_mem hx hy
      | inv x _ hx => simpa using (elementaryGroup (ι ⊕ κ) R).inv_mem hx
    exact map_mem g g.property⟩
  map_one' := by
    apply Subtype.ext
    exact (stabilizeUnit (ι := ι) (κ := κ) (R := R)).map_one
  map_mul' x y := by
    apply Subtype.ext
    exact (stabilizeUnit (ι := ι) (κ := κ) (R := R)).map_mul x y

theorem elementaryStabilization_injective :
    Function.Injective (elementaryStabilization (ι := ι) (κ := κ) (R := R)) := by
  intro x y hxy
  apply Subtype.ext
  apply Units.ext
  ext i j
  have h := congrArg
    (fun u : elementaryGroup (ι ⊕ κ) R ↦
      (↑(↑u : (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ) :
        Matrix (ι ⊕ κ) (ι ⊕ κ) R) (Sum.inl i) (Sum.inl j)) hxy
  exact h

end NonsoficGroupsExist
