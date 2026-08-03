import NonsoficGroupsExist.ElementaryGroup
import NonsoficGroupsExist.LeavittCorner
import Mathlib.Tactic.NoncommRing

/-!
# Leavitt compression on elementary matrix groups

For a binary Leavitt family, the formula

`M ↦ p₁ I + (s₀ I) M (t₀ I)`

is a multiplicative, identity-preserving map on square matrices.  This module
constructs the induced injective homomorphism on unit groups and proves that it
restricts to an endomorphism of every elementary group.  No compression datum
is stored as a hypothesis.
-/

namespace NonsoficGroupsExist
namespace LeavittFamily

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Ring A]
variable (L : LeavittFamily A)

/-- A constant diagonal matrix. -/
def scalarDiagonal (a : A) : Matrix ι ι A := Matrix.diagonal fun _ ↦ a

omit [Fintype ι] in
@[simp] theorem scalarDiagonal_apply (a : A) (i j : ι) :
    scalarDiagonal (ι := ι) a i j = if i = j then a else 0 := by
  simp [scalarDiagonal, Matrix.diagonal_apply]

theorem scalarDiagonal_mul (a b : A) :
    scalarDiagonal (ι := ι) a * scalarDiagonal b = scalarDiagonal (a * b) := by
  ext i j
  simp [Matrix.mul_apply, scalarDiagonal_apply]

omit [Fintype ι] in
theorem scalarDiagonal_one : scalarDiagonal (ι := ι) (1 : A) = 1 := by
  ext i j
  simp [scalarDiagonal_apply, Matrix.one_apply]

omit [Fintype ι] in
theorem scalarDiagonal_zero : scalarDiagonal (ι := ι) (0 : A) = 0 := by
  ext i j
  simp [scalarDiagonal_apply]

/-- The multiplicative matrix-corner formula. -/
def matrixCompression (M : Matrix ι ι A) : Matrix ι ι A :=
  scalarDiagonal L.p1 + scalarDiagonal L.s0 * M * scalarDiagonal L.t0

@[simp] theorem matrixCompression_apply (M : Matrix ι ι A) (i j : ι) :
    L.matrixCompression M i j =
      (if i = j then L.p1 else 0) + L.s0 * M i j * L.t0 := by
  simp [matrixCompression, Matrix.mul_apply, scalarDiagonal_apply]

theorem matrixCompression_one : L.matrixCompression (1 : Matrix ι ι A) = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [matrixCompression_apply]
  · simp [matrixCompression_apply, hij]

theorem matrixCompression_mul (M N : Matrix ι ι A) :
    L.matrixCompression (M * N) = L.matrixCompression M * L.matrixCompression N := by
  let P : Matrix ι ι A := scalarDiagonal L.p1
  let S : Matrix ι ι A := scalarDiagonal L.s0
  let T : Matrix ι ι A := scalarDiagonal L.t0
  have hPP : P * P = P := by simp [P, scalarDiagonal_mul]
  have hPS : P * S = 0 := by
    change scalarDiagonal L.p1 * scalarDiagonal L.s0 = 0
    rw [scalarDiagonal_mul, L.p1_mul_s0, scalarDiagonal_zero]
  have hTP : T * P = 0 := by
    change scalarDiagonal L.t0 * scalarDiagonal L.p1 = 0
    rw [scalarDiagonal_mul, L.t0_mul_p1, scalarDiagonal_zero]
  have hTS : T * S = 1 := by
    calc
      T * S = scalarDiagonal (L.t0 * L.s0) := scalarDiagonal_mul _ _
      _ = scalarDiagonal 1 := by rw [L.t0_s0]
      _ = 1 := scalarDiagonal_one
  have hcore : S * M * T * (S * N * T) = S * (M * N) * T := by
    calc
      S * M * T * (S * N * T) = S * M * (T * S) * N * T := by
        noncomm_ring
      _ = S * (M * N) * T := by rw [hTS]; simp [mul_assoc]
  have hPS' : P * (S * N * T) = 0 := by
    calc
      P * (S * N * T) = (P * S) * N * T := by noncomm_ring
      _ = 0 := by rw [hPS]; simp
  have hTP' : (S * M * T) * P = 0 := by
    calc
      (S * M * T) * P = S * M * (T * P) := by noncomm_ring
      _ = 0 := by rw [hTP]; simp
  change P + S * (M * N) * T = (P + S * M * T) * (P + S * N * T)
  symm
  calc
    (P + S * M * T) * (P + S * N * T) =
        P * P + P * (S * N * T) + (S * M * T) * P +
          (S * M * T) * (S * N * T) := by noncomm_ring
    _ = P + S * (M * N) * T := by rw [hPP, hPS', hTP', hcore]; simp

/-- Compression of one invertible matrix, with its inverse constructed by the
same formula. -/
def matrixCompressionUnit (u : (Matrix ι ι A)ˣ) : (Matrix ι ι A)ˣ where
  val := L.matrixCompression (↑u : Matrix ι ι A)
  inv := L.matrixCompression (↑(u⁻¹) : Matrix ι ι A)
  val_inv := by
    rw [← matrixCompression_mul (L := L), Units.mul_inv, matrixCompression_one]
  inv_val := by
    rw [← matrixCompression_mul (L := L), Units.inv_mul, matrixCompression_one]

@[simp] theorem matrixCompressionUnit_val (u : (Matrix ι ι A)ˣ) :
    (↑(L.matrixCompressionUnit u) : Matrix ι ι A) =
      L.matrixCompression (↑u : Matrix ι ι A) := rfl

/-- Compression as an injective homomorphism of matrix unit groups. -/
def matrixCompressionHom : (Matrix ι ι A)ˣ →* (Matrix ι ι A)ˣ where
  toFun := L.matrixCompressionUnit
  map_one' := by apply Units.ext; exact matrixCompression_one (L := L)
  map_mul' u v := by
    apply Units.ext
    exact matrixCompression_mul (L := L) (↑u : Matrix ι ι A) (↑v : Matrix ι ι A)

@[simp] theorem matrixCompressionHom_val (u : (Matrix ι ι A)ˣ) :
    (↑(L.matrixCompressionHom u) : Matrix ι ι A) = L.matrixCompression ↑u := rfl

theorem matrixCompression_recover (M : Matrix ι ι A) :
    scalarDiagonal L.t0 * L.matrixCompression M * scalarDiagonal L.s0 = M := by
  let P : Matrix ι ι A := scalarDiagonal L.p1
  let S : Matrix ι ι A := scalarDiagonal L.s0
  let T : Matrix ι ι A := scalarDiagonal L.t0
  have hTP : T * P = 0 := by
    change scalarDiagonal L.t0 * scalarDiagonal L.p1 = 0
    rw [scalarDiagonal_mul, L.t0_mul_p1, scalarDiagonal_zero]
  have hTS : T * S = 1 := by
    calc
      T * S = scalarDiagonal (L.t0 * L.s0) := scalarDiagonal_mul _ _
      _ = scalarDiagonal 1 := by rw [L.t0_s0]
      _ = 1 := scalarDiagonal_one
  change T * (P + S * M * T) * S = M
  have hM : M * T * S = M := by
    calc
      M * T * S = M * (T * S) := mul_assoc _ _ _
      _ = M := by rw [hTS, mul_one]
  calc
    T * (P + S * M * T) * S = T * P * S + T * S * M * T * S := by
      noncomm_ring
    _ = M := by
      rw [hTP, hTS, zero_mul, zero_add, one_mul]
      exact hM

theorem matrixCompressionHom_injective :
    Function.Injective (matrixCompressionHom (ι := ι) L) := by
  intro u v huv
  apply Units.ext
  have h := congrArg (fun x : (Matrix ι ι A)ˣ ↦
    scalarDiagonal L.t0 * (↑x : Matrix ι ι A) * scalarDiagonal L.s0) huv
  simpa only [matrixCompressionHom_val, matrixCompression_recover] using h

@[simp] theorem matrixCompression_elementaryUnit (i j : ι) (hij : i ≠ j) (a : A) :
    matrixCompressionHom (ι := ι) L (elementaryUnit i j hij a) =
      elementaryUnit i j hij (L.s0 * a * L.t0) := by
  apply Units.ext
  ext x y
  have hdiag (q : A) : L.p1 + (L.s0 * L.t0 + q) = 1 + q := by
    rw [← add_assoc, L.p1_add_s0t0]
  simp only [matrixCompressionHom_val, matrixCompression_apply]
  by_cases hxy : x = y <;> by_cases hxi : x = i <;> by_cases hyj : y = j
  all_goals simp_all [elementaryUnit, Matrix.single, mul_add, add_mul]

theorem matrixCompressionHom_mem_elementary
    (x : (Matrix ι ι A)ˣ) (hx : x ∈ elementaryGroup ι A) :
    matrixCompressionHom (ι := ι) L x ∈ elementaryGroup ι A := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, j, hij, a, rfl⟩ := hx
      rw [matrixCompression_elementaryUnit]
      exact elementaryUnit_mem _ _ _ _
  | one => simp
  | mul x y _ _ hx hy => simpa using (elementaryGroup ι A).mul_mem hx hy
  | inv x _ hx => simpa using (elementaryGroup ι A).inv_mem hx

/-- The corner compression endomorphism of `EL_ι(A)`. -/
noncomputable def elementaryCompressionElement (g : elementaryGroup ι A) :
    elementaryGroup ι A :=
  ⟨matrixCompressionHom (ι := ι) L g,
    matrixCompressionHom_mem_elementary (ι := ι) L g g.property⟩

@[simp] theorem elementaryCompressionElement_val (g : elementaryGroup ι A) :
    (elementaryCompressionElement L g : (Matrix ι ι A)ˣ) =
      matrixCompressionHom (ι := ι) L g := rfl

/-- The corner compression endomorphism of `EL_ι(A)`. -/
noncomputable def elementaryCompressionEnd :
    elementaryGroup ι A →* elementaryGroup ι A where
  toFun := elementaryCompressionElement L
  map_one' := by
    apply Subtype.ext
    exact (matrixCompressionHom (ι := ι) L).map_one
  map_mul' x y := by
    apply Subtype.ext
    exact (matrixCompressionHom (ι := ι) L).map_mul x y

theorem elementaryCompressionEnd_injective :
    Function.Injective (elementaryCompressionEnd (ι := ι) L :
      elementaryGroup ι A → elementaryGroup ι A) := by
  intro x y hxy
  apply Subtype.ext
  exact matrixCompressionHom_injective L (congrArg Subtype.val hxy)

end LeavittFamily
end NonsoficGroupsExist
