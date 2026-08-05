import NonsoficGroupsExist.ElementaryGroup
import NonsoficGroupsExist.LeavittSimplicity
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-!
# Elementary diagonalization over strongly divisible rings

Over a nontrivial ring in which every nonzero element divides the identity
from both sides (`∀ x ≠ 0, ∃ p q, p·x·q = 1` — the strong form of pure
infiniteness proved for `L_k(1,2)`), every invertible two-by-two matrix is
reduced to `diag(u, 1)` by elementary row and column operations.  This is
the GE property of Ara--Goodearl--Pardo in the exact form used by the
manuscript, with a short direct proof: one column operation makes the
`(0,1)` entry left-invertible, one row operation then plants a literal `1`
in the `(1,1)` position, and two more operations clear the off-diagonal.
-/

namespace NonsoficGroupsExist
namespace MatrixDiagonalization

variable {R : Type*} [Ring R]

/-- `diag(u, 1)` as a unit of the two-by-two matrix ring. -/
def diagUnit (u : Rˣ) : (Matrix (Fin 2) (Fin 2) R)ˣ where
  val := !![(u : R), 0; 0, 1]
  inv := !![((u⁻¹ : Rˣ) : R), 0; 0, 1]
  val_inv := by
    rw [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  inv_val := by
    rw [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem elementaryUnit01_val (t : R) :
    ((elementaryUnit (0 : Fin 2) 1 (by decide) t :
      (Matrix (Fin 2) (Fin 2) R)ˣ) : Matrix (Fin 2) (Fin 2) R) =
      !![1, t; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [elementaryUnit, Matrix.single]

theorem elementaryUnit10_val (t : R) :
    ((elementaryUnit (1 : Fin 2) 0 (by decide) t :
      (Matrix (Fin 2) (Fin 2) R)ˣ) : Matrix (Fin 2) (Fin 2) R) =
      !![1, 0; t, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [elementaryUnit, Matrix.single]

/-- The auxiliary reduction, assuming the corner entry is nonzero. -/
theorem exists_elementary_mul_diag_of_corner_ne_zero [Nontrivial R]
    (hdiv : ∀ x : R, x ≠ 0 → ∃ p q : R, p * x * q = 1)
    (A : (Matrix (Fin 2) (Fin 2) R)ˣ)
    (hA : (A : Matrix (Fin 2) (Fin 2) R) 0 0 ≠ 0) :
    ∃ (E F : (Matrix (Fin 2) (Fin 2) R)ˣ) (u : Rˣ),
      E ∈ elementaryGroup (Fin 2) R ∧ F ∈ elementaryGroup (Fin 2) R ∧
      E * A * F = diagUnit u := by
  set a := (A : Matrix (Fin 2) (Fin 2) R) 0 0 with ha
  set b := (A : Matrix (Fin 2) (Fin 2) R) 0 1 with hb
  set c := (A : Matrix (Fin 2) (Fin 2) R) 1 0 with hc
  set d := (A : Matrix (Fin 2) (Fin 2) R) 1 1 with hd
  have hAval : (A : Matrix (Fin 2) (Fin 2) R) = !![a, b; c, d] :=
    Matrix.eta_fin_two _
  obtain ⟨p, q, hpq⟩ := hdiv a hA
  -- step 1: make the (0,1) entry left-invertible
  set ρ := q * (1 - p * b) with hρ
  set F₁ : (Matrix (Fin 2) (Fin 2) R)ˣ :=
    elementaryUnit (0 : Fin 2) 1 (by decide) ρ with hF₁
  set b' := a * ρ + b with hb'
  set d' := c * ρ + d with hd'
  have hA₂ : ((A * F₁ : (Matrix (Fin 2) (Fin 2) R)ˣ) :
      Matrix (Fin 2) (Fin 2) R) = !![a, b'; c, d'] := by
    rw [Units.val_mul, hF₁, elementaryUnit01_val, hAval,
      Matrix.mul_fin_two]
    simp [hb', hd']
  have hpb' : p * b' = 1 := by
    rw [hb', hρ]
    calc
      p * (a * (q * (1 - p * b)) + b) =
          p * a * q * (1 - p * b) + p * b := by
        rw [mul_add]
        congr 1
        rw [← mul_assoc, ← mul_assoc]
      _ = 1 := by
        rw [hpq, one_mul]
        noncomm_ring
  -- step 2: plant a literal 1 in the (1,1) position
  set w := (1 - d') * p with hw
  set E₁ : (Matrix (Fin 2) (Fin 2) R)ˣ :=
    elementaryUnit (1 : Fin 2) 0 (by decide) w with hE₁
  set c₃ := w * a + c with hc₃
  have hA₃ : ((E₁ * (A * F₁) : (Matrix (Fin 2) (Fin 2) R)ˣ) :
      Matrix (Fin 2) (Fin 2) R) = !![a, b'; c₃, 1] := by
    rw [Units.val_mul, hE₁, elementaryUnit10_val, hA₂,
      Matrix.mul_fin_two]
    rw [show w * b' + 1 * d' = 1 from by
      rw [hw, mul_assoc, hpb', one_mul]
      noncomm_ring]
    simp [hc₃]
  -- step 3: clear the (0,1) entry
  set E₂ : (Matrix (Fin 2) (Fin 2) R)ˣ :=
    elementaryUnit (0 : Fin 2) 1 (by decide) (-b') with hE₂
  set v := a - b' * c₃ with hv
  have hA₄ : ((E₂ * (E₁ * (A * F₁)) : (Matrix (Fin 2) (Fin 2) R)ˣ) :
      Matrix (Fin 2) (Fin 2) R) = !![v, 0; c₃, 1] := by
    rw [Units.val_mul, hE₂, elementaryUnit01_val, hA₃,
      Matrix.mul_fin_two]
    simp [hv, sub_eq_add_neg]
  -- step 4: clear the (1,0) entry
  set F₂ : (Matrix (Fin 2) (Fin 2) R)ˣ :=
    elementaryUnit (1 : Fin 2) 0 (by decide) (-c₃) with hF₂
  have hA₅ : ((E₂ * (E₁ * (A * F₁)) * F₂ : (Matrix (Fin 2) (Fin 2) R)ˣ) :
      Matrix (Fin 2) (Fin 2) R) = !![v, 0; 0, 1] := by
    rw [Units.val_mul, hF₂, elementaryUnit10_val, hA₄,
      Matrix.mul_fin_two]
    simp
  -- the surviving corner is a unit
  set Z : (Matrix (Fin 2) (Fin 2) R)ˣ := E₂ * (E₁ * (A * F₁)) * F₂
    with hZ
  have hval : (Z : Matrix (Fin 2) (Fin 2) R) = !![v, 0; 0, 1] := hA₅
  have hleft : ((Z⁻¹ : (Matrix (Fin 2) (Fin 2) R)ˣ) :
      Matrix (Fin 2) (Fin 2) R) 0 0 * v = 1 := by
    have h1 := Z.inv_val
    have h2 := congrFun (congrFun h1 0) 0
    rw [hval] at h2
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
      using h2
  have hright : v * ((Z⁻¹ : (Matrix (Fin 2) (Fin 2) R)ˣ) :
      Matrix (Fin 2) (Fin 2) R) 0 0 = 1 := by
    have h1 := Z.val_inv
    have h2 := congrFun (congrFun h1 0) 0
    rw [hval] at h2
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
      using h2
  set u : Rˣ :=
    ⟨v, ((Z⁻¹ : (Matrix (Fin 2) (Fin 2) R)ˣ) :
      Matrix (Fin 2) (Fin 2) R) 0 0, hright, hleft⟩ with hu
  refine ⟨E₂ * E₁, F₁ * F₂, u, ?_, ?_, ?_⟩
  · exact Subgroup.mul_mem _
      (elementaryUnit_mem (0 : Fin 2) 1 (by decide) (-b'))
      (elementaryUnit_mem (1 : Fin 2) 0 (by decide) w)
  · exact Subgroup.mul_mem _
      (elementaryUnit_mem (0 : Fin 2) 1 (by decide) ρ)
      (elementaryUnit_mem (1 : Fin 2) 0 (by decide) (-c₃))
  · apply Units.ext
    have hassoc : E₂ * E₁ * A * (F₁ * F₂) = Z := by
      rw [hZ]
      group
    rw [hassoc, hval]
    rfl

/-- **Elementary diagonalization** (checkpoint `B3`, the GE property in
the form used): over a nontrivial ring with two-sided division of the
identity by every nonzero element, every invertible two-by-two matrix is
carried to `diag(u, 1)` by elementary operations. -/
theorem exists_elementary_mul_diag [Nontrivial R]
    (hdiv : ∀ x : R, x ≠ 0 → ∃ p q : R, p * x * q = 1)
    (A : (Matrix (Fin 2) (Fin 2) R)ˣ) :
    ∃ (E F : (Matrix (Fin 2) (Fin 2) R)ˣ) (u : Rˣ),
      E ∈ elementaryGroup (Fin 2) R ∧ F ∈ elementaryGroup (Fin 2) R ∧
      E * A * F = diagUnit u := by
  by_cases hA : (A : Matrix (Fin 2) (Fin 2) R) 0 0 ≠ 0
  · exact exists_elementary_mul_diag_of_corner_ne_zero hdiv A hA
  push Not at hA
  have hb : (A : Matrix (Fin 2) (Fin 2) R) 0 1 ≠ 0 := by
    intro hb0
    have h1 := A.val_inv
    have h2 := congrFun (congrFun h1 0) 0
    rw [Matrix.mul_apply, Fin.sum_univ_two, hA, hb0] at h2
    simp only [zero_mul, add_zero, Matrix.one_apply_eq] at h2
    exact one_ne_zero h2.symm
  set F₀ : (Matrix (Fin 2) (Fin 2) R)ˣ :=
    elementaryUnit (1 : Fin 2) 0 (by decide) 1 with hF₀
  have hcorner : ((A * F₀ : (Matrix (Fin 2) (Fin 2) R)ˣ) :
      Matrix (Fin 2) (Fin 2) R) 0 0 ≠ 0 := by
    rw [Units.val_mul, hF₀, elementaryUnit10_val]
    rw [show (A : Matrix (Fin 2) (Fin 2) R) =
      !![(A : Matrix (Fin 2) (Fin 2) R) 0 0,
        (A : Matrix (Fin 2) (Fin 2) R) 0 1;
        (A : Matrix (Fin 2) (Fin 2) R) 1 0,
        (A : Matrix (Fin 2) (Fin 2) R) 1 1] from
      Matrix.eta_fin_two _]
    rw [Matrix.mul_fin_two]
    simpa [hA] using hb
  obtain ⟨E, F, u, hE, hF, hEF⟩ :=
    exists_elementary_mul_diag_of_corner_ne_zero hdiv (A * F₀) hcorner
  refine ⟨E, F₀ * F, u, hE, ?_, ?_⟩
  · exact Subgroup.mul_mem _
      (elementaryUnit_mem (1 : Fin 2) 0 (by decide) 1) hF
  · rw [← hEF]
    group


/-- The signed swap is a product of three elementary matrices. -/
theorem exists_elementary_signedSwap :
    ∃ E ∈ elementaryGroup (Fin 2) R,
      (E : Matrix (Fin 2) (Fin 2) R) = !![0, -1; 1, 0] := by
  refine ⟨elementaryUnit (0 : Fin 2) 1 (by decide) (-1) *
    (elementaryUnit (1 : Fin 2) 0 (by decide) 1 *
      elementaryUnit (0 : Fin 2) 1 (by decide) (-1)),
    Subgroup.mul_mem _
      (elementaryUnit_mem (0 : Fin 2) 1 (by decide) (-1))
      (Subgroup.mul_mem _
        (elementaryUnit_mem (1 : Fin 2) 0 (by decide) 1)
        (elementaryUnit_mem (0 : Fin 2) 1 (by decide) (-1))), ?_⟩
  simp only [Units.val_mul, elementaryUnit01_val, elementaryUnit10_val]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- **The Whitehead lemma**: `diag(u, u⁻¹)` is a product of elementary
matrices. -/
theorem exists_elementary_whitehead (u : Rˣ) :
    ∃ E ∈ elementaryGroup (Fin 2) R,
      (E : Matrix (Fin 2) (Fin 2) R) =
        !![(u : R), 0; 0, ((u⁻¹ : Rˣ) : R)] := by
  obtain ⟨P, hPmem, hPval⟩ :=
    (exists_elementary_signedSwap (R := R))
  refine ⟨elementaryUnit (0 : Fin 2) 1 (by decide) (u : R) *
    (elementaryUnit (1 : Fin 2) 0 (by decide) (-((u⁻¹ : Rˣ) : R)) *
      elementaryUnit (0 : Fin 2) 1 (by decide) (u : R)) * P,
    Subgroup.mul_mem _
      (Subgroup.mul_mem _
        (elementaryUnit_mem (0 : Fin 2) 1 (by decide) (u : R))
        (Subgroup.mul_mem _
          (elementaryUnit_mem (1 : Fin 2) 0 (by decide)
            (-((u⁻¹ : Rˣ) : R)))
          (elementaryUnit_mem (0 : Fin 2) 1 (by decide) (u : R))))
      hPmem, ?_⟩
  simp only [Units.val_mul, elementaryUnit01_val, elementaryUnit10_val,
    hPval]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- **The unipotent Whitehead lemma**: when `b·a = 0`, the diagonal
`diag(1 + a·b, 1)` is a product of four elementary matrices. -/
theorem exists_elementary_unipotent_diag (a b : R) (hba : b * a = 0) :
    ∃ E ∈ elementaryGroup (Fin 2) R,
      (E : Matrix (Fin 2) (Fin 2) R) = !![1 + a * b, 0; 0, 1] := by
  have habab1 : b * (a * b) = 0 := by
    rw [← mul_assoc, hba, zero_mul]
  refine ⟨elementaryUnit (0 : Fin 2) 1 (by decide) a *
    (elementaryUnit (1 : Fin 2) 0 (by decide) b *
      (elementaryUnit (0 : Fin 2) 1 (by decide) (-a) *
        elementaryUnit (1 : Fin 2) 0 (by decide) (-b))),
    Subgroup.mul_mem _
      (elementaryUnit_mem (0 : Fin 2) 1 (by decide) a)
      (Subgroup.mul_mem _
        (elementaryUnit_mem (1 : Fin 2) 0 (by decide) b)
        (Subgroup.mul_mem _
          (elementaryUnit_mem (0 : Fin 2) 1 (by decide) (-a))
          (elementaryUnit_mem (1 : Fin 2) 0 (by decide) (-b)))), ?_⟩
  simp only [Units.val_mul, elementaryUnit01_val, elementaryUnit10_val]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [mul_add, hba, habab1]
  · simp [mul_add, hba, habab1]
  · simp [mul_add, hba, habab1]
  · simp [mul_add, hba, habab1]

/-- **GE for the universal binary Leavitt algebra** (`thm:agp`(a) at rank
two, in the exact form used): every invertible two-by-two matrix over
`L_k(1,2)` is carried to `diag(u, 1)` by elementary operations. -/
theorem binaryLeavitt_exists_elementary_mul_diag (k : Type) [Field k]
    (A : (Matrix (Fin 2) (Fin 2) (BinaryLeavitt.BinaryLeavittAlgebra k))ˣ) :
    ∃ (E F : (Matrix (Fin 2) (Fin 2)
        (BinaryLeavitt.BinaryLeavittAlgebra k))ˣ)
      (u : (BinaryLeavitt.BinaryLeavittAlgebra k)ˣ),
      E ∈ elementaryGroup (Fin 2) (BinaryLeavitt.BinaryLeavittAlgebra k) ∧
      F ∈ elementaryGroup (Fin 2) (BinaryLeavitt.BinaryLeavittAlgebra k) ∧
      E * A * F = diagUnit u :=
  exists_elementary_mul_diag
    (fun _ hx ↦ BinaryLeavitt.exists_mul_mul_eq_one k hx) A

end MatrixDiagonalization
end NonsoficGroupsExist
