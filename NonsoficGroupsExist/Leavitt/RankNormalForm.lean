import NonsoficGroupsExist.KOne.BalancedStableRank
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Rank normal form for balanced elements

Balanced elements of a Leavitt family are scalar matrices in disguise,
so the classical rank normal form transports: every balanced `c` is
`g⁻¹·e·h⁻¹` for balanced-valued units `g, h` and a cylinder-sum
idempotent `e`, with `e = 1` exactly in the invertible case.  Two
consequences used downstream: a balanced element that is a unit of the
ambient ring has balanced inverse (its matrix cannot be singular, else
it would be a zero divisor), and the invertibility of a balanced
element is detected by its diagonalized cylinder support.
-/

namespace NonsoficGroupsExist
namespace LeavittFamily

variable {A : Type*} [Ring A] (L : LeavittFamily A)
variable {k : Type*} [Field k] [Algebra k A]

/-- The scalar-matrix embedding sends diagonal matrices to weighted
cylinder sums. -/
theorem balancedEmbed_diagonal (n : ℕ) (d : (Fin n → Fin 2) → k) :
    L.balancedEmbed (k := k) n (Matrix.diagonal d) =
      ∑ γ : Fin n → Fin 2, d γ • L.cylinder (List.ofFn γ) := by
  show (L.prefixMatrixFamily (fullBinaryCode n)
      (L.fullBinaryCode_complete n)).matrixRingEquiv
      ((algebraMap k A).mapMatrix (Matrix.diagonal d)) = _
  rw [RingHom.mapMatrix_apply,
    Matrix.diagonal_map (map_zero (algebraMap k A)),
    CompleteMatrixFamily.matrixRingEquiv_diagonal]
  refine Finset.sum_congr rfl fun γ _ ↦ ?_
  show L.wordS (List.ofFn γ) * algebraMap k A (d γ) *
      L.wordT (List.ofFn γ) = _
  rw [show L.wordS (List.ofFn γ) * algebraMap k A (d γ) =
      algebraMap k A (d γ) * L.wordS (List.ofFn γ) from
        (Algebra.commutes _ _).symm,
    mul_assoc, ← Algebra.smul_def, cylinder]

/-- Indicator diagonals map to cylinder sums. -/
theorem balancedEmbed_indicator (n : ℕ) (S : Finset (Fin n → Fin 2)) :
    L.balancedEmbed (k := k) n
      (Matrix.diagonal fun γ ↦ if γ ∈ S then (1 : k) else 0) =
      ∑ γ ∈ S, L.cylinder (List.ofFn γ) := by
  classical
  rw [L.balancedEmbed_diagonal]
  have hsw : ∀ γ : Fin n → Fin 2,
      (if γ ∈ S then (1 : k) else 0) • L.cylinder (List.ofFn γ) =
      (if γ ∈ S then L.cylinder (List.ofFn γ) else 0) := by
    intro γ
    split_ifs <;> simp
  simp only [hsw]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- A balanced element that is a unit has an invertible matrix: a
singular matrix would make it a zero divisor. -/
theorem isUnit_matrix_of_isUnit [Nontrivial A] {n : ℕ}
    {C : Matrix (Fin n → Fin 2) (Fin n → Fin 2) k}
    (hu : IsUnit (L.balancedEmbed (k := k) n C)) : IsUnit C := by
  classical
  by_contra hC
  have hdet : C.det = 0 := by
    by_contra hd
    exact hC ((Matrix.isUnit_iff_isUnit_det C).mpr
      (isUnit_iff_ne_zero.mpr hd))
  obtain ⟨v, hv, hCv⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hdet
  set X : Matrix (Fin n → Fin 2) (Fin n → Fin 2) k :=
    Matrix.of fun i _ ↦ v i with hX
  have hCX : C * X = 0 := by
    ext i j
    have := congrFun hCv i
    simpa [hX, Matrix.mul_apply, Matrix.mulVec, dotProduct]
      using this
  have hXne : X ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    intro h0
    apply hi
    have h1 : X i i = (0 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) k)
        i i := by rw [h0]
    simpa [hX] using h1
  have hxne : L.balancedEmbed (k := k) n X ≠ 0 := by
    intro h0
    exact hXne (L.balancedEmbed_injective (k := k) n
      (h0.trans (map_zero _).symm))
  obtain ⟨u, huval⟩ := hu
  have hzero : L.balancedEmbed (k := k) n C *
      L.balancedEmbed (k := k) n X = 0 := by
    rw [← map_mul, hCX, map_zero]
  apply hxne
  calc L.balancedEmbed (k := k) n X
      = ((u⁻¹ : Aˣ) : A) * ((u : A) *
          L.balancedEmbed (k := k) n X) := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = ((u⁻¹ : Aˣ) : A) * (L.balancedEmbed (k := k) n C *
          L.balancedEmbed (k := k) n X) := by rw [huval]
    _ = 0 := by rw [hzero, mul_zero]

/-- **Balanced units have balanced inverses.** -/
theorem inv_mem_levelSpan_of_val_mem [Nontrivial A] {n : ℕ} (u : Aˣ)
    (hval : (u : A) ∈ Submodule.span k (L.levelMonomials n)) :
    ((u⁻¹ : Aˣ) : A) ∈ Submodule.span k (L.levelMonomials n) := by
  obtain ⟨C, hC⟩ := L.exists_balancedEmbed_eq hval
  have hCu : IsUnit C := L.isUnit_matrix_of_isUnit (n := n)
    (hC.symm ▸ ⟨u, rfl⟩)
  obtain ⟨Cu, hCuval⟩ := hCu
  have hone : (u : A) * L.balancedEmbed (k := k) n
      ((Cu⁻¹ : (Matrix (Fin n → Fin 2) (Fin n → Fin 2) k)ˣ) :
        Matrix (Fin n → Fin 2) (Fin n → Fin 2) k) = 1 := by
    rw [← hC, ← hCuval, ← map_mul, Units.mul_inv, map_one]
  have hinv : ((u⁻¹ : Aˣ) : A) = L.balancedEmbed (k := k) n
      ((Cu⁻¹ : (Matrix (Fin n → Fin 2) (Fin n → Fin 2) k)ˣ) :
        Matrix (Fin n → Fin 2) (Fin n → Fin 2) k) := by
    calc ((u⁻¹ : Aˣ) : A)
        = ((u⁻¹ : Aˣ) : A) * ((u : A) * L.balancedEmbed (k := k) n
            ((Cu⁻¹ : (Matrix (Fin n → Fin 2) (Fin n → Fin 2) k)ˣ) :
              Matrix (Fin n → Fin 2) (Fin n → Fin 2) k)) := by
          rw [hone, mul_one]
      _ = L.balancedEmbed (k := k) n
            ((Cu⁻¹ : (Matrix (Fin n → Fin 2) (Fin n → Fin 2) k)ˣ) :
              Matrix (Fin n → Fin 2) (Fin n → Fin 2) k) := by
          rw [← mul_assoc, Units.inv_mul, one_mul]
  rw [hinv]
  exact L.balancedEmbed_mem_span n _

/-- **Rank normal form**: every balanced element is equivalent, via
balanced-valued units with balanced inverses, to a cylinder-sum
idempotent; full support certifies invertibility. -/
theorem exists_rank_normal_form {n : ℕ} {c : A}
    (hc : c ∈ Submodule.span k (L.levelMonomials n)) :
    ∃ (g h : Aˣ) (S : Finset (Fin n → Fin 2)),
      (g : A) ∈ Submodule.span k (L.levelMonomials n) ∧
      ((g⁻¹ : Aˣ) : A) ∈ Submodule.span k (L.levelMonomials n) ∧
      (h : A) ∈ Submodule.span k (L.levelMonomials n) ∧
      ((h⁻¹ : Aˣ) : A) ∈ Submodule.span k (L.levelMonomials n) ∧
      (g : A) * c * (h : A) = ∑ γ ∈ S, L.cylinder (List.ofFn γ) ∧
      (S = Finset.univ → IsUnit c) := by
  classical
  obtain ⟨C, hC⟩ := L.exists_balancedEmbed_eq hc
  obtain ⟨Lt, Lt', dvec, hCdec⟩ :=
    Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec C
  set P : Matrix (Fin n → Fin 2) (Fin n → Fin 2) k :=
    (Lt.map Matrix.TransvectionStruct.toMatrix).prod with hP
  set Q : Matrix (Fin n → Fin 2) (Fin n → Fin 2) k :=
    (Lt'.map Matrix.TransvectionStruct.toMatrix).prod with hQ
  have hPunit : IsUnit P := by
    have h := Matrix.TransvectionStruct.prod_mul_reverse_inv_prod Lt
    have hdet := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_one] at hdet
    exact (Matrix.isUnit_iff_isUnit_det P).mpr
      (isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul_eq_one hdet))
  have hQunit : IsUnit Q := by
    have h := Matrix.TransvectionStruct.prod_mul_reverse_inv_prod Lt'
    have hdet := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_one] at hdet
    exact (Matrix.isUnit_iff_isUnit_det Q).mpr
      (isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul_eq_one hdet))
  set D₁ : Matrix (Fin n → Fin 2) (Fin n → Fin 2) k :=
    Matrix.diagonal (fun γ ↦ if dvec γ = 0 then 1 else dvec γ)
    with hD₁
  set S : Finset (Fin n → Fin 2) :=
    Finset.univ.filter (fun γ ↦ dvec γ ≠ 0) with hS
  set E : Matrix (Fin n → Fin 2) (Fin n → Fin 2) k :=
    Matrix.diagonal (fun γ ↦ if γ ∈ S then (1 : k) else 0) with hE
  have hD₁unit : IsUnit D₁ := by
    refine (Matrix.isUnit_iff_isUnit_det D₁).mpr ?_
    rw [hD₁, Matrix.det_diagonal]
    refine isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr ?_)
    intro γ _
    split_ifs with h
    · exact one_ne_zero
    · exact h
  have hDE : Matrix.diagonal dvec = D₁ * E := by
    rw [hD₁, hE, Matrix.diagonal_mul_diagonal]
    congr 1
    funext γ
    by_cases h : dvec γ = 0
    · rw [if_pos h, if_neg (by simp [hS, h]), mul_zero, h]
    · rw [if_neg h, if_pos (by simp [hS, h]), mul_one]
  obtain ⟨Pu, hPu⟩ := hPunit.mul hD₁unit
  obtain ⟨Qu, hQu⟩ := hQunit
  refine ⟨Units.map (L.balancedEmbed (k := k) n).toMonoidHom Pu⁻¹,
    Units.map (L.balancedEmbed (k := k) n).toMonoidHom Qu⁻¹, S,
    L.balancedEmbed_mem_span n _, ?_, L.balancedEmbed_mem_span n _,
    ?_, ?_, ?_⟩
  · rw [Units.coe_map_inv]
    exact L.balancedEmbed_mem_span n _
  · rw [Units.coe_map_inv]
    exact L.balancedEmbed_mem_span n _
  · show L.balancedEmbed (k := k) n
        ((Pu⁻¹ : (Matrix _ _ k)ˣ) : Matrix _ _ k) * c *
      L.balancedEmbed (k := k) n
        ((Qu⁻¹ : (Matrix _ _ k)ˣ) : Matrix _ _ k) = _
    rw [← hC, ← map_mul, ← map_mul,
      ← L.balancedEmbed_indicator (k := k) n S, ← hE]
    congr 1
    have hCform : C = (P * D₁) * (E * Q) := by
      rw [hCdec, hDE]
      noncomm_ring
    rw [hCform, ← hPu, ← hQu]
    calc ((Pu⁻¹ : (Matrix _ _ k)ˣ) : Matrix _ _ k) *
          ((Pu : Matrix _ _ k) * (E * (Qu : Matrix _ _ k))) *
          ((Qu⁻¹ : (Matrix _ _ k)ˣ) : Matrix _ _ k)
        = (((Pu⁻¹ : (Matrix _ _ k)ˣ) : Matrix _ _ k) *
            (Pu : Matrix _ _ k)) * E *
          ((Qu : Matrix _ _ k) *
            ((Qu⁻¹ : (Matrix _ _ k)ˣ) : Matrix _ _ k)) := by
          noncomm_ring
      _ = E := by rw [Units.inv_mul, Units.mul_inv, one_mul, mul_one]
  · intro hSuniv
    have hEone : E = 1 := by
      rw [hE, hSuniv]
      simp [Matrix.diagonal_one]
    have hCunit : IsUnit C := by
      rw [hCdec, hDE, hEone, mul_one]
      exact (hPunit.mul hD₁unit).mul ⟨Qu, hQu⟩
    rw [← hC]
    exact hCunit.map (L.balancedEmbed (k := k) n)

end LeavittFamily
end NonsoficGroupsExist
