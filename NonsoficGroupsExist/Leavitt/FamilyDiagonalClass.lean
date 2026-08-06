import NonsoficGroupsExist.KOne.StableUnitsGenerators
import NonsoficGroupsExist.Leavitt.MatrixSelfSimilarity

/-!
# Diagonal classes through a complete matrix family

The degree-zero half of the rose-graph `K₁` computation.  A complete
matrix family `F` on `ι` identifies `Mᵢ(A) ≅ A`; under this
identification a matrix transvection pulls back to a unipotent unit
`1 + F.left i * c * F.right j`, which lies in the diagonal class group
by the unipotent Whitehead lemma, while an invertible diagonal with
central entries pulls back to a product of corner insertions and is
therefore congruent to a central scalar.  The receptacle for these
statements is `centralClassGroup A`: the subgroup of units that are a
central scalar times a diagonal-class element, so that the manuscript's
rose-graph input `ScalarReduction A` says exactly that this subgroup is
everything.
-/

namespace NonsoficGroupsExist
namespace MatrixDiagonalization

variable {A : Type*} [Ring A]

theorem central_units_comm {c : Aˣ} (hc : ∀ x : A, (c : A) * x = x * (c : A))
    (g : Aˣ) : g * c = c * g :=
  Units.ext (hc (g : A)).symm

theorem central_inv {c : Aˣ} (hc : ∀ x : A, (c : A) * x = x * (c : A)) :
    ∀ x : A, ((c⁻¹ : Aˣ) : A) * x = x * ((c⁻¹ : Aˣ) : A) := by
  intro x
  calc ((c⁻¹ : Aˣ) : A) * x
      = ((c⁻¹ : Aˣ) : A) * x * ((c : A) * ((c⁻¹ : Aˣ) : A)) := by
        rw [Units.mul_inv, mul_one]
    _ = ((c⁻¹ : Aˣ) : A) * (x * (c : A)) * ((c⁻¹ : Aˣ) : A) := by
        noncomm_ring
    _ = ((c⁻¹ : Aˣ) : A) * ((c : A) * x) * ((c⁻¹ : Aˣ) : A) := by
        rw [← hc x]
    _ = x * ((c⁻¹ : Aˣ) : A) := by
        rw [← mul_assoc, Units.inv_mul, one_mul]

/-- The subgroup of units that are a central scalar times an element of
the diagonal class group. -/
def centralClassGroup (A : Type*) [Ring A] : Subgroup Aˣ where
  carrier := {u | ∃ c : Aˣ, (∀ x : A, (c : A) * x = x * (c : A)) ∧
    c⁻¹ * u ∈ stableUnits A}
  one_mem' := ⟨1, fun x ↦ by rw [Units.val_one, one_mul, mul_one],
    by rw [inv_one, mul_one]; exact one_mem _⟩
  mul_mem' := by
    rintro a b ⟨c, hc, hca⟩ ⟨e, he, heb⟩
    refine ⟨c * e, fun x ↦ ?_, ?_⟩
    · rw [Units.val_mul, mul_assoc, he x, ← mul_assoc, hc x, mul_assoc]
    · have hsplit : (c * e)⁻¹ * (a * b) = (c⁻¹ * a) * (e⁻¹ * b) := by
        have h1 : (c⁻¹ * a) * e⁻¹ = e⁻¹ * (c⁻¹ * a) :=
          central_units_comm (central_inv he) (c⁻¹ * a)
        rw [mul_inv_rev, show (c⁻¹ * a) * (e⁻¹ * b) =
          ((c⁻¹ * a) * e⁻¹) * b from by group, h1]
        group
      rw [hsplit]
      exact mul_mem hca heb
  inv_mem' := by
    rintro a ⟨c, hc, hca⟩
    refine ⟨c⁻¹, central_inv hc, ?_⟩
    have h1 : (c⁻¹)⁻¹ * a⁻¹ = (c⁻¹ * a)⁻¹ := by
      rw [mul_inv_rev, inv_inv]
      exact (central_units_comm hc a⁻¹).symm
    rw [h1]
    exact inv_mem hca

theorem mem_centralClassGroup_iff (u : Aˣ) :
    u ∈ centralClassGroup A ↔ ∃ c : Aˣ,
      (∀ x : A, (c : A) * x = x * (c : A)) ∧ c⁻¹ * u ∈ stableUnits A :=
  Iff.rfl

/-- The diagonal class group sits inside the central class group. -/
theorem stableUnits_le_centralClassGroup :
    stableUnits A ≤ centralClassGroup A := fun u hu ↦
  ⟨1, fun x ↦ by rw [Units.val_one, one_mul, mul_one],
    by rwa [inv_one, one_mul]⟩

/-- The manuscript's rose-graph input is exactly the statement that the
central class group is all of `Aˣ`. -/
theorem scalarReduction_of_forall_mem_centralClassGroup
    (h : ∀ u : Aˣ, u ∈ centralClassGroup A) : ScalarReduction A :=
  fun u ↦ h u

end MatrixDiagonalization

namespace CompleteMatrixFamily

open MatrixDiagonalization

variable {A : Type*} [Ring A] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (F : CompleteMatrixFamily A ι)

theorem right_mul_left_self (i : ι) : F.right i * F.left i = 1 := by
  rw [F.orthogonal i i, if_pos rfl]

theorem right_mul_left_ne {i j : ι} (hij : i ≠ j) :
    F.right i * F.left j = 0 := by
  rw [F.orthogonal i j, if_neg hij]

theorem matrixRingEquiv_single (i j : ι) (c : A) :
    F.matrixRingEquiv (Matrix.single i j c) = F.left i * c * F.right j := by
  rw [matrixRingEquiv_apply]
  have hrow : ∑ p, ∑ q, F.left p * Matrix.single i j c p q * F.right q =
      ∑ q, F.left i * Matrix.single i j c i q * F.right q := by
    refine Finset.sum_eq_single i (fun b _ hb ↦ ?_)
      (fun h ↦ absurd (Finset.mem_univ i) h)
    refine Finset.sum_eq_zero fun q _ ↦ ?_
    rw [Matrix.single_apply_of_row_ne (Ne.symm hb) j q c, mul_zero,
      zero_mul]
  have hcol : ∑ q, F.left i * Matrix.single i j c i q * F.right q =
      F.left i * Matrix.single i j c i j * F.right j := by
    refine Finset.sum_eq_single j (fun b _ hb ↦ ?_)
      (fun h ↦ absurd (Finset.mem_univ j) h)
    rw [Matrix.single_apply_of_col_ne i i (Ne.symm hb) c, mul_zero,
      zero_mul]
  rw [hrow, hcol, Matrix.single_apply_same]

theorem matrixRingEquiv_diagonal (v : ι → A) :
    F.matrixRingEquiv (Matrix.diagonal v) =
      ∑ i, F.left i * v i * F.right i := by
  rw [matrixRingEquiv_apply]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  refine (Finset.sum_eq_single p (fun b _ hb ↦ ?_)
    (fun h ↦ absurd (Finset.mem_univ p) h)).trans ?_
  · rw [Matrix.diagonal_apply_ne v (Ne.symm hb), mul_zero, zero_mul]
  · rw [Matrix.diagonal_apply_eq]

/-- **Transvection pullback**: through the family identification, a
matrix transvection becomes a unipotent unit lying in the diagonal
class group. -/
theorem unitsEquiv_unipotent_mem_stableUnits {i j : ι} (hij : i ≠ j)
    (c : A) (U : (Matrix ι ι A)ˣ)
    (hU : (U : Matrix ι ι A) = 1 + Matrix.single i j c) :
    F.unitsEquiv U ∈ stableUnits A := by
  apply mem_stableUnits_of_val_unipotent (F.left i * c) (F.right j)
  · rw [show F.right j * (F.left i * c) = (F.right j * F.left i) * c from
      (mul_assoc _ _ _).symm, F.right_mul_left_ne (Ne.symm hij), zero_mul]
  · rw [unitsEquiv_apply_val, hU, map_add, map_one,
      F.matrixRingEquiv_single i j c]

/-- **Corner-sum factorization over any complete family**: for each
finite index set there is a unit realizing the partial diagonal sum,
and it is a central scalar modulo the diagonal class. -/
theorem exists_partial_diagonal_unit [Nontrivial A]
    (hdiv : ∀ x : A, x ≠ 0 → ∃ p q : A, p * x * q = 1)
    (d : ι → Aˣ) (hd : ∀ i, ∀ x : A, ((d i : Aˣ) : A) * x = x * ((d i : Aˣ) : A))
    (S : Finset ι) :
    ∃ u : Aˣ,
      (u : A) = (∑ i ∈ S, F.left i * ((d i : Aˣ) : A) * F.right i) +
        (1 - ∑ i ∈ S, F.left i * F.right i) ∧
      u ∈ centralClassGroup A := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by simp, one_mem _⟩
  | insert a S haS IH =>
    obtain ⟨u, hval, hmem⟩ := IH
    refine ⟨pairKappaUnit (F.left a) (F.right a)
      (F.right_mul_left_self a) (d a) * u, ?_, ?_⟩
    · have htD : F.right a *
          (∑ i ∈ S, F.left i * ((d i : Aˣ) : A) * F.right i) = 0 := by
        rw [Finset.mul_sum]
        refine Finset.sum_eq_zero fun i hi ↦ ?_
        rw [show F.right a * (F.left i * ((d i : Aˣ) : A) * F.right i) =
          (F.right a * F.left i) * (((d i : Aˣ) : A) * F.right i) from by
            noncomm_ring,
          F.right_mul_left_ne (fun h ↦ haS (by rw [h]; exact hi)),
          zero_mul]
      have htP : F.right a * (∑ i ∈ S, F.left i * F.right i) = 0 := by
        rw [Finset.mul_sum]
        refine Finset.sum_eq_zero fun i hi ↦ ?_
        rw [← mul_assoc,
          F.right_mul_left_ne (fun h ↦ haS (by rw [h]; exact hi)),
          zero_mul]
      rw [Units.val_mul, pairKappaUnit_val, hval,
        Finset.sum_insert haS, Finset.sum_insert haS]
      set DS := ∑ i ∈ S, F.left i * ((d i : Aˣ) : A) * F.right i with hDS
      set PS := ∑ i ∈ S, F.left i * F.right i with hPS
      have h1 : (F.left a * ((d a : Aˣ) : A) * F.right a) * DS = 0 := by
        rw [mul_assoc (F.left a * ((d a : Aˣ) : A)) (F.right a) DS, htD,
          mul_zero]
      have h2 : (F.left a * ((d a : Aˣ) : A) * F.right a) * (1 - PS) =
          F.left a * ((d a : Aˣ) : A) * F.right a := by
        rw [mul_sub, mul_one,
          mul_assoc (F.left a * ((d a : Aˣ) : A)) (F.right a) PS, htP,
          mul_zero, sub_zero]
      have h3 : (1 - F.left a * F.right a) * DS = DS := by
        rw [sub_mul, one_mul, mul_assoc, htD, mul_zero, sub_zero]
      have h4 : (1 - F.left a * F.right a) * (1 - PS) =
          1 - PS - F.left a * F.right a := by
        rw [sub_mul, one_mul, mul_sub, mul_one, mul_assoc, htP, mul_zero,
          sub_zero]
      rw [add_mul, mul_add, mul_add, h1, h2, h3, h4]
      abel
    · have hκ : pairKappaUnit (F.left a) (F.right a)
          (F.right_mul_left_self a) (d a) ∈ centralClassGroup A := by
        refine ⟨d a, hd a, ?_⟩
        have h := pairKappaUnit_mul_inv_mem_stableUnits (F.left a)
          (F.right a) (F.right_mul_left_self a) hdiv (d a)
        rwa [central_units_comm (central_inv (hd a))
          (pairKappaUnit (F.left a) (F.right a)
            (F.right_mul_left_self a) (d a))] at h
      exact mul_mem hκ hmem

/-- **Diagonal pullback**: through the family identification, an
invertible diagonal matrix with central unit entries is a central
scalar modulo the diagonal class. -/
theorem unitsEquiv_diagonal_mem_centralClassGroup [Nontrivial A]
    (hdiv : ∀ x : A, x ≠ 0 → ∃ p q : A, p * x * q = 1)
    (d : ι → Aˣ) (hd : ∀ i, ∀ x : A, ((d i : Aˣ) : A) * x = x * ((d i : Aˣ) : A))
    (U : (Matrix ι ι A)ˣ)
    (hU : (U : Matrix ι ι A) = Matrix.diagonal fun i ↦ ((d i : Aˣ) : A)) :
    F.unitsEquiv U ∈ centralClassGroup A := by
  obtain ⟨u, hval, hmem⟩ :=
    F.exists_partial_diagonal_unit hdiv d hd Finset.univ
  have heq : F.unitsEquiv U = u := by
    apply Units.ext
    rw [unitsEquiv_apply_val, hU, F.matrixRingEquiv_diagonal, hval,
      F.complete, sub_self, add_zero]
  rw [heq]
  exact hmem

end CompleteMatrixFamily
end NonsoficGroupsExist
