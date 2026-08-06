import NonsoficGroupsExist.Leavitt.DiagonalClassGroup
import NonsoficGroupsExist.Leavitt.MatrixDiagonalization

/-!
# Generators of the diagonal class group

Building blocks for the rose-graph `K₁` computation: units of the form
`1 + a * b` with `b * a = 0` lie in the diagonal class group by the
unipotent Whitehead lemma, and for any one-sided-inverse pair
`t * s = 1` the corner insertion `s u t + (1 - s t)` is a unit congruent
to `u` modulo the diagonal class.  These generalize the binary-word
corner calculus of `LeavittDiagonalClass` from prefix words to
arbitrary isometry pairs, as needed for the depth-`n` matrix picture of
the degree-zero subalgebra.
-/

set_option linter.unusedSimpArgs false

open scoped commutatorElement

namespace NonsoficGroupsExist
namespace MatrixDiagonalization

variable {A : Type*} [Ring A]

/-- Units with unipotent value `1 + a * b`, `b * a = 0`, lie in the
diagonal class group. -/
theorem mem_stableUnits_of_val_unipotent {u : Aˣ} (a b : A)
    (hba : b * a = 0) (hval : (u : A) = 1 + a * b) :
    u ∈ stableUnits A := by
  obtain ⟨E, hE, hEval⟩ := exists_elementary_unipotent_diag a b hba
  have hEeq : E = diagUnit u := by
    apply Units.ext
    rw [hEval]
    show _ = !![(u : A), 0; 0, 1]
    rw [hval]
  rwa [hEeq] at hE

section Pair

variable (s t : A)

theorem pair_t_mul_range (hts : t * s = 1) (x : A) : t * (s * x) = x := by
  rw [← mul_assoc, hts, one_mul]

theorem pair_t_mul_one_sub_range (hts : t * s = 1) :
    t * (1 - s * t) = 0 := by
  rw [mul_sub, mul_one, pair_t_mul_range s t hts]
  exact sub_self _

theorem pair_one_sub_range_mul_s (hts : t * s = 1) :
    (1 - s * t) * s = 0 := by
  rw [sub_mul, one_mul, mul_assoc, hts, mul_one]
  exact sub_self _

theorem pair_one_sub_range_idem (hts : t * s = 1) :
    (1 - s * t) * (1 - s * t) = 1 - s * t := by
  have hp : (s * t) * (s * t) = s * t := by
    rw [mul_assoc, pair_t_mul_range s t hts]
  rw [mul_sub, mul_one, sub_mul, one_mul, hp]
  abel

theorem pair_corner_mul_corner (hts : t * s = 1) (x y : A) :
    (s * x * t) * (s * y * t) = s * (x * y) * t := by
  rw [show (s * x * t) * (s * y * t) = s * x * (t * s) * y * t from by
    noncomm_ring, hts]
  noncomm_ring

theorem pair_corner_mul_one_sub_range (hts : t * s = 1) (x : A) :
    (s * x * t) * (1 - s * t) = 0 := by
  rw [show (s * x * t) * (1 - s * t) =
    s * x * (t * (1 - s * t)) from by noncomm_ring,
    pair_t_mul_one_sub_range s t hts]
  noncomm_ring

theorem pair_one_sub_range_mul_corner (hts : t * s = 1) (x : A) :
    (1 - s * t) * (s * x * t) = 0 := by
  rw [show (1 - s * t) * (s * x * t) =
    ((1 - s * t) * s) * x * t from by noncomm_ring,
    pair_one_sub_range_mul_s s t hts]
  noncomm_ring

/-- The corner insertion of a unit along an isometry pair. -/
def pairKappaUnit (hts : t * s = 1) (u : Aˣ) : Aˣ where
  val := s * (u : A) * t + (1 - s * t)
  inv := s * ((u⁻¹ : Aˣ) : A) * t + (1 - s * t)
  val_inv := by
    rw [add_mul, mul_add, mul_add, pair_corner_mul_corner s t hts,
      pair_corner_mul_one_sub_range s t hts,
      pair_one_sub_range_mul_corner s t hts,
      pair_one_sub_range_idem s t hts]
    rw [show ((u : A) * ((u⁻¹ : Aˣ) : A)) = 1 from u.mul_inv, mul_one]
    rw [add_zero, zero_add]
    abel
  inv_val := by
    rw [add_mul, mul_add, mul_add, pair_corner_mul_corner s t hts,
      pair_corner_mul_one_sub_range s t hts,
      pair_one_sub_range_mul_corner s t hts,
      pair_one_sub_range_idem s t hts]
    rw [show (((u⁻¹ : Aˣ) : A) * (u : A)) = 1 from u.inv_mul, mul_one]
    rw [add_zero, zero_add]
    abel

@[simp] theorem pairKappaUnit_val (hts : t * s = 1) (u : Aˣ) :
    (pairKappaUnit s t hts u : A) = s * (u : A) * t + (1 - s * t) :=
  rfl

/-- The intertwiner realizing the corner insertion as a `GL₂`
conjugate of `diag(u, 1)`. -/
def pairIntertwiner (hts : t * s = 1) : (Matrix (Fin 2) (Fin 2) A)ˣ where
  val := !![s, 1 - s * t; 0, t]
  inv := !![t, 0; 1 - s * t, s]
  val_inv := by
    rw [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pair_one_sub_range_idem s t hts,
        pair_one_sub_range_mul_s s t hts,
        pair_t_mul_one_sub_range s t hts, hts]
  inv_val := by
    rw [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pair_one_sub_range_idem s t hts,
        pair_one_sub_range_mul_s s t hts,
        pair_t_mul_one_sub_range s t hts, hts]

theorem pairIntertwiner_conj_diagUnit (hts : t * s = 1) (u : Aˣ) :
    pairIntertwiner s t hts * diagUnit u *
      (pairIntertwiner s t hts)⁻¹ =
      diagUnit (pairKappaUnit s t hts u) := by
  apply Units.ext
  show !![s, 1 - s * t; 0, t] * !![(u : A), 0; 0, 1] *
    !![t, 0; 1 - s * t, s] = _
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagUnit, pairKappaUnit, pair_one_sub_range_idem s t hts,
      pair_one_sub_range_mul_s s t hts,
      pair_t_mul_one_sub_range s t hts, hts]

/-- **The corner-insertion coset identity** along any isometry pair:
under strong division, `s u t + (1 - s t)` is congruent to `u` modulo
the diagonal class group. -/
theorem pairKappaUnit_mul_inv_mem_stableUnits [Nontrivial A]
    (hts : t * s = 1)
    (hdiv : ∀ x : A, x ≠ 0 → ∃ p q : A, p * x * q = 1) (u : Aˣ) :
    pairKappaUnit s t hts u * u⁻¹ ∈ stableUnits A := by
  rw [mem_stableUnits_iff]
  have hcomm := commutator_mem_elementaryGroup_of_division hdiv
    (pairIntertwiner s t hts) (diagUnit u)
  have hval : ⁅pairIntertwiner s t hts, diagUnit u⁆ =
      diagUnit (pairKappaUnit s t hts u * u⁻¹) := by
    have hinv : (diagUnit u)⁻¹ = diagUnit u⁻¹ :=
      (map_inv diagUnitHom u).symm
    rw [commutatorElement_def, pairIntertwiner_conj_diagUnit, hinv,
      ← diagUnit_mul]
  rwa [hval] at hcomm

end Pair

end MatrixDiagonalization
end NonsoficGroupsExist
