import NonsoficGroupsExist.A2MagicGraph

/-!
# The explicit Laplacian of the A₂ magic graph

This is the four-regular graph `K₆` with the three opposite pairs removed.
All formulas are stated on the concrete `Fin 6` indexing, so its spectral
constant is proved by finite Hilbert-space algebra rather than imported as a
graph-theoretic assertion.
-/

namespace NonsoficGroupsExist

universe v

namespace A2MagicLaplacian

open A2MagicGraph

variable {E : Type v} [NormedAddCommGroup E]

/-- Sum of the six coordinates. -/
def total (f : Fin 6 → E) : E := ∑ i, f i

/-- The unnormalized degree-four graph Laplacian. -/
def laplacian (f : Fin 6 → E) (i : Fin 6) : E :=
  ∑ n : Fin 4, (f i - f (neighborIndex i n))

/-- Directed edge energy of the four-regular magic graph. -/
def directedEnergy (f : Fin 6 → E) : ℝ :=
  ∑ i : Fin 6, ∑ n : Fin 4, ‖f i - f (neighborIndex i n)‖ ^ 2

/-- Integral centering: `6 fᵢ - Σf`.  This avoids division while retaining
exactly the zero-sum component of a family. -/
def centered (f : Fin 6 → E) (i : Fin 6) : E := 6 • f i - total f

/-- Each vertex sees every vertex except itself and its opposite. -/
theorem laplacian_eq_five_smul_add_opposite_sub_total
    (f : Fin 6 → E) (i : Fin 6) :
    laplacian f i = 5 • f i + f (oppositeIndex i) - total f := by
  fin_cases i <;>
    simp [laplacian, total, neighborIndex, oppositeIndex, Fin.sum_univ_succ] <;>
    module

/-- The six Laplacian coordinates sum to zero. -/
theorem sum_laplacian (f : Fin 6 → E) : ∑ i, laplacian f i = 0 := by
  simp [laplacian, neighborIndex, Fin.sum_univ_succ]
  module

/-- Adding a constant family does not change the Laplacian. -/
theorem laplacian_add_const (f : Fin 6 → E) (x : E) (i : Fin 6) :
    laplacian (fun j ↦ f j + x) i = laplacian f i := by
  simp [laplacian]

/-- The Laplacian of a constant family is zero. -/
@[simp] theorem laplacian_const (x : E) (i : Fin 6) :
    laplacian (fun _ ↦ x) i = 0 := by
  simp [laplacian]

theorem directedEnergy_add_const (f : Fin 6 → E) (x : E) :
    directedEnergy (fun i ↦ f i + x) = directedEnergy f := by
  simp [directedEnergy]

@[simp] theorem total_centered (f : Fin 6 → E) : total (centered f) = 0 := by
  simp [total, centered, Fin.sum_univ_succ]

theorem laplacian_centered (f : Fin 6 → E) (i : Fin 6) :
    laplacian (centered f) i = 6 • laplacian f i := by
  unfold laplacian
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [centered]
  module

section InnerProduct

variable [InnerProductSpace ℝ E]

/-- The directed edge energy is twice the Laplacian quadratic form. -/
theorem directedEnergy_eq_two_sum_inner_laplacian (f : Fin 6 → E) :
    directedEnergy f = 2 * ∑ i : Fin 6, inner ℝ (f i) (laplacian f i) := by
  simp [directedEnergy, laplacian, neighborIndex, Fin.sum_univ_succ,
    norm_sub_sq_real, inner_sub_right, inner_add_right,
    ← Nat.cast_smul_eq_nsmul ℝ, inner_smul_right, real_inner_comm]
  ring

omit [InnerProductSpace ℝ E] in
/-- Cauchy--Schwarz at one degree-four vertex. -/
theorem laplacian_norm_sq_le_four_incidentEnergy (f : Fin 6 → E) (i : Fin 6) :
    ‖laplacian f i‖ ^ 2 ≤
      4 * ∑ n : Fin 4, ‖f i - f (neighborIndex i n)‖ ^ 2 := by
  have hnorm : ‖laplacian f i‖ ≤
      ∑ n : Fin 4, ‖f i - f (neighborIndex i n)‖ := by
    exact norm_sum_le _ _
  have hsum0 : 0 ≤ ∑ n : Fin 4, ‖f i - f (neighborIndex i n)‖ :=
    Finset.sum_nonneg fun n hn ↦ norm_nonneg _
  have hsq := sq_le_sq₀ (norm_nonneg _) hsum0 |>.2 hnorm
  have hcauchy :
      (∑ n : Fin 4, ‖f i - f (neighborIndex i n)‖) ^ 2 ≤
        4 * ∑ n : Fin 4, ‖f i - f (neighborIndex i n)‖ ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq
      (s := (Finset.univ : Finset (Fin 4)))
      (f := fun _ ↦ (1 : ℝ))
      (g := fun n ↦ ‖f i - f (neighborIndex i n)‖)
  exact hsq.trans hcauchy

omit [InnerProductSpace ℝ E] in
/-- The squared Laplacian norm is at most four times directed edge energy. -/
theorem sum_laplacian_norm_sq_le_four_directedEnergy (f : Fin 6 → E) :
    ∑ i : Fin 6, ‖laplacian f i‖ ^ 2 ≤ 4 * directedEnergy f := by
  calc
    ∑ i : Fin 6, ‖laplacian f i‖ ^ 2 ≤
        ∑ i : Fin 6,
          4 * ∑ n : Fin 4, ‖f i - f (neighborIndex i n)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact laplacian_norm_sq_le_four_incidentEnergy f i
    _ = 4 * directedEnergy f := by
      simp [directedEnergy, Finset.mul_sum]

omit [InnerProductSpace ℝ E] in
/-- Universal two-endpoint bound for one directed edge. -/
theorem norm_sub_sq_le_two (x y : E) :
    ‖x - y‖ ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have hnorm : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
  have hsq := sq_le_sq₀ (norm_nonneg _)
    (add_nonneg (norm_nonneg _) (norm_nonneg _)) |>.2 hnorm
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

omit [InnerProductSpace ℝ E] in
/-- The directed edge energy is bounded by sixteen times the family norm
squared. -/
theorem directedEnergy_le_sixteen_sum_norm_sq (f : Fin 6 → E) :
    directedEnergy f ≤ 16 * ∑ i : Fin 6, ‖f i‖ ^ 2 := by
  calc
    directedEnergy f ≤
        ∑ i : Fin 6, ∑ n : Fin 4,
          2 * (‖f i‖ ^ 2 + ‖f (neighborIndex i n)‖ ^ 2) := by
      unfold directedEnergy
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro n hn
      exact norm_sub_sq_le_two (f i) (f (neighborIndex i n))
    _ = 16 * ∑ i : Fin 6, ‖f i‖ ^ 2 := by
      simp [neighborIndex, Fin.sum_univ_succ]
      ring

/-- The elementary opposite-pair estimate behind the eigenvalue `4`. -/
theorem oppositePair_laplacian_norm_sq_ge (x y : E) :
    16 * (‖x‖ ^ 2 + ‖y‖ ^ 2) ≤
      ‖(5 : ℝ) • x + y‖ ^ 2 + ‖x + (5 : ℝ) • y‖ ^ 2 := by
  have hidentity :
      ‖(5 : ℝ) • x + y‖ ^ 2 + ‖x + (5 : ℝ) • y‖ ^ 2 =
        16 * (‖x‖ ^ 2 + ‖y‖ ^ 2) + 10 * ‖x + y‖ ^ 2 := by
    rw [norm_add_sq_real, norm_add_sq_real, norm_add_sq_real]
    rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 5)]
    simp only [inner_smul_left, inner_smul_right]
    rw [real_inner_comm y x]
    norm_num
    ring
  calc
    16 * (‖x‖ ^ 2 + ‖y‖ ^ 2) ≤
        16 * (‖x‖ ^ 2 + ‖y‖ ^ 2) + 10 * ‖x + y‖ ^ 2 :=
      le_add_of_nonneg_right (mul_nonneg (by norm_num) (sq_nonneg _))
    _ = ‖(5 : ℝ) • x + y‖ ^ 2 + ‖x + (5 : ℝ) • y‖ ^ 2 := hidentity.symm

/-- On the zero-sum subspace, the squared norm of the magic-graph Laplacian
is at least `4²` times the squared coordinate norm. -/
theorem laplacian_norm_sq_ge_sixteen
    (f : Fin 6 → E) (htotal : total f = 0) :
    16 * ∑ i, ‖f i‖ ^ 2 ≤ ∑ i, ‖laplacian f i‖ ^ 2 := by
  have hlap (i : Fin 6) :
      laplacian f i = (5 : ℝ) • f i + f (oppositeIndex i) := by
    rw [laplacian_eq_five_smul_add_opposite_sub_total, htotal]
    simp only [sub_zero]
    congr 1
    exact (Nat.cast_smul_eq_nsmul ℝ 5 (f i)).symm
  have h02 := oppositePair_laplacian_norm_sq_ge (f 0) (f 2)
  have h14 := oppositePair_laplacian_norm_sq_ge (f 1) (f 4)
  have h35 := oppositePair_laplacian_norm_sq_ge (f 3) (f 5)
  calc
    16 * ∑ i, ‖f i‖ ^ 2 =
        16 * (‖f 0‖ ^ 2 + ‖f 2‖ ^ 2) +
          16 * (‖f 1‖ ^ 2 + ‖f 4‖ ^ 2) +
          16 * (‖f 3‖ ^ 2 + ‖f 5‖ ^ 2) := by
            simp [Fin.sum_univ_succ]
            ring
    _ ≤ (‖(5 : ℝ) • f 0 + f 2‖ ^ 2 + ‖f 0 + (5 : ℝ) • f 2‖ ^ 2) +
        (‖(5 : ℝ) • f 1 + f 4‖ ^ 2 + ‖f 1 + (5 : ℝ) • f 4‖ ^ 2) +
        (‖(5 : ℝ) • f 3 + f 5‖ ^ 2 + ‖f 3 + (5 : ℝ) • f 5‖ ^ 2) := by
          exact add_le_add (add_le_add h02 h14) h35
    _ = ∑ i, ‖laplacian f i‖ ^ 2 := by
      simp_rw [hlap]
      simp [oppositeIndex, Fin.sum_univ_succ]
      rw [show f 0 + (5 : ℝ) • f 2 = (5 : ℝ) • f 2 + f 0 by abel]
      rw [show f 1 + (5 : ℝ) • f 4 = (5 : ℝ) • f 4 + f 1 by abel]
      rw [show f 3 + (5 : ℝ) • f 5 = (5 : ℝ) • f 5 + f 3 by abel]
      ring

/-- On the zero-sum subspace, `L² ≥ 4L`; equivalently, the squared
Laplacian norm is at least twice the directed edge energy. -/
theorem two_directedEnergy_le_sum_laplacian_norm_sq
    (f : Fin 6 → E) (htotal : total f = 0) :
    2 * directedEnergy f ≤ ∑ i : Fin 6, ‖laplacian f i‖ ^ 2 := by
  have hlap (i : Fin 6) :
      laplacian f i = (5 : ℝ) • f i + f (oppositeIndex i) := by
    rw [laplacian_eq_five_smul_add_opposite_sub_total, htotal]
    simp only [sub_zero]
    congr 1
    exact (Nat.cast_smul_eq_nsmul ℝ 5 (f i)).symm
  rw [directedEnergy_eq_two_sum_inner_laplacian]
  simp_rw [hlap]
  simp [oppositeIndex, Fin.sum_univ_succ, norm_add_sq_real,
    norm_smul,
    inner_add_right, inner_smul_left, inner_smul_right, real_inner_comm]
  have h02 : 0 ≤ ‖f 0 + f 2‖ ^ 2 := sq_nonneg _
  have h14 : 0 ≤ ‖f 1 + f 4‖ ^ 2 := sq_nonneg _
  have h35 : 0 ≤ ‖f 3 + f 5‖ ^ 2 := sq_nonneg _
  rw [norm_add_sq_real] at h02 h14 h35
  rw [real_inner_comm (f 2) (f 0)] at *
  nlinarith

/-- The inequality `L² ≥ 4L` holds on every family because both sides
vanish on constants. -/
theorem two_directedEnergy_le_sum_laplacian_norm_sq_general (f : Fin 6 → E) :
    2 * directedEnergy f ≤ ∑ i : Fin 6, ‖laplacian f i‖ ^ 2 := by
  let m : E := (6 : ℝ)⁻¹ • total f
  let g : Fin 6 → E := fun i ↦ f i + (-m)
  have hgTotal : total g = 0 := by
    simp [total, g, m, Fin.sum_univ_succ]
    module
  have h := two_directedEnergy_le_sum_laplacian_norm_sq g hgTotal
  simpa only [g, directedEnergy_add_const, laplacian_add_const] using h

/-- Division-free Poincaré inequality for an arbitrary six-tuple. -/
theorem centered_norm_sq_le_laplacian_norm_sq (f : Fin 6 → E) :
    16 * ∑ i, ‖centered f i‖ ^ 2 ≤
      ∑ i, ‖6 • laplacian f i‖ ^ 2 := by
  have h := laplacian_norm_sq_ge_sixteen (centered f) (total_centered f)
  simpa only [laplacian_centered] using h

end InnerProduct

end A2MagicLaplacian
end NonsoficGroupsExist
