import NonsoficGroupsExist.GradedComponents
import NonsoficGroupsExist.WindowNonposReduction
import NonsoficGroupsExist.WindowNonnegReduction

/-!
# The window dichotomy: full one-sided degree parts kill the window

The two terminal branches of the pencil elimination.  Let `v` be a
narrow unit with value `a + c + b` (degrees `-1, 0, 1`).

* If the degree `+1` part is **left invertible** — `w·b = 1` for some
  `w` — then every positive-degree component of `v⁻¹` dies from the
  top of the graded equations, so `v⁻¹` is a nonpositive-window unit
  and `v ∈ H`.
* Mirror: if the degree `-1` part is **right invertible** —
  `a·w = 1` — then `v⁻¹` is a nonnegative-window unit and `v ∈ H`.

In pencil terms the hypotheses hold whenever a code-relative scalar
stack `[B₀; B₁]` has full column rank, resp. `(A₀ | A₁)` full row
rank: the witness is the transported scalar one-sided inverse.
-/

namespace NonsoficGroupsExist
namespace BinaryLeavitt

open LeavittFamily MatrixDiagonalization

variable (k : Type) [Field k]

/-- **Left-full degree-one part ⟹ `v` is in the class group.** -/
theorem mem_stableUnits_of_deg_one_left_full
    [Nontrivial (BinaryLeavittAlgebra k)]
    (v : (BinaryLeavittAlgebra k)ˣ) {a c b : BinaryLeavittAlgebra k}
    (ha : a ∈ Submodule.span k ((family k).degreeMonomials (-1) (-1)))
    (hc : c ∈ Submodule.span k ((family k).degreeMonomials 0 0))
    (hb : b ∈ Submodule.span k ((family k).degreeMonomials 1 1))
    (hv : (v : BinaryLeavittAlgebra k) = a + c + b)
    (w : BinaryLeavittAlgebra k) (hw : w * b = 1) :
    v ∈ stableUnits (BinaryLeavittAlgebra k) := by
  classical
  set x : BinaryLeavittAlgebra k :=
    ((v⁻¹ : (BinaryLeavittAlgebra k)ˣ) : BinaryLeavittAlgebra k) with hx
  obtain ⟨lo₀, hi₀, hx₀⟩ := exists_mem_span_degreeMonomials k x
  set lo : ℤ := min lo₀ 0 with hlodef
  set hi : ℤ := max hi₀ 0 with hhidef
  have hlo : lo ≤ 0 := min_le_right _ _
  have hhi : 0 ≤ hi := le_max_right _ _
  have hxw : x ∈ Submodule.span k ((family k).degreeMonomials lo hi) :=
    (family k).span_degreeMonomials_mono (min_le_left _ _)
      (le_max_left _ _) hx₀
  obtain ⟨y, hymem, hysupp, hysum⟩ := exists_components k hxw
  -- the graded equations of `v · v⁻¹ = 1`
  have hzmem : ∀ D : ℤ, a * y (D + 1) + c * y D + b * y (D + (-1)) ∈
      Submodule.span k ((family k).degreeMonomials D D) := by
    intro D
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · have h := (family k).window_mul_mem_span (k := k) ha
        (hymem (D + 1))
      refine (family k).span_degreeMonomials_mono ?_ ?_ h <;> omega
    · have h := (family k).window_mul_mem_span (k := k) hc (hymem D)
      refine (family k).span_degreeMonomials_mono ?_ ?_ h <;> omega
    · have h := (family k).window_mul_mem_span (k := k) hb
        (hymem (D + (-1)))
      refine (family k).span_degreeMonomials_mono ?_ ?_ h <;> omega
  have h1 : ∑ D ∈ Finset.Icc (lo - 1) (hi + 1), y (D + 1) = x := by
    have hm := Finset.sum_map (Finset.Icc (lo - 1) (hi + 1))
      (addRightEmbedding (1 : ℤ)) y
    simp only [addRightEmbedding_apply] at hm
    rw [Finset.map_add_right_Icc] at hm
    rw [show lo - 1 + 1 = lo from by ring,
      show hi + 1 + 1 = hi + 2 from by ring] at hm
    rw [← hm, hysum]
    exact (Finset.sum_subset
      (Finset.Icc_subset_Icc le_rfl (by omega))
      (fun d hd hd' ↦ hysupp d (Or.inr (by
        rw [Finset.mem_Icc] at hd
        rw [Finset.mem_Icc] at hd'
        omega)))).symm
  have h0 : ∑ D ∈ Finset.Icc (lo - 1) (hi + 1), y D = x := by
    rw [hysum]
    exact (Finset.sum_subset
      (Finset.Icc_subset_Icc (by omega) (by omega))
      (fun d hd hd' ↦ hysupp d (by
        rw [Finset.mem_Icc] at hd
        rw [Finset.mem_Icc] at hd'
        omega))).symm
  have h2 : ∑ D ∈ Finset.Icc (lo - 1) (hi + 1), y (D + (-1)) = x := by
    have hm := Finset.sum_map (Finset.Icc (lo - 1) (hi + 1))
      (addRightEmbedding (-1 : ℤ)) y
    simp only [addRightEmbedding_apply] at hm
    rw [Finset.map_add_right_Icc] at hm
    rw [show lo - 1 + (-1) = lo - 2 from by ring,
      show hi + 1 + (-1) = hi from by ring] at hm
    rw [← hm, hysum]
    exact (Finset.sum_subset
      (Finset.Icc_subset_Icc (by omega) le_rfl)
      (fun d hd hd' ↦ hysupp d (Or.inl (by
        rw [Finset.mem_Icc] at hd
        rw [Finset.mem_Icc] at hd'
        omega)))).symm
  have hzsum : ∑ D ∈ Finset.Icc (lo - 1) (hi + 1),
      (a * y (D + 1) + c * y D + b * y (D + (-1))) = 1 := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
      h1, h0, h2, ← add_mul, ← add_mul, ← hv]
    exact v.mul_inv
  have hwsum : ∑ D ∈ Finset.Icc (lo - 1) (hi + 1),
      (if D = (0 : ℤ) then (1 : BinaryLeavittAlgebra k) else 0) = 1 := by
    rw [Finset.sum_ite_eq' (Finset.Icc (lo - 1) (hi + 1)) (0 : ℤ)
      (fun _ ↦ (1 : BinaryLeavittAlgebra k))]
    rw [if_pos (Finset.mem_Icc.mpr (by omega))]
  have huniq := components_unique k
    (D := Finset.Icc (lo - 1) (hi + 1))
    (y := fun D ↦ a * y (D + 1) + c * y D + b * y (D + (-1)))
    (z := fun D ↦ if D = (0 : ℤ) then 1 else 0)
    (fun D _ ↦ hzmem D)
    (fun D _ ↦ by
      split_ifs with hD
      · rw [hD]
        exact (family k).one_mem_window (k := k)
      · exact Submodule.zero_mem _)
    (by rw [hzsum, hwsum])
  -- kill the positive components from the top down
  have hkill : ∀ n : ℕ, ∀ d : ℤ, 1 ≤ d → hi + 1 - n ≤ d → y d = 0 := by
    intro n
    induction n with
    | zero =>
        intro d _ h2'
        exact hysupp d (Or.inr (by omega))
    | succ m ih =>
        intro d hd1 hd2
        by_cases hcase : hi + 1 - m ≤ d
        · exact ih d hd1 hcase
        · have hd1' : y (d + 1) = 0 := ih (d + 1) (by omega) (by omega)
          have hd2' : y (d + 2) = 0 := ih (d + 2) (by omega) (by omega)
          have heq := huniq (d + 1) (Finset.mem_Icc.mpr (by omega))
          beta_reduce at heq
          rw [if_neg (by omega : ¬(d + 1 = 0)),
            show d + 1 + 1 = d + 2 from by ring,
            show d + 1 + (-1) = d from by ring,
            hd2', hd1', mul_zero, mul_zero, zero_add, zero_add] at heq
          calc y d = w * b * y d := by rw [hw, one_mul]
            _ = w * (b * y d) := by rw [mul_assoc]
            _ = 0 := by rw [heq, mul_zero]
  -- the inverse has a nonpositive window
  have hxneg : x ∈ Submodule.span k
      ((family k).degreeMonomials lo 0) := by
    have hxsplit : x = ∑ d ∈ Finset.Icc lo 0, y d := by
      rw [hysum]
      exact (Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hhi)
        (fun d hd hd' ↦ by
          rw [Finset.mem_Icc] at hd
          rw [Finset.mem_Icc] at hd'
          exact hkill (hi + 1 - d).toNat d (by omega) (by omega))).symm
    rw [hxsplit]
    refine Submodule.sum_mem _ fun d hd ↦ ?_
    rw [Finset.mem_Icc] at hd
    exact (family k).span_degreeMonomials_mono (by omega) (by omega)
      (hymem d)
  have hinv : v⁻¹ ∈ stableUnits (BinaryLeavittAlgebra k) := by
    refine window_nonpos_mem_stableUnits k lo.natAbs v⁻¹ ?_
    refine (family k).span_degreeMonomials_mono ?_ le_rfl hxneg
    omega
  simpa using inv_mem hinv

/-- **Right-full degree-minus-one part ⟹ `v` is in the class
group.** -/
theorem mem_stableUnits_of_deg_neg_one_right_full
    [Nontrivial (BinaryLeavittAlgebra k)]
    (v : (BinaryLeavittAlgebra k)ˣ) {a c b : BinaryLeavittAlgebra k}
    (ha : a ∈ Submodule.span k ((family k).degreeMonomials (-1) (-1)))
    (hc : c ∈ Submodule.span k ((family k).degreeMonomials 0 0))
    (hb : b ∈ Submodule.span k ((family k).degreeMonomials 1 1))
    (hv : (v : BinaryLeavittAlgebra k) = a + c + b)
    (w : BinaryLeavittAlgebra k) (hw : a * w = 1) :
    v ∈ stableUnits (BinaryLeavittAlgebra k) := by
  classical
  set x : BinaryLeavittAlgebra k :=
    ((v⁻¹ : (BinaryLeavittAlgebra k)ˣ) : BinaryLeavittAlgebra k) with hx
  obtain ⟨lo₀, hi₀, hx₀⟩ := exists_mem_span_degreeMonomials k x
  set lo : ℤ := min lo₀ 0 with hlodef
  set hi : ℤ := max hi₀ 0 with hhidef
  have hlo : lo ≤ 0 := min_le_right _ _
  have hhi : 0 ≤ hi := le_max_right _ _
  have hxw : x ∈ Submodule.span k ((family k).degreeMonomials lo hi) :=
    (family k).span_degreeMonomials_mono (min_le_left _ _)
      (le_max_left _ _) hx₀
  obtain ⟨y, hymem, hysupp, hysum⟩ := exists_components k hxw
  -- the graded equations of `v⁻¹ · v = 1`
  have hzmem : ∀ D : ℤ, y (D + 1) * a + y D * c + y (D + (-1)) * b ∈
      Submodule.span k ((family k).degreeMonomials D D) := by
    intro D
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · have h := (family k).window_mul_mem_span (k := k)
        (hymem (D + 1)) ha
      refine (family k).span_degreeMonomials_mono ?_ ?_ h <;> omega
    · have h := (family k).window_mul_mem_span (k := k) (hymem D) hc
      refine (family k).span_degreeMonomials_mono ?_ ?_ h <;> omega
    · have h := (family k).window_mul_mem_span (k := k)
        (hymem (D + (-1))) hb
      refine (family k).span_degreeMonomials_mono ?_ ?_ h <;> omega
  have h1 : ∑ D ∈ Finset.Icc (lo - 1) (hi + 1), y (D + 1) = x := by
    have hm := Finset.sum_map (Finset.Icc (lo - 1) (hi + 1))
      (addRightEmbedding (1 : ℤ)) y
    simp only [addRightEmbedding_apply] at hm
    rw [Finset.map_add_right_Icc] at hm
    rw [show lo - 1 + 1 = lo from by ring,
      show hi + 1 + 1 = hi + 2 from by ring] at hm
    rw [← hm, hysum]
    exact (Finset.sum_subset
      (Finset.Icc_subset_Icc le_rfl (by omega))
      (fun d hd hd' ↦ hysupp d (Or.inr (by
        rw [Finset.mem_Icc] at hd
        rw [Finset.mem_Icc] at hd'
        omega)))).symm
  have h0 : ∑ D ∈ Finset.Icc (lo - 1) (hi + 1), y D = x := by
    rw [hysum]
    exact (Finset.sum_subset
      (Finset.Icc_subset_Icc (by omega) (by omega))
      (fun d hd hd' ↦ hysupp d (by
        rw [Finset.mem_Icc] at hd
        rw [Finset.mem_Icc] at hd'
        omega))).symm
  have h2 : ∑ D ∈ Finset.Icc (lo - 1) (hi + 1), y (D + (-1)) = x := by
    have hm := Finset.sum_map (Finset.Icc (lo - 1) (hi + 1))
      (addRightEmbedding (-1 : ℤ)) y
    simp only [addRightEmbedding_apply] at hm
    rw [Finset.map_add_right_Icc] at hm
    rw [show lo - 1 + (-1) = lo - 2 from by ring,
      show hi + 1 + (-1) = hi from by ring] at hm
    rw [← hm, hysum]
    exact (Finset.sum_subset
      (Finset.Icc_subset_Icc (by omega) le_rfl)
      (fun d hd hd' ↦ hysupp d (Or.inl (by
        rw [Finset.mem_Icc] at hd
        rw [Finset.mem_Icc] at hd'
        omega)))).symm
  have hzsum : ∑ D ∈ Finset.Icc (lo - 1) (hi + 1),
      (y (D + 1) * a + y D * c + y (D + (-1)) * b) = 1 := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul,
      h1, h0, h2, ← mul_add, ← mul_add, ← hv]
    exact v.inv_mul
  have hwsum : ∑ D ∈ Finset.Icc (lo - 1) (hi + 1),
      (if D = (0 : ℤ) then (1 : BinaryLeavittAlgebra k) else 0) = 1 := by
    rw [Finset.sum_ite_eq' (Finset.Icc (lo - 1) (hi + 1)) (0 : ℤ)
      (fun _ ↦ (1 : BinaryLeavittAlgebra k))]
    rw [if_pos (Finset.mem_Icc.mpr (by omega))]
  have huniq := components_unique k
    (D := Finset.Icc (lo - 1) (hi + 1))
    (y := fun D ↦ y (D + 1) * a + y D * c + y (D + (-1)) * b)
    (z := fun D ↦ if D = (0 : ℤ) then 1 else 0)
    (fun D _ ↦ hzmem D)
    (fun D _ ↦ by
      split_ifs with hD
      · rw [hD]
        exact (family k).one_mem_window (k := k)
      · exact Submodule.zero_mem _)
    (by rw [hzsum, hwsum])
  -- kill the negative components from the bottom up
  have hkill : ∀ n : ℕ, ∀ d : ℤ, d ≤ -1 → d ≤ lo - 1 + n → y d = 0 := by
    intro n
    induction n with
    | zero =>
        intro d _ h2'
        exact hysupp d (Or.inl (by omega))
    | succ m ih =>
        intro d hd1 hd2
        by_cases hcase : d ≤ lo - 1 + m
        · exact ih d hd1 hcase
        · have hd1' : y (d - 1) = 0 := ih (d - 1) (by omega) (by omega)
          have hd2' : y (d - 2) = 0 := ih (d - 2) (by omega) (by omega)
          have heq := huniq (d - 1) (Finset.mem_Icc.mpr (by omega))
          beta_reduce at heq
          rw [if_neg (by omega : ¬(d - 1 = 0)),
            show d - 1 + 1 = d from by ring,
            show d - 1 + (-1) = d - 2 from by ring,
            hd1', hd2', zero_mul, zero_mul, add_zero, add_zero] at heq
          calc y d = y d * (a * w) := by rw [hw, mul_one]
            _ = y d * a * w := by rw [← mul_assoc]
            _ = 0 := by rw [heq, zero_mul]
  -- the inverse has a nonnegative window
  have hxpos : x ∈ Submodule.span k
      ((family k).degreeMonomials 0 hi) := by
    have hxsplit : x = ∑ d ∈ Finset.Icc 0 hi, y d := by
      rw [hysum]
      exact (Finset.sum_subset (Finset.Icc_subset_Icc hlo le_rfl)
        (fun d hd hd' ↦ by
          rw [Finset.mem_Icc] at hd
          rw [Finset.mem_Icc] at hd'
          exact hkill (d - lo + 1).toNat d (by omega) (by omega))).symm
    rw [hxsplit]
    refine Submodule.sum_mem _ fun d hd ↦ ?_
    rw [Finset.mem_Icc] at hd
    exact (family k).span_degreeMonomials_mono (by omega) (by omega)
      (hymem d)
  have hinv : v⁻¹ ∈ stableUnits (BinaryLeavittAlgebra k) := by
    refine window_nonneg_mem_stableUnits k hi.toNat v⁻¹ ?_
    refine (family k).span_degreeMonomials_mono le_rfl ?_ hxpos
    omega
  simpa using inv_mem hinv

end BinaryLeavitt
end NonsoficGroupsExist
