import NonsoficGroupsExist.KOne.BalancedStableRank

/-!
# Von Neumann regularity of the balanced subalgebra

Every matrix over a field has a generalized inverse: diagonalize by
transvections, invert the nonzero diagonal entries.  Transported
through the scalar-matrix embedding this gives every balanced element
`z` of a Leavitt family a balanced pseudo-inverse `ξ` with `zξz = z`.
Consequence: square-zero tails die — if `(s₁z)² = 0` then
`1 + s₁z = 1 + (s₁z)(ξz)` with `(ξz)(s₁z) = 0`, so the unipotent
Whitehead lemma places the unit in the diagonal class group.
-/

namespace NonsoficGroupsExist

open MatrixDiagonalization

/-- Every square matrix over a field is von Neumann regular. -/
theorem exists_pseudoInverse_matrix {k : Type*} [Field k] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (C : Matrix ι ι k) :
    ∃ X : Matrix ι ι k, C * X * C = C := by
  classical
  obtain ⟨L, L', D, hC⟩ :=
    Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec C
  set P : Matrix ι ι k := (L.map Matrix.TransvectionStruct.toMatrix).prod
    with hP
  set Q : Matrix ι ι k :=
    (L'.map Matrix.TransvectionStruct.toMatrix).prod with hQ
  -- P and Q are invertible (products of transvections)
  have hPunit : IsUnit P := by
    rw [hP]
    exact IsUnit.of_mul_eq_one _ (Matrix.TransvectionStruct.prod_mul_reverse_inv_prod L)
  have hQunit : IsUnit Q := by
    rw [hQ]
    exact IsUnit.of_mul_eq_one _ (Matrix.TransvectionStruct.prod_mul_reverse_inv_prod L')
  -- pseudo-inverse of the diagonal: entrywise inverse-or-zero
  set Dinv : Matrix ι ι k := Matrix.diagonal fun i ↦ (D i)⁻¹ with hD
  have hDDD : Matrix.diagonal D * Dinv * Matrix.diagonal D =
      Matrix.diagonal D := by
    rw [hD, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases h : D i = 0
    · simp [h]
    · field_simp
  obtain ⟨Pu, hPu⟩ := hPunit
  obtain ⟨Qu, hQu⟩ := hQunit
  refine ⟨((Qu⁻¹ : (Matrix ι ι k)ˣ) : Matrix ι ι k) * Dinv *
    ((Pu⁻¹ : (Matrix ι ι k)ˣ) : Matrix ι ι k), ?_⟩
  have hCform : C = P * Matrix.diagonal D * Q := hC
  rw [hCform, ← hPu, ← hQu]
  calc (Pu : Matrix ι ι k) * Matrix.diagonal D * (Qu : Matrix ι ι k) *
        (((Qu⁻¹ : (Matrix ι ι k)ˣ) : Matrix ι ι k) * Dinv *
          ((Pu⁻¹ : (Matrix ι ι k)ˣ) : Matrix ι ι k)) *
        ((Pu : Matrix ι ι k) * Matrix.diagonal D *
          (Qu : Matrix ι ι k))
      = (Pu : Matrix ι ι k) * (Matrix.diagonal D *
          ((Qu : Matrix ι ι k) *
            ((Qu⁻¹ : (Matrix ι ι k)ˣ) : Matrix ι ι k)) * Dinv *
          (((Pu⁻¹ : (Matrix ι ι k)ˣ) : Matrix ι ι k) *
            (Pu : Matrix ι ι k)) * Matrix.diagonal D) *
        (Qu : Matrix ι ι k) := by noncomm_ring
    _ = (Pu : Matrix ι ι k) * (Matrix.diagonal D * Dinv *
          Matrix.diagonal D) * (Qu : Matrix ι ι k) := by
        rw [Units.mul_inv, Units.inv_mul, mul_one]
        noncomm_ring
    _ = (Pu : Matrix ι ι k) * Matrix.diagonal D *
        (Qu : Matrix ι ι k) := by rw [hDDD]

namespace LeavittFamily

variable {A : Type*} [Ring A] (L : LeavittFamily A)
variable {k : Type*} [Field k] [Algebra k A]

/-- **Balanced regularity**: every balanced element has a balanced
pseudo-inverse. -/
theorem exists_balanced_pseudoInverse [Nontrivial A] {n : ℕ} {z : A}
    (hz : z ∈ Submodule.span k (L.levelMonomials n)) :
    ∃ ξ : A, (∃ m, ξ ∈ Submodule.span k (L.levelMonomials m)) ∧
      z * ξ * z = z := by
  obtain ⟨C, hC⟩ := L.exists_balancedEmbed_eq hz
  obtain ⟨X, hX⟩ := exists_pseudoInverse_matrix C
  refine ⟨L.balancedEmbed n X, ⟨n, L.balancedEmbed_mem_span n X⟩, ?_⟩
  rw [← hC, ← map_mul, ← map_mul, hX]

/-- **Square-zero tails die**: if `(s₁z)² = 0` with `z` balanced, then
any unit of value `1 + s₁z` lies in the diagonal class group. -/
theorem square_zero_tail_mem_stableUnits [Nontrivial A] {n : ℕ}
    {z : A} (hz : z ∈ Submodule.span k (L.levelMonomials n))
    (hsq : L.s 1 * z * (L.s 1 * z) = 0) (u : Aˣ)
    (hu : (u : A) = 1 + L.s 1 * z) :
    u ∈ stableUnits A := by
  obtain ⟨ξ, _, hξ⟩ := L.exists_balanced_pseudoInverse hz
  have ht1s1 : L.t 1 * L.s 1 = 1 := by rw [t_mul_s]; simp
  -- z·s₁·z = 0 by left-cancelling s₁
  have hzsz : z * (L.s 1 * z) = 0 := by
    have h1 : L.t 1 * (L.s 1 * z * (L.s 1 * z)) = 0 := by
      rw [hsq, mul_zero]
    rwa [show L.t 1 * (L.s 1 * z * (L.s 1 * z)) =
      (L.t 1 * L.s 1) * (z * (L.s 1 * z)) from by noncomm_ring,
      ht1s1, one_mul] at h1
  refine mem_stableUnits_of_val_unipotent (L.s 1 * z) (ξ * z) ?_ ?_
  · rw [show ξ * z * (L.s 1 * z) = ξ * (z * (L.s 1 * z)) from by
      noncomm_ring, hzsz, mul_zero]
  · rw [hu]
    congr 1
    rw [show L.s 1 * z * (ξ * z) = L.s 1 * (z * ξ * z) from by
      noncomm_ring, hξ]

end LeavittFamily
end NonsoficGroupsExist
