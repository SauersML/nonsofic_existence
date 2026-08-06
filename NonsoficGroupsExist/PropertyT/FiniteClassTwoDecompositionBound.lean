import NonsoficGroupsExist.PropertyT.FiniteOrbitRepresentation
import NonsoficGroupsExist.Kazhdan.HilbertEpsilonOrthogonality
import NonsoficGroupsExist.PropertyT.OrthogonalRepresentationDecomposition

/-!
# Finite class-two averaging bound

The scalar `1 / sqrt 2` estimate is obtained on the finite-dimensional span
of the two group orbits by orthogonal irreducible decomposition.  Central
commutators may have any one positive bounded exponent, so the bound applies
over every finite characteristic, not only exponent two.
-/

namespace NonsoficGroupsExist

open scoped commutatorElement

universe u v

namespace FiniteClassTwoDecompositionBound

variable {G : Type u} [Group G] [Finite G]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The full finite class-two `1 / sqrt 2` orthogonality theorem for
arbitrary real Hilbert spaces, with central commutators of one positive
bounded exponent.  The finite-dimensional estimate is applied on the span of
the two finite group orbits. -/
theorem epsilonOrthogonal
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (X Y C : Subgroup G)
    (n : ℕ) (hn : 0 < n)
    (hgen : X ⊔ Y = ⊤)
    (hcomm : ⁅Y, X⁆ ≤ C)
    (hcentral : C ≤ Subgroup.center G)
    (hexp : ∀ c ∈ C, c ^ n = 1)
    (hno : IsKazhdanPair.HasNoInvariantVectors G rho) :
    HilbertEpsilonOrthogonality.EpsilonOrthogonal
      (KazhdanFixedSpace.fixedSubspace rho X)
      (KazhdanFixedSpace.fixedSubspace rho Y)
      (Real.sqrt 2)⁻¹ := by
  intro u hu v hv
  let W := FiniteOrbitRepresentation.orbitSpan rho u v
  let rhoW := FiniteOrbitRepresentation.representation rho u v
  let uW : W := ⟨u, FiniteOrbitRepresentation.left_mem_orbitSpan rho u v⟩
  let vW : W := ⟨v, FiniteOrbitRepresentation.right_mem_orbitSpan rho u v⟩
  let q : W := FiniteGroupAverage.orbitAverage
    (KazhdanFixedSpace.restrictRepresentation rhoW X) vW
  letI : FiniteDimensional ℝ W :=
    FiniteOrbitRepresentation.orbitSpan_finiteDimensional rho u v
  have hnoW : IsKazhdanPair.HasNoInvariantVectors G rhoW :=
    FiniteOrbitRepresentation.representation_hasNoInvariantVectors rho u v hno
  have huW : uW ∈ KazhdanFixedSpace.fixedSubspace rhoW X := by
    rw [KazhdanFixedSpace.mem_fixedSubspace_iff]
    intro x hx
    apply Subtype.ext
    exact (KazhdanFixedSpace.mem_fixedSubspace_iff rho X u).mp hu x hx
  have hvW : vW ∈ KazhdanFixedSpace.fixedSubspace rhoW Y := by
    rw [KazhdanFixedSpace.mem_fixedSubspace_iff]
    intro y hy
    apply Subtype.ext
    exact (KazhdanFixedSpace.mem_fixedSubspace_iff rho Y v).mp hv y hy
  have hsq : ‖q‖ ^ 2 ≤ (1 / 2 : ℝ) * ‖vW‖ ^ 2 :=
    OrthogonalRepresentationDecomposition.norm_orbitAverage_sq_le_half_boundedExponent
      rhoW X Y C n hn hgen hcomm hcentral hexp hnoW hvW
  have hq : ‖q‖ ≤ (Real.sqrt 2)⁻¹ * ‖vW‖ :=
    FiniteClassTwoOrthogonality.le_inv_sqrt_two_mul_of_sq_le_half
      (norm_nonneg q) (norm_nonneg vW) hsq
  have huFixed : ∀ x : X,
      (KazhdanFixedSpace.restrictRepresentation rhoW X) x uW = uW := by
    intro x
    exact (KazhdanFixedSpace.mem_fixedSubspace_iff rhoW X uW).mp huW x.1 x.2
  have havg := FiniteGroupAverage.inner_orbitAverage_eq_of_fixed_right
    (KazhdanFixedSpace.restrictRepresentation rhoW X) vW uW huFixed
  change inner ℝ q uW = inner ℝ vW uW at havg
  have hinner : inner ℝ u v = inner ℝ q uW := by
    calc
      inner ℝ u v = inner ℝ v u := real_inner_comm v u
      _ = inner ℝ vW uW := rfl
      _ = inner ℝ q uW := havg.symm
  rw [hinner]
  calc
    |inner ℝ q uW| ≤ ‖q‖ * ‖uW‖ := abs_real_inner_le_norm q uW
    _ ≤ ((Real.sqrt 2)⁻¹ * ‖vW‖) * ‖uW‖ :=
      mul_le_mul_of_nonneg_right hq (norm_nonneg uW)
    _ = (Real.sqrt 2)⁻¹ * ‖u‖ * ‖v‖ := by
      change (Real.sqrt 2)⁻¹ * ‖v‖ * ‖u‖ =
        (Real.sqrt 2)⁻¹ * ‖u‖ * ‖v‖
      ring

end FiniteClassTwoDecompositionBound
end NonsoficGroupsExist
