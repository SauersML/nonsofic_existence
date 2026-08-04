import NonsoficGroupsExist.FiniteGroupAverage

/-!
# The central-fixed part of the finite class-two angle estimate

For two subgroups generating a finite class-two group, the components of
their fixed spaces on which the commutator subgroup acts trivially are
exactly orthogonal in a representation without invariant vectors.  This is
the zero-angle half of the finite-stage argument; the complementary central
moving part carries the quantitative `1 / sqrt 2` estimate.
-/

namespace NonsoficGroupsExist

open scoped commutatorElement

universe u v

namespace FiniteClassTwoOrthogonality

variable {G : Type u} [Group G]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- On the part fixed by the commutator subgroup, the fixed spaces of the
two generating subgroups are orthogonal.  The proof uses the literal finite
average over `X`: modulo `C`, every point in the `X`-orbit of a `Y`-fixed
vector is still `Y`-fixed. -/
theorem inner_eq_zero_of_fixed_center
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (X Y C : Subgroup G) [Finite X]
    (hgen : X ⊔ Y = ⊤)
    (hcomm : ⁅Y, X⁆ ≤ C)
    (hXnorm : X ≤ Subgroup.normalizer (C : Set G))
    (hno : IsKazhdanPair.HasNoInvariantVectors G rho)
    {u v : E}
    (huX : u ∈ KazhdanFixedSpace.fixedSubspace rho X)
    (hvY : v ∈ KazhdanFixedSpace.fixedSubspace rho Y)
    (hvC : v ∈ KazhdanFixedSpace.fixedSubspace rho C) :
    inner ℝ u v = 0 := by
  let rhoX := KazhdanFixedSpace.restrictRepresentation rho X
  let w : E := FiniteGroupAverage.orbitAverage rhoX v
  have hwX : w ∈ KazhdanFixedSpace.fixedSubspace rho X := by
    rw [KazhdanFixedSpace.mem_fixedSubspace_iff]
    intro x hx
    let xX : X := ⟨x, hx⟩
    exact FiniteGroupAverage.orbitAverage_fixed rhoX v xX
  have hwY : w ∈ KazhdanFixedSpace.fixedSubspace rho Y := by
    rw [KazhdanFixedSpace.mem_fixedSubspace_iff]
    intro y hy
    letI := Fintype.ofFinite X
    unfold w FiniteGroupAverage.orbitAverage
    rw [map_smul, map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    change rho y (rho x.1 v) = rho x.1 v
    let c : G := ⁅y, x.1⁆
    have hc : c ∈ C :=
      hcomm (Subgroup.commutator_mem_commutator hy x.2)
    have hcconj : x.1⁻¹ * c * x.1 ∈ C :=
      (Subgroup.mem_normalizer_iff''.mp (hXnorm x.2) c).mp hc
    have hyfix : rho y v = v :=
      (KazhdanFixedSpace.mem_fixedSubspace_iff rho Y v).mp hvY y hy
    have hcfix : rho (x.1⁻¹ * c * x.1) v = v :=
      (KazhdanFixedSpace.mem_fixedSubspace_iff rho C v).mp hvC
        (x.1⁻¹ * c * x.1) hcconj
    calc
      rho y (rho x.1 v) = rho (y * x.1) v := by
        change (rho y * rho x.1) v = rho (y * x.1) v
        rw [← map_mul]
      _ = rho (c * x.1 * y) v := by
        congr 2
        simp [c, commutatorElement_def, mul_assoc]
      _ = rho c (rho x.1 (rho y v)) := by simp [map_mul]
      _ = rho c (rho x.1 v) := by rw [hyfix]
      _ = rho (c * x.1) v := by
        change (rho c * rho x.1) v = rho (c * x.1) v
        rw [← map_mul]
      _ = rho (x.1 * (x.1⁻¹ * c * x.1)) v := by
        congr 2
        group
      _ = rho x.1 (rho (x.1⁻¹ * c * x.1) v) := by
        change rho (x.1 * (x.1⁻¹ * c * x.1)) v =
          (rho x.1 * rho (x.1⁻¹ * c * x.1)) v
        rw [map_mul]
      _ = rho x.1 v := by rw [hcfix]
  have hwTop : w ∈ KazhdanFixedSpace.fixedSubspace rho ⊤ := by
    rw [← hgen, KazhdanFixedSpace.fixedSubspace_sup]
    exact ⟨hwX, hwY⟩
  have hw0 : w = 0 := by
    apply hno w
    intro g
    exact (KazhdanFixedSpace.mem_fixedSubspace_iff rho ⊤ w).mp hwTop
      g (Subgroup.mem_top g)
  have huFixed : ∀ x : X, rhoX x u = u := by
    intro x
    exact (KazhdanFixedSpace.mem_fixedSubspace_iff rho X u).mp huX x.1 x.2
  have havg := FiniteGroupAverage.inner_orbitAverage_eq_of_fixed_right
    rhoX v u huFixed
  change inner ℝ w u = inner ℝ v u at havg
  rw [hw0, inner_zero_left] at havg
  rw [real_inner_comm]
  exact havg.symm

end FiniteClassTwoOrthogonality
end NonsoficGroupsExist
