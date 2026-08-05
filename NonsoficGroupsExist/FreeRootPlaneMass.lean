import NonsoficGroupsExist.FreeRootPlane
import NonsoficGroupsExist.CharacterMass

/-!
# Character masses on the two-root coefficient plane

The two-root coefficient plane at a finite degree stage is parametrized
additively by pairs of stage coefficients.  This file identifies that
parametrization as a homomorphism from the finite coefficient vector space
into the elementary group, and instantiates the finite-field character-mass
calculus on it: positivity, conservation, the displacement identity, and the
moving-mass gap bound all hold for every real orthogonal representation of
the elementary group, at every stage, over every finite coefficient field.
Every nonzero plane character is nontrivial on at least one of the two
coefficient coordinates, which is what the valuation analysis consumes.
-/

namespace NonsoficGroupsExist

namespace FreeRootPlaneMass

open FreeAlgebraDegree

variable (X : Type*) [Fintype X]
variable (K : Type*) [Field K] [Fintype K]
variable (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)

/-- The additive parameter space of the degree-`n` coefficient plane. -/
abbrev PlaneVector := degreeLE X K n × degreeLE X K n

noncomputable instance : Fintype (PlaneVector X K n) :=
  Fintype.ofFinite _

/-- The additive-to-multiplicative parametrization of the plane. -/
noncomputable def planePoint (v : PlaneVector X K n) :
    elementaryGroup (Fin 3) (FreeAlgebra K X) :=
  elementaryRoot i k hik (v.1 : FreeAlgebra K X) *
    elementaryRoot j k hjk (v.2 : FreeAlgebra K X)

omit [Fintype K] in
theorem planePoint_mem (v : PlaneVector X K n) :
    planePoint X K i j k hik hjk n v ∈
      FreeRootPlane.rootPlaneDegreeSubgroup X K i j k hij hik hjk n :=
  ⟨(v.1 : FreeAlgebra K X), v.1.2, (v.2 : FreeAlgebra K X), v.2.2, rfl⟩

omit [Fintype K] in
/-- The parametrization is surjective onto the plane subgroup. -/
theorem planePoint_surjective (g : elementaryGroup (Fin 3) (FreeAlgebra K X))
    (hg : g ∈ FreeRootPlane.rootPlaneDegreeSubgroup X K i j k hij hik hjk n) :
    ∃ v : PlaneVector X K n, planePoint X K i j k hik hjk n v = g := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hg
  exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩

omit [Fintype K] in
/-- The parametrization is additive-to-multiplicative. -/
theorem planePoint_add (v w : PlaneVector X K n) :
    planePoint X K i j k hik hjk n (v + w) =
      planePoint X K i j k hik hjk n v *
        planePoint X K i j k hik hjk n w := by
  unfold planePoint
  have hcoe1 : ((v + w).1 : FreeAlgebra K X) =
      (v.1 : FreeAlgebra K X) + (w.1 : FreeAlgebra K X) := rfl
  have hcoe2 : ((v + w).2 : FreeAlgebra K X) =
      (v.2 : FreeAlgebra K X) + (w.2 : FreeAlgebra K X) := rfl
  rw [hcoe1, hcoe2, ← elementaryRoot_mul i k hik, ← elementaryRoot_mul j k hjk]
  have hcomm := elementaryRoot_commute_of_ne i k j k hik hjk
    hjk.symm hik.symm (w.1 : FreeAlgebra K X) (v.2 : FreeAlgebra K X)
  calc
    (elementaryRoot i k hik (v.1 : FreeAlgebra K X) *
        elementaryRoot i k hik (w.1 : FreeAlgebra K X)) *
      (elementaryRoot j k hjk (v.2 : FreeAlgebra K X) *
        elementaryRoot j k hjk (w.2 : FreeAlgebra K X)) =
      elementaryRoot i k hik (v.1 : FreeAlgebra K X) *
        (elementaryRoot i k hik (w.1 : FreeAlgebra K X) *
          elementaryRoot j k hjk (v.2 : FreeAlgebra K X)) *
        elementaryRoot j k hjk (w.2 : FreeAlgebra K X) := by
      simp only [mul_assoc]
    _ = elementaryRoot i k hik (v.1 : FreeAlgebra K X) *
        (elementaryRoot j k hjk (v.2 : FreeAlgebra K X) *
          elementaryRoot i k hik (w.1 : FreeAlgebra K X)) *
        elementaryRoot j k hjk (w.2 : FreeAlgebra K X) := by
      rw [hcomm.eq]
    _ = (elementaryRoot i k hik (v.1 : FreeAlgebra K X) *
          elementaryRoot j k hjk (v.2 : FreeAlgebra K X)) *
        (elementaryRoot i k hik (w.1 : FreeAlgebra K X) *
          elementaryRoot j k hjk (w.2 : FreeAlgebra K X)) := by
      simp only [mul_assoc]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (rho : elementaryGroup (Fin 3) (FreeAlgebra K X) →* (E ≃ₗᵢ[ℝ] E))

/-- The plane acting on the representation space through its additive
parametrization. -/
noncomputable def planeAction (v : PlaneVector X K n) : E ≃ₗᵢ[ℝ] E :=
  rho (planePoint X K i j k hik hjk n v)

omit [Fintype K] in
theorem planeAction_add (v w : PlaneVector X K n) :
    planeAction X K i j k hik hjk n rho (v + w) =
      planeAction X K i j k hik hjk n rho v *
        planeAction X K i j k hik hjk n rho w := by
  unfold planeAction
  rw [planePoint_add, map_mul]

variable (ψ : AddChar K ℂ)

/-- The character mass of a vector on the degree-`n` plane. -/
noncomputable def planeMass (χ : Module.Dual K (PlaneVector X K n)) (z : E) :
    ℝ :=
  CharacterMass.mass ψ (planeAction X K i j k hik hjk n rho) χ z

theorem planeMass_nonneg (χ : Module.Dual K (PlaneVector X K n)) (z : E) :
    0 ≤ planeMass X K i j k hik hjk n rho ψ χ z :=
  CharacterMass.mass_nonneg ψ _ (planeAction_add X K i j k hik hjk n rho) χ z

/-- Conservation of plane masses. -/
theorem sum_planeMass (hψ : ψ ≠ 1) (z : E) :
    ∑ χ : Module.Dual K (PlaneVector X K n),
      planeMass X K i j k hik hjk n rho ψ χ z = ‖z‖ ^ 2 := by
  classical
  exact CharacterMass.sum_mass ψ _
    (planeAction_add X K i j k hik hjk n rho) hψ z

/-- The displacement identity on the plane. -/
theorem norm_planeAction_sub_sq (hψ : ψ ≠ 1) (z : E)
    (w : PlaneVector X K n) :
    ‖rho (planePoint X K i j k hik hjk n w) z - z‖ ^ 2 =
      ∑ χ : Module.Dual K (PlaneVector X K n),
        2 * (1 - (ψ (χ w)).re) *
          planeMass X K i j k hik hjk n rho ψ χ z := by
  classical
  exact CharacterMass.norm_action_sub_sq ψ _
    (planeAction_add X K i j k hik hjk n rho) hψ z w

/-- The moving-mass gap bound on the plane. -/
theorem mul_sum_planeMass_le_of_gap (hψ : ψ ≠ 1) (z : E)
    (w : PlaneVector X K n)
    (S : Finset (Module.Dual K (PlaneVector X K n))) (δ : ℝ)
    (hδ : ∀ χ ∈ S, δ ≤ 2 * (1 - (ψ (χ w)).re)) :
    δ * ∑ χ ∈ S, planeMass X K i j k hik hjk n rho ψ χ z ≤
      ‖rho (planePoint X K i j k hik hjk n w) z - z‖ ^ 2 := by
  classical
  exact CharacterMass.mul_sum_mass_le_of_gap ψ _
    (planeAction_add X K i j k hik hjk n rho) hψ z w S δ hδ

/-- The first coordinate functional of a plane character. -/
noncomputable def firstCoordinateChar
    (χ : Module.Dual K (PlaneVector X K n)) :
    Module.Dual K (degreeLE X K n) :=
  χ.comp (LinearMap.inl K (degreeLE X K n) (degreeLE X K n))

/-- The second coordinate functional of a plane character. -/
noncomputable def secondCoordinateChar
    (χ : Module.Dual K (PlaneVector X K n)) :
    Module.Dual K (degreeLE X K n) :=
  χ.comp (LinearMap.inr K (degreeLE X K n) (degreeLE X K n))

omit [Fintype K] in
/-- Every plane character is the sum of its two coordinate functionals. -/
theorem char_eq_coordinate_sum
    (χ : Module.Dual K (PlaneVector X K n)) (v : PlaneVector X K n) :
    χ v = firstCoordinateChar X K n χ v.1 +
      secondCoordinateChar X K n χ v.2 := by
  unfold firstCoordinateChar secondCoordinateChar
  rw [LinearMap.comp_apply, LinearMap.comp_apply, ← map_add]
  congr 1
  change v = (v.1, 0) + (0, v.2)
  ext <;> simp

omit [Fintype K] in
/-- Every nonzero plane character is nontrivial on at least one of the two
coefficient coordinates. -/
theorem coordinateChar_ne_zero_of_ne_zero
    (χ : Module.Dual K (PlaneVector X K n)) (hχ : χ ≠ 0) :
    firstCoordinateChar X K n χ ≠ 0 ∨
      secondCoordinateChar X K n χ ≠ 0 := by
  by_contra hboth
  push Not at hboth
  apply hχ
  refine LinearMap.ext fun v ↦ ?_
  rw [char_eq_coordinate_sum X K n χ v, hboth.1, hboth.2]
  simp

end FreeRootPlaneMass

end NonsoficGroupsExist
