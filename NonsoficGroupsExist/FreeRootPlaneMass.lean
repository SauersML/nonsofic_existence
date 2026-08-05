import NonsoficGroupsExist.FreeRootPlane
import NonsoficGroupsExist.FreeRootFunctionalValuation
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

open Classical in
/-- **Scalar-orbit moving-mass control on the plane**: the total mass of
all characters nonvanishing at a plane vector is bounded, at the
character's positive gap constant, by the summed squared displacements of
the scalar multiples of that vector. -/
theorem gap_mul_sum_planeMass_ne_zero_le (hψ : ψ ≠ 1) (z : E)
    (w : PlaneVector X K n) :
    CharacterMass.gap ψ *
        ∑ χ ∈ Finset.univ.filter
          (fun χ : Module.Dual K (PlaneVector X K n) ↦ χ w ≠ 0),
          planeMass X K i j k hik hjk n rho ψ χ z ≤
      ∑ t : K,
        ‖rho (planePoint X K i j k hik hjk n (t • w)) z - z‖ ^ 2 :=
  CharacterMass.gap_mul_sum_mass_ne_zero_le ψ _
    (planeAction_add X K i j k hik hjk n rho) hψ z w

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


/-! ### The two adjacent shears as linear stage maps, and mass transport -/

open FreeRootFunctionalValuation in
/-- The forward adjacent shear on plane coefficients:
`(a, b) ↦ (a + x·b, b)`, landing in the next stage. -/
noncomputable def forwardShear (x : X) :
    PlaneVector X K n →ₗ[K] PlaneVector X K (n + 1) :=
  LinearMap.prod
    ((stageInclusion X K n).comp (LinearMap.fst K _ _) +
      (generatorMulLinear X K n x).comp (LinearMap.snd K _ _))
    ((stageInclusion X K n).comp (LinearMap.snd K _ _))

open FreeRootFunctionalValuation in
/-- The opposite adjacent shear on plane coefficients:
`(a, b) ↦ (a, x·a + b)`, landing in the next stage. -/
noncomputable def oppositeShear (x : X) :
    PlaneVector X K n →ₗ[K] PlaneVector X K (n + 1) :=
  LinearMap.prod
    ((stageInclusion X K n).comp (LinearMap.fst K _ _))
    ((generatorMulLinear X K n x).comp (LinearMap.fst K _ _) +
      (stageInclusion X K n).comp (LinearMap.snd K _ _))

omit [Fintype K] in
/-- Conjugation by the forward adjacent generator root realizes the forward
shear on plane points. -/
theorem planePoint_forwardShear (x : X) (v : PlaneVector X K n) :
    elementaryRoot i j hij (FreeAlgebra.ι K x) *
        planePoint X K i j k hik hjk n v *
        (elementaryRoot i j hij (FreeAlgebra.ι K x))⁻¹ =
      planePoint X K i j k hik hjk (n + 1)
        (forwardShear X K n x v) := by
  set g := elementaryRoot i j hij (FreeAlgebra.ι K x) with hg
  have hsplit : g * planePoint X K i j k hik hjk n v * g⁻¹ =
      (g * elementaryRoot i k hik (v.1 : FreeAlgebra K X) * g⁻¹) *
        (g * elementaryRoot j k hjk (v.2 : FreeAlgebra K X) * g⁻¹) := by
    unfold planePoint
    group
  have hfirst : g * elementaryRoot i k hik (v.1 : FreeAlgebra K X) * g⁻¹ =
      elementaryRoot i k hik (v.1 : FreeAlgebra K X) := by
    have hcomm := elementaryRoot_commute_of_ne i j i k hij hik
      hij.symm hik.symm (FreeAlgebra.ι K x) (v.1 : FreeAlgebra K X)
    rw [hg, hcomm.eq]
    group
  have hsecond : g * elementaryRoot j k hjk (v.2 : FreeAlgebra K X) * g⁻¹ =
      elementaryRoot i k hik
          (FreeAlgebra.ι K x * (v.2 : FreeAlgebra K X)) *
        elementaryRoot j k hjk (v.2 : FreeAlgebra K X) := by
    rw [hg]
    exact FreeRootActions.conjugate_by_generator X K i j k hij hjk hik x _
  rw [hsplit, hfirst, hsecond]
  unfold planePoint forwardShear
  rw [show ((LinearMap.prod
      ((FreeRootFunctionalValuation.stageInclusion X K n).comp
        (LinearMap.fst K _ _) +
        (FreeRootFunctionalValuation.generatorMulLinear X K n x).comp
          (LinearMap.snd K _ _))
      ((FreeRootFunctionalValuation.stageInclusion X K n).comp
        (LinearMap.snd K _ _))) v).1 =
    FreeRootFunctionalValuation.stageInclusion X K n v.1 +
      FreeRootFunctionalValuation.generatorMulLinear X K n x v.2 from rfl]
  rw [show (((FreeRootFunctionalValuation.stageInclusion X K n v.1 +
      FreeRootFunctionalValuation.generatorMulLinear X K n x v.2) :
        degreeLE X K (n + 1)) : FreeAlgebra K X) =
    (v.1 : FreeAlgebra K X) +
      FreeAlgebra.ι K x * (v.2 : FreeAlgebra K X) from rfl]
  rw [← elementaryRoot_mul i k hik]
  rw [show ((LinearMap.prod
      ((FreeRootFunctionalValuation.stageInclusion X K n).comp
        (LinearMap.fst K _ _) +
        (FreeRootFunctionalValuation.generatorMulLinear X K n x).comp
          (LinearMap.snd K _ _))
      ((FreeRootFunctionalValuation.stageInclusion X K n).comp
        (LinearMap.snd K _ _)) : PlaneVector X K n →ₗ[K]
          PlaneVector X K (n + 1)) v).2 =
    FreeRootFunctionalValuation.stageInclusion X K n v.2 from rfl]
  rw [show ((FreeRootFunctionalValuation.stageInclusion X K n v.2 :
      degreeLE X K (n + 1)) : FreeAlgebra K X) =
    (v.2 : FreeAlgebra K X) from rfl]
  rw [mul_assoc]

omit [Fintype K] in
/-- Conjugation by the opposite adjacent generator root realizes the
opposite shear on plane points. -/
theorem planePoint_oppositeShear (x : X) (v : PlaneVector X K n) :
    elementaryRoot j i hij.symm (FreeAlgebra.ι K x) *
        planePoint X K i j k hik hjk n v *
        (elementaryRoot j i hij.symm (FreeAlgebra.ι K x))⁻¹ =
      planePoint X K i j k hik hjk (n + 1)
        (oppositeShear X K n x v) := by
  set g := elementaryRoot j i hij.symm (FreeAlgebra.ι K x) with hg
  have hsplit : g * planePoint X K i j k hik hjk n v * g⁻¹ =
      (g * elementaryRoot i k hik (v.1 : FreeAlgebra K X) * g⁻¹) *
        (g * elementaryRoot j k hjk (v.2 : FreeAlgebra K X) * g⁻¹) := by
    unfold planePoint
    group
  have hfirst : g * elementaryRoot i k hik (v.1 : FreeAlgebra K X) * g⁻¹ =
      elementaryRoot i k hik (v.1 : FreeAlgebra K X) *
        elementaryRoot j k hjk
          (FreeAlgebra.ι K x * (v.1 : FreeAlgebra K X)) := by
    rw [hg, FreeRootActions.conjugate_by_generator X K j i k
      hij.symm hik hjk x _]
    exact (elementaryRoot_commute_of_ne j k i k hjk hik
      hik.symm hjk.symm _ _).eq
  have hsecond : g * elementaryRoot j k hjk (v.2 : FreeAlgebra K X) * g⁻¹ =
      elementaryRoot j k hjk (v.2 : FreeAlgebra K X) := by
    have hcomm := elementaryRoot_commute_of_ne j i j k hij.symm hjk
      hij hjk.symm (FreeAlgebra.ι K x) (v.2 : FreeAlgebra K X)
    rw [hg, hcomm.eq]
    group
  rw [hsplit, hfirst, hsecond]
  unfold planePoint oppositeShear
  rw [show ((LinearMap.prod
      ((FreeRootFunctionalValuation.stageInclusion X K n).comp
        (LinearMap.fst K _ _))
      ((FreeRootFunctionalValuation.generatorMulLinear X K n x).comp
        (LinearMap.fst K _ _) +
        (FreeRootFunctionalValuation.stageInclusion X K n).comp
          (LinearMap.snd K _ _)) : PlaneVector X K n →ₗ[K]
            PlaneVector X K (n + 1)) v).1 =
    FreeRootFunctionalValuation.stageInclusion X K n v.1 from rfl]
  rw [show ((FreeRootFunctionalValuation.stageInclusion X K n v.1 :
      degreeLE X K (n + 1)) : FreeAlgebra K X) =
    (v.1 : FreeAlgebra K X) from rfl]
  rw [show ((LinearMap.prod
      ((FreeRootFunctionalValuation.stageInclusion X K n).comp
        (LinearMap.fst K _ _))
      ((FreeRootFunctionalValuation.generatorMulLinear X K n x).comp
        (LinearMap.fst K _ _) +
        (FreeRootFunctionalValuation.stageInclusion X K n).comp
          (LinearMap.snd K _ _)) : PlaneVector X K n →ₗ[K]
            PlaneVector X K (n + 1)) v).2 =
    FreeRootFunctionalValuation.generatorMulLinear X K n x v.1 +
      FreeRootFunctionalValuation.stageInclusion X K n v.2 from rfl]
  rw [show (((FreeRootFunctionalValuation.generatorMulLinear X K n x v.1 +
      FreeRootFunctionalValuation.stageInclusion X K n v.2) :
        degreeLE X K (n + 1)) : FreeAlgebra K X) =
    FreeAlgebra.ι K x * (v.1 : FreeAlgebra K X) +
      (v.2 : FreeAlgebra K X) from rfl]
  rw [← elementaryRoot_mul j k hjk, mul_assoc]

open Classical in
/-- **Forward mass transport**: the stage-`n` plane mass of `z` at a coarse
character is the total stage-`n+1` plane mass of the conjugated vector over
the forward dual-shear fiber. -/
theorem planeMass_eq_sum_fiber_forwardShear (hψ : ψ ≠ 1) (x : X) (z : E)
    (χ : Module.Dual K (PlaneVector X K n)) :
    planeMass X K i j k hik hjk n rho ψ χ z =
      ∑ χ' ∈ Finset.univ.filter
          (fun χ' : Module.Dual K (PlaneVector X K (n + 1)) ↦
            χ'.comp (forwardShear X K n x) = χ),
        planeMass X K i j k hik hjk (n + 1) rho ψ χ'
          (rho (elementaryRoot i j hij (FreeAlgebra.ι K x)) z) := by
  set u := rho (elementaryRoot i j hij (FreeAlgebra.ι K x)) with hu
  have hconj : ∀ v : PlaneVector X K n,
      planeAction X K i j k hik hjk n rho v =
        u⁻¹ * planeAction X K i j k hik hjk (n + 1) rho
          (forwardShear X K n x v) * (u⁻¹)⁻¹ := by
    intro v
    unfold planeAction
    rw [inv_inv, hu, ← map_inv, ← map_mul, ← map_mul,
      ← planePoint_forwardShear X K i j k hij hik hjk n x v]
    congr 1
    group
  have hz : z = u⁻¹ (u z) := by
    change z = (u⁻¹ * u) z
    rw [inv_mul_cancel]
    rfl
  calc
    planeMass X K i j k hik hjk n rho ψ χ z =
        CharacterMass.mass ψ
          (fun v ↦ u⁻¹ * planeAction X K i j k hik hjk (n + 1) rho
            (forwardShear X K n x v) * (u⁻¹)⁻¹) χ (u⁻¹ (u z)) := by
      rw [planeMass, ← hz]
      congr 1
      funext v
      exact hconj v
    _ = CharacterMass.mass ψ
        (fun v ↦ planeAction X K i j k hik hjk (n + 1) rho
          (forwardShear X K n x v)) χ (u z) :=
      CharacterMass.mass_conj ψ _ u⁻¹ χ (u z)
    _ = ∑ χ' ∈ Finset.univ.filter
        (fun χ' : Module.Dual K (PlaneVector X K (n + 1)) ↦
          χ'.comp (forwardShear X K n x) = χ),
        planeMass X K i j k hik hjk (n + 1) rho ψ χ' (u z) :=
      (CharacterMass.sum_mass_fiber_comp ψ _
        (planeAction_add X K i j k hik hjk (n + 1) rho) hψ
        (forwardShear X K n x) (u z) χ).symm

open Classical in
/-- **Opposite mass transport**: the same law along the opposite dual
shear. -/
theorem planeMass_eq_sum_fiber_oppositeShear (hψ : ψ ≠ 1) (x : X) (z : E)
    (χ : Module.Dual K (PlaneVector X K n)) :
    planeMass X K i j k hik hjk n rho ψ χ z =
      ∑ χ' ∈ Finset.univ.filter
          (fun χ' : Module.Dual K (PlaneVector X K (n + 1)) ↦
            χ'.comp (oppositeShear X K n x) = χ),
        planeMass X K i j k hik hjk (n + 1) rho ψ χ'
          (rho (elementaryRoot j i hij.symm (FreeAlgebra.ι K x)) z) := by
  set u := rho (elementaryRoot j i hij.symm (FreeAlgebra.ι K x)) with hu
  have hconj : ∀ v : PlaneVector X K n,
      planeAction X K i j k hik hjk n rho v =
        u⁻¹ * planeAction X K i j k hik hjk (n + 1) rho
          (oppositeShear X K n x v) * (u⁻¹)⁻¹ := by
    intro v
    unfold planeAction
    rw [inv_inv, hu, ← map_inv, ← map_mul, ← map_mul,
      ← planePoint_oppositeShear X K i j k hij hik hjk n x v]
    congr 1
    group
  have hz : z = u⁻¹ (u z) := by
    change z = (u⁻¹ * u) z
    rw [inv_mul_cancel]
    rfl
  calc
    planeMass X K i j k hik hjk n rho ψ χ z =
        CharacterMass.mass ψ
          (fun v ↦ u⁻¹ * planeAction X K i j k hik hjk (n + 1) rho
            (oppositeShear X K n x v) * (u⁻¹)⁻¹) χ (u⁻¹ (u z)) := by
      rw [planeMass, ← hz]
      congr 1
      funext v
      exact hconj v
    _ = CharacterMass.mass ψ
        (fun v ↦ planeAction X K i j k hik hjk (n + 1) rho
          (oppositeShear X K n x v)) χ (u z) :=
      CharacterMass.mass_conj ψ _ u⁻¹ χ (u z)
    _ = ∑ χ' ∈ Finset.univ.filter
        (fun χ' : Module.Dual K (PlaneVector X K (n + 1)) ↦
          χ'.comp (oppositeShear X K n x) = χ),
        planeMass X K i j k hik hjk (n + 1) rho ψ χ' (u z) :=
      (CharacterMass.sum_mass_fiber_comp ψ _
        (planeAction_add X K i j k hik hjk (n + 1) rho) hψ
        (oppositeShear X K n x) (u z) χ).symm

open FreeRootFunctionalValuation in
omit [Fintype K] in
/-- The forward dual shear on the first coordinate functional: restriction
to the previous stage. -/
theorem firstCoordinateChar_comp_forwardShear (x : X)
    (χ' : Module.Dual K (PlaneVector X K (n + 1))) :
    firstCoordinateChar X K n (χ'.comp (forwardShear X K n x)) =
      restrictSucc X K (firstCoordinateChar X K (n + 1) χ') := by
  refine LinearMap.ext fun a ↦ ?_
  show χ' (forwardShear X K n x (a, 0)) =
    χ' (stageInclusion X K n a, 0)
  congr 1
  show (stageInclusion X K n a + generatorMulLinear X K n x 0,
      stageInclusion X K n (0 : degreeLE X K n)) =
    (stageInclusion X K n a, 0)
  rw [map_zero, map_zero, add_zero]

open FreeRootFunctionalValuation in
omit [Fintype K] in
/-- The forward dual shear on the second coordinate functional: the
generator-derived first functional plus the restricted second functional —
the algebraic dual shear of the valuation analysis. -/
theorem secondCoordinateChar_comp_forwardShear (x : X)
    (χ' : Module.Dual K (PlaneVector X K (n + 1))) :
    secondCoordinateChar X K n (χ'.comp (forwardShear X K n x)) =
      leftDerived X K (firstCoordinateChar X K (n + 1) χ') x +
        restrictSucc X K (secondCoordinateChar X K (n + 1) χ') := by
  refine LinearMap.ext fun b ↦ ?_
  show χ' (forwardShear X K n x (0, b)) =
    χ' (generatorMulLinear X K n x b, 0) +
      χ' (0, stageInclusion X K n b)
  rw [← map_add]
  congr 1
  show (stageInclusion X K n 0 + generatorMulLinear X K n x b,
      stageInclusion X K n b) =
    (generatorMulLinear X K n x b + 0, 0 + stageInclusion X K n b)
  rw [map_zero, zero_add, add_zero, zero_add]

open FreeRootFunctionalValuation in
omit [Fintype K] in
/-- The opposite dual shear on the first coordinate functional. -/
theorem firstCoordinateChar_comp_oppositeShear (x : X)
    (χ' : Module.Dual K (PlaneVector X K (n + 1))) :
    firstCoordinateChar X K n (χ'.comp (oppositeShear X K n x)) =
      restrictSucc X K (firstCoordinateChar X K (n + 1) χ') +
        leftDerived X K (secondCoordinateChar X K (n + 1) χ') x := by
  refine LinearMap.ext fun a ↦ ?_
  show χ' (oppositeShear X K n x (a, 0)) =
    χ' (stageInclusion X K n a, 0) +
      χ' (0, generatorMulLinear X K n x a)
  rw [← map_add]
  congr 1
  show (stageInclusion X K n a,
      generatorMulLinear X K n x a + stageInclusion X K n 0) =
    (stageInclusion X K n a + 0, 0 + generatorMulLinear X K n x a)
  rw [map_zero, add_zero, add_zero, zero_add]

open FreeRootFunctionalValuation in
omit [Fintype K] in
/-- The opposite dual shear on the second coordinate functional. -/
theorem secondCoordinateChar_comp_oppositeShear (x : X)
    (χ' : Module.Dual K (PlaneVector X K (n + 1))) :
    secondCoordinateChar X K n (χ'.comp (oppositeShear X K n x)) =
      restrictSucc X K (secondCoordinateChar X K (n + 1) χ') := by
  refine LinearMap.ext fun b ↦ ?_
  show χ' (oppositeShear X K n x (0, b)) =
    χ' (0, stageInclusion X K n b)
  congr 1
  show (stageInclusion X K n (0 : degreeLE X K n),
      generatorMulLinear X K n x 0 + stageInclusion X K n b) =
    (0, stageInclusion X K n b)
  rw [map_zero, map_zero, zero_add]


/-! ### Same-stage unit shears and the region transport into `B` -/

/-- The forward same-stage unit shear `(a, b) ↦ (a + b, b)`. -/
noncomputable def unitShearForward :
    PlaneVector X K n ≃ₗ[K] PlaneVector X K n :=
  LinearEquiv.ofLinear
    (LinearMap.prod (LinearMap.fst K _ _ + LinearMap.snd K _ _)
      (LinearMap.snd K _ _))
    (LinearMap.prod (LinearMap.fst K _ _ - LinearMap.snd K _ _)
      (LinearMap.snd K _ _))
    (by
      refine LinearMap.ext fun v ↦ ?_
      apply Prod.ext
      · show v.1 - v.2 + v.2 = v.1
        abel
      · rfl)
    (by
      refine LinearMap.ext fun v ↦ ?_
      apply Prod.ext
      · show v.1 + v.2 - v.2 = v.1
        abel
      · rfl)

/-- The opposite same-stage unit shear `(a, b) ↦ (a, a + b)`. -/
noncomputable def unitShearOpposite :
    PlaneVector X K n ≃ₗ[K] PlaneVector X K n :=
  LinearEquiv.ofLinear
    (LinearMap.prod (LinearMap.fst K _ _)
      (LinearMap.fst K _ _ + LinearMap.snd K _ _))
    (LinearMap.prod (LinearMap.fst K _ _)
      (LinearMap.snd K _ _ - LinearMap.fst K _ _))
    (by
      refine LinearMap.ext fun v ↦ ?_
      apply Prod.ext
      · rfl
      · show v.1 + (v.2 - v.1) = v.2
        abel)
    (by
      refine LinearMap.ext fun v ↦ ?_
      apply Prod.ext
      · rfl
      · show v.1 + v.2 - v.1 = v.2
        abel)

omit [Fintype K] in
/-- Conjugation by the forward unit root realizes the forward unit shear on
plane points. -/
theorem planePoint_unitShearForward (v : PlaneVector X K n) :
    elementaryRoot i j hij (1 : FreeAlgebra K X) *
        planePoint X K i j k hik hjk n v *
        (elementaryRoot i j hij (1 : FreeAlgebra K X))⁻¹ =
      planePoint X K i j k hik hjk n (unitShearForward X K n v) := by
  set g := elementaryRoot i j hij (1 : FreeAlgebra K X) with hg
  have hsplit : g * planePoint X K i j k hik hjk n v * g⁻¹ =
      (g * elementaryRoot i k hik (v.1 : FreeAlgebra K X) * g⁻¹) *
        (g * elementaryRoot j k hjk (v.2 : FreeAlgebra K X) * g⁻¹) := by
    unfold planePoint
    group
  have hfirst : g * elementaryRoot i k hik (v.1 : FreeAlgebra K X) * g⁻¹ =
      elementaryRoot i k hik (v.1 : FreeAlgebra K X) := by
    have hcomm := elementaryRoot_commute_of_ne i j i k hij hik
      hij.symm hik.symm (1 : FreeAlgebra K X) (v.1 : FreeAlgebra K X)
    rw [hg, hcomm.eq]
    group
  have hsecond : g * elementaryRoot j k hjk (v.2 : FreeAlgebra K X) * g⁻¹ =
      elementaryRoot i k hik (v.2 : FreeAlgebra K X) *
        elementaryRoot j k hjk (v.2 : FreeAlgebra K X) := by
    rw [hg, elementaryRoot_conjugate i j k hij hjk hik
      (1 : FreeAlgebra K X) (v.2 : FreeAlgebra K X), one_mul]
  rw [hsplit, hfirst, hsecond]
  unfold planePoint
  rw [show ((unitShearForward X K n v).1 : FreeAlgebra K X) =
    (v.1 : FreeAlgebra K X) + (v.2 : FreeAlgebra K X) from rfl]
  rw [show ((unitShearForward X K n v).2 : FreeAlgebra K X) =
    (v.2 : FreeAlgebra K X) from rfl]
  rw [← elementaryRoot_mul i k hik, mul_assoc]

omit [Fintype K] in
/-- Conjugation by the opposite unit root realizes the opposite unit shear
on plane points. -/
theorem planePoint_unitShearOpposite (v : PlaneVector X K n) :
    elementaryRoot j i hij.symm (1 : FreeAlgebra K X) *
        planePoint X K i j k hik hjk n v *
        (elementaryRoot j i hij.symm (1 : FreeAlgebra K X))⁻¹ =
      planePoint X K i j k hik hjk n (unitShearOpposite X K n v) := by
  set g := elementaryRoot j i hij.symm (1 : FreeAlgebra K X) with hg
  have hsplit : g * planePoint X K i j k hik hjk n v * g⁻¹ =
      (g * elementaryRoot i k hik (v.1 : FreeAlgebra K X) * g⁻¹) *
        (g * elementaryRoot j k hjk (v.2 : FreeAlgebra K X) * g⁻¹) := by
    unfold planePoint
    group
  have hfirst : g * elementaryRoot i k hik (v.1 : FreeAlgebra K X) * g⁻¹ =
      elementaryRoot i k hik (v.1 : FreeAlgebra K X) *
        elementaryRoot j k hjk (v.1 : FreeAlgebra K X) := by
    rw [hg, elementaryRoot_conjugate j i k hij.symm hik hjk
      (1 : FreeAlgebra K X) (v.1 : FreeAlgebra K X), one_mul]
    exact (elementaryRoot_commute_of_ne j k i k hjk hik
      hik.symm hjk.symm _ _).eq
  have hsecond : g * elementaryRoot j k hjk (v.2 : FreeAlgebra K X) * g⁻¹ =
      elementaryRoot j k hjk (v.2 : FreeAlgebra K X) := by
    have hcomm := elementaryRoot_commute_of_ne j i j k hij.symm hjk
      hij hjk.symm (1 : FreeAlgebra K X) (v.2 : FreeAlgebra K X)
    rw [hg, hcomm.eq]
    group
  rw [hsplit, hfirst, hsecond]
  unfold planePoint
  rw [show ((unitShearOpposite X K n v).1 : FreeAlgebra K X) =
    (v.1 : FreeAlgebra K X) from rfl]
  rw [show ((unitShearOpposite X K n v).2 : FreeAlgebra K X) =
    (v.1 : FreeAlgebra K X) + (v.2 : FreeAlgebra K X) from rfl]
  rw [← elementaryRoot_mul j k hjk, mul_assoc]

/-- **Same-stage mass transport** along the forward unit shear. -/
theorem planeMass_unitShearForward
    (χ : Module.Dual K (PlaneVector X K n)) (z : E) :
    planeMass X K i j k hik hjk n rho ψ χ z =
      planeMass X K i j k hik hjk n rho ψ
        (χ.comp ((unitShearForward X K n).symm :
          PlaneVector X K n →ₗ[K] PlaneVector X K n))
        (rho (elementaryRoot i j hij (1 : FreeAlgebra K X)) z) := by
  set U := rho (elementaryRoot i j hij (1 : FreeAlgebra K X)) with hU
  have hconj : ∀ v : PlaneVector X K n,
      U * planeAction X K i j k hik hjk n rho v * U⁻¹ =
        planeAction X K i j k hik hjk n rho
          (unitShearForward X K n v) := by
    intro v
    unfold planeAction
    rw [hU, ← map_inv, ← map_mul, ← map_mul,
      planePoint_unitShearForward X K i j k hij hik hjk n v]
  calc
    planeMass X K i j k hik hjk n rho ψ χ z =
        CharacterMass.mass ψ
          (fun v ↦ U * planeAction X K i j k hik hjk n rho v * U⁻¹)
          χ (U z) := by
      rw [planeMass]
      exact (CharacterMass.mass_conj ψ _ U χ z).symm
    _ = CharacterMass.mass ψ
        (fun v ↦ planeAction X K i j k hik hjk n rho
          (unitShearForward X K n v)) χ (U z) := by
      congr 1
      funext v
      exact hconj v
    _ = planeMass X K i j k hik hjk n rho ψ
        (χ.comp ((unitShearForward X K n).symm :
          PlaneVector X K n →ₗ[K] PlaneVector X K n)) (U z) :=
      CharacterMass.mass_precomp ψ _ (unitShearForward X K n) χ (U z)

/-- **Same-stage mass transport** along the opposite unit shear. -/
theorem planeMass_unitShearOpposite
    (χ : Module.Dual K (PlaneVector X K n)) (z : E) :
    planeMass X K i j k hik hjk n rho ψ χ z =
      planeMass X K i j k hik hjk n rho ψ
        (χ.comp ((unitShearOpposite X K n).symm :
          PlaneVector X K n →ₗ[K] PlaneVector X K n))
        (rho (elementaryRoot j i hij.symm (1 : FreeAlgebra K X)) z) := by
  set U := rho (elementaryRoot j i hij.symm (1 : FreeAlgebra K X)) with hU
  have hconj : ∀ v : PlaneVector X K n,
      U * planeAction X K i j k hik hjk n rho v * U⁻¹ =
        planeAction X K i j k hik hjk n rho
          (unitShearOpposite X K n v) := by
    intro v
    unfold planeAction
    rw [hU, ← map_inv, ← map_mul, ← map_mul,
      planePoint_unitShearOpposite X K i j k hij hik hjk n v]
  calc
    planeMass X K i j k hik hjk n rho ψ χ z =
        CharacterMass.mass ψ
          (fun v ↦ U * planeAction X K i j k hik hjk n rho v * U⁻¹)
          χ (U z) := by
      rw [planeMass]
      exact (CharacterMass.mass_conj ψ _ U χ z).symm
    _ = CharacterMass.mass ψ
        (fun v ↦ planeAction X K i j k hik hjk n rho
          (unitShearOpposite X K n v)) χ (U z) := by
      congr 1
      funext v
      exact hconj v
    _ = planeMass X K i j k hik hjk n rho ψ
        (χ.comp ((unitShearOpposite X K n).symm :
          PlaneVector X K n →ₗ[K] PlaneVector X K n)) (U z) :=
      CharacterMass.mass_precomp ψ _ (unitShearOpposite X K n) χ (U z)

omit [Fintype K] in
/-- Coordinate functionals of the forward unit-shear transport. -/
theorem coordinateChar_comp_unitShearForward_symm
    (χ : Module.Dual K (PlaneVector X K n)) :
    firstCoordinateChar X K n (χ.comp
        ((unitShearForward X K n).symm :
          PlaneVector X K n →ₗ[K] PlaneVector X K n)) =
      firstCoordinateChar X K n χ ∧
    secondCoordinateChar X K n (χ.comp
        ((unitShearForward X K n).symm :
          PlaneVector X K n →ₗ[K] PlaneVector X K n)) =
      -firstCoordinateChar X K n χ + secondCoordinateChar X K n χ := by
  constructor
  · refine LinearMap.ext fun a ↦ ?_
    show χ ((unitShearForward X K n).symm (a, 0)) = χ (a, 0)
    rw [show (unitShearForward X K n).symm (a, 0) = (a, 0) by
      rw [unitShearForward, LinearEquiv.ofLinear_symm_apply]
      apply Prod.ext
      · show a - 0 = a
        rw [sub_zero]
      · rfl]
  · refine LinearMap.ext fun b ↦ ?_
    show χ ((unitShearForward X K n).symm (0, b)) =
      -χ (b, 0) + χ (0, b)
    rw [← map_neg, ← map_add,
      show (unitShearForward X K n).symm (0, b) = (-b + 0, 0 + b) by
        rw [unitShearForward, LinearEquiv.ofLinear_symm_apply]
        apply Prod.ext
        · show (0 : degreeLE X K n) - b = -b + 0
          rw [zero_sub, add_zero]
        · show b = 0 + b
          rw [zero_add]]
    congr 1
    apply Prod.ext <;> simp

omit [Fintype K] in
/-- Coordinate functionals of the opposite unit-shear transport. -/
theorem coordinateChar_comp_unitShearOpposite_symm
    (χ : Module.Dual K (PlaneVector X K n)) :
    firstCoordinateChar X K n (χ.comp
        ((unitShearOpposite X K n).symm :
          PlaneVector X K n →ₗ[K] PlaneVector X K n)) =
      firstCoordinateChar X K n χ - secondCoordinateChar X K n χ ∧
    secondCoordinateChar X K n (χ.comp
        ((unitShearOpposite X K n).symm :
          PlaneVector X K n →ₗ[K] PlaneVector X K n)) =
      secondCoordinateChar X K n χ := by
  constructor
  · refine LinearMap.ext fun a ↦ ?_
    show χ ((unitShearOpposite X K n).symm (a, 0)) =
      χ (a, 0) - χ (0, a)
    rw [← map_sub,
      show (unitShearOpposite X K n).symm (a, 0) = (a - 0, 0 - a) by
        rw [unitShearOpposite, LinearEquiv.ofLinear_symm_apply]
        apply Prod.ext
        · show a = a - 0
          rw [sub_zero]
        · rfl]
    congr 1
  · refine LinearMap.ext fun b ↦ ?_
    show χ ((unitShearOpposite X K n).symm (0, b)) = χ (0, b)
    rw [show (unitShearOpposite X K n).symm (0, b) = (0, b) by
      rw [unitShearOpposite, LinearEquiv.ofLinear_symm_apply]
      apply Prod.ext
      · rfl
      · show b - 0 = b
        rw [sub_zero]]

open FreeRootFunctionalValuation in
omit [Fintype K] in
/-- **Region `C` is sent into region `B`** by the forward unit-shear
transport. -/
theorem pairRegion_comp_unitShearForward_symm_of_C
    (χ : Module.Dual K (PlaneVector X K n))
    (h : pairRegion X K (firstCoordinateChar X K n χ)
      (secondCoordinateChar X K n χ) = .C) :
    pairRegion X K
        (firstCoordinateChar X K n (χ.comp
          ((unitShearForward X K n).symm :
            PlaneVector X K n →ₗ[K] PlaneVector X K n)))
        (secondCoordinateChar X K n (χ.comp
          ((unitShearForward X K n).symm :
            PlaneVector X K n →ₗ[K] PlaneVector X K n))) = .B := by
  obtain ⟨hz, hφ, hχ2, hlt⟩ := pairRegion_C_data X K _ _ h
  obtain ⟨hfirst, hsecond⟩ :=
    coordinateChar_comp_unitShearForward_symm X K n χ
  rw [hfirst, hsecond]
  have hnegval : valuation X K (-firstCoordinateChar X K n χ) =
      valuation X K (firstCoordinateChar X K n χ) :=
    valuation_neg X K _
  have hval : valuation X K
      (-firstCoordinateChar X K n χ + secondCoordinateChar X K n χ) =
      valuation X K (firstCoordinateChar X K n χ) := by
    rw [valuation_add_of_lt X K _ _ (by omega), hnegval]
  apply pairRegion_eq_B_of_data
  · intro hcontra
    have hb := valuation_le_succ X K (secondCoordinateChar X K n χ)
    omega
  · exact hφ
  · omega
  · omega

open FreeRootFunctionalValuation in
omit [Fintype K] in
/-- **Region `A` is sent into region `B`** by the opposite unit-shear
transport. -/
theorem pairRegion_comp_unitShearOpposite_symm_of_A
    (χ : Module.Dual K (PlaneVector X K n))
    (h : pairRegion X K (firstCoordinateChar X K n χ)
      (secondCoordinateChar X K n χ) = .A) :
    pairRegion X K
        (firstCoordinateChar X K n (χ.comp
          ((unitShearOpposite X K n).symm :
            PlaneVector X K n →ₗ[K] PlaneVector X K n)))
        (secondCoordinateChar X K n (χ.comp
          ((unitShearOpposite X K n).symm :
            PlaneVector X K n →ₗ[K] PlaneVector X K n))) = .B := by
  obtain ⟨hz, hχ1, hχ2, hlt⟩ := pairRegion_A_data X K _ _ h
  obtain ⟨hfirst, hsecond⟩ :=
    coordinateChar_comp_unitShearOpposite_symm X K n χ
  rw [hfirst, hsecond]
  have hval : valuation X K
      (firstCoordinateChar X K n χ - secondCoordinateChar X K n χ) =
      valuation X K (secondCoordinateChar X K n χ) := by
    rw [show firstCoordinateChar X K n χ - secondCoordinateChar X K n χ =
      -secondCoordinateChar X K n χ + firstCoordinateChar X K n χ by abel]
    rw [valuation_add_of_lt X K _ _
      (by rw [valuation_neg X K _]; omega), valuation_neg X K _]
  apply pairRegion_eq_B_of_data
  · intro hcontra
    have hb := valuation_le_succ X K (firstCoordinateChar X K n χ)
    omega
  · omega
  · exact hχ2
  · omega


/-! ### Region `D` control and the trivial-mass boundary layer -/

/-- The first unit plane vector. -/
noncomputable def unitVectorFirst : PlaneVector X K n :=
  (wordMonomialInDegree X K n 1, 0)

/-- The second unit plane vector. -/
noncomputable def unitVectorSecond : PlaneVector X K n :=
  (0, wordMonomialInDegree X K n 1)

open FreeRootFunctionalValuation in
omit [Fintype K] in
/-- A region-`D` character does not vanish at one of the two unit plane
vectors. -/
theorem apply_unitVector_ne_zero_of_D
    (χ : Module.Dual K (PlaneVector X K n))
    (h : pairRegion X K (firstCoordinateChar X K n χ)
      (secondCoordinateChar X K n χ) = .D) :
    χ (unitVectorFirst X K n) ≠ 0 ∨ χ (unitVectorSecond X K n) ≠ 0 := by
  rcases pairRegion_D_data X K _ _ h with h0 | h0
  · left
    have := (valuation_eq_zero_iff X K _).1 h0
    exact this
  · right
    have := (valuation_eq_zero_iff X K _).1 h0
    exact this

open FreeRootFunctionalValuation in
open Classical in
/-- **Region `D` mass control**: the total region-`D` mass is bounded by
the summed squared displacements of the scalar multiples of the two unit
plane vectors, at the character gap constant. -/
theorem gap_mul_sum_planeMass_D_le (hψ : ψ ≠ 1) (z : E) :
    CharacterMass.gap ψ *
        ∑ χ ∈ Finset.univ.filter
          (fun χ : Module.Dual K (PlaneVector X K n) ↦
            pairRegion X K (firstCoordinateChar X K n χ)
              (secondCoordinateChar X K n χ) = .D),
          planeMass X K i j k hik hjk n rho ψ χ z ≤
      (∑ t : K, ‖rho (planePoint X K i j k hik hjk n
          (t • unitVectorFirst X K n)) z - z‖ ^ 2) +
        ∑ t : K, ‖rho (planePoint X K i j k hik hjk n
          (t • unitVectorSecond X K n)) z - z‖ ^ 2 := by
  set D := Finset.univ.filter
    (fun χ : Module.Dual K (PlaneVector X K n) ↦
      pairRegion X K (firstCoordinateChar X K n χ)
        (secondCoordinateChar X K n χ) = .D) with hD
  set E₁ := Finset.univ.filter
    (fun χ : Module.Dual K (PlaneVector X K n) ↦
      χ (unitVectorFirst X K n) ≠ 0) with hE₁
  set E₂ := Finset.univ.filter
    (fun χ : Module.Dual K (PlaneVector X K n) ↦
      χ (unitVectorSecond X K n) ≠ 0) with hE₂
  have hsubset : D ⊆ E₁ ∪ E₂ := by
    intro χ hχ
    rw [hD, Finset.mem_filter] at hχ
    rcases apply_unitVector_ne_zero_of_D X K n χ hχ.2 with h | h
    · exact Finset.mem_union_left _
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
  have hDle : (∑ χ ∈ D, planeMass X K i j k hik hjk n rho ψ χ z) ≤
      (∑ χ ∈ E₁, planeMass X K i j k hik hjk n rho ψ χ z) +
        ∑ χ ∈ E₂, planeMass X K i j k hik hjk n rho ψ χ z := by
    have h1 : (∑ χ ∈ D, planeMass X K i j k hik hjk n rho ψ χ z) ≤
        ∑ χ ∈ E₁ ∪ E₂, planeMass X K i j k hik hjk n rho ψ χ z :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        fun χ _ _ ↦ planeMass_nonneg X K i j k hik hjk n rho ψ χ z
    have h2 : (∑ χ ∈ E₁ ∪ E₂,
        planeMass X K i j k hik hjk n rho ψ χ z) +
        ∑ χ ∈ E₁ ∩ E₂, planeMass X K i j k hik hjk n rho ψ χ z =
      (∑ χ ∈ E₁, planeMass X K i j k hik hjk n rho ψ χ z) +
        ∑ χ ∈ E₂, planeMass X K i j k hik hjk n rho ψ χ z :=
      Finset.sum_union_inter
    have h3 : 0 ≤ ∑ χ ∈ E₁ ∩ E₂,
        planeMass X K i j k hik hjk n rho ψ χ z :=
      Finset.sum_nonneg fun χ _ ↦
        planeMass_nonneg X K i j k hik hjk n rho ψ χ z
    linarith
  calc
    CharacterMass.gap ψ *
        ∑ χ ∈ D, planeMass X K i j k hik hjk n rho ψ χ z ≤
        CharacterMass.gap ψ *
          ((∑ χ ∈ E₁, planeMass X K i j k hik hjk n rho ψ χ z) +
            ∑ χ ∈ E₂, planeMass X K i j k hik hjk n rho ψ χ z) :=
      mul_le_mul_of_nonneg_left hDle (CharacterMass.gap_pos ψ).le
    _ = CharacterMass.gap ψ *
          (∑ χ ∈ E₁, planeMass X K i j k hik hjk n rho ψ χ z) +
        CharacterMass.gap ψ *
          ∑ χ ∈ E₂, planeMass X K i j k hik hjk n rho ψ χ z := by
      ring
    _ ≤ (∑ t : K, ‖rho (planePoint X K i j k hik hjk n
          (t • unitVectorFirst X K n)) z - z‖ ^ 2) +
        ∑ t : K, ‖rho (planePoint X K i j k hik hjk n
          (t • unitVectorSecond X K n)) z - z‖ ^ 2 :=
      add_le_add
        (gap_mul_sum_planeMass_ne_zero_le X K i j k hik hjk n rho ψ
          hψ z (unitVectorFirst X K n))
        (gap_mul_sum_planeMass_ne_zero_le X K i j k hik hjk n rho ψ
          hψ z (unitVectorSecond X K n))

open Classical in
/-- **Trivial-mass monotonicity** along the forward shear conjugation: the
next-stage trivial mass of the conjugated vector never exceeds the current
trivial mass. -/
theorem planeMass_zero_conj_le (hψ : ψ ≠ 1) (x : X) (z : E) :
    planeMass X K i j k hik hjk (n + 1) rho ψ 0
        (rho (elementaryRoot i j hij (FreeAlgebra.ι K x)) z) ≤
      planeMass X K i j k hik hjk n rho ψ 0 z := by
  rw [planeMass_eq_sum_fiber_forwardShear X K i j k hij hik hjk n rho ψ
    hψ x z 0]
  have hmem : (0 : Module.Dual K (PlaneVector X K (n + 1))) ∈
      Finset.univ.filter
        (fun χ' : Module.Dual K (PlaneVector X K (n + 1)) ↦
          χ'.comp (forwardShear X K n x) = 0) :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, by
      refine LinearMap.ext fun v ↦ ?_
      rfl⟩
  exact Finset.single_le_sum
    (fun χ' _ ↦ planeMass_nonneg X K i j k hik hjk (n + 1) rho ψ χ' _)
    hmem

open Classical in
/-- **The boundary-layer drop identity**: the total mass of the nonzero
fine characters killed by the forward dual shear is exactly the drop of the
nested trivial mass. -/
theorem sum_fiber_zero_ne_eq_drop (hψ : ψ ≠ 1) (x : X) (z : E) :
    ∑ χ' ∈ Finset.univ.filter
        (fun χ' : Module.Dual K (PlaneVector X K (n + 1)) ↦
          χ'.comp (forwardShear X K n x) = 0 ∧ χ' ≠ 0),
      planeMass X K i j k hik hjk (n + 1) rho ψ χ'
        (rho (elementaryRoot i j hij (FreeAlgebra.ι K x)) z) =
    planeMass X K i j k hik hjk n rho ψ 0 z -
      planeMass X K i j k hik hjk (n + 1) rho ψ 0
        (rho (elementaryRoot i j hij (FreeAlgebra.ι K x)) z) := by
  rw [planeMass_eq_sum_fiber_forwardShear X K i j k hij hik hjk n rho ψ
    hψ x z 0]
  rw [show (Finset.univ.filter
      (fun χ' : Module.Dual K (PlaneVector X K (n + 1)) ↦
        χ'.comp (forwardShear X K n x) = 0)) =
    insert (0 : Module.Dual K (PlaneVector X K (n + 1)))
      (Finset.univ.filter
        (fun χ' : Module.Dual K (PlaneVector X K (n + 1)) ↦
          χ'.comp (forwardShear X K n x) = 0 ∧ χ' ≠ 0)) from by
    ext χ'
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · intro h
      by_cases hzero : χ' = 0
      · exact Or.inl hzero
      · exact Or.inr ⟨h, hzero⟩
    · rintro (rfl | ⟨h, -⟩)
      · refine LinearMap.ext fun v ↦ ?_
        rfl
      · exact h]
  rw [Finset.sum_insert (by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rintro ⟨-, h⟩
    exact h rfl)]
  ring

end FreeRootPlaneMass

end NonsoficGroupsExist
