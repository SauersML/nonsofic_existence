import NonsoficGroupsExist.FreeRootPlane
import NonsoficGroupsExist.FreeRootFunctionalValuation
import NonsoficGroupsExist.CharacterMass
import NonsoficGroupsExist.KazhdanFixedSpace

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


open FreeRootFunctionalValuation in
open Classical in
/-- **Region `A` sum bound**: the total region-`A` mass of `z` is at most
the total region-`B` mass of the opposite-unit-conjugated vector. -/
theorem sum_planeMass_A_le_sum_B (z : E) :
    ∑ χ ∈ Finset.univ.filter
        (fun χ : Module.Dual K (PlaneVector X K n) ↦
          pairRegion X K (firstCoordinateChar X K n χ)
            (secondCoordinateChar X K n χ) = .A),
      planeMass X K i j k hik hjk n rho ψ χ z ≤
    ∑ χ ∈ Finset.univ.filter
        (fun χ : Module.Dual K (PlaneVector X K n) ↦
          pairRegion X K (firstCoordinateChar X K n χ)
            (secondCoordinateChar X K n χ) = .B),
      planeMass X K i j k hik hjk n rho ψ χ
        (rho (elementaryRoot j i hij.symm (1 : FreeAlgebra K X)) z) := by
  set τ : Module.Dual K (PlaneVector X K n) →
      Module.Dual K (PlaneVector X K n) := fun χ ↦
    χ.comp ((unitShearOpposite X K n).symm :
      PlaneVector X K n →ₗ[K] PlaneVector X K n) with hτ
  set A := Finset.univ.filter
    (fun χ : Module.Dual K (PlaneVector X K n) ↦
      pairRegion X K (firstCoordinateChar X K n χ)
        (secondCoordinateChar X K n χ) = .A) with hA
  set B := Finset.univ.filter
    (fun χ : Module.Dual K (PlaneVector X K n) ↦
      pairRegion X K (firstCoordinateChar X K n χ)
        (secondCoordinateChar X K n χ) = .B) with hB
  set z' := rho (elementaryRoot j i hij.symm (1 : FreeAlgebra K X)) z
    with hz'
  have hstep : (∑ χ ∈ A, planeMass X K i j k hik hjk n rho ψ χ z) =
      ∑ χ ∈ A, planeMass X K i j k hik hjk n rho ψ (τ χ) z' := by
    refine Finset.sum_congr rfl fun χ _ ↦ ?_
    exact planeMass_unitShearOpposite X K i j k hij hik hjk n rho ψ χ z
  rw [hstep]
  have hinj : Set.InjOn τ A := by
    intro χ _ χ' _ h
    refine LinearMap.ext fun v ↦ ?_
    have := congrArg
      (fun φ : Module.Dual K (PlaneVector X K n) ↦
        φ (unitShearOpposite X K n v)) h
    simpa [hτ, LinearEquiv.symm_apply_apply] using this
  rw [show (∑ χ ∈ A, planeMass X K i j k hik hjk n rho ψ (τ χ) z') =
      ∑ η ∈ A.image τ, planeMass X K i j k hik hjk n rho ψ η z' from
    (Finset.sum_image
      (f := fun η ↦ planeMass X K i j k hik hjk n rho ψ η z')
      (fun χ hχ χ' hχ' h ↦ hinj hχ hχ' h)).symm]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_
    fun η _ _ ↦ planeMass_nonneg X K i j k hik hjk n rho ψ η z'
  intro η hη
  obtain ⟨χ, hχ, rfl⟩ := Finset.mem_image.1 hη
  rw [hB, Finset.mem_filter]
  rw [hA, Finset.mem_filter] at hχ
  exact ⟨Finset.mem_univ _,
    pairRegion_comp_unitShearOpposite_symm_of_A X K n χ hχ.2⟩

open FreeRootFunctionalValuation in
open Classical in
/-- **Region `C` sum bound**: the total region-`C` mass of `z` is at most
the total region-`B` mass of the forward-unit-conjugated vector. -/
theorem sum_planeMass_C_le_sum_B (z : E) :
    ∑ χ ∈ Finset.univ.filter
        (fun χ : Module.Dual K (PlaneVector X K n) ↦
          pairRegion X K (firstCoordinateChar X K n χ)
            (secondCoordinateChar X K n χ) = .C),
      planeMass X K i j k hik hjk n rho ψ χ z ≤
    ∑ χ ∈ Finset.univ.filter
        (fun χ : Module.Dual K (PlaneVector X K n) ↦
          pairRegion X K (firstCoordinateChar X K n χ)
            (secondCoordinateChar X K n χ) = .B),
      planeMass X K i j k hik hjk n rho ψ χ
        (rho (elementaryRoot i j hij (1 : FreeAlgebra K X)) z) := by
  set τ : Module.Dual K (PlaneVector X K n) →
      Module.Dual K (PlaneVector X K n) := fun χ ↦
    χ.comp ((unitShearForward X K n).symm :
      PlaneVector X K n →ₗ[K] PlaneVector X K n) with hτ
  set C := Finset.univ.filter
    (fun χ : Module.Dual K (PlaneVector X K n) ↦
      pairRegion X K (firstCoordinateChar X K n χ)
        (secondCoordinateChar X K n χ) = .C) with hC
  set B := Finset.univ.filter
    (fun χ : Module.Dual K (PlaneVector X K n) ↦
      pairRegion X K (firstCoordinateChar X K n χ)
        (secondCoordinateChar X K n χ) = .B) with hB
  set z' := rho (elementaryRoot i j hij (1 : FreeAlgebra K X)) z
    with hz'
  have hstep : (∑ χ ∈ C, planeMass X K i j k hik hjk n rho ψ χ z) =
      ∑ χ ∈ C, planeMass X K i j k hik hjk n rho ψ (τ χ) z' := by
    refine Finset.sum_congr rfl fun χ _ ↦ ?_
    exact planeMass_unitShearForward X K i j k hij hik hjk n rho ψ χ z
  rw [hstep]
  have hinj : Set.InjOn τ C := by
    intro χ _ χ' _ h
    refine LinearMap.ext fun v ↦ ?_
    have := congrArg
      (fun φ : Module.Dual K (PlaneVector X K n) ↦
        φ (unitShearForward X K n v)) h
    simpa [hτ, LinearEquiv.symm_apply_apply] using this
  rw [show (∑ χ ∈ C, planeMass X K i j k hik hjk n rho ψ (τ χ) z') =
      ∑ η ∈ C.image τ, planeMass X K i j k hik hjk n rho ψ η z' from
    (Finset.sum_image
      (f := fun η ↦ planeMass X K i j k hik hjk n rho ψ η z')
      (fun χ hχ χ' hχ' h ↦ hinj hχ hχ' h)).symm]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_
    fun η _ _ ↦ planeMass_nonneg X K i j k hik hjk n rho ψ η z'
  intro η hη
  obtain ⟨χ, hχ, rfl⟩ := Finset.mem_image.1 hη
  rw [hB, Finset.mem_filter]
  rw [hC, Finset.mem_filter] at hχ
  exact ⟨Finset.mem_univ _,
    pairRegion_comp_unitShearForward_symm_of_C X K n χ hχ.2⟩


open FreeRootFunctionalValuation in
omit [Fintype K] in
/-- **The descent classification**: a fine character over a coarse
region-`B` character, whose first functional descends by exactly one along
the chosen generator, lies in the opposite region `A` — or in `D` at the
lowest level.  This is the region movement that powers the finite-stage
induction. -/
theorem fine_pairRegion_of_coarse_B_forward (x : X)
    (χ' : Module.Dual K (PlaneVector X K (n + 1)))
    (hB : pairRegion X K
        (firstCoordinateChar X K n (χ'.comp (forwardShear X K n x)))
        (secondCoordinateChar X K n (χ'.comp (forwardShear X K n x))) =
        .B)
    (hlead : valuation X K
        (leftDerived X K (firstCoordinateChar X K (n + 1) χ') x) + 1 =
      valuation X K (firstCoordinateChar X K (n + 1) χ')) :
    pairRegion X K (firstCoordinateChar X K (n + 1) χ')
        (secondCoordinateChar X K (n + 1) χ') = .A ∨
      pairRegion X K (firstCoordinateChar X K (n + 1) χ')
        (secondCoordinateChar X K (n + 1) χ') = .D := by
  obtain ⟨hz, h1ne, h2ne, heq⟩ := pairRegion_B_data X K _ _ hB
  rw [firstCoordinateChar_comp_forwardShear X K n x χ'] at hz h1ne heq
  rw [secondCoordinateChar_comp_forwardShear X K n x χ'] at hz h2ne heq
  set φ₁ := firstCoordinateChar X K (n + 1) χ' with hφ₁
  set φ₂ := secondCoordinateChar X K (n + 1) χ' with hφ₂
  set d := valuation X K (restrictSucc X K φ₁) with hd
  have hdlen : d ≤ n + 1 := valuation_le_succ X K _
  have hdn : d ≤ n := by
    by_contra hgt
    have h2 : valuation X K
        (leftDerived X K φ₁ x + restrictSucc X K φ₂) = d := heq.symm
    exact hz ⟨by omega, by omega⟩
  have hval₁ : valuation X K φ₁ = d := by
    have := valuation_restrictSucc_eq_min X K φ₁
    rw [← hd] at this
    omega
  have hdpos : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h0 | h1
    · exact absurd h0 h1ne
    · exact h1
  have hderived : valuation X K (leftDerived X K φ₁ x) = d - 1 := by
    omega
  have hval₂' : valuation X K (restrictSucc X K φ₂) = d - 1 := by
    by_contra hne
    rcases Nat.lt_or_ge (valuation X K (restrictSucc X K φ₂)) (d - 1)
      with hlt | hge
    · have := valuation_add_of_lt X K (restrictSucc X K φ₂)
        (leftDerived X K φ₁ x) (by omega)
      rw [show restrictSucc X K φ₂ + leftDerived X K φ₁ x =
        leftDerived X K φ₁ x + restrictSucc X K φ₂ by abel] at this
      omega
    · have hgt : d - 1 < valuation X K (restrictSucc X K φ₂) := by
        omega
      have := valuation_add_of_lt X K (leftDerived X K φ₁ x)
        (restrictSucc X K φ₂) (by omega)
      omega
  have hval₂ : valuation X K φ₂ = d - 1 := by
    have := valuation_restrictSucc_eq_min X K φ₂
    rw [hval₂'] at this
    omega
  rcases Nat.eq_or_lt_of_le hdpos with h1 | h2
  · right
    exact pairRegion_eq_D_of_right_zero X K _ _ (by omega)
  · left
    exact pairRegion_eq_A_of_pos_of_lt X K _ _ (by omega) (by omega)

open FreeRootFunctionalValuation in
omit [Fintype K] in
/-- The symmetric descent classification along the opposite shear: a fine
character over a coarse region-`B` character, whose second functional
descends by exactly one, lies in region `C` — or in `D` at the lowest
level. -/
theorem fine_pairRegion_of_coarse_B_opposite (x : X)
    (χ' : Module.Dual K (PlaneVector X K (n + 1)))
    (hB : pairRegion X K
        (firstCoordinateChar X K n (χ'.comp (oppositeShear X K n x)))
        (secondCoordinateChar X K n (χ'.comp (oppositeShear X K n x))) =
        .B)
    (hlead : valuation X K
        (leftDerived X K (secondCoordinateChar X K (n + 1) χ') x) + 1 =
      valuation X K (secondCoordinateChar X K (n + 1) χ')) :
    pairRegion X K (firstCoordinateChar X K (n + 1) χ')
        (secondCoordinateChar X K (n + 1) χ') = .C ∨
      pairRegion X K (firstCoordinateChar X K (n + 1) χ')
        (secondCoordinateChar X K (n + 1) χ') = .D := by
  obtain ⟨hz, h1ne, h2ne, heq⟩ := pairRegion_B_data X K _ _ hB
  rw [firstCoordinateChar_comp_oppositeShear X K n x χ'] at hz h1ne heq
  rw [secondCoordinateChar_comp_oppositeShear X K n x χ'] at hz h2ne heq
  set φ₁ := firstCoordinateChar X K (n + 1) χ' with hφ₁
  set φ₂ := secondCoordinateChar X K (n + 1) χ' with hφ₂
  set d := valuation X K (restrictSucc X K φ₂) with hd
  have hdlen : d ≤ n + 1 := valuation_le_succ X K _
  have hdn : d ≤ n := by
    by_contra hgt
    exact hz ⟨by omega, by omega⟩
  have hval₂ : valuation X K φ₂ = d := by
    have := valuation_restrictSucc_eq_min X K φ₂
    rw [← hd] at this
    omega
  have hdpos : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h0 | h1
    · exact absurd h0 h2ne
    · exact h1
  have hderived : valuation X K (leftDerived X K φ₂ x) = d - 1 := by
    omega
  have hval₁' : valuation X K (restrictSucc X K φ₁) = d - 1 := by
    by_contra hne
    rcases Nat.lt_or_ge (valuation X K (restrictSucc X K φ₁)) (d - 1)
      with hlt | hge
    · have := valuation_add_of_lt X K (restrictSucc X K φ₁)
        (leftDerived X K φ₂ x) (by omega)
      omega
    · have hgt : d - 1 < valuation X K (restrictSucc X K φ₁) := by
        omega
      have := valuation_add_of_lt X K (leftDerived X K φ₂ x)
        (restrictSucc X K φ₁) (by omega)
      rw [show leftDerived X K φ₂ x + restrictSucc X K φ₁ =
        restrictSucc X K φ₁ + leftDerived X K φ₂ x by abel] at this
      omega
  have hval₁ : valuation X K φ₁ = d - 1 := by
    have := valuation_restrictSucc_eq_min X K φ₁
    rw [hval₁'] at this
    omega
  rcases Nat.eq_or_lt_of_le hdpos with h1 | h2
  · right
    exact pairRegion_eq_D_of_left_zero X K _ _ (by omega)
  · left
    exact pairRegion_eq_C_of_pos_of_lt X K _ _ (by omega) (by omega)


open FreeRootFunctionalValuation in
open Classical in
/-- **The assembled region-`B` descent inequality**: the total coarse
region-`B` mass at a stage is bounded by the total fine opposite-region
(`A` or `D`) mass of the generator-conjugated vectors at the next stage,
summed over the alphabet.  Every coarse `B`-character is charged through
the forward shear of its canonical least leading generator; the fibers of
distinct coarse characters are disjoint, and the descent classification
places every receiving fine character in region `A` or `D`. -/
theorem sum_planeMass_B_le_sum_fine (hψ : ψ ≠ 1) (z : E) :
    ∑ χ ∈ Finset.univ.filter
        (fun χ : Module.Dual K (PlaneVector X K (n + 1)) ↦
          pairRegion X K (firstCoordinateChar X K (n + 1) χ)
            (secondCoordinateChar X K (n + 1) χ) = .B),
      planeMass X K i j k hik hjk (n + 1) rho ψ χ z ≤
    ∑ x : X, ∑ χ' ∈ Finset.univ.filter
        (fun χ' : Module.Dual K (PlaneVector X K (n + 2)) ↦
          pairRegion X K (firstCoordinateChar X K (n + 2) χ')
            (secondCoordinateChar X K (n + 2) χ') = .A ∨
          pairRegion X K (firstCoordinateChar X K (n + 2) χ')
            (secondCoordinateChar X K (n + 2) χ') = .D),
      planeMass X K i j k hik hjk (n + 2) rho ψ χ'
        (rho (elementaryRoot i j hij (FreeAlgebra.ι K x)) z) := by
  set B := Finset.univ.filter
    (fun χ : Module.Dual K (PlaneVector X K (n + 1)) ↦
      pairRegion X K (firstCoordinateChar X K (n + 1) χ)
        (secondCoordinateChar X K (n + 1) χ) = .B) with hB
  set selIdx : Module.Dual K (PlaneVector X K (n + 1)) →
      Fin (Fintype.card X + 1) := fun χ ↦
    if h : leastLeadingGeneratorIndex X K
        (firstCoordinateChar X K (n + 1) χ) < Fintype.card X then
      ⟨leastLeadingGeneratorIndex X K
        (firstCoordinateChar X K (n + 1) χ), Nat.lt_succ_of_lt h⟩
    else Fin.last (Fintype.card X) with hselIdx
  have hleadset : ∀ χ ∈ B,
      (leadingGeneratorIndexSet X K
        (firstCoordinateChar X K (n + 1) χ)).Nonempty := by
    intro χ hχ
    rw [hB, Finset.mem_filter] at hχ
    obtain ⟨hz, h1ne, h2ne, heq⟩ := pairRegion_B_data X K _ _ hχ.2
    have hle : valuation X K (firstCoordinateChar X K (n + 1) χ) ≤
        n + 1 := by
      have := valuation_le_succ X K
        (firstCoordinateChar X K (n + 1) χ)
      have h2b := valuation_le_succ X K
        (secondCoordinateChar X K (n + 1) χ)
      omega
    refine leadingGeneratorIndexSet_nonempty X K _ ?_ (by omega)
    by_contra hnone
    have := valuation_eq_succ_of_not_exists X K _ hnone
    omega
  have hpartition : (∑ χ ∈ B,
      planeMass X K i j k hik hjk (n + 1) rho ψ χ z) =
    ∑ q : Fin (Fintype.card X + 1),
      ∑ χ ∈ B.filter (fun χ ↦ selIdx χ = q),
        planeMass X K i j k hik hjk (n + 1) rho ψ χ z :=
    (Finset.sum_fiberwise B selIdx _).symm
  rw [hpartition, Fin.sum_univ_castSucc]
  have hlast : B.filter
      (fun χ ↦ selIdx χ = Fin.last (Fintype.card X)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro χ hχ
    have hlt := leastLeadingGeneratorIndex_lt_card X K
      (firstCoordinateChar X K (n + 1) χ) (hleadset χ hχ)
    rw [hselIdx]
    beta_reduce
    rw [dif_pos hlt]
    intro hcontra
    have := congrArg Fin.val hcontra
    simp only [Fin.val_last] at this
    omega
  rw [hlast, Finset.sum_empty, add_zero]
  rw [show (∑ x : X, ∑ χ' ∈ Finset.univ.filter
      (fun χ' : Module.Dual K (PlaneVector X K (n + 2)) ↦
        pairRegion X K (firstCoordinateChar X K (n + 2) χ')
          (secondCoordinateChar X K (n + 2) χ') = .A ∨
        pairRegion X K (firstCoordinateChar X K (n + 2) χ')
          (secondCoordinateChar X K (n + 2) χ') = .D),
      planeMass X K i j k hik hjk (n + 2) rho ψ χ'
        (rho (elementaryRoot i j hij (FreeAlgebra.ι K x)) z)) =
    ∑ q : Fin (Fintype.card X), ∑ χ' ∈ Finset.univ.filter
      (fun χ' : Module.Dual K (PlaneVector X K (n + 2)) ↦
        pairRegion X K (firstCoordinateChar X K (n + 2) χ')
          (secondCoordinateChar X K (n + 2) χ') = .A ∨
        pairRegion X K (firstCoordinateChar X K (n + 2) χ')
          (secondCoordinateChar X K (n + 2) χ') = .D),
      planeMass X K i j k hik hjk (n + 2) rho ψ χ'
        (rho (elementaryRoot i j hij
          (FreeAlgebra.ι K (generatorEnumeration X q))) z) from
    (Fintype.sum_equiv (generatorEnumeration X) _ _ fun q ↦ rfl).symm]
  refine Finset.sum_le_sum fun q _ ↦ ?_
  set x := generatorEnumeration X q with hx
  set Bx := B.filter (fun χ ↦ selIdx χ = q.castSucc) with hBx
  have htransport : (∑ χ ∈ Bx,
      planeMass X K i j k hik hjk (n + 1) rho ψ χ z) =
    ∑ χ ∈ Bx, ∑ χ' ∈ Finset.univ.filter
        (fun χ' : Module.Dual K (PlaneVector X K (n + 2)) ↦
          χ'.comp (forwardShear X K (n + 1) x) = χ),
      planeMass X K i j k hik hjk (n + 2) rho ψ χ'
        (rho (elementaryRoot i j hij (FreeAlgebra.ι K x)) z) := by
    refine Finset.sum_congr rfl fun χ _ ↦ ?_
    exact planeMass_eq_sum_fiber_forwardShear X K i j k hij hik hjk
      (n + 1) rho ψ hψ x z χ
  rw [htransport]
  have hdisj : (Bx : Set (Module.Dual K
      (PlaneVector X K (n + 1)))).PairwiseDisjoint
      (fun χ ↦ Finset.univ.filter
        (fun χ' : Module.Dual K (PlaneVector X K (n + 2)) ↦
          χ'.comp (forwardShear X K (n + 1) x) = χ)) := by
    intro χ₁ _ χ₂ _ hne
    refine Finset.disjoint_left.2 fun χ' h1 h2 ↦ ?_
    rw [Finset.mem_filter] at h1 h2
    exact hne (h1.2 ▸ h2.2)
  rw [← Finset.sum_biUnion hdisj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_
    fun χ' _ _ ↦ planeMass_nonneg X K i j k hik hjk (n + 2) rho ψ χ' _
  intro χ' hχ'
  obtain ⟨χ, hχBx, hχ'fiber⟩ := Finset.mem_biUnion.1 hχ'
  rw [Finset.mem_filter] at hχ'fiber
  have hfib : χ'.comp (forwardShear X K (n + 1) x) = χ := hχ'fiber.2
  rw [hBx, Finset.mem_filter] at hχBx
  obtain ⟨hχB, hχsel⟩ := hχBx
  have hχB' := hχB
  rw [hB, Finset.mem_filter] at hχB'
  have hBcoarse : pairRegion X K
      (firstCoordinateChar X K (n + 1)
        (χ'.comp (forwardShear X K (n + 1) x)))
      (secondCoordinateChar X K (n + 1)
        (χ'.comp (forwardShear X K (n + 1) x))) = .B := by
    rw [hfib]
    exact hχB'.2
  have hfirstid : firstCoordinateChar X K (n + 1) χ =
      restrictSucc X K (firstCoordinateChar X K (n + 2) χ') := by
    rw [← hfib]
    exact firstCoordinateChar_comp_forwardShear X K (n + 1) x χ'
  obtain ⟨hz2, h1ne, h2ne, heq⟩ := pairRegion_B_data X K _ _ hχB'.2
  have hdle : valuation X K (firstCoordinateChar X K (n + 1) χ) ≤
      n + 1 := by
    have := valuation_le_succ X K (firstCoordinateChar X K (n + 1) χ)
    have h2b := valuation_le_succ X K
      (secondCoordinateChar X K (n + 1) χ)
    omega
  have hfineval : valuation X K
      (firstCoordinateChar X K (n + 2) χ') ≤ n + 2 - 1 := by
    have hmin := valuation_restrictSucc_eq_min X K
      (firstCoordinateChar X K (n + 2) χ')
    rw [← hfirstid] at hmin
    omega
  have hleasteq : leastLeadingGeneratorIndex X K
      (firstCoordinateChar X K (n + 1) χ) =
    leastLeadingGeneratorIndex X K
      (firstCoordinateChar X K (n + 2) χ') := by
    rw [hfirstid]
    exact leastLeadingGeneratorIndex_restrictSucc X K
      (firstCoordinateChar X K (n + 2) χ') (by omega)
  have hsetseq : leadingGeneratorIndexSet X K
      (firstCoordinateChar X K (n + 1) χ) =
    leadingGeneratorIndexSet X K
      (firstCoordinateChar X K (n + 2) χ') := by
    rw [hfirstid]
    exact leadingGeneratorIndexSet_restrictSucc X K
      (firstCoordinateChar X K (n + 2) χ') (by omega)
  have hne : (leadingGeneratorIndexSet X K
      (firstCoordinateChar X K (n + 2) χ')).Nonempty := by
    rw [← hsetseq]
    exact hleadset χ hχB
  have hltcard : leastLeadingGeneratorIndex X K
      (firstCoordinateChar X K (n + 1) χ) < Fintype.card X := by
    rw [hleasteq]
    exact leastLeadingGeneratorIndex_lt_card X K _ hne
  have hidx : leastLeadingGeneratorIndex X K
      (firstCoordinateChar X K (n + 1) χ) = (q : ℕ) := by
    have := hχsel
    rw [hselIdx] at this
    beta_reduce at this
    rw [dif_pos hltcard] at this
    have hval := congrArg Fin.val this
    simpa using hval
  have hqfin : q = (⟨leastLeadingGeneratorIndex X K
      (firstCoordinateChar X K (n + 2) χ'),
      leastLeadingGeneratorIndex_lt_card X K _ hne⟩ :
        Fin (Fintype.card X)) := by
    apply Fin.ext
    show (q : ℕ) = leastLeadingGeneratorIndex X K
      (firstCoordinateChar X K (n + 2) χ')
    omega
  have hxval : x = generatorEnumeration X
      ⟨leastLeadingGeneratorIndex X K
        (firstCoordinateChar X K (n + 2) χ'),
        leastLeadingGeneratorIndex_lt_card X K _ hne⟩ := by
    rw [hx, hqfin]
  have hlead : valuation X K
      (leftDerived X K (firstCoordinateChar X K (n + 2) χ') x) + 1 =
    valuation X K (firstCoordinateChar X K (n + 2) χ') := by
    rw [hxval]
    exact leastLeadingGeneratorIndex_spec X K _ hne
  rcases fine_pairRegion_of_coarse_B_forward X K (n + 1) x χ'
      hBcoarse hlead with hA | hD
  · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, Or.inl hA⟩
  · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, Or.inr hD⟩


/-! ### The stage inclusion, nested trivial masses, and the boundary layer -/

open FreeRootFunctionalValuation in
/-- The stage inclusion on plane vectors. -/
noncomputable def planeStageInclusion :
    PlaneVector X K n →ₗ[K] PlaneVector X K (n + 1) :=
  LinearMap.prod
    ((stageInclusion X K n).comp (LinearMap.fst K _ _))
    ((stageInclusion X K n).comp (LinearMap.snd K _ _))

open Classical in
/-- **Nested mass transport**: the stage-`n` plane mass of `z` at a coarse
character is the total stage-`n+1` plane mass of the same vector over the
dual stage-inclusion fiber.  No conjugation is involved: the stage-`n`
plane is a subgroup of the stage-`n+1` plane. -/
theorem planeMass_eq_sum_fiber_stageInclusion (hψ : ψ ≠ 1) (z : E)
    (χ : Module.Dual K (PlaneVector X K n)) :
    planeMass X K i j k hik hjk n rho ψ χ z =
      ∑ χ' ∈ Finset.univ.filter
          (fun χ' : Module.Dual K (PlaneVector X K (n + 1)) ↦
            χ'.comp (planeStageInclusion X K n) = χ),
        planeMass X K i j k hik hjk (n + 1) rho ψ χ' z := by
  calc
    planeMass X K i j k hik hjk n rho ψ χ z =
        CharacterMass.mass ψ
          (fun v ↦ planeAction X K i j k hik hjk (n + 1) rho
            (planeStageInclusion X K n v)) χ z := rfl
    _ = ∑ χ' ∈ Finset.univ.filter
        (fun χ' : Module.Dual K (PlaneVector X K (n + 1)) ↦
          χ'.comp (planeStageInclusion X K n) = χ),
        planeMass X K i j k hik hjk (n + 1) rho ψ χ' z :=
      (CharacterMass.sum_mass_fiber_comp ψ _
        (planeAction_add X K i j k hik hjk (n + 1) rho) hψ
        (planeStageInclusion X K n) z χ).symm

open Classical in
/-- The total mass of the characters trivial on the first coordinate. -/
noncomputable def firstTrivialMass (z : E) : ℝ :=
  ∑ χ ∈ Finset.univ.filter
      (fun χ : Module.Dual K (PlaneVector X K n) ↦
        firstCoordinateChar X K n χ = 0),
    planeMass X K i j k hik hjk n rho ψ χ z

open Classical in
/-- The total mass of the characters trivial on the second coordinate. -/
noncomputable def secondTrivialMass (z : E) : ℝ :=
  ∑ χ ∈ Finset.univ.filter
      (fun χ : Module.Dual K (PlaneVector X K n) ↦
        secondCoordinateChar X K n χ = 0),
    planeMass X K i j k hik hjk n rho ψ χ z

open FreeRootFunctionalValuation in
open Classical in
/-- The total mass of the characters whose first coordinate is detected
exactly in the top degree of the stage. -/
noncomputable def firstBoundaryMass (z : E) : ℝ :=
  ∑ χ ∈ Finset.univ.filter
      (fun χ : Module.Dual K (PlaneVector X K n) ↦
        valuation X K (firstCoordinateChar X K n χ) = n),
    planeMass X K i j k hik hjk n rho ψ χ z

open FreeRootFunctionalValuation in
open Classical in
/-- The total mass of the characters whose second coordinate is detected
exactly in the top degree of the stage. -/
noncomputable def secondBoundaryMass (z : E) : ℝ :=
  ∑ χ ∈ Finset.univ.filter
      (fun χ : Module.Dual K (PlaneVector X K n) ↦
        valuation X K (secondCoordinateChar X K n χ) = n),
    planeMass X K i j k hik hjk n rho ψ χ z

theorem firstTrivialMass_nonneg (z : E) :
    0 ≤ firstTrivialMass X K i j k hik hjk n rho ψ z :=
  Finset.sum_nonneg fun χ _ ↦
    planeMass_nonneg X K i j k hik hjk n rho ψ χ z

theorem secondTrivialMass_nonneg (z : E) :
    0 ≤ secondTrivialMass X K i j k hik hjk n rho ψ z :=
  Finset.sum_nonneg fun χ _ ↦
    planeMass_nonneg X K i j k hik hjk n rho ψ χ z

theorem firstBoundaryMass_nonneg (z : E) :
    0 ≤ firstBoundaryMass X K i j k hik hjk n rho ψ z :=
  Finset.sum_nonneg fun χ _ ↦
    planeMass_nonneg X K i j k hik hjk n rho ψ χ z

theorem secondBoundaryMass_nonneg (z : E) :
    0 ≤ secondBoundaryMass X K i j k hik hjk n rho ψ z :=
  Finset.sum_nonneg fun χ _ ↦
    planeMass_nonneg X K i j k hik hjk n rho ψ χ z

open FreeRootFunctionalValuation in
open Classical in
/-- **The first-coordinate telescoping identity**: the trivial mass at one
stage splits exactly into the next trivial mass plus the boundary-layer
mass newly detected in the top degree. -/
theorem firstTrivialMass_eq_add_boundary (hψ : ψ ≠ 1) (z : E) :
    firstTrivialMass X K i j k hik hjk n rho ψ z =
      firstTrivialMass X K i j k hik hjk (n + 1) rho ψ z +
        firstBoundaryMass X K i j k hik hjk (n + 1) rho ψ z := by
  set T := Finset.univ.filter
    (fun χ : Module.Dual K (PlaneVector X K n) ↦
      firstCoordinateChar X K n χ = 0) with hT
  have h1 : firstTrivialMass X K i j k hik hjk n rho ψ z =
      ∑ χ ∈ T, ∑ χ' ∈ Finset.univ.filter
          (fun χ' : Module.Dual K (PlaneVector X K (n + 1)) ↦
            χ'.comp (planeStageInclusion X K n) = χ),
        planeMass X K i j k hik hjk (n + 1) rho ψ χ' z :=
    Finset.sum_congr rfl fun χ _ ↦
      planeMass_eq_sum_fiber_stageInclusion X K i j k hik hjk n rho ψ
        hψ z χ
  have hdisj : (T : Set (Module.Dual K
      (PlaneVector X K n))).PairwiseDisjoint
      (fun χ ↦ Finset.univ.filter
        (fun χ' : Module.Dual K (PlaneVector X K (n + 1)) ↦
          χ'.comp (planeStageInclusion X K n) = χ)) := by
    intro χ₁ _ χ₂ _ hne
    refine Finset.disjoint_left.2 fun χ' hm1 hm2 ↦ ?_
    rw [Finset.mem_filter] at hm1 hm2
    exact hne (hm1.2 ▸ hm2.2)
  have h2 : T.biUnion
      (fun χ ↦ Finset.univ.filter
        (fun χ' : Module.Dual K (PlaneVector X K (n + 1)) ↦
          χ'.comp (planeStageInclusion X K n) = χ)) =
    Finset.univ.filter
      (fun χ' : Module.Dual K (PlaneVector X K (n + 1)) ↦
        firstCoordinateChar X K (n + 1) χ' = 0 ∨
          valuation X K (firstCoordinateChar X K (n + 1) χ') = n + 1) := by
    ext χ'
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
      true_and, hT]
    constructor
    · rintro ⟨χ, hχ, rfl⟩
      have hres : restrictSucc X K
          (firstCoordinateChar X K (n + 1) χ') = 0 := hχ
      have hval : valuation X K (restrictSucc X K
          (firstCoordinateChar X K (n + 1) χ')) = n + 1 :=
        (valuation_eq_succ_iff X K _).2 hres
      have hmin := valuation_restrictSucc_eq_min X K
        (firstCoordinateChar X K (n + 1) χ')
      have hle := valuation_le_succ X K
        (firstCoordinateChar X K (n + 1) χ')
      by_cases hz : firstCoordinateChar X K (n + 1) χ' = 0
      · exact Or.inl hz
      · refine Or.inr ?_
        have := valuation_le_stage_of_ne_zero X K hz
        omega
    · intro h
      refine ⟨χ'.comp (planeStageInclusion X K n), ?_, rfl⟩
      show restrictSucc X K (firstCoordinateChar X K (n + 1) χ') = 0
      rcases h with hz | hval
      · rw [hz]
        rfl
      · rw [← valuation_eq_succ_iff X K
          (restrictSucc X K (firstCoordinateChar X K (n + 1) χ'))]
        have hmin := valuation_restrictSucc_eq_min X K
          (firstCoordinateChar X K (n + 1) χ')
        omega
  have h3 : (Finset.univ.filter
      (fun χ' : Module.Dual K (PlaneVector X K (n + 1)) ↦
        firstCoordinateChar X K (n + 1) χ' = 0 ∨
          valuation X K (firstCoordinateChar X K (n + 1) χ') = n + 1)) =
    (Finset.univ.filter
      (fun χ' : Module.Dual K (PlaneVector X K (n + 1)) ↦
        firstCoordinateChar X K (n + 1) χ' = 0)) ∪
      Finset.univ.filter
        (fun χ' : Module.Dual K (PlaneVector X K (n + 1)) ↦
          valuation X K (firstCoordinateChar X K (n + 1) χ') = n + 1) := by
    ext χ'
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ,
      true_and]
  have h4 : Disjoint
      (Finset.univ.filter
        (fun χ' : Module.Dual K (PlaneVector X K (n + 1)) ↦
          firstCoordinateChar X K (n + 1) χ' = 0))
      (Finset.univ.filter
        (fun χ' : Module.Dual K (PlaneVector X K (n + 1)) ↦
          valuation X K (firstCoordinateChar X K (n + 1) χ') = n + 1)) := by
    refine Finset.disjoint_left.2 fun χ' hm1 hm2 ↦ ?_
    rw [Finset.mem_filter] at hm1 hm2
    have := (valuation_eq_succ_iff X K
      (firstCoordinateChar X K (n + 1) χ')).2 hm1.2
    omega
  rw [firstTrivialMass] at h1 ⊢
  rw [h1, ← Finset.sum_biUnion hdisj, h2, h3, Finset.sum_union h4]
  rfl

open FreeRootFunctionalValuation in
open Classical in
/-- **The second-coordinate telescoping identity**. -/
theorem secondTrivialMass_eq_add_boundary (hψ : ψ ≠ 1) (z : E) :
    secondTrivialMass X K i j k hik hjk n rho ψ z =
      secondTrivialMass X K i j k hik hjk (n + 1) rho ψ z +
        secondBoundaryMass X K i j k hik hjk (n + 1) rho ψ z := by
  set T := Finset.univ.filter
    (fun χ : Module.Dual K (PlaneVector X K n) ↦
      secondCoordinateChar X K n χ = 0) with hT
  have h1 : secondTrivialMass X K i j k hik hjk n rho ψ z =
      ∑ χ ∈ T, ∑ χ' ∈ Finset.univ.filter
          (fun χ' : Module.Dual K (PlaneVector X K (n + 1)) ↦
            χ'.comp (planeStageInclusion X K n) = χ),
        planeMass X K i j k hik hjk (n + 1) rho ψ χ' z :=
    Finset.sum_congr rfl fun χ _ ↦
      planeMass_eq_sum_fiber_stageInclusion X K i j k hik hjk n rho ψ
        hψ z χ
  have hdisj : (T : Set (Module.Dual K
      (PlaneVector X K n))).PairwiseDisjoint
      (fun χ ↦ Finset.univ.filter
        (fun χ' : Module.Dual K (PlaneVector X K (n + 1)) ↦
          χ'.comp (planeStageInclusion X K n) = χ)) := by
    intro χ₁ _ χ₂ _ hne
    refine Finset.disjoint_left.2 fun χ' hm1 hm2 ↦ ?_
    rw [Finset.mem_filter] at hm1 hm2
    exact hne (hm1.2 ▸ hm2.2)
  have h2 : T.biUnion
      (fun χ ↦ Finset.univ.filter
        (fun χ' : Module.Dual K (PlaneVector X K (n + 1)) ↦
          χ'.comp (planeStageInclusion X K n) = χ)) =
    Finset.univ.filter
      (fun χ' : Module.Dual K (PlaneVector X K (n + 1)) ↦
        secondCoordinateChar X K (n + 1) χ' = 0 ∨
          valuation X K (secondCoordinateChar X K (n + 1) χ') = n + 1) := by
    ext χ'
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
      true_and, hT]
    constructor
    · rintro ⟨χ, hχ, rfl⟩
      have hres : restrictSucc X K
          (secondCoordinateChar X K (n + 1) χ') = 0 := hχ
      have hval : valuation X K (restrictSucc X K
          (secondCoordinateChar X K (n + 1) χ')) = n + 1 :=
        (valuation_eq_succ_iff X K _).2 hres
      have hmin := valuation_restrictSucc_eq_min X K
        (secondCoordinateChar X K (n + 1) χ')
      have hle := valuation_le_succ X K
        (secondCoordinateChar X K (n + 1) χ')
      by_cases hz : secondCoordinateChar X K (n + 1) χ' = 0
      · exact Or.inl hz
      · refine Or.inr ?_
        have := valuation_le_stage_of_ne_zero X K hz
        omega
    · intro h
      refine ⟨χ'.comp (planeStageInclusion X K n), ?_, rfl⟩
      show restrictSucc X K (secondCoordinateChar X K (n + 1) χ') = 0
      rcases h with hz | hval
      · rw [hz]
        rfl
      · rw [← valuation_eq_succ_iff X K
          (restrictSucc X K (secondCoordinateChar X K (n + 1) χ'))]
        have hmin := valuation_restrictSucc_eq_min X K
          (secondCoordinateChar X K (n + 1) χ')
        omega
  have h3 : (Finset.univ.filter
      (fun χ' : Module.Dual K (PlaneVector X K (n + 1)) ↦
        secondCoordinateChar X K (n + 1) χ' = 0 ∨
          valuation X K (secondCoordinateChar X K (n + 1) χ') = n + 1)) =
    (Finset.univ.filter
      (fun χ' : Module.Dual K (PlaneVector X K (n + 1)) ↦
        secondCoordinateChar X K (n + 1) χ' = 0)) ∪
      Finset.univ.filter
        (fun χ' : Module.Dual K (PlaneVector X K (n + 1)) ↦
          valuation X K (secondCoordinateChar X K (n + 1) χ') = n + 1) := by
    ext χ'
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ,
      true_and]
  have h4 : Disjoint
      (Finset.univ.filter
        (fun χ' : Module.Dual K (PlaneVector X K (n + 1)) ↦
          secondCoordinateChar X K (n + 1) χ' = 0))
      (Finset.univ.filter
        (fun χ' : Module.Dual K (PlaneVector X K (n + 1)) ↦
          valuation X K (secondCoordinateChar X K (n + 1) χ') = n + 1)) := by
    refine Finset.disjoint_left.2 fun χ' hm1 hm2 ↦ ?_
    rw [Finset.mem_filter] at hm1 hm2
    have := (valuation_eq_succ_iff X K
      (secondCoordinateChar X K (n + 1) χ')).2 hm1.2
    omega
  rw [secondTrivialMass] at h1 ⊢
  rw [h1, ← Finset.sum_biUnion hdisj, h2, h3, Finset.sum_union h4]
  rfl

/-- **The first boundary layer vanishes in the limit**: the nested trivial
masses are nonincreasing and bounded, so their consecutive drops tend to
zero. -/
theorem tendsto_firstBoundaryMass_zero (hψ : ψ ≠ 1) (z : E) :
    Filter.Tendsto
      (fun m ↦ firstBoundaryMass X K i j k hik hjk (m + 1) rho ψ z)
      Filter.atTop (nhds 0) := by
  set T : ℕ → ℝ := fun m ↦ firstTrivialMass X K i j k hik hjk m rho ψ z
    with hTdef
  have hanti : Antitone T := by
    refine antitone_nat_of_succ_le fun m ↦ ?_
    have := firstTrivialMass_eq_add_boundary X K i j k hik hjk m rho ψ
      hψ z
    have hb := firstBoundaryMass_nonneg X K i j k hik hjk (m + 1) rho ψ z
    rw [hTdef]
    beta_reduce
    linarith
  have hbdd : BddBelow (Set.range T) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨m, rfl⟩
    exact firstTrivialMass_nonneg X K i j k hik hjk m rho ψ z
  have hconv := tendsto_atTop_ciInf hanti hbdd
  have hsucc : Filter.Tendsto (fun m ↦ T (m + 1)) Filter.atTop
      (nhds (⨅ m, T m)) :=
    (Filter.tendsto_add_atTop_iff_nat 1).2 hconv
  have heq : (fun m ↦
      firstBoundaryMass X K i j k hik hjk (m + 1) rho ψ z) =
    fun m ↦ T m - T (m + 1) := by
    funext m
    have := firstTrivialMass_eq_add_boundary X K i j k hik hjk m rho ψ
      hψ z
    rw [hTdef]
    beta_reduce
    linarith
  rw [heq]
  simpa using hconv.sub hsucc

/-- **The second boundary layer vanishes in the limit**. -/
theorem tendsto_secondBoundaryMass_zero (hψ : ψ ≠ 1) (z : E) :
    Filter.Tendsto
      (fun m ↦ secondBoundaryMass X K i j k hik hjk (m + 1) rho ψ z)
      Filter.atTop (nhds 0) := by
  set T : ℕ → ℝ := fun m ↦ secondTrivialMass X K i j k hik hjk m rho ψ z
    with hTdef
  have hanti : Antitone T := by
    refine antitone_nat_of_succ_le fun m ↦ ?_
    have := secondTrivialMass_eq_add_boundary X K i j k hik hjk m rho ψ
      hψ z
    have hb := secondBoundaryMass_nonneg X K i j k hik hjk (m + 1) rho ψ z
    rw [hTdef]
    beta_reduce
    linarith
  have hbdd : BddBelow (Set.range T) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨m, rfl⟩
    exact secondTrivialMass_nonneg X K i j k hik hjk m rho ψ z
  have hconv := tendsto_atTop_ciInf hanti hbdd
  have hsucc : Filter.Tendsto (fun m ↦ T (m + 1)) Filter.atTop
      (nhds (⨅ m, T m)) :=
    (Filter.tendsto_add_atTop_iff_nat 1).2 hconv
  have heq : (fun m ↦
      secondBoundaryMass X K i j k hik hjk (m + 1) rho ψ z) =
    fun m ↦ T m - T (m + 1) := by
    funext m
    have := secondTrivialMass_eq_add_boundary X K i j k hik hjk m rho ψ
      hψ z
    rw [hTdef]
    beta_reduce
    linarith
  rw [heq]
  simpa using hconv.sub hsucc


open FreeRootFunctionalValuation in
open Classical in
/-- **Cross-stage region monotonicity**: for any region predicate, the
selected mass at one stage is bounded by the selected mass at the next
stage plus both boundary layers. -/
theorem sum_planeMass_region_le_succ_add_boundaries (hψ : ψ ≠ 1) (z : E)
    (P : ValuationRegion → Prop) [DecidablePred P] :
    ∑ χ ∈ Finset.univ.filter
        (fun χ : Module.Dual K (PlaneVector X K n) ↦
          P (pairRegion X K (firstCoordinateChar X K n χ)
            (secondCoordinateChar X K n χ))),
      planeMass X K i j k hik hjk n rho ψ χ z ≤
    (∑ χ' ∈ Finset.univ.filter
        (fun χ' : Module.Dual K (PlaneVector X K (n + 1)) ↦
          P (pairRegion X K (firstCoordinateChar X K (n + 1) χ')
            (secondCoordinateChar X K (n + 1) χ'))),
      planeMass X K i j k hik hjk (n + 1) rho ψ χ' z) +
      firstBoundaryMass X K i j k hik hjk (n + 1) rho ψ z +
      secondBoundaryMass X K i j k hik hjk (n + 1) rho ψ z := by
  set S := Finset.univ.filter
    (fun χ : Module.Dual K (PlaneVector X K n) ↦
      P (pairRegion X K (firstCoordinateChar X K n χ)
        (secondCoordinateChar X K n χ))) with hS
  set F := Finset.univ.filter
    (fun χ' : Module.Dual K (PlaneVector X K (n + 1)) ↦
      P (pairRegion X K (firstCoordinateChar X K (n + 1) χ')
        (secondCoordinateChar X K (n + 1) χ'))) with hF
  set B₁ := Finset.univ.filter
    (fun χ' : Module.Dual K (PlaneVector X K (n + 1)) ↦
      valuation X K (firstCoordinateChar X K (n + 1) χ') = n + 1)
    with hB₁
  set B₂ := Finset.univ.filter
    (fun χ' : Module.Dual K (PlaneVector X K (n + 1)) ↦
      valuation X K (secondCoordinateChar X K (n + 1) χ') = n + 1)
    with hB₂
  have h1 : (∑ χ ∈ S, planeMass X K i j k hik hjk n rho ψ χ z) =
      ∑ χ ∈ S, ∑ χ' ∈ Finset.univ.filter
          (fun χ' : Module.Dual K (PlaneVector X K (n + 1)) ↦
            χ'.comp (planeStageInclusion X K n) = χ),
        planeMass X K i j k hik hjk (n + 1) rho ψ χ' z :=
    Finset.sum_congr rfl fun χ _ ↦
      planeMass_eq_sum_fiber_stageInclusion X K i j k hik hjk n rho ψ
        hψ z χ
  have hdisj : (S : Set (Module.Dual K
      (PlaneVector X K n))).PairwiseDisjoint
      (fun χ ↦ Finset.univ.filter
        (fun χ' : Module.Dual K (PlaneVector X K (n + 1)) ↦
          χ'.comp (planeStageInclusion X K n) = χ)) := by
    intro χ₁ _ χ₂ _ hne
    refine Finset.disjoint_left.2 fun χ' hm1 hm2 ↦ ?_
    rw [Finset.mem_filter] at hm1 hm2
    exact hne (hm1.2 ▸ hm2.2)
  have hsubset : S.biUnion
      (fun χ ↦ Finset.univ.filter
        (fun χ' : Module.Dual K (PlaneVector X K (n + 1)) ↦
          χ'.comp (planeStageInclusion X K n) = χ)) ⊆
      (F ∪ B₁) ∪ B₂ := by
    intro χ' hχ'
    obtain ⟨χ, hχS, hfib⟩ := Finset.mem_biUnion.1 hχ'
    rw [Finset.mem_filter] at hfib
    rw [hS, Finset.mem_filter] at hχS
    have hcoarse : P (pairRegion X K
        (restrictSucc X K (firstCoordinateChar X K (n + 1) χ'))
        (restrictSucc X K (secondCoordinateChar X K (n + 1) χ'))) := by
      have hchi : firstCoordinateChar X K n
            (χ'.comp (planeStageInclusion X K n)) =
          restrictSucc X K (firstCoordinateChar X K (n + 1) χ') := rfl
      have hchi2 : secondCoordinateChar X K n
            (χ'.comp (planeStageInclusion X K n)) =
          restrictSucc X K (secondCoordinateChar X K (n + 1) χ') := rfl
      rw [← hchi, ← hchi2, hfib.2]
      exact hχS.2
    by_cases hv1 : valuation X K
        (firstCoordinateChar X K (n + 1) χ') = n + 1
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, hv1⟩))
    by_cases hv2 : valuation X K
        (secondCoordinateChar X K (n + 1) χ') = n + 1
    · exact Finset.mem_union_right _
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, hv2⟩)
    refine Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩))
    rwa [← pairRegion_restrictSucc_of_ne_top X K _ _ hv1 hv2]
  calc
    (∑ χ ∈ S, planeMass X K i j k hik hjk n rho ψ χ z) =
        ∑ χ' ∈ S.biUnion
          (fun χ ↦ Finset.univ.filter
            (fun χ' : Module.Dual K (PlaneVector X K (n + 1)) ↦
              χ'.comp (planeStageInclusion X K n) = χ)),
          planeMass X K i j k hik hjk (n + 1) rho ψ χ' z := by
      rw [h1, Finset.sum_biUnion hdisj]
    _ ≤ ∑ χ' ∈ (F ∪ B₁) ∪ B₂,
        planeMass X K i j k hik hjk (n + 1) rho ψ χ' z :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        fun χ' _ _ ↦ planeMass_nonneg X K i j k hik hjk (n + 1) rho ψ χ' z
    _ ≤ (∑ χ' ∈ F ∪ B₁,
          planeMass X K i j k hik hjk (n + 1) rho ψ χ' z) +
        ∑ χ' ∈ B₂,
          planeMass X K i j k hik hjk (n + 1) rho ψ χ' z := by
      have hui := Finset.sum_union_inter
        (s₁ := F ∪ B₁) (s₂ := B₂)
        (f := fun χ' ↦ planeMass X K i j k hik hjk (n + 1) rho ψ χ' z)
      have hpos : 0 ≤ ∑ χ' ∈ (F ∪ B₁) ∩ B₂,
          planeMass X K i j k hik hjk (n + 1) rho ψ χ' z :=
        Finset.sum_nonneg fun χ' _ ↦
          planeMass_nonneg X K i j k hik hjk (n + 1) rho ψ χ' z
      linarith
    _ ≤ ((∑ χ' ∈ F,
          planeMass X K i j k hik hjk (n + 1) rho ψ χ' z) +
        ∑ χ' ∈ B₁,
          planeMass X K i j k hik hjk (n + 1) rho ψ χ' z) +
        ∑ χ' ∈ B₂,
          planeMass X K i j k hik hjk (n + 1) rho ψ χ' z := by
      have hui := Finset.sum_union_inter (s₁ := F) (s₂ := B₁)
        (f := fun χ' ↦ planeMass X K i j k hik hjk (n + 1) rho ψ χ' z)
      have hpos : 0 ≤ ∑ χ' ∈ F ∩ B₁,
          planeMass X K i j k hik hjk (n + 1) rho ψ χ' z :=
        Finset.sum_nonneg fun χ' _ ↦
          planeMass_nonneg X K i j k hik hjk (n + 1) rho ψ χ' z
      linarith
    _ = (∑ χ' ∈ F,
          planeMass X K i j k hik hjk (n + 1) rho ψ χ' z) +
        firstBoundaryMass X K i j k hik hjk (n + 1) rho ψ z +
        secondBoundaryMass X K i j k hik hjk (n + 1) rho ψ z := rfl


open FreeRootFunctionalValuation in
omit [Fintype K] in
/-- **Coarse-image classification along the opposite shear**: a fine
character in region `A` or `B`, whose second functional lies strictly
below the top degree and descends by exactly one along `x`, has coarse
opposite-shear image in region `C` — or `D` at the lowest level. -/
theorem coarse_pairRegion_of_fine_AB_opposite (x : X)
    (χ' : Module.Dual K (PlaneVector X K (n + 1)))
    (hAB : pairRegion X K (firstCoordinateChar X K (n + 1) χ')
        (secondCoordinateChar X K (n + 1) χ') = .A ∨
      pairRegion X K (firstCoordinateChar X K (n + 1) χ')
        (secondCoordinateChar X K (n + 1) χ') = .B)
    (hint : valuation X K (secondCoordinateChar X K (n + 1) χ') ≤ n)
    (hlead : valuation X K
        (leftDerived X K (secondCoordinateChar X K (n + 1) χ') x) + 1 =
      valuation X K (secondCoordinateChar X K (n + 1) χ')) :
    pairRegion X K
        (firstCoordinateChar X K n (χ'.comp (oppositeShear X K n x)))
        (secondCoordinateChar X K n
          (χ'.comp (oppositeShear X K n x))) = .C ∨
      pairRegion X K
        (firstCoordinateChar X K n (χ'.comp (oppositeShear X K n x)))
        (secondCoordinateChar X K n
          (χ'.comp (oppositeShear X K n x))) = .D := by
  set φ₁ := firstCoordinateChar X K (n + 1) χ' with hφ₁
  set φ₂ := secondCoordinateChar X K (n + 1) χ' with hφ₂
  have hdata : valuation X K φ₂ ≠ 0 ∧
      valuation X K φ₂ ≤ valuation X K φ₁ := by
    rcases hAB with hA | hB
    · obtain ⟨-, -, h2ne, hlt⟩ := pairRegion_A_data X K _ _ hA
      exact ⟨h2ne, hlt.le⟩
    · obtain ⟨-, -, h2ne, heq⟩ := pairRegion_B_data X K _ _ hB
      exact ⟨h2ne, heq.symm.le⟩
  obtain ⟨h2ne, hle⟩ := hdata
  rw [firstCoordinateChar_comp_oppositeShear X K n x χ',
    secondCoordinateChar_comp_oppositeShear X K n x χ', ← hφ₁, ← hφ₂]
  have hmin1 := valuation_restrictSucc_eq_min X K φ₁
  have hmin2 := valuation_restrictSucc_eq_min X K φ₂
  have hfirst : valuation X K
      (restrictSucc X K φ₁ + leftDerived X K φ₂ x) =
    valuation X K φ₂ - 1 := by
    have hadd := valuation_add_of_lt X K (leftDerived X K φ₂ x)
      (restrictSucc X K φ₁) (by omega)
    rw [show leftDerived X K φ₂ x + restrictSucc X K φ₁ =
      restrictSucc X K φ₁ + leftDerived X K φ₂ x by abel] at hadd
    omega
  have hsecond : valuation X K (restrictSucc X K φ₂) =
      valuation X K φ₂ := by
    omega
  rcases Nat.eq_or_lt_of_le
      (Nat.one_le_iff_ne_zero.2 h2ne) with h1 | h2
  · right
    exact pairRegion_eq_D_of_left_zero X K _ _ (by omega)
  · left
    exact pairRegion_eq_C_of_pos_of_lt X K _ _ (by omega) (by omega)

open FreeRootFunctionalValuation in
omit [Fintype K] in
/-- **Coarse-image classification along the forward shear**: a fine
character in region `C` or `B`, whose first functional lies strictly
below the top degree and descends by exactly one along `x`, has coarse
forward-shear image in region `A` — or `D` at the lowest level. -/
theorem coarse_pairRegion_of_fine_CB_forward (x : X)
    (χ' : Module.Dual K (PlaneVector X K (n + 1)))
    (hCB : pairRegion X K (firstCoordinateChar X K (n + 1) χ')
        (secondCoordinateChar X K (n + 1) χ') = .C ∨
      pairRegion X K (firstCoordinateChar X K (n + 1) χ')
        (secondCoordinateChar X K (n + 1) χ') = .B)
    (hint : valuation X K (firstCoordinateChar X K (n + 1) χ') ≤ n)
    (hlead : valuation X K
        (leftDerived X K (firstCoordinateChar X K (n + 1) χ') x) + 1 =
      valuation X K (firstCoordinateChar X K (n + 1) χ')) :
    pairRegion X K
        (firstCoordinateChar X K n (χ'.comp (forwardShear X K n x)))
        (secondCoordinateChar X K n
          (χ'.comp (forwardShear X K n x))) = .A ∨
      pairRegion X K
        (firstCoordinateChar X K n (χ'.comp (forwardShear X K n x)))
        (secondCoordinateChar X K n
          (χ'.comp (forwardShear X K n x))) = .D := by
  set φ₁ := firstCoordinateChar X K (n + 1) χ' with hφ₁
  set φ₂ := secondCoordinateChar X K (n + 1) χ' with hφ₂
  have hdata : valuation X K φ₁ ≠ 0 ∧
      valuation X K φ₁ ≤ valuation X K φ₂ := by
    rcases hCB with hC | hB
    · obtain ⟨-, h1ne, -, hlt⟩ := pairRegion_C_data X K _ _ hC
      exact ⟨h1ne, hlt.le⟩
    · obtain ⟨-, h1ne, -, heq⟩ := pairRegion_B_data X K _ _ hB
      exact ⟨h1ne, heq.le⟩
  obtain ⟨h1ne, hle⟩ := hdata
  rw [firstCoordinateChar_comp_forwardShear X K n x χ',
    secondCoordinateChar_comp_forwardShear X K n x χ', ← hφ₁, ← hφ₂]
  have hmin1 := valuation_restrictSucc_eq_min X K φ₁
  have hmin2 := valuation_restrictSucc_eq_min X K φ₂
  have hsecond : valuation X K
      (leftDerived X K φ₁ x + restrictSucc X K φ₂) =
    valuation X K φ₁ - 1 := by
    have hadd := valuation_add_of_lt X K (leftDerived X K φ₁ x)
      (restrictSucc X K φ₂) (by omega)
    omega
  have hfirst : valuation X K (restrictSucc X K φ₁) =
      valuation X K φ₁ := by
    omega
  rcases Nat.eq_or_lt_of_le
      (Nat.one_le_iff_ne_zero.2 h1ne) with h1 | h2
  · right
    exact pairRegion_eq_D_of_right_zero X K _ _ (by omega)
  · left
    exact pairRegion_eq_A_of_pos_of_lt X K _ _ (by omega) (by omega)


open FreeRootFunctionalValuation in
open Classical in
/-- **The same-vector `A ∪ B` descent estimate**: the total fine mass in
regions `A` and `B` is bounded by the coarse mass in regions `C` and `D`
of the same vector, plus one opposite-generator displacement error per
alphabet letter, plus the second boundary layer.  Every interior fine
character is charged through the opposite shear of the canonical least
leading generator of its second functional; the receiving coarse
characters remember that generator, so the images over distinct letters
are disjoint. -/
theorem sum_planeMass_AB_le_coarse_CD (hψ : ψ ≠ 1) (z : E) :
    ∑ χ' ∈ Finset.univ.filter
        (fun χ' : Module.Dual K (PlaneVector X K (n + 2)) ↦
          pairRegion X K (firstCoordinateChar X K (n + 2) χ')
            (secondCoordinateChar X K (n + 2) χ') = .A ∨
          pairRegion X K (firstCoordinateChar X K (n + 2) χ')
            (secondCoordinateChar X K (n + 2) χ') = .B),
      planeMass X K i j k hik hjk (n + 2) rho ψ χ' z ≤
    (∑ η ∈ Finset.univ.filter
        (fun η : Module.Dual K (PlaneVector X K (n + 1)) ↦
          pairRegion X K (firstCoordinateChar X K (n + 1) η)
            (secondCoordinateChar X K (n + 1) η) = .C ∨
          pairRegion X K (firstCoordinateChar X K (n + 1) η)
            (secondCoordinateChar X K (n + 1) η) = .D),
      planeMass X K i j k hik hjk (n + 1) rho ψ η z) +
      (∑ x : X, 2 * ‖z‖ *
        ‖rho (elementaryRoot j i hij.symm (FreeAlgebra.ι K x)) z - z‖) +
      secondBoundaryMass X K i j k hik hjk (n + 2) rho ψ z := by
  set S := Finset.univ.filter
    (fun χ' : Module.Dual K (PlaneVector X K (n + 2)) ↦
      pairRegion X K (firstCoordinateChar X K (n + 2) χ')
        (secondCoordinateChar X K (n + 2) χ') = .A ∨
      pairRegion X K (firstCoordinateChar X K (n + 2) χ')
        (secondCoordinateChar X K (n + 2) χ') = .B) with hS
  set CD := Finset.univ.filter
    (fun η : Module.Dual K (PlaneVector X K (n + 1)) ↦
      pairRegion X K (firstCoordinateChar X K (n + 1) η)
        (secondCoordinateChar X K (n + 1) η) = .C ∨
      pairRegion X K (firstCoordinateChar X K (n + 1) η)
        (secondCoordinateChar X K (n + 1) η) = .D) with hCD
  -- interior/boundary split of the fine source
  have hsplit := Finset.sum_filter_add_sum_filter_not S
    (fun χ' ↦ valuation X K
      (secondCoordinateChar X K (n + 2) χ') ≤ n + 1)
    (fun χ' ↦ planeMass X K i j k hik hjk (n + 2) rho ψ χ' z)
  set Si := S.filter
    (fun χ' ↦ valuation X K
      (secondCoordinateChar X K (n + 2) χ') ≤ n + 1) with hSi
  have hboundary : (∑ χ' ∈ S.filter
      (fun χ' ↦ ¬ valuation X K
        (secondCoordinateChar X K (n + 2) χ') ≤ n + 1),
      planeMass X K i j k hik hjk (n + 2) rho ψ χ' z) ≤
    secondBoundaryMass X K i j k hik hjk (n + 2) rho ψ z := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_
      fun χ' _ _ ↦ planeMass_nonneg X K i j k hik hjk (n + 2) rho ψ χ' z
    intro χ' hχ'
    rw [Finset.mem_filter, hS, Finset.mem_filter] at hχ'
    obtain ⟨⟨-, hreg⟩, htop⟩ := hχ'
    have hne : valuation X K
        (secondCoordinateChar X K (n + 2) χ') ≠ 0 ∧
        ¬(valuation X K (firstCoordinateChar X K (n + 2) χ') = n + 3 ∧
          valuation X K (secondCoordinateChar X K (n + 2) χ') = n + 3) ∧
        valuation X K (secondCoordinateChar X K (n + 2) χ') ≤
          valuation X K (firstCoordinateChar X K (n + 2) χ') := by
      rcases hreg with hA | hB
      · obtain ⟨hz2, -, h2ne, hlt⟩ := pairRegion_A_data X K _ _ hA
        exact ⟨h2ne, hz2, hlt.le⟩
      · obtain ⟨hz2, -, h2ne, heq⟩ := pairRegion_B_data X K _ _ hB
        exact ⟨h2ne, hz2, heq.symm.le⟩
    obtain ⟨h2ne, hz2, hle2⟩ := hne
    have hb1 := valuation_le_succ X K
      (firstCoordinateChar X K (n + 2) χ')
    have hb2 := valuation_le_succ X K
      (secondCoordinateChar X K (n + 2) χ')
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    omega
  -- selector partition of the interior part
  set selIdx : Module.Dual K (PlaneVector X K (n + 2)) →
      Fin (Fintype.card X + 1) := fun χ' ↦
    if h : leastLeadingGeneratorIndex X K
        (secondCoordinateChar X K (n + 2) χ') < Fintype.card X then
      ⟨leastLeadingGeneratorIndex X K
        (secondCoordinateChar X K (n + 2) χ'), Nat.lt_succ_of_lt h⟩
    else Fin.last (Fintype.card X) with hselIdx
  have hleadset : ∀ χ' ∈ Si,
      (leadingGeneratorIndexSet X K
        (secondCoordinateChar X K (n + 2) χ')).Nonempty := by
    intro χ' hχ'
    rw [hSi, Finset.mem_filter, hS, Finset.mem_filter] at hχ'
    obtain ⟨⟨-, hreg⟩, hint⟩ := hχ'
    have h2ne : valuation X K
        (secondCoordinateChar X K (n + 2) χ') ≠ 0 := by
      rcases hreg with hA | hB
      · exact (pairRegion_A_data X K _ _ hA).2.2.1
      · exact (pairRegion_B_data X K _ _ hB).2.2.1
    refine leadingGeneratorIndexSet_nonempty X K _ ?_ (by omega)
    by_contra hnone
    have := valuation_eq_succ_of_not_exists X K _ hnone
    omega
  have hpartition : (∑ χ' ∈ Si,
      planeMass X K i j k hik hjk (n + 2) rho ψ χ' z) =
    ∑ q : Fin (Fintype.card X + 1),
      ∑ χ' ∈ Si.filter (fun χ' ↦ selIdx χ' = q),
        planeMass X K i j k hik hjk (n + 2) rho ψ χ' z :=
    (Finset.sum_fiberwise Si selIdx _).symm
  have hlast : Si.filter
      (fun χ' ↦ selIdx χ' = Fin.last (Fintype.card X)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro χ' hχ'
    have hlt := leastLeadingGeneratorIndex_lt_card X K
      (secondCoordinateChar X K (n + 2) χ') (hleadset χ' hχ')
    rw [hselIdx]
    beta_reduce
    rw [dif_pos hlt]
    intro hcontra
    have := congrArg Fin.val hcontra
    simp only [Fin.val_last] at this
    omega
  -- the per-letter charge
  have hperq : ∀ q : Fin (Fintype.card X),
      (∑ χ' ∈ Si.filter (fun χ' ↦ selIdx χ' = q.castSucc),
        planeMass X K i j k hik hjk (n + 2) rho ψ χ' z) ≤
      (∑ η ∈ Finset.univ.filter
          (fun η : Module.Dual K (PlaneVector X K (n + 1)) ↦
            (pairRegion X K (firstCoordinateChar X K (n + 1) η)
              (secondCoordinateChar X K (n + 1) η) = .C ∨
            pairRegion X K (firstCoordinateChar X K (n + 1) η)
              (secondCoordinateChar X K (n + 1) η) = .D) ∧
            leastLeadingGeneratorIndex X K
              (secondCoordinateChar X K (n + 1) η) = (q : ℕ)),
        planeMass X K i j k hik hjk (n + 1) rho ψ η z) +
        2 * ‖z‖ * ‖rho (elementaryRoot j i hij.symm
          (FreeAlgebra.ι K (generatorEnumeration X q))) z - z‖ := by
    intro q
    set x := generatorEnumeration X q with hx
    set u := rho (elementaryRoot j i hij.symm (FreeAlgebra.ι K x))
      with hu
    set Sq := Si.filter (fun χ' ↦ selIdx χ' = q.castSucc) with hSq
    set Uq := Finset.univ.filter
      (fun η : Module.Dual K (PlaneVector X K (n + 1)) ↦
        (pairRegion X K (firstCoordinateChar X K (n + 1) η)
          (secondCoordinateChar X K (n + 1) η) = .C ∨
        pairRegion X K (firstCoordinateChar X K (n + 1) η)
          (secondCoordinateChar X K (n + 1) η) = .D) ∧
        leastLeadingGeneratorIndex X K
          (secondCoordinateChar X K (n + 1) η) = (q : ℕ)) with hUq
    -- facts shared by every member of the fiber part
    have hmem : ∀ χ' ∈ Sq,
        χ'.comp (oppositeShear X K (n + 1) x) ∈ Uq := by
      intro χ' hχ'
      rw [hSq, Finset.mem_filter] at hχ'
      obtain ⟨hSi', hsel⟩ := hχ'
      rw [hSi, Finset.mem_filter, hS, Finset.mem_filter] at hSi'
      obtain ⟨⟨-, hreg⟩, hint⟩ := hSi'
      have hne : (leadingGeneratorIndexSet X K
          (secondCoordinateChar X K (n + 2) χ')).Nonempty :=
        hleadset χ' (by
          rw [hSi, Finset.mem_filter, hS, Finset.mem_filter]
          exact ⟨⟨Finset.mem_univ _, hreg⟩, hint⟩)
      have hltcard := leastLeadingGeneratorIndex_lt_card X K
        (secondCoordinateChar X K (n + 2) χ') hne
      have hidx : leastLeadingGeneratorIndex X K
          (secondCoordinateChar X K (n + 2) χ') = (q : ℕ) := by
        have := hsel
        rw [hselIdx] at this
        beta_reduce at this
        rw [dif_pos hltcard] at this
        have hval := congrArg Fin.val this
        simpa using hval
      have hqfin : q = (⟨leastLeadingGeneratorIndex X K
          (secondCoordinateChar X K (n + 2) χ'), hltcard⟩ :
            Fin (Fintype.card X)) := by
        apply Fin.ext
        show (q : ℕ) = leastLeadingGeneratorIndex X K
          (secondCoordinateChar X K (n + 2) χ')
        omega
      have hxval : x = generatorEnumeration X
          ⟨leastLeadingGeneratorIndex X K
            (secondCoordinateChar X K (n + 2) χ'), hltcard⟩ := by
        rw [hx, hqfin]
      have hlead : valuation X K
          (leftDerived X K
            (secondCoordinateChar X K (n + 2) χ') x) + 1 =
        valuation X K (secondCoordinateChar X K (n + 2) χ') := by
        rw [hxval]
        exact leastLeadingGeneratorIndex_spec X K _ hne
      have hregion := coarse_pairRegion_of_fine_AB_opposite
        X K (n + 1) x χ' hreg hint hlead
      have hsecondid : secondCoordinateChar X K (n + 1)
          (χ'.comp (oppositeShear X K (n + 1) x)) =
        restrictSucc X K (secondCoordinateChar X K (n + 2) χ') :=
        secondCoordinateChar_comp_oppositeShear X K (n + 1) x χ'
      have htag : leastLeadingGeneratorIndex X K
          (secondCoordinateChar X K (n + 1)
            (χ'.comp (oppositeShear X K (n + 1) x))) = (q : ℕ) := by
        rw [hsecondid,
          leastLeadingGeneratorIndex_restrictSucc X K
            (secondCoordinateChar X K (n + 2) χ') (by omega)]
        exact hidx
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hregion, htag⟩
    -- fibers over distinct coarse characters are disjoint
    have hdisj : (Uq : Set (Module.Dual K
        (PlaneVector X K (n + 1)))).PairwiseDisjoint
        (fun η ↦ Finset.univ.filter
          (fun χ'' : Module.Dual K (PlaneVector X K (n + 2)) ↦
            χ''.comp (oppositeShear X K (n + 1) x) = η)) := by
      intro η₁ _ η₂ _ hne
      refine Finset.disjoint_left.2 fun χ'' h1 h2 ↦ ?_
      rw [Finset.mem_filter] at h1 h2
      exact hne (h1.2 ▸ h2.2)
    have huu : ∀ w : E, u (u⁻¹ w) = w := by
      intro w
      change (u * u⁻¹) w = w
      rw [mul_inv_cancel]
      rfl
    have htransport : ∀ η ∈ Uq,
        planeMass X K i j k hik hjk (n + 1) rho ψ η (u⁻¹ z) =
        ∑ χ'' ∈ Finset.univ.filter
            (fun χ'' : Module.Dual K (PlaneVector X K (n + 2)) ↦
              χ''.comp (oppositeShear X K (n + 1) x) = η),
          planeMass X K i j k hik hjk (n + 2) rho ψ χ'' z := by
      intro η _
      have h := planeMass_eq_sum_fiber_oppositeShear X K i j k hij
        hik hjk (n + 1) rho ψ hψ x (u⁻¹ z) η
      rw [← hu] at h
      rw [huu z] at h
      exact h
    have hchain : (∑ χ' ∈ Sq,
        planeMass X K i j k hik hjk (n + 2) rho ψ χ' z) ≤
      ∑ η ∈ Uq, planeMass X K i j k hik hjk (n + 1) rho ψ η (u⁻¹ z) := by
      calc
        (∑ χ' ∈ Sq,
            planeMass X K i j k hik hjk (n + 2) rho ψ χ' z) ≤
          ∑ χ' ∈ Uq.biUnion
            (fun η ↦ Finset.univ.filter
              (fun χ'' : Module.Dual K (PlaneVector X K (n + 2)) ↦
                χ''.comp (oppositeShear X K (n + 1) x) = η)),
            planeMass X K i j k hik hjk (n + 2) rho ψ χ' z := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_
            fun χ' _ _ ↦
              planeMass_nonneg X K i j k hik hjk (n + 2) rho ψ χ' z
          intro χ' hχ'
          refine Finset.mem_biUnion.2
            ⟨χ'.comp (oppositeShear X K (n + 1) x), hmem χ' hχ', ?_⟩
          exact Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩
        _ = ∑ η ∈ Uq, ∑ χ'' ∈ Finset.univ.filter
            (fun χ'' : Module.Dual K (PlaneVector X K (n + 2)) ↦
              χ''.comp (oppositeShear X K (n + 1) x) = η),
            planeMass X K i j k hik hjk (n + 2) rho ψ χ'' z :=
          Finset.sum_biUnion hdisj
        _ = ∑ η ∈ Uq,
            planeMass X K i j k hik hjk (n + 1) rho ψ η (u⁻¹ z) :=
          (Finset.sum_congr rfl htransport).symm
    have hcont : (∑ η ∈ Uq,
        planeMass X K i j k hik hjk (n + 1) rho ψ η (u⁻¹ z)) ≤
      (∑ η ∈ Uq, planeMass X K i j k hik hjk (n + 1) rho ψ η z) +
        2 * ‖z‖ * ‖u z - z‖ := by
      have habs := CharacterMass.abs_sum_mass_sub_sum_mass_le ψ
        (planeAction X K i j k hik hjk (n + 1) rho)
        (planeAction_add X K i j k hik hjk (n + 1) rho) hψ
        Uq (u⁻¹ z) z
      have hnorm1 : ‖(u⁻¹ : E ≃ₗᵢ[ℝ] E) z‖ = ‖z‖ :=
        (u⁻¹ : E ≃ₗᵢ[ℝ] E).norm_map z
      have hnorm2 : ‖(u⁻¹ : E ≃ₗᵢ[ℝ] E) z - z‖ = ‖u z - z‖ := by
        have hmap : u ((u⁻¹ : E ≃ₗᵢ[ℝ] E) z - z) = z - u z := by
          rw [map_sub, huu z]
        calc
          ‖(u⁻¹ : E ≃ₗᵢ[ℝ] E) z - z‖ =
              ‖u ((u⁻¹ : E ≃ₗᵢ[ℝ] E) z - z)‖ :=
            (u.norm_map _).symm
          _ = ‖z - u z‖ := by rw [hmap]
          _ = ‖u z - z‖ := norm_sub_rev _ _
      have hle := abs_le.1 habs
      have h1 := hle.2
      rw [hnorm1, hnorm2] at h1
      change (∑ η ∈ Uq,
          planeMass X K i j k hik hjk (n + 1) rho ψ η (u⁻¹ z)) -
        (∑ η ∈ Uq, planeMass X K i j k hik hjk (n + 1) rho ψ η z) ≤
        (‖z‖ + ‖z‖) * ‖u z - z‖ at h1
      linarith
    calc
      (∑ χ' ∈ Sq,
          planeMass X K i j k hik hjk (n + 2) rho ψ χ' z) ≤
        ∑ η ∈ Uq,
          planeMass X K i j k hik hjk (n + 1) rho ψ η (u⁻¹ z) := hchain
      _ ≤ (∑ η ∈ Uq,
            planeMass X K i j k hik hjk (n + 1) rho ψ η z) +
          2 * ‖z‖ * ‖u z - z‖ := hcont
  -- assemble the per-letter charges
  have htags : (∑ q : Fin (Fintype.card X),
      ∑ η ∈ Finset.univ.filter
        (fun η : Module.Dual K (PlaneVector X K (n + 1)) ↦
          (pairRegion X K (firstCoordinateChar X K (n + 1) η)
            (secondCoordinateChar X K (n + 1) η) = .C ∨
          pairRegion X K (firstCoordinateChar X K (n + 1) η)
            (secondCoordinateChar X K (n + 1) η) = .D) ∧
          leastLeadingGeneratorIndex X K
            (secondCoordinateChar X K (n + 1) η) = (q : ℕ)),
        planeMass X K i j k hik hjk (n + 1) rho ψ η z) ≤
      ∑ η ∈ CD, planeMass X K i j k hik hjk (n + 1) rho ψ η z := by
    have hdisjq : ((Finset.univ : Finset (Fin (Fintype.card X))) :
        Set (Fin (Fintype.card X))).PairwiseDisjoint
        (fun q ↦ Finset.univ.filter
          (fun η : Module.Dual K (PlaneVector X K (n + 1)) ↦
            (pairRegion X K (firstCoordinateChar X K (n + 1) η)
              (secondCoordinateChar X K (n + 1) η) = .C ∨
            pairRegion X K (firstCoordinateChar X K (n + 1) η)
              (secondCoordinateChar X K (n + 1) η) = .D) ∧
            leastLeadingGeneratorIndex X K
              (secondCoordinateChar X K (n + 1) η) = (q : ℕ))) := by
      intro q₁ _ q₂ _ hne
      refine Finset.disjoint_left.2 fun η h1 h2 ↦ ?_
      rw [Finset.mem_filter] at h1 h2
      exact hne (Fin.ext (by omega))
    rw [← Finset.sum_biUnion hdisjq]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_
      fun η _ _ ↦ planeMass_nonneg X K i j k hik hjk (n + 1) rho ψ η z
    intro η hη
    obtain ⟨q, -, hqmem⟩ := Finset.mem_biUnion.1 hη
    rw [Finset.mem_filter] at hqmem
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hqmem.2.1⟩
  have herr : (∑ q : Fin (Fintype.card X),
      2 * ‖z‖ * ‖rho (elementaryRoot j i hij.symm
        (FreeAlgebra.ι K (generatorEnumeration X q))) z - z‖) =
    ∑ x : X, 2 * ‖z‖ *
      ‖rho (elementaryRoot j i hij.symm (FreeAlgebra.ι K x)) z - z‖ :=
    Fintype.sum_equiv (generatorEnumeration X) _ _ fun q ↦ rfl
  calc
    (∑ χ' ∈ S, planeMass X K i j k hik hjk (n + 2) rho ψ χ' z) =
        (∑ χ' ∈ Si,
          planeMass X K i j k hik hjk (n + 2) rho ψ χ' z) +
        ∑ χ' ∈ S.filter
          (fun χ' ↦ ¬ valuation X K
            (secondCoordinateChar X K (n + 2) χ') ≤ n + 1),
          planeMass X K i j k hik hjk (n + 2) rho ψ χ' z := hsplit.symm
    _ ≤ (∑ q : Fin (Fintype.card X + 1),
          ∑ χ' ∈ Si.filter (fun χ' ↦ selIdx χ' = q),
            planeMass X K i j k hik hjk (n + 2) rho ψ χ' z) +
        secondBoundaryMass X K i j k hik hjk (n + 2) rho ψ z := by
      rw [← hpartition]
      linarith
    _ = (∑ q : Fin (Fintype.card X),
          ∑ χ' ∈ Si.filter (fun χ' ↦ selIdx χ' = q.castSucc),
            planeMass X K i j k hik hjk (n + 2) rho ψ χ' z) +
        secondBoundaryMass X K i j k hik hjk (n + 2) rho ψ z := by
      rw [Fin.sum_univ_castSucc, hlast, Finset.sum_empty, add_zero]
    _ ≤ (∑ q : Fin (Fintype.card X),
          ((∑ η ∈ Finset.univ.filter
            (fun η : Module.Dual K (PlaneVector X K (n + 1)) ↦
              (pairRegion X K (firstCoordinateChar X K (n + 1) η)
                (secondCoordinateChar X K (n + 1) η) = .C ∨
              pairRegion X K (firstCoordinateChar X K (n + 1) η)
                (secondCoordinateChar X K (n + 1) η) = .D) ∧
              leastLeadingGeneratorIndex X K
                (secondCoordinateChar X K (n + 1) η) = (q : ℕ)),
            planeMass X K i j k hik hjk (n + 1) rho ψ η z) +
          2 * ‖z‖ * ‖rho (elementaryRoot j i hij.symm
            (FreeAlgebra.ι K (generatorEnumeration X q))) z - z‖)) +
        secondBoundaryMass X K i j k hik hjk (n + 2) rho ψ z := by
      have hsum := Finset.sum_le_sum fun q (_ : q ∈ Finset.univ) ↦
        hperq q
      linarith
    _ = ((∑ q : Fin (Fintype.card X),
          ∑ η ∈ Finset.univ.filter
            (fun η : Module.Dual K (PlaneVector X K (n + 1)) ↦
              (pairRegion X K (firstCoordinateChar X K (n + 1) η)
                (secondCoordinateChar X K (n + 1) η) = .C ∨
              pairRegion X K (firstCoordinateChar X K (n + 1) η)
                (secondCoordinateChar X K (n + 1) η) = .D) ∧
              leastLeadingGeneratorIndex X K
                (secondCoordinateChar X K (n + 1) η) = (q : ℕ)),
            planeMass X K i j k hik hjk (n + 1) rho ψ η z) +
          ∑ q : Fin (Fintype.card X),
            2 * ‖z‖ * ‖rho (elementaryRoot j i hij.symm
              (FreeAlgebra.ι K (generatorEnumeration X q))) z - z‖) +
        secondBoundaryMass X K i j k hik hjk (n + 2) rho ψ z := by
      rw [Finset.sum_add_distrib]
    _ ≤ ((∑ η ∈ CD,
          planeMass X K i j k hik hjk (n + 1) rho ψ η z) +
          ∑ x : X, 2 * ‖z‖ *
            ‖rho (elementaryRoot j i hij.symm
              (FreeAlgebra.ι K x)) z - z‖) +
        secondBoundaryMass X K i j k hik hjk (n + 2) rho ψ z := by
      rw [← herr]
      linarith


open FreeRootFunctionalValuation in
open Classical in
/-- **The same-vector `C ∪ B` descent estimate**: the mirror of the
`A ∪ B` estimate, charging through the forward shear of the canonical
least leading generator of the first functional. -/
theorem sum_planeMass_CB_le_coarse_AD (hψ : ψ ≠ 1) (z : E) :
    ∑ χ' ∈ Finset.univ.filter
        (fun χ' : Module.Dual K (PlaneVector X K (n + 2)) ↦
          pairRegion X K (firstCoordinateChar X K (n + 2) χ')
            (secondCoordinateChar X K (n + 2) χ') = .C ∨
          pairRegion X K (firstCoordinateChar X K (n + 2) χ')
            (secondCoordinateChar X K (n + 2) χ') = .B),
      planeMass X K i j k hik hjk (n + 2) rho ψ χ' z ≤
    (∑ η ∈ Finset.univ.filter
        (fun η : Module.Dual K (PlaneVector X K (n + 1)) ↦
          pairRegion X K (firstCoordinateChar X K (n + 1) η)
            (secondCoordinateChar X K (n + 1) η) = .A ∨
          pairRegion X K (firstCoordinateChar X K (n + 1) η)
            (secondCoordinateChar X K (n + 1) η) = .D),
      planeMass X K i j k hik hjk (n + 1) rho ψ η z) +
      (∑ x : X, 2 * ‖z‖ *
        ‖rho (elementaryRoot i j hij (FreeAlgebra.ι K x)) z - z‖) +
      firstBoundaryMass X K i j k hik hjk (n + 2) rho ψ z := by
  set S := Finset.univ.filter
    (fun χ' : Module.Dual K (PlaneVector X K (n + 2)) ↦
      pairRegion X K (firstCoordinateChar X K (n + 2) χ')
        (secondCoordinateChar X K (n + 2) χ') = .C ∨
      pairRegion X K (firstCoordinateChar X K (n + 2) χ')
        (secondCoordinateChar X K (n + 2) χ') = .B) with hS
  set AD := Finset.univ.filter
    (fun η : Module.Dual K (PlaneVector X K (n + 1)) ↦
      pairRegion X K (firstCoordinateChar X K (n + 1) η)
        (secondCoordinateChar X K (n + 1) η) = .A ∨
      pairRegion X K (firstCoordinateChar X K (n + 1) η)
        (secondCoordinateChar X K (n + 1) η) = .D) with hAD
  have hsplit := Finset.sum_filter_add_sum_filter_not S
    (fun χ' ↦ valuation X K
      (firstCoordinateChar X K (n + 2) χ') ≤ n + 1)
    (fun χ' ↦ planeMass X K i j k hik hjk (n + 2) rho ψ χ' z)
  set Si := S.filter
    (fun χ' ↦ valuation X K
      (firstCoordinateChar X K (n + 2) χ') ≤ n + 1) with hSi
  have hboundary : (∑ χ' ∈ S.filter
      (fun χ' ↦ ¬ valuation X K
        (firstCoordinateChar X K (n + 2) χ') ≤ n + 1),
      planeMass X K i j k hik hjk (n + 2) rho ψ χ' z) ≤
    firstBoundaryMass X K i j k hik hjk (n + 2) rho ψ z := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_
      fun χ' _ _ ↦ planeMass_nonneg X K i j k hik hjk (n + 2) rho ψ χ' z
    intro χ' hχ'
    rw [Finset.mem_filter, hS, Finset.mem_filter] at hχ'
    obtain ⟨⟨-, hreg⟩, htop⟩ := hχ'
    have hne : valuation X K
        (firstCoordinateChar X K (n + 2) χ') ≠ 0 ∧
        ¬(valuation X K (firstCoordinateChar X K (n + 2) χ') = n + 3 ∧
          valuation X K (secondCoordinateChar X K (n + 2) χ') = n + 3) ∧
        valuation X K (firstCoordinateChar X K (n + 2) χ') ≤
          valuation X K (secondCoordinateChar X K (n + 2) χ') := by
      rcases hreg with hC | hB
      · obtain ⟨hz2, h1ne, -, hlt⟩ := pairRegion_C_data X K _ _ hC
        exact ⟨h1ne, hz2, hlt.le⟩
      · obtain ⟨hz2, h1ne, -, heq⟩ := pairRegion_B_data X K _ _ hB
        exact ⟨h1ne, hz2, heq.le⟩
    obtain ⟨h1ne, hz2, hle1⟩ := hne
    have hb1 := valuation_le_succ X K
      (firstCoordinateChar X K (n + 2) χ')
    have hb2 := valuation_le_succ X K
      (secondCoordinateChar X K (n + 2) χ')
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    omega
  set selIdx : Module.Dual K (PlaneVector X K (n + 2)) →
      Fin (Fintype.card X + 1) := fun χ' ↦
    if h : leastLeadingGeneratorIndex X K
        (firstCoordinateChar X K (n + 2) χ') < Fintype.card X then
      ⟨leastLeadingGeneratorIndex X K
        (firstCoordinateChar X K (n + 2) χ'), Nat.lt_succ_of_lt h⟩
    else Fin.last (Fintype.card X) with hselIdx
  have hleadset : ∀ χ' ∈ Si,
      (leadingGeneratorIndexSet X K
        (firstCoordinateChar X K (n + 2) χ')).Nonempty := by
    intro χ' hχ'
    rw [hSi, Finset.mem_filter, hS, Finset.mem_filter] at hχ'
    obtain ⟨⟨-, hreg⟩, hint⟩ := hχ'
    have h1ne : valuation X K
        (firstCoordinateChar X K (n + 2) χ') ≠ 0 := by
      rcases hreg with hC | hB
      · exact (pairRegion_C_data X K _ _ hC).2.1
      · exact (pairRegion_B_data X K _ _ hB).2.1
    refine leadingGeneratorIndexSet_nonempty X K _ ?_ (by omega)
    by_contra hnone
    have := valuation_eq_succ_of_not_exists X K _ hnone
    omega
  have hpartition : (∑ χ' ∈ Si,
      planeMass X K i j k hik hjk (n + 2) rho ψ χ' z) =
    ∑ q : Fin (Fintype.card X + 1),
      ∑ χ' ∈ Si.filter (fun χ' ↦ selIdx χ' = q),
        planeMass X K i j k hik hjk (n + 2) rho ψ χ' z :=
    (Finset.sum_fiberwise Si selIdx _).symm
  have hlast : Si.filter
      (fun χ' ↦ selIdx χ' = Fin.last (Fintype.card X)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro χ' hχ'
    have hlt := leastLeadingGeneratorIndex_lt_card X K
      (firstCoordinateChar X K (n + 2) χ') (hleadset χ' hχ')
    rw [hselIdx]
    beta_reduce
    rw [dif_pos hlt]
    intro hcontra
    have := congrArg Fin.val hcontra
    simp only [Fin.val_last] at this
    omega
  have hperq : ∀ q : Fin (Fintype.card X),
      (∑ χ' ∈ Si.filter (fun χ' ↦ selIdx χ' = q.castSucc),
        planeMass X K i j k hik hjk (n + 2) rho ψ χ' z) ≤
      (∑ η ∈ Finset.univ.filter
          (fun η : Module.Dual K (PlaneVector X K (n + 1)) ↦
            (pairRegion X K (firstCoordinateChar X K (n + 1) η)
              (secondCoordinateChar X K (n + 1) η) = .A ∨
            pairRegion X K (firstCoordinateChar X K (n + 1) η)
              (secondCoordinateChar X K (n + 1) η) = .D) ∧
            leastLeadingGeneratorIndex X K
              (firstCoordinateChar X K (n + 1) η) = (q : ℕ)),
        planeMass X K i j k hik hjk (n + 1) rho ψ η z) +
        2 * ‖z‖ * ‖rho (elementaryRoot i j hij
          (FreeAlgebra.ι K (generatorEnumeration X q))) z - z‖ := by
    intro q
    set x := generatorEnumeration X q with hx
    set u := rho (elementaryRoot i j hij (FreeAlgebra.ι K x)) with hu
    set Sq := Si.filter (fun χ' ↦ selIdx χ' = q.castSucc) with hSq
    set Uq := Finset.univ.filter
      (fun η : Module.Dual K (PlaneVector X K (n + 1)) ↦
        (pairRegion X K (firstCoordinateChar X K (n + 1) η)
          (secondCoordinateChar X K (n + 1) η) = .A ∨
        pairRegion X K (firstCoordinateChar X K (n + 1) η)
          (secondCoordinateChar X K (n + 1) η) = .D) ∧
        leastLeadingGeneratorIndex X K
          (firstCoordinateChar X K (n + 1) η) = (q : ℕ)) with hUq
    have hmem : ∀ χ' ∈ Sq,
        χ'.comp (forwardShear X K (n + 1) x) ∈ Uq := by
      intro χ' hχ'
      rw [hSq, Finset.mem_filter] at hχ'
      obtain ⟨hSi', hsel⟩ := hχ'
      rw [hSi, Finset.mem_filter, hS, Finset.mem_filter] at hSi'
      obtain ⟨⟨-, hreg⟩, hint⟩ := hSi'
      have hne : (leadingGeneratorIndexSet X K
          (firstCoordinateChar X K (n + 2) χ')).Nonempty :=
        hleadset χ' (by
          rw [hSi, Finset.mem_filter, hS, Finset.mem_filter]
          exact ⟨⟨Finset.mem_univ _, hreg⟩, hint⟩)
      have hltcard := leastLeadingGeneratorIndex_lt_card X K
        (firstCoordinateChar X K (n + 2) χ') hne
      have hidx : leastLeadingGeneratorIndex X K
          (firstCoordinateChar X K (n + 2) χ') = (q : ℕ) := by
        have := hsel
        rw [hselIdx] at this
        beta_reduce at this
        rw [dif_pos hltcard] at this
        have hval := congrArg Fin.val this
        simpa using hval
      have hqfin : q = (⟨leastLeadingGeneratorIndex X K
          (firstCoordinateChar X K (n + 2) χ'), hltcard⟩ :
            Fin (Fintype.card X)) := by
        apply Fin.ext
        show (q : ℕ) = leastLeadingGeneratorIndex X K
          (firstCoordinateChar X K (n + 2) χ')
        omega
      have hxval : x = generatorEnumeration X
          ⟨leastLeadingGeneratorIndex X K
            (firstCoordinateChar X K (n + 2) χ'), hltcard⟩ := by
        rw [hx, hqfin]
      have hlead : valuation X K
          (leftDerived X K
            (firstCoordinateChar X K (n + 2) χ') x) + 1 =
        valuation X K (firstCoordinateChar X K (n + 2) χ') := by
        rw [hxval]
        exact leastLeadingGeneratorIndex_spec X K _ hne
      have hregion := coarse_pairRegion_of_fine_CB_forward
        X K (n + 1) x χ' hreg hint hlead
      have hfirstid : firstCoordinateChar X K (n + 1)
          (χ'.comp (forwardShear X K (n + 1) x)) =
        restrictSucc X K (firstCoordinateChar X K (n + 2) χ') :=
        firstCoordinateChar_comp_forwardShear X K (n + 1) x χ'
      have htag : leastLeadingGeneratorIndex X K
          (firstCoordinateChar X K (n + 1)
            (χ'.comp (forwardShear X K (n + 1) x))) = (q : ℕ) := by
        rw [hfirstid,
          leastLeadingGeneratorIndex_restrictSucc X K
            (firstCoordinateChar X K (n + 2) χ') (by omega)]
        exact hidx
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hregion, htag⟩
    have hdisj : (Uq : Set (Module.Dual K
        (PlaneVector X K (n + 1)))).PairwiseDisjoint
        (fun η ↦ Finset.univ.filter
          (fun χ'' : Module.Dual K (PlaneVector X K (n + 2)) ↦
            χ''.comp (forwardShear X K (n + 1) x) = η)) := by
      intro η₁ _ η₂ _ hne
      refine Finset.disjoint_left.2 fun χ'' h1 h2 ↦ ?_
      rw [Finset.mem_filter] at h1 h2
      exact hne (h1.2 ▸ h2.2)
    have huu : ∀ w : E, u (u⁻¹ w) = w := by
      intro w
      change (u * u⁻¹) w = w
      rw [mul_inv_cancel]
      rfl
    have htransport : ∀ η ∈ Uq,
        planeMass X K i j k hik hjk (n + 1) rho ψ η (u⁻¹ z) =
        ∑ χ'' ∈ Finset.univ.filter
            (fun χ'' : Module.Dual K (PlaneVector X K (n + 2)) ↦
              χ''.comp (forwardShear X K (n + 1) x) = η),
          planeMass X K i j k hik hjk (n + 2) rho ψ χ'' z := by
      intro η _
      have h := planeMass_eq_sum_fiber_forwardShear X K i j k hij
        hik hjk (n + 1) rho ψ hψ x (u⁻¹ z) η
      rw [← hu] at h
      rw [huu z] at h
      exact h
    have hchain : (∑ χ' ∈ Sq,
        planeMass X K i j k hik hjk (n + 2) rho ψ χ' z) ≤
      ∑ η ∈ Uq, planeMass X K i j k hik hjk (n + 1) rho ψ η (u⁻¹ z) := by
      calc
        (∑ χ' ∈ Sq,
            planeMass X K i j k hik hjk (n + 2) rho ψ χ' z) ≤
          ∑ χ' ∈ Uq.biUnion
            (fun η ↦ Finset.univ.filter
              (fun χ'' : Module.Dual K (PlaneVector X K (n + 2)) ↦
                χ''.comp (forwardShear X K (n + 1) x) = η)),
            planeMass X K i j k hik hjk (n + 2) rho ψ χ' z := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_
            fun χ' _ _ ↦
              planeMass_nonneg X K i j k hik hjk (n + 2) rho ψ χ' z
          intro χ' hχ'
          refine Finset.mem_biUnion.2
            ⟨χ'.comp (forwardShear X K (n + 1) x), hmem χ' hχ', ?_⟩
          exact Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩
        _ = ∑ η ∈ Uq, ∑ χ'' ∈ Finset.univ.filter
            (fun χ'' : Module.Dual K (PlaneVector X K (n + 2)) ↦
              χ''.comp (forwardShear X K (n + 1) x) = η),
            planeMass X K i j k hik hjk (n + 2) rho ψ χ'' z :=
          Finset.sum_biUnion hdisj
        _ = ∑ η ∈ Uq,
            planeMass X K i j k hik hjk (n + 1) rho ψ η (u⁻¹ z) :=
          (Finset.sum_congr rfl htransport).symm
    have hcont : (∑ η ∈ Uq,
        planeMass X K i j k hik hjk (n + 1) rho ψ η (u⁻¹ z)) ≤
      (∑ η ∈ Uq, planeMass X K i j k hik hjk (n + 1) rho ψ η z) +
        2 * ‖z‖ * ‖u z - z‖ := by
      have habs := CharacterMass.abs_sum_mass_sub_sum_mass_le ψ
        (planeAction X K i j k hik hjk (n + 1) rho)
        (planeAction_add X K i j k hik hjk (n + 1) rho) hψ
        Uq (u⁻¹ z) z
      have hnorm1 : ‖(u⁻¹ : E ≃ₗᵢ[ℝ] E) z‖ = ‖z‖ :=
        (u⁻¹ : E ≃ₗᵢ[ℝ] E).norm_map z
      have hnorm2 : ‖(u⁻¹ : E ≃ₗᵢ[ℝ] E) z - z‖ = ‖u z - z‖ := by
        have hmap : u ((u⁻¹ : E ≃ₗᵢ[ℝ] E) z - z) = z - u z := by
          rw [map_sub, huu z]
        calc
          ‖(u⁻¹ : E ≃ₗᵢ[ℝ] E) z - z‖ =
              ‖u ((u⁻¹ : E ≃ₗᵢ[ℝ] E) z - z)‖ :=
            (u.norm_map _).symm
          _ = ‖z - u z‖ := by rw [hmap]
          _ = ‖u z - z‖ := norm_sub_rev _ _
      have hle := abs_le.1 habs
      have h1 := hle.2
      rw [hnorm1, hnorm2] at h1
      change (∑ η ∈ Uq,
          planeMass X K i j k hik hjk (n + 1) rho ψ η (u⁻¹ z)) -
        (∑ η ∈ Uq, planeMass X K i j k hik hjk (n + 1) rho ψ η z) ≤
        (‖z‖ + ‖z‖) * ‖u z - z‖ at h1
      linarith
    calc
      (∑ χ' ∈ Sq,
          planeMass X K i j k hik hjk (n + 2) rho ψ χ' z) ≤
        ∑ η ∈ Uq,
          planeMass X K i j k hik hjk (n + 1) rho ψ η (u⁻¹ z) := hchain
      _ ≤ (∑ η ∈ Uq,
            planeMass X K i j k hik hjk (n + 1) rho ψ η z) +
          2 * ‖z‖ * ‖u z - z‖ := hcont
  have htags : (∑ q : Fin (Fintype.card X),
      ∑ η ∈ Finset.univ.filter
        (fun η : Module.Dual K (PlaneVector X K (n + 1)) ↦
          (pairRegion X K (firstCoordinateChar X K (n + 1) η)
            (secondCoordinateChar X K (n + 1) η) = .A ∨
          pairRegion X K (firstCoordinateChar X K (n + 1) η)
            (secondCoordinateChar X K (n + 1) η) = .D) ∧
          leastLeadingGeneratorIndex X K
            (firstCoordinateChar X K (n + 1) η) = (q : ℕ)),
        planeMass X K i j k hik hjk (n + 1) rho ψ η z) ≤
      ∑ η ∈ AD, planeMass X K i j k hik hjk (n + 1) rho ψ η z := by
    have hdisjq : ((Finset.univ : Finset (Fin (Fintype.card X))) :
        Set (Fin (Fintype.card X))).PairwiseDisjoint
        (fun q ↦ Finset.univ.filter
          (fun η : Module.Dual K (PlaneVector X K (n + 1)) ↦
            (pairRegion X K (firstCoordinateChar X K (n + 1) η)
              (secondCoordinateChar X K (n + 1) η) = .A ∨
            pairRegion X K (firstCoordinateChar X K (n + 1) η)
              (secondCoordinateChar X K (n + 1) η) = .D) ∧
            leastLeadingGeneratorIndex X K
              (firstCoordinateChar X K (n + 1) η) = (q : ℕ))) := by
      intro q₁ _ q₂ _ hne
      refine Finset.disjoint_left.2 fun η h1 h2 ↦ ?_
      rw [Finset.mem_filter] at h1 h2
      exact hne (Fin.ext (by omega))
    rw [← Finset.sum_biUnion hdisjq]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_
      fun η _ _ ↦ planeMass_nonneg X K i j k hik hjk (n + 1) rho ψ η z
    intro η hη
    obtain ⟨q, -, hqmem⟩ := Finset.mem_biUnion.1 hη
    rw [Finset.mem_filter] at hqmem
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hqmem.2.1⟩
  have herr : (∑ q : Fin (Fintype.card X),
      2 * ‖z‖ * ‖rho (elementaryRoot i j hij
        (FreeAlgebra.ι K (generatorEnumeration X q))) z - z‖) =
    ∑ x : X, 2 * ‖z‖ *
      ‖rho (elementaryRoot i j hij (FreeAlgebra.ι K x)) z - z‖ :=
    Fintype.sum_equiv (generatorEnumeration X) _ _ fun q ↦ rfl
  calc
    (∑ χ' ∈ S, planeMass X K i j k hik hjk (n + 2) rho ψ χ' z) =
        (∑ χ' ∈ Si,
          planeMass X K i j k hik hjk (n + 2) rho ψ χ' z) +
        ∑ χ' ∈ S.filter
          (fun χ' ↦ ¬ valuation X K
            (firstCoordinateChar X K (n + 2) χ') ≤ n + 1),
          planeMass X K i j k hik hjk (n + 2) rho ψ χ' z := hsplit.symm
    _ ≤ (∑ q : Fin (Fintype.card X + 1),
          ∑ χ' ∈ Si.filter (fun χ' ↦ selIdx χ' = q),
            planeMass X K i j k hik hjk (n + 2) rho ψ χ' z) +
        firstBoundaryMass X K i j k hik hjk (n + 2) rho ψ z := by
      rw [← hpartition]
      linarith
    _ = (∑ q : Fin (Fintype.card X),
          ∑ χ' ∈ Si.filter (fun χ' ↦ selIdx χ' = q.castSucc),
            planeMass X K i j k hik hjk (n + 2) rho ψ χ' z) +
        firstBoundaryMass X K i j k hik hjk (n + 2) rho ψ z := by
      rw [Fin.sum_univ_castSucc, hlast, Finset.sum_empty, add_zero]
    _ ≤ (∑ q : Fin (Fintype.card X),
          ((∑ η ∈ Finset.univ.filter
            (fun η : Module.Dual K (PlaneVector X K (n + 1)) ↦
              (pairRegion X K (firstCoordinateChar X K (n + 1) η)
                (secondCoordinateChar X K (n + 1) η) = .A ∨
              pairRegion X K (firstCoordinateChar X K (n + 1) η)
                (secondCoordinateChar X K (n + 1) η) = .D) ∧
              leastLeadingGeneratorIndex X K
                (firstCoordinateChar X K (n + 1) η) = (q : ℕ)),
            planeMass X K i j k hik hjk (n + 1) rho ψ η z) +
          2 * ‖z‖ * ‖rho (elementaryRoot i j hij
            (FreeAlgebra.ι K (generatorEnumeration X q))) z - z‖)) +
        firstBoundaryMass X K i j k hik hjk (n + 2) rho ψ z := by
      have hsum := Finset.sum_le_sum fun q (_ : q ∈ Finset.univ) ↦
        hperq q
      linarith
    _ = ((∑ q : Fin (Fintype.card X),
          ∑ η ∈ Finset.univ.filter
            (fun η : Module.Dual K (PlaneVector X K (n + 1)) ↦
              (pairRegion X K (firstCoordinateChar X K (n + 1) η)
                (secondCoordinateChar X K (n + 1) η) = .A ∨
              pairRegion X K (firstCoordinateChar X K (n + 1) η)
                (secondCoordinateChar X K (n + 1) η) = .D) ∧
              leastLeadingGeneratorIndex X K
                (firstCoordinateChar X K (n + 1) η) = (q : ℕ)),
            planeMass X K i j k hik hjk (n + 1) rho ψ η z) +
          ∑ q : Fin (Fintype.card X),
            2 * ‖z‖ * ‖rho (elementaryRoot i j hij
              (FreeAlgebra.ι K (generatorEnumeration X q))) z - z‖) +
        firstBoundaryMass X K i j k hik hjk (n + 2) rho ψ z := by
      rw [Finset.sum_add_distrib]
    _ ≤ ((∑ η ∈ AD,
          planeMass X K i j k hik hjk (n + 1) rho ψ η z) +
          ∑ x : X, 2 * ‖z‖ *
            ‖rho (elementaryRoot i j hij (FreeAlgebra.ι K x)) z - z‖) +
        firstBoundaryMass X K i j k hik hjk (n + 2) rho ψ z := by
      rw [← herr]
      linarith


open FreeRootFunctionalValuation in
open Classical in
/-- **The finite-stage Kassabov estimate**: the total mass in all four
nonzero valuation regions is controlled by the displacements of the
explicit unit and generator elements, the scalar unit displacements at
the character gap, and the two vanishing boundary layers. -/
theorem sum_planeMass_nonzero_le_explicit_errors (hψ : ψ ≠ 1) (z : E) :
    (∑ χ ∈ Finset.univ.filter
        (fun χ : Module.Dual K (PlaneVector X K (n + 2)) ↦
          pairRegion X K (firstCoordinateChar X K (n + 2) χ)
            (secondCoordinateChar X K (n + 2) χ) = .A),
      planeMass X K i j k hik hjk (n + 2) rho ψ χ z) +
    (∑ χ ∈ Finset.univ.filter
        (fun χ : Module.Dual K (PlaneVector X K (n + 2)) ↦
          pairRegion X K (firstCoordinateChar X K (n + 2) χ)
            (secondCoordinateChar X K (n + 2) χ) = .B),
      planeMass X K i j k hik hjk (n + 2) rho ψ χ z) +
    (∑ χ ∈ Finset.univ.filter
        (fun χ : Module.Dual K (PlaneVector X K (n + 2)) ↦
          pairRegion X K (firstCoordinateChar X K (n + 2) χ)
            (secondCoordinateChar X K (n + 2) χ) = .C),
      planeMass X K i j k hik hjk (n + 2) rho ψ χ z) +
    (∑ χ ∈ Finset.univ.filter
        (fun χ : Module.Dual K (PlaneVector X K (n + 2)) ↦
          pairRegion X K (firstCoordinateChar X K (n + 2) χ)
            (secondCoordinateChar X K (n + 2) χ) = .D),
      planeMass X K i j k hik hjk (n + 2) rho ψ χ z) ≤
    4 * ((CharacterMass.gap ψ)⁻¹ *
      ((∑ t : K, ‖rho (planePoint X K i j k hik hjk (n + 2)
          (t • unitVectorFirst X K (n + 2))) z - z‖ ^ 2) +
        ∑ t : K, ‖rho (planePoint X K i j k hik hjk (n + 2)
          (t • unitVectorSecond X K (n + 2))) z - z‖ ^ 2)) +
    (3 : ℝ) / 2 *
      ((∑ x : X, 2 * ‖z‖ *
        ‖rho (elementaryRoot j i hij.symm (FreeAlgebra.ι K x)) z - z‖) +
      ∑ x : X, 2 * ‖z‖ *
        ‖rho (elementaryRoot i j hij (FreeAlgebra.ι K x)) z - z‖) +
    2 * ‖z‖ *
      ‖rho (elementaryRoot j i hij.symm (1 : FreeAlgebra K X)) z - z‖ +
    2 * ‖z‖ *
      ‖rho (elementaryRoot i j hij (1 : FreeAlgebra K X)) z - z‖ +
    (9 : ℝ) / 2 *
      (firstBoundaryMass X K i j k hik hjk (n + 2) rho ψ z +
        secondBoundaryMass X K i j k hik hjk (n + 2) rho ψ z) := by
  have hsplit : ∀ (m : ℕ) (r s : ValuationRegion), r ≠ s →
      (∑ χ ∈ Finset.univ.filter
        (fun χ : Module.Dual K (PlaneVector X K m) ↦
          pairRegion X K (firstCoordinateChar X K m χ)
            (secondCoordinateChar X K m χ) = r ∨
          pairRegion X K (firstCoordinateChar X K m χ)
            (secondCoordinateChar X K m χ) = s),
        planeMass X K i j k hik hjk m rho ψ χ z) =
      (∑ χ ∈ Finset.univ.filter
        (fun χ : Module.Dual K (PlaneVector X K m) ↦
          pairRegion X K (firstCoordinateChar X K m χ)
            (secondCoordinateChar X K m χ) = r),
        planeMass X K i j k hik hjk m rho ψ χ z) +
      ∑ χ ∈ Finset.univ.filter
        (fun χ : Module.Dual K (PlaneVector X K m) ↦
          pairRegion X K (firstCoordinateChar X K m χ)
            (secondCoordinateChar X K m χ) = s),
        planeMass X K i j k hik hjk m rho ψ χ z := by
    intro m r s hrs
    rw [show (Finset.univ.filter
        (fun χ : Module.Dual K (PlaneVector X K m) ↦
          pairRegion X K (firstCoordinateChar X K m χ)
            (secondCoordinateChar X K m χ) = r ∨
          pairRegion X K (firstCoordinateChar X K m χ)
            (secondCoordinateChar X K m χ) = s)) =
      (Finset.univ.filter
        (fun χ : Module.Dual K (PlaneVector X K m) ↦
          pairRegion X K (firstCoordinateChar X K m χ)
            (secondCoordinateChar X K m χ) = r)) ∪
        Finset.univ.filter
          (fun χ : Module.Dual K (PlaneVector X K m) ↦
            pairRegion X K (firstCoordinateChar X K m χ)
              (secondCoordinateChar X K m χ) = s) from by
      ext χ
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ,
        true_and]]
    refine Finset.sum_union ?_
    refine Finset.disjoint_left.2 fun χ h1 h2 ↦ ?_
    rw [Finset.mem_filter] at h1 h2
    exact hrs (by rw [← h1.2, h2.2])
  have hAB := sum_planeMass_AB_le_coarse_CD X K i j k hij hik hjk n
    rho ψ hψ z
  have hCB := sum_planeMass_CB_le_coarse_AD X K i j k hij hik hjk n
    rho ψ hψ z
  have hliftCD := sum_planeMass_region_le_succ_add_boundaries
    X K i j k hik hjk (n + 1) rho ψ hψ z
    (fun r ↦ r = ValuationRegion.C ∨ r = ValuationRegion.D)
  have hliftAD := sum_planeMass_region_le_succ_add_boundaries
    X K i j k hik hjk (n + 1) rho ψ hψ z
    (fun r ↦ r = ValuationRegion.A ∨ r = ValuationRegion.D)
  beta_reduce at hliftCD hliftAD
  simp only [show n + 1 + 1 = n + 2 from rfl] at hliftCD hliftAD
  -- unit-shear conversions to the same vector
  have hcontinuity : ∀ (g : elementaryGroup (Fin 3) (FreeAlgebra K X))
      (r : ValuationRegion),
      (∑ χ ∈ Finset.univ.filter
        (fun χ : Module.Dual K (PlaneVector X K (n + 2)) ↦
          pairRegion X K (firstCoordinateChar X K (n + 2) χ)
            (secondCoordinateChar X K (n + 2) χ) = r),
        planeMass X K i j k hik hjk (n + 2) rho ψ χ (rho g z)) ≤
      (∑ χ ∈ Finset.univ.filter
        (fun χ : Module.Dual K (PlaneVector X K (n + 2)) ↦
          pairRegion X K (firstCoordinateChar X K (n + 2) χ)
            (secondCoordinateChar X K (n + 2) χ) = r),
        planeMass X K i j k hik hjk (n + 2) rho ψ χ z) +
        2 * ‖z‖ * ‖rho g z - z‖ := by
    intro g r
    have habs := CharacterMass.abs_sum_mass_sub_sum_mass_le ψ
      (planeAction X K i j k hik hjk (n + 2) rho)
      (planeAction_add X K i j k hik hjk (n + 2) rho) hψ
      (Finset.univ.filter
        (fun χ : Module.Dual K (PlaneVector X K (n + 2)) ↦
          pairRegion X K (firstCoordinateChar X K (n + 2) χ)
            (secondCoordinateChar X K (n + 2) χ) = r))
      (rho g z) z
    have hnorm : ‖rho g z‖ = ‖z‖ := (rho g).norm_map z
    have h1 := (abs_le.1 habs).2
    rw [hnorm] at h1
    change (∑ χ ∈ Finset.univ.filter
        (fun χ : Module.Dual K (PlaneVector X K (n + 2)) ↦
          pairRegion X K (firstCoordinateChar X K (n + 2) χ)
            (secondCoordinateChar X K (n + 2) χ) = r),
        planeMass X K i j k hik hjk (n + 2) rho ψ χ (rho g z)) -
      (∑ χ ∈ Finset.univ.filter
        (fun χ : Module.Dual K (PlaneVector X K (n + 2)) ↦
          pairRegion X K (firstCoordinateChar X K (n + 2) χ)
            (secondCoordinateChar X K (n + 2) χ) = r),
        planeMass X K i j k hik hjk (n + 2) rho ψ χ z) ≤
      (‖z‖ + ‖z‖) * ‖rho g z - z‖ at h1
    linarith
  have hA := sum_planeMass_A_le_sum_B X K i j k hij hik hjk (n + 2)
    rho ψ z
  have hAcont := hcontinuity
    (elementaryRoot j i hij.symm (1 : FreeAlgebra K X)) .B
  have hC := sum_planeMass_C_le_sum_B X K i j k hij hik hjk (n + 2)
    rho ψ z
  have hCcont := hcontinuity
    (elementaryRoot i j hij (1 : FreeAlgebra K X)) .B
  have hgapD := gap_mul_sum_planeMass_D_le X K i j k hik hjk (n + 2)
    rho ψ hψ z
  have hgap := CharacterMass.gap_pos ψ
  have hD : (∑ χ ∈ Finset.univ.filter
      (fun χ : Module.Dual K (PlaneVector X K (n + 2)) ↦
        pairRegion X K (firstCoordinateChar X K (n + 2) χ)
          (secondCoordinateChar X K (n + 2) χ) = .D),
      planeMass X K i j k hik hjk (n + 2) rho ψ χ z) ≤
    (CharacterMass.gap ψ)⁻¹ *
      ((∑ t : K, ‖rho (planePoint X K i j k hik hjk (n + 2)
          (t • unitVectorFirst X K (n + 2))) z - z‖ ^ 2) +
        ∑ t : K, ‖rho (planePoint X K i j k hik hjk (n + 2)
          (t • unitVectorSecond X K (n + 2))) z - z‖ ^ 2) := by
    have hmul := mul_le_mul_of_nonneg_left hgapD
      (inv_nonneg.2 hgap.le)
    rw [← mul_assoc, inv_mul_cancel₀ hgap.ne', one_mul] at hmul
    exact hmul
  rw [hsplit (n + 2) .A .B (by simp), hsplit (n + 1) .C .D (by simp)]
    at hAB
  rw [hsplit (n + 2) .C .B (by simp), hsplit (n + 1) .A .D (by simp)]
    at hCB
  rw [hsplit (n + 1) .C .D (by simp), hsplit (n + 2) .C .D (by simp)]
    at hliftCD
  rw [hsplit (n + 1) .A .D (by simp), hsplit (n + 2) .A .D (by simp)]
    at hliftAD
  linarith


/-! ### The limiting two-root moving-mass bound -/

open Classical in
/-- **The trivial mass is the fixed projection**: the trivial-character
mass at any stage is the squared norm of the orthogonal projection onto
the subspace fixed by that stage's plane subgroup. -/
theorem planeMass_zero_eq_norm_fixedProjection_sq [CompleteSpace E]
    (z : E) :
    planeMass X K i j k hik hjk n rho ψ 0 z =
      ‖(KazhdanFixedSpace.fixedProjection rho
        (FreeRootPlane.rootPlaneDegreeSubgroup X K i j k hij hik hjk n)
          z : E)‖ ^ 2 := by
  set H := FreeRootPlane.rootPlaneDegreeSubgroup X K i j k hij hik hjk n
    with hH
  set U := KazhdanFixedSpace.fixedSubspace rho H with hU
  set avg : E := (Fintype.card (PlaneVector X K n) : ℝ)⁻¹ •
    ∑ v : PlaneVector X K n, planeAction X K i j k hik hjk n rho v z
    with havg
  have hmass : planeMass X K i j k hik hjk n rho ψ 0 z = ‖avg‖ ^ 2 :=
    CharacterMass.mass_zero_eq_norm_average_sq ψ _
      (planeAction_add X K i j k hik hjk n rho) z
  have hfixaction : ∀ v₀ : PlaneVector X K n,
      planeAction X K i j k hik hjk n rho v₀ avg = avg := by
    intro v₀
    rw [havg, map_smul, map_sum]
    congr 1
    calc
      (∑ v : PlaneVector X K n,
          planeAction X K i j k hik hjk n rho v₀
            (planeAction X K i j k hik hjk n rho v z)) =
          ∑ v : PlaneVector X K n,
            planeAction X K i j k hik hjk n rho (v₀ + v) z := by
        refine Finset.sum_congr rfl fun v _ ↦ ?_
        rw [planeAction_add]
        rfl
      _ = ∑ v : PlaneVector X K n,
          planeAction X K i j k hik hjk n rho v z :=
        Equiv.sum_comp (Equiv.addLeft v₀)
          (fun w ↦ planeAction X K i j k hik hjk n rho w z)
  have hfix : avg ∈ U := by
    rw [hU, KazhdanFixedSpace.mem_fixedSubspace_iff]
    intro h hh
    obtain ⟨v₀, rfl⟩ :=
      planePoint_surjective X K i j k hij hik hjk n h hh
    exact hfixaction v₀
  have horth : z - avg ∈ Uᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    rw [hU, KazhdanFixedSpace.mem_fixedSubspace_iff] at hu
    have hinner : ∀ v : PlaneVector X K n,
        inner ℝ u (planeAction X K i j k hik hjk n rho v z) =
          inner ℝ u z := by
      intro v
      have hufix : planeAction X K i j k hik hjk n rho v u = u :=
        hu _ (planePoint_mem X K i j k hij hik hjk n v)
      calc
        inner ℝ u (planeAction X K i j k hik hjk n rho v z) =
            inner ℝ (planeAction X K i j k hik hjk n rho v u)
              (planeAction X K i j k hik hjk n rho v z) := by
          rw [hufix]
        _ = inner ℝ u z :=
          (planeAction X K i j k hik hjk n rho v).inner_map_map u z
    have hcard : ((Fintype.card (PlaneVector X K n) : ℝ)) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    rw [inner_sub_right, havg, inner_smul_right, inner_sum]
    rw [Finset.sum_congr rfl fun v _ ↦ hinner v, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, inv_mul_cancel_left₀ hcard]
    exact sub_self _
  letI : CompleteSpace U :=
    (KazhdanFixedSpace.isClosed_fixedSubspace rho H).completeSpace_coe
  have hproj : (KazhdanFixedSpace.fixedProjection rho H z : E) = avg := by
    change U.starProjection z = avg
    exact U.eq_starProjection_of_mem_orthogonal hfix horth
  rw [hmass, hproj]

open FreeRootFunctionalValuation in
open Classical in
/-- **The moving-mass identity**: the total mass in the four nonzero
valuation regions is exactly the squared norm of the moving projection
for the stage plane subgroup. -/
theorem sum_planeMass_nonzero_eq_norm_movingProjection_sq
    [CompleteSpace E] (hψ : ψ ≠ 1) (z : E) :
    (∑ χ ∈ Finset.univ.filter
        (fun χ : Module.Dual K (PlaneVector X K n) ↦
          pairRegion X K (firstCoordinateChar X K n χ)
            (secondCoordinateChar X K n χ) = .A),
      planeMass X K i j k hik hjk n rho ψ χ z) +
    (∑ χ ∈ Finset.univ.filter
        (fun χ : Module.Dual K (PlaneVector X K n) ↦
          pairRegion X K (firstCoordinateChar X K n χ)
            (secondCoordinateChar X K n χ) = .B),
      planeMass X K i j k hik hjk n rho ψ χ z) +
    (∑ χ ∈ Finset.univ.filter
        (fun χ : Module.Dual K (PlaneVector X K n) ↦
          pairRegion X K (firstCoordinateChar X K n χ)
            (secondCoordinateChar X K n χ) = .C),
      planeMass X K i j k hik hjk n rho ψ χ z) +
    (∑ χ ∈ Finset.univ.filter
        (fun χ : Module.Dual K (PlaneVector X K n) ↦
          pairRegion X K (firstCoordinateChar X K n χ)
            (secondCoordinateChar X K n χ) = .D),
      planeMass X K i j k hik hjk n rho ψ χ z) =
    ‖KazhdanFixedSpace.subgroupMovingProjection rho
      (FreeRootPlane.rootPlaneDegreeSubgroup X K i j k hij hik hjk n)
        z‖ ^ 2 := by
  have hconserv := sum_planeMass X K i j k hik hjk n rho ψ hψ z
  have hfiber := Finset.sum_fiberwise Finset.univ
    (fun χ : Module.Dual K (PlaneVector X K n) ↦
      pairRegion X K (firstCoordinateChar X K n χ)
        (secondCoordinateChar X K n χ))
    (fun χ ↦ planeMass X K i j k hik hjk n rho ψ χ z)
  rw [show (Finset.univ : Finset ValuationRegion) =
    {ValuationRegion.zero, ValuationRegion.A, ValuationRegion.B,
      ValuationRegion.C, ValuationRegion.D} from by decide] at hfiber
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton] at hfiber
  have hzerofilter : Finset.univ.filter
      (fun χ : Module.Dual K (PlaneVector X K n) ↦
        pairRegion X K (firstCoordinateChar X K n χ)
          (secondCoordinateChar X K n χ) = ValuationRegion.zero) =
    {(0 : Module.Dual K (PlaneVector X K n))} := by
    ext χ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := (pairRegion_eq_zero_iff X K _ _).1 h
      rw [valuation_eq_succ_iff] at h1 h2
      by_contra hne
      rcases coordinateChar_ne_zero_of_ne_zero X K n χ hne with hc | hc
      · exact hc h1
      · exact hc h2
    · rintro rfl
      refine (pairRegion_eq_zero_iff X K _ _).2 ⟨?_, ?_⟩ <;>
        rw [valuation_eq_succ_iff] <;>
        exact LinearMap.zero_comp _
  rw [hzerofilter, Finset.sum_singleton] at hfiber
  have hzero := planeMass_zero_eq_norm_fixedProjection_sq
    X K i j k hij hik hjk n rho ψ z
  have hpyth := KazhdanFixedSpace.norm_sq_fixedProjection_add_movingProjection
    rho (FreeRootPlane.rootPlaneDegreeSubgroup X K i j k hij hik hjk n) z
  linarith

omit [Fintype K] in
/-- The scalar multiples of the first unit plane vector parametrize the
stage-independent scalar first-root elements. -/
theorem planePoint_smul_unitVectorFirst (t : K) :
    planePoint X K i j k hik hjk n (t • unitVectorFirst X K n) =
      elementaryRoot i k hik (t • (1 : FreeAlgebra K X)) := by
  unfold planePoint unitVectorFirst
  rw [show (((t • ((wordMonomialInDegree X K n 1 : degreeLE X K n),
        (0 : degreeLE X K n)) : PlaneVector X K n)).1 :
      FreeAlgebra K X) = t • (1 : FreeAlgebra K X) from by
    change ((t • wordMonomialInDegree X K n 1 : degreeLE X K n) :
      FreeAlgebra K X) = t • (1 : FreeAlgebra K X)
    rw [Submodule.coe_smul, wordMonomialInDegree_one_val]]
  rw [show (((t • ((wordMonomialInDegree X K n 1 : degreeLE X K n),
        (0 : degreeLE X K n)) : PlaneVector X K n)).2 :
      FreeAlgebra K X) = 0 from by
    change ((t • (0 : degreeLE X K n) : degreeLE X K n) :
      FreeAlgebra K X) = 0
    rw [smul_zero]
    rfl]
  rw [elementaryRoot_zero, mul_one]

omit [Fintype K] in
/-- The scalar multiples of the second unit plane vector parametrize the
stage-independent scalar second-root elements. -/
theorem planePoint_smul_unitVectorSecond (t : K) :
    planePoint X K i j k hik hjk n (t • unitVectorSecond X K n) =
      elementaryRoot j k hjk (t • (1 : FreeAlgebra K X)) := by
  unfold planePoint unitVectorSecond
  rw [show (((t • ((0 : degreeLE X K n),
        (wordMonomialInDegree X K n 1 : degreeLE X K n)) :
          PlaneVector X K n)).1 : FreeAlgebra K X) = 0 from by
    change ((t • (0 : degreeLE X K n) : degreeLE X K n) :
      FreeAlgebra K X) = 0
    rw [smul_zero]
    rfl]
  rw [show (((t • ((0 : degreeLE X K n),
        (wordMonomialInDegree X K n 1 : degreeLE X K n)) :
          PlaneVector X K n)).2 : FreeAlgebra K X) =
      t • (1 : FreeAlgebra K X) from by
    change ((t • wordMonomialInDegree X K n 1 : degreeLE X K n) :
      FreeAlgebra K X) = t • (1 : FreeAlgebra K X)
    rw [Submodule.coe_smul, wordMonomialInDegree_one_val]]
  rw [elementaryRoot_zero, one_mul]

open Classical in
/-- **The limiting two-root moving-mass bound**: the squared norm of the
moving projection for the join of the two full column-root subgroups is
controlled by the displacements of the explicit scalar, unit, and
generator elements alone.  The boundary layers vanish along the
exhaustive degree filtration. -/
theorem norm_joinRootMovingProjection_sq_le_explicit_errors
    [CompleteSpace E] (hψ : ψ ≠ 1) (z : E) :
    ‖KazhdanFixedSpace.subgroupMovingProjection rho
        (elementaryRootSubgroup i k hik ⊔
          elementaryRootSubgroup j k hjk) z‖ ^ 2 ≤
      4 * ((CharacterMass.gap ψ)⁻¹ *
        ((∑ t : K, ‖rho (elementaryRoot i k hik
            (t • (1 : FreeAlgebra K X))) z - z‖ ^ 2) +
          ∑ t : K, ‖rho (elementaryRoot j k hjk
            (t • (1 : FreeAlgebra K X))) z - z‖ ^ 2)) +
      (3 : ℝ) / 2 *
        ((∑ x : X, 2 * ‖z‖ *
          ‖rho (elementaryRoot j i hij.symm
            (FreeAlgebra.ι K x)) z - z‖) +
        ∑ x : X, 2 * ‖z‖ *
          ‖rho (elementaryRoot i j hij (FreeAlgebra.ι K x)) z - z‖) +
      2 * ‖z‖ *
        ‖rho (elementaryRoot j i hij.symm (1 : FreeAlgebra K X)) z - z‖ +
      2 * ‖z‖ *
        ‖rho (elementaryRoot i j hij (1 : FreeAlgebra K X)) z - z‖ := by
  set C : ℝ :=
    4 * ((CharacterMass.gap ψ)⁻¹ *
      ((∑ t : K, ‖rho (elementaryRoot i k hik
          (t • (1 : FreeAlgebra K X))) z - z‖ ^ 2) +
        ∑ t : K, ‖rho (elementaryRoot j k hjk
          (t • (1 : FreeAlgebra K X))) z - z‖ ^ 2)) +
    (3 : ℝ) / 2 *
      ((∑ x : X, 2 * ‖z‖ *
        ‖rho (elementaryRoot j i hij.symm
          (FreeAlgebra.ι K x)) z - z‖) +
      ∑ x : X, 2 * ‖z‖ *
        ‖rho (elementaryRoot i j hij (FreeAlgebra.ι K x)) z - z‖) +
    2 * ‖z‖ *
      ‖rho (elementaryRoot j i hij.symm (1 : FreeAlgebra K X)) z - z‖ +
    2 * ‖z‖ *
      ‖rho (elementaryRoot i j hij (1 : FreeAlgebra K X)) z - z‖
    with hC
  have hfinite : ∀ m : ℕ,
      ‖KazhdanFixedSpace.subgroupMovingProjection rho
        (FreeRootPlane.rootPlaneDegreeSubgroup X K i j k hij hik hjk
          (m + 2)) z‖ ^ 2 ≤
      C + (9 : ℝ) / 2 *
        (firstBoundaryMass X K i j k hik hjk (m + 2) rho ψ z +
          secondBoundaryMass X K i j k hik hjk (m + 2) rho ψ z) := by
    intro m
    have hid := sum_planeMass_nonzero_eq_norm_movingProjection_sq
      X K i j k hij hik hjk (m + 2) rho ψ hψ z
    have hest := sum_planeMass_nonzero_le_explicit_errors
      X K i j k hij hik hjk m rho ψ hψ z
    have hfirstsum : (∑ t : K, ‖rho (planePoint X K i j k hik hjk (m + 2)
        (t • unitVectorFirst X K (m + 2))) z - z‖ ^ 2) =
      ∑ t : K, ‖rho (elementaryRoot i k hik
        (t • (1 : FreeAlgebra K X))) z - z‖ ^ 2 :=
      Finset.sum_congr rfl fun t _ ↦ by
        rw [planePoint_smul_unitVectorFirst X K i j k hik hjk (m + 2) t]
    have hsecondsum : (∑ t : K, ‖rho (planePoint X K i j k hik hjk (m + 2)
        (t • unitVectorSecond X K (m + 2))) z - z‖ ^ 2) =
      ∑ t : K, ‖rho (elementaryRoot j k hjk
        (t • (1 : FreeAlgebra K X))) z - z‖ ^ 2 :=
      Finset.sum_congr rfl fun t _ ↦ by
        rw [planePoint_smul_unitVectorSecond X K i j k hik hjk (m + 2) t]
    rw [hfirstsum, hsecondsum, ← hC] at hest
    linarith
  have hleft : Filter.Tendsto
      (fun m ↦ ‖KazhdanFixedSpace.subgroupMovingProjection rho
        (FreeRootPlane.rootPlaneDegreeSubgroup X K i j k hij hik hjk
          (m + 2)) z‖ ^ 2)
      Filter.atTop
      (nhds (‖KazhdanFixedSpace.subgroupMovingProjection rho
        (elementaryRootSubgroup i k hik ⊔
          elementaryRootSubgroup j k hjk) z‖ ^ 2)) := by
    have h := KazhdanFixedSpace.tendsto_subgroupMovingProjection_iSup
      rho (FreeRootPlane.rootPlaneDegreeSubgroup X K i j k hij hik hjk)
      (elementaryRootSubgroup i k hik ⊔ elementaryRootSubgroup j k hjk)
      (FreeRootPlane.rootPlaneDegreeSubgroup_mono X K i j k hij hik hjk)
      (FreeRootPlane.iSup_rootPlaneDegreeSubgroup X K i j k hij hik hjk)
      z
    have hsq := h.norm.pow 2
    exact (Filter.tendsto_add_atTop_iff_nat 2).2 hsq
  have hfirstb : Filter.Tendsto
      (fun m ↦ firstBoundaryMass X K i j k hik hjk (m + 2) rho ψ z)
      Filter.atTop (nhds 0) :=
    (Filter.tendsto_add_atTop_iff_nat 1).2
      (tendsto_firstBoundaryMass_zero X K i j k hik hjk rho ψ hψ z)
  have hsecondb : Filter.Tendsto
      (fun m ↦ secondBoundaryMass X K i j k hik hjk (m + 2) rho ψ z)
      Filter.atTop (nhds 0) :=
    (Filter.tendsto_add_atTop_iff_nat 1).2
      (tendsto_secondBoundaryMass_zero X K i j k hik hjk rho ψ hψ z)
  have hright : Filter.Tendsto
      (fun m ↦ C + (9 : ℝ) / 2 *
        (firstBoundaryMass X K i j k hik hjk (m + 2) rho ψ z +
          secondBoundaryMass X K i j k hik hjk (m + 2) rho ψ z))
      Filter.atTop (nhds C) := by
    have hscaled : Filter.Tendsto
        (fun m ↦ (9 : ℝ) / 2 *
          (firstBoundaryMass X K i j k hik hjk (m + 2) rho ψ z +
            secondBoundaryMass X K i j k hik hjk (m + 2) rho ψ z))
        Filter.atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul (hfirstb.add hsecondb)
    simpa using tendsto_const_nhds.add hscaled
  exact le_of_tendsto_of_tendsto hleft hright
    (Filter.Eventually.of_forall hfinite)

end FreeRootPlaneMass

end NonsoficGroupsExist
