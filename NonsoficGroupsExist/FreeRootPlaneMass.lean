import NonsoficGroupsExist.FreeRootPlaneMassBase
import NonsoficGroupsExist.FreeRootFunctionalValuation
import NonsoficGroupsExist.CharacterMass
import NonsoficGroupsExist.KazhdanFixedSpace

/-!
# Free-root plane mass: the trivial and boundary decomposition

`FreeRootPlaneMassBase` builds the character mass of a plane component and
its behaviour under the stage inclusion.  This file splits that mass into
the parts carried by characters trivial on each coordinate and by the
top-degree boundary, and proves the step estimates the Kazhdan bound
consumes.
-/

namespace NonsoficGroupsExist

namespace FreeRootPlaneMass

open FreeAlgebraDegree

variable (X : Type*) [Fintype X]
variable (K : Type*) [Field K] [Fintype K]
variable (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (rho : elementaryGroup (Fin 3) (FreeAlgebra K X) →* (E ≃ₗᵢ[ℝ] E))
variable (ψ : AddChar K ℂ)

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
