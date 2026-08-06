import NonsoficGroupsExist.FreeRootCharacterValuationBase
import NonsoficGroupsExist.KazhdanFixedSpace

/-!
# Free-root character valuations: transport across a representation

The analytic half.  `FreeRootCharacterValuationBase` defines the valuation
and its region partition over the finite alphabet; this file carries them
across an orthogonal representation -- Fourier moving parts, the mass
estimates on region unions, and the shear transport that sends each
leading-generator fibre into the region Kassabov's argument requires.
-/

namespace NonsoficGroupsExist

namespace FreeRootCharacterValuation

open FreeAlgebraDegree
open FreeRootPlaneFourier
open FreeRootFiltration
open FreeRootPlane
open FiniteInvolutionDecomposition

noncomputable section

universe u

variable (X : Type*) [Fintype X]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Fourier moving part lies in the orthogonal complement of the
stage-fixed subspace. -/
theorem planeMovingPart_mem_fixedSubspace_orthogonal
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (n : ℕ) :
    planeMovingPart X i j k hij hik hjk rho z n ∈
      (KazhdanFixedSpace.fixedSubspace rho
        (rootPlaneDegreeSubgroup X (ZMod 2) i j k hij hik hjk n))ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro y hy
  unfold planeMovingPart
  rw [inner_sum]
  apply Finset.sum_eq_zero
  intro sign hsign
  exact inner_planeComponent_eq_zero_of_fixed_of_mem_nonzero
    X i j k hij hik hjk rho z y n sign hsign hy

/-- The single all-positive Fourier component. -/
noncomputable def planeTrivialPart
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (n : ℕ) : E :=
  planeComponent X i j k hij hik hjk n rho (fun _ ↦ true) z

theorem planeTrivialPart_mem_fixedSubspace
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (n : ℕ) :
    planeTrivialPart X i j k hij hik hjk rho z n ∈
      KazhdanFixedSpace.fixedSubspace rho
        (rootPlaneDegreeSubgroup X (ZMod 2) i j k hij hik hjk n) := by
  rw [KazhdanFixedSpace.mem_fixedSubspace_iff]
  intro g hg
  obtain ⟨q, hq⟩ := exists_planeFamily_eq X i j k hij hik hjk n ⟨g, hg⟩
  have hq' : planeFamily X i j k hij hik hjk n q = g := by
    simpa using hq
  unfold planeTrivialPart
  rw [← hq']
  simpa using action_planeComponent X i j k hij hik hjk n rho
    (fun _ ↦ true) z q

theorem sum_planeRegionSignSet_zero_eq_trivialPart
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (n : ℕ) :
    (∑ sign ∈ planeRegionSignSet X i j k hij hik hjk n .zero,
        planeComponent X i j k hij hik hjk n rho sign z) =
      planeTrivialPart X i j k hij hik hjk rho z n := by
  classical
  unfold planeTrivialPart
  rw [Finset.sum_eq_single (fun _ ↦ true)]
  · intro sign hsign hne
    have hzero : planeCharacterRegion X i j k hij hik hjk n sign = .zero := by
      simpa [planeRegionSignSet] using hsign
    exact planeComponent_eq_zero_of_region_zero_of_sign_ne_true
      X i j k hij hik hjk rho z n sign hzero hne
  · simp [planeRegionSignSet, planeCharacterRegion_const_true_eq_zero]

/-- Exact fixed-plus-moving reconstruction at every finite stage. -/
theorem planeTrivialPart_add_movingPart
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (n : ℕ) :
    planeTrivialPart X i j k hij hik hjk rho z n +
      planeMovingPart X i j k hij hik hjk rho z n = z := by
  classical
  let nonzero := planeNonzeroRegionSignSet X i j k hij hik hjk n
  let zero := planeRegionSignSet X i j k hij hik hjk n .zero
  have hpartition : (Finset.univ : Finset
      (Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool)) =
      nonzero ∪ zero := by
    ext sign
    simp only [nonzero, zero, planeNonzeroRegionSignSet, planeRegionSignSet,
      Finset.mem_univ, Finset.mem_filter, true_and, Finset.mem_union]
    by_cases hzero : planeCharacterRegion X i j k hij hik hjk n sign = .zero
    · simp [hzero]
    · simp [hzero]
  have hdisjoint : Disjoint nonzero zero := by
    rw [Finset.disjoint_left]
    intro sign hn hz
    simp only [nonzero, planeNonzeroRegionSignSet, Finset.mem_filter,
      Finset.mem_univ, true_and] at hn
    simp only [zero, planeRegionSignSet, Finset.mem_filter,
      Finset.mem_univ, true_and] at hz
    exact hn hz
  have htotal := sum_planeComponent X i j k hij hik hjk n rho z
  change (∑ sign ∈ (Finset.univ : Finset
      (Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool)),
      planeComponent X i j k hij hik hjk n rho sign z) = z at htotal
  rw [hpartition, Finset.sum_union hdisjoint] at htotal
  rw [sum_planeRegionSignSet_zero_eq_trivialPart
    X i j k hij hik hjk rho z n] at htotal
  simpa [nonzero, planeMovingPart, add_comm] using htotal

/-- The Fourier moving part is the genuine orthogonal projection onto the
complement of the stage-fixed space. -/
theorem planeMovingPart_eq_subgroupMovingProjection [CompleteSpace E]
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (n : ℕ) :
    planeMovingPart X i j k hij hik hjk rho z n =
      KazhdanFixedSpace.subgroupMovingProjection rho
        (rootPlaneDegreeSubgroup X (ZMod 2) i j k hij hik hjk n) z := by
  let H := rootPlaneDegreeSubgroup X (ZMod 2) i j k hij hik hjk n
  let U := KazhdanFixedSpace.fixedSubspace rho H
  let fixed := planeTrivialPart X i j k hij hik hjk rho z n
  let moving := planeMovingPart X i j k hij hik hjk rho z n
  have hfixed : fixed ∈ U :=
    planeTrivialPart_mem_fixedSubspace X i j k hij hik hjk rho z n
  have hmoving : moving ∈ Uᗮ :=
    planeMovingPart_mem_fixedSubspace_orthogonal
      X i j k hij hik hjk rho z n
  have hreconstruct : fixed + moving = z :=
    planeTrivialPart_add_movingPart X i j k hij hik hjk rho z n
  have hres : z - fixed = moving := by
    rw [← hreconstruct]
    abel
  have hresOrth : z - fixed ∈ Uᗮ := by
    rw [hres]
    exact hmoving
  letI : CompleteSpace U :=
    (KazhdanFixedSpace.isClosed_fixedSubspace rho H).completeSpace_coe
  have hfixedProjection : (KazhdanFixedSpace.fixedProjection rho H z : E) =
      fixed := by
    change U.starProjection z = fixed
    exact U.eq_starProjection_of_mem_orthogonal hfixed hresOrth
  rw [KazhdanFixedSpace.subgroupMovingProjection_eq_sub_fixedProjection,
    hfixedProjection, hres]

/-- The finite Fourier moving parts converge to the genuine moving projection
for the join of the two full column-root subgroups.  Thus no mass can escape
through the increasing degree filtration. -/
theorem tendsto_planeMovingPart [CompleteSpace E]
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    Filter.Tendsto
      (fun n ↦ planeMovingPart X i j k hij hik hjk rho z n)
      Filter.atTop
      (nhds (KazhdanFixedSpace.subgroupMovingProjection rho
        (elementaryRootSubgroup i k hik ⊔
          elementaryRootSubgroup j k hjk) z)) := by
  have h := KazhdanFixedSpace.tendsto_subgroupMovingProjection_iSup rho
    (rootPlaneDegreeSubgroup X (ZMod 2) i j k hij hik hjk)
    (elementaryRootSubgroup i k hik ⊔ elementaryRootSubgroup j k hjk)
    (rootPlaneDegreeSubgroup_mono X (ZMod 2) i j k hij hik hjk)
    (iSup_rootPlaneDegreeSubgroup X (ZMod 2) i j k hij hik hjk) z
  simpa only [planeMovingPart_eq_subgroupMovingProjection
    X i j k hij hik hjk rho z] using h

/-- Squared moving mass converges to the squared norm of the full two-root
moving projection. -/
theorem tendsto_norm_planeMovingPart_sq [CompleteSpace E]
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    Filter.Tendsto
      (fun n ↦ ‖planeMovingPart X i j k hij hik hjk rho z n‖ ^ 2)
      Filter.atTop
      (nhds (‖KazhdanFixedSpace.subgroupMovingProjection rho
        (elementaryRootSubgroup i k hik ⊔
          elementaryRootSubgroup j k hjk) z‖ ^ 2)) := by
  exact (tendsto_planeMovingPart X i j k hij hik hjk rho z).norm.pow 2

private theorem sum_union_le_sum_add_sum
    {α : Type*} [DecidableEq α] (f : α → ℝ) (hf : ∀ x, 0 ≤ f x)
    (a b : Finset α) :
    (∑ x ∈ a ∪ b, f x) ≤ (∑ x ∈ a, f x) + ∑ x ∈ b, f x := by
  have hab : a ∪ b = a ∪ (b \ a) := by
    ext x
    simp
  have hdisjoint : Disjoint a (b \ a) := by
    rw [Finset.disjoint_left]
    intro x ha hba
    exact (Finset.mem_sdiff.mp hba).2 ha
  have hdiff : (∑ x ∈ b \ a, f x) ≤ ∑ x ∈ b, f x :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (fun x _ _ ↦ hf x)
  rw [hab, Finset.sum_union hdisjoint]
  simpa [add_comm] using add_le_add_left hdiff (∑ x ∈ a, f x)

/-- After one refinement, the mass over two coarse regions is supported on
the same two fine regions together with the two new top-degree layers. -/
theorem sum_norm_planeRegionUnion_sq_le_succ_union_topBoundarySignSets
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (r s : ValuationRegion)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    (∑ sign ∈ (planeRegionSignSet X i j k hij hik hjk n r ∪
          planeRegionSignSet X i j k hij hik hjk n s),
        ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2) ≤
      ∑ sign ∈
          ((planeRegionSignSet X i j k hij hik hjk (n + 1) r ∪
              planeRegionSignSet X i j k hij hik hjk (n + 1) s) ∪
            (planeFirstTopBoundarySignSet X i j k hij hik hjk (n + 1) ∪
              planeSecondTopBoundarySignSet X i j k hij hik hjk (n + 1))),
        ‖planeComponent X i j k hij hik hjk (n + 1) rho sign z‖ ^ 2 := by
  classical
  let coarse := planeRegionSignSet X i j k hij hik hjk n r ∪
    planeRegionSignSet X i j k hij hik hjk n s
  let fine := planeRegionSignSet X i j k hij hik hjk (n + 1) r ∪
    planeRegionSignSet X i j k hij hik hjk (n + 1) s
  let preimage := fineRestrictionSignSet
    (Nat.card (Plane X i j k hij hik hjk (n + 1)))
    (Nat.card (Plane X i j k hij hik hjk n))
    (planeSuccIndex X i j k hij hik hjk n) coarse
  let validPreimage := planeValidSignSubset X i j k hij hik hjk (n + 1) preimage
  let firstTop := planeFirstTopBoundarySignSet X i j k hij hik hjk (n + 1)
  let secondTop := planeSecondTopBoundarySignSet X i j k hij hik hjk (n + 1)
  let mass := fun sign :
      Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool ↦
    ‖planeComponent X i j k hij hik hjk (n + 1) rho sign z‖ ^ 2
  have hremove :
      (∑ sign ∈ preimage, mass sign) =
        ∑ sign ∈ validPreimage, mass sign := by
    simpa [validPreimage, mass] using
      sum_norm_planeSignSet_eq_filter_valid
        X i j k hij hik hjk (n + 1) rho preimage z
  have hsubset : validPreimage ⊆ fine ∪ (firstTop ∪ secondTop) := by
    simpa [validPreimage, preimage, coarse, fine, firstTop, secondTop] using
      filter_valid_fineRestriction_regionUnion_subset
        X i j k hij hik hjk n r s
  calc
    (∑ sign ∈ coarse,
        ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2) =
        ∑ sign ∈ preimage, mass sign :=
      (sum_norm_planeRestriction_sq X i j k hij hik hjk n rho coarse z).symm
    _ = ∑ sign ∈ validPreimage, mass sign := hremove
    _ ≤ ∑ sign ∈ fine ∪ (firstTop ∪ secondTop), mass sign :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun _ _ _ ↦ sq_nonneg _)

/-- Refining the mass in any union of two valuation regions changes the
region only on the two newly exposed top-degree character layers.  Invalid
binary assignments are discarded here using their proved zero Fourier
component; no character-validity premise is supplied by the caller. -/
theorem sum_norm_planeRegionUnion_sq_le_succ_add_topBoundaries
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (r s : ValuationRegion)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    (∑ sign ∈ (planeRegionSignSet X i j k hij hik hjk n r ∪
          planeRegionSignSet X i j k hij hik hjk n s),
        ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2) ≤
      (∑ sign ∈ (planeRegionSignSet X i j k hij hik hjk (n + 1) r ∪
            planeRegionSignSet X i j k hij hik hjk (n + 1) s),
          ‖planeComponent X i j k hij hik hjk (n + 1) rho sign z‖ ^ 2) +
        planeFirstTopBoundaryMass X i j k hij hik hjk rho z (n + 1) +
        planeSecondTopBoundaryMass X i j k hij hik hjk rho z (n + 1) := by
  classical
  let fine := planeRegionSignSet X i j k hij hik hjk (n + 1) r ∪
    planeRegionSignSet X i j k hij hik hjk (n + 1) s
  let firstTop := planeFirstTopBoundarySignSet X i j k hij hik hjk (n + 1)
  let secondTop := planeSecondTopBoundarySignSet X i j k hij hik hjk (n + 1)
  let mass := fun sign :
      Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool ↦
    ‖planeComponent X i j k hij hik hjk (n + 1) rho sign z‖ ^ 2
  calc
    _ ≤ ∑ sign ∈ fine ∪ (firstTop ∪ secondTop), mass sign := by
      simpa [fine, firstTop, secondTop, mass] using
        sum_norm_planeRegionUnion_sq_le_succ_union_topBoundarySignSets
          X i j k hij hik hjk n r s rho z
    _ ≤ (∑ sign ∈ fine, mass sign) +
          ∑ sign ∈ firstTop ∪ secondTop, mass sign :=
      sum_union_le_sum_add_sum mass (fun _ ↦ sq_nonneg _) fine
        (firstTop ∪ secondTop)
    _ ≤ (∑ sign ∈ fine, mass sign) +
          ((∑ sign ∈ firstTop, mass sign) +
            ∑ sign ∈ secondTop, mass sign) :=
      by
        have hexception : (∑ sign ∈ firstTop ∪ secondTop, mass sign) ≤
            (∑ sign ∈ firstTop, mass sign) +
              ∑ sign ∈ secondTop, mass sign :=
          sum_union_le_sum_add_sum mass (fun _ ↦ sq_nonneg _) firstTop secondTop
        simpa [add_comm] using add_le_add_left hexception
          (∑ sign ∈ fine, mass sign)
    _ = _ := by
      simp only [fine, firstTop, secondTop, mass,
        planeFirstTopBoundaryMass, planeSecondTopBoundaryMass]
      rw [add_assoc]

theorem planeFirstTrivialMass_step
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (n : ℕ) :
    planeFirstTrivialMass X i j k hij hik hjk rho z n =
      planeFirstTopBoundaryMass X i j k hij hik hjk rho z (n + 1) +
        planeFirstTrivialMass X i j k hij hik hjk rho z (n + 1) :=
  sum_norm_planeFirstTrivialSignSet_sq X i j k hij hik hjk n rho z

theorem planeSecondTrivialMass_step
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (n : ℕ) :
    planeSecondTrivialMass X i j k hij hik hjk rho z n =
      planeSecondTopBoundaryMass X i j k hij hik hjk rho z (n + 1) +
        planeSecondTrivialMass X i j k hij hik hjk rho z (n + 1) :=
  sum_norm_planeSecondTrivialSignSet_sq X i j k hij hik hjk n rho z

theorem planeFirstTopBoundaryMass_nonneg
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (n : ℕ) :
    0 ≤ planeFirstTopBoundaryMass X i j k hij hik hjk rho z n :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

theorem planeSecondTopBoundaryMass_nonneg
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (n : ℕ) :
    0 ≤ planeSecondTopBoundaryMass X i j k hij hik hjk rho z n :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

theorem planeFirstTrivialMass_nonneg
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (n : ℕ) :
    0 ≤ planeFirstTrivialMass X i j k hij hik hjk rho z n :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

theorem planeSecondTrivialMass_nonneg
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (n : ℕ) :
    0 ≤ planeSecondTrivialMass X i j k hij hik hjk rho z n :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

theorem antitone_planeFirstTrivialMass
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    Antitone (planeFirstTrivialMass X i j k hij hik hjk rho z) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [planeFirstTrivialMass_step X i j k hij hik hjk rho z n]
  exact le_add_of_nonneg_left
    (planeFirstTopBoundaryMass_nonneg X i j k hij hik hjk rho z (n + 1))

theorem antitone_planeSecondTrivialMass
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    Antitone (planeSecondTrivialMass X i j k hij hik hjk rho z) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [planeSecondTrivialMass_step X i j k hij hik hjk rho z n]
  exact le_add_of_nonneg_left
    (planeSecondTopBoundaryMass_nonneg X i j k hij hik hjk rho z (n + 1))

/-- First-coordinate top-degree boundary mass vanishes along the exhaustive
filtration.  This is a consequence of an actual nonnegative telescoping
identity, not an assumed boundary condition. -/
theorem tendsto_planeFirstTopBoundaryMass_succ_zero
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    Filter.Tendsto
      (fun n ↦ planeFirstTopBoundaryMass X i j k hij hik hjk rho z (n + 1))
      Filter.atTop (nhds 0) := by
  let mass := planeFirstTrivialMass X i j k hij hik hjk rho z
  have hanti : Antitone mass :=
    antitone_planeFirstTrivialMass X i j k hij hik hjk rho z
  have hbdd : BddBelow (Set.range mass) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact planeFirstTrivialMass_nonneg X i j k hij hik hjk rho z n
  let limit : ℝ := ⨅ n, mass n
  have hlimit : Filter.Tendsto mass Filter.atTop (nhds limit) :=
    tendsto_atTop_ciInf hanti hbdd
  have hlimitSucc : Filter.Tendsto (fun n ↦ mass (n + 1))
      Filter.atTop (nhds limit) :=
    (Filter.tendsto_add_atTop_iff_nat 1).2 hlimit
  have hdiff : Filter.Tendsto (fun n ↦ mass n - mass (n + 1))
      Filter.atTop (nhds 0) := by
    simpa using hlimit.sub hlimitSucc
  convert hdiff using 1
  funext n
  change planeFirstTopBoundaryMass X i j k hij hik hjk rho z (n + 1) =
    planeFirstTrivialMass X i j k hij hik hjk rho z n -
      planeFirstTrivialMass X i j k hij hik hjk rho z (n + 1)
  rw [planeFirstTrivialMass_step X i j k hij hik hjk rho z n]
  ring

/-- The symmetric second-coordinate top-degree boundary also vanishes. -/
theorem tendsto_planeSecondTopBoundaryMass_succ_zero
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    Filter.Tendsto
      (fun n ↦ planeSecondTopBoundaryMass X i j k hij hik hjk rho z (n + 1))
      Filter.atTop (nhds 0) := by
  let mass := planeSecondTrivialMass X i j k hij hik hjk rho z
  have hanti : Antitone mass :=
    antitone_planeSecondTrivialMass X i j k hij hik hjk rho z
  have hbdd : BddBelow (Set.range mass) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact planeSecondTrivialMass_nonneg X i j k hij hik hjk rho z n
  let limit : ℝ := ⨅ n, mass n
  have hlimit : Filter.Tendsto mass Filter.atTop (nhds limit) :=
    tendsto_atTop_ciInf hanti hbdd
  have hlimitSucc : Filter.Tendsto (fun n ↦ mass (n + 1))
      Filter.atTop (nhds limit) :=
    (Filter.tendsto_add_atTop_iff_nat 1).2 hlimit
  have hdiff : Filter.Tendsto (fun n ↦ mass n - mass (n + 1))
      Filter.atTop (nhds 0) := by
    simpa using hlimit.sub hlimitSucc
  convert hdiff using 1
  funext n
  change planeSecondTopBoundaryMass X i j k hij hik hjk rho z (n + 1) =
    planeSecondTrivialMass X i j k hij hik hjk rho z n -
      planeSecondTrivialMass X i j k hij hik hjk rho z (n + 1)
  rw [planeSecondTrivialMass_step X i j k hij hik hjk rho z n]
  ring

/-- The first-character opposite-shear formula needs only algebraic character
validity. -/
theorem firstCoefficientEigenvalue_oppositeConjugatedRestriction_of_valid
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : X) (n : ℕ)
    (fineSign : Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool)
    (hvalid : IsPlaneCharacterSign X i j k hij hik hjk (n + 1) fineSign)
    (a : degreeLE X (ZMod 2) n) :
    firstCoefficientEigenvalue X i j k hij hik hjk n
        (fun q ↦ fineSign
          (oppositeConjugatedPlaneSuccIndex X i j k hij hik hjk x n q)) a =
      oppositeShearedFirstCharacter X
        (firstCoefficientEigenvalue X i j k hij hik hjk (n + 1) fineSign)
        (secondCoefficientEigenvalue X i j k hij hik hjk (n + 1) fineSign)
        x a := by
  rw [firstCoefficientEigenvalue,
    planeEigenvalue_oppositeConjugatedRestriction]
  have hconj : oppositeConjugatedPlaneSucc X i j k hij hik hjk x n
      (firstCoordinate X (ZMod 2) i j k hij hik hjk n a) =
      generatorShearedFirstCoordinate X (ZMod 2) i j k hij hik hjk x n a := by
    apply Subtype.ext
    exact conjugate_firstCoordinate_opposite_generator
      X (ZMod 2) i j k hij hik hjk x n a
  rw [hconj, generatorShearedFirstCoordinate, hvalid]
  rfl

/-- On a nonzero fine Fourier component, restricting its sign assignment
along the opposite conjugated-plane map produces exactly the algebraic dual
shear of the first coefficient character. -/
theorem firstCoefficientEigenvalue_oppositeConjugatedRestriction
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : X) (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (fineSign : Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool)
    (z : E)
    (hv : planeComponent X i j k hij hik hjk (n + 1) rho fineSign z ≠ 0)
    (a : degreeLE X (ZMod 2) n) :
    firstCoefficientEigenvalue X i j k hij hik hjk n
        (fun q ↦ fineSign
          (oppositeConjugatedPlaneSuccIndex X i j k hij hik hjk x n q)) a =
      oppositeShearedFirstCharacter X
        (firstCoefficientEigenvalue X i j k hij hik hjk (n + 1) fineSign)
        (secondCoefficientEigenvalue X i j k hij hik hjk (n + 1) fineSign)
        x a := by
  exact firstCoefficientEigenvalue_oppositeConjugatedRestriction_of_valid
    X i j k hij hik hjk x n fineSign
      (isPlaneCharacterSign_of_component_ne_zero
        X i j k hij hik hjk (n + 1) rho fineSign z hv) a

/-- The second coefficient of the opposite-conjugated restriction is exactly
the restricted fine second character. -/
theorem secondCoefficientEigenvalue_oppositeConjugatedRestriction
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : X) (n : ℕ)
    (fineSign : Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool)
    (b : degreeLE X (ZMod 2) n) :
    secondCoefficientEigenvalue X i j k hij hik hjk n
        (fun q ↦ fineSign
          (oppositeConjugatedPlaneSuccIndex X i j k hij hik hjk x n q)) b =
      oppositeShearedSecondCharacter X
        (secondCoefficientEigenvalue X i j k hij hik hjk (n + 1) fineSign) b := by
  rw [secondCoefficientEigenvalue,
    planeEigenvalue_oppositeConjugatedRestriction]
  have hconj : oppositeConjugatedPlaneSucc X i j k hij hik hjk x n
      (secondCoordinate X (ZMod 2) i j k hij hik hjk n b) =
      secondCoordinate X (ZMod 2) i j k hij hik hjk (n + 1)
        (coefficientSucc X (ZMod 2) b) := by
    apply Subtype.ext
    exact conjugate_secondCoordinate_opposite_generator
      X (ZMod 2) i j k hij hik hjk x n b
  rw [hconj]
  rfl

/-- The first coefficient of the forward-conjugated restriction is the
ordinary restriction of the fine first character. -/
theorem firstCoefficientEigenvalue_forwardConjugatedRestriction
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : X) (n : ℕ)
    (fineSign : Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool)
    (a : degreeLE X (ZMod 2) n) :
    firstCoefficientEigenvalue X i j k hij hik hjk n
        (fun q ↦ fineSign
          (forwardConjugatedPlaneSuccIndex X i j k hij hik hjk x n q)) a =
      forwardShearedFirstCharacter X
        (firstCoefficientEigenvalue X i j k hij hik hjk (n + 1) fineSign) a := by
  rw [firstCoefficientEigenvalue,
    planeEigenvalue_forwardConjugatedRestriction]
  have hconj : forwardConjugatedPlaneSucc X i j k hij hik hjk x n
      (firstCoordinate X (ZMod 2) i j k hij hik hjk n a) =
      firstCoordinate X (ZMod 2) i j k hij hik hjk (n + 1)
        (coefficientSucc X (ZMod 2) a) := by
    apply Subtype.ext
    exact conjugate_firstCoordinate_generator X (ZMod 2) i j k hij hik hjk x n a
  rw [hconj]
  rfl

/-- The second-character forward-shear formula from algebraic character
validity alone. -/
theorem secondCoefficientEigenvalue_forwardConjugatedRestriction_of_valid
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : X) (n : ℕ)
    (fineSign : Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool)
    (hvalid : IsPlaneCharacterSign X i j k hij hik hjk (n + 1) fineSign)
    (b : degreeLE X (ZMod 2) n) :
    secondCoefficientEigenvalue X i j k hij hik hjk n
        (fun q ↦ fineSign
          (forwardConjugatedPlaneSuccIndex X i j k hij hik hjk x n q)) b =
      forwardShearedSecondCharacter X
        (firstCoefficientEigenvalue X i j k hij hik hjk (n + 1) fineSign)
        (secondCoefficientEigenvalue X i j k hij hik hjk (n + 1) fineSign)
        x b := by
  rw [secondCoefficientEigenvalue,
    planeEigenvalue_forwardConjugatedRestriction]
  have hconj : forwardConjugatedPlaneSucc X i j k hij hik hjk x n
      (secondCoordinate X (ZMod 2) i j k hij hik hjk n b) =
      generatorShearedSecondCoordinate X (ZMod 2) i j k hij hik hjk x n b := by
    apply Subtype.ext
    exact conjugate_secondCoordinate_generator X (ZMod 2) i j k hij hik hjk x n b
  rw [hconj, generatorShearedSecondCoordinate, hvalid]
  simp only [forwardShearedSecondCharacter, oppositeShearedFirstCharacter,
    characterProduct, restrictCharacterSucc, leftDerivedCharacter,
    firstCoefficientEigenvalue, secondCoefficientEigenvalue]
  rw [mul_comm]

/-- On a nonzero fine component, the second coefficient of the
forward-conjugated restriction is exactly the algebraic forward dual shear. -/
theorem secondCoefficientEigenvalue_forwardConjugatedRestriction
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : X) (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (fineSign : Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool)
    (z : E)
    (hv : planeComponent X i j k hij hik hjk (n + 1) rho fineSign z ≠ 0)
    (b : degreeLE X (ZMod 2) n) :
    secondCoefficientEigenvalue X i j k hij hik hjk n
        (fun q ↦ fineSign
          (forwardConjugatedPlaneSuccIndex X i j k hij hik hjk x n q)) b =
      forwardShearedSecondCharacter X
        (firstCoefficientEigenvalue X i j k hij hik hjk (n + 1) fineSign)
        (secondCoefficientEigenvalue X i j k hij hik hjk (n + 1) fineSign)
        x b := by
  exact secondCoefficientEigenvalue_forwardConjugatedRestriction_of_valid
    X i j k hij hik hjk x n fineSign
      (isPlaneCharacterSign_of_component_ne_zero
        X i j k hij hik hjk (n + 1) rho fineSign z hv) b

/-- Below the top-degree boundary, the second character of an opposite
conjugated restriction retains the source character's canonical leading
generator. -/
theorem leastLeadingGeneratorIndex_second_oppositeConjugatedRestriction
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : X) (n : ℕ)
    (fineSign : Fin (Nat.card (Plane X i j k hij hik hjk (n + 2))) → Bool)
    (hle : secondCoefficientValuation X i j k hij hik hjk (n + 2) fineSign ≤
      n + 1) :
    leastLeadingGeneratorIndex X
        (secondCoefficientEigenvalue X i j k hij hik hjk (n + 1)
          (fun r ↦ fineSign (oppositeConjugatedPlaneSuccIndex
            X i j k hij hik hjk x (n + 1) r))) =
      leastLeadingGeneratorIndex X
        (secondCoefficientEigenvalue X i j k hij hik hjk (n + 2) fineSign) := by
  have hcharacter : secondCoefficientEigenvalue X i j k hij hik hjk (n + 1)
      (fun r ↦ fineSign (oppositeConjugatedPlaneSuccIndex
        X i j k hij hik hjk x (n + 1) r)) =
      restrictCharacterSucc X
        (secondCoefficientEigenvalue X i j k hij hik hjk (n + 2) fineSign) := by
    funext b
    exact secondCoefficientEigenvalue_oppositeConjugatedRestriction
      X i j k hij hik hjk x (n + 1) fineSign b
  rw [hcharacter]
  exact leastLeadingGeneratorIndex_restrictCharacterSucc X _ hle

/-- Symmetrically, the first character of a forward-conjugated restriction
retains its canonical leading generator below the boundary. -/
theorem leastLeadingGeneratorIndex_first_forwardConjugatedRestriction
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : X) (n : ℕ)
    (fineSign : Fin (Nat.card (Plane X i j k hij hik hjk (n + 2))) → Bool)
    (hle : firstCoefficientValuation X i j k hij hik hjk (n + 2) fineSign ≤
      n + 1) :
    leastLeadingGeneratorIndex X
        (firstCoefficientEigenvalue X i j k hij hik hjk (n + 1)
          (fun r ↦ fineSign (forwardConjugatedPlaneSuccIndex
            X i j k hij hik hjk x (n + 1) r))) =
      leastLeadingGeneratorIndex X
        (firstCoefficientEigenvalue X i j k hij hik hjk (n + 2) fineSign) := by
  have hcharacter : firstCoefficientEigenvalue X i j k hij hik hjk (n + 1)
      (fun r ↦ fineSign (forwardConjugatedPlaneSuccIndex
        X i j k hij hik hjk x (n + 1) r)) =
      restrictCharacterSucc X
        (firstCoefficientEigenvalue X i j k hij hik hjk (n + 2) fineSign) := by
    funext a
    exact firstCoefficientEigenvalue_forwardConjugatedRestriction
      X i j k hij hik hjk x (n + 1) fineSign a
  rw [hcharacter]
  exact leastLeadingGeneratorIndex_restrictCharacterSucc X _ hle

/-- The interior of an `A ∪ B` leading fiber consists of characters detected
strictly below the top degree that will be lost on restriction. -/
noncomputable def planeABInteriorLeadingSignSet
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (q : Fin (Fintype.card X)) :
    Finset (Fin (Nat.card (Plane X i j k hij hik hjk (n + 2))) → Bool) :=
  (planeABLeadingSignSet X i j k hij hik hjk (n + 1) q).filter
    fun fineSign ↦
      secondCoefficientValuation X i j k hij hik hjk (n + 2) fineSign ≤ n + 1

/-- The algebraically valid characters in one interior `A ∪ B` fiber. -/
noncomputable def planeABValidInteriorLeadingSignSet
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (q : Fin (Fintype.card X)) :
    Finset (Fin (Nat.card (Plane X i j k hij hik hjk (n + 2))) → Bool) :=
  by
    classical
    exact (planeABInteriorLeadingSignSet X i j k hij hik hjk n q).filter
      (IsPlaneCharacterSign X i j k hij hik hjk (n + 2))

/-- Coarse sign characters obtained by the concrete opposite shear from one
interior leading fiber. -/
noncomputable def planeABOppositeInteriorImageSignSet
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (q : Fin (Fintype.card X)) :
    Finset (Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool) :=
  (planeABValidInteriorLeadingSignSet X i j k hij hik hjk n q).image
    fun fineSign r ↦ fineSign (oppositeConjugatedPlaneSuccIndex
      X i j k hij hik hjk (generatorEnumeration X q) (n + 1) r)

/-- Distinct least-leading-generator fibers have disjoint opposite-shear
images below the top-degree boundary. -/
theorem planeABOppositeInteriorImageSignSet_pairwise_disjoint
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ) :
    Pairwise (fun q r : Fin (Fintype.card X) ↦
      Disjoint (planeABOppositeInteriorImageSignSet
        X i j k hij hik hjk n q)
        (planeABOppositeInteriorImageSignSet X i j k hij hik hjk n r)) := by
  intro q r hqr
  rw [Finset.disjoint_left]
  intro coarseSign hq hr
  obtain ⟨fineQ, hfineQ, hcoarseQ⟩ := Finset.mem_image.mp hq
  obtain ⟨fineR, hfineR, hcoarseR⟩ := Finset.mem_image.mp hr
  simp only [planeABValidInteriorLeadingSignSet, Finset.mem_filter] at hfineQ hfineR
  obtain ⟨hfineQ, _⟩ := hfineQ
  obtain ⟨hfineR, _⟩ := hfineR
  simp only [planeABInteriorLeadingSignSet, Finset.mem_filter] at hfineQ hfineR
  obtain ⟨hqFiber, hqLe⟩ := hfineQ
  obtain ⟨hrFiber, hrLe⟩ := hfineR
  simp only [planeABLeadingSignSet, Finset.mem_filter, Finset.mem_univ,
    true_and] at hqFiber hrFiber
  have hleastQ :=
    leastLeadingGeneratorIndex_second_oppositeConjugatedRestriction
      X i j k hij hik hjk (generatorEnumeration X q) n fineQ hqLe
  have hleastR :=
    leastLeadingGeneratorIndex_second_oppositeConjugatedRestriction
      X i j k hij hik hjk (generatorEnumeration X r) n fineR hrLe
  have hindexQ : leastLeadingGeneratorIndex X
      (secondCoefficientEigenvalue X i j k hij hik hjk (n + 1) coarseSign) =
      q.val := by
    rw [← hcoarseQ]
    exact hleastQ.trans hqFiber.2
  have hindexR : leastLeadingGeneratorIndex X
      (secondCoefficientEigenvalue X i j k hij hik hjk (n + 1) coarseSign) =
      r.val := by
    rw [← hcoarseR]
    exact hleastR.trans hrFiber.2
  apply hqr
  apply Fin.ext
  exact hindexQ.symm.trans hindexR

/-- The below-boundary interior of a `C ∪ B` leading fiber. -/
noncomputable def planeCBInteriorLeadingSignSet
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (q : Fin (Fintype.card X)) :
    Finset (Fin (Nat.card (Plane X i j k hij hik hjk (n + 2))) → Bool) :=
  (planeCBLeadingSignSet X i j k hij hik hjk (n + 1) q).filter
    fun fineSign ↦
      firstCoefficientValuation X i j k hij hik hjk (n + 2) fineSign ≤ n + 1

/-- The algebraically valid characters in one interior `C ∪ B` fiber. -/
noncomputable def planeCBValidInteriorLeadingSignSet
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (q : Fin (Fintype.card X)) :
    Finset (Fin (Nat.card (Plane X i j k hij hik hjk (n + 2))) → Bool) :=
  by
    classical
    exact (planeCBInteriorLeadingSignSet X i j k hij hik hjk n q).filter
      (IsPlaneCharacterSign X i j k hij hik hjk (n + 2))

/-- Coarse sign characters obtained by the concrete forward shear from one
interior `C ∪ B` fiber. -/
noncomputable def planeCBForwardInteriorImageSignSet
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (q : Fin (Fintype.card X)) :
    Finset (Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool) :=
  (planeCBValidInteriorLeadingSignSet X i j k hij hik hjk n q).image
    fun fineSign r ↦ fineSign (forwardConjugatedPlaneSuccIndex
      X i j k hij hik hjk (generatorEnumeration X q) (n + 1) r)

/-- Distinct `C ∪ B` least-leading-generator fibers have disjoint
forward-shear images below the top-degree boundary. -/
theorem planeCBForwardInteriorImageSignSet_pairwise_disjoint
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ) :
    Pairwise (fun q r : Fin (Fintype.card X) ↦
      Disjoint (planeCBForwardInteriorImageSignSet
        X i j k hij hik hjk n q)
        (planeCBForwardInteriorImageSignSet X i j k hij hik hjk n r)) := by
  intro q r hqr
  rw [Finset.disjoint_left]
  intro coarseSign hq hr
  obtain ⟨fineQ, hfineQ, hcoarseQ⟩ := Finset.mem_image.mp hq
  obtain ⟨fineR, hfineR, hcoarseR⟩ := Finset.mem_image.mp hr
  simp only [planeCBValidInteriorLeadingSignSet, Finset.mem_filter] at hfineQ hfineR
  obtain ⟨hfineQ, _⟩ := hfineQ
  obtain ⟨hfineR, _⟩ := hfineR
  simp only [planeCBInteriorLeadingSignSet, Finset.mem_filter] at hfineQ hfineR
  obtain ⟨hqFiber, hqLe⟩ := hfineQ
  obtain ⟨hrFiber, hrLe⟩ := hfineR
  simp only [planeCBLeadingSignSet, Finset.mem_filter, Finset.mem_univ,
    true_and] at hqFiber hrFiber
  have hleastQ :=
    leastLeadingGeneratorIndex_first_forwardConjugatedRestriction
      X i j k hij hik hjk (generatorEnumeration X q) n fineQ hqLe
  have hleastR :=
    leastLeadingGeneratorIndex_first_forwardConjugatedRestriction
      X i j k hij hik hjk (generatorEnumeration X r) n fineR hrLe
  have hindexQ : leastLeadingGeneratorIndex X
      (firstCoefficientEigenvalue X i j k hij hik hjk (n + 1) coarseSign) =
      q.val := by
    rw [← hcoarseQ]
    exact hleastQ.trans hqFiber.2
  have hindexR : leastLeadingGeneratorIndex X
      (firstCoefficientEigenvalue X i j k hij hik hjk (n + 1) coarseSign) =
      r.val := by
    rw [← hcoarseR]
    exact hleastR.trans hrFiber.2
  apply hqr
  apply Fin.ext
  exact hindexQ.symm.trans hindexR

/-- Exact mass transport from one interior `A ∪ B` fiber into only its
concrete opposite-shear image set. -/
theorem sum_norm_planeABInteriorLeadingSignSet_sq_le_image
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (q : Fin (Fintype.card X))
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    ∑ fineSign ∈ planeABInteriorLeadingSignSet X i j k hij hik hjk n q,
        ‖planeComponent X i j k hij hik hjk (n + 2) rho fineSign z‖ ^ 2 ≤
      ∑ coarseSign ∈
          planeABOppositeInteriorImageSignSet X i j k hij hik hjk n q,
        ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign
          (rho (elementaryRoot j i hij.symm
            (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z)‖ ^ 2 := by
  let index := oppositeConjugatedPlaneSuccIndex X i j k hij hik hjk
    (generatorEnumeration X q) (n + 1)
  let image := planeABOppositeInteriorImageSignSet X i j k hij hik hjk n q
  have hmass :
      (∑ fineSign ∈ planeABInteriorLeadingSignSet X i j k hij hik hjk n q,
          ‖planeComponent X i j k hij hik hjk (n + 2) rho fineSign z‖ ^ 2) =
        ∑ fineSign ∈ planeABValidInteriorLeadingSignSet
            X i j k hij hik hjk n q,
          ‖planeComponent X i j k hij hik hjk (n + 2) rho fineSign z‖ ^ 2 := by
    classical
    rw [planeABValidInteriorLeadingSignSet]
    generalize planeABInteriorLeadingSignSet X i j k hij hik hjk n q = signs
    induction signs using Finset.induction_on with
    | empty => simp
    | @insert fineSign signs hnot ih =>
        by_cases hvalid : IsPlaneCharacterSign X i j k hij hik hjk (n + 2) fineSign
        · rw [Finset.filter_insert]
          simp [hnot, hvalid, ih]
        · have hzero := planeComponent_eq_zero_of_not_isPlaneCharacterSign
            X i j k hij hik hjk (n + 2) rho fineSign z hvalid
          rw [Finset.filter_insert]
          simp [hnot, hvalid, hzero, ih]
  have hsubset : planeABValidInteriorLeadingSignSet
        X i j k hij hik hjk n q ⊆
      fineRestrictionSignSet
        (Nat.card (Plane X i j k hij hik hjk (n + 2)))
        (Nat.card (Plane X i j k hij hik hjk (n + 1))) index image := by
    intro fineSign hmem
    simp only [fineRestrictionSignSet, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact Finset.mem_image.mpr ⟨fineSign, hmem, rfl⟩
  calc
    ∑ fineSign ∈ planeABInteriorLeadingSignSet X i j k hij hik hjk n q,
        ‖planeComponent X i j k hij hik hjk (n + 2) rho fineSign z‖ ^ 2 =
        ∑ fineSign ∈ planeABValidInteriorLeadingSignSet
            X i j k hij hik hjk n q,
          ‖planeComponent X i j k hij hik hjk (n + 2) rho fineSign z‖ ^ 2 :=
      hmass
    _ ≤
        ∑ fineSign ∈ fineRestrictionSignSet
          (Nat.card (Plane X i j k hij hik hjk (n + 2)))
          (Nat.card (Plane X i j k hij hik hjk (n + 1))) index image,
          ‖planeComponent X i j k hij hik hjk (n + 2) rho fineSign z‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun _ _ _ ↦ sq_nonneg _)
    _ = ∑ coarseSign ∈ image,
          ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign
            (rho (elementaryRoot j i hij.symm
              (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z)‖ ^ 2 :=
      sum_norm_oppositeConjugatedRestriction_sq X i j k hij hik hjk
        (generatorEnumeration X q) (n + 1) rho image z

/-- Exact mass transport from one interior `C ∪ B` fiber into only its
concrete forward-shear image set. -/
theorem sum_norm_planeCBInteriorLeadingSignSet_sq_le_image
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (q : Fin (Fintype.card X))
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    ∑ fineSign ∈ planeCBInteriorLeadingSignSet X i j k hij hik hjk n q,
        ‖planeComponent X i j k hij hik hjk (n + 2) rho fineSign z‖ ^ 2 ≤
      ∑ coarseSign ∈
          planeCBForwardInteriorImageSignSet X i j k hij hik hjk n q,
        ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign
          (rho (elementaryRoot i j hij
            (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z)‖ ^ 2 := by
  let index := forwardConjugatedPlaneSuccIndex X i j k hij hik hjk
    (generatorEnumeration X q) (n + 1)
  let image := planeCBForwardInteriorImageSignSet X i j k hij hik hjk n q
  have hmass :
      (∑ fineSign ∈ planeCBInteriorLeadingSignSet X i j k hij hik hjk n q,
          ‖planeComponent X i j k hij hik hjk (n + 2) rho fineSign z‖ ^ 2) =
        ∑ fineSign ∈ planeCBValidInteriorLeadingSignSet
            X i j k hij hik hjk n q,
          ‖planeComponent X i j k hij hik hjk (n + 2) rho fineSign z‖ ^ 2 := by
    classical
    rw [planeCBValidInteriorLeadingSignSet]
    generalize planeCBInteriorLeadingSignSet X i j k hij hik hjk n q = signs
    induction signs using Finset.induction_on with
    | empty => simp
    | @insert fineSign signs hnot ih =>
        by_cases hvalid : IsPlaneCharacterSign X i j k hij hik hjk (n + 2) fineSign
        · rw [Finset.filter_insert]
          simp [hnot, hvalid, ih]
        · have hzero := planeComponent_eq_zero_of_not_isPlaneCharacterSign
            X i j k hij hik hjk (n + 2) rho fineSign z hvalid
          rw [Finset.filter_insert]
          simp [hnot, hvalid, hzero, ih]
  have hsubset : planeCBValidInteriorLeadingSignSet
        X i j k hij hik hjk n q ⊆
      fineRestrictionSignSet
        (Nat.card (Plane X i j k hij hik hjk (n + 2)))
        (Nat.card (Plane X i j k hij hik hjk (n + 1))) index image := by
    intro fineSign hmem
    simp only [fineRestrictionSignSet, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact Finset.mem_image.mpr ⟨fineSign, hmem, rfl⟩
  calc
    ∑ fineSign ∈ planeCBInteriorLeadingSignSet X i j k hij hik hjk n q,
        ‖planeComponent X i j k hij hik hjk (n + 2) rho fineSign z‖ ^ 2 =
        ∑ fineSign ∈ planeCBValidInteriorLeadingSignSet
            X i j k hij hik hjk n q,
          ‖planeComponent X i j k hij hik hjk (n + 2) rho fineSign z‖ ^ 2 :=
      hmass
    _ ≤
        ∑ fineSign ∈ fineRestrictionSignSet
          (Nat.card (Plane X i j k hij hik hjk (n + 2)))
          (Nat.card (Plane X i j k hij hik hjk (n + 1))) index image,
          ‖planeComponent X i j k hij hik hjk (n + 2) rho fineSign z‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun _ _ _ ↦ sq_nonneg _)
    _ = ∑ coarseSign ∈ image,
          ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign
            (rho (elementaryRoot i j hij
              (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z)‖ ^ 2 :=
      sum_norm_forwardConjugatedRestriction_sq X i j k hij hik hjk
        (generatorEnumeration X q) (n + 1) rho image z

/-- Algebraic character validity is sufficient for the concrete opposite
conjugation to carry an `A ∪ B` leading fiber into `C ∪ D`. -/
theorem planeCharacterRegion_oppositeConjugatedRestriction_eq_C_or_D_of_valid
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (q : Fin (Fintype.card X))
    (fineSign : Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool)
    (hvalid : IsPlaneCharacterSign X i j k hij hik hjk (n + 1) fineSign)
    (hsign : fineSign ∈ planeABLeadingSignSet X i j k hij hik hjk n q) :
    planeCharacterRegion X i j k hij hik hjk n
        (fun r ↦ fineSign (oppositeConjugatedPlaneSuccIndex X i j k hij hik hjk
          (generatorEnumeration X q) n r)) = .C ∨
      planeCharacterRegion X i j k hij hik hjk n
        (fun r ↦ fineSign (oppositeConjugatedPlaneSuccIndex X i j k hij hik hjk
          (generatorEnumeration X q) n r)) = .D := by
  have hfirst : firstCoefficientEigenvalue X i j k hij hik hjk n
      (fun r ↦ fineSign (oppositeConjugatedPlaneSuccIndex X i j k hij hik hjk
        (generatorEnumeration X q) n r)) =
      oppositeShearedFirstCharacter X
        (firstCoefficientEigenvalue X i j k hij hik hjk (n + 1) fineSign)
        (secondCoefficientEigenvalue X i j k hij hik hjk (n + 1) fineSign)
        (generatorEnumeration X q) := by
    funext a
    exact firstCoefficientEigenvalue_oppositeConjugatedRestriction_of_valid
      X i j k hij hik hjk (generatorEnumeration X q) n fineSign hvalid a
  have hsecond : secondCoefficientEigenvalue X i j k hij hik hjk n
      (fun r ↦ fineSign (oppositeConjugatedPlaneSuccIndex X i j k hij hik hjk
        (generatorEnumeration X q) n r)) =
      oppositeShearedSecondCharacter X
        (secondCoefficientEigenvalue X i j k hij hik hjk (n + 1) fineSign) := by
    funext b
    exact secondCoefficientEigenvalue_oppositeConjugatedRestriction
      X i j k hij hik hjk (generatorEnumeration X q) n fineSign b
  unfold planeCharacterRegion
  rw [hfirst, hsecond]
  exact planeABLeadingSignSet_region_transport X i j k hij hik hjk n q
    fineSign hsign

/-- The exact concrete opposite conjugation carries every nonzero fine
component in an `A ∪ B` leading fiber to a coarse character in `C ∪ D`.
This closes the bridge from the matrix conjugation to the valuation transport
statement. -/
theorem planeCharacterRegion_oppositeConjugatedRestriction_eq_C_or_D
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (q : Fin (Fintype.card X))
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (fineSign : Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool)
    (z : E)
    (hv : planeComponent X i j k hij hik hjk (n + 1) rho fineSign z ≠ 0)
    (hsign : fineSign ∈ planeABLeadingSignSet X i j k hij hik hjk n q) :
    planeCharacterRegion X i j k hij hik hjk n
        (fun r ↦ fineSign (oppositeConjugatedPlaneSuccIndex X i j k hij hik hjk
          (generatorEnumeration X q) n r)) = .C ∨
      planeCharacterRegion X i j k hij hik hjk n
        (fun r ↦ fineSign (oppositeConjugatedPlaneSuccIndex X i j k hij hik hjk
          (generatorEnumeration X q) n r)) = .D := by
  exact planeCharacterRegion_oppositeConjugatedRestriction_eq_C_or_D_of_valid
    X i j k hij hik hjk n q fineSign
      (isPlaneCharacterSign_of_component_ne_zero
        X i j k hij hik hjk (n + 1) rho fineSign z hv) hsign

/-- Algebraic character validity is sufficient for the forward concrete
conjugation to carry a `C ∪ B` leading fiber into `A ∪ D`. -/
theorem planeCharacterRegion_forwardConjugatedRestriction_eq_A_or_D_of_valid
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (q : Fin (Fintype.card X))
    (fineSign : Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool)
    (hvalid : IsPlaneCharacterSign X i j k hij hik hjk (n + 1) fineSign)
    (hsign : fineSign ∈ planeCBLeadingSignSet X i j k hij hik hjk n q) :
    planeCharacterRegion X i j k hij hik hjk n
        (fun r ↦ fineSign (forwardConjugatedPlaneSuccIndex X i j k hij hik hjk
          (generatorEnumeration X q) n r)) = .A ∨
      planeCharacterRegion X i j k hij hik hjk n
        (fun r ↦ fineSign (forwardConjugatedPlaneSuccIndex X i j k hij hik hjk
          (generatorEnumeration X q) n r)) = .D := by
  have hfirst : firstCoefficientEigenvalue X i j k hij hik hjk n
      (fun r ↦ fineSign (forwardConjugatedPlaneSuccIndex X i j k hij hik hjk
        (generatorEnumeration X q) n r)) =
      forwardShearedFirstCharacter X
        (firstCoefficientEigenvalue X i j k hij hik hjk (n + 1) fineSign) := by
    funext a
    exact firstCoefficientEigenvalue_forwardConjugatedRestriction
      X i j k hij hik hjk (generatorEnumeration X q) n fineSign a
  have hsecond : secondCoefficientEigenvalue X i j k hij hik hjk n
      (fun r ↦ fineSign (forwardConjugatedPlaneSuccIndex X i j k hij hik hjk
        (generatorEnumeration X q) n r)) =
      forwardShearedSecondCharacter X
        (firstCoefficientEigenvalue X i j k hij hik hjk (n + 1) fineSign)
        (secondCoefficientEigenvalue X i j k hij hik hjk (n + 1) fineSign)
        (generatorEnumeration X q) := by
    funext b
    exact secondCoefficientEigenvalue_forwardConjugatedRestriction_of_valid
      X i j k hij hik hjk (generatorEnumeration X q) n fineSign hvalid b
  unfold planeCharacterRegion
  rw [hfirst, hsecond]
  exact planeCBLeadingSignSet_region_transport X i j k hij hik hjk n q
    fineSign hsign

/-- The symmetric concrete forward conjugation sends every nonzero fine
component in a `C ∪ B` leading fiber to `A ∪ D` at the coarse stage. -/
theorem planeCharacterRegion_forwardConjugatedRestriction_eq_A_or_D
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (q : Fin (Fintype.card X))
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (fineSign : Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool)
    (z : E)
    (hv : planeComponent X i j k hij hik hjk (n + 1) rho fineSign z ≠ 0)
    (hsign : fineSign ∈ planeCBLeadingSignSet X i j k hij hik hjk n q) :
    planeCharacterRegion X i j k hij hik hjk n
        (fun r ↦ fineSign (forwardConjugatedPlaneSuccIndex X i j k hij hik hjk
          (generatorEnumeration X q) n r)) = .A ∨
      planeCharacterRegion X i j k hij hik hjk n
        (fun r ↦ fineSign (forwardConjugatedPlaneSuccIndex X i j k hij hik hjk
          (generatorEnumeration X q) n r)) = .D := by
  exact planeCharacterRegion_forwardConjugatedRestriction_eq_A_or_D_of_valid
    X i j k hij hik hjk n q fineSign
      (isPlaneCharacterSign_of_component_ne_zero
        X i j k hij hik hjk (n + 1) rho fineSign z hv) hsign

/-- Every valid opposite-shear image below the top-degree boundary lies in
the coarse `C ∪ D` region. -/
theorem planeABOppositeInteriorImageSignSet_subset_C_union_D
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (q : Fin (Fintype.card X)) :
    planeABOppositeInteriorImageSignSet X i j k hij hik hjk n q ⊆
      planeRegionSignSet X i j k hij hik hjk (n + 1) .C ∪
        planeRegionSignSet X i j k hij hik hjk (n + 1) .D := by
  classical
  intro coarseSign hcoarse
  obtain ⟨fineSign, hfine, rfl⟩ := Finset.mem_image.mp hcoarse
  obtain ⟨hinterior, hvalid⟩ := Finset.mem_filter.mp hfine
  obtain ⟨hleading, _⟩ := Finset.mem_filter.mp hinterior
  have hregion :=
    planeCharacterRegion_oppositeConjugatedRestriction_eq_C_or_D_of_valid
      X i j k hij hik hjk (n + 1) q fineSign hvalid hleading
  simpa [planeRegionSignSet] using hregion

/-- Every valid forward-shear image below the top-degree boundary lies in
the coarse `A ∪ D` region. -/
theorem planeCBForwardInteriorImageSignSet_subset_A_union_D
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (q : Fin (Fintype.card X)) :
    planeCBForwardInteriorImageSignSet X i j k hij hik hjk n q ⊆
      planeRegionSignSet X i j k hij hik hjk (n + 1) .A ∪
        planeRegionSignSet X i j k hij hik hjk (n + 1) .D := by
  classical
  intro coarseSign hcoarse
  obtain ⟨fineSign, hfine, rfl⟩ := Finset.mem_image.mp hcoarse
  obtain ⟨hinterior, hvalid⟩ := Finset.mem_filter.mp hfine
  obtain ⟨hleading, _⟩ := Finset.mem_filter.mp hinterior
  have hregion :=
    planeCharacterRegion_forwardConjugatedRestriction_eq_A_or_D_of_valid
      X i j k hij hik hjk (n + 1) q fineSign hvalid hleading
  simpa [planeRegionSignSet] using hregion

/-- Because the valid opposite-shear images are pairwise disjoint, their
total nonnegative weight is bounded by the weight of the single `C ∪ D`
target region. -/
theorem sum_planeABOppositeInteriorImageSignSet_le_C_union_D
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (f : (Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool) → ℝ)
    (hf : ∀ sign, 0 ≤ f sign) :
    (∑ q : Fin (Fintype.card X),
        ∑ sign ∈ planeABOppositeInteriorImageSignSet
            X i j k hij hik hjk n q,
          f sign) ≤
      ∑ sign ∈ (planeRegionSignSet X i j k hij hik hjk (n + 1) .C ∪
          planeRegionSignSet X i j k hij hik hjk (n + 1) .D),
        f sign := by
  classical
  have hpair :
      ((Finset.univ : Finset (Fin (Fintype.card X))) : Set _).PairwiseDisjoint
        (planeABOppositeInteriorImageSignSet X i j k hij hik hjk n) := by
    intro q _ r _ hqr
    exact planeABOppositeInteriorImageSignSet_pairwise_disjoint
      X i j k hij hik hjk n hqr
  rw [← Finset.sum_biUnion hpair]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro sign hsign
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hsign
    obtain ⟨q, hq⟩ := hsign
    exact planeABOppositeInteriorImageSignSet_subset_C_union_D
      X i j k hij hik hjk n q hq
  · intro sign _ _
    exact hf sign

/-- The symmetric disjoint-image estimate into the single `A ∪ D` target
region. -/
theorem sum_planeCBForwardInteriorImageSignSet_le_A_union_D
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (f : (Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool) → ℝ)
    (hf : ∀ sign, 0 ≤ f sign) :
    (∑ q : Fin (Fintype.card X),
        ∑ sign ∈ planeCBForwardInteriorImageSignSet
            X i j k hij hik hjk n q,
          f sign) ≤
      ∑ sign ∈ (planeRegionSignSet X i j k hij hik hjk (n + 1) .A ∪
          planeRegionSignSet X i j k hij hik hjk (n + 1) .D),
        f sign := by
  classical
  have hpair :
      ((Finset.univ : Finset (Fin (Fintype.card X))) : Set _).PairwiseDisjoint
        (planeCBForwardInteriorImageSignSet X i j k hij hik hjk n) := by
    intro q _ r _ hqr
    exact planeCBForwardInteriorImageSignSet_pairwise_disjoint
      X i j k hij hik hjk n hqr
  rw [← Finset.sum_biUnion hpair]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro sign hsign
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hsign
    obtain ⟨q, hq⟩ := hsign
    exact planeCBForwardInteriorImageSignSet_subset_A_union_D
      X i j k hij hik hjk n q hq
  · intro sign _ _
    exact hf sign

/-- The full below-boundary `A ∪ B` mass is charged injectively to one copy
of the `C ∪ D` mass, up to the sum of the concrete adjacent-generator
displacements.  In particular, the target mass has no generator-cardinality
factor. -/
theorem sum_norm_planeABInteriorLeadingSignSet_sq_le_target_add_error
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    (∑ q : Fin (Fintype.card X),
        ∑ fineSign ∈ planeABInteriorLeadingSignSet
            X i j k hij hik hjk n q,
          ‖planeComponent X i j k hij hik hjk (n + 2) rho fineSign z‖ ^ 2) ≤
      (∑ coarseSign ∈
          (planeRegionSignSet X i j k hij hik hjk (n + 1) .C ∪
            planeRegionSignSet X i j k hij hik hjk (n + 1) .D),
          ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign z‖ ^ 2) +
        ∑ q : Fin (Fintype.card X),
          2 * ‖z‖ *
            ‖rho (elementaryRoot j i hij.symm
              (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z - z‖ := by
  classical
  let moved : Fin (Fintype.card X) → E := fun q ↦
    rho (elementaryRoot j i hij.symm
      (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z
  have hfiber :
      (∑ q : Fin (Fintype.card X),
          ∑ fineSign ∈ planeABInteriorLeadingSignSet
              X i j k hij hik hjk n q,
            ‖planeComponent X i j k hij hik hjk (n + 2) rho fineSign z‖ ^ 2) ≤
        ∑ q : Fin (Fintype.card X),
          ∑ coarseSign ∈ planeABOppositeInteriorImageSignSet
              X i j k hij hik hjk n q,
            ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign
              (moved q)‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro q _
    exact sum_norm_planeABInteriorLeadingSignSet_sq_le_image
      X i j k hij hik hjk n q rho z
  have hmoved :
      (∑ q : Fin (Fintype.card X),
          ∑ coarseSign ∈ planeABOppositeInteriorImageSignSet
              X i j k hij hik hjk n q,
            ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign
              (moved q)‖ ^ 2) ≤
        ∑ q : Fin (Fintype.card X),
          ((∑ coarseSign ∈ planeABOppositeInteriorImageSignSet
                X i j k hij hik hjk n q,
              ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign z‖ ^ 2) +
            2 * ‖z‖ * ‖moved q - z‖) := by
    apply Finset.sum_le_sum
    intro q _
    have hvariation := abs_sum_norm_planeComponent_sq_sub_le
      X i j k hij hik hjk (n + 1) rho
      (planeABOppositeInteriorImageSignSet X i j k hij hik hjk n q)
      (moved q) z
    have hdiff :
        (∑ coarseSign ∈ planeABOppositeInteriorImageSignSet
              X i j k hij hik hjk n q,
            ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign
              (moved q)‖ ^ 2) -
          (∑ coarseSign ∈ planeABOppositeInteriorImageSignSet
              X i j k hij hik hjk n q,
            ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign z‖ ^ 2) ≤
        (‖moved q‖ + ‖z‖) * ‖moved q - z‖ :=
      (le_abs_self _).trans hvariation
    rw [sub_le_iff_le_add] at hdiff
    have hnorm : ‖moved q‖ = ‖z‖ := by
      exact (rho (elementaryRoot j i hij.symm
        (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q)))).norm_map z
    calc
      _ ≤ (‖moved q‖ + ‖z‖) * ‖moved q - z‖ +
          ∑ coarseSign ∈ planeABOppositeInteriorImageSignSet
              X i j k hij hik hjk n q,
            ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign z‖ ^ 2 :=
        hdiff
      _ = (∑ coarseSign ∈ planeABOppositeInteriorImageSignSet
              X i j k hij hik hjk n q,
            ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign z‖ ^ 2) +
          2 * ‖z‖ * ‖moved q - z‖ := by
        rw [hnorm]
        ring
  have htarget :
      (∑ q : Fin (Fintype.card X),
          ∑ coarseSign ∈ planeABOppositeInteriorImageSignSet
              X i j k hij hik hjk n q,
            ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign z‖ ^ 2) ≤
        ∑ coarseSign ∈
            (planeRegionSignSet X i j k hij hik hjk (n + 1) .C ∪
              planeRegionSignSet X i j k hij hik hjk (n + 1) .D),
          ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign z‖ ^ 2 :=
    sum_planeABOppositeInteriorImageSignSet_le_C_union_D
      X i j k hij hik hjk n
      (fun coarseSign ↦
        ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign z‖ ^ 2)
      (fun _ ↦ sq_nonneg _)
  calc
    _ ≤ ∑ q : Fin (Fintype.card X),
          ∑ coarseSign ∈ planeABOppositeInteriorImageSignSet
              X i j k hij hik hjk n q,
            ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign
              (moved q)‖ ^ 2 := hfiber
    _ ≤ ∑ q : Fin (Fintype.card X),
          ((∑ coarseSign ∈ planeABOppositeInteriorImageSignSet
                X i j k hij hik hjk n q,
              ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign z‖ ^ 2) +
            2 * ‖z‖ * ‖moved q - z‖) := hmoved
    _ = (∑ q : Fin (Fintype.card X),
          ∑ coarseSign ∈ planeABOppositeInteriorImageSignSet
              X i j k hij hik hjk n q,
            ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign z‖ ^ 2) +
        ∑ q : Fin (Fintype.card X), 2 * ‖z‖ * ‖moved q - z‖ := by
      rw [Finset.sum_add_distrib]
    _ ≤ (∑ coarseSign ∈
          (planeRegionSignSet X i j k hij hik hjk (n + 1) .C ∪
            planeRegionSignSet X i j k hij hik hjk (n + 1) .D),
          ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign z‖ ^ 2) +
        ∑ q : Fin (Fintype.card X), 2 * ‖z‖ * ‖moved q - z‖ :=
      add_le_add htarget (le_refl _)
    _ = _ := by rfl

/-- The symmetric full below-boundary `C ∪ B` estimate charges its mass
injectively to one copy of `A ∪ D`, again with no cardinality factor on the
target mass. -/
theorem sum_norm_planeCBInteriorLeadingSignSet_sq_le_target_add_error
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    (∑ q : Fin (Fintype.card X),
        ∑ fineSign ∈ planeCBInteriorLeadingSignSet
            X i j k hij hik hjk n q,
          ‖planeComponent X i j k hij hik hjk (n + 2) rho fineSign z‖ ^ 2) ≤
      (∑ coarseSign ∈
          (planeRegionSignSet X i j k hij hik hjk (n + 1) .A ∪
            planeRegionSignSet X i j k hij hik hjk (n + 1) .D),
          ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign z‖ ^ 2) +
        ∑ q : Fin (Fintype.card X),
          2 * ‖z‖ *
            ‖rho (elementaryRoot i j hij
              (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z - z‖ := by
  classical
  let moved : Fin (Fintype.card X) → E := fun q ↦
    rho (elementaryRoot i j hij
      (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z
  have hfiber :
      (∑ q : Fin (Fintype.card X),
          ∑ fineSign ∈ planeCBInteriorLeadingSignSet
              X i j k hij hik hjk n q,
            ‖planeComponent X i j k hij hik hjk (n + 2) rho fineSign z‖ ^ 2) ≤
        ∑ q : Fin (Fintype.card X),
          ∑ coarseSign ∈ planeCBForwardInteriorImageSignSet
              X i j k hij hik hjk n q,
            ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign
              (moved q)‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro q _
    exact sum_norm_planeCBInteriorLeadingSignSet_sq_le_image
      X i j k hij hik hjk n q rho z
  have hmoved :
      (∑ q : Fin (Fintype.card X),
          ∑ coarseSign ∈ planeCBForwardInteriorImageSignSet
              X i j k hij hik hjk n q,
            ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign
              (moved q)‖ ^ 2) ≤
        ∑ q : Fin (Fintype.card X),
          ((∑ coarseSign ∈ planeCBForwardInteriorImageSignSet
                X i j k hij hik hjk n q,
              ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign z‖ ^ 2) +
            2 * ‖z‖ * ‖moved q - z‖) := by
    apply Finset.sum_le_sum
    intro q _
    have hvariation := abs_sum_norm_planeComponent_sq_sub_le
      X i j k hij hik hjk (n + 1) rho
      (planeCBForwardInteriorImageSignSet X i j k hij hik hjk n q)
      (moved q) z
    have hdiff :
        (∑ coarseSign ∈ planeCBForwardInteriorImageSignSet
              X i j k hij hik hjk n q,
            ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign
              (moved q)‖ ^ 2) -
          (∑ coarseSign ∈ planeCBForwardInteriorImageSignSet
              X i j k hij hik hjk n q,
            ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign z‖ ^ 2) ≤
        (‖moved q‖ + ‖z‖) * ‖moved q - z‖ :=
      (le_abs_self _).trans hvariation
    rw [sub_le_iff_le_add] at hdiff
    have hnorm : ‖moved q‖ = ‖z‖ := by
      exact (rho (elementaryRoot i j hij
        (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q)))).norm_map z
    calc
      _ ≤ (‖moved q‖ + ‖z‖) * ‖moved q - z‖ +
          ∑ coarseSign ∈ planeCBForwardInteriorImageSignSet
              X i j k hij hik hjk n q,
            ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign z‖ ^ 2 :=
        hdiff
      _ = (∑ coarseSign ∈ planeCBForwardInteriorImageSignSet
              X i j k hij hik hjk n q,
            ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign z‖ ^ 2) +
          2 * ‖z‖ * ‖moved q - z‖ := by
        rw [hnorm]
        ring
  have htarget :
      (∑ q : Fin (Fintype.card X),
          ∑ coarseSign ∈ planeCBForwardInteriorImageSignSet
              X i j k hij hik hjk n q,
            ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign z‖ ^ 2) ≤
        ∑ coarseSign ∈
            (planeRegionSignSet X i j k hij hik hjk (n + 1) .A ∪
              planeRegionSignSet X i j k hij hik hjk (n + 1) .D),
          ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign z‖ ^ 2 :=
    sum_planeCBForwardInteriorImageSignSet_le_A_union_D
      X i j k hij hik hjk n
      (fun coarseSign ↦
        ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign z‖ ^ 2)
      (fun _ ↦ sq_nonneg _)
  calc
    _ ≤ ∑ q : Fin (Fintype.card X),
          ∑ coarseSign ∈ planeCBForwardInteriorImageSignSet
              X i j k hij hik hjk n q,
            ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign
              (moved q)‖ ^ 2 := hfiber
    _ ≤ ∑ q : Fin (Fintype.card X),
          ((∑ coarseSign ∈ planeCBForwardInteriorImageSignSet
                X i j k hij hik hjk n q,
              ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign z‖ ^ 2) +
            2 * ‖z‖ * ‖moved q - z‖) := hmoved
    _ = (∑ q : Fin (Fintype.card X),
          ∑ coarseSign ∈ planeCBForwardInteriorImageSignSet
              X i j k hij hik hjk n q,
            ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign z‖ ^ 2) +
        ∑ q : Fin (Fintype.card X), 2 * ‖z‖ * ‖moved q - z‖ := by
      rw [Finset.sum_add_distrib]
    _ ≤ (∑ coarseSign ∈
          (planeRegionSignSet X i j k hij hik hjk (n + 1) .A ∪
            planeRegionSignSet X i j k hij hik hjk (n + 1) .D),
          ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign z‖ ^ 2) +
        ∑ q : Fin (Fintype.card X), 2 * ‖z‖ * ‖moved q - z‖ :=
      add_le_add htarget (le_refl _)
    _ = _ := by rfl

/-- The omitted part of an `A ∪ B` leading fiber consists exactly of signs
whose second character is first detected in the fine stage's top degree. -/
noncomputable def planeABTopBoundaryLeadingSignSet
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (q : Fin (Fintype.card X)) :
    Finset (Fin (Nat.card (Plane X i j k hij hik hjk (n + 2))) → Bool) :=
  (planeABLeadingSignSet X i j k hij hik hjk (n + 1) q).filter
    fun sign ↦
      secondCoefficientValuation X i j k hij hik hjk (n + 2) sign = n + 2

/-- Symmetrically, the omitted `C ∪ B` part is the top-degree first-character
layer. -/
noncomputable def planeCBTopBoundaryLeadingSignSet
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (q : Fin (Fintype.card X)) :
    Finset (Fin (Nat.card (Plane X i j k hij hik hjk (n + 2))) → Bool) :=
  (planeCBLeadingSignSet X i j k hij hik hjk (n + 1) q).filter
    fun sign ↦
      firstCoefficientValuation X i j k hij hik hjk (n + 2) sign = n + 2

theorem secondCoefficientValuation_le_top_of_mem_planeABLeadingSignSet
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (q : Fin (Fintype.card X))
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk (n + 2))) → Bool)
    (hsign : sign ∈ planeABLeadingSignSet X i j k hij hik hjk (n + 1) q) :
    secondCoefficientValuation X i j k hij hik hjk (n + 2) sign ≤ n + 2 := by
  simp only [planeABLeadingSignSet, Finset.mem_filter, Finset.mem_univ,
    true_and] at hsign
  have hfirstBound := characterValuation_le_succ X
    (firstCoefficientEigenvalue X i j k hij hik hjk (n + 2) sign)
  have hsecondBound := characterValuation_le_succ X
    (secondCoefficientEigenvalue X i j k hij hik hjk (n + 2) sign)
  change firstCoefficientValuation X i j k hij hik hjk (n + 2) sign ≤
    n + 3 at hfirstBound
  change secondCoefficientValuation X i j k hij hik hjk (n + 2) sign ≤
    n + 3 at hsecondBound
  rcases hsign.1 with hA | hB
  · have hdata := characterPairRegion_A_data X (n + 2)
      (firstCoefficientEigenvalue X i j k hij hik hjk (n + 2) sign)
      (secondCoefficientEigenvalue X i j k hij hik hjk (n + 2) sign) hA
    exact Nat.le_of_lt_succ (hdata.2.2.2.trans_le hfirstBound)
  · have hdata := characterPairRegion_B_data X (n + 2)
      (firstCoefficientEigenvalue X i j k hij hik hjk (n + 2) sign)
      (secondCoefficientEigenvalue X i j k hij hik hjk (n + 2) sign) hB
    by_contra hnot
    have hsecond : secondCoefficientValuation X i j k hij hik hjk (n + 2) sign =
        n + 3 := by omega
    have hfirst : firstCoefficientValuation X i j k hij hik hjk (n + 2) sign =
        n + 3 := hdata.2.2.2.trans hsecond
    exact hdata.1 ⟨hfirst, hsecond⟩

theorem firstCoefficientValuation_le_top_of_mem_planeCBLeadingSignSet
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (q : Fin (Fintype.card X))
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk (n + 2))) → Bool)
    (hsign : sign ∈ planeCBLeadingSignSet X i j k hij hik hjk (n + 1) q) :
    firstCoefficientValuation X i j k hij hik hjk (n + 2) sign ≤ n + 2 := by
  simp only [planeCBLeadingSignSet, Finset.mem_filter, Finset.mem_univ,
    true_and] at hsign
  have hfirstBound := characterValuation_le_succ X
    (firstCoefficientEigenvalue X i j k hij hik hjk (n + 2) sign)
  have hsecondBound := characterValuation_le_succ X
    (secondCoefficientEigenvalue X i j k hij hik hjk (n + 2) sign)
  change firstCoefficientValuation X i j k hij hik hjk (n + 2) sign ≤
    n + 3 at hfirstBound
  change secondCoefficientValuation X i j k hij hik hjk (n + 2) sign ≤
    n + 3 at hsecondBound
  rcases hsign.1 with hC | hB
  · have hdata := characterPairRegion_C_data X (n + 2)
      (firstCoefficientEigenvalue X i j k hij hik hjk (n + 2) sign)
      (secondCoefficientEigenvalue X i j k hij hik hjk (n + 2) sign) hC
    exact Nat.le_of_lt_succ (hdata.2.2.2.trans_le hsecondBound)
  · have hdata := characterPairRegion_B_data X (n + 2)
      (firstCoefficientEigenvalue X i j k hij hik hjk (n + 2) sign)
      (secondCoefficientEigenvalue X i j k hij hik hjk (n + 2) sign) hB
    by_contra hnot
    have hfirst : firstCoefficientValuation X i j k hij hik hjk (n + 2) sign =
        n + 3 := by omega
    have hsecond : secondCoefficientValuation X i j k hij hik hjk (n + 2) sign =
        n + 3 := hdata.2.2.2.symm.trans hfirst
    exact hdata.1 ⟨hfirst, hsecond⟩

theorem planeABLeadingSignSet_eq_interior_union_topBoundary
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (q : Fin (Fintype.card X)) :
    planeABLeadingSignSet X i j k hij hik hjk (n + 1) q =
      planeABInteriorLeadingSignSet X i j k hij hik hjk n q ∪
        planeABTopBoundaryLeadingSignSet X i j k hij hik hjk n q := by
  classical
  ext sign
  simp only [planeABInteriorLeadingSignSet,
    planeABTopBoundaryLeadingSignSet, Finset.mem_filter, Finset.mem_union]
  constructor
  · intro hsign
    have hbound := secondCoefficientValuation_le_top_of_mem_planeABLeadingSignSet
      X i j k hij hik hjk n q sign hsign
    by_cases hle : secondCoefficientValuation X i j k hij hik hjk (n + 2) sign ≤
        n + 1
    · exact Or.inl ⟨hsign, hle⟩
    · exact Or.inr ⟨hsign, by omega⟩
  · rintro (⟨hsign, _⟩ | ⟨hsign, _⟩) <;> exact hsign

theorem planeCBLeadingSignSet_eq_interior_union_topBoundary
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (q : Fin (Fintype.card X)) :
    planeCBLeadingSignSet X i j k hij hik hjk (n + 1) q =
      planeCBInteriorLeadingSignSet X i j k hij hik hjk n q ∪
        planeCBTopBoundaryLeadingSignSet X i j k hij hik hjk n q := by
  classical
  ext sign
  simp only [planeCBInteriorLeadingSignSet,
    planeCBTopBoundaryLeadingSignSet, Finset.mem_filter, Finset.mem_union]
  constructor
  · intro hsign
    have hbound := firstCoefficientValuation_le_top_of_mem_planeCBLeadingSignSet
      X i j k hij hik hjk n q sign hsign
    by_cases hle : firstCoefficientValuation X i j k hij hik hjk (n + 2) sign ≤
        n + 1
    · exact Or.inl ⟨hsign, hle⟩
    · exact Or.inr ⟨hsign, by omega⟩
  · rintro (⟨hsign, _⟩ | ⟨hsign, _⟩) <;> exact hsign

theorem planeABInteriorLeadingSignSet_disjoint_topBoundary
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (q : Fin (Fintype.card X)) :
    Disjoint (planeABInteriorLeadingSignSet X i j k hij hik hjk n q)
      (planeABTopBoundaryLeadingSignSet X i j k hij hik hjk n q) := by
  classical
  rw [Finset.disjoint_left]
  intro sign hinterior htop
  simp only [planeABInteriorLeadingSignSet,
    planeABTopBoundaryLeadingSignSet, Finset.mem_filter] at hinterior htop
  omega

theorem planeCBInteriorLeadingSignSet_disjoint_topBoundary
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (q : Fin (Fintype.card X)) :
    Disjoint (planeCBInteriorLeadingSignSet X i j k hij hik hjk n q)
      (planeCBTopBoundaryLeadingSignSet X i j k hij hik hjk n q) := by
  classical
  rw [Finset.disjoint_left]
  intro sign hinterior htop
  simp only [planeCBInteriorLeadingSignSet,
    planeCBTopBoundaryLeadingSignSet, Finset.mem_filter] at hinterior htop
  omega

theorem planeABTopBoundaryLeadingSignSet_pairwise_disjoint
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) :
    Pairwise (fun q r : Fin (Fintype.card X) ↦
      Disjoint (planeABTopBoundaryLeadingSignSet X i j k hij hik hjk n q)
        (planeABTopBoundaryLeadingSignSet X i j k hij hik hjk n r)) := by
  intro q r hqr
  exact (planeABLeadingSignSet_pairwise_disjoint
    X i j k hij hik hjk (n + 1) hqr).mono
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)

theorem planeCBTopBoundaryLeadingSignSet_pairwise_disjoint
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) :
    Pairwise (fun q r : Fin (Fintype.card X) ↦
      Disjoint (planeCBTopBoundaryLeadingSignSet X i j k hij hik hjk n q)
        (planeCBTopBoundaryLeadingSignSet X i j k hij hik hjk n r)) := by
  intro q r hqr
  exact (planeCBLeadingSignSet_pairwise_disjoint
    X i j k hij hik hjk (n + 1) hqr).mono
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)

theorem sum_planeABLeadingSignSet_eq_interior_add_topBoundary
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (f : (Fin (Nat.card (Plane X i j k hij hik hjk (n + 2))) → Bool) → ℝ) :
    (∑ q : Fin (Fintype.card X),
        ∑ sign ∈ planeABLeadingSignSet X i j k hij hik hjk (n + 1) q,
          f sign) =
      (∑ q : Fin (Fintype.card X),
        ∑ sign ∈ planeABInteriorLeadingSignSet X i j k hij hik hjk n q,
          f sign) +
      ∑ q : Fin (Fintype.card X),
        ∑ sign ∈ planeABTopBoundaryLeadingSignSet X i j k hij hik hjk n q,
          f sign := by
  classical
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  rw [planeABLeadingSignSet_eq_interior_union_topBoundary]
  exact Finset.sum_union
    (planeABInteriorLeadingSignSet_disjoint_topBoundary
      X i j k hij hik hjk n q)

theorem sum_planeCBLeadingSignSet_eq_interior_add_topBoundary
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (f : (Fin (Nat.card (Plane X i j k hij hik hjk (n + 2))) → Bool) → ℝ) :
    (∑ q : Fin (Fintype.card X),
        ∑ sign ∈ planeCBLeadingSignSet X i j k hij hik hjk (n + 1) q,
          f sign) =
      (∑ q : Fin (Fintype.card X),
        ∑ sign ∈ planeCBInteriorLeadingSignSet X i j k hij hik hjk n q,
          f sign) +
      ∑ q : Fin (Fintype.card X),
        ∑ sign ∈ planeCBTopBoundaryLeadingSignSet X i j k hij hik hjk n q,
          f sign := by
  classical
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  rw [planeCBLeadingSignSet_eq_interior_union_topBoundary]
  exact Finset.sum_union
    (planeCBInteriorLeadingSignSet_disjoint_topBoundary
      X i j k hij hik hjk n q)

theorem sum_norm_planeABTopBoundaryLeadingSignSet_sq_le
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    (∑ q : Fin (Fintype.card X),
        ∑ sign ∈ planeABTopBoundaryLeadingSignSet
            X i j k hij hik hjk n q,
          ‖planeComponent X i j k hij hik hjk (n + 2) rho sign z‖ ^ 2) ≤
      planeSecondTopBoundaryMass X i j k hij hik hjk rho z (n + 2) := by
  classical
  have hpair :
      ((Finset.univ : Finset (Fin (Fintype.card X))) : Set _).PairwiseDisjoint
        (planeABTopBoundaryLeadingSignSet X i j k hij hik hjk n) := by
    intro q _ r _ hqr
    exact planeABTopBoundaryLeadingSignSet_pairwise_disjoint
      X i j k hij hik hjk n hqr
  rw [← Finset.sum_biUnion hpair]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro sign hsign
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hsign
    obtain ⟨q, hq⟩ := hsign
    simp only [planeABTopBoundaryLeadingSignSet, Finset.mem_filter] at hq
    simpa [planeSecondTopBoundarySignSet] using hq.2
  · intro _ _ _
    exact sq_nonneg _

theorem sum_norm_planeCBTopBoundaryLeadingSignSet_sq_le
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    (∑ q : Fin (Fintype.card X),
        ∑ sign ∈ planeCBTopBoundaryLeadingSignSet
            X i j k hij hik hjk n q,
          ‖planeComponent X i j k hij hik hjk (n + 2) rho sign z‖ ^ 2) ≤
      planeFirstTopBoundaryMass X i j k hij hik hjk rho z (n + 2) := by
  classical
  have hpair :
      ((Finset.univ : Finset (Fin (Fintype.card X))) : Set _).PairwiseDisjoint
        (planeCBTopBoundaryLeadingSignSet X i j k hij hik hjk n) := by
    intro q _ r _ hqr
    exact planeCBTopBoundaryLeadingSignSet_pairwise_disjoint
      X i j k hij hik hjk n hqr
  rw [← Finset.sum_biUnion hpair]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro sign hsign
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hsign
    obtain ⟨q, hq⟩ := hsign
    simp only [planeCBTopBoundaryLeadingSignSet, Finset.mem_filter] at hq
    simpa [planeFirstTopBoundarySignSet] using hq.2
  · intro _ _ _
    exact sq_nonneg _

/-- Full finite-stage `A ∪ B` estimate: the only term not controlled by the
fixed adjacent generators is the explicit second-coordinate top-degree layer,
which tends to zero by the telescoping theorem above. -/
theorem sum_norm_planeABRegion_sq_le_target_add_error_add_boundary
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    (∑ sign ∈ (planeRegionSignSet X i j k hij hik hjk (n + 2) .A ∪
          planeRegionSignSet X i j k hij hik hjk (n + 2) .B),
        ‖planeComponent X i j k hij hik hjk (n + 2) rho sign z‖ ^ 2) ≤
      ((∑ sign ∈
          (planeRegionSignSet X i j k hij hik hjk (n + 1) .C ∪
            planeRegionSignSet X i j k hij hik hjk (n + 1) .D),
          ‖planeComponent X i j k hij hik hjk (n + 1) rho sign z‖ ^ 2) +
        ∑ q : Fin (Fintype.card X),
          2 * ‖z‖ *
            ‖rho (elementaryRoot j i hij.symm
              (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z - z‖) +
        planeSecondTopBoundaryMass X i j k hij hik hjk rho z (n + 2) := by
  classical
  let componentMass := fun sign :
      Fin (Nat.card (Plane X i j k hij hik hjk (n + 2))) → Bool ↦
    ‖planeComponent X i j k hij hik hjk (n + 2) rho sign z‖ ^ 2
  calc
    _ = ∑ q : Fin (Fintype.card X),
          ∑ sign ∈ planeABLeadingSignSet X i j k hij hik hjk (n + 1) q,
            componentMass sign :=
      sum_planeABLeadingSignSet X i j k hij hik hjk (n + 1) componentMass
    _ = (∑ q : Fin (Fintype.card X),
          ∑ sign ∈ planeABInteriorLeadingSignSet X i j k hij hik hjk n q,
            componentMass sign) +
        ∑ q : Fin (Fintype.card X),
          ∑ sign ∈ planeABTopBoundaryLeadingSignSet X i j k hij hik hjk n q,
            componentMass sign :=
      sum_planeABLeadingSignSet_eq_interior_add_topBoundary
        X i j k hij hik hjk n componentMass
    _ ≤ ((∑ sign ∈
            (planeRegionSignSet X i j k hij hik hjk (n + 1) .C ∪
              planeRegionSignSet X i j k hij hik hjk (n + 1) .D),
            ‖planeComponent X i j k hij hik hjk (n + 1) rho sign z‖ ^ 2) +
          ∑ q : Fin (Fintype.card X),
            2 * ‖z‖ *
              ‖rho (elementaryRoot j i hij.symm
                (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z - z‖) +
          planeSecondTopBoundaryMass X i j k hij hik hjk rho z (n + 2) :=
      add_le_add
        (sum_norm_planeABInteriorLeadingSignSet_sq_le_target_add_error
          X i j k hij hik hjk n rho z)
        (sum_norm_planeABTopBoundaryLeadingSignSet_sq_le
          X i j k hij hik hjk n rho z)

/-- Symmetric full `C ∪ B` estimate with its explicit first-coordinate
top-degree boundary. -/
theorem sum_norm_planeCBRegion_sq_le_target_add_error_add_boundary
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    (∑ sign ∈ (planeRegionSignSet X i j k hij hik hjk (n + 2) .C ∪
          planeRegionSignSet X i j k hij hik hjk (n + 2) .B),
        ‖planeComponent X i j k hij hik hjk (n + 2) rho sign z‖ ^ 2) ≤
      ((∑ sign ∈
          (planeRegionSignSet X i j k hij hik hjk (n + 1) .A ∪
            planeRegionSignSet X i j k hij hik hjk (n + 1) .D),
          ‖planeComponent X i j k hij hik hjk (n + 1) rho sign z‖ ^ 2) +
        ∑ q : Fin (Fintype.card X),
          2 * ‖z‖ *
            ‖rho (elementaryRoot i j hij
              (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z - z‖) +
        planeFirstTopBoundaryMass X i j k hij hik hjk rho z (n + 2) := by
  classical
  let componentMass := fun sign :
      Fin (Nat.card (Plane X i j k hij hik hjk (n + 2))) → Bool ↦
    ‖planeComponent X i j k hij hik hjk (n + 2) rho sign z‖ ^ 2
  calc
    _ = ∑ q : Fin (Fintype.card X),
          ∑ sign ∈ planeCBLeadingSignSet X i j k hij hik hjk (n + 1) q,
            componentMass sign :=
      sum_planeCBLeadingSignSet X i j k hij hik hjk (n + 1) componentMass
    _ = (∑ q : Fin (Fintype.card X),
          ∑ sign ∈ planeCBInteriorLeadingSignSet X i j k hij hik hjk n q,
            componentMass sign) +
        ∑ q : Fin (Fintype.card X),
          ∑ sign ∈ planeCBTopBoundaryLeadingSignSet X i j k hij hik hjk n q,
            componentMass sign :=
      sum_planeCBLeadingSignSet_eq_interior_add_topBoundary
        X i j k hij hik hjk n componentMass
    _ ≤ ((∑ sign ∈
            (planeRegionSignSet X i j k hij hik hjk (n + 1) .A ∪
              planeRegionSignSet X i j k hij hik hjk (n + 1) .D),
            ‖planeComponent X i j k hij hik hjk (n + 1) rho sign z‖ ^ 2) +
          ∑ q : Fin (Fintype.card X),
            2 * ‖z‖ *
              ‖rho (elementaryRoot i j hij
                (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z - z‖) +
          planeFirstTopBoundaryMass X i j k hij hik hjk rho z (n + 2) :=
      add_le_add
        (sum_norm_planeCBInteriorLeadingSignSet_sq_le_target_add_error
          X i j k hij hik hjk n rho z)
        (sum_norm_planeCBTopBoundaryLeadingSignSet_sq_le
          X i j k hij hik hjk n rho z)

/-- Full `A ∪ B` estimate with source and target at the same finite stage.
The price of replacing the coarse target is exactly the two proved
top-degree boundary masses. -/
theorem planeABMass_le_sameStage_CDMass_add_errors
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    planeRegionUnionMass X i j k hij hik hjk rho z (n + 2) .A .B ≤
      planeRegionUnionMass X i j k hij hik hjk rho z (n + 2) .C .D +
        (∑ q : Fin (Fintype.card X),
          2 * ‖z‖ *
            ‖rho (elementaryRoot j i hij.symm
              (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z - z‖) +
        planeFirstTopBoundaryMass X i j k hij hik hjk rho z (n + 2) +
        2 * planeSecondTopBoundaryMass X i j k hij hik hjk rho z (n + 2) := by
  have hfull := sum_norm_planeABRegion_sq_le_target_add_error_add_boundary
    X i j k hij hik hjk n rho z
  have hrefine := sum_norm_planeRegionUnion_sq_le_succ_add_topBoundaries
    X i j k hij hik hjk (n + 1) .C .D rho z
  change planeRegionUnionMass X i j k hij hik hjk rho z (n + 2) .A .B ≤
    planeRegionUnionMass X i j k hij hik hjk rho z (n + 1) .C .D +
      (∑ q : Fin (Fintype.card X),
        2 * ‖z‖ *
          ‖rho (elementaryRoot j i hij.symm
            (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z - z‖) +
      planeSecondTopBoundaryMass X i j k hij hik hjk rho z (n + 2) at hfull
  change planeRegionUnionMass X i j k hij hik hjk rho z (n + 1) .C .D ≤
    planeRegionUnionMass X i j k hij hik hjk rho z (n + 2) .C .D +
      planeFirstTopBoundaryMass X i j k hij hik hjk rho z (n + 2) +
      planeSecondTopBoundaryMass X i j k hij hik hjk rho z (n + 2) at hrefine
  linarith

/-- Symmetric same-stage `C ∪ B` estimate. -/
theorem planeCBMass_le_sameStage_ADMass_add_errors
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    planeRegionUnionMass X i j k hij hik hjk rho z (n + 2) .C .B ≤
      planeRegionUnionMass X i j k hij hik hjk rho z (n + 2) .A .D +
        (∑ q : Fin (Fintype.card X),
          2 * ‖z‖ *
            ‖rho (elementaryRoot i j hij
              (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z - z‖) +
        2 * planeFirstTopBoundaryMass X i j k hij hik hjk rho z (n + 2) +
        planeSecondTopBoundaryMass X i j k hij hik hjk rho z (n + 2) := by
  have hfull := sum_norm_planeCBRegion_sq_le_target_add_error_add_boundary
    X i j k hij hik hjk n rho z
  have hrefine := sum_norm_planeRegionUnion_sq_le_succ_add_topBoundaries
    X i j k hij hik hjk (n + 1) .A .D rho z
  change planeRegionUnionMass X i j k hij hik hjk rho z (n + 2) .C .B ≤
    planeRegionUnionMass X i j k hij hik hjk rho z (n + 1) .A .D +
      (∑ q : Fin (Fintype.card X),
        2 * ‖z‖ *
          ‖rho (elementaryRoot i j hij
            (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z - z‖) +
      planeFirstTopBoundaryMass X i j k hij hik hjk rho z (n + 2) at hfull
  change planeRegionUnionMass X i j k hij hik hjk rho z (n + 1) .A .D ≤
    planeRegionUnionMass X i j k hij hik hjk rho z (n + 2) .A .D +
      planeFirstTopBoundaryMass X i j k hij hik hjk rho z (n + 2) +
      planeSecondTopBoundaryMass X i j k hij hik hjk rho z (n + 2) at hrefine
  linarith

/-- The part of region `D` detected on the first unit coefficient. -/
noncomputable def planeDFirstSignSet
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) :
    Finset (Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool) :=
  (planeRegionSignSet X i j k hij hik hjk n .D).filter fun sign ↦
    firstCoefficientValuation X i j k hij hik hjk n sign = 0

/-- The remaining part of `D`; its second unit coefficient is necessarily
detected. -/
noncomputable def planeDSecondSignSet
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) :
    Finset (Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool) :=
  (planeRegionSignSet X i j k hij hik hjk n .D).filter fun sign ↦
    firstCoefficientValuation X i j k hij hik hjk n sign ≠ 0

theorem planeRegionSignSet_D_eq_unit_split
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) :
    planeRegionSignSet X i j k hij hik hjk n .D =
      planeDFirstSignSet X i j k hij hik hjk n ∪
        planeDSecondSignSet X i j k hij hik hjk n := by
  classical
  ext sign
  simp only [planeDFirstSignSet, planeDSecondSignSet,
    Finset.mem_filter, Finset.mem_union]
  tauto

theorem planeDFirstSignSet_disjoint_planeDSecondSignSet
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) :
    Disjoint (planeDFirstSignSet X i j k hij hik hjk n)
      (planeDSecondSignSet X i j k hij hik hjk n) := by
  classical
  rw [Finset.disjoint_left]
  intro sign hfirst hsecond
  simp only [planeDFirstSignSet, planeDSecondSignSet,
    Finset.mem_filter] at hfirst hsecond
  exact hsecond.2 hfirst.2

theorem planeDFirstSignSet_subset_negative_unit
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) :
    planeDFirstSignSet X i j k hij hik hjk n ⊆
      negativePlaneSignSet X i j k hij hik hjk n
        (firstCoordinate X (ZMod 2) i j k hij hik hjk n
          (wordMonomialInDegree X (ZMod 2) n 1)) := by
  classical
  intro sign hsign
  simp only [planeDFirstSignSet, Finset.mem_filter] at hsign
  have hdetect := (characterValuation_eq_zero_iff X
    (firstCoefficientEigenvalue X i j k hij hik hjk n sign)).1 hsign.2
  simpa [negativePlaneSignSet, firstCoefficientEigenvalue] using hdetect

theorem planeDSecondSignSet_subset_negative_unit
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) :
    planeDSecondSignSet X i j k hij hik hjk n ⊆
      negativePlaneSignSet X i j k hij hik hjk n
        (secondCoordinate X (ZMod 2) i j k hij hik hjk n
          (wordMonomialInDegree X (ZMod 2) n 1)) := by
  classical
  intro sign hsign
  simp only [planeDSecondSignSet, Finset.mem_filter] at hsign
  have hregion : planeCharacterRegion X i j k hij hik hjk n sign = .D := by
    simpa [planeRegionSignSet] using hsign.1
  have hzero := characterPairRegion_D_data X n
    (firstCoefficientEigenvalue X i j k hij hik hjk n sign)
    (secondCoefficientEigenvalue X i j k hij hik hjk n sign) hregion
  have hsecond : secondCoefficientValuation X i j k hij hik hjk n sign = 0 :=
    hzero.resolve_left hsign.2
  have hdetect := (characterValuation_eq_zero_iff X
    (secondCoefficientEigenvalue X i j k hij hik hjk n sign)).1 hsecond
  simpa [negativePlaneSignSet, secondCoefficientEigenvalue] using hdetect

/-- Region `D` is controlled exactly by the two unit-coordinate
displacements. -/
theorem sum_norm_planeRegionSignSet_D_sq_le_unit_displacements
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    (∑ sign ∈ planeRegionSignSet X i j k hij hik hjk n .D,
        ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2) ≤
      (4 : ℝ)⁻¹ *
          ‖rho (firstCoordinate X (ZMod 2) i j k hij hik hjk n
            (wordMonomialInDegree X (ZMod 2) n 1)).1 z - z‖ ^ 2 +
        (4 : ℝ)⁻¹ *
          ‖rho (secondCoordinate X (ZMod 2) i j k hij hik hjk n
            (wordMonomialInDegree X (ZMod 2) n 1)).1 z - z‖ ^ 2 := by
  classical
  rw [planeRegionSignSet_D_eq_unit_split,
    Finset.sum_union
      (planeDFirstSignSet_disjoint_planeDSecondSignSet
        X i j k hij hik hjk n)]
  calc
    _ ≤ (∑ sign ∈ negativePlaneSignSet X i j k hij hik hjk n
            (firstCoordinate X (ZMod 2) i j k hij hik hjk n
              (wordMonomialInDegree X (ZMod 2) n 1)),
          ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2) +
        ∑ sign ∈ negativePlaneSignSet X i j k hij hik hjk n
            (secondCoordinate X (ZMod 2) i j k hij hik hjk n
              (wordMonomialInDegree X (ZMod 2) n 1)),
          ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2 :=
      add_le_add
        (Finset.sum_le_sum_of_subset_of_nonneg
          (planeDFirstSignSet_subset_negative_unit
            X i j k hij hik hjk n) (fun _ _ _ ↦ sq_nonneg _))
        (Finset.sum_le_sum_of_subset_of_nonneg
          (planeDSecondSignSet_subset_negative_unit
            X i j k hij hik hjk n) (fun _ _ _ ↦ sq_nonneg _))
    _ = _ := by
      rw [planeCharacterMass_eq_quarter_displacement,
        planeCharacterMass_eq_quarter_displacement]

/-- Under opposite unit conjugation, the first coefficient character becomes
the product of the two original characters. -/
theorem firstCoefficientEigenvalue_oppositeUnitConjugatedRestriction_of_valid
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool)
    (hvalid : IsPlaneCharacterSign X i j k hij hik hjk n sign) :
    firstCoefficientEigenvalue X i j k hij hik hjk n
        (fun q ↦ sign
          (oppositeUnitConjugatedPlaneIndex X i j k hij hik hjk n q)) =
      characterProduct X
        (firstCoefficientEigenvalue X i j k hij hik hjk n sign)
        (secondCoefficientEigenvalue X i j k hij hik hjk n sign) := by
  funext a
  rw [firstCoefficientEigenvalue,
    planeEigenvalue_oppositeUnitConjugatedRestriction]
  have hconj : oppositeUnitConjugatedPlane X i j k hij hik hjk n
      (firstCoordinate X (ZMod 2) i j k hij hik hjk n a) =
      firstCoordinate X (ZMod 2) i j k hij hik hjk n a *
        secondCoordinate X (ZMod 2) i j k hij hik hjk n a := by
    apply Subtype.ext
    change elementaryRoot j i hij.symm 1 * elementaryRoot i k hik a.1 *
        (elementaryRoot j i hij.symm 1)⁻¹ =
      elementaryRoot i k hik a.1 * elementaryRoot j k hjk a.1
    rw [elementaryRoot_conjugate, one_mul]
    exact (elementaryRoot_commute_of_ne j k i k hjk hik
      hik.symm hjk.symm _ _).eq
  rw [hconj, hvalid]
  rfl

/-- Opposite unit conjugation fixes the second coefficient character. -/
theorem secondCoefficientEigenvalue_oppositeUnitConjugatedRestriction
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool) :
    secondCoefficientEigenvalue X i j k hij hik hjk n
        (fun q ↦ sign
          (oppositeUnitConjugatedPlaneIndex X i j k hij hik hjk n q)) =
      secondCoefficientEigenvalue X i j k hij hik hjk n sign := by
  funext b
  rw [secondCoefficientEigenvalue,
    planeEigenvalue_oppositeUnitConjugatedRestriction]
  have hconj : oppositeUnitConjugatedPlane X i j k hij hik hjk n
      (secondCoordinate X (ZMod 2) i j k hij hik hjk n b) =
      secondCoordinate X (ZMod 2) i j k hij hik hjk n b := by
    apply Subtype.ext
    have hcomm := elementaryRoot_commute_of_ne j i j k hij.symm hjk
      hij hjk.symm (1 : FreeRing X) b.1
    change elementaryRoot j i hij.symm 1 * elementaryRoot j k hjk b.1 *
        (elementaryRoot j i hij.symm 1)⁻¹ = elementaryRoot j k hjk b.1
    rw [hcomm.eq]
    simp
  rw [hconj]
  rfl

/-- Forward unit conjugation fixes the first coefficient character. -/
theorem firstCoefficientEigenvalue_forwardUnitConjugatedRestriction
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool) :
    firstCoefficientEigenvalue X i j k hij hik hjk n
        (fun q ↦ sign
          (forwardUnitConjugatedPlaneIndex X i j k hij hik hjk n q)) =
      firstCoefficientEigenvalue X i j k hij hik hjk n sign := by
  funext a
  rw [firstCoefficientEigenvalue,
    planeEigenvalue_forwardUnitConjugatedRestriction]
  have hconj : forwardUnitConjugatedPlane X i j k hij hik hjk n
      (firstCoordinate X (ZMod 2) i j k hij hik hjk n a) =
      firstCoordinate X (ZMod 2) i j k hij hik hjk n a := by
    apply Subtype.ext
    have hcomm := elementaryRoot_commute_of_ne i j i k hij hik
      hij.symm hik.symm (1 : FreeRing X) a.1
    change elementaryRoot i j hij 1 * elementaryRoot i k hik a.1 *
        (elementaryRoot i j hij 1)⁻¹ = elementaryRoot i k hik a.1
    rw [hcomm.eq]
    simp
  rw [hconj]
  rfl

/-- Under forward unit conjugation, the second coefficient character becomes
the product of the two original characters. -/
theorem secondCoefficientEigenvalue_forwardUnitConjugatedRestriction_of_valid
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool)
    (hvalid : IsPlaneCharacterSign X i j k hij hik hjk n sign) :
    secondCoefficientEigenvalue X i j k hij hik hjk n
        (fun q ↦ sign
          (forwardUnitConjugatedPlaneIndex X i j k hij hik hjk n q)) =
      characterProduct X
        (firstCoefficientEigenvalue X i j k hij hik hjk n sign)
        (secondCoefficientEigenvalue X i j k hij hik hjk n sign) := by
  funext b
  rw [secondCoefficientEigenvalue,
    planeEigenvalue_forwardUnitConjugatedRestriction]
  have hconj : forwardUnitConjugatedPlane X i j k hij hik hjk n
      (secondCoordinate X (ZMod 2) i j k hij hik hjk n b) =
      firstCoordinate X (ZMod 2) i j k hij hik hjk n b *
        secondCoordinate X (ZMod 2) i j k hij hik hjk n b := by
    apply Subtype.ext
    change elementaryRoot i j hij 1 * elementaryRoot j k hjk b.1 *
        (elementaryRoot i j hij 1)⁻¹ =
      elementaryRoot i k hik b.1 * elementaryRoot j k hjk b.1
    rw [elementaryRoot_conjugate, one_mul]
  rw [hconj, hvalid]
  rfl

/-- The opposite unit shear sends every valid region-`A` sign into `B`. -/
theorem planeCharacterRegion_oppositeUnitConjugatedRestriction_eq_B_of_valid
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool)
    (hvalid : IsPlaneCharacterSign X i j k hij hik hjk n sign)
    (hA : planeCharacterRegion X i j k hij hik hjk n sign = .A) :
    planeCharacterRegion X i j k hij hik hjk n
        (fun q ↦ sign
          (oppositeUnitConjugatedPlaneIndex X i j k hij hik hjk n q)) = .B := by
  let chi := firstCoefficientEigenvalue X i j k hij hik hjk n sign
  let psi := secondCoefficientEigenvalue X i j k hij hik hjk n sign
  have hdata := characterPairRegion_A_data X n chi psi hA
  have hPsiExists : ∃ d, HasDetectionAtDegree X psi d := by
    by_contra hnone
    have hsentinel := characterValuation_eq_succ_of_not_exists X psi hnone
    have hchiBound := characterValuation_le_succ X chi
    omega
  have hproduct := characterValuation_characterProduct_eq_right_of_lt
    X chi psi
    (firstCoefficientEigenvalue_eq_one_or_neg_one X i j k hij hik hjk n sign)
    (secondCoefficientEigenvalue_eq_one_or_neg_one X i j k hij hik hjk n sign)
    hPsiExists hdata.2.2.2
  have hfirst := firstCoefficientEigenvalue_oppositeUnitConjugatedRestriction_of_valid
    X i j k hij hik hjk n sign hvalid
  have hsecond := secondCoefficientEigenvalue_oppositeUnitConjugatedRestriction
    X i j k hij hik hjk n sign
  unfold planeCharacterRegion
  rw [hfirst, hsecond]
  apply characterPairRegion_eq_B_of_data X n
  · intro hboth
    change characterValuation X (characterProduct X chi psi) = n + 1 ∧
      characterValuation X psi = n + 1 at hboth
    have hchiBound := characterValuation_le_succ X chi
    omega
  · rw [hproduct]
    exact hdata.2.2.1
  · exact hdata.2.2.1
  · exact hproduct

/-- The forward unit shear sends every valid region-`C` sign into `B`. -/
theorem planeCharacterRegion_forwardUnitConjugatedRestriction_eq_B_of_valid
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool)
    (hvalid : IsPlaneCharacterSign X i j k hij hik hjk n sign)
    (hC : planeCharacterRegion X i j k hij hik hjk n sign = .C) :
    planeCharacterRegion X i j k hij hik hjk n
        (fun q ↦ sign
          (forwardUnitConjugatedPlaneIndex X i j k hij hik hjk n q)) = .B := by
  let chi := firstCoefficientEigenvalue X i j k hij hik hjk n sign
  let psi := secondCoefficientEigenvalue X i j k hij hik hjk n sign
  have hdata := characterPairRegion_C_data X n chi psi hC
  have hChiExists : ∃ d, HasDetectionAtDegree X chi d := by
    by_contra hnone
    have hsentinel := characterValuation_eq_succ_of_not_exists X chi hnone
    have hpsiBound := characterValuation_le_succ X psi
    omega
  have hproduct := characterValuation_characterProduct_eq_left_of_lt
    X chi psi
    (firstCoefficientEigenvalue_eq_one_or_neg_one X i j k hij hik hjk n sign)
    (secondCoefficientEigenvalue_eq_one_or_neg_one X i j k hij hik hjk n sign)
    hChiExists hdata.2.2.2
  have hfirst := firstCoefficientEigenvalue_forwardUnitConjugatedRestriction
    X i j k hij hik hjk n sign
  have hsecond := secondCoefficientEigenvalue_forwardUnitConjugatedRestriction_of_valid
    X i j k hij hik hjk n sign hvalid
  unfold planeCharacterRegion
  rw [hfirst, hsecond]
  apply characterPairRegion_eq_B_of_data X n
  · intro hboth
    change characterValuation X chi = n + 1 ∧
      characterValuation X (characterProduct X chi psi) = n + 1 at hboth
    have hpsiBound := characterValuation_le_succ X psi
    omega
  · exact hdata.2.1
  · rw [hproduct]
    exact hdata.2.1
  · exact hproduct.symm

/-- The genuine multiplicative signs inside one valuation region. -/
noncomputable def planeValidRegionSignSet
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (region : ValuationRegion) :
    Finset (Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool) :=
  planeValidSignSubset X i j k hij hik hjk n
    (planeRegionSignSet X i j k hij hik hjk n region)

/-- Invalid binary assignments contribute zero, so every valuation region has
exactly the same mass after filtering to genuine multiplicative signs. -/
theorem sum_norm_planeRegionSignSet_eq_valid
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (region : ValuationRegion)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    (∑ sign ∈ planeRegionSignSet X i j k hij hik hjk n region,
        ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2) =
      ∑ sign ∈ planeValidRegionSignSet X i j k hij hik hjk n region,
        ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2 := by
  classical
  simpa [planeValidRegionSignSet] using
    sum_norm_planeSignSet_eq_filter_valid X i j k hij hik hjk n rho
      (planeRegionSignSet X i j k hij hik hjk n region) z

/-- Same-stage unit transport gives the quantitative `A → B` mass estimate
from Kassabov's argument. -/
theorem sum_norm_planeRegionSignSet_A_sq_le_B_add_unit_error
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    (∑ sign ∈ planeRegionSignSet X i j k hij hik hjk n .A,
        ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2) ≤
      (∑ sign ∈ planeRegionSignSet X i j k hij hik hjk n .B,
        ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2) +
      2 * ‖z‖ * ‖rho (elementaryRoot j i hij.symm 1) z - z‖ := by
  classical
  let source := planeRegionSignSet X i j k hij hik hjk n .A
  let validSource := source.filter
    (IsPlaneCharacterSign X i j k hij hik hjk n)
  let target := planeRegionSignSet X i j k hij hik hjk n .B
  let index := oppositeUnitConjugatedPlaneIndex X i j k hij hik hjk n
  let moved := rho (elementaryRoot j i hij.symm 1) z
  have hsubset : validSource ⊆ fineRestrictionSignSet
      (Nat.card (Plane X i j k hij hik hjk n))
      (Nat.card (Plane X i j k hij hik hjk n)) index target := by
    intro sign hsign
    obtain ⟨hsource, hvalid⟩ := Finset.mem_filter.mp hsign
    have hA : planeCharacterRegion X i j k hij hik hjk n sign = .A := by
      simpa [source, planeRegionSignSet] using hsource
    have hB :=
      planeCharacterRegion_oppositeUnitConjugatedRestriction_eq_B_of_valid
        X i j k hij hik hjk n sign hvalid hA
    simp only [fineRestrictionSignSet, Finset.mem_filter, Finset.mem_univ,
      true_and]
    simpa [index, target, planeRegionSignSet] using hB
  have htransport :
      (∑ sign ∈ source,
          ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2) ≤
        ∑ sign ∈ target,
          ‖planeComponent X i j k hij hik hjk n rho sign moved‖ ^ 2 := by
    calc
      _ = ∑ sign ∈ validSource,
          ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2 := by
        exact sum_norm_planeRegionSignSet_eq_valid
          X i j k hij hik hjk n .A rho z
      _ ≤ ∑ sign ∈ fineRestrictionSignSet
            (Nat.card (Plane X i j k hij hik hjk n))
            (Nat.card (Plane X i j k hij hik hjk n)) index target,
          ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun _ _ _ ↦ sq_nonneg _)
      _ = ∑ sign ∈ target,
          ‖planeComponent X i j k hij hik hjk n rho sign moved‖ ^ 2 :=
        sum_norm_oppositeUnitConjugatedRestriction_sq
          X i j k hij hik hjk n rho target z
  have hvariation := abs_sum_norm_planeComponent_sq_sub_le
    X i j k hij hik hjk n rho target moved z
  have hdiff :
      (∑ sign ∈ target,
          ‖planeComponent X i j k hij hik hjk n rho sign moved‖ ^ 2) -
        (∑ sign ∈ target,
          ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2) ≤
      (‖moved‖ + ‖z‖) * ‖moved - z‖ :=
    (le_abs_self _).trans hvariation
  rw [sub_le_iff_le_add] at hdiff
  have hnorm : ‖moved‖ = ‖z‖ :=
    (rho (elementaryRoot j i hij.symm 1)).norm_map z
  calc
    _ ≤ ∑ sign ∈ target,
          ‖planeComponent X i j k hij hik hjk n rho sign moved‖ ^ 2 := htransport
    _ ≤ (‖moved‖ + ‖z‖) * ‖moved - z‖ +
        ∑ sign ∈ target,
          ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2 := hdiff
    _ = (∑ sign ∈ target,
          ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2) +
        2 * ‖z‖ * ‖moved - z‖ := by rw [hnorm]; ring
    _ = _ := by rfl

/-- Symmetric quantitative `C → B` unit-shear estimate. -/
theorem sum_norm_planeRegionSignSet_C_sq_le_B_add_unit_error
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    (∑ sign ∈ planeRegionSignSet X i j k hij hik hjk n .C,
        ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2) ≤
      (∑ sign ∈ planeRegionSignSet X i j k hij hik hjk n .B,
        ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2) +
      2 * ‖z‖ * ‖rho (elementaryRoot i j hij 1) z - z‖ := by
  classical
  let source := planeRegionSignSet X i j k hij hik hjk n .C
  let validSource := source.filter
    (IsPlaneCharacterSign X i j k hij hik hjk n)
  let target := planeRegionSignSet X i j k hij hik hjk n .B
  let index := forwardUnitConjugatedPlaneIndex X i j k hij hik hjk n
  let moved := rho (elementaryRoot i j hij 1) z
  have hsubset : validSource ⊆ fineRestrictionSignSet
      (Nat.card (Plane X i j k hij hik hjk n))
      (Nat.card (Plane X i j k hij hik hjk n)) index target := by
    intro sign hsign
    obtain ⟨hsource, hvalid⟩ := Finset.mem_filter.mp hsign
    have hC : planeCharacterRegion X i j k hij hik hjk n sign = .C := by
      simpa [source, planeRegionSignSet] using hsource
    have hB :=
      planeCharacterRegion_forwardUnitConjugatedRestriction_eq_B_of_valid
        X i j k hij hik hjk n sign hvalid hC
    simp only [fineRestrictionSignSet, Finset.mem_filter, Finset.mem_univ,
      true_and]
    simpa [index, target, planeRegionSignSet] using hB
  have htransport :
      (∑ sign ∈ source,
          ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2) ≤
        ∑ sign ∈ target,
          ‖planeComponent X i j k hij hik hjk n rho sign moved‖ ^ 2 := by
    calc
      _ = ∑ sign ∈ validSource,
          ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2 := by
        exact sum_norm_planeRegionSignSet_eq_valid
          X i j k hij hik hjk n .C rho z
      _ ≤ ∑ sign ∈ fineRestrictionSignSet
            (Nat.card (Plane X i j k hij hik hjk n))
            (Nat.card (Plane X i j k hij hik hjk n)) index target,
          ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun _ _ _ ↦ sq_nonneg _)
      _ = ∑ sign ∈ target,
          ‖planeComponent X i j k hij hik hjk n rho sign moved‖ ^ 2 :=
        sum_norm_forwardUnitConjugatedRestriction_sq
          X i j k hij hik hjk n rho target z
  have hvariation := abs_sum_norm_planeComponent_sq_sub_le
    X i j k hij hik hjk n rho target moved z
  have hdiff :
      (∑ sign ∈ target,
          ‖planeComponent X i j k hij hik hjk n rho sign moved‖ ^ 2) -
        (∑ sign ∈ target,
          ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2) ≤
      (‖moved‖ + ‖z‖) * ‖moved - z‖ :=
    (le_abs_self _).trans hvariation
  rw [sub_le_iff_le_add] at hdiff
  have hnorm : ‖moved‖ = ‖z‖ :=
    (rho (elementaryRoot i j hij 1)).norm_map z
  calc
    _ ≤ ∑ sign ∈ target,
          ‖planeComponent X i j k hij hik hjk n rho sign moved‖ ^ 2 := htransport
    _ ≤ (‖moved‖ + ‖z‖) * ‖moved - z‖ +
        ∑ sign ∈ target,
          ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2 := hdiff
    _ = (∑ sign ∈ target,
          ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2) +
        2 * ‖z‖ * ‖moved - z‖ := by rw [hnorm]; ring
    _ = _ := by rfl

/-- Adding the two same-stage generator-shear inequalities cancels regions
`A` and `C`, leaving a direct bound for the diagonal region `B`. -/
theorem planeRegionMass_B_le_D_add_generatorErrors_add_boundaries
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    planeRegionMass X i j k hij hik hjk rho z (n + 2) .B ≤
      planeRegionMass X i j k hij hik hjk rho z (n + 2) .D +
        (2 : ℝ)⁻¹ *
          ((∑ q : Fin (Fintype.card X),
              2 * ‖z‖ *
                ‖rho (elementaryRoot j i hij.symm
                  (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z - z‖) +
            ∑ q : Fin (Fintype.card X),
              2 * ‖z‖ *
                ‖rho (elementaryRoot i j hij
                  (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z - z‖) +
        (3 : ℝ) / 2 *
          (planeFirstTopBoundaryMass X i j k hij hik hjk rho z (n + 2) +
            planeSecondTopBoundaryMass X i j k hij hik hjk rho z (n + 2)) := by
  have hab := planeABMass_le_sameStage_CDMass_add_errors
    X i j k hij hik hjk n rho z
  have hcb := planeCBMass_le_sameStage_ADMass_add_errors
    X i j k hij hik hjk n rho z
  rw [planeRegionUnionMass_eq_add X i j k hij hik hjk rho z (n + 2)
      .A .B (by decide),
    planeRegionUnionMass_eq_add X i j k hij hik hjk rho z (n + 2)
      .C .D (by decide)] at hab
  rw [planeRegionUnionMass_eq_add X i j k hij hik hjk rho z (n + 2)
      .C .B (by decide),
    planeRegionUnionMass_eq_add X i j k hij hik hjk rho z (n + 2)
      .A .D (by decide)] at hcb
  linarith

/-- Finite-stage Kassabov estimate for the total mass in all four nonzero
valuation regions.  Every term on the right is the displacement of an
explicit elementary generator, except the two boundary masses already proved
to converge to zero. -/
theorem sum_planeRegionMass_nonzero_le_explicit_errors
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    planeRegionMass X i j k hij hik hjk rho z (n + 2) .A +
        planeRegionMass X i j k hij hik hjk rho z (n + 2) .B +
        planeRegionMass X i j k hij hik hjk rho z (n + 2) .C +
        planeRegionMass X i j k hij hik hjk rho z (n + 2) .D ≤
      ‖rho (firstCoordinate X (ZMod 2) i j k hij hik hjk (n + 2)
          (wordMonomialInDegree X (ZMod 2) (n + 2) 1)).1 z - z‖ ^ 2 +
        ‖rho (secondCoordinate X (ZMod 2) i j k hij hik hjk (n + 2)
          (wordMonomialInDegree X (ZMod 2) (n + 2) 1)).1 z - z‖ ^ 2 +
        (3 : ℝ) / 2 *
          ((∑ q : Fin (Fintype.card X),
              2 * ‖z‖ *
                ‖rho (elementaryRoot j i hij.symm
                  (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z - z‖) +
            ∑ q : Fin (Fintype.card X),
              2 * ‖z‖ *
                ‖rho (elementaryRoot i j hij
                  (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z - z‖) +
        2 * ‖z‖ * ‖rho (elementaryRoot j i hij.symm 1) z - z‖ +
        2 * ‖z‖ * ‖rho (elementaryRoot i j hij 1) z - z‖ +
        (9 : ℝ) / 2 *
          (planeFirstTopBoundaryMass X i j k hij hik hjk rho z (n + 2) +
            planeSecondTopBoundaryMass X i j k hij hik hjk rho z (n + 2)) := by
  have hA := sum_norm_planeRegionSignSet_A_sq_le_B_add_unit_error
    X i j k hij hik hjk (n + 2) rho z
  have hC := sum_norm_planeRegionSignSet_C_sq_le_B_add_unit_error
    X i j k hij hik hjk (n + 2) rho z
  have hB := planeRegionMass_B_le_D_add_generatorErrors_add_boundaries
    X i j k hij hik hjk n rho z
  have hD := sum_norm_planeRegionSignSet_D_sq_le_unit_displacements
    X i j k hij hik hjk (n + 2) rho z
  change planeRegionMass X i j k hij hik hjk rho z (n + 2) .A ≤
    planeRegionMass X i j k hij hik hjk rho z (n + 2) .B +
      2 * ‖z‖ * ‖rho (elementaryRoot j i hij.symm 1) z - z‖ at hA
  change planeRegionMass X i j k hij hik hjk rho z (n + 2) .C ≤
    planeRegionMass X i j k hij hik hjk rho z (n + 2) .B +
      2 * ‖z‖ * ‖rho (elementaryRoot i j hij 1) z - z‖ at hC
  change planeRegionMass X i j k hij hik hjk rho z (n + 2) .D ≤
    (4 : ℝ)⁻¹ *
        ‖rho (firstCoordinate X (ZMod 2) i j k hij hik hjk (n + 2)
          (wordMonomialInDegree X (ZMod 2) (n + 2) 1)).1 z - z‖ ^ 2 +
      (4 : ℝ)⁻¹ *
        ‖rho (secondCoordinate X (ZMod 2) i j k hij hik hjk (n + 2)
          (wordMonomialInDegree X (ZMod 2) (n + 2) 1)).1 z - z‖ ^ 2 at hD
  linarith

/-- Limiting two-root relative Kazhdan estimate.  The finite Fourier boundary
terms disappear along the exhaustive free-word filtration, leaving only the
displacements of the explicit adjacent-root generators and the two unit
elements in the moving plane. -/
theorem norm_joinRootMovingProjection_sq_le_explicit_errors [CompleteSpace E]
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    ‖KazhdanFixedSpace.subgroupMovingProjection rho
        (elementaryRootSubgroup i k hik ⊔
          elementaryRootSubgroup j k hjk) z‖ ^ 2 ≤
      ‖rho (elementaryRoot i k hik 1) z - z‖ ^ 2 +
        ‖rho (elementaryRoot j k hjk 1) z - z‖ ^ 2 +
        (3 : ℝ) / 2 *
          ((∑ q : Fin (Fintype.card X),
              2 * ‖z‖ *
                ‖rho (elementaryRoot j i hij.symm
                  (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z - z‖) +
            ∑ q : Fin (Fintype.card X),
              2 * ‖z‖ *
                ‖rho (elementaryRoot i j hij
                  (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z - z‖) +
          2 * ‖z‖ * ‖rho (elementaryRoot j i hij.symm 1) z - z‖ +
          2 * ‖z‖ * ‖rho (elementaryRoot i j hij 1) z - z‖ := by
  let C : ℝ :=
    ‖rho (elementaryRoot i k hik 1) z - z‖ ^ 2 +
      ‖rho (elementaryRoot j k hjk 1) z - z‖ ^ 2 +
      (3 : ℝ) / 2 *
        ((∑ q : Fin (Fintype.card X),
            2 * ‖z‖ *
              ‖rho (elementaryRoot j i hij.symm
                (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z - z‖) +
          ∑ q : Fin (Fintype.card X),
            2 * ‖z‖ *
              ‖rho (elementaryRoot i j hij
                (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z - z‖) +
        2 * ‖z‖ * ‖rho (elementaryRoot j i hij.symm 1) z - z‖ +
        2 * ‖z‖ * ‖rho (elementaryRoot i j hij 1) z - z‖
  change
    ‖KazhdanFixedSpace.subgroupMovingProjection rho
        (elementaryRootSubgroup i k hik ⊔
          elementaryRootSubgroup j k hjk) z‖ ^ 2 ≤ C
  have hfinite (n : ℕ) :
      ‖planeMovingPart X i j k hij hik hjk rho z (n + 2)‖ ^ 2 ≤
        C + (9 : ℝ) / 2 *
          (planeFirstTopBoundaryMass X i j k hij hik hjk rho z (n + 2) +
            planeSecondTopBoundaryMass X i j k hij hik hjk rho z (n + 2)) := by
    rw [norm_planeMovingPart_sq_eq_sum_regionMass
      X i j k hij hik hjk rho z (n + 2)]
    have h := sum_planeRegionMass_nonzero_le_explicit_errors
      X i j k hij hik hjk n rho z
    simp only [firstCoordinate_val, secondCoordinate_val,
      wordMonomialInDegree_one_val] at h
    dsimp only [C]
    linarith
  have hleft : Filter.Tendsto
      (fun n ↦ ‖planeMovingPart X i j k hij hik hjk rho z (n + 2)‖ ^ 2)
      Filter.atTop
      (nhds (‖KazhdanFixedSpace.subgroupMovingProjection rho
        (elementaryRootSubgroup i k hik ⊔
          elementaryRootSubgroup j k hjk) z‖ ^ 2)) := by
    exact (Filter.tendsto_add_atTop_iff_nat 2).2
      (tendsto_norm_planeMovingPart_sq X i j k hij hik hjk rho z)
  have hfirst : Filter.Tendsto
      (fun n ↦ planeFirstTopBoundaryMass X i j k hij hik hjk rho z (n + 2))
      Filter.atTop (nhds 0) := by
    have h := (Filter.tendsto_add_atTop_iff_nat 1).2
      (tendsto_planeFirstTopBoundaryMass_succ_zero
        X i j k hij hik hjk rho z)
    simpa [Nat.add_assoc] using h
  have hsecond : Filter.Tendsto
      (fun n ↦ planeSecondTopBoundaryMass X i j k hij hik hjk rho z (n + 2))
      Filter.atTop (nhds 0) := by
    have h := (Filter.tendsto_add_atTop_iff_nat 1).2
      (tendsto_planeSecondTopBoundaryMass_succ_zero
        X i j k hij hik hjk rho z)
    simpa [Nat.add_assoc] using h
  have hscaled : Filter.Tendsto
      (fun n ↦ (9 : ℝ) / 2 *
        (planeFirstTopBoundaryMass X i j k hij hik hjk rho z (n + 2) +
          planeSecondTopBoundaryMass X i j k hij hik hjk rho z (n + 2)))
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul (hfirst.add hsecond))
  have hright : Filter.Tendsto
      (fun n ↦ C + (9 : ℝ) / 2 *
        (planeFirstTopBoundaryMass X i j k hij hik hjk rho z (n + 2) +
          planeSecondTopBoundaryMass X i j k hij hik hjk rho z (n + 2)))
      Filter.atTop (nhds C) := by
    simpa using tendsto_const_nhds.add hscaled
  exact le_of_tendsto_of_tendsto hleft hright
    (Filter.Eventually.of_forall hfinite)

/-- The squared mass of one `A ∪ B` leading-generator fiber is bounded by
the coarse `C ∪ D` mass after acting by its opposite adjacent generator.
No component is counted through a merely algebraic character map: the proof
uses the concrete conjugated-plane refinement. -/
theorem sum_norm_planeABLeadingSignSet_sq_le
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (q : Fin (Fintype.card X))
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    ∑ fineSign ∈ planeABLeadingSignSet X i j k hij hik hjk n q,
        ‖planeComponent X i j k hij hik hjk (n + 1) rho fineSign z‖ ^ 2 ≤
      ∑ coarseSign ∈
          (planeRegionSignSet X i j k hij hik hjk n .C ∪
            planeRegionSignSet X i j k hij hik hjk n .D),
        ‖planeComponent X i j k hij hik hjk n rho coarseSign
          (rho (elementaryRoot j i hij.symm
            (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z)‖ ^ 2 := by
  classical
  let fiber := planeABLeadingSignSet X i j k hij hik hjk n q
  let nonzeroFiber := fiber.filter fun fineSign ↦
    planeComponent X i j k hij hik hjk (n + 1) rho fineSign z ≠ 0
  let target := planeRegionSignSet X i j k hij hik hjk n .C ∪
    planeRegionSignSet X i j k hij hik hjk n .D
  let index := oppositeConjugatedPlaneSuccIndex X i j k hij hik hjk
    (generatorEnumeration X q) n
  have hremove :
      ∑ fineSign ∈ fiber,
          ‖planeComponent X i j k hij hik hjk (n + 1) rho fineSign z‖ ^ 2 =
        ∑ fineSign ∈ nonzeroFiber,
          ‖planeComponent X i j k hij hik hjk (n + 1) rho fineSign z‖ ^ 2 := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro fineSign hmem hnot
    have hzero : planeComponent X i j k hij hik hjk (n + 1) rho fineSign z = 0 := by
      by_contra hne
      exact hnot (Finset.mem_filter.mpr ⟨hmem, hne⟩)
    rw [hzero]
    simp
  have hsubset : nonzeroFiber ⊆ fineRestrictionSignSet
      (Nat.card (Plane X i j k hij hik hjk (n + 1)))
      (Nat.card (Plane X i j k hij hik hjk n)) index target := by
    intro fineSign hmem
    obtain ⟨hfiber, hne⟩ := Finset.mem_filter.mp hmem
    have hregion :=
      planeCharacterRegion_oppositeConjugatedRestriction_eq_C_or_D
        X i j k hij hik hjk n q rho fineSign z hne hfiber
    simp only [fineRestrictionSignSet, Finset.mem_filter, Finset.mem_univ,
      true_and]
    change (fun r ↦ fineSign (index r)) ∈ target
    simpa [target, planeRegionSignSet] using hregion
  calc
    ∑ fineSign ∈ planeABLeadingSignSet X i j k hij hik hjk n q,
        ‖planeComponent X i j k hij hik hjk (n + 1) rho fineSign z‖ ^ 2 =
        ∑ fineSign ∈ nonzeroFiber,
          ‖planeComponent X i j k hij hik hjk (n + 1) rho fineSign z‖ ^ 2 :=
      hremove
    _ ≤ ∑ fineSign ∈ fineRestrictionSignSet
          (Nat.card (Plane X i j k hij hik hjk (n + 1)))
          (Nat.card (Plane X i j k hij hik hjk n)) index target,
          ‖planeComponent X i j k hij hik hjk (n + 1) rho fineSign z‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun _ _ _ ↦ sq_nonneg _)
    _ = ∑ coarseSign ∈ target,
          ‖planeComponent X i j k hij hik hjk n rho coarseSign
            (rho (elementaryRoot j i hij.symm
              (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z)‖ ^ 2 :=
      sum_norm_oppositeConjugatedRestriction_sq X i j k hij hik hjk
        (generatorEnumeration X q) n rho target z

/-- Symmetrically, one `C ∪ B` leading-generator fiber is bounded by the
coarse `A ∪ D` mass after the corresponding forward adjacent action. -/
theorem sum_norm_planeCBLeadingSignSet_sq_le
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (q : Fin (Fintype.card X))
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    ∑ fineSign ∈ planeCBLeadingSignSet X i j k hij hik hjk n q,
        ‖planeComponent X i j k hij hik hjk (n + 1) rho fineSign z‖ ^ 2 ≤
      ∑ coarseSign ∈
          (planeRegionSignSet X i j k hij hik hjk n .A ∪
            planeRegionSignSet X i j k hij hik hjk n .D),
        ‖planeComponent X i j k hij hik hjk n rho coarseSign
          (rho (elementaryRoot i j hij
            (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z)‖ ^ 2 := by
  classical
  let fiber := planeCBLeadingSignSet X i j k hij hik hjk n q
  let nonzeroFiber := fiber.filter fun fineSign ↦
    planeComponent X i j k hij hik hjk (n + 1) rho fineSign z ≠ 0
  let target := planeRegionSignSet X i j k hij hik hjk n .A ∪
    planeRegionSignSet X i j k hij hik hjk n .D
  let index := forwardConjugatedPlaneSuccIndex X i j k hij hik hjk
    (generatorEnumeration X q) n
  have hremove :
      ∑ fineSign ∈ fiber,
          ‖planeComponent X i j k hij hik hjk (n + 1) rho fineSign z‖ ^ 2 =
        ∑ fineSign ∈ nonzeroFiber,
          ‖planeComponent X i j k hij hik hjk (n + 1) rho fineSign z‖ ^ 2 := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro fineSign hmem hnot
    have hzero : planeComponent X i j k hij hik hjk (n + 1) rho fineSign z = 0 := by
      by_contra hne
      exact hnot (Finset.mem_filter.mpr ⟨hmem, hne⟩)
    rw [hzero]
    simp
  have hsubset : nonzeroFiber ⊆ fineRestrictionSignSet
      (Nat.card (Plane X i j k hij hik hjk (n + 1)))
      (Nat.card (Plane X i j k hij hik hjk n)) index target := by
    intro fineSign hmem
    obtain ⟨hfiber, hne⟩ := Finset.mem_filter.mp hmem
    have hregion :=
      planeCharacterRegion_forwardConjugatedRestriction_eq_A_or_D
        X i j k hij hik hjk n q rho fineSign z hne hfiber
    simp only [fineRestrictionSignSet, Finset.mem_filter, Finset.mem_univ,
      true_and]
    change (fun r ↦ fineSign (index r)) ∈ target
    simpa [target, planeRegionSignSet] using hregion
  calc
    ∑ fineSign ∈ planeCBLeadingSignSet X i j k hij hik hjk n q,
        ‖planeComponent X i j k hij hik hjk (n + 1) rho fineSign z‖ ^ 2 =
        ∑ fineSign ∈ nonzeroFiber,
          ‖planeComponent X i j k hij hik hjk (n + 1) rho fineSign z‖ ^ 2 :=
      hremove
    _ ≤ ∑ fineSign ∈ fineRestrictionSignSet
          (Nat.card (Plane X i j k hij hik hjk (n + 1)))
          (Nat.card (Plane X i j k hij hik hjk n)) index target,
          ‖planeComponent X i j k hij hik hjk (n + 1) rho fineSign z‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun _ _ _ ↦ sq_nonneg _)
    _ = ∑ coarseSign ∈ target,
          ‖planeComponent X i j k hij hik hjk n rho coarseSign
            (rho (elementaryRoot i j hij
              (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z)‖ ^ 2 :=
      sum_norm_forwardConjugatedRestriction_sq X i j k hij hik hjk
        (generatorEnumeration X q) n rho target z

/-- A nonzero Fourier component with a nontrivial plane character has at least
one genuinely detected coordinate valuation within the current stage. -/
theorem firstValuation_le_or_secondValuation_le_of_planeEigenvalue_eq_neg_one
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool)
    (z : E)
    (hv : planeComponent X i j k hij hik hjk n rho sign z ≠ 0)
    (g : Plane X i j k hij hik hjk n)
    (hg : planeEigenvalue X i j k hij hik hjk n sign g = -1) :
    firstCoefficientValuation X i j k hij hik hjk n sign ≤ n ∨
      secondCoefficientValuation X i j k hij hik hjk n sign ≤ n := by
  rcases exists_nontrivial_coefficient_of_planeEigenvalue_eq_neg_one
      X i j k hij hik hjk n rho sign z hv g hg with ⟨a, ha⟩ | ⟨b, hb⟩
  · left
    exact characterValuation_le_stage_of_eq_neg_one X
      (firstCoefficientEigenvalue X i j k hij hik hjk n sign)
      (firstCoefficientEigenvalue_zero_of_component_ne_zero
        X i j k hij hik hjk n rho sign z hv)
      (firstCoefficientEigenvalue_add_of_component_ne_zero
        X i j k hij hik hjk n rho sign z hv)
      (firstCoefficientEigenvalue_eq_one_or_neg_one
        X i j k hij hik hjk n sign) a ha
  · right
    exact characterValuation_le_stage_of_eq_neg_one X
      (secondCoefficientEigenvalue X i j k hij hik hjk n sign)
      (secondCoefficientEigenvalue_zero_of_component_ne_zero
        X i j k hij hik hjk n rho sign z hv)
      (secondCoefficientEigenvalue_add_of_component_ne_zero
        X i j k hij hik hjk n rho sign z hv)
      (secondCoefficientEigenvalue_eq_one_or_neg_one
        X i j k hij hik hjk n sign) b hb


end

end FreeRootCharacterValuation

end NonsoficGroupsExist
