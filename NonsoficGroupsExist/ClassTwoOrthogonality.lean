import NonsoficGroupsExist.ClassTwoApproximation
import NonsoficGroupsExist.ClassTwoNormalForm
import NonsoficGroupsExist.FiniteClassTwoDecompositionBound

/-!
# Universal class-two fixed-space orthogonality

Finite subsets of the two generating abelian bounded-exponent subgroups
produce finite class-two stages.  The finite `1 / sqrt 2` theorem is applied
in each stage's moving representation, and the directed projection theorem
passes to the full (possibly infinitely generated) group.  One positive
exponent bound suffices, so every finite characteristic is covered.
-/

namespace NonsoficGroupsExist

open scoped commutatorElement

universe u v

namespace ClassTwoOrthogonality

variable {G : Type u} [Group G]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- Universal `1 / sqrt 2` orthogonality for two abelian bounded-exponent
subgroups whose cross-commutator is central of the same bounded exponent. -/
theorem epsilonOrthogonal
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (X Y : Subgroup G)
    (n : ℕ) (hn : 0 < n)
    (hgen : X ⊔ Y = ⊤)
    (hXcomm : ∀ x ∈ X, ∀ x' ∈ X, Commute x x')
    (hYcomm : ∀ y ∈ Y, ∀ y' ∈ Y, Commute y y')
    (hXexp : ∀ x ∈ X, x ^ n = 1)
    (hYexp : ∀ y ∈ Y, y ^ n = 1)
    (hcentral : ⁅Y, X⁆ ≤ Subgroup.center G)
    (hCexp : ∀ c ∈ ⁅Y, X⁆, c ^ n = 1)
    (hno : IsKazhdanPair.HasNoInvariantVectors G rho) :
    HilbertEpsilonOrthogonality.EpsilonOrthogonal
      (KazhdanFixedSpace.fixedSubspace rho X)
      (KazhdanFixedSpace.fixedSubspace rho Y)
      (Real.sqrt 2)⁻¹ := by
  apply ClassTwoApproximation.epsilonOrthogonal_of_stage_estimates
    rho X Y hgen hno
  intro a u hu v hv
  let X₀ := ClassTwoApproximation.leftStage X Y a
  let Y₀ := ClassTwoApproximation.rightStage X Y a
  let K := ClassTwoApproximation.stageGroup X Y a
  let C₀ := ⁅Y₀, X₀⁆
  have hC₀C : C₀ ≤ ⁅Y, X⁆ :=
    Subgroup.commutator_mono
      (ClassTwoApproximation.rightStage_le X Y a)
      (ClassTwoApproximation.leftStage_le X Y a)
  letI : Finite X₀ :=
    ClassTwoApproximation.finite_leftStage X Y a n hn hXcomm hXexp
  letI : Finite Y₀ :=
    ClassTwoApproximation.finite_rightStage X Y a n hn hYcomm hYexp
  have hC₀fg : C₀.FG :=
    ClassTwoApproximation.commutator_fg_of_finite Y₀ X₀
  have hC₀comm : ∀ c ∈ C₀, ∀ d ∈ C₀, Commute c d := by
    intro c hc d hd
    exact (Subgroup.mem_center_iff.mp (hcentral (hC₀C hc)) d).symm
  have hC₀exp : ∀ c ∈ C₀, c ^ n = 1 := by
    intro c hc
    exact hCexp c (hC₀C hc)
  letI : Finite C₀ :=
    ClassTwoApproximation.finite_of_fg_commute_boundedExponent
      C₀ n hn hC₀fg hC₀comm hC₀exp
  have hYX : ⁅Y₀, X₀⁆ ≤ C₀ := le_rfl
  have hXC : ⁅X₀, C₀⁆ ≤ C₀ := by
    apply Subgroup.commutator_le.mpr
    intro x hx c hc
    rw [commutatorElement_eq_one_iff_commute.mpr
      (Subgroup.mem_center_iff.mp (hcentral (hC₀C hc)) x)]
    exact C₀.one_mem
  have hYC : ⁅Y₀, C₀⁆ ≤ C₀ := by
    apply Subgroup.commutator_le.mpr
    intro y hy c hc
    rw [commutatorElement_eq_one_iff_commute.mpr
      (Subgroup.mem_center_iff.mp (hcentral (hC₀C hc)) y)]
    exact C₀.one_mem
  have hC₀K : C₀ ≤ K := by
    intro c hc
    have := Subgroup.commutator_le_sup Y₀ X₀ hc
    simpa [K, ClassTwoApproximation.stageGroup, sup_comm] using this
  letI : Finite K := ClassTwoNormalForm.finite_sup_of_three_factor
    X₀ Y₀ C₀ hYX hXC hYC hC₀K
  let XL := X₀.subgroupOf K
  let YL := Y₀.subgroupOf K
  let CL := C₀.subgroupOf K
  have hgenK : XL ⊔ YL = ⊤ :=
    ClassTwoNormalForm.subgroupOf_sup_eq_top X₀ Y₀ K
      le_sup_left le_sup_right rfl
  have hcommK : ⁅YL, XL⁆ ≤ CL := by
    apply Subgroup.commutator_le.mpr
    intro y hy x hx
    apply Subgroup.mem_subgroupOf.mpr
    exact Subgroup.commutator_mem_commutator
      (Subgroup.mem_subgroupOf.mp hy) (Subgroup.mem_subgroupOf.mp hx)
  have hcentralK : CL ≤ Subgroup.center K := by
    intro c hc
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp
      (hcentral (hC₀C (Subgroup.mem_subgroupOf.mp hc))) g.1
  have hCLexp : ∀ c ∈ CL, c ^ n = 1 := by
    intro c hc
    apply Subtype.ext
    exact hC₀exp c.1 (Subgroup.mem_subgroupOf.mp hc)
  let W := KazhdanFixedSpace.subgroupMovingSubspace rho K
  let rhoW := KazhdanFixedSpace.subgroupMovingRepresentation rho K
  let pu := KazhdanFixedSpace.subgroupMovingProjection rho K u
  let pv := KazhdanFixedSpace.subgroupMovingProjection rho K v
  let uW : W := ⟨pu, KazhdanFixedSpace.subgroupMovingProjection_mem rho K u⟩
  let vW : W := ⟨pv, KazhdanFixedSpace.subgroupMovingProjection_mem rho K v⟩
  have huX₀ : u ∈ KazhdanFixedSpace.fixedSubspace rho X₀ :=
    KazhdanFixedSpace.antitone rho
      (ClassTwoApproximation.leftStage_le X Y a) hu
  have hvY₀ : v ∈ KazhdanFixedSpace.fixedSubspace rho Y₀ :=
    KazhdanFixedSpace.antitone rho
      (ClassTwoApproximation.rightStage_le X Y a) hv
  have hpuX₀ : pu ∈ KazhdanFixedSpace.fixedSubspace rho X₀ :=
    KazhdanFixedSpace.subgroupMovingProjection_mem_fixedSubspace
      rho X₀ K le_sup_left huX₀
  have hpvY₀ : pv ∈ KazhdanFixedSpace.fixedSubspace rho Y₀ :=
    KazhdanFixedSpace.subgroupMovingProjection_mem_fixedSubspace
      rho Y₀ K le_sup_right hvY₀
  have huW : uW ∈ KazhdanFixedSpace.fixedSubspace rhoW XL := by
    rw [KazhdanFixedSpace.mem_fixedSubspace_iff]
    intro x hx
    apply Subtype.ext
    exact (KazhdanFixedSpace.mem_fixedSubspace_iff rho X₀ pu).mp
      hpuX₀ x.1 (Subgroup.mem_subgroupOf.mp hx)
  have hvW : vW ∈ KazhdanFixedSpace.fixedSubspace rhoW YL := by
    rw [KazhdanFixedSpace.mem_fixedSubspace_iff]
    intro y hy
    apply Subtype.ext
    exact (KazhdanFixedSpace.mem_fixedSubspace_iff rho Y₀ pv).mp
      hpvY₀ y.1 (Subgroup.mem_subgroupOf.mp hy)
  have heps := FiniteClassTwoDecompositionBound.epsilonOrthogonal
    rhoW XL YL CL n hn hgenK hcommK hcentralK hCLexp
      (KazhdanFixedSpace.subgroupMovingRepresentation_hasNoInvariantVectors rho K)
  have hbound := heps uW huW vW hvW
  exact hbound

end ClassTwoOrthogonality
end NonsoficGroupsExist
