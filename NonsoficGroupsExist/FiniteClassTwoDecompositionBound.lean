import NonsoficGroupsExist.CentralInvolutionDecomposition
import NonsoficGroupsExist.FiniteClassTwoOrthogonality

/-!
# Finite-dimensional class-two averaging bound

The scalar `1 / sqrt 2` estimate is recombined across the simultaneous
eigenspaces of the finite central involution subgroup.  All sums below are
the actual finite supports of `DirectSum` elements.
-/

namespace NonsoficGroupsExist

open scoped commutatorElement

universe u v

namespace FiniteClassTwoDecompositionBound

variable {G : Type u} [Group G]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The squared-norm half estimate for a finite-dimensional orthogonal
representation of a class-two group whose central commutators are
involutions. -/
theorem norm_orbitAverage_sq_le_half
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (X Y C : Subgroup G) [Finite X]
    (hgen : X ⊔ Y = ⊤)
    (hcomm : ⁅Y, X⁆ ≤ C)
    (hcentral : C ≤ Subgroup.center G)
    (hexp : ∀ c ∈ C, c ^ 2 = 1)
    (hno : IsKazhdanPair.HasNoInvariantVectors G rho)
    {v : E} (hvY : v ∈ KazhdanFixedSpace.fixedSubspace rho Y) :
    ‖FiniteGroupAverage.orbitAverage
        (KazhdanFixedSpace.restrictRepresentation rho X) v‖ ^ 2 ≤
      (1 / 2 : ℝ) * ‖v‖ ^ 2 := by
  classical
  let U : (C → ℝ) → Submodule ℝ E := fun chi ↦
    CentralInvolutionDecomposition.jointEigenspace rho C chi
  let dv := CentralInvolutionDecomposition.components rho C hcentral hexp v
  let w := FiniteGroupAverage.orbitAverage
    (KazhdanFixedSpace.restrictRepresentation rho X) v
  let dw := CentralInvolutionDecomposition.components rho C hcentral hexp w
  let s := dv.support ∪ dw.support
  have hcomponent (chi : C → ℝ) :
      ‖dw chi‖ ^ 2 ≤ (1 / 2 : ℝ) * ‖dv chi‖ ^ 2 := by
    by_cases hchi : U chi = ⊥
    · have hv0 : dv chi = 0 := by
        apply Subtype.ext
        have : (dv chi : E) ∈ (⊥ : Submodule ℝ E) := by
          rw [← hchi]
          exact (dv chi).2
        simpa using this
      have hw0 : dw chi = 0 := by
        apply Subtype.ext
        have : (dw chi : E) ∈ (⊥ : Submodule ℝ E) := by
          rw [← hchi]
          exact (dw chi).2
        simpa using this
      rw [hv0, hw0, norm_zero, zero_pow (by norm_num)]
      exact mul_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num)
        (show (0 : ℝ) ≤ 0 by norm_num)
    · let rhoChi := CentralInvolutionDecomposition.representation
          rho C hcentral chi
      have hnoChi : IsKazhdanPair.HasNoInvariantVectors G rhoChi := by
        intro z hz
        apply Subtype.ext
        apply hno z.1
        intro g
        have hg := congrArg Subtype.val (hz g)
        exact hg
      have hscalar : ∀ y ∈ Y, ∀ x ∈ X,
          rhoChi ⁅y, x⁆ = 1 ∨
            ∀ z, rhoChi ⁅y, x⁆ z = -z := by
        intro y hy x hx
        have hc : ⁅y, x⁆ ∈ C :=
          hcomm (Subgroup.commutator_mem_commutator hy hx)
        let cC : C := ⟨⁅y, x⁆, hc⟩
        rcases CentralInvolutionDecomposition.action_eq_or_neg_on_jointEigenspace
            rho C hexp chi hchi cC with hplus | hminus
        · left
          ext z
          change rho ⁅y, x⁆ z.1 = z.1
          exact hplus z
        · right
          intro z
          apply Subtype.ext
          change rho ⁅y, x⁆ z.1 = -z.1
          exact hminus z
      have hvChi : dv chi ∈ KazhdanFixedSpace.fixedSubspace rhoChi Y := by
        rw [KazhdanFixedSpace.mem_fixedSubspace_iff]
        intro y hy
        exact CentralInvolutionDecomposition.component_fixed
          rho C hcentral hexp
          ((KazhdanFixedSpace.mem_fixedSubspace_iff rho Y v).mp hvY y hy) chi
      have hbound :=
        FiniteClassTwoOrthogonality.norm_orbitAverage_sq_le_half_of_scalar
          rhoChi X Y hgen hnoChi hscalar hvChi
      rw [← CentralInvolutionDecomposition.component_orbitAverage
        rho C hcentral hexp X v chi] at hbound
      exact hbound
  have hsum_components (d : DirectSum (C → ℝ) (fun chi ↦ ↑(U chi)))
      (t : Finset (C → ℝ)) (hdt : d.support ⊆ t) :
      ∑ chi ∈ t, ((d chi : U chi) : E) =
        DirectSum.coeLinearMap U d := by
    have hsupp := DirectSum.sum_support_of d
    have hsmall : ∑ chi ∈ d.support, ((d chi : U chi) : E) =
        DirectSum.coeLinearMap U d := by
      have hmapped := congrArg (DirectSum.coeLinearMap U) hsupp
      simpa only [map_sum, DirectSum.coeLinearMap_of] using hmapped
    rw [← hsmall]
    symm
    apply Finset.sum_subset hdt
    intro chi _ hchiNot
    have hzero : d chi = 0 := DFinsupp.notMem_support_iff.mp hchiNot
    rw [hzero]
    rfl
  have hvsum : ∑ chi ∈ s, ((dv chi : U chi) : E) = v := by
    calc
      ∑ chi ∈ s, ((dv chi : U chi) : E) =
          DirectSum.coeLinearMap U dv :=
        hsum_components dv s Finset.subset_union_left
      _ = v := CentralInvolutionDecomposition.coeLinearMap_components
        rho C hcentral hexp v
  have hwsum : ∑ chi ∈ s, ((dw chi : U chi) : E) = w := by
    calc
      ∑ chi ∈ s, ((dw chi : U chi) : E) =
          DirectSum.coeLinearMap U dw :=
        hsum_components dw s Finset.subset_union_right
      _ = w := CentralInvolutionDecomposition.coeLinearMap_components
        rho C hcentral hexp w
  have horth :=
    CentralInvolutionDecomposition.jointEigenspaces_orthogonalFamily rho C hexp
  have hvnorm : ‖v‖ ^ 2 = ∑ chi ∈ s, ‖dv chi‖ ^ 2 := by
    rw [← hvsum]
    exact horth.norm_sum (fun chi ↦ dv chi) s
  have hwnorm : ‖w‖ ^ 2 = ∑ chi ∈ s, ‖dw chi‖ ^ 2 := by
    rw [← hwsum]
    exact horth.norm_sum (fun chi ↦ dw chi) s
  change ‖w‖ ^ 2 ≤ (1 / 2 : ℝ) * ‖v‖ ^ 2
  rw [hwnorm, hvnorm, Finset.mul_sum]
  exact Finset.sum_le_sum fun chi _ ↦ hcomponent chi

end FiniteClassTwoDecompositionBound
end NonsoficGroupsExist
