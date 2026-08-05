import NonsoficGroupsExist.ScaledStreamRepresentation
import NonsoficGroupsExist.VandermondeExtraction

/-!
# Graded independence over an infinite field

The scaled stream representations separate the degree components of
the binary Leavitt algebra: a vanishing finite sum of pure-degree
elements has vanishing components.  Scaling multiplies the degree-`d`
component by `c^d`, the Vandermonde extraction kills each image, and
faithfulness of the stream representation kills each component.
-/

namespace NonsoficGroupsExist
namespace BinaryLeavitt

variable (K : Type) [Field K] [Infinite K]

/-- **Graded independence**: over an infinite field, a vanishing
finite sum of pure-degree elements has all components zero. -/
theorem graded_independence (D : Finset ℤ)
    (x : ℤ → BinaryLeavittAlgebra K)
    (hx : ∀ d ∈ D, x d ∈
      Submodule.span K ((family K).degreeMonomials d d))
    (hsum : ∑ d ∈ D, x d = 0) : ∀ d ∈ D, x d = 0 := by
  have hkill : ∀ d ∈ D, streamRepresentation K (x d) = 0 := by
    refine eq_zero_of_forall_units_zpow_smul (K := K)
      (V := Module.End K (StreamSpace K)) D
      (fun d ↦ streamRepresentation K (x d)) ?_
    intro c
    have h1 := congrArg (scaledStreamRepresentation K c) hsum
    rw [map_sum, map_zero] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun d hd ↦ ?_
    exact (scaledStreamRepresentation_degree K c d (hx d hd)).symm
  intro d hd
  exact streamRepresentation_injective K
    (by rw [hkill d hd, map_zero])

end BinaryLeavitt
end NonsoficGroupsExist
