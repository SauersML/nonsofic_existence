import NonsoficGroupsExist.A2MagicGraphEstimates
import NonsoficGroupsExist.A2MagicLaplacian

/-!
# Global energy bookkeeping for the A₂ magic graph

This file sums the proved local characteristic-two defect over the concrete
six-vertex graph.  The definitions separate the fixed and moving components
of every oriented edge difference; their energy decomposition is orthogonal
Pythagoras, not an assumed graph certificate.
-/

namespace NonsoficGroupsExist

universe u v

namespace A2MagicEnergy

open A2MagicGraph

variable {G : Type u} [Group G]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- Difference along an oriented edge of the magic graph. -/
def edgeDifference (f : A2Root → E) (r : A2Root) (n : Fin 4) : E :=
  f r - f (neighbor r n)

/-- Component of an edge difference moving under its source vertex group. -/
noncomputable def vertexMovingEdgeComponent
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (f : A2Root → E) (r : A2Root) (n : Fin 4) : E :=
  KazhdanFixedSpace.subgroupMovingProjection rho (A.vertexGroup r)
    (edgeDifference f r n)

/-- Component of an edge difference fixed by its source vertex group. -/
noncomputable def vertexFixedEdgeComponent
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (f : A2Root → E) (r : A2Root) (n : Fin 4) : E :=
  KazhdanFixedSpace.fixedProjection rho (A.vertexGroup r)
    (edgeDifference f r n)

/-- Moving projection of the graph Laplacian at one vertex. -/
noncomputable def vertexMovingLaplacian
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (f : A2Root → E) (r : A2Root) : E :=
  KazhdanFixedSpace.subgroupMovingProjection rho (A.vertexGroup r)
    (∑ n : Fin 4, edgeDifference f r n)

/-- Directed edge energy.  Every undirected edge occurs twice. -/
def edgeEnergy (f : A2Root → E) : ℝ :=
  ∑ r : A2Root, ∑ n : Fin 4, ‖edgeDifference f r n‖ ^ 2

/-- Energy of the source-vertex moving components. -/
noncomputable def vertexMovingEdgeEnergy
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (f : A2Root → E) : ℝ :=
  ∑ r : A2Root, ∑ n : Fin 4,
    ‖vertexMovingEdgeComponent A rho f r n‖ ^ 2

/-- Energy of the source-vertex fixed components. -/
noncomputable def vertexFixedEdgeEnergy
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (f : A2Root → E) : ℝ :=
  ∑ r : A2Root, ∑ n : Fin 4,
    ‖vertexFixedEdgeComponent A rho f r n‖ ^ 2

/-- The strict root-moving energy.  At each vertex these are precisely the
two incident root edges not containing the central root subgroup. -/
noncomputable def centralMovingEdgeEnergy
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (f : A2Root → E) : ℝ :=
  ∑ r : A2Root,
    (‖centralMovingIncidentComponent A rho f r 2‖ ^ 2 +
      ‖centralMovingIncidentComponent A rho f r 3‖ ^ 2)

/-- Energy of the moving projection of the graph Laplacian. -/
noncomputable def vertexMovingLaplacianEnergy
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (f : A2Root → E) : ℝ :=
  ∑ r : A2Root, ‖vertexMovingLaplacian A rho f r‖ ^ 2

/-- Orthogonal fixed/moving decomposition of the full directed edge energy. -/
theorem edgeEnergy_eq_moving_add_fixed
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (f : A2Root → E) :
    edgeEnergy f =
      vertexMovingEdgeEnergy A rho f + vertexFixedEdgeEnergy A rho f := by
  unfold edgeEnergy vertexMovingEdgeEnergy vertexFixedEdgeEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [add_comm]
  exact KazhdanFixedSpace.norm_sq_fixedProjection_add_movingProjection
    rho (A.vertexGroup r) (edgeDifference f r n)

/-- The summed local estimate: the borderline coefficient `2` loses a
strict multiple of the characteristic-two root-moving energy. -/
theorem vertexMovingLaplacianEnergy_le_with_defect
    (A : A2System G)
    (hexp : ∀ (i j : Fin 3) (hij : i ≠ j),
      ∀ g ∈ A.root i j hij, g ^ 2 = 1)
    (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (f : A2Root → E)
    (hf : ∀ r, f r ∈ KazhdanFixedSpace.fixedSubspace rho (A.vertexGroup r)) :
    vertexMovingLaplacianEnergy A rho f ≤
      2 * vertexMovingEdgeEnergy A rho f -
        (1 - (Real.sqrt 2)⁻¹) * centralMovingEdgeEnergy A rho f := by
  unfold vertexMovingLaplacianEnergy vertexMovingEdgeEnergy
    centralMovingEdgeEnergy vertexMovingLaplacian vertexMovingEdgeComponent
    edgeDifference
  calc
    ∑ r : A2Root,
        ‖KazhdanFixedSpace.subgroupMovingProjection rho (A.vertexGroup r)
          (∑ n : Fin 4, (f r - f (neighbor r n)))‖ ^ 2 ≤
      ∑ r : A2Root,
        (2 * ∑ n : Fin 4,
            ‖KazhdanFixedSpace.subgroupMovingProjection rho (A.vertexGroup r)
              (f r - f (neighbor r n))‖ ^ 2 -
          (1 - (Real.sqrt 2)⁻¹) *
            (‖centralMovingIncidentComponent A rho f r 2‖ ^ 2 +
              ‖centralMovingIncidentComponent A rho f r 3‖ ^ 2)) := by
        apply Finset.sum_le_sum
        intro r hr
        exact incidentMovingLaplacian_norm_sq_le_with_defect
          A hexp rho f hf r
    _ = 2 * ∑ r : A2Root, ∑ n : Fin 4,
          ‖KazhdanFixedSpace.subgroupMovingProjection rho (A.vertexGroup r)
            (f r - f (neighbor r n))‖ ^ 2 -
        (1 - (Real.sqrt 2)⁻¹) *
          ∑ r : A2Root,
            (‖centralMovingIncidentComponent A rho f r 2‖ ^ 2 +
              ‖centralMovingIncidentComponent A rho f r 3‖ ^ 2) := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]

end A2MagicEnergy
end NonsoficGroupsExist
