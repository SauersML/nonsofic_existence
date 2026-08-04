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
open scoped commutatorElement

variable {G : Type u} [Group G]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- The projection identity used in EJZ Claim 5.7.  If a vector is fixed by
the two roots ending at `k`, then its projection to `Xᵢⱼ` is already its
projection to the full vertex group `Gᵢₖ`. -/
theorem fixedProjection_root_eq_vertex
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {x : E}
    (hxik : x ∈ KazhdanFixedSpace.fixedSubspace rho (A.root i k hik))
    (hxjk : x ∈ KazhdanFixedSpace.fixedSubspace rho (A.root j k hjk)) :
    (KazhdanFixedSpace.fixedProjection rho (A.root i j hij) x : E) =
      KazhdanFixedSpace.fixedProjection rho
        (A.vertexGroup ⟨(i, k), hik⟩) x := by
  let Xij := A.root i j hij
  let Xik := A.root i k hik
  let Xjk := A.root j k hjk
  let a : A2Root := ⟨(i, k), hik⟩
  have hthird : a2ThirdIndex i k = j :=
    a2ThirdIndex_eq_of_pairwise_ne i j k hij hik hjk
  have hXikV : Xik ≤ Xij ⊔ Xjk := by
    simpa [Xik, Xij, Xjk, a, A2System.vertexGroup,
      A2System.rootAt, A2System.leftRootGroup,
      A2System.rightRootGroup, hthird] using A.rootAt_le_vertexGroup a
  have hgroup : (Xij ⊔ Xik) ⊔ Xjk = A.vertexGroup a := by
    have hvertex : A.vertexGroup a = Xij ⊔ Xjk := by
      simp [a, Xij, Xjk, A2System.vertexGroup,
        A2System.leftRootGroup, A2System.rightRootGroup, hthird]
    rw [hvertex]
    apply le_antisymm
    · exact sup_le (sup_le le_sup_left hXikV) le_sup_right
    · exact sup_le (le_sup_left.trans le_sup_left) le_sup_right
  have hXikNorm : Xik ≤ Subgroup.normalizer (Xij : Set G) := by
    intro y hy
    apply Subgroup.centralizer_le_normalizer (Xij : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (A.commute i k i j hik hij hik.symm hij.symm y hy x hx).symm
  have hYX : ⁅Xjk, Xij⁆ ≤ Xik := by
    apply Subgroup.commutator_le.mpr
    intro y hy x hx
    have hxy : ⁅x, y⁆ ∈ Xik :=
      A.commutator_mem i j k hij hjk hik x hx y hy
    rw [← commutatorElement_inv x y]
    exact Xik.inv_mem hxy
  have hYZ : ⁅Xjk, Xik⁆ ≤ Xik := by
    apply Subgroup.commutator_le.mpr
    intro y hy z hz
    have hcomm : Commute y z :=
      A.commute j k i k hjk hik hik.symm hjk.symm y hy z hz
    rw [commutatorElement_eq_one_iff_commute.mpr hcomm]
    exact Xik.one_mem
  have hXjkNorm : Xjk ≤ Subgroup.normalizer (Xij ⊔ Xik : Subgroup G) :=
    ClassTwoNormalForm.le_normalizer_sup Xij Xjk Xik hYX hYZ
  have hp1 := KazhdanFixedSpace.fixedProjection_eq_sup_of_fixed_of_normalizes
    rho Xij Xik hXikNorm hxik
  have hp2 := KazhdanFixedSpace.fixedProjection_eq_sup_of_fixed_of_normalizes
    rho (Xij ⊔ Xik) Xjk hXjkNorm hxjk
  change (KazhdanFixedSpace.fixedProjection rho Xij x : E) =
    KazhdanFixedSpace.fixedProjection rho (A.vertexGroup a) x
  calc
    (KazhdanFixedSpace.fixedProjection rho Xij x : E) =
        KazhdanFixedSpace.fixedProjection rho (Xij ⊔ Xik) x := hp1
    _ = KazhdanFixedSpace.fixedProjection rho ((Xij ⊔ Xik) ⊔ Xjk) x := hp2
    _ = KazhdanFixedSpace.fixedProjection rho (A.vertexGroup a) x := by
      rw [hgroup]

/-- Concrete edge-difference instance of `fixedProjection_root_eq_vertex`.
The required two root invariances follow from the endpoint vertex groups. -/
theorem fixedProjection_root_edgeDifference_eq_vertex
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (f : A2Root → E)
    (hf : ∀ r, f r ∈ KazhdanFixedSpace.fixedSubspace rho (A.vertexGroup r))
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    let rik : A2Root := ⟨(i, k), hik⟩
    let rjk : A2Root := ⟨(j, k), hjk⟩
    (KazhdanFixedSpace.fixedProjection rho (A.root i j hij)
        (f rik - f rjk) : E) =
      KazhdanFixedSpace.fixedProjection rho (A.vertexGroup rik)
        (f rik - f rjk) := by
  let rik : A2Root := ⟨(i, k), hik⟩
  let rjk : A2Root := ⟨(j, k), hjk⟩
  have hthirdIK : a2ThirdIndex i k = j :=
    a2ThirdIndex_eq_of_pairwise_ne i j k hij hik hjk
  have hthirdJK : a2ThirdIndex j k = i :=
    a2ThirdIndex_eq_of_pairwise_ne j i k hij.symm hjk hik
  have hXik_rik : A.root i k hik ≤ A.vertexGroup rik := by
    simpa [rik, A2System.rootAt] using A.rootAt_le_vertexGroup rik
  have hXik_rjk : A.root i k hik ≤ A.vertexGroup rjk := by
    simpa [rjk, A2System.rightRootGroup, hthirdJK] using
      A.rightRoot_le_vertexGroup rjk
  have hXjk_rik : A.root j k hjk ≤ A.vertexGroup rik := by
    simpa [rik, A2System.rightRootGroup, hthirdIK] using
      A.rightRoot_le_vertexGroup rik
  have hXjk_rjk : A.root j k hjk ≤ A.vertexGroup rjk := by
    simpa [rjk, A2System.rootAt] using A.rootAt_le_vertexGroup rjk
  have hxik : f rik - f rjk ∈
      KazhdanFixedSpace.fixedSubspace rho (A.root i k hik) :=
    (KazhdanFixedSpace.fixedSubspace rho (A.root i k hik)).sub_mem
      (KazhdanFixedSpace.antitone rho hXik_rik (hf rik))
      (KazhdanFixedSpace.antitone rho hXik_rjk (hf rjk))
  have hxjk : f rik - f rjk ∈
      KazhdanFixedSpace.fixedSubspace rho (A.root j k hjk) :=
    (KazhdanFixedSpace.fixedSubspace rho (A.root j k hjk)).sub_mem
      (KazhdanFixedSpace.antitone rho hXjk_rik (hf rik))
      (KazhdanFixedSpace.antitone rho hXjk_rjk (hf rjk))
  exact fixedProjection_root_eq_vertex A rho i j k hij hik hjk hxik hxjk

/-- Equation (5.8) of the magic-graph proof, with all three vertices and
projections explicit. -/
theorem triangle_edge_norm_sq_eq
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (f : A2Root → E)
    (hf : ∀ r, f r ∈ KazhdanFixedSpace.fixedSubspace rho (A.vertexGroup r))
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    let rij : A2Root := ⟨(i, j), hij⟩
    let rik : A2Root := ⟨(i, k), hik⟩
    let rjk : A2Root := ⟨(j, k), hjk⟩
    ‖f rik - f rjk‖ ^ 2 =
      ‖(KazhdanFixedSpace.fixedProjection rho (A.vertexGroup rik)
          (f rik - f rjk) : E)‖ ^ 2 +
        ‖KazhdanFixedSpace.subgroupMovingProjection rho (A.rootAt rij)
          (f rij - f rjk)‖ ^ 2 := by
  let rij : A2Root := ⟨(i, j), hij⟩
  let rik : A2Root := ⟨(i, k), hik⟩
  let rjk : A2Root := ⟨(j, k), hjk⟩
  let Xij := A.root i j hij
  have hthirdIK : a2ThirdIndex i k = j :=
    a2ThirdIndex_eq_of_pairwise_ne i j k hij hik hjk
  have hXij_rij : Xij ≤ A.vertexGroup rij := by
    simpa [Xij, rij, A2System.rootAt] using A.rootAt_le_vertexGroup rij
  have hXij_rik : Xij ≤ A.vertexGroup rik := by
    simpa [Xij, rik, A2System.leftRootGroup, hthirdIK] using
      A.leftRoot_le_vertexGroup rik
  have hfixed : f rik - f rij ∈ KazhdanFixedSpace.fixedSubspace rho Xij :=
    (KazhdanFixedSpace.fixedSubspace rho Xij).sub_mem
      (KazhdanFixedSpace.antitone rho hXij_rik (hf rik))
      (KazhdanFixedSpace.antitone rho hXij_rij (hf rij))
  have hzero : KazhdanFixedSpace.subgroupMovingProjection rho Xij
      (f rik - f rij) = 0 :=
    KazhdanFixedSpace.subgroupMovingProjection_eq_zero_of_mem rho Xij hfixed
  have hmove : KazhdanFixedSpace.subgroupMovingProjection rho Xij
      (f rik - f rjk) =
      KazhdanFixedSpace.subgroupMovingProjection rho Xij
        (f rij - f rjk) := by
    have hdecomp : f rik - f rjk =
        (f rik - f rij) + (f rij - f rjk) := by module
    rw [hdecomp, map_add, hzero, zero_add]
  have hpyth := KazhdanFixedSpace.norm_sq_fixedProjection_add_movingProjection
    rho Xij (f rik - f rjk)
  have hproj := fixedProjection_root_edgeDifference_eq_vertex
    A rho f hf i j k hij hik hjk
  change ‖f rik - f rjk‖ ^ 2 =
    ‖(KazhdanFixedSpace.fixedProjection rho (A.vertexGroup rik)
        (f rik - f rjk) : E)‖ ^ 2 +
      ‖KazhdanFixedSpace.subgroupMovingProjection rho (A.rootAt rij)
        (f rij - f rjk)‖ ^ 2
  change (KazhdanFixedSpace.fixedProjection rho Xij
      (f rik - f rjk) : E) =
    KazhdanFixedSpace.fixedProjection rho (A.vertexGroup rik)
      (f rik - f rjk) at hproj
  have hroot : A.rootAt rij = Xij := rfl
  rw [hroot]
  change ‖f rik - f rjk‖ ^ 2 =
    ‖(KazhdanFixedSpace.fixedProjection rho (A.vertexGroup rik)
        (f rik - f rjk) : E)‖ ^ 2 +
      ‖KazhdanFixedSpace.subgroupMovingProjection rho Xij
        (f rij - f rjk)‖ ^ 2
  rw [← hproj, ← hmove]
  exact hpyth

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

/-- The unprojected magic-graph Laplacian on the root-indexed vertices. -/
def rootLaplacian (f : A2Root → E) (r : A2Root) : E :=
  ∑ n : Fin 4, edgeDifference f r n

/-- Sum and integral centering on the root-indexed form of the graph. -/
def rootTotal (f : A2Root → E) : E := ∑ r, f r

def rootCentered (f : A2Root → E) (r : A2Root) : E :=
  6 • f r - rootTotal f

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- The explicit enumeration intertwines the two Laplacian definitions. -/
theorem rootLaplacian_vertex (f : A2Root → E) (i : Fin 6) :
    rootLaplacian f (vertex i) =
      A2MagicLaplacian.laplacian (fun j ↦ f (vertex j)) i := by
  simp [rootLaplacian, edgeDifference, A2MagicLaplacian.laplacian]

omit [CompleteSpace E] in
/-- The proved eigenvalue-four gap, transported to the actual root index. -/
theorem rootCentered_norm_sq_le_rootLaplacian_norm_sq
    (f : A2Root → E) :
    16 * ∑ r : A2Root, ‖rootCentered f r‖ ^ 2 ≤
      ∑ r : A2Root, ‖6 • rootLaplacian f r‖ ^ 2 := by
  let g : Fin 6 → E := fun i ↦ f (vertexEquiv i)
  have htotal : A2MagicLaplacian.total g = rootTotal f := by
    exact Equiv.sum_comp vertexEquiv f
  have hcenter (i : Fin 6) :
      A2MagicLaplacian.centered g i = rootCentered f (vertexEquiv i) := by
    change 6 • f (vertexEquiv i) - A2MagicLaplacian.total g =
      6 • f (vertexEquiv i) - rootTotal f
    rw [htotal]
  have hlap (i : Fin 6) :
      A2MagicLaplacian.laplacian g i = rootLaplacian f (vertexEquiv i) := by
    symm
    exact rootLaplacian_vertex f i
  have h := A2MagicLaplacian.centered_norm_sq_le_laplacian_norm_sq g
  rw [show (∑ r : A2Root, ‖rootCentered f r‖ ^ 2) =
      ∑ i : Fin 6, ‖rootCentered f (vertexEquiv i)‖ ^ 2 by
        exact (Equiv.sum_comp vertexEquiv
          (fun r ↦ ‖rootCentered f r‖ ^ 2)).symm]
  rw [show (∑ r : A2Root, ‖6 • rootLaplacian f r‖ ^ 2) =
      ∑ i : Fin 6, ‖6 • rootLaplacian f (vertexEquiv i)‖ ^ 2 by
        exact (Equiv.sum_comp vertexEquiv
          (fun r ↦ ‖6 • rootLaplacian f r‖ ^ 2)).symm]
  simpa only [hcenter, hlap] using h

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
