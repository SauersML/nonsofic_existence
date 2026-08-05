import NonsoficGroupsExist.A2Kazhdan
import NonsoficGroupsExist.A2ClassTwoOrthogonality
import NonsoficGroupsExist.A2MagicGraph

/-!
# Local energy estimates on the A₂ magic graph

At each vertex the four incident edge differences lie in the four fixed
spaces from the local codistance theorem.  This file records the resulting
energy inequality without any abstract graph certificate.
-/

namespace NonsoficGroupsExist

universe u v

namespace A2MagicGraph

variable {G : Type u} [Group G]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- In a vertex restriction without invariant vectors, the sum of its four
incident edge differences has squared norm at most twice their energy. -/
theorem incidentDifference_norm_sq_le
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (f : A2Root → E)
    (hf : ∀ r, f r ∈ KazhdanFixedSpace.fixedSubspace rho (A.vertexGroup r))
    (r : A2Root)
    (hno : IsKazhdanPair.HasNoInvariantVectors (A.vertexGroup r)
      (KazhdanFixedSpace.restrictRepresentation rho (A.vertexGroup r))) :
    ‖∑ n : Fin 4, (f r - f (neighbor r n))‖ ^ 2 ≤
      2 * ∑ n : Fin 4, ‖f r - f (neighbor r n)‖ ^ 2 := by
  let d : Fin 4 → E := fun n ↦ f r - f (neighbor r n)
  have hd (n : Fin 4) : d n ∈
      KazhdanFixedSpace.fixedSubspace rho (edgeGroup A r n) :=
    vertexFixed_sub_neighbor_mem_edgeFixed A rho f hf r n
  have hlocal := A.vertex_four_fixed_norm_sq_le rho r hno
    (p := d 0) (q := d 1) (s := d 2) (t := d 3)
    (by simpa [edgeGroup] using hd 0)
    (by simpa [edgeGroup] using hd 1)
    (by simpa [edgeGroup, A2System.leftRootGroup] using hd 2)
    (by simpa [edgeGroup, A2System.rightRootGroup] using hd 3)
  change ‖∑ n : Fin 4, d n‖ ^ 2 ≤ 2 * ∑ n : Fin 4, ‖d n‖ ^ 2
  simpa [Fin.sum_univ_succ, add_assoc] using hlocal

/-- For an arbitrary global representation, project the four incident edge
differences to the moving summand of the vertex restriction.  The same local
energy estimate holds there, now without assuming that the original vertex
restriction has no invariant vectors. -/
theorem incidentMovingProjection_norm_sq_le
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (f : A2Root → E)
    (hf : ∀ r, f r ∈ KazhdanFixedSpace.fixedSubspace rho (A.vertexGroup r))
    (r : A2Root) :
    let L := A.vertexGroup r
    let W := KazhdanFixedSpace.subgroupMovingSubspace rho L
    let d : Fin 4 → E := fun n ↦ f r - f (neighbor r n)
    let p : Fin 4 → W := fun n ↦
      ⟨KazhdanFixedSpace.subgroupMovingProjection rho L (d n),
        KazhdanFixedSpace.subgroupMovingProjection_mem rho L (d n)⟩
    ‖∑ n : Fin 4, p n‖ ^ 2 ≤ 2 * ∑ n : Fin 4, ‖p n‖ ^ 2 := by
  let L := A.vertexGroup r
  let W := KazhdanFixedSpace.subgroupMovingSubspace rho L
  letI : CompleteSpace W := by
    dsimp [W, KazhdanFixedSpace.subgroupMovingSubspace]
    exact (KazhdanFixedSpace.fixedSubspace rho L).isClosed_orthogonal.completeSpace_coe
  let rhoW := KazhdanFixedSpace.subgroupMovingRepresentation rho L
  let d : Fin 4 → E := fun n ↦ f r - f (neighbor r n)
  let p : Fin 4 → W := fun n ↦
    ⟨KazhdanFixedSpace.subgroupMovingProjection rho L (d n),
      KazhdanFixedSpace.subgroupMovingProjection_mem rho L (d n)⟩
  have hd (n : Fin 4) : d n ∈
      KazhdanFixedSpace.fixedSubspace rho (edgeGroup A r n) :=
    vertexFixed_sub_neighbor_mem_edgeFixed A rho f hf r n
  have hp (n : Fin 4) : p n ∈ KazhdanFixedSpace.fixedSubspace rhoW
      ((edgeGroup A r n).subgroupOf L) := by
    have hproj := KazhdanFixedSpace.subgroupMovingProjection_mem_fixedSubspace
      rho (edgeGroup A r n) L (edgeGroup_le_sourceVertex A r n) (hd n)
    rw [KazhdanFixedSpace.mem_fixedSubspace_iff]
    intro h hh
    apply Subtype.ext
    exact (KazhdanFixedSpace.mem_fixedSubspace_iff rho
      (edgeGroup A r n)
      (KazhdanFixedSpace.subgroupMovingProjection rho L (d n))).mp
        hproj h.1 (Subgroup.mem_subgroupOf.mp hh)
  have hlocal := A.vertex_four_fixed_norm_sq_le_restricted r rhoW
    (KazhdanFixedSpace.subgroupMovingRepresentation_hasNoInvariantVectors rho L)
    (p := p 0) (q := p 1) (s := p 2) (t := p 3)
    (by simpa [edgeGroup] using hp 0)
    (by simpa [edgeGroup] using hp 1)
    (by simpa [edgeGroup, A2System.leftRootGroup] using hp 2)
    (by simpa [edgeGroup, A2System.rightRootGroup] using hp 3)
  change ‖∑ n : Fin 4, p n‖ ^ 2 ≤ 2 * ∑ n : Fin 4, ‖p n‖ ^ 2
  simpa [Fin.sum_univ_succ, add_assoc] using hlocal

/-- On the component orthogonal to the central sum-root fixed space, the two
root components satisfy the strict bounded-exponent bound. -/
theorem centerMovingRoot_norm_sq_le_of_root_boundedExponent
    (A : A2System G)
    (n : ℕ) (hn : 0 < n)
    (hexp : ∀ (i j : Fin 3) (hij : i ≠ j),
      ∀ g ∈ A.root i j hij, g ^ n = 1)
    (r : A2Root)
    (rho : A.vertexGroup r →* (E ≃ₗᵢ[ℝ] E))
    (hno : IsKazhdanPair.HasNoInvariantVectors (A.vertexGroup r) rho)
    {s t : E}
    (hs : s ∈ KazhdanFixedSpace.fixedSubspace rho
      ((A.leftRootGroup r).subgroupOf (A.vertexGroup r)))
    (ht : t ∈ KazhdanFixedSpace.fixedSubspace rho
      ((A.rightRootGroup r).subgroupOf (A.vertexGroup r))) :
    let Z := (A.rootAt r).subgroupOf (A.vertexGroup r)
    let sN := s - KazhdanFixedSpace.fixedProjection rho Z s
    let tN := t - KazhdanFixedSpace.fixedProjection rho Z t
    ‖sN + tN‖ ^ 2 ≤ (1 + (Real.sqrt 2)⁻¹) *
      (‖sN‖ ^ 2 + ‖tN‖ ^ 2) := by
  let L := A.vertexGroup r
  let X := (A.leftRootGroup r).subgroupOf L
  let Y := (A.rightRootGroup r).subgroupOf L
  let Z := (A.rootAt r).subgroupOf L
  let sL : E := KazhdanFixedSpace.fixedProjection rho Z s
  let tL : E := KazhdanFixedSpace.fixedProjection rho Z t
  let sN : E := s - sL
  let tN : E := t - tL
  have hZcenter : Z ≤ Subgroup.center L := A.rootAt_subgroupOf_le_center r
  have hXnorm : X ≤ Subgroup.normalizer (Z : Set L) := by
    intro x hx
    apply Subgroup.centralizer_le_normalizer (Z : Set L)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_center_iff.mp (hZcenter hz) x).symm
  have hYnorm : Y ≤ Subgroup.normalizer (Z : Set L) := by
    intro y hy
    apply Subgroup.centralizer_le_normalizer (Z : Set L)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_center_iff.mp (hZcenter hz) y).symm
  have hsLX : sL ∈ KazhdanFixedSpace.fixedSubspace rho X := by
    rw [KazhdanFixedSpace.mem_fixedSubspace_iff]
    intro x hx
    have hsx : rho x s = s :=
      (KazhdanFixedSpace.mem_fixedSubspace_iff rho X s).mp hs x hx
    calc
      rho x sL = (KazhdanFixedSpace.fixedProjection rho Z (rho x s) : E) :=
        (KazhdanFixedSpace.fixedProjection_equivariant_of_mem_normalizer
          rho Z (hXnorm hx) s).symm
      _ = sL := by rw [hsx]
  have htLY : tL ∈ KazhdanFixedSpace.fixedSubspace rho Y := by
    rw [KazhdanFixedSpace.mem_fixedSubspace_iff]
    intro y hy
    have hty : rho y t = t :=
      (KazhdanFixedSpace.mem_fixedSubspace_iff rho Y t).mp ht y hy
    calc
      rho y tL = (KazhdanFixedSpace.fixedProjection rho Z (rho y t) : E) :=
        (KazhdanFixedSpace.fixedProjection_equivariant_of_mem_normalizer
          rho Z (hYnorm hy) t).symm
      _ = tL := by rw [hty]
  have hsNX : sN ∈ KazhdanFixedSpace.fixedSubspace rho X :=
    (KazhdanFixedSpace.fixedSubspace rho X).sub_mem hs hsLX
  have htNY : tN ∈ KazhdanFixedSpace.fixedSubspace rho Y :=
    (KazhdanFixedSpace.fixedSubspace rho Y).sub_mem ht htLY
  have hangle :=
    A.rootFixedSubspaces_epsilonOrthogonal_restricted_of_root_boundedExponent
      n hn hexp r rho hno
  exact HilbertEpsilonOrthogonality.norm_add_sq_le
    (by positivity) hangle hsNX htNY

/-- Defect form of the four-edge estimate in the moving representation of a
vertex group.  The deficit is exactly the energy of the two root-edge
components orthogonal to the central root fixed space. -/
theorem vertex_four_fixed_norm_sq_le_restricted_with_defect
    (A : A2System G)
    (n : ℕ) (hn : 0 < n)
    (hexp : ∀ (i j : Fin 3) (hij : i ≠ j),
      ∀ g ∈ A.root i j hij, g ^ n = 1)
    (r : A2Root)
    (rho : A.vertexGroup r →* (E ≃ₗᵢ[ℝ] E))
    (hno : IsKazhdanPair.HasNoInvariantVectors (A.vertexGroup r) rho)
    {p q s t : E}
    (hp : p ∈ KazhdanFixedSpace.fixedSubspace rho
      ((A.leftEdgeGroup r).subgroupOf (A.vertexGroup r)))
    (hq : q ∈ KazhdanFixedSpace.fixedSubspace rho
      ((A.rightEdgeGroup r).subgroupOf (A.vertexGroup r)))
    (hs : s ∈ KazhdanFixedSpace.fixedSubspace rho
      ((A.leftRootGroup r).subgroupOf (A.vertexGroup r)))
    (ht : t ∈ KazhdanFixedSpace.fixedSubspace rho
      ((A.rightRootGroup r).subgroupOf (A.vertexGroup r))) :
    let Z := (A.rootAt r).subgroupOf (A.vertexGroup r)
    let sN := s - KazhdanFixedSpace.fixedProjection rho Z s
    let tN := t - KazhdanFixedSpace.fixedProjection rho Z t
    ‖p + q + s + t‖ ^ 2 ≤
      2 * (‖p‖ ^ 2 + ‖q‖ ^ 2 + ‖s‖ ^ 2 + ‖t‖ ^ 2) -
        (1 - (Real.sqrt 2)⁻¹) * (‖sN‖ ^ 2 + ‖tN‖ ^ 2) := by
  let L := A.vertexGroup r
  let X := (A.leftRootGroup r).subgroupOf L
  let Y := (A.rightRootGroup r).subgroupOf L
  let Z := (A.rootAt r).subgroupOf L
  let H := (A.leftEdgeGroup r).subgroupOf L
  let K := (A.rightEdgeGroup r).subgroupOf L
  have hXZ : X ⊔ Z = H := by
    rw [← Subgroup.subgroupOf_sup (A.leftRoot_le_vertexGroup r)
      (A.rootAt_le_vertexGroup r)]
    rfl
  have hYZ : Y ⊔ Z = K := by
    rw [← Subgroup.subgroupOf_sup (A.rightRoot_le_vertexGroup r)
      (A.rootAt_le_vertexGroup r)]
    rfl
  have hZcenter : Z ≤ Subgroup.center L := A.rootAt_subgroupOf_le_center r
  have hXnorm : X ≤ Subgroup.normalizer (Z : Set L) := by
    intro x hx
    apply Subgroup.centralizer_le_normalizer (Z : Set L)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_center_iff.mp (hZcenter hz) x).symm
  have hYnorm : Y ≤ Subgroup.normalizer (Z : Set L) := by
    intro y hy
    apply Subgroup.centralizer_le_normalizer (Z : Set L)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_center_iff.mp (hZcenter hz) y).symm
  letI : H.Normal := A.leftEdgeGroup_normalIn_vertexGroup r
  have hedgeHK := KazhdanFixedSpace.fixedSubspaces_isOrtho_of_normal_generate
    rho H K (A.edgeSubgroups_sup_top r) hno
  have hedge : KazhdanFixedSpace.fixedSubspace rho (X ⊔ Z) ⟂
      KazhdanFixedSpace.fixedSubspace rho (Y ⊔ Z) := by
    simpa [hXZ, hYZ] using hedgeHK
  have hangle :=
    A.rootFixedSubspaces_epsilonOrthogonal_restricted_of_root_boundedExponent
      n hn hexp r rho hno
  apply NormalEdgeCodistance.four_fixed_norm_sq_le_with_defect
    rho X Y Z (by positivity) hXnorm hYnorm hedge
  · simpa [X, Y] using hangle
  · simpa [hXZ] using hp
  · simpa [hYZ] using hq
  · exact hs
  · exact ht

/-- The component of an incident edge difference which moves both under the
vertex group and under its central root subgroup.  Completeness of the
nested moving space is constructed internally, so this is a closed concrete
definition rather than a certificate parameter. -/
noncomputable def centralMovingIncidentComponent
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (f : A2Root → E) (r : A2Root) (n : Fin 4) : E :=
  KazhdanFixedSpace.nestedMovingProjection rho (A.rootAt r)
    (A.vertexGroup r) (A.rootAt_le_vertexGroup r)
    (f r - f (neighbor r n))

/-- The nested component is exactly direct movement relative to the central
root subgroup. -/
theorem centralMovingIncidentComponent_eq
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (f : A2Root → E) (r : A2Root) (n : Fin 4) :
    centralMovingIncidentComponent A rho f r n =
      KazhdanFixedSpace.subgroupMovingProjection rho (A.rootAt r)
        (f r - f (neighbor r n)) :=
  KazhdanFixedSpace.nestedMovingProjection_eq rho (A.rootAt r)
    (A.vertexGroup r) (A.rootAt_le_vertexGroup r)
    (f r - f (neighbor r n))

/-- The local defect estimate applied to the four oriented edge differences
of a vertex-fixed family.  All projections here are constructed from the
given representation; no local no-invariants hypothesis is supplied. -/
theorem incidentMovingProjection_norm_sq_le_with_defect
    (A : A2System G)
    (n : ℕ) (hn : 0 < n)
    (hexp : ∀ (i j : Fin 3) (hij : i ≠ j),
      ∀ g ∈ A.root i j hij, g ^ n = 1)
    (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (f : A2Root → E)
    (hf : ∀ r, f r ∈ KazhdanFixedSpace.fixedSubspace rho (A.vertexGroup r))
    (r : A2Root) :
    let L := A.vertexGroup r
    let W := KazhdanFixedSpace.subgroupMovingSubspace rho L
    let d : Fin 4 → E := fun n ↦ f r - f (neighbor r n)
    let p : Fin 4 → W := fun n ↦
      ⟨KazhdanFixedSpace.subgroupMovingProjection rho L (d n),
        KazhdanFixedSpace.subgroupMovingProjection_mem rho L (d n)⟩
    ‖∑ n : Fin 4, p n‖ ^ 2 ≤
      2 * ∑ n : Fin 4, ‖p n‖ ^ 2 -
        (1 - (Real.sqrt 2)⁻¹) *
          (‖centralMovingIncidentComponent A rho f r 2‖ ^ 2 +
            ‖centralMovingIncidentComponent A rho f r 3‖ ^ 2) := by
  let L := A.vertexGroup r
  let W := KazhdanFixedSpace.subgroupMovingSubspace rho L
  letI : CompleteSpace W := by
    dsimp [W, KazhdanFixedSpace.subgroupMovingSubspace]
    exact (KazhdanFixedSpace.fixedSubspace rho L).isClosed_orthogonal.completeSpace_coe
  let rhoW := KazhdanFixedSpace.subgroupMovingRepresentation rho L
  let d : Fin 4 → E := fun n ↦ f r - f (neighbor r n)
  let p : Fin 4 → W := fun n ↦
    ⟨KazhdanFixedSpace.subgroupMovingProjection rho L (d n),
      KazhdanFixedSpace.subgroupMovingProjection_mem rho L (d n)⟩
  let Z := (A.rootAt r).subgroupOf L
  let sN : W := p 2 - KazhdanFixedSpace.fixedProjection rhoW Z (p 2)
  let tN : W := p 3 - KazhdanFixedSpace.fixedProjection rhoW Z (p 3)
  have hd (n : Fin 4) : d n ∈
      KazhdanFixedSpace.fixedSubspace rho (edgeGroup A r n) :=
    vertexFixed_sub_neighbor_mem_edgeFixed A rho f hf r n
  have hp (n : Fin 4) : p n ∈ KazhdanFixedSpace.fixedSubspace rhoW
      ((edgeGroup A r n).subgroupOf L) := by
    exact KazhdanFixedSpace.subgroupMovingProjection_mem_restricted_fixedSubspace
      rho (edgeGroup A r n) L (edgeGroup_le_sourceVertex A r n) (hd n)
  have hlocal := vertex_four_fixed_norm_sq_le_restricted_with_defect
    A n hn hexp r rhoW
    (KazhdanFixedSpace.subgroupMovingRepresentation_hasNoInvariantVectors rho L)
    (p := p 0) (q := p 1) (s := p 2) (t := p 3)
    (by simpa [edgeGroup] using hp 0)
    (by simpa [edgeGroup] using hp 1)
    (by simpa [edgeGroup, A2System.leftRootGroup] using hp 2)
    (by simpa [edgeGroup, A2System.rightRootGroup] using hp 3)
  simpa [Fin.sum_univ_succ, add_assoc, Z, sN, tN,
    centralMovingIncidentComponent, KazhdanFixedSpace.nestedMovingProjection,
    L, W, rhoW, d, p] using hlocal

/-- E-valued form of the preceding estimate: the sum of the four moving
edge components is the moving projection of the graph Laplacian at the
vertex. -/
theorem incidentMovingLaplacian_norm_sq_le_with_defect
    (A : A2System G)
    (n : ℕ) (hn : 0 < n)
    (hexp : ∀ (i j : Fin 3) (hij : i ≠ j),
      ∀ g ∈ A.root i j hij, g ^ n = 1)
    (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (f : A2Root → E)
    (hf : ∀ r, f r ∈ KazhdanFixedSpace.fixedSubspace rho (A.vertexGroup r))
    (r : A2Root) :
    let L := A.vertexGroup r
    let d : Fin 4 → E := fun n ↦ f r - f (neighbor r n)
    ‖KazhdanFixedSpace.subgroupMovingProjection rho L (∑ n, d n)‖ ^ 2 ≤
      2 * ∑ n, ‖KazhdanFixedSpace.subgroupMovingProjection rho L (d n)‖ ^ 2 -
        (1 - (Real.sqrt 2)⁻¹) *
          (‖centralMovingIncidentComponent A rho f r 2‖ ^ 2 +
            ‖centralMovingIncidentComponent A rho f r 3‖ ^ 2) := by
  have h := incidentMovingProjection_norm_sq_le_with_defect
    A n hn hexp rho f hf r
  simpa [KazhdanFixedSpace.subgroupMovingProjection] using h

/-- The moving components of the first two incident edges are orthogonal.
Their edge subgroups are normal and together generate the source vertex
group. -/
theorem incidentFirstSecondMoving_inner_eq_zero
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (f : A2Root → E)
    (hf : ∀ r, f r ∈ KazhdanFixedSpace.fixedSubspace rho (A.vertexGroup r))
    (r : A2Root) :
    inner ℝ
      (KazhdanFixedSpace.subgroupMovingProjection rho (A.vertexGroup r)
        (f r - f (neighbor r 0)))
      (KazhdanFixedSpace.subgroupMovingProjection rho (A.vertexGroup r)
        (f r - f (neighbor r 1))) = 0 := by
  let L := A.vertexGroup r
  let W := KazhdanFixedSpace.subgroupMovingSubspace rho L
  letI : CompleteSpace W := by
    dsimp [W, KazhdanFixedSpace.subgroupMovingSubspace]
    exact (KazhdanFixedSpace.fixedSubspace rho L).isClosed_orthogonal.completeSpace_coe
  let rhoW := KazhdanFixedSpace.subgroupMovingRepresentation rho L
  let H := (A.leftEdgeGroup r).subgroupOf L
  let K := (A.rightEdgeGroup r).subgroupOf L
  let d : Fin 4 → E := fun n ↦ f r - f (neighbor r n)
  let p : Fin 4 → W := fun n ↦
    ⟨KazhdanFixedSpace.subgroupMovingProjection rho L (d n),
      KazhdanFixedSpace.subgroupMovingProjection_mem rho L (d n)⟩
  have hd (n : Fin 4) : d n ∈
      KazhdanFixedSpace.fixedSubspace rho (edgeGroup A r n) :=
    vertexFixed_sub_neighbor_mem_edgeFixed A rho f hf r n
  have hp (n : Fin 4) : p n ∈ KazhdanFixedSpace.fixedSubspace rhoW
      ((edgeGroup A r n).subgroupOf L) :=
    KazhdanFixedSpace.subgroupMovingProjection_mem_restricted_fixedSubspace
      rho (edgeGroup A r n) L (edgeGroup_le_sourceVertex A r n) (hd n)
  letI : H.Normal := A.leftEdgeGroup_normalIn_vertexGroup r
  have hedge := KazhdanFixedSpace.fixedSubspaces_isOrtho_of_normal_generate
    rhoW H K (A.edgeSubgroups_sup_top r)
      (KazhdanFixedSpace.subgroupMovingRepresentation_hasNoInvariantVectors rho L)
  have hinner : inner ℝ (p 0) (p 1) = 0 :=
    hedge.inner_eq (by simpa [H, edgeGroup] using hp 0)
      (by simpa [K, edgeGroup] using hp 1)
  exact hinner

end A2MagicGraph
end NonsoficGroupsExist
