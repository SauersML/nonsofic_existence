import NonsoficGroupsExist.PropertyT.A2System
import NonsoficGroupsExist.Kazhdan.HilbertConvexFixedPoint
import NonsoficGroupsExist.Kazhdan.KazhdanControl
import NonsoficGroupsExist.PropertyT.NormalEdgeCodistance

/-!
# Representation geometry of an A₂ system

This file connects displacement by the six root subgroups to their closed
fixed subspaces.  These are the first analytic reductions in the EJZ
six-vertex argument; all root subgroups and all vectors are quantified over
directly.
-/

namespace NonsoficGroupsExist

universe u v

namespace A2System

variable {G : Type u} [Group G]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A uniform upper bound for the codistance of the six vertex fixed spaces.
The normalization is the standard one: `gamma = 1` is the universal
Cauchy--Schwarz bound, while `gamma < 1` is the strict gap needed by the
Kazhdan argument. -/
def VertexCodistanceBound (A : A2System G) (gamma : ℝ) : Prop :=
  ∀ (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E],
    ∀ rho : G →* (E ≃ₗᵢ[ℝ] E),
      IsKazhdanPair.HasNoInvariantVectors G rho →
      ∀ f : A2Root → E,
        (∀ a, f a ∈ KazhdanFixedSpace.fixedSubspace rho (A.vertexGroup a)) →
        ‖∑ a, f a‖ ^ 2 ≤
          Fintype.card A2Root * gamma * ∑ a, ‖f a‖ ^ 2

/-- Equivalent operator-facing target for the spectral proof: the sum of the
squared norms of the six vertex-fixed projections is uniformly bounded. -/
def VertexProjectionBound (A : A2System G) (gamma : ℝ) : Prop :=
  ∀ (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E],
    ∀ rho : G →* (E ≃ₗᵢ[ℝ] E),
      IsKazhdanPair.HasNoInvariantVectors G rho →
      ∀ x : E,
        ∑ a : A2Root,
            ‖(KazhdanFixedSpace.fixedProjection rho (A.vertexGroup a) x : E)‖ ^ 2 ≤
          Fintype.card A2Root * gamma * ‖x‖ ^ 2

/-- The projection formulation implies the standard six-subspace codistance
inequality by self-adjointness and finite Cauchy--Schwarz. -/
theorem vertexCodistanceBound_of_projectionBound
    (A : A2System G) {gamma : ℝ} (hgamma : 0 ≤ gamma)
    (hprojection : VertexProjectionBound.{u, v} A gamma) :
    VertexCodistanceBound.{u, v} A gamma := by
  intro E _ _ _ rho hno f hf
  let S : E := ∑ a, f a
  let p : A2Root → E := fun a ↦
    KazhdanFixedSpace.fixedProjection rho (A.vertexGroup a) S
  have hinner (a : A2Root) : inner ℝ (f a) S = inner ℝ (f a) (p a) := by
    let U := KazhdanFixedSpace.fixedSubspace rho (A.vertexGroup a)
    letI : CompleteSpace U :=
      (KazhdanFixedSpace.isClosed_fixedSubspace rho
        (A.vertexGroup a)).completeSpace_coe
    calc
      inner ℝ (f a) S = inner ℝ (U.starProjection (f a)) S := by
        rw [U.starProjection_eq_self_iff.mpr (hf a)]
      _ = inner ℝ (f a) (U.starProjection S) :=
        U.inner_starProjection_left_eq_right (f a) S
      _ = inner ℝ (f a) (p a) := rfl
  have hsumInner : ‖S‖ ^ 2 = ∑ a, inner ℝ (f a) (p a) := by
    calc
      ‖S‖ ^ 2 = inner ℝ S S := (real_inner_self_eq_norm_sq S).symm
      _ = ∑ a, inner ℝ (f a) S := by
        dsimp [S]
        rw [sum_inner]
      _ = ∑ a, inner ℝ (f a) (p a) := by
        apply Finset.sum_congr rfl
        intro a ha
        exact hinner a
  have hsumAbs : ‖S‖ ^ 2 ≤ ∑ a, ‖f a‖ * ‖p a‖ := by
    rw [hsumInner]
    calc
      ∑ a, inner ℝ (f a) (p a) ≤
          ∑ a, |inner ℝ (f a) (p a)| := by
        apply Finset.sum_le_sum
        intro a ha
        exact le_abs_self _
      _ ≤ ∑ a, ‖f a‖ * ‖p a‖ := by
        apply Finset.sum_le_sum
        intro a ha
        exact abs_real_inner_le_norm _ _
  have hcauchy : (∑ a, ‖f a‖ * ‖p a‖) ^ 2 ≤
      (∑ a, ‖f a‖ ^ 2) * ∑ a, ‖p a‖ ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq
      (s := (Finset.univ : Finset A2Root))
      (f := fun a ↦ ‖f a‖) (g := fun a ↦ ‖p a‖)
  have hsumSq : ‖S‖ ^ 4 ≤
      (∑ a, ‖f a‖ ^ 2) * ∑ a, ‖p a‖ ^ 2 := by
    have hsquare := sq_le_sq₀ (sq_nonneg ‖S‖)
      (Finset.sum_nonneg fun a ha ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _))
      |>.mpr hsumAbs
    calc
      ‖S‖ ^ 4 = (‖S‖ ^ 2) ^ 2 := by ring
      _ ≤ (∑ a, ‖f a‖ ^ 2) * ∑ a, ‖p a‖ ^ 2 := hsquare.trans hcauchy
  have hpbound := hprojection E rho hno S
  change ∑ a, ‖p a‖ ^ 2 ≤
    Fintype.card A2Root * gamma * ‖S‖ ^ 2 at hpbound
  by_cases hS : S = 0
  · change ‖S‖ ^ 2 ≤
      Fintype.card A2Root * gamma * ∑ a, ‖f a‖ ^ 2
    rw [hS, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) hgamma)
      (Finset.sum_nonneg fun a ha ↦ sq_nonneg _)
  · have hSnorm : 0 < ‖S‖ := norm_pos_iff.mpr hS
    have hcombine : ‖S‖ ^ 4 ≤
        (∑ a, ‖f a‖ ^ 2) *
          (Fintype.card A2Root * gamma * ‖S‖ ^ 2) :=
      hsumSq.trans (mul_le_mul_of_nonneg_left hpbound
        (Finset.sum_nonneg fun a ha ↦ sq_nonneg _))
    change ‖S‖ ^ 2 ≤
      Fintype.card A2Root * gamma * ∑ a, ‖f a‖ ^ 2
    have hspos : 0 < ‖S‖ ^ 2 := sq_pos_of_pos hSnorm
    have hcancel :
        ‖S‖ ^ 2 * ‖S‖ ^ 2 ≤
          (Fintype.card A2Root * gamma * ∑ a, ‖f a‖ ^ 2) * ‖S‖ ^ 2 := by
      calc
        ‖S‖ ^ 2 * ‖S‖ ^ 2 = ‖S‖ ^ 4 := by ring
        _ ≤ (∑ a, ‖f a‖ ^ 2) *
            (Fintype.card A2Root * gamma * ‖S‖ ^ 2) := hcombine
        _ = (Fintype.card A2Root * gamma * ∑ a, ‖f a‖ ^ 2) * ‖S‖ ^ 2 := by
          ring
    nlinarith

/-- Membership in every root fixed subspace implies global invariance because
the six root subgroups generate the group. -/
theorem invariant_of_mem_root_fixedSubspaces (A : A2System G)
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (x : E)
    (hx : ∀ a : A2Root,
      x ∈ KazhdanFixedSpace.fixedSubspace rho (A.rootAt a)) :
    ∀ g : G, rho g x = x := by
  apply KazhdanFixedSpace.invariant_of_fixed_generators rho A.rootSet
    A.rootSet_generate x
  intro g hg
  obtain ⟨a, hga⟩ := (A.mem_rootSet_iff g).mp hg
  exact (KazhdanFixedSpace.mem_fixedSubspace_iff rho (A.rootAt a) x).mp
    (hx a) g hga

/-- If every element of the root union moves `x` by less than `delta`, then
each of the six root fixed subspaces contains a point within `delta` of `x`.
The point is produced by the bounded-orbit fixed-point theorem. -/
theorem exists_near_root_fixedSubspace [CompleteSpace E]
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) {delta : ℝ}
    (hnear : ∀ g ∈ A.rootSet, ‖rho g x - x‖ < delta)
    (a : A2Root) :
    ∃ y ∈ KazhdanFixedSpace.fixedSubspace rho (A.rootAt a),
      ‖y - x‖ ≤ delta := by
  apply HilbertConvexFixedPoint.exists_near_fixedSubspace rho (A.rootAt a) x
  intro h
  exact (hnear h.1 ((A.mem_rootSet_iff h.1).2 ⟨a, h.2⟩)).le

/-- The analogous nearest-fixed-point statement for the six vertex groups. -/
theorem exists_near_vertex_fixedSubspace [CompleteSpace E]
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) {delta : ℝ}
    (hnear : ∀ g ∈ A.vertexSet, ‖rho g x - x‖ < delta)
    (a : A2Root) :
    ∃ y ∈ KazhdanFixedSpace.fixedSubspace rho (A.vertexGroup a),
      ‖y - x‖ ≤ delta := by
  apply HilbertConvexFixedPoint.exists_near_fixedSubspace rho
    (A.vertexGroup a) x
  intro h
  exact (hnear h.1 ⟨a, h.2⟩).le

/-- The six-root index is nonempty, so its real cardinality is positive. -/
theorem a2Root_card_pos : (0 : ℝ) < Fintype.card A2Root := by
  have hne : Nonempty A2Root :=
    ⟨⟨((0 : Fin 3), (1 : Fin 3)), by norm_num⟩⟩
  exact_mod_cast Fintype.card_pos_iff.mpr hne

/-- A point within `delta` of every member of a finite family has its sum
within `card * delta` of the corresponding multiple of that point. -/
theorem norm_sum_sub_card_smul_le {ι : Type*} [Fintype ι]
    (f : ι → E) (x : E) {delta : ℝ}
    (hnear : ∀ i, ‖f i - x‖ ≤ delta) :
    ‖(∑ i, f i) - (Fintype.card ι : ℝ) • x‖ ≤
      (Fintype.card ι : ℝ) * delta := by
  calc
    ‖(∑ i, f i) - (Fintype.card ι : ℝ) • x‖ =
        ‖∑ i, (f i - x)‖ := by
      congr 1
      rw [Finset.sum_sub_distrib]
      simp [Nat.cast_smul_eq_nsmul]
    _ ≤ ∑ i, ‖f i - x‖ := norm_sum_le _ _
    _ ≤ ∑ _ : ι, delta := Finset.sum_le_sum fun i _ ↦ hnear i
    _ = (Fintype.card ι : ℝ) * delta := by simp

/-- Displacement of a product is at most the sum of the two displacements. -/
theorem norm_mul_displacement_le (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (x : E) (g h : G) :
    ‖rho (g * h) x - x‖ ≤ ‖rho g x - x‖ + ‖rho h x - x‖ := by
  calc
    ‖rho (g * h) x - x‖ = ‖rho g (rho h x) - x‖ := by
      rw [map_mul]
      rfl
    _ = ‖(rho g (rho h x) - rho g x) + (rho g x - x)‖ := by
      congr 1
      abel
    _ ≤ ‖rho g (rho h x) - rho g x‖ + ‖rho g x - x‖ := norm_add_le _ _
    _ = ‖rho h x - x‖ + ‖rho g x - x‖ := by
      rw [← (rho g).map_sub, (rho g).norm_map]
    _ = ‖rho g x - x‖ + ‖rho h x - x‖ := add_comm _ _

/-- A Kazhdan bound for the six magic-graph vertex groups transfers to the
six root groups.  The loss of a factor four follows from the proved
three-factor vertex normal form (the paper obtains the sharper factor three). -/
theorem rootSet_isKazhdan_of_vertexSet
    (A : A2System G) {kappa : ℝ}
    (hvertex : IsKazhdanSubset.{u, v} G A.vertexSet kappa) :
    IsKazhdanSubset.{u, v} G A.rootSet (kappa / 4) := by
  have hquarter : 0 < kappa / 4 := div_pos hvertex.1 (by norm_num)
  refine ⟨hquarter, ?_⟩
  intro E _ _ _ rho v hv hnear
  apply hvertex.2 E rho v hv
  intro g hg
  obtain ⟨a, hga⟩ := hg
  obtain ⟨x, hx, y, hy, z, hz, rfl⟩ :=
    A.exists_vertexGroup_three_factor a hga
  have hxSet : x ∈ A.rootSet := by
    exact ⟨a.1.1, a2ThirdIndex a.1.1 a.1.2,
      (a2ThirdIndex_ne_left a.1.1 a.1.2 a.2).symm, hx⟩
  have hySet : y ∈ A.rootSet := by
    exact ⟨a2ThirdIndex a.1.1 a.1.2, a.1.2,
      a2ThirdIndex_ne_right a.1.1 a.1.2 a.2, hy⟩
  have hzSet : z ∈ A.rootSet := (A.mem_rootSet_iff z).2 ⟨a, hz⟩
  have hxyz := norm_mul_displacement_le rho v (x * y) z
  have hxy := norm_mul_displacement_le rho v x y
  calc
    ‖rho (x * y * z) v - v‖ ≤
        ‖rho (x * y) v - v‖ + ‖rho z v - v‖ := hxyz
    _ ≤ (‖rho x v - v‖ + ‖rho y v - v‖) + ‖rho z v - v‖ :=
      add_le_add hxy le_rfl
    _ < kappa := by
      have hxnear := hnear x hxSet
      have hynear := hnear y hySet
      have hznear := hnear z hzSet
      linarith

/-- In the restriction to a vertex group with no invariant vectors, the two
normal edge fixed spaces are orthogonal.  This is the direct formal analogue
of the normal-subgroup lemma used in the first half of EJZ Claim 5.6. -/
theorem edgeFixedSubspaces_isOrtho
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E)) [CompleteSpace E]
    (a : A2Root)
    (hno : IsKazhdanPair.HasNoInvariantVectors (A.vertexGroup a)
      (KazhdanFixedSpace.restrictRepresentation rho (A.vertexGroup a))) :
    KazhdanFixedSpace.fixedSubspace rho (A.leftEdgeGroup a) ⟂
      KazhdanFixedSpace.fixedSubspace rho (A.rightEdgeGroup a) := by
  let L := A.vertexGroup a
  let H := (A.leftEdgeGroup a).subgroupOf L
  let K := (A.rightEdgeGroup a).subgroupOf L
  letI : H.Normal := A.leftEdgeGroup_normalIn_vertexGroup a
  have hortho := KazhdanFixedSpace.fixedSubspaces_isOrtho_of_normal_generate
    (KazhdanFixedSpace.restrictRepresentation rho L) H K
    (A.edgeSubgroups_sup_top a) hno
  rw [KazhdanFixedSpace.fixedSubspace_subgroupOf_eq rho
      (A.leftEdgeGroup a) L (A.leftEdgeGroup_le_vertexGroup a),
    KazhdanFixedSpace.fixedSubspace_subgroupOf_eq rho
      (A.rightEdgeGroup a) L (A.rightEdgeGroup_le_vertexGroup a)] at hortho
  exact hortho

/-- The first local magic-graph estimate: four vectors fixed by the four edge
groups incident to a vertex satisfy the codistance-`1/2` inequality. -/
theorem vertex_four_fixed_norm_sq_le
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E)) [CompleteSpace E]
    (r : A2Root)
    (hno : IsKazhdanPair.HasNoInvariantVectors (A.vertexGroup r)
      (KazhdanFixedSpace.restrictRepresentation rho (A.vertexGroup r)))
    {p q s t : E}
    (hp : p ∈ KazhdanFixedSpace.fixedSubspace rho (A.leftEdgeGroup r))
    (hq : q ∈ KazhdanFixedSpace.fixedSubspace rho (A.rightEdgeGroup r))
    (hs : s ∈ KazhdanFixedSpace.fixedSubspace rho
      (A.root r.1.1 (a2ThirdIndex r.1.1 r.1.2)
        (a2ThirdIndex_ne_left r.1.1 r.1.2 r.2).symm))
    (ht : t ∈ KazhdanFixedSpace.fixedSubspace rho
      (A.root (a2ThirdIndex r.1.1 r.1.2) r.1.2
        (a2ThirdIndex_ne_right r.1.1 r.1.2 r.2))) :
    ‖p + q + s + t‖ ^ 2 ≤
      2 * (‖p‖ ^ 2 + ‖q‖ ^ 2 + ‖s‖ ^ 2 + ‖t‖ ^ 2) := by
  let X := A.root r.1.1 (a2ThirdIndex r.1.1 r.1.2)
    (a2ThirdIndex_ne_left r.1.1 r.1.2 r.2).symm
  let Y := A.root (a2ThirdIndex r.1.1 r.1.2) r.1.2
    (a2ThirdIndex_ne_right r.1.1 r.1.2 r.2)
  let Z := A.rootAt r
  have hXnorm : X ≤ Subgroup.normalizer (Z : Set G) :=
    (A.leftRoot_le_vertexGroup r).trans (A.vertexGroup_le_normalizer_rootAt r)
  have hYnorm : Y ≤ Subgroup.normalizer (Z : Set G) :=
    (A.rightRoot_le_vertexGroup r).trans (A.vertexGroup_le_normalizer_rootAt r)
  have hedge := A.edgeFixedSubspaces_isOrtho rho r hno
  exact NormalEdgeCodistance.four_fixed_norm_sq_le rho X Y Z
    hXnorm hYnorm hedge hp hq hs ht

/-- Subtype form of the local four-edge estimate.  This is the version used
after passing to the moving summand of an arbitrary vertex restriction. -/
theorem vertex_four_fixed_norm_sq_le_restricted
    (A : A2System G) (r : A2Root)
    (rho : A.vertexGroup r →* (E ≃ₗᵢ[ℝ] E)) [CompleteSpace E]
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
    ‖p + q + s + t‖ ^ 2 ≤
      2 * (‖p‖ ^ 2 + ‖q‖ ^ 2 + ‖s‖ ^ 2 + ‖t‖ ^ 2) := by
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
  apply NormalEdgeCodistance.four_fixed_norm_sq_le rho X Y Z
    hXnorm hYnorm hedge
  · simpa [hXZ] using hp
  · simpa [hYZ] using hq
  · exact hs
  · exact ht

/-- A strict uniform codistance bound makes the union of the six vertex
groups a Kazhdan subset. -/
theorem vertexSet_isKazhdan_of_codistanceBound
    (A : A2System G) {gamma : ℝ} (hgamma0 : 0 ≤ gamma)
    (hgamma1 : gamma < 1)
    (hcodistance : VertexCodistanceBound.{u, v} A gamma) :
    IsKazhdanSubset.{u, v} G A.vertexSet ((1 - gamma) / 8) := by
  let delta : ℝ := (1 - gamma) / 8
  have hdelta : 0 < delta := div_pos (sub_pos.mpr hgamma1) (by norm_num)
  have hdelta1 : delta < 1 := by
    dsimp [delta]
    nlinarith
  have hdelta0 : 0 ≤ delta := hdelta.le
  have hstrict : gamma * (1 + delta) ^ 2 < (1 - delta) ^ 2 := by
    dsimp [delta]
    nlinarith [sq_nonneg (1 - gamma)]
  refine ⟨hdelta, ?_⟩
  intro E _ _ _ rho x hx hnear
  by_contra hinv
  have hno : IsKazhdanPair.HasNoInvariantVectors G rho := by
    intro y hy
    by_contra hy0
    exact hinv ⟨y, hy0, hy⟩
  choose f hfmem hfnear using fun a ↦
    A.exists_near_vertex_fixedSubspace rho x hnear a
  let N : ℝ := Fintype.card A2Root
  have hN : 0 < N := a2Root_card_pos
  have herror : ‖(∑ a, f a) - N • x‖ ≤ N * delta := by
    exact norm_sum_sub_card_smul_le f x hfnear
  have hsumNormSq : ∑ a, ‖f a‖ ^ 2 ≤ N * (1 + delta) ^ 2 := by
    calc
      ∑ a, ‖f a‖ ^ 2 ≤ ∑ _ : A2Root, (1 + delta) ^ 2 := by
        apply Finset.sum_le_sum
        intro a _
        have hfa : ‖f a - x‖ ≤ delta := by
          simpa [delta] using hfnear a
        have hnorm : ‖f a‖ ≤ 1 + delta := by
          calc
            ‖f a‖ = ‖(f a - x) + x‖ := by congr 1; abel
            _ ≤ ‖f a - x‖ + ‖x‖ := norm_add_le _ _
            _ ≤ delta + 1 := by rw [hx]; linarith
            _ = 1 + delta := add_comm _ _
        exact (sq_le_sq₀ (norm_nonneg _) (by linarith)).mpr hnorm
      _ = N * (1 + delta) ^ 2 := by simp [N]
  have hupperSq : ‖∑ a, f a‖ ^ 2 ≤
      N ^ 2 * gamma * (1 + delta) ^ 2 := by
    calc
      ‖∑ a, f a‖ ^ 2 ≤ N * gamma * ∑ a, ‖f a‖ ^ 2 := by
        simpa [N] using hcodistance E rho hno f hfmem
      _ ≤ N * gamma * (N * (1 + delta) ^ 2) := by
        gcongr
      _ = N ^ 2 * gamma * (1 + delta) ^ 2 := by ring
  have hlower : N * (1 - delta) ≤ ‖∑ a, f a‖ := by
    have hscale : ‖N • x‖ = N := by
      simp [norm_smul, hx, Real.norm_eq_abs, abs_of_pos hN]
    have hreverse : N ≤ N * delta + ‖∑ a, f a‖ := by
      calc
        N = ‖N • x‖ := hscale.symm
        _ = ‖(N • x - ∑ a, f a) + ∑ a, f a‖ := by
          congr 1
          abel
        _ ≤ ‖N • x - ∑ a, f a‖ + ‖∑ a, f a‖ := norm_add_le _ _
        _ = ‖(∑ a, f a) - N • x‖ + ‖∑ a, f a‖ := by
          rw [norm_sub_rev]
        _ ≤ N * delta + ‖∑ a, f a‖ := add_le_add herror le_rfl
    calc
      N * (1 - delta) = N - N * delta := by ring
      _ ≤ ‖∑ a, f a‖ := by linarith
  have hlower0 : 0 ≤ N * (1 - delta) :=
    mul_nonneg hN.le (sub_nonneg.mpr hdelta1.le)
  have hlowerSq : N ^ 2 * (1 - delta) ^ 2 ≤ ‖∑ a, f a‖ ^ 2 := by
    nlinarith [sq_nonneg (‖∑ a, f a‖ - N * (1 - delta))]
  have hcontradiction : (1 - delta) ^ 2 ≤ gamma * (1 + delta) ^ 2 := by
    apply le_of_mul_le_mul_left (a := N ^ 2)
    · calc
        N ^ 2 * (1 - delta) ^ 2 ≤ ‖∑ a, f a‖ ^ 2 := hlowerSq
        _ ≤ N ^ 2 * gamma * (1 + delta) ^ 2 := hupperSq
        _ = N ^ 2 * (gamma * (1 + delta) ^ 2) := by ring
    · positivity
  exact (not_le_of_gt hstrict) hcontradiction

/-- The vertex codistance bound therefore yields a Kazhdan bound on the six
root subgroups, using the proved three-factor vertex normal form. -/
theorem rootSet_isKazhdan_of_vertexCodistanceBound
    (A : A2System G) {gamma : ℝ} (hgamma0 : 0 ≤ gamma)
    (hgamma1 : gamma < 1)
    (hcodistance : VertexCodistanceBound.{u, v} A gamma) :
    IsKazhdanSubset.{u, v} G A.rootSet ((1 - gamma) / 32) := by
  convert A.rootSet_isKazhdan_of_vertexSet
    (A.vertexSet_isKazhdan_of_codistanceBound hgamma0 hgamma1 hcodistance) using 1
  ring

end A2System
end NonsoficGroupsExist
