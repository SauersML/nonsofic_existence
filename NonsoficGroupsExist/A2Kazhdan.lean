import NonsoficGroupsExist.A2System
import NonsoficGroupsExist.HilbertConvexFixedPoint
import NonsoficGroupsExist.KazhdanControl

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

/-- The uniform contraction statement supplied by the six-vertex spectral
argument: in a representation without invariant vectors, a sum of six root-
fixed vectors loses a fixed proportion of the triangle-inequality bound.
This definition isolates the exact analytic conclusion to be proved from the
strong `A₂` relations; it contains no invariant vector or property-`(T)`
conclusion. -/
def FixedSumContraction (A : A2System G) (c : ℝ) : Prop :=
  ∀ (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E],
    ∀ rho : G →* (E ≃ₗᵢ[ℝ] E),
      IsKazhdanPair.HasNoInvariantVectors G rho →
      ∀ f : A2Root → E,
        (∀ a, f a ∈ KazhdanFixedSpace.fixedSubspace rho (A.rootAt a)) →
        ‖∑ a, f a‖ ≤ c * ∑ a, ‖f a‖

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

/-- The six-vertex fixed-space contraction implies that the union of the root
subgroups is a Kazhdan subset.  This is the norm-comparison step after the
spectral estimate, with an explicit (non-optimal) constant. -/
theorem rootSet_isKazhdan_of_fixedSumContraction
    (A : A2System G) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hcontract : FixedSumContraction.{u, v} A c) :
    IsKazhdanSubset.{u, v} G A.rootSet ((1 - c) / 4) := by
  have hkappa : 0 < (1 - c) / 4 := div_pos (sub_pos.mpr hc1) (by norm_num)
  refine ⟨hkappa, ?_⟩
  intro E _ _ _ rho x hx hnear
  by_contra hinv
  have hno : IsKazhdanPair.HasNoInvariantVectors G rho := by
    intro y hy
    by_contra hy0
    exact hinv ⟨y, hy0, hy⟩
  choose f hfmem hfnear using fun a ↦
    A.exists_near_root_fixedSubspace rho x hnear a
  let N : ℝ := Fintype.card A2Root
  let delta : ℝ := (1 - c) / 4
  have hN : 0 < N := a2Root_card_pos
  have herror : ‖(∑ a, f a) - N • x‖ ≤ N * delta := by
    exact norm_sum_sub_card_smul_le f x hfnear
  have hsumNorm : ∑ a, ‖f a‖ ≤ N * (1 + delta) := by
    calc
      ∑ a, ‖f a‖ ≤ ∑ _ : A2Root, (1 + delta) := by
        apply Finset.sum_le_sum
        intro a _
        have hfa : ‖f a - x‖ ≤ delta := by
          simpa [delta] using hfnear a
        calc
          ‖f a‖ = ‖(f a - x) + x‖ := by congr 1; abel
          _ ≤ ‖f a - x‖ + ‖x‖ := norm_add_le _ _
          _ ≤ delta + 1 := by rw [hx]; linarith
          _ = 1 + delta := add_comm _ _
      _ = N * (1 + delta) := by simp [N]; ring
  have hupper : ‖∑ a, f a‖ ≤ c * (N * (1 + delta)) :=
    (hcontract E rho hno f hfmem).trans
      (mul_le_mul_of_nonneg_left hsumNorm hc0)
  have hscale : ‖N • x‖ = N := by
    simp [norm_smul, hx, Real.norm_eq_abs, abs_of_pos hN]
  have hlower : N ≤ ‖∑ a, f a‖ + N * delta := by
    calc
      N = ‖N • x‖ := hscale.symm
      _ = ‖((N • x) - ∑ a, f a) + ∑ a, f a‖ := by
        congr 1
        abel
      _ ≤ ‖(N • x) - ∑ a, f a‖ + ‖∑ a, f a‖ := norm_add_le _ _
      _ = ‖(∑ a, f a) - N • x‖ + ‖∑ a, f a‖ := by
        rw [norm_sub_rev]
      _ ≤ N * delta + ‖∑ a, f a‖ := add_le_add herror le_rfl
      _ = ‖∑ a, f a‖ + N * delta := add_comm _ _
  have hbad : N ≤ N * (c * (1 + delta) + delta) := by
    calc
      N ≤ ‖∑ a, f a‖ + N * delta := hlower
      _ ≤ c * (N * (1 + delta)) + N * delta :=
        add_le_add hupper le_rfl
      _ = N * (c * (1 + delta) + delta) := by ring
  have hone : 1 ≤ c * (1 + delta) + delta := by
    apply le_of_mul_le_mul_left (a := N) (by simpa using hbad) hN
  dsimp [delta] at hone
  nlinarith [sq_nonneg (1 - c)]

end A2System
end NonsoficGroupsExist
