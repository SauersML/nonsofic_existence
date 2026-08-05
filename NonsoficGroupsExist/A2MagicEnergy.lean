import NonsoficGroupsExist.A2MagicGraphEstimates
import NonsoficGroupsExist.A2MagicLaplacian

/-!
# Global energy bookkeeping for the A₂ magic graph

This file sums the proved local bounded-exponent defect over the concrete
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

/-- The companion projection identity with the other generating root first.
If a vector is fixed by `Xᵢⱼ` and `Xᵢₖ`, its `Xⱼₖ`-projection is its full
`Gᵢₖ`-projection. -/
theorem fixedProjection_other_root_eq_vertex
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {x : E}
    (hxij : x ∈ KazhdanFixedSpace.fixedSubspace rho (A.root i j hij))
    (hxik : x ∈ KazhdanFixedSpace.fixedSubspace rho (A.root i k hik)) :
    (KazhdanFixedSpace.fixedProjection rho (A.root j k hjk) x : E) =
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
  have hgroup : (Xjk ⊔ Xik) ⊔ Xij = A.vertexGroup a := by
    have hvertex : A.vertexGroup a = Xij ⊔ Xjk := by
      simp [a, Xij, Xjk, A2System.vertexGroup,
        A2System.leftRootGroup, A2System.rightRootGroup, hthird]
    rw [hvertex]
    apply le_antisymm
    · exact sup_le (sup_le le_sup_right hXikV) le_sup_left
    · exact sup_le le_sup_right (le_sup_left.trans le_sup_left)
  have hXikNorm : Xik ≤ Subgroup.normalizer (Xjk : Set G) := by
    intro z hz
    apply Subgroup.centralizer_le_normalizer (Xjk : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact A.commute j k i k hjk hik hik.symm hjk.symm y hy z hz
  have hYX : ⁅Xij, Xjk⁆ ≤ Xik := by
    apply Subgroup.commutator_le.mpr
    intro x hx y hy
    exact A.commutator_mem i j k hij hjk hik x hx y hy
  have hYZ : ⁅Xij, Xik⁆ ≤ Xik := by
    apply Subgroup.commutator_le.mpr
    intro x hx z hz
    have hcomm : Commute x z :=
      A.commute i j i k hij hik hij.symm hik.symm x hx z hz
    rw [commutatorElement_eq_one_iff_commute.mpr hcomm]
    exact Xik.one_mem
  have hXijNorm : Xij ≤ Subgroup.normalizer (Xjk ⊔ Xik : Subgroup G) :=
    ClassTwoNormalForm.le_normalizer_sup Xjk Xij Xik hYX hYZ
  have hp1 := KazhdanFixedSpace.fixedProjection_eq_sup_of_fixed_of_normalizes
    rho Xjk Xik hXikNorm hxik
  have hp2 := KazhdanFixedSpace.fixedProjection_eq_sup_of_fixed_of_normalizes
    rho (Xjk ⊔ Xik) Xij hXijNorm hxij
  change (KazhdanFixedSpace.fixedProjection rho Xjk x : E) =
    KazhdanFixedSpace.fixedProjection rho (A.vertexGroup a) x
  calc
    (KazhdanFixedSpace.fixedProjection rho Xjk x : E) =
        KazhdanFixedSpace.fixedProjection rho (Xjk ⊔ Xik) x := hp1
    _ = KazhdanFixedSpace.fixedProjection rho ((Xjk ⊔ Xik) ⊔ Xij) x := hp2
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

/-- Equation (5.9), strengthened to equality by retaining the full
fixed/moving orthogonal decomposition. -/
theorem triangle_second_edge_norm_sq_eq
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (f : A2Root → E)
    (hf : ∀ r, f r ∈ KazhdanFixedSpace.fixedSubspace rho (A.vertexGroup r))
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    let rij : A2Root := ⟨(i, j), hij⟩
    let rik : A2Root := ⟨(i, k), hik⟩
    let rjk : A2Root := ⟨(j, k), hjk⟩
    ‖f rik - f rij‖ ^ 2 =
      ‖(KazhdanFixedSpace.fixedProjection rho (A.vertexGroup rik)
          (f rik - f rij) : E)‖ ^ 2 +
        ‖KazhdanFixedSpace.subgroupMovingProjection rho (A.rootAt rjk)
          (f rjk - f rij)‖ ^ 2 := by
  let rij : A2Root := ⟨(i, j), hij⟩
  let rik : A2Root := ⟨(i, k), hik⟩
  let rjk : A2Root := ⟨(j, k), hjk⟩
  let Xij := A.root i j hij
  let Xik := A.root i k hik
  let Xjk := A.root j k hjk
  have hthirdIK : a2ThirdIndex i k = j :=
    a2ThirdIndex_eq_of_pairwise_ne i j k hij hik hjk
  have hthirdIJ : a2ThirdIndex i j = k :=
    a2ThirdIndex_eq_of_pairwise_ne i k j hik hij hjk.symm
  have hXij_rik : Xij ≤ A.vertexGroup rik := by
    simpa [Xij, rik, A2System.leftRootGroup, hthirdIK] using
      A.leftRoot_le_vertexGroup rik
  have hXij_rij : Xij ≤ A.vertexGroup rij := by
    simpa [Xij, rij, A2System.rootAt] using A.rootAt_le_vertexGroup rij
  have hXik_rik : Xik ≤ A.vertexGroup rik := by
    simpa [Xik, rik, A2System.rootAt] using A.rootAt_le_vertexGroup rik
  have hXik_rij : Xik ≤ A.vertexGroup rij := by
    simpa [Xik, rij, A2System.leftRootGroup, hthirdIJ] using
      A.leftRoot_le_vertexGroup rij
  have hxij : f rik - f rij ∈ KazhdanFixedSpace.fixedSubspace rho Xij :=
    (KazhdanFixedSpace.fixedSubspace rho Xij).sub_mem
      (KazhdanFixedSpace.antitone rho hXij_rik (hf rik))
      (KazhdanFixedSpace.antitone rho hXij_rij (hf rij))
  have hxik : f rik - f rij ∈ KazhdanFixedSpace.fixedSubspace rho Xik :=
    (KazhdanFixedSpace.fixedSubspace rho Xik).sub_mem
      (KazhdanFixedSpace.antitone rho hXik_rik (hf rik))
      (KazhdanFixedSpace.antitone rho hXik_rij (hf rij))
  have hproj := fixedProjection_other_root_eq_vertex
    A rho i j k hij hik hjk hxij hxik
  have hXjk_rik : Xjk ≤ A.vertexGroup rik := by
    simpa [Xjk, rik, A2System.rightRootGroup, hthirdIK] using
      A.rightRoot_le_vertexGroup rik
  have hXjk_rjk : Xjk ≤ A.vertexGroup rjk := by
    simpa [Xjk, rjk, A2System.rootAt] using A.rootAt_le_vertexGroup rjk
  have hfixed : f rik - f rjk ∈ KazhdanFixedSpace.fixedSubspace rho Xjk :=
    (KazhdanFixedSpace.fixedSubspace rho Xjk).sub_mem
      (KazhdanFixedSpace.antitone rho hXjk_rik (hf rik))
      (KazhdanFixedSpace.antitone rho hXjk_rjk (hf rjk))
  have hzero : KazhdanFixedSpace.subgroupMovingProjection rho Xjk
      (f rik - f rjk) = 0 :=
    KazhdanFixedSpace.subgroupMovingProjection_eq_zero_of_mem rho Xjk hfixed
  have hmove : KazhdanFixedSpace.subgroupMovingProjection rho Xjk
      (f rik - f rij) =
      KazhdanFixedSpace.subgroupMovingProjection rho Xjk
        (f rjk - f rij) := by
    have hdecomp : f rik - f rij =
        (f rik - f rjk) + (f rjk - f rij) := by module
    rw [hdecomp, map_add, hzero, zero_add]
  have hpyth := KazhdanFixedSpace.norm_sq_fixedProjection_add_movingProjection
    rho Xjk (f rik - f rij)
  change ‖f rik - f rij‖ ^ 2 =
    ‖(KazhdanFixedSpace.fixedProjection rho (A.vertexGroup rik)
        (f rik - f rij) : E)‖ ^ 2 +
      ‖KazhdanFixedSpace.subgroupMovingProjection rho (A.rootAt rjk)
        (f rjk - f rij)‖ ^ 2
  change (KazhdanFixedSpace.fixedProjection rho Xjk
      (f rik - f rij) : E) =
    KazhdanFixedSpace.fixedProjection rho (A.vertexGroup rik)
      (f rik - f rij) at hproj
  have hroot : A.rootAt rjk = Xjk := rfl
  rw [hroot]
  change ‖f rik - f rij‖ ^ 2 =
    ‖(KazhdanFixedSpace.fixedProjection rho (A.vertexGroup rik)
        (f rik - f rij) : E)‖ ^ 2 +
      ‖KazhdanFixedSpace.subgroupMovingProjection rho Xjk
        (f rjk - f rij)‖ ^ 2
  rw [← hproj, ← hmove]
  exact hpyth

/-- Equation (5.10): the third side of an A₂ triangle is controlled by the
fixed and moving components of the two sides meeting at `Gᵢₖ`. -/
theorem triangle_third_edge_norm_sq_le
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (f : A2Root → E)
    (hf : ∀ r, f r ∈ KazhdanFixedSpace.fixedSubspace rho (A.vertexGroup r))
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    let rij : A2Root := ⟨(i, j), hij⟩
    let rik : A2Root := ⟨(i, k), hik⟩
    let rjk : A2Root := ⟨(j, k), hjk⟩
    let L := A.vertexGroup rik
    let a := f rij - f rik
    let b := f rik - f rjk
    ‖f rij - f rjk‖ ^ 2 ≤
      2 * (‖(KazhdanFixedSpace.fixedProjection rho L a : E)‖ ^ 2 +
        ‖(KazhdanFixedSpace.fixedProjection rho L b : E)‖ ^ 2) +
      ‖KazhdanFixedSpace.subgroupMovingProjection rho L a‖ ^ 2 +
      ‖KazhdanFixedSpace.subgroupMovingProjection rho L b‖ ^ 2 := by
  let rij : A2Root := ⟨(i, j), hij⟩
  let rik : A2Root := ⟨(i, k), hik⟩
  let rjk : A2Root := ⟨(j, k), hjk⟩
  let L := A.vertexGroup rik
  let a : E := f rij - f rik
  let b : E := f rik - f rjk
  let c : E := f rij - f rjk
  have hthird : a2ThirdIndex i k = j :=
    a2ThirdIndex_eq_of_pairwise_ne i j k hij hik hjk
  have hn0 : neighbor rik 0 = rij := by
    apply Subtype.ext
    simp [neighbor, rik, rij, hthird]
  have hn1 : neighbor rik 1 = rjk := by
    apply Subtype.ext
    simp [neighbor, rik, rjk, hthird]
  have hbase := incidentFirstSecondMoving_inner_eq_zero A rho f hf rik
  rw [hn0, hn1] at hbase
  have ha : a = -(f rik - f rij) := by
    dsimp [a]
    module
  have horth : inner ℝ
      (KazhdanFixedSpace.subgroupMovingProjection rho L a)
      (KazhdanFixedSpace.subgroupMovingProjection rho L b) = 0 := by
    rw [ha, map_neg, inner_neg_left]
    exact neg_eq_zero.mpr hbase
  have hc : c = a + b := by
    dsimp [a, b, c]
    module
  have hfixed : (KazhdanFixedSpace.fixedProjection rho L c : E) =
      (KazhdanFixedSpace.fixedProjection rho L a : E) +
        KazhdanFixedSpace.fixedProjection rho L b := by
    rw [hc, map_add]
    rfl
  have hmoving : KazhdanFixedSpace.subgroupMovingProjection rho L c =
      KazhdanFixedSpace.subgroupMovingProjection rho L a +
        KazhdanFixedSpace.subgroupMovingProjection rho L b := by
    rw [hc, map_add]
  have hfixedBound := HilbertEpsilonOrthogonality.norm_add_sq_le_two
    (KazhdanFixedSpace.fixedProjection rho L a : E)
    (KazhdanFixedSpace.fixedProjection rho L b : E)
  have hmovingEq : ‖KazhdanFixedSpace.subgroupMovingProjection rho L c‖ ^ 2 =
      ‖KazhdanFixedSpace.subgroupMovingProjection rho L a‖ ^ 2 +
        ‖KazhdanFixedSpace.subgroupMovingProjection rho L b‖ ^ 2 := by
    rw [hmoving]
    simpa [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_real horth
  have hpyth := KazhdanFixedSpace.norm_sq_fixedProjection_add_movingProjection
    rho L c
  change ‖c‖ ^ 2 ≤
    2 * (‖(KazhdanFixedSpace.fixedProjection rho L a : E)‖ ^ 2 +
      ‖(KazhdanFixedSpace.fixedProjection rho L b : E)‖ ^ 2) +
    ‖KazhdanFixedSpace.subgroupMovingProjection rho L a‖ ^ 2 +
    ‖KazhdanFixedSpace.subgroupMovingProjection rho L b‖ ^ 2
  rw [hpyth, hfixed, hmovingEq]
  nlinarith

/-- The three estimates combine with coefficients `3` and `5`, which is the
per-triangle form of EJZ Claim 5.7(a). -/
theorem triangle_total_energy_le_three_root_add_five_vertex
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (f : A2Root → E)
    (hf : ∀ r, f r ∈ KazhdanFixedSpace.fixedSubspace rho (A.vertexGroup r))
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    let rij : A2Root := ⟨(i, j), hij⟩
    let rik : A2Root := ⟨(i, k), hik⟩
    let rjk : A2Root := ⟨(j, k), hjk⟩
    let L := A.vertexGroup rik
    let a := f rij - f rik
    let b := f rik - f rjk
    let c := f rij - f rjk
    ‖a‖ ^ 2 + ‖b‖ ^ 2 + 2 * ‖c‖ ^ 2 ≤
      5 * (‖(KazhdanFixedSpace.fixedProjection rho L a : E)‖ ^ 2 +
        ‖(KazhdanFixedSpace.fixedProjection rho L b : E)‖ ^ 2) +
      3 * (‖KazhdanFixedSpace.subgroupMovingProjection rho (A.rootAt rij) c‖ ^ 2 +
        ‖KazhdanFixedSpace.subgroupMovingProjection rho (A.rootAt rjk) (-c)‖ ^ 2) := by
  let rij : A2Root := ⟨(i, j), hij⟩
  let rik : A2Root := ⟨(i, k), hik⟩
  let rjk : A2Root := ⟨(j, k), hjk⟩
  let L := A.vertexGroup rik
  let a : E := f rij - f rik
  let b : E := f rik - f rjk
  let c : E := f rij - f rjk
  have h8 := triangle_edge_norm_sq_eq A rho f hf i j k hij hik hjk
  have h9 := triangle_second_edge_norm_sq_eq A rho f hf i j k hij hik hjk
  have h10 := triangle_third_edge_norm_sq_le A rho f hf i j k hij hik hjk
  dsimp only at h8 h9 h10
  have haNeg : f rik - f rij = -a := by
    dsimp [a]
    module
  have hcNeg : f rjk - f rij = -c := by
    dsimp [c]
    module
  rw [haNeg, map_neg, norm_neg, hcNeg] at h9
  simp only [Submodule.coe_neg, norm_neg] at h9
  have hpythA := KazhdanFixedSpace.norm_sq_fixedProjection_add_movingProjection
    rho L a
  have hpythB := KazhdanFixedSpace.norm_sq_fixedProjection_add_movingProjection
    rho L b
  change ‖a‖ ^ 2 + ‖b‖ ^ 2 + 2 * ‖c‖ ^ 2 ≤
    5 * (‖(KazhdanFixedSpace.fixedProjection rho L a : E)‖ ^ 2 +
      ‖(KazhdanFixedSpace.fixedProjection rho L b : E)‖ ^ 2) +
    3 * (‖KazhdanFixedSpace.subgroupMovingProjection rho (A.rootAt rij) c‖ ^ 2 +
      ‖KazhdanFixedSpace.subgroupMovingProjection rho (A.rootAt rjk) (-c)‖ ^ 2)
  change ‖b‖ ^ 2 =
    ‖(KazhdanFixedSpace.fixedProjection rho L b : E)‖ ^ 2 +
      ‖KazhdanFixedSpace.subgroupMovingProjection rho (A.rootAt rij) c‖ ^ 2 at h8
  change ‖a‖ ^ 2 =
    ‖(KazhdanFixedSpace.fixedProjection rho L a : E)‖ ^ 2 +
      ‖KazhdanFixedSpace.subgroupMovingProjection rho (A.rootAt rjk) (-c)‖ ^ 2 at h9
  change ‖c‖ ^ 2 ≤
    2 * (‖(KazhdanFixedSpace.fixedProjection rho L a : E)‖ ^ 2 +
      ‖(KazhdanFixedSpace.fixedProjection rho L b : E)‖ ^ 2) +
    ‖KazhdanFixedSpace.subgroupMovingProjection rho L a‖ ^ 2 +
    ‖KazhdanFixedSpace.subgroupMovingProjection rho L b‖ ^ 2 at h10
  nlinarith

/-- The six ordered triples of distinct coordinates. -/
def tripleI : Fin 6 → Fin 3 := ![0, 0, 1, 1, 2, 2]
def tripleJ : Fin 6 → Fin 3 := ![1, 2, 0, 2, 0, 1]
def tripleK : Fin 6 → Fin 3 := ![2, 1, 2, 0, 1, 0]

theorem tripleI_ne_tripleJ (t : Fin 6) : tripleI t ≠ tripleJ t := by
  fin_cases t <;> decide

theorem tripleI_ne_tripleK (t : Fin 6) : tripleI t ≠ tripleK t := by
  fin_cases t <;> decide

theorem tripleJ_ne_tripleK (t : Fin 6) : tripleJ t ≠ tripleK t := by
  fin_cases t <;> decide

def tripleIJ (t : Fin 6) : A2Root :=
  ⟨(tripleI t, tripleJ t), tripleI_ne_tripleJ t⟩

def tripleIK (t : Fin 6) : A2Root :=
  ⟨(tripleI t, tripleK t), tripleI_ne_tripleK t⟩

def tripleJK (t : Fin 6) : A2Root :=
  ⟨(tripleJ t, tripleK t), tripleJ_ne_tripleK t⟩

def tripleIKIndex : Fin 6 → Fin 6 := ![1, 0, 3, 2, 5, 4]
def tripleJKIndex : Fin 6 → Fin 6 := ![3, 5, 1, 4, 0, 2]

noncomputable def tripleIKEquiv : Fin 6 ≃ Fin 6 :=
  Equiv.ofBijective tripleIKIndex ⟨by
    intro s t h
    fin_cases s <;> fin_cases t <;> simp_all [tripleIKIndex], by
    intro t
    fin_cases t
    · exact ⟨1, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨5, rfl⟩
    · exact ⟨4, rfl⟩⟩

noncomputable def tripleJKEquiv : Fin 6 ≃ Fin 6 :=
  Equiv.ofBijective tripleJKIndex ⟨by
    intro s t h
    fin_cases s <;> fin_cases t <;> simp_all [tripleJKIndex], by
    intro t
    fin_cases t
    · exact ⟨4, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨5, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨1, rfl⟩⟩

@[simp] theorem tripleIKEquiv_apply (t : Fin 6) :
    tripleIKEquiv t = tripleIKIndex t := rfl

@[simp] theorem tripleJKEquiv_apply (t : Fin 6) :
    tripleJKEquiv t = tripleJKIndex t := rfl

@[simp] theorem tripleIJ_eq_vertex (t : Fin 6) : tripleIJ t = vertex t := by
  fin_cases t <;> apply Subtype.ext <;> rfl

@[simp] theorem tripleIK_eq_vertex (t : Fin 6) :
    tripleIK t = vertex (tripleIKIndex t) := by
  fin_cases t <;> apply Subtype.ext <;> rfl

@[simp] theorem tripleJK_eq_vertex (t : Fin 6) :
    tripleJK t = vertex (tripleJKIndex t) := by
  fin_cases t <;> apply Subtype.ext <;> rfl

@[simp] theorem neighborIndex_tripleIK_zero (t : Fin 6) :
    neighborIndex (tripleIKIndex t) 0 = t := by
  fin_cases t <;> rfl

@[simp] theorem neighborIndex_tripleIK_one (t : Fin 6) :
    neighborIndex (tripleIKIndex t) 1 = tripleJKIndex t := by
  fin_cases t <;> rfl

@[simp] theorem neighborIndex_two (t : Fin 6) :
    neighborIndex t 2 = tripleJKIndex t := by
  fin_cases t <;> rfl

@[simp] theorem neighborIndex_tripleJK_three (t : Fin 6) :
    neighborIndex (tripleJKIndex t) 3 = t := by
  fin_cases t <;> rfl

@[simp] theorem neighbor_vertex_tripleIK_zero (t : Fin 6) :
    neighbor (vertex (tripleIKIndex t)) 0 = vertex t := by
  rw [← vertex_neighborIndex, neighborIndex_tripleIK_zero]

@[simp] theorem neighbor_vertex_tripleIK_one (t : Fin 6) :
    neighbor (vertex (tripleIKIndex t)) 1 = vertex (tripleJKIndex t) := by
  rw [← vertex_neighborIndex, neighborIndex_tripleIK_one]

@[simp] theorem neighbor_vertex_two (t : Fin 6) :
    neighbor (vertex t) 2 = vertex (tripleJKIndex t) := by
  rw [← vertex_neighborIndex, neighborIndex_two]

@[simp] theorem neighbor_vertex_tripleJK_three (t : Fin 6) :
    neighbor (vertex (tripleJKIndex t)) 3 = vertex t := by
  rw [← vertex_neighborIndex, neighborIndex_tripleJK_three]

/-- The three-edge energy attached to one ordered coordinate triple. -/
def triangleEnergy (f : A2Root → E) (t : Fin 6) : ℝ :=
  ‖f (tripleIJ t) - f (tripleIK t)‖ ^ 2 +
    ‖f (tripleIK t) - f (tripleJK t)‖ ^ 2 +
      2 * ‖f (tripleIJ t) - f (tripleJK t)‖ ^ 2

/-- The two source-vertex fixed components in one triangle. -/
noncomputable def triangleVertexFixedEnergy
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (f : A2Root → E) (t : Fin 6) : ℝ :=
  let rik := tripleIK t
  ‖(KazhdanFixedSpace.fixedProjection rho (A.vertexGroup rik)
      (f (tripleIJ t) - f rik) : E)‖ ^ 2 +
    ‖(KazhdanFixedSpace.fixedProjection rho (A.vertexGroup rik)
      (f rik - f (tripleJK t)) : E)‖ ^ 2

/-- The two strict root-moving components in one triangle. -/
noncomputable def triangleRootMovingEnergy
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (f : A2Root → E) (t : Fin 6) : ℝ :=
  let rij := tripleIJ t
  let rjk := tripleJK t
  let c := f rij - f rjk
  ‖KazhdanFixedSpace.subgroupMovingProjection rho (A.rootAt rij) c‖ ^ 2 +
    ‖KazhdanFixedSpace.subgroupMovingProjection rho (A.rootAt rjk) (-c)‖ ^ 2

/-- Claim 5.7(a) on each of the six explicit ordered triples. -/
theorem triangleEnergy_le
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (f : A2Root → E)
    (hf : ∀ r, f r ∈ KazhdanFixedSpace.fixedSubspace rho (A.vertexGroup r))
    (t : Fin 6) :
    triangleEnergy f t ≤
      3 * triangleRootMovingEnergy A rho f t +
        5 * triangleVertexFixedEnergy A rho f t := by
  have h := triangle_total_energy_le_three_root_add_five_vertex A rho f hf
    (tripleI t) (tripleJ t) (tripleK t)
    (tripleI_ne_tripleJ t) (tripleI_ne_tripleK t)
    (tripleJ_ne_tripleK t)
  calc
    triangleEnergy f t ≤
        5 * triangleVertexFixedEnergy A rho f t +
          3 * triangleRootMovingEnergy A rho f t := by
      unfold triangleEnergy triangleRootMovingEnergy triangleVertexFixedEnergy
      exact h
    _ = 3 * triangleRootMovingEnergy A rho f t +
        5 * triangleVertexFixedEnergy A rho f t := add_comm _ _

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

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- The six triangle energies enumerate the full directed edge energy. -/
theorem sum_triangleEnergy (f : A2Root → E) :
    ∑ t : Fin 6, triangleEnergy f t = edgeEnergy f := by
  let e : Fin 6 → Fin 4 → ℝ := fun i n ↦
    ‖f (vertex i) - f (vertex (neighborIndex i n))‖ ^ 2
  have h0 : (∑ t : Fin 6,
      ‖f (tripleIJ t) - f (tripleIK t)‖ ^ 2) = ∑ i, e i 0 := by
    calc
      _ = ∑ t : Fin 6, e (tripleIKEquiv t) 0 := by
        apply Finset.sum_congr rfl
        intro t ht
        simp only [tripleIJ_eq_vertex, tripleIK_eq_vertex,
          tripleIKEquiv_apply]
        unfold e
        rw [neighborIndex_tripleIK_zero, norm_sub_rev]
      _ = ∑ i, e i 0 := Equiv.sum_comp tripleIKEquiv (fun i ↦ e i 0)
  have h1 : (∑ t : Fin 6,
      ‖f (tripleIK t) - f (tripleJK t)‖ ^ 2) = ∑ i, e i 1 := by
    calc
      _ = ∑ t : Fin 6, e (tripleIKEquiv t) 1 := by
        apply Finset.sum_congr rfl
        intro t ht
        simp only [tripleIK_eq_vertex, tripleJK_eq_vertex,
          tripleIKEquiv_apply]
        unfold e
        rw [neighborIndex_tripleIK_one]
      _ = ∑ i, e i 1 := Equiv.sum_comp tripleIKEquiv (fun i ↦ e i 1)
  have h2 : (∑ t : Fin 6,
      ‖f (tripleIJ t) - f (tripleJK t)‖ ^ 2) = ∑ i, e i 2 := by
    apply Finset.sum_congr rfl
    intro t ht
    simp only [tripleIJ_eq_vertex, tripleJK_eq_vertex]
    unfold e
    rw [neighborIndex_two]
  have h3 : (∑ i : Fin 6, e i 3) = ∑ i, e i 2 := by
    calc
      _ = ∑ t : Fin 6, e (tripleJKEquiv t) 3 :=
        (Equiv.sum_comp tripleJKEquiv (fun i ↦ e i 3)).symm
      _ = ∑ i, e i 2 := by
        apply Finset.sum_congr rfl
        intro t ht
        simp only [tripleJKEquiv_apply]
        unfold e
        rw [neighborIndex_tripleJK_three, neighborIndex_two, norm_sub_rev]
  have hedge : edgeEnergy f =
      (∑ i, e i 0) + (∑ i, e i 1) + (∑ i, e i 2) + ∑ i, e i 3 := by
    calc
      edgeEnergy f = ∑ i : Fin 6, ∑ n : Fin 4, e i n := by
        unfold edgeEnergy
        rw [← Equiv.sum_comp vertexEquiv]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro n hn
        simp [e, edgeDifference]
      _ = ∑ i : Fin 6, (e i 0 + e i 1 + e i 2 + e i 3) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [Fin.sum_univ_succ]
        ring
      _ = (∑ i, e i 0) + (∑ i, e i 1) +
          (∑ i, e i 2) + ∑ i, e i 3 := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.sum_add_distrib]
  calc
    ∑ t : Fin 6, triangleEnergy f t =
        (∑ i, e i 0) + (∑ i, e i 1) + 2 * ∑ i, e i 2 := by
      unfold triangleEnergy
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, h0, h1]
      rw [← Finset.mul_sum, h2]
    _ = (∑ i, e i 0) + (∑ i, e i 1) +
        (∑ i, e i 2) + ∑ i, e i 3 := by rw [h3]; ring
    _ = edgeEnergy f := hedge.symm

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

/-- The fixed terms selected by the six triangle inequalities are bounded by
the full source-vertex fixed edge energy; the omitted two incidences at each
vertex have nonnegative energy. -/
theorem sum_triangleVertexFixedEnergy_le
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (f : A2Root → E) :
    ∑ t : Fin 6, triangleVertexFixedEnergy A rho f t ≤
      vertexFixedEdgeEnergy A rho f := by
  let e : Fin 6 → Fin 4 → ℝ := fun i n ↦
    ‖vertexFixedEdgeComponent A rho f (vertex i) n‖ ^ 2
  have ht (t : Fin 6) : triangleVertexFixedEnergy A rho f t =
      e (tripleIKEquiv t) 0 + e (tripleIKEquiv t) 1 := by
    unfold triangleVertexFixedEnergy e vertexFixedEdgeComponent edgeDifference
    simp only [tripleIJ_eq_vertex, tripleIK_eq_vertex, tripleJK_eq_vertex,
      tripleIKEquiv_apply]
    have hneg : f (vertex t) - f (vertex (tripleIKIndex t)) =
        -(f (vertex (tripleIKIndex t)) - f (vertex t)) := by module
    rw [hneg, map_neg]
    simp only [Submodule.coe_neg, norm_neg]
    rw [neighbor_vertex_tripleIK_zero, neighbor_vertex_tripleIK_one]
    rw [tripleIK_eq_vertex]
    congr 1
  have hselected : (∑ t : Fin 6,
      triangleVertexFixedEnergy A rho f t) =
      (∑ i : Fin 6, e i 0) + ∑ i : Fin 6, e i 1 := by
    calc
      _ = ∑ t : Fin 6,
          (e (tripleIKEquiv t) 0 + e (tripleIKEquiv t) 1) := by
        apply Finset.sum_congr rfl
        intro t hmem
        exact ht t
      _ = (∑ t : Fin 6, e (tripleIKEquiv t) 0) +
          ∑ t : Fin 6, e (tripleIKEquiv t) 1 := Finset.sum_add_distrib
      _ = (∑ i : Fin 6, e i 0) + ∑ i : Fin 6, e i 1 := by
        rw [Equiv.sum_comp tripleIKEquiv (fun i ↦ e i 0),
          Equiv.sum_comp tripleIKEquiv (fun i ↦ e i 1)]
  have hfull : vertexFixedEdgeEnergy A rho f =
      (∑ i : Fin 6, e i 0) + (∑ i, e i 1) +
        (∑ i, e i 2) + ∑ i, e i 3 := by
    calc
      vertexFixedEdgeEnergy A rho f =
          ∑ i : Fin 6, ∑ n : Fin 4, e i n := by
        unfold vertexFixedEdgeEnergy
        rw [← Equiv.sum_comp vertexEquiv]
        rfl
      _ = ∑ i : Fin 6, (e i 0 + e i 1 + e i 2 + e i 3) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [Fin.sum_univ_succ]
        ring
      _ = (∑ i : Fin 6, e i 0) + (∑ i, e i 1) +
          (∑ i, e i 2) + ∑ i, e i 3 := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.sum_add_distrib]
  rw [hselected, hfull]
  have hn2 : 0 ≤ ∑ i : Fin 6, e i 2 :=
    Finset.sum_nonneg fun i hi ↦ sq_nonneg _
  have hn3 : 0 ≤ ∑ i : Fin 6, e i 3 :=
    Finset.sum_nonneg fun i hi ↦ sq_nonneg _
  linarith

/-- The strict root-moving energy.  At each vertex these are precisely the
two incident root edges not containing the central root subgroup. -/
noncomputable def centralMovingEdgeEnergy
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (f : A2Root → E) : ℝ :=
  ∑ r : A2Root,
    (‖centralMovingIncidentComponent A rho f r 2‖ ^ 2 +
      ‖centralMovingIncidentComponent A rho f r 3‖ ^ 2)

/-- The strict terms in the six triangle inequalities enumerate exactly the
two central-root-moving incidences at every vertex. -/
theorem sum_triangleRootMovingEnergy
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (f : A2Root → E) :
    ∑ t : Fin 6, triangleRootMovingEnergy A rho f t =
      centralMovingEdgeEnergy A rho f := by
  let c : Fin 6 → Fin 4 → ℝ := fun i n ↦
    ‖centralMovingIncidentComponent A rho f (vertex i) n‖ ^ 2
  have ht (t : Fin 6) : triangleRootMovingEnergy A rho f t =
      c t 2 + c (tripleJKEquiv t) 3 := by
    unfold triangleRootMovingEnergy c
    simp only [tripleIJ_eq_vertex, tripleJK_eq_vertex,
      tripleJKEquiv_apply]
    rw [centralMovingIncidentComponent_eq,
      centralMovingIncidentComponent_eq]
    rw [neighbor_vertex_two, neighbor_vertex_tripleJK_three]
    simp only [neg_sub]
  calc
    ∑ t : Fin 6, triangleRootMovingEnergy A rho f t =
        ∑ t : Fin 6, (c t 2 + c (tripleJKEquiv t) 3) := by
      apply Finset.sum_congr rfl
      intro t hmem
      exact ht t
    _ = (∑ t : Fin 6, c t 2) + ∑ t : Fin 6, c (tripleJKEquiv t) 3 :=
      Finset.sum_add_distrib
    _ = (∑ t : Fin 6, c t 2) + ∑ t : Fin 6, c t 3 := by
      rw [Equiv.sum_comp tripleJKEquiv (fun t ↦ c t 3)]
    _ = centralMovingEdgeEnergy A rho f := by
      unfold centralMovingEdgeEnergy
      rw [← Equiv.sum_comp vertexEquiv]
      rw [Finset.sum_add_distrib]
      rfl

/-- EJZ Claim 5.7(a) on the full magic graph, in the directed-edge
normalization used by the local estimates. -/
theorem edgeEnergy_le_three_root_add_five_vertex
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (f : A2Root → E)
    (hf : ∀ r, f r ∈ KazhdanFixedSpace.fixedSubspace rho (A.vertexGroup r)) :
    edgeEnergy f ≤
      3 * centralMovingEdgeEnergy A rho f +
        5 * vertexFixedEdgeEnergy A rho f := by
  have hsum : (∑ t : Fin 6, triangleEnergy f t) ≤
      ∑ t : Fin 6,
        (3 * triangleRootMovingEnergy A rho f t +
          5 * triangleVertexFixedEnergy A rho f t) := by
    apply Finset.sum_le_sum
    intro t ht
    exact triangleEnergy_le A rho f hf t
  have hfixed := sum_triangleVertexFixedEnergy_le A rho f
  calc
    edgeEnergy f = ∑ t : Fin 6, triangleEnergy f t :=
      (sum_triangleEnergy f).symm
    _ ≤ ∑ t : Fin 6,
        (3 * triangleRootMovingEnergy A rho f t +
          5 * triangleVertexFixedEnergy A rho f t) := hsum
    _ = 3 * centralMovingEdgeEnergy A rho f +
        5 * ∑ t : Fin 6, triangleVertexFixedEnergy A rho f t := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        sum_triangleRootMovingEnergy]
    _ ≤ 3 * centralMovingEdgeEnergy A rho f +
        5 * vertexFixedEdgeEnergy A rho f := by
      have hm := mul_le_mul_of_nonneg_left hfixed (by norm_num : (0 : ℝ) ≤ 5)
      linarith

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
strict multiple of the bounded-exponent root-moving energy. -/
theorem vertexMovingLaplacianEnergy_le_with_defect
    (A : A2System G)
    (n : ℕ) (hn : 0 < n)
    (hexp : ∀ (i j : Fin 3) (hij : i ≠ j),
      ∀ g ∈ A.root i j hij, g ^ n = 1)
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
          A n hn hexp rho f hf r
    _ = 2 * ∑ r : A2Root, ∑ n : Fin 4,
          ‖KazhdanFixedSpace.subgroupMovingProjection rho (A.vertexGroup r)
            (f r - f (neighbor r n))‖ ^ 2 -
        (1 - (Real.sqrt 2)⁻¹) *
          ∑ r : A2Root,
            (‖centralMovingIncidentComponent A rho f r 2‖ ^ 2 +
              ‖centralMovingIncidentComponent A rho f r 3‖ ^ 2) := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]

/-- Combining Claim 5.7(a) with the strict local defect gives a uniform
coefficient strictly below the borderline value `2`. -/
theorem vertexMovingLaplacianEnergy_lt_two_mul_edgeEnergy
    (A : A2System G)
    (n : ℕ) (hn : 0 < n)
    (hexp : ∀ (i j : Fin 3) (hij : i ≠ j),
      ∀ g ∈ A.root i j hij, g ^ n = 1)
    (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (f : A2Root → E)
    (hf : ∀ r, f r ∈ KazhdanFixedSpace.fixedSubspace rho (A.vertexGroup r)) :
    vertexMovingLaplacianEnergy A rho f ≤
      (2 - (1 - (Real.sqrt 2)⁻¹) / 3) * edgeEnergy f := by
  let c : ℝ := 1 - (Real.sqrt 2)⁻¹
  let D := edgeEnergy f
  let M := vertexMovingEdgeEnergy A rho f
  let F := vertexFixedEdgeEnergy A rho f
  let R := centralMovingEdgeEnergy A rho f
  have hsqrt0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt 2 := by
    have hsqrtNonneg := Real.sqrt_nonneg 2
    nlinarith
  have hinv0 : 0 ≤ (Real.sqrt 2)⁻¹ := inv_nonneg.mpr hsqrt0.le
  have hinv1 : (Real.sqrt 2)⁻¹ ≤ 1 :=
    (inv_le_one₀ hsqrt0).2 hsqrt1
  have hc0 : 0 ≤ c := by dsimp [c]; linarith
  have hc1 : c ≤ 1 := by dsimp [c]; linarith
  have hF0 : 0 ≤ F := by
    dsimp [F, vertexFixedEdgeEnergy]
    positivity
  have hclaim : D ≤ 3 * R + 5 * F := by
    exact edgeEnergy_le_three_root_add_five_vertex A rho f hf
  have hscaled : (c / 3) * D ≤ (c / 3) * (3 * R + 5 * F) :=
    mul_le_mul_of_nonneg_left hclaim (div_nonneg hc0 (by norm_num))
  have hcoef : 5 * (c / 3) ≤ 2 := by nlinarith
  have hcoefF : 5 * (c / 3) * F ≤ 2 * F :=
    mul_le_mul_of_nonneg_right hcoef hF0
  have hdefect : (c / 3) * D ≤ c * R + 2 * F := by
    calc
      (c / 3) * D ≤ (c / 3) * (3 * R + 5 * F) := hscaled
      _ = c * R + 5 * (c / 3) * F := by ring
      _ ≤ c * R + 2 * F := by linarith
  have hsplit : D = M + F := edgeEnergy_eq_moving_add_fixed A rho f
  have hlocal : vertexMovingLaplacianEnergy A rho f ≤ 2 * M - c * R := by
    exact vertexMovingLaplacianEnergy_le_with_defect A n hn hexp rho f hf
  change vertexMovingLaplacianEnergy A rho f ≤ (2 - c / 3) * D
  nlinarith

end A2MagicEnergy
end NonsoficGroupsExist
