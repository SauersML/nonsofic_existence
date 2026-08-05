import NonsoficGroupsExist.A2System
import NonsoficGroupsExist.ClassTwoOrthogonality

/-!
# Class-two angles at A₂ vertices

The two root subgroups generating an A₂ vertex are abelian.  Their cross-
commutator lies in the sum root, which is central in the vertex.  When all
root elements have one positive bounded exponent, the universal class-two
theorem therefore gives the sharp `1 / sqrt 2` bound for the two root fixed
spaces; in characteristic `p` the exponent is `p`.
-/

namespace NonsoficGroupsExist

open scoped commutatorElement

universe u v

namespace A2System

variable {G : Type u} [Group G]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- Subtype form of the root-space angle theorem for a representation of one
A₂ vertex group. -/
theorem rootFixedSubspaces_epsilonOrthogonal_restricted_of_root_boundedExponent
    (A : A2System G)
    (n : ℕ) (hn : 0 < n)
    (hexp : ∀ (i j : Fin 3) (hij : i ≠ j),
      ∀ g ∈ A.root i j hij, g ^ n = 1)
    (r : A2Root)
    (rho : A.vertexGroup r →* (E ≃ₗᵢ[ℝ] E))
    (hno : IsKazhdanPair.HasNoInvariantVectors (A.vertexGroup r) rho) :
    HilbertEpsilonOrthogonality.EpsilonOrthogonal
      (KazhdanFixedSpace.fixedSubspace rho
        ((A.leftRootGroup r).subgroupOf (A.vertexGroup r)))
      (KazhdanFixedSpace.fixedSubspace rho
        ((A.rightRootGroup r).subgroupOf (A.vertexGroup r)))
      (Real.sqrt 2)⁻¹ := by
  let i := r.1.1
  let j := r.1.2
  let k := a2ThirdIndex i j
  have hik : i ≠ k := (a2ThirdIndex_ne_left i j r.2).symm
  have hkj : k ≠ j := a2ThirdIndex_ne_right i j r.2
  let X := A.leftRootGroup r
  let Y := A.rightRootGroup r
  let L := A.vertexGroup r
  let XL := X.subgroupOf L
  let YL := Y.subgroupOf L
  let ZL := (A.rootAt r).subgroupOf L
  have hgen : XL ⊔ YL = ⊤ :=
    ClassTwoNormalForm.subgroupOf_sup_eq_top X Y L
      (A.leftRoot_le_vertexGroup r) (A.rightRoot_le_vertexGroup r) rfl
  have hXcomm : ∀ x ∈ XL, ∀ x' ∈ XL, Commute x x' := by
    intro x hx x' hx'
    apply Subtype.ext
    exact (A.root_commute i k hik x.1
      (Subgroup.mem_subgroupOf.mp hx) x'.1
      (Subgroup.mem_subgroupOf.mp hx')).eq
  have hYcomm : ∀ y ∈ YL, ∀ y' ∈ YL, Commute y y' := by
    intro y hy y' hy'
    apply Subtype.ext
    exact (A.root_commute k j hkj y.1
      (Subgroup.mem_subgroupOf.mp hy) y'.1
      (Subgroup.mem_subgroupOf.mp hy')).eq
  have hXexp : ∀ x ∈ XL, x ^ n = 1 := by
    intro x hx
    apply Subtype.ext
    exact hexp i k hik x.1 (Subgroup.mem_subgroupOf.mp hx)
  have hYexp : ∀ y ∈ YL, y ^ n = 1 := by
    intro y hy
    apply Subtype.ext
    exact hexp k j hkj y.1 (Subgroup.mem_subgroupOf.mp hy)
  have hcomm : ⁅YL, XL⁆ ≤ ZL := by
    apply Subgroup.commutator_le.mpr
    intro y hy x hx
    apply Subgroup.mem_subgroupOf.mpr
    have hxy : ⁅x.1, y.1⁆ ∈ A.rootAt r :=
      A.commutator_mem i k j hik hkj r.2 x.1
        (Subgroup.mem_subgroupOf.mp hx) y.1
        (Subgroup.mem_subgroupOf.mp hy)
    change ⁅y.1, x.1⁆ ∈ A.rootAt r
    rw [← commutatorElement_inv x.1 y.1]
    exact (A.rootAt r).inv_mem hxy
  have hcentral : ⁅YL, XL⁆ ≤ Subgroup.center L :=
    hcomm.trans (A.rootAt_subgroupOf_le_center r)
  have hCexp : ∀ c ∈ ⁅YL, XL⁆, c ^ n = 1 := by
    intro c hc
    apply Subtype.ext
    exact hexp i j r.2 c.1
      (Subgroup.mem_subgroupOf.mp (hcomm hc))
  have hangle := ClassTwoOrthogonality.epsilonOrthogonal
    rho
    XL YL n hn hgen hXcomm hYcomm hXexp hYexp hcentral hCexp hno
  exact hangle

/-- The two root fixed spaces at every A₂ vertex have angle at most
`1 / sqrt 2` when all root elements have one positive bounded exponent. -/
theorem rootFixedSubspaces_epsilonOrthogonal_of_root_boundedExponent
    (A : A2System G)
    (n : ℕ) (hn : 0 < n)
    (hexp : ∀ (i j : Fin 3) (hij : i ≠ j),
      ∀ g ∈ A.root i j hij, g ^ n = 1)
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (r : A2Root)
    (hno : IsKazhdanPair.HasNoInvariantVectors (A.vertexGroup r)
      (KazhdanFixedSpace.restrictRepresentation rho (A.vertexGroup r))) :
    HilbertEpsilonOrthogonality.EpsilonOrthogonal
      (KazhdanFixedSpace.fixedSubspace rho (A.leftRootGroup r))
      (KazhdanFixedSpace.fixedSubspace rho (A.rightRootGroup r))
      (Real.sqrt 2)⁻¹ := by
  have hangle :=
    A.rootFixedSubspaces_epsilonOrthogonal_restricted_of_root_boundedExponent
      n hn hexp r
      (KazhdanFixedSpace.restrictRepresentation rho (A.vertexGroup r)) hno
  rw [KazhdanFixedSpace.fixedSubspace_subgroupOf_eq rho
      (A.leftRootGroup r) (A.vertexGroup r) (A.leftRoot_le_vertexGroup r),
    KazhdanFixedSpace.fixedSubspace_subgroupOf_eq rho
      (A.rightRootGroup r) (A.vertexGroup r) (A.rightRoot_le_vertexGroup r)] at hangle
  exact hangle

/-- The preceding vertex-angle theorem for elementary rank-three groups over
an arbitrary ring of positive characteristic. -/
theorem elementary_rootFixedSubspaces_epsilonOrthogonal
    (R : Type*) [Ring R] (p : ℕ) (hp : 0 < p) [CharP R p]
    (rho : elementaryGroup (Fin 3) R →* (E ≃ₗᵢ[ℝ] E))
    (r : A2Root)
    (hno : IsKazhdanPair.HasNoInvariantVectors
      ((elementaryA2System R).vertexGroup r)
      (KazhdanFixedSpace.restrictRepresentation rho
        ((elementaryA2System R).vertexGroup r))) :
    HilbertEpsilonOrthogonality.EpsilonOrthogonal
      (KazhdanFixedSpace.fixedSubspace rho
        ((elementaryA2System R).leftRootGroup r))
      (KazhdanFixedSpace.fixedSubspace rho
        ((elementaryA2System R).rightRootGroup r))
      (Real.sqrt 2)⁻¹ := by
  apply rootFixedSubspaces_epsilonOrthogonal_of_root_boundedExponent
    (elementaryA2System R) p hp
  intro i j hij g hg
  exact elementaryRootSubgroup_pow_char p i j hij g hg
  exact hno

end A2System
end NonsoficGroupsExist
