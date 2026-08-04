import NonsoficGroupsExist.A2System
import NonsoficGroupsExist.ClassTwoApproximation
import NonsoficGroupsExist.FiniteClassTwoDecompositionBound

/-!
# Finite class-two stages in characteristic two

Finite subsets of the two root groups at an `A₂` vertex generate a finite
class-two group when every root element has exponent two.  For elementary
groups over a characteristic-two ring, that exponent statement is proved by
the elementary-matrix multiplication formula.
-/

namespace NonsoficGroupsExist

open scoped commutatorElement

universe u

namespace A2System

variable {G : Type u} [Group G]

/-- The left generating root at a magic-graph vertex. -/
def leftRootGroup (A : A2System G) (r : A2Root) : Subgroup G :=
  A.root r.1.1 (a2ThirdIndex r.1.1 r.1.2)
    (a2ThirdIndex_ne_left r.1.1 r.1.2 r.2).symm

/-- The right generating root at a magic-graph vertex. -/
def rightRootGroup (A : A2System G) (r : A2Root) : Subgroup G :=
  A.root (a2ThirdIndex r.1.1 r.1.2) r.1.2
    (a2ThirdIndex_ne_right r.1.1 r.1.2 r.2)

/-- Every explicit finite stage at a vertex is finite when all root elements
have exponent two. -/
theorem vertexStage_finite_of_root_exponent_two
    (A : A2System G)
    (hexp : ∀ (i j : Fin 3) (hij : i ≠ j),
      ∀ g ∈ A.root i j hij, g ^ 2 = 1)
    (r : A2Root)
    (a : ClassTwoApproximation.StageIndex
      (A.leftRootGroup r) (A.rightRootGroup r)) :
    Finite (ClassTwoApproximation.stageGroup
      (A.leftRootGroup r) (A.rightRootGroup r) a) := by
  let i := r.1.1
  let j := r.1.2
  let k := a2ThirdIndex i j
  have hik : i ≠ k := (a2ThirdIndex_ne_left i j r.2).symm
  have hkj : k ≠ j := a2ThirdIndex_ne_right i j r.2
  let X := A.leftRootGroup r
  let Y := A.rightRootGroup r
  let X₀ := ClassTwoApproximation.leftStage X Y a
  let Y₀ := ClassTwoApproximation.rightStage X Y a
  let C := ⁅Y₀, X₀⁆
  let Z := A.rootAt r
  have hXcomm : ∀ x ∈ X, ∀ y ∈ X, Commute x y := by
    exact A.root_commute i k hik
  have hYcomm : ∀ x ∈ Y, ∀ y ∈ Y, Commute x y := by
    exact A.root_commute k j hkj
  have hXexp : ∀ x ∈ X, x ^ 2 = 1 := by
    exact hexp i k hik
  have hYexp : ∀ y ∈ Y, y ^ 2 = 1 := by
    exact hexp k j hkj
  letI : Finite X₀ :=
    ClassTwoApproximation.finite_leftStage X Y a hXcomm hXexp
  letI : Finite Y₀ :=
    ClassTwoApproximation.finite_rightStage X Y a hYcomm hYexp
  have hC_le_Z : C ≤ Z := by
    apply Subgroup.commutator_le.mpr
    intro y hy x hx
    have hxX : x ∈ X := ClassTwoApproximation.leftStage_le X Y a hx
    have hyY : y ∈ Y := ClassTwoApproximation.rightStage_le X Y a hy
    have hxy : ⁅x, y⁆ ∈ Z := A.commutator_mem i k j hik hkj r.2 x hxX y hyY
    rw [← commutatorElement_inv x y]
    exact Z.inv_mem hxy
  have hCfg : C.FG := ClassTwoApproximation.commutator_fg_of_finite Y₀ X₀
  have hCcomm : ∀ x ∈ C, ∀ y ∈ C, Commute x y := by
    intro x hx y hy
    exact A.root_commute i j r.2 x (hC_le_Z hx) y (hC_le_Z hy)
  have hCexp : ∀ z ∈ C, z ^ 2 = 1 := by
    intro z hz
    exact hexp i j r.2 z (hC_le_Z hz)
  letI : Finite C :=
    ClassTwoApproximation.finite_of_fg_commute_exponent_two C hCfg hCcomm hCexp
  have hYX : ⁅Y₀, X₀⁆ ≤ C := le_rfl
  have hXC : ⁅X₀, C⁆ ≤ C := by
    apply Subgroup.commutator_le.mpr
    intro x hx z hz
    have hxX : x ∈ X := ClassTwoApproximation.leftStage_le X Y a hx
    have hcomm : Commute x z :=
      A.commute i k i j hik r.2
        (a2ThirdIndex_ne_left i j r.2) r.2.symm
        x hxX z (hC_le_Z hz)
    rw [commutatorElement_eq_one_iff_commute.mpr hcomm]
    exact C.one_mem
  have hYC : ⁅Y₀, C⁆ ≤ C := by
    apply Subgroup.commutator_le.mpr
    intro y hy z hz
    have hyY : y ∈ Y := ClassTwoApproximation.rightStage_le X Y a hy
    have hcomm : Commute y z :=
      A.commute k j i j hkj r.2 r.2.symm hkj.symm
        y hyY z (hC_le_Z hz)
    rw [commutatorElement_eq_one_iff_commute.mpr hcomm]
    exact C.one_mem
  have hC : C ≤ X₀ ⊔ Y₀ := by
    intro c hc
    have := Subgroup.commutator_le_sup Y₀ X₀ hc
    simpa [sup_comm] using this
  exact ClassTwoNormalForm.finite_sup_of_three_factor X₀ Y₀ C
    hYX hXC hYC hC

/-- For elementary groups over a characteristic-two ring, every finite
vertex stage is finite with no additional premise. -/
theorem elementary_vertexStage_finite
    (R : Type*) [Ring R] [CharP R 2]
    (r : A2Root)
    (a : ClassTwoApproximation.StageIndex
      ((elementaryA2System R).leftRootGroup r)
      ((elementaryA2System R).rightRootGroup r)) :
    Finite (ClassTwoApproximation.stageGroup
      ((elementaryA2System R).leftRootGroup r)
      ((elementaryA2System R).rightRootGroup r) a) := by
  apply vertexStage_finite_of_root_exponent_two (elementaryA2System R)
  intro i j hij g hg
  exact elementaryRootSubgroup_sq i j hij g hg

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every finite A₂ vertex stage has the universal class-two
`1 / sqrt 2` fixed-space angle bound when root elements have exponent two. -/
theorem vertexStage_epsilonOrthogonal_of_root_exponent_two
    (A : A2System G)
    (hexp : ∀ (i j : Fin 3) (hij : i ≠ j),
      ∀ g ∈ A.root i j hij, g ^ 2 = 1)
    (r : A2Root)
    (a : ClassTwoApproximation.StageIndex
      (A.leftRootGroup r) (A.rightRootGroup r))
    (rho : ClassTwoApproximation.stageGroup
      (A.leftRootGroup r) (A.rightRootGroup r) a →*
        (E ≃ₗᵢ[ℝ] E))
    (hno : IsKazhdanPair.HasNoInvariantVectors
      (ClassTwoApproximation.stageGroup
        (A.leftRootGroup r) (A.rightRootGroup r) a) rho) :
    HilbertEpsilonOrthogonality.EpsilonOrthogonal
      (KazhdanFixedSpace.fixedSubspace rho
        ((ClassTwoApproximation.leftStage
          (A.leftRootGroup r) (A.rightRootGroup r) a).subgroupOf
            (ClassTwoApproximation.stageGroup
              (A.leftRootGroup r) (A.rightRootGroup r) a)))
      (KazhdanFixedSpace.fixedSubspace rho
        ((ClassTwoApproximation.rightStage
          (A.leftRootGroup r) (A.rightRootGroup r) a).subgroupOf
            (ClassTwoApproximation.stageGroup
              (A.leftRootGroup r) (A.rightRootGroup r) a)))
      (Real.sqrt 2)⁻¹ := by
  let i := r.1.1
  let j := r.1.2
  let k := a2ThirdIndex i j
  have hik : i ≠ k := (a2ThirdIndex_ne_left i j r.2).symm
  have hkj : k ≠ j := a2ThirdIndex_ne_right i j r.2
  let X := A.leftRootGroup r
  let Y := A.rightRootGroup r
  let X₀ := ClassTwoApproximation.leftStage X Y a
  let Y₀ := ClassTwoApproximation.rightStage X Y a
  let L := ClassTwoApproximation.stageGroup X Y a
  let C₀ := ⁅Y₀, X₀⁆
  let XL := X₀.subgroupOf L
  let YL := Y₀.subgroupOf L
  have hC₀L : C₀ ≤ L := by
    intro c hc
    have := Subgroup.commutator_le_sup Y₀ X₀ hc
    simpa [L, ClassTwoApproximation.stageGroup, sup_comm] using this
  let CL := C₀.subgroupOf L
  let Z := A.rootAt r
  have hC₀Z : C₀ ≤ Z := by
    apply Subgroup.commutator_le.mpr
    intro y hy x hx
    have hxX : x ∈ X := ClassTwoApproximation.leftStage_le X Y a hx
    have hyY : y ∈ Y := ClassTwoApproximation.rightStage_le X Y a hy
    have hxy : ⁅x, y⁆ ∈ Z :=
      A.commutator_mem i k j hik hkj r.2 x hxX y hyY
    rw [← commutatorElement_inv x y]
    exact Z.inv_mem hxy
  have hgen : XL ⊔ YL = ⊤ := by
    exact ClassTwoNormalForm.subgroupOf_sup_eq_top X₀ Y₀ L
      le_sup_left le_sup_right rfl
  have hcomm : ⁅YL, XL⁆ ≤ CL := by
    apply Subgroup.commutator_le.mpr
    intro y hy x hx
    apply Subgroup.mem_subgroupOf.mpr
    exact Subgroup.commutator_mem_commutator
      (Subgroup.mem_subgroupOf.mp hy) (Subgroup.mem_subgroupOf.mp hx)
  have hcentral : CL ≤ Subgroup.center L := by
    intro c hc
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hcC₀ : c.1 ∈ C₀ := Subgroup.mem_subgroupOf.mp hc
    have hcZ : c.1 ∈ Z := hC₀Z hcC₀
    let D := Subgroup.centralizer ({c.1} : Set G)
    have hX₀D : X₀ ≤ D := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hxX : x ∈ X := ClassTwoApproximation.leftStage_le X Y a hx
      exact (A.commute i k i j hik r.2
        (a2ThirdIndex_ne_left i j r.2) r.2.symm
        x hxX c.1 hcZ).eq
    have hY₀D : Y₀ ≤ D := by
      intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hyY : y ∈ Y := ClassTwoApproximation.rightStage_le X Y a hy
      exact (A.commute k j i j hkj r.2 r.2.symm hkj.symm
        y hyY c.1 hcZ).eq
    exact Subgroup.mem_centralizer_singleton_iff.mp
      ((sup_le hX₀D hY₀D) g.2)
  have hCLexp : ∀ c ∈ CL, c ^ 2 = 1 := by
    intro c hc
    apply Subtype.ext
    exact hexp i j r.2 c.1 (hC₀Z (Subgroup.mem_subgroupOf.mp hc))
  letI : Finite L := vertexStage_finite_of_root_exponent_two A hexp r a
  exact FiniteClassTwoDecompositionBound.epsilonOrthogonal
    rho XL YL CL hgen hcomm hcentral hCLexp hno

/-- Concrete characteristic-two elementary A₂ stages satisfy the same
angle bound with no additional algebraic premise. -/
theorem elementary_vertexStage_epsilonOrthogonal
    (R : Type*) [Ring R] [CharP R 2]
    (r : A2Root)
    (a : ClassTwoApproximation.StageIndex
      ((elementaryA2System R).leftRootGroup r)
      ((elementaryA2System R).rightRootGroup r))
    (rho : ClassTwoApproximation.stageGroup
      ((elementaryA2System R).leftRootGroup r)
      ((elementaryA2System R).rightRootGroup r) a →* (E ≃ₗᵢ[ℝ] E))
    (hno : IsKazhdanPair.HasNoInvariantVectors
      (ClassTwoApproximation.stageGroup
        ((elementaryA2System R).leftRootGroup r)
        ((elementaryA2System R).rightRootGroup r) a) rho) :
    HilbertEpsilonOrthogonality.EpsilonOrthogonal
      (KazhdanFixedSpace.fixedSubspace rho
        ((ClassTwoApproximation.leftStage
          ((elementaryA2System R).leftRootGroup r)
          ((elementaryA2System R).rightRootGroup r) a).subgroupOf
            (ClassTwoApproximation.stageGroup
              ((elementaryA2System R).leftRootGroup r)
              ((elementaryA2System R).rightRootGroup r) a)))
      (KazhdanFixedSpace.fixedSubspace rho
        ((ClassTwoApproximation.rightStage
          ((elementaryA2System R).leftRootGroup r)
          ((elementaryA2System R).rightRootGroup r) a).subgroupOf
            (ClassTwoApproximation.stageGroup
              ((elementaryA2System R).leftRootGroup r)
              ((elementaryA2System R).rightRootGroup r) a)))
      (Real.sqrt 2)⁻¹ := by
  apply vertexStage_epsilonOrthogonal_of_root_exponent_two
    (elementaryA2System R)
  intro p q hpq g hg
  exact elementaryRootSubgroup_sq p q hpq g hg
  exact hno

end A2System
end NonsoficGroupsExist
