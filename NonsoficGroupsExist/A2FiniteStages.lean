import NonsoficGroupsExist.A2System
import NonsoficGroupsExist.ClassTwoApproximation

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

end A2System
end NonsoficGroupsExist
