import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Group

/-!
# Three-factor normal form for a class-two join

The lemma in this file is the algebraic normal-form calculation used for the
vertex groups in the EJZ six-vertex graph.  It is stated entirely in terms of
subgroup commutators and normalizers.
-/

namespace NonsoficGroupsExist

open scoped commutatorElement Pointwise

variable {G : Type*} [Group G]

namespace ClassTwoNormalForm

/-- If commutators of `Y` with each generator subgroup of `X ⊔ Z` lie in
`Z`, then `Y` normalizes `X ⊔ Z`. -/
theorem le_normalizer_sup (X Y Z : Subgroup G)
    (hYX : ⁅Y, X⁆ ≤ Z) (hYZ : ⁅Y, Z⁆ ≤ Z) :
    Y ≤ Subgroup.normalizer (X ⊔ Z : Subgroup G) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    let C : Subgroup G := (X ⊔ Z).comap (MulAut.conj y).toMonoidHom
    have hXC : X ≤ C := by
      intro x hx
      change y * x * y⁻¹ ∈ X ⊔ Z
      rw [show y * x * y⁻¹ = ⁅y, x⁆ * x by
        simp [commutatorElement_def, mul_assoc]]
      exact (X ⊔ Z).mul_mem
        ((show Z ≤ X ⊔ Z from le_sup_right)
          (hYX (Subgroup.commutator_mem_commutator hy hx)))
        ((show X ≤ X ⊔ Z from le_sup_left) hx)
    have hZC : Z ≤ C := by
      intro z hz
      change y * z * y⁻¹ ∈ X ⊔ Z
      rw [show y * z * y⁻¹ = ⁅y, z⁆ * z by
        simp [commutatorElement_def, mul_assoc]]
      exact (X ⊔ Z).mul_mem
        ((show Z ≤ X ⊔ Z from le_sup_right)
          (hYZ (Subgroup.commutator_mem_commutator hy hz)))
        ((show Z ≤ X ⊔ Z from le_sup_right) hz)
    exact (sup_le hXC hZC hw)
  · intro hconj
    have hyinv : y⁻¹ ∈ Y := Y.inv_mem hy
    have hYXinv : ∀ x ∈ X, y⁻¹ * x * (y⁻¹)⁻¹ ∈ X ⊔ Z := by
      intro x hx
      rw [show y⁻¹ * x * (y⁻¹)⁻¹ = ⁅y⁻¹, x⁆ * x by
        simp [commutatorElement_def, mul_assoc]]
      exact (X ⊔ Z).mul_mem
        ((show Z ≤ X ⊔ Z from le_sup_right)
          (hYX (Subgroup.commutator_mem_commutator hyinv hx)))
        ((show X ≤ X ⊔ Z from le_sup_left) hx)
    have hYZinv : ∀ z ∈ Z, y⁻¹ * z * (y⁻¹)⁻¹ ∈ X ⊔ Z := by
      intro z hz
      rw [show y⁻¹ * z * (y⁻¹)⁻¹ = ⁅y⁻¹, z⁆ * z by
        simp [commutatorElement_def, mul_assoc]]
      exact (X ⊔ Z).mul_mem
        ((show Z ≤ X ⊔ Z from le_sup_right)
          (hYZ (Subgroup.commutator_mem_commutator hyinv hz)))
        ((show Z ≤ X ⊔ Z from le_sup_right) hz)
    let C : Subgroup G := (X ⊔ Z).comap (MulAut.conj y⁻¹).toMonoidHom
    have hC : X ⊔ Z ≤ C := sup_le hYXinv hYZinv
    have := hC hconj
    change y⁻¹ * (y * w * y⁻¹) * (y⁻¹)⁻¹ ∈ X ⊔ Z at this
    have heq : y⁻¹ * (y * w * y⁻¹) * (y⁻¹)⁻¹ = w := by group
    rwa [heq] at this

/-- If `Z` contains the relevant commutators and already lies in `X ⊔ Y`,
then every element of `X ⊔ Y` has the normal form `x * y * z`. -/
theorem exists_three_factor (X Y Z : Subgroup G)
    (hYX : ⁅Y, X⁆ ≤ Z) (hXZ : ⁅X, Z⁆ ≤ Z) (hYZ : ⁅Y, Z⁆ ≤ Z)
    (hZ : Z ≤ X ⊔ Y) {g : G} (hg : g ∈ X ⊔ Y) :
    ∃ x ∈ X, ∃ y ∈ Y, ∃ z ∈ Z, x * y * z = g := by
  have hXnormZ : X ≤ Subgroup.normalizer Z :=
    Subgroup.le_normalizer_iff_commutator_le_right.mpr hXZ
  have hYnormZ : Y ≤ Subgroup.normalizer Z :=
    Subgroup.le_normalizer_iff_commutator_le_right.mpr hYZ
  have hYnormXZ : Y ≤ Subgroup.normalizer (X ⊔ Z : Subgroup G) :=
    le_normalizer_sup X Y Z hYX hYZ
  have heq : (X ⊔ Z) ⊔ Y = X ⊔ Y := by
    apply le_antisymm
    · exact sup_le (sup_le le_sup_left hZ) le_sup_right
    · exact sup_le
        ((show X ≤ X ⊔ Z from le_sup_left).trans
          (show X ⊔ Z ≤ (X ⊔ Z) ⊔ Y from le_sup_left))
        (show Y ≤ (X ⊔ Z) ⊔ Y from le_sup_right)
  have hg' : g ∈ (X ⊔ Z) ⊔ Y := by simpa [heq] using hg
  change g ∈ (↑((X ⊔ Z) ⊔ Y) : Set G) at hg'
  rw [show ((↑((X ⊔ Z) ⊔ Y) : Set G)) =
      (X ⊔ Z : Subgroup G) * (Y : Set G) from
        Subgroup.coe_mul_of_right_le_normalizer_left (X ⊔ Z) Y hYnormXZ] at hg'
  rcases hg' with ⟨xz, hxz, y, hy, rfl⟩
  change xz ∈ (↑(X ⊔ Z) : Set G) at hxz
  rw [show ((↑(X ⊔ Z) : Set G)) = (X : Set G) * (Z : Set G) from
    Subgroup.coe_mul_of_left_le_normalizer_right X Z hXnormZ] at hxz
  rcases hxz with ⟨x, hx, z, hz, rfl⟩
  let z' := y⁻¹ * z * y
  have hz' : z' ∈ Z := by
    exact (Subgroup.mem_normalizer_iff''.mp (hYnormZ hy) z).mp hz
  refine ⟨x, hx, y, hy, z', hz', ?_⟩
  dsimp [z']
  group

end ClassTwoNormalForm
end NonsoficGroupsExist
