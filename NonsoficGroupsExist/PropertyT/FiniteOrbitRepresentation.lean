import NonsoficGroupsExist.Kazhdan.KazhdanFixedSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Finite-dimensional orbit subrepresentations

For a finite group, the span of the orbits of two vectors is a finite-
dimensional invariant subspace.  This reduces a two-vector fixed-space
estimate in an arbitrary Hilbert representation to finite dimensions.
-/

namespace NonsoficGroupsExist

universe u v

namespace FiniteOrbitRepresentation

variable {G : Type u} [Group G] [Finite G]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The span of the two finite group orbits. -/
noncomputable def orbitSpan (rho : G →* (E ≃ₗᵢ[ℝ] E)) (u v : E) :
    Submodule ℝ E :=
  Submodule.span ℝ
    (Set.range (fun g : G ↦ rho g u) ∪ Set.range (fun g : G ↦ rho g v))

omit [Finite G] in theorem left_mem_orbitSpan
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (u v : E) :
    u ∈ orbitSpan rho u v := by
  apply Submodule.subset_span
  apply Set.mem_union_left
  exact ⟨1, by simp⟩

omit [Finite G] in theorem right_mem_orbitSpan
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (u v : E) :
    v ∈ orbitSpan rho u v := by
  apply Submodule.subset_span
  apply Set.mem_union_right
  exact ⟨1, by simp⟩

/-- The two-orbit span is finite-dimensional because the group is finite. -/
theorem orbitSpan_finiteDimensional
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (u v : E) :
    FiniteDimensional ℝ (orbitSpan rho u v) := by
  apply FiniteDimensional.span_of_finite ℝ
  exact (Set.finite_range _).union (Set.finite_range _)

omit [Finite G] in
/-- Every group element preserves the two-orbit span. -/
theorem map_mem_orbitSpan
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (u v : E)
    (g : G) {x : E} (hx : x ∈ orbitSpan rho u v) :
    rho g x ∈ orbitSpan rho u v := by
  let W := orbitSpan rho u v
  let M : Submodule ℝ E := W.comap (rho g).toLinearMap
  have hWM : W ≤ M := by
    rw [show W = Submodule.span ℝ
      (Set.range (fun h : G ↦ rho h u) ∪
        Set.range (fun h : G ↦ rho h v)) from rfl]
    rw [Submodule.span_le]
    rintro y (hy | hy)
    · obtain ⟨h, rfl⟩ := hy
      change rho g (rho h u) ∈ W
      have hmem : rho (g * h) u ∈ W :=
        Submodule.subset_span (Set.mem_union_left _ ⟨g * h, rfl⟩)
      simpa [map_mul] using hmem
    · obtain ⟨h, rfl⟩ := hy
      change rho g (rho h v) ∈ W
      have hmem : rho (g * h) v ∈ W :=
        Submodule.subset_span (Set.mem_union_right _ ⟨g * h, rfl⟩)
      simpa [map_mul] using hmem
  exact hWM hx

omit [Finite G] in
/-- The orthogonal representation restricted to the two-orbit span. -/
noncomputable def representation (rho : G →* (E ≃ₗᵢ[ℝ] E)) (u v : E) :
    G →* (orbitSpan rho u v ≃ₗᵢ[ℝ] orbitSpan rho u v) :=
  KazhdanFixedSpace.restrictToInvariantSubspace rho (orbitSpan rho u v)
    fun g _ hx ↦ map_mem_orbitSpan rho u v g hx

omit [Finite G] in
@[simp] theorem representation_apply
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (u v : E) (g : G)
    (x : orbitSpan rho u v) :
    ((representation rho u v g x : orbitSpan rho u v) : E) = rho g x.1 := rfl

omit [Finite G] in
/-- Absence of invariant vectors passes to the finite-dimensional orbit
subrepresentation. -/
theorem representation_hasNoInvariantVectors
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (u v : E)
    (hno : IsKazhdanPair.HasNoInvariantVectors G rho) :
    IsKazhdanPair.HasNoInvariantVectors G (representation rho u v) := by
  intro x hx
  apply Subtype.ext
  apply hno x.1
  intro g
  have h := congrArg Subtype.val (hx g)
  simpa using h

end FiniteOrbitRepresentation
end NonsoficGroupsExist
