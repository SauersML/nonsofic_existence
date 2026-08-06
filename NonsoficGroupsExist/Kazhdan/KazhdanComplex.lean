import NonsoficGroupsExist.Kazhdan.Kazhdan
import NonsoficGroupsExist.Kazhdan.HilbertComplexification

/-!
# The complex-unitary form of Kazhdan's property `(T)`

`NonsoficGroupsExist.IsKazhdanPair` is stated with real orthogonal
representations.  The textbook definition of property `(T)` uses unitary
representations on complex Hilbert spaces.  This module states that complex
form, `IsKazhdanPairComplex`, and proves the two forms equivalent for a
discrete group -- with the *same* control set and the *same* tolerance, so no
constants are lost in either direction:

* `IsKazhdanPair.toComplex`: realification.  A complex Hilbert space is a real
  Hilbert space for `re ⟪·,·⟫` with the same norm, and a unitary is in
  particular a real linear isometry, so the real hypothesis applies verbatim
  and returns a vector invariant under the very same maps.
* `IsKazhdanPairComplex.toReal`: complexification.  A real Hilbert space `E`
  embeds isometrically into `E ⊕ iE` as `a ↦ (a,0)`, an orthogonal
  representation extends to a unitary one, and the real and imaginary parts of
  an invariant vector are invariant, at least one of them nonzero.

The two are packaged as `isKazhdanPair_iff_complex` and, at the level of the
group property, `hasKazhdanPropertyT_iff_complex`.
-/

namespace NonsoficGroupsExist

universe u v

open scoped InnerProductSpace

section Realify

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A complex linear isometry equivalence read as a real one, for the real
inner product `re ⟪·,·⟫` on the same space and with the same norm. -/
noncomputable def realifyEquiv (f : E ≃ₗᵢ[ℂ] E) :
    letI : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
    E ≃ₗᵢ[ℝ] E :=
  letI : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
  { toFun := f
    invFun := f.symm
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_add' := fun x y ↦ f.map_add x y
    map_smul' := fun (r : ℝ) x ↦ by
      show f ((r : ℂ) • x) = (r : ℂ) • f x
      exact f.map_smul _ _
    norm_map' := f.norm_map }

/-- A unitary representation read as an orthogonal representation on the
underlying real Hilbert space. -/
noncomputable def realifyHom {G : Type u} [Group G]
    (ρ : G →* (E ≃ₗᵢ[ℂ] E)) :
    letI : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
    G →* (E ≃ₗᵢ[ℝ] E) :=
  letI : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
  { toFun := fun g ↦ realifyEquiv (ρ g)
    map_one' := by
      ext x
      simp [realifyEquiv, map_one]
    map_mul' := fun g h ↦ by
      ext x
      simp [realifyEquiv, map_mul] }

end Realify

/-- The complex-unitary form of a Kazhdan pair: every unitary representation
on a complex Hilbert space admitting a `(Q,ε)`-almost invariant unit vector
has a nonzero invariant vector.  This is the textbook definition of a Kazhdan
pair for a discrete group. -/
def IsKazhdanPairComplex (G : Type u) [Group G] (Q : Finset G) (ε : ℝ) : Prop :=
  0 < ε ∧
    ∀ (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
      [CompleteSpace E],
      ∀ ρ : G →* (E ≃ₗᵢ[ℂ] E), ∀ x : E, ‖x‖ = 1 →
        (∀ q ∈ Q, ‖ρ q x - x‖ < ε) →
          ∃ y : E, y ≠ 0 ∧ ∀ g : G, ρ g y = y

/-- Positive control: the empty set is a complex Kazhdan pair for the
trivial group, at tolerance one, witnessed outright. -/
theorem isKazhdanPairComplex_punit :
    IsKazhdanPairComplex PUnit (∅ : Finset PUnit) 1 := by
  refine ⟨one_pos, ?_⟩
  intro E _ _ _ ρ x hx _hq
  refine ⟨x, ?_, ?_⟩
  · intro h
    rw [h, norm_zero] at hx
    exact one_ne_zero hx.symm
  · intro g
    rw [Subsingleton.elim g 1, map_one]
    rfl

/-- Kazhdan's property `(T)` in its textbook complex-unitary form. -/
def HasKazhdanPropertyTComplex (G : Type u) [Group G] : Prop :=
  ∃ Q : Finset G, ∃ ε : ℝ, IsKazhdanPairComplex.{u, v} G Q ε

variable {G : Type u} [Group G] {Q : Finset G} {ε : ℝ}

/-- Realification: a real Kazhdan pair is a complex Kazhdan pair, with the
same control set and the same tolerance. -/
theorem IsKazhdanPair.toComplex (h : IsKazhdanPair.{u, v} G Q ε) :
    IsKazhdanPairComplex.{u, v} G Q ε := by
  refine ⟨h.1, ?_⟩
  intro E _ _ _ ρ x hx hnear
  letI : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
  obtain ⟨y, hy0, hy⟩ := h.2 E (realifyHom ρ) x hx hnear
  exact ⟨y, hy0, fun g ↦ hy g⟩

/-- Complexification: a complex Kazhdan pair is a real Kazhdan pair, with the
same control set and the same tolerance. -/
theorem IsKazhdanPairComplex.toReal (h : IsKazhdanPairComplex.{u, v} G Q ε) :
    IsKazhdanPair.{u, v} G Q ε := by
  refine ⟨h.1, ?_⟩
  intro E _ _ _ ρ x hx hnear
  have hxc : ‖Complexification.mk x (0 : E)‖ = 1 := by
    rw [Complexification.norm_mk_zero]; exact hx
  have hnearc : ∀ q ∈ Q,
      ‖Complexification.mapHom ρ q (Complexification.mk x (0 : E)) -
        Complexification.mk x (0 : E)‖ < ε := by
    intro q hq
    have hq0 : Complexification.mapHom ρ q (Complexification.mk x (0 : E)) =
        Complexification.mk (ρ q x) (0 : E) := by
      simp
    rw [hq0, Complexification.norm_mk_sub_mk]
    exact hnear q hq
  obtain ⟨y, hy0, hy⟩ :=
    h.2 (Complexification E) (Complexification.mapHom ρ) _ hxc hnearc
  have hre : ∀ g : G, ρ g y.re = y.re := fun g ↦
    congrArg Complexification.re (hy g)
  have him : ∀ g : G, ρ g y.im = y.im := fun g ↦
    congrArg Complexification.im (hy g)
  by_cases hyre : y.re = 0
  · refine ⟨y.im, ?_, him⟩
    intro hyim
    exact hy0 (Complexification.eq_zero_iff.mpr ⟨hyre, hyim⟩)
  · exact ⟨y.re, hyre, hre⟩

/-- The real and the complex-unitary forms of a Kazhdan pair agree, with no
loss in either the control set or the tolerance. -/
theorem isKazhdanPair_iff_complex :
    IsKazhdanPair.{u, v} G Q ε ↔ IsKazhdanPairComplex.{u, v} G Q ε :=
  ⟨IsKazhdanPair.toComplex, IsKazhdanPairComplex.toReal⟩

/-- Property `(T)` as formalized here is exactly the textbook complex-unitary
property `(T)`. -/
theorem hasKazhdanPropertyT_iff_complex :
    HasKazhdanPropertyT.{u, v} G ↔ HasKazhdanPropertyTComplex.{u, v} G := by
  constructor
  · rintro ⟨Q, a, h⟩
    exact ⟨Q, a, h.toComplex⟩
  · rintro ⟨Q, a, h⟩
    exact ⟨Q, a, h.toReal⟩

end NonsoficGroupsExist
