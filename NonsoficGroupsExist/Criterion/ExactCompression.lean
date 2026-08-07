import NonsoficGroupsExist.Sofic.Sofic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Exact compressions normalize for free

Theorem `thm:local` spends its length forcing a *two-sided* comparison out of
the one-sided hypothesis \eqref{eq:gen}: a compressor `t` satisfies only
`tΓt⁻¹ ≤ Γ`, and the median normalization, the co-area inequality and the
matching argument exist to upgrade that to an almost-equality of component
sizes.

None of that machinery is needed when the action is *exact*.  This file proves
the exact statement, and it is three lines: for a genuine action on a finite
set, the `Γ`-fixed points of the compressed subgroup are the image of the
`Γ`-fixed points,

  `Fix(tΓt⁻¹) = φ(t) • Fix(Γ)`,

while `tΓt⁻¹ ≤ Γ` gives `Fix(Γ) ⊆ Fix(tΓt⁻¹)`.  A finite set contained in its
own bijective image equals it, so `φ(t)` maps `Fix(Γ)` *onto* itself, with no
expansion, no medians, and no property `(T)`.  Since the compressors together
with `Γ` generate the ambient group, `Fix(Γ)` is invariant under everything
(`fixedSet_smul_eq_of_closure`).

This is the honest measure of what the approximation-theoretic sections buy.
The compression--centralizer mechanism is trivial for exact actions; the entire
difficulty of Theorem `thm:local` is that a sofic approximation is not one, and
the same is true of the unitary analogue, where finite dimension plays the role
that finiteness of the vertex set plays here.
-/

namespace NonsoficGroupsExist

variable {G Y : Type*} [Group G]

/-- The points fixed by every element of `Γ`. -/
def fixedSet (φ : G →* Equiv.Perm Y) (Γ : Subgroup G) : Set Y :=
  {y | ∀ γ ∈ Γ, φ γ y = y}

theorem mem_fixedSet {φ : G →* Equiv.Perm Y} {Γ : Subgroup G} {y : Y} :
    y ∈ fixedSet φ Γ ↔ ∀ γ ∈ Γ, φ γ y = y := Iff.rfl

/-- Conjugating the group translates the fixed set: the points fixed by
`tΓt⁻¹` are exactly the `φ(t)`-image of the points fixed by `Γ`. -/
theorem fixedSet_conj (φ : G →* Equiv.Perm Y) (Γ : Subgroup G) (t : G) :
    {y : Y | ∀ γ ∈ Γ, φ (t * γ * t⁻¹) y = y} = φ t '' fixedSet φ Γ := by
  ext y
  constructor
  · intro hy
    refine ⟨(φ t)⁻¹ y, fun γ hγ ↦ ?_, by simp⟩
    have h := hy γ hγ
    rw [map_mul, map_mul, map_inv] at h
    have h' : (φ t) ((φ γ) ((φ t)⁻¹ y)) = y := h
    calc (φ γ) ((φ t)⁻¹ y) = (φ t)⁻¹ ((φ t) ((φ γ) ((φ t)⁻¹ y))) := by simp
      _ = (φ t)⁻¹ y := by rw [h']
  · rintro ⟨z, hz, rfl⟩ γ hγ
    rw [map_mul, map_mul, map_inv]
    show (φ t) ((φ γ) ((φ t)⁻¹ ((φ t) z))) = (φ t) z
    simp [hz γ hγ]

/-- **One-sided compression is two-sided on a finite set.**  If `t` compresses
`Γ`, then `φ(t)` maps the `Γ`-fixed set onto itself.  Finiteness is the whole
argument: the fixed set sits inside its own bijective image. -/
theorem fixedSet_image_eq [Finite Y] (φ : G →* Equiv.Perm Y) (Γ : Subgroup G)
    {t : G} (ht : ∀ γ ∈ Γ, t * γ * t⁻¹ ∈ Γ) :
    φ t '' fixedSet φ Γ = fixedSet φ Γ := by
  classical
  have hsub : fixedSet φ Γ ⊆ φ t '' fixedSet φ Γ := by
    rw [← fixedSet_conj]
    intro y hy γ hγ
    exact hy _ (ht γ hγ)
  have hcard : (φ t '' fixedSet φ Γ).ncard = (fixedSet φ Γ).ncard :=
    Set.ncard_image_of_injective _ (Equiv.injective _)
  exact (Set.eq_of_subset_of_ncard_le hsub (le_of_eq hcard)
    (Set.toFinite _)).symm

/-- The fixed set is invariant under every compressor, hence under everything
they generate together with `Γ`.  This is the exact-action shadow of the
matching argument of Theorem `thm:local`. -/
theorem fixedSet_smul_eq_of_closure [Finite Y] (φ : G →* Equiv.Perm Y)
    (Γ : Subgroup G) (T : Set G) (hT : ∀ t ∈ T, ∀ γ ∈ Γ, t * γ * t⁻¹ ∈ Γ)
    (hgen : Subgroup.closure ((Γ : Set G) ∪ T) = ⊤) (g : G) :
    φ g '' fixedSet φ Γ = fixedSet φ Γ := by
  classical
  -- the elements acting invariantly form a subgroup containing `Γ` and `T`
  have hmem : ∀ x ∈ Subgroup.closure ((Γ : Set G) ∪ T),
      φ x '' fixedSet φ Γ = fixedSet φ Γ := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
        rcases hy with hyΓ | hyT
        · -- an element of `Γ` fixes the fixed set pointwise
          ext z
          constructor
          · rintro ⟨w, hw, rfl⟩
            rw [hw y hyΓ]
            exact hw
          · intro hz
            exact ⟨z, hz, hz y hyΓ⟩
        · exact fixedSet_image_eq φ Γ (hT y hyT)
    | one => simp
    | mul a b _ _ iha ihb => rw [map_mul, Equiv.Perm.coe_mul, Set.image_comp, ihb, iha]
    | inv a _ iha =>
        rw [map_inv]
        have hid : ((φ a)⁻¹ : Equiv.Perm Y) '' (((φ a) : Equiv.Perm Y) '' fixedSet φ Γ)
            = fixedSet φ Γ := by
          rw [← Set.image_comp]
          simp
        rw [iha] at hid
        exact hid
  exact hmem g (hgen ▸ Subgroup.mem_top g)

/-! ## The linear category

The same collapse, with finite dimension in place of finiteness of the vertex
set.  This is the form the unitary analogue uses: a one-sided compression of
`Γ` moves the `Γ`-fixed subspace onto itself, so for genuine finite-dimensional
representations the normalization the matching argument works for is automatic.
-/

section Linear

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- The subspace fixed by every element of `Γ`. -/
def fixedSubmodule (σ : G →* (V ≃ₗ[k] V)) (Γ : Subgroup G) : Submodule k V where
  carrier := {v | ∀ γ ∈ Γ, σ γ v = v}
  zero_mem' := by intro γ _; simp
  add_mem' := by
    intro a b ha hb γ hγ
    rw [map_add, ha γ hγ, hb γ hγ]
  smul_mem' := by
    intro c a ha γ hγ
    rw [map_smul, ha γ hγ]

theorem mem_fixedSubmodule {σ : G →* (V ≃ₗ[k] V)} {Γ : Subgroup G} {v : V} :
    v ∈ fixedSubmodule σ Γ ↔ ∀ γ ∈ Γ, σ γ v = v := Iff.rfl

/-- **One-sided compression is two-sided in finite dimension.**  The `Γ`-fixed
subspace is carried onto itself by any compressor, with no hypothesis beyond
`tΓt⁻¹ ≤ Γ` and finite dimension. -/
theorem fixedSubmodule_map_eq [FiniteDimensional k V] (σ : G →* (V ≃ₗ[k] V))
    (Γ : Subgroup G) {t : G} (ht : ∀ γ ∈ Γ, t * γ * t⁻¹ ∈ Γ) :
    (fixedSubmodule σ Γ).map (σ t : V →ₗ[k] V) = fixedSubmodule σ Γ := by
  have hle : fixedSubmodule σ Γ ≤ (fixedSubmodule σ Γ).map (σ t : V →ₗ[k] V) := by
    intro v hv
    refine ⟨(σ t).symm v, fun γ hγ ↦ ?_, by simp⟩
    have hconj : σ (t * γ * t⁻¹) v = v := hv _ (ht γ hγ)
    rw [map_mul, map_mul, map_inv] at hconj
    have happ : (σ t) ((σ γ) ((σ t)⁻¹ v)) = v := hconj
    have : (σ t).symm ((σ t) ((σ γ) ((σ t)⁻¹ v))) = (σ t).symm v := by rw [happ]
    simpa using this
  have hiso : (fixedSubmodule σ Γ) ≃ₗ[k]
      ((fixedSubmodule σ Γ).map (σ t : V →ₗ[k] V)) :=
    Submodule.equivMapOfInjective _ (σ t).injective _
  exact (Submodule.eq_of_le_of_finrank_le hle (le_of_eq hiso.finrank_eq.symm)).symm

end Linear

end NonsoficGroupsExist
