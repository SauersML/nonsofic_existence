import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Normalizing an independent pair by an invertible scalar matrix

Over a field, any linearly independent pair of vectors in `ι → k` is
carried to any two prescribed distinct standard basis vectors by an
invertible matrix: extend the pair to a basis, re-index it by a
bijection prescribing the two values, and take the change-of-basis
matrix.  This supplies the left `GL(k)`-move that puts a pure-`t`
pencil column into the exact shift-atom shape consumed by the peel.
-/

namespace NonsoficGroupsExist

open Module

theorem exists_isUnit_matrix_mulVec_pair {k : Type*} [Field k]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b : ι → k} (hab : LinearIndependent k ![a, b])
    (i₁ i₂ : ι) (hne : i₁ ≠ i₂) :
    ∃ G : Matrix ι ι k, IsUnit G ∧
      G.mulVec a = Pi.single i₁ 1 ∧ G.mulVec b = Pi.single i₂ 1 := by
  classical
  have hane : a ≠ b := by
    intro h
    have h01 : (![a, b] : Fin 2 → ι → k) 0 = ![a, b] 1 := by
      simp [h]
    exact (by decide : (0 : Fin 2) ≠ 1) (hab.injective h01)
  -- extend the pair to a basis
  -- `LinearIndependent.to_subtype_range` is now `linearIndepOn_id`, phrased
  -- as `LinearIndepOn k id (Set.range ![a, b])`.
  have hrange : LinearIndepOn k id (Set.range ![a, b]) :=
    hab.linearIndepOn_id
  set B : Basis (hrange.extend (Set.subset_univ _)) k (ι → k) :=
    Basis.extend hrange with hB
  have haS : a ∈ hrange.extend (Set.subset_univ _) :=
    hrange.subset_extend _ ⟨0, by simp⟩
  have hbS : b ∈ hrange.extend (Set.subset_univ _) :=
    hrange.subset_extend _ ⟨1, by simp⟩
  haveI : Fintype (hrange.extend (Set.subset_univ _)) :=
    FiniteDimensional.fintypeBasisIndex B
  -- a bijection to `ι` prescribing the two values
  have hcard : Fintype.card (hrange.extend (Set.subset_univ _)) =
      Fintype.card ι := by
    rw [← Module.finrank_eq_card_basis B, Module.finrank_pi]
  obtain ⟨e⟩ := Fintype.card_eq.mp hcard
  set pa : hrange.extend (Set.subset_univ _) := ⟨a, haS⟩ with hpa
  set pb : hrange.extend (Set.subset_univ _) := ⟨b, hbS⟩ with hpb
  have hpab : pa ≠ pb := fun h ↦ hane (congrArg Subtype.val h)
  set e₁ := e.trans (Equiv.swap (e pa) i₁) with he₁
  have he₁a : e₁ pa = i₁ := by
    rw [he₁]
    simp [Equiv.swap_apply_left]
  set e₂ := e₁.trans (Equiv.swap (e₁ pb) i₂) with he₂
  have he₂b : e₂ pb = i₂ := by
    rw [he₂]
    simp [Equiv.swap_apply_left]
  have he₂a : e₂ pa = i₁ := by
    rw [he₂]
    have h1 : e₁ pb ≠ i₁ := by
      rw [← he₁a]
      -- `e₁.injective h.symm : pa = pb` already; the extra `.symm` flipped it
      exact fun h ↦ hpab (e₁.injective h.symm)
    simp only [Equiv.trans_apply, he₁a]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm h1) hne
  -- the change-of-basis equivalence
  set f : (ι → k) ≃ₗ[k] (ι → k) := B.equiv (Pi.basisFun k ι) e₂
    with hf
  have hfa : f a = Pi.single i₁ 1 := by
    have h1 : a = B pa := by
      rw [hB, Basis.extend_apply_self]
    rw [h1, hf, Basis.equiv_apply, he₂a, Pi.basisFun_apply]
  have hfb : f b = Pi.single i₂ 1 := by
    have h1 : b = B pb := by
      rw [hB, Basis.extend_apply_self]
    rw [h1, hf, Basis.equiv_apply, he₂b, Pi.basisFun_apply]
  -- the matrix
  refine ⟨LinearMap.toMatrix' (f : (ι → k) →ₗ[k] (ι → k)),
    ⟨⟨LinearMap.toMatrix' (f : (ι → k) →ₗ[k] (ι → k)),
      LinearMap.toMatrix' (f.symm : (ι → k) →ₗ[k] (ι → k)), ?_, ?_⟩,
      rfl⟩, ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp]
    have hcomp : (f : (ι → k) →ₗ[k] (ι → k)).comp
        (f.symm : (ι → k) →ₗ[k] (ι → k)) = LinearMap.id := by
      ext v
      simp
    rw [hcomp, LinearMap.toMatrix'_id]
  · rw [← LinearMap.toMatrix'_comp]
    have hcomp : (f.symm : (ι → k) →ₗ[k] (ι → k)).comp
        (f : (ι → k) →ₗ[k] (ι → k)) = LinearMap.id := by
      ext v
      simp
    rw [hcomp, LinearMap.toMatrix'_id]
  · rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    exact hfa
  · rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    exact hfb

end NonsoficGroupsExist
