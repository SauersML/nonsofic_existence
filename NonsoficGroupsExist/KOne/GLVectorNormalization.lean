import NonsoficGroupsExist.KOne.GLPairNormalization

/-!
# A nonzero vector as a column of an invertible matrix

The single-vector companion of `exists_isUnit_matrix_mulVec_pair`:
any nonzero vector is `G *ᵥ (Pi.single j₀ 1)` — the `j₀`-th column —
of some invertible scalar matrix `G`.  This is the right
`GL(k)`-normalization pulling a kernel vector of the pencil stacks
into a coordinate column.
-/

namespace NonsoficGroupsExist

open Module

theorem exists_isUnit_matrix_col {k : Type*} [Field k]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {v : ι → k} (hv : v ≠ 0) (j₀ : ι) :
    ∃ G : Matrix ι ι k, IsUnit G ∧
      G.mulVec (Pi.single j₀ 1) = v := by
  classical
  -- `linearIndependent_unique` is now the iff form `linearIndependent_unique_iff`
  have hli : LinearIndependent k ![v] :=
    linearIndependent_unique_iff.mpr (by simpa using hv)
  have hrange : LinearIndepOn k id (Set.range ![v]) :=
    hli.linearIndepOn_id
  set B : Basis (hrange.extend (Set.subset_univ _)) k (ι → k) :=
    Basis.extend hrange with hB
  have hvS : v ∈ hrange.extend (Set.subset_univ _) :=
    hrange.subset_extend _ ⟨0, by simp⟩
  haveI : Fintype (hrange.extend (Set.subset_univ _)) :=
    FiniteDimensional.fintypeBasisIndex B
  have hcard : Fintype.card (hrange.extend (Set.subset_univ _)) =
      Fintype.card ι := by
    rw [← Module.finrank_eq_card_basis B, Module.finrank_pi]
  obtain ⟨e⟩ := Fintype.card_eq.mp hcard
  set pv : hrange.extend (Set.subset_univ _) := ⟨v, hvS⟩ with hpv
  set e₁ := e.trans (Equiv.swap (e pv) j₀) with he₁
  have he₁v : e₁ pv = j₀ := by
    rw [he₁]
    simp [Equiv.swap_apply_left]
  set f : (ι → k) ≃ₗ[k] (ι → k) := B.equiv (Pi.basisFun k ι) e₁
    with hf
  have hfv : f v = Pi.single j₀ 1 := by
    have h1 : v = B pv := by
      rw [hB, Basis.extend_apply_self]
    rw [h1, hf, Basis.equiv_apply, he₁v, Pi.basisFun_apply]
  refine ⟨LinearMap.toMatrix' (f.symm : (ι → k) →ₗ[k] (ι → k)),
    ⟨⟨LinearMap.toMatrix' (f.symm : (ι → k) →ₗ[k] (ι → k)),
      LinearMap.toMatrix' (f : (ι → k) →ₗ[k] (ι → k)), ?_, ?_⟩,
      rfl⟩, ?_⟩
  · rw [← LinearMap.toMatrix'_comp]
    have hcomp : (f.symm : (ι → k) →ₗ[k] (ι → k)).comp
        (f : (ι → k) →ₗ[k] (ι → k)) = LinearMap.id := by
      ext x
      simp
    rw [hcomp, LinearMap.toMatrix'_id]
  · rw [← LinearMap.toMatrix'_comp]
    have hcomp : (f : (ι → k) →ₗ[k] (ι → k)).comp
        (f.symm : (ι → k) →ₗ[k] (ι → k)) = LinearMap.id := by
      ext x
      simp
    rw [hcomp, LinearMap.toMatrix'_id]
  · rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix', ← hfv]
    exact f.symm_apply_apply v

end NonsoficGroupsExist
