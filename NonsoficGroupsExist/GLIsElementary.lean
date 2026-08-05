import NonsoficGroupsExist.DiagonalClassGroup
import NonsoficGroupsExist.LeavittSelfSimilarity

/-!
# `GL = EL` from Gaussian elimination and the diagonal class

Checkpoint `B5`: over a ring with the strong division property whose
diagonal class group is everything (`diag(u, 1) ∈ EL₂` for every unit —
the checkpoint-`B4` input), every invertible two-by-two matrix is
elementary, by the proved rank-two Gaussian elimination.  The rank-four
case follows with no new elimination: `GL₄ ≅ GL₂(M₂)` by block
flattening, the self-similarity isomorphism `M₂(R) ≃+* R` transports
both hypotheses to `M₂(R)`, and the elementary groups match up under
the same flattening (`elementaryBlockGroup_map`).
-/

namespace NonsoficGroupsExist
namespace MatrixDiagonalization

variable {R : Type*} [Ring R]

/-- Rank-two `GL = EL` from strong division and the diagonal-class
input. -/
theorem mem_elementaryGroup_of_division_of_stable [Nontrivial R]
    (hdiv : ∀ x : R, x ≠ 0 → ∃ p q : R, p * x * q = 1)
    (hK1 : ∀ u : Rˣ, diagUnit u ∈ elementaryGroup (Fin 2) R)
    (A : (Matrix (Fin 2) (Fin 2) R)ˣ) :
    A ∈ elementaryGroup (Fin 2) R := by
  obtain ⟨E, F, u, hE, hF, hEAF⟩ := exists_elementary_mul_diag hdiv A
  have hA : A = E⁻¹ * diagUnit u * F⁻¹ := by
    rw [← hEAF]
    group
  rw [hA]
  exact mul_mem (mul_mem (inv_mem hE) (hK1 u)) (inv_mem hF)

section Transport

variable {S : Type*} [Ring S]

/-- Strong division transports along ring isomorphisms. -/
theorem division_of_ringEquiv (e : R ≃+* S)
    (hdiv : ∀ x : S, x ≠ 0 → ∃ p q : S, p * x * q = 1) :
    ∀ x : R, x ≠ 0 → ∃ p q : R, p * x * q = 1 := by
  intro x hx
  have hex : e x ≠ 0 := by
    intro h0
    apply hx
    have := congrArg e.symm h0
    simpa using this
  obtain ⟨p, q, hpq⟩ := hdiv (e x) hex
  refine ⟨e.symm p, e.symm q, ?_⟩
  have := congrArg e.symm hpq
  simpa [map_mul] using this

theorem elementaryMatrixUnitMap_diagUnit (f : R →+* S) (u : Rˣ) :
    elementaryMatrixUnitMap (ι := Fin 2) f (diagUnit u) =
      diagUnit (Units.map (f : R →* S) u) := by
  apply Units.ext
  show (f.mapMatrix : Matrix (Fin 2) (Fin 2) R →+*
    Matrix (Fin 2) (Fin 2) S) !![(u : R), 0; 0, 1] = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [RingHom.mapMatrix_apply, diagUnit]

/-- The diagonal-class input transports along ring isomorphisms. -/
theorem stable_of_ringEquiv (e : R ≃+* S)
    (hK1 : ∀ u : Sˣ, diagUnit u ∈ elementaryGroup (Fin 2) S) :
    ∀ u : Rˣ, diagUnit u ∈ elementaryGroup (Fin 2) R := by
  intro u
  set v : Sˣ := Units.map ((e : R →+* S) : R →* S) u with hv
  have hmem := hK1 v
  have himg := elementaryGroup_map_le (ι := Fin 2)
    ((e.symm : S →+* R))
    ⟨diagUnit v, hmem, rfl⟩
  have heq : elementaryMatrixUnitMap (ι := Fin 2)
      ((e.symm : S →+* R)) (diagUnit v) = diagUnit u := by
    rw [elementaryMatrixUnitMap_diagUnit]
    congr 1
    apply Units.ext
    rw [hv]
    simp
  rwa [heq] at himg

end Transport

section RankFour

variable [Nontrivial R]

/-- Rank-four `GL = EL` through block flattening and self-similarity:
given the strong division property, the diagonal-class input, and a
self-similarity isomorphism `M₂(R) ≃+* R`, every invertible four-by-four
matrix is elementary. -/
theorem mem_elementaryGroup_four_of_division_of_stable
    (hdiv : ∀ x : R, x ≠ 0 → ∃ p q : R, p * x * q = 1)
    (hK1 : ∀ u : Rˣ, diagUnit u ∈ elementaryGroup (Fin 2) R)
    (e : Matrix (Fin 2) (Fin 2) R ≃+* R)
    (A : (Matrix (Fin 4) (Fin 4) R)ˣ) :
    A ∈ elementaryGroup (Fin 4) R := by
  classical
  -- Transport both hypotheses to `M₂(R)`.
  have hdiv₂ : ∀ x : Matrix (Fin 2) (Fin 2) R, x ≠ 0 →
      ∃ p q : Matrix (Fin 2) (Fin 2) R, p * x * q = 1 :=
    division_of_ringEquiv e hdiv
  have hK1₂ : ∀ u : (Matrix (Fin 2) (Fin 2) R)ˣ,
      diagUnit u ∈ elementaryGroup (Fin 2)
        (Matrix (Fin 2) (Fin 2) R) :=
    stable_of_ringEquiv e hK1
  -- Reindex `Fin 4` as `Fin 2 × Fin 2` and unflatten to blocks.
  set e4 : Fin 2 × Fin 2 ≃ Fin 4 :=
    (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin (2 * 2))
  set A' : (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) R)ˣ :=
    (elementaryReindexUnitEquiv (R := R) e4).symm A with hA'
  set X : (Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) R))ˣ :=
    (elementaryBlockUnitEquiv (ι := Fin 2) (κ := Fin 2)
      (R := R)).symm A' with hX
  -- The block matrix is elementary over `M₂(R)`.
  have hXmem : X ∈ elementaryGroup (Fin 2) (Matrix (Fin 2) (Fin 2) R) :=
    mem_elementaryGroup_of_division_of_stable hdiv₂ hK1₂ X
  -- Push forward through the flattening and the reindexing.
  have hA'mem : A' ∈ elementaryGroup (Fin 2 × Fin 2) R := by
    rw [← elementaryBlockGroup_map (ι := Fin 2) (κ := Fin 2) (R := R)]
    refine ⟨X, hXmem, ?_⟩
    rw [hX]
    simp
  have hAmem : A ∈ elementaryGroup (Fin 4) R := by
    rw [← elementaryReindexGroup_map (R := R) e4]
    refine ⟨A', hA'mem, ?_⟩
    rw [hA']
    simp
  exact hAmem

end RankFour

end MatrixDiagonalization

namespace LeavittFamily

open MatrixDiagonalization

variable {R : Type*} [Ring R] [Nontrivial R]

/-- **Checkpoint `B5`, conditional form**: over a binary Leavitt ring
with the strong division property, the diagonal-class input `K₁ = 0`
forces `GL₂ = EL₂` and `GL₄ = EL₄`.  The self-similarity isomorphism is
the ring's own `binaryMatrixRingEquiv`. -/
theorem glFour_eq_elementary_of_stable (L : LeavittFamily R)
    (hdiv : ∀ x : R, x ≠ 0 → ∃ p q : R, p * x * q = 1)
    (hK1 : ∀ u : Rˣ, diagUnit u ∈ elementaryGroup (Fin 2) R)
    (A : (Matrix (Fin 4) (Fin 4) R)ˣ) :
    A ∈ elementaryGroup (Fin 4) R :=
  mem_elementaryGroup_four_of_division_of_stable hdiv hK1
    (L.binaryMatrixRingEquiv) A

end LeavittFamily
end NonsoficGroupsExist
