import NonsoficGroupsExist.LeavittGradingSpans
import NonsoficGroupsExist.LeavittDiagonalClass

/-!
# Balanced units lie in the diagonal class group

Over a Leavitt family the central-scalar collapse (`c ≡ c²`, hence
`c ≡ 1`, modulo the diagonal class) upgrades the degree-zero
`centralClassGroup` conclusion to outright membership in the diagonal
class group: every unit whose value lies in a balanced span is in `H`.
In particular every equal-length code-permutation unit — a value
`Σ s_{vᵢ} t_{wᵢ}` with all words of one common length — is in `H`,
which is the balanced half of Step C of the Laurent endgame.
-/

namespace NonsoficGroupsExist
namespace LeavittFamily

open MatrixDiagonalization

variable {A : Type*} [Ring A] (L : LeavittFamily A)

include L in
/-- Over a Leavitt family, the central class group collapses into the
diagonal class group: central scalars are trivial by the corner-sum
squaring identity. -/
theorem centralClassGroup_le_stableUnits [Nontrivial A]
    (hdiv : ∀ x : A, x ≠ 0 → ∃ p q : A, p * x * q = 1) :
    centralClassGroup A ≤ stableUnits A := by
  rintro u ⟨c, hc, hmem⟩
  have hcH : c ∈ stableUnits A := L.central_mem_stableUnits hdiv c hc
  have := mul_mem hcH hmem
  rwa [mul_inv_cancel_left] at this

section Balanced

variable {k : Type*} [Field k] [Algebra k A]

/-- **Balanced units are in the diagonal class group**: a unit whose
value lies in the balanced span at any depth is in `H`. -/
theorem mem_stableUnits_of_val_mem_levelSpan [Nontrivial A]
    (hdiv : ∀ x : A, x ≠ 0 → ∃ p q : A, p * x * q = 1)
    (n : ℕ) (u : Aˣ)
    (hu : (u : A) ∈ Submodule.span k (L.levelMonomials n)) :
    u ∈ stableUnits A :=
  L.centralClassGroup_le_stableUnits hdiv
    (L.mem_centralClassGroup_of_val_mem_levelSpan hdiv n u hu)

/-- The identity is a balanced value at every depth. -/
theorem one_mem_span_levelMonomials (n : ℕ) :
    (1 : A) ∈ Submodule.span k (L.levelMonomials n) := by
  have hc := L.fullBinaryCode_complete n
  have h1 : (1 : A) = ∑ f : Fin n → Fin 2,
      L.wordS (List.ofFn f) * L.wordT (List.ofFn f) := by
    have := hc
    unfold IsComplete at this
    exact this.symm
  rw [h1]
  refine Submodule.sum_mem _ fun f _ ↦ Submodule.subset_span ?_
  exact ⟨f, f, rfl⟩

/-- Balanced monomials are balanced values. -/
theorem monomial_mem_span_levelMonomials (n : ℕ) {a b : List (Fin 2)}
    (ha : a.length = n) (hb : b.length = n) :
    L.wordS a * L.wordT b ∈
      Submodule.span k (L.levelMonomials n) := by
  refine Submodule.subset_span ?_
  rw [levelMonomials_eq]
  exact ⟨a, b, ha, hb, rfl⟩

end Balanced

end LeavittFamily
end NonsoficGroupsExist
