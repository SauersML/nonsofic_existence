import NonsoficGroupsExist.WindowNonposReduction
import NonsoficGroupsExist.CodeChangeUnits
import NonsoficGroupsExist.ResidualReduction

/-!
# Triangular factorization implies the narrow-window kill

The three one-sided classes are now all in the diagonal class group:
units with values in nonnegative windows, units with values in
nonpositive windows, and code-change units between complete prefix
codes.  Consequently the narrow-window kill (`NarrowReduction`)
reduces to the Birkhoff-style triangular factorization statement:
every narrow unit is a product of a nonpositive-window unit, a
code-change unit, and a nonnegative-window unit.  This file states
the factorization and performs the reduction, so the sole remaining
input of the `K₁`-vanishing chain is `TriangularFactorization`.
-/

namespace NonsoficGroupsExist
namespace BinaryLeavitt

open LeavittFamily MatrixDiagonalization

variable (k : Type) [Field k]

/-- **The Birkhoff-style factorization statement**: every unit whose
value lies in the narrow window factors as a nonpositive-window unit
times a code-change unit times a nonnegative-window unit. -/
def TriangularFactorization : Prop :=
  ∀ u : (BinaryLeavittAlgebra k)ˣ,
    (u : BinaryLeavittAlgebra k) ∈
      Submodule.span k ((family k).degreeMonomials (-1) 1) →
    ∃ (nneg nposΩ : (BinaryLeavittAlgebra k)ˣ)
      (P : List (List (Fin 2) × List (Fin 2))) (M N : ℕ),
      (nneg : BinaryLeavittAlgebra k) ∈ Submodule.span k
        ((family k).degreeMonomials (-(M : ℤ) - 1) 0) ∧
      ((nposΩ : (BinaryLeavittAlgebra k)ˣ) :
        BinaryLeavittAlgebra k) ∈ Submodule.span k
        ((family k).degreeMonomials 0 ((N : ℤ) + 1)) ∧
      ∃ Ω : (BinaryLeavittAlgebra k)ˣ,
        (family k).IsCompleteCode (P.map Prod.snd) ∧
        (family k).IsCompleteCode (P.map Prod.fst) ∧
        (Ω : BinaryLeavittAlgebra k) = (family k).pairValue P ∧
        u = nneg * Ω * nposΩ

/-- **The factorization closes the chain**: it implies the
narrow-window kill, hence scalar reduction, hence `B4`. -/
theorem narrowReduction_of_triangularFactorization
    [Nontrivial (BinaryLeavittAlgebra k)]
    (hfac : TriangularFactorization k) : NarrowReduction k := by
  intro u hu
  obtain ⟨nneg, nposΩ, P, M, N, hneg, hpos, Ω, hsrc, htgt, hΩ, hu'⟩ :=
    hfac u hu
  have hdiv : ∀ x : BinaryLeavittAlgebra k, x ≠ 0 →
      ∃ p q : BinaryLeavittAlgebra k, p * x * q = 1 :=
    fun x hx ↦ exists_mul_mul_eq_one k hx
  have h1 : nneg ∈ stableUnits (BinaryLeavittAlgebra k) :=
    window_nonpos_mem_stableUnits k M nneg hneg
  have h2 : Ω ∈ stableUnits (BinaryLeavittAlgebra k) :=
    (family k).codeChange_mem_stableUnits (k := k) hdiv P.length P
      rfl hsrc htgt Ω hΩ
  have h3 : nposΩ ∈ stableUnits (BinaryLeavittAlgebra k) :=
    window_nonneg_mem_stableUnits k N nposΩ hpos
  have hmem : u ∈ stableUnits (BinaryLeavittAlgebra k) := by
    rw [hu']
    exact mul_mem (mul_mem h1 h2) h3
  -- `stableUnits_le_centralClassGroup` takes no explicit ring argument;
  -- the ring is inferred from `hmem`.
  exact stableUnits_le_centralClassGroup hmem

end BinaryLeavitt
end NonsoficGroupsExist
