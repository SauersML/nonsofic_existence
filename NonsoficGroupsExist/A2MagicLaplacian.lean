import NonsoficGroupsExist.A2MagicGraph

/-!
# The explicit Laplacian of the A₂ magic graph

This is the four-regular graph `K₆` with the three opposite pairs removed.
All formulas are stated on the concrete `Fin 6` indexing, so its spectral
constant is proved by finite Hilbert-space algebra rather than imported as a
graph-theoretic assertion.
-/

namespace NonsoficGroupsExist

universe v

namespace A2MagicLaplacian

open A2MagicGraph

variable {E : Type v} [NormedAddCommGroup E]

/-- Sum of the six coordinates. -/
def total (f : Fin 6 → E) : E := ∑ i, f i

/-- The unnormalized degree-four graph Laplacian. -/
def laplacian (f : Fin 6 → E) (i : Fin 6) : E :=
  ∑ n : Fin 4, (f i - f (neighborIndex i n))

/-- Each vertex sees every vertex except itself and its opposite. -/
theorem laplacian_eq_five_smul_add_opposite_sub_total
    (f : Fin 6 → E) (i : Fin 6) :
    laplacian f i = 5 • f i + f (oppositeIndex i) - total f := by
  fin_cases i <;>
    simp [laplacian, total, neighborIndex, oppositeIndex, Fin.sum_univ_succ] <;>
    module

/-- The six Laplacian coordinates sum to zero. -/
theorem sum_laplacian (f : Fin 6 → E) : ∑ i, laplacian f i = 0 := by
  simp [laplacian, neighborIndex, Fin.sum_univ_succ]
  module

/-- Adding a constant family does not change the Laplacian. -/
theorem laplacian_add_const (f : Fin 6 → E) (x : E) (i : Fin 6) :
    laplacian (fun j ↦ f j + x) i = laplacian f i := by
  simp [laplacian]

/-- The Laplacian of a constant family is zero. -/
@[simp] theorem laplacian_const (x : E) (i : Fin 6) :
    laplacian (fun _ ↦ x) i = 0 := by
  simp [laplacian]

end A2MagicLaplacian
end NonsoficGroupsExist
