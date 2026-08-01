import Mathlib.Tactic.NormNum
import NonsoficGroupsExist.Sofic

/-!
# Finite multigraphs and median edge cases

Edges are bundled occurrences rather than endpoint pairs.  Consequently all
boundary cardinalities count parallel edges with their multiplicities.
-/

namespace NonsoficGroupsExist

/-- A finite loopless multigraph.  Distinct elements of `edge` may have the
same endpoints and remain distinct edge occurrences. -/
structure FiniteMultiGraph where
  vertex : FiniteModel
  edge : FiniteModel
  first : edge → vertex
  second : edge → vertex
  loopless : ∀ e, first e ≠ second e

namespace FiniteMultiGraph

/-- Boundary edge occurrences of a vertex finset. -/
def boundary (X : FiniteMultiGraph) (U : Finset X.vertex) : Finset X.edge :=
  Finset.univ.filter fun e ↦
    (X.first e ∈ U ∧ X.second e ∉ U) ∨ (X.second e ∈ U ∧ X.first e ∉ U)

/-- Boundary cardinality, counting edge occurrences and hence multiplicity. -/
def boundaryCard (X : FiniteMultiGraph) (U : Finset X.vertex) : ℕ :=
  (X.boundary U).card

/-- The explicit quantitative assertion that every nonempty set of at most
half the vertices has boundary ratio at least `h`. -/
def HasCheegerLowerBound (X : FiniteMultiGraph) (h : ℝ) : Prop :=
  0 < h ∧ ∀ U : Finset X.vertex, U.Nonempty →
    2 * U.card ≤ Fintype.card X.vertex →
      h * U.card ≤ X.boundaryCard U

/-- A finite-sample median, stated without division so singleton and empty
edge cases remain explicit. -/
def IsMedian {Y : FiniteModel} (f : Y → ℝ) (c : ℝ) : Prop :=
  2 * (Finset.univ.filter fun y ↦ c < f y).card ≤ Fintype.card Y ∧
    2 * (Finset.univ.filter fun y ↦ f y < c).card ≤ Fintype.card Y

/-- The audited one-vertex endpoint of the co-area argument: the two median
inequalities force the unique value to equal the median. -/
theorem IsMedian.eq_of_subsingleton {Y : FiniteModel} [Nonempty Y] [Subsingleton Y]
    {f : Y → ℝ} {c : ℝ} (hc : IsMedian f c) : ∀ y, f y = c := by
  intro y
  letI : Unique Y :=
    { default := Classical.choice (inferInstance : Nonempty Y)
      uniq := fun _ ↦ Subsingleton.elim _ _ }
  have hcard : Fintype.card Y = 1 := Fintype.card_unique
  have hnotGreater : ¬c < f y := by
    intro hy
    have hfilter : (Finset.univ.filter fun z ↦ c < f z) = Finset.univ := by
      ext z
      simp [Subsingleton.elim z y, hy]
    have h := hc.1
    rw [hfilter, Finset.card_univ, hcard] at h
    norm_num at h
  have hnotLess : ¬f y < c := by
    intro hy
    have hfilter : (Finset.univ.filter fun z ↦ f z < c) = Finset.univ := by
      ext z
      simp [Subsingleton.elim z y, hy]
    have h := hc.2
    rw [hfilter, Finset.card_univ, hcard] at h
    norm_num at h
  exact le_antisymm (not_lt.mp hnotGreater) (not_lt.mp hnotLess)

end FiniteMultiGraph
end NonsoficGroupsExist
