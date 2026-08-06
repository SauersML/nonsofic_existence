import NonsoficGroupsExist.Matching.FiniteGraph
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Median pinning

This file formalizes Lemma `lem:pin` of the manuscript.  A graph all of whose
components expand, carrying a function whose componentwise median is `1/2`,
concentrates that function at `1/2` in `L¹` at a cost controlled by the total
edge variation.

A decomposition into components is presented as a finite family of graphs; every
edge of the manuscript's `Z` lies inside a component, so summing the co-area
estimate of `FiniteMultiGraph.coarea_mul` over the family is exactly the
manuscript's one-line proof.

The file also records the transfer of medians along an increasing
reparametrization, which is how the manuscript passes from a median of the
component sizes to the median `1/2` of the normalization `s/(s+m)`.
-/

namespace NonsoficGroupsExist
namespace FiniteMultiGraph

open scoped BigOperators

/-- Medians transfer along any map that is strictly increasing on the range of
the observable.  Applied with `φ t = t/(t+m)` this turns a median of the
component sizes into the median `1/2` of the normalization. -/
theorem IsMedian.comp_increasing {Y : FiniteModel} {s : Y → ℝ} {m : ℝ}
    (hs : ∀ y, 0 ≤ s y) (hm : 0 ≤ m) (hmed : IsMedian s m) (φ : ℝ → ℝ)
    (hφ : ∀ a b, 0 ≤ a → 0 ≤ b → (a < b ↔ φ a < φ b)) :
    IsMedian (fun y ↦ φ (s y)) (φ m) := by
  classical
  constructor
  · have hset : (Finset.univ.filter fun y ↦ φ m < φ (s y)) =
        Finset.univ.filter fun y ↦ m < s y := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hφ m (s y) hm (hs y)).symm
    rw [hset]
    exact hmed.1
  · have hset : (Finset.univ.filter fun y ↦ φ (s y) < φ m) =
        Finset.univ.filter fun y ↦ s y < m := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hφ (s y) m (hs y) hm).symm
    rw [hset]
    exact hmed.2

/-- **Lemma `lem:pin`**, in denominator-free form. -/
theorem median_pinning_mul {κ : Type*} [Fintype κ] (X : κ → FiniteMultiGraph)
    {h : ℝ} (hch : ∀ k, (X k).HasCheegerLowerBound h)
    (f : ∀ k, (X k).vertex → ℝ) (hmed : ∀ k, IsMedian (f k) (1 / 2)) :
    h * ∑ k, ∑ x, |f k x - 1 / 2| ≤ ∑ k, (X k).edgeVariation (f k) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  exact coarea_mul (X k) (hch k) (f k) (1 / 2) (hmed k)

/-- **Lemma `lem:pin`** as displayed in the manuscript. -/
theorem median_pinning {κ : Type*} [Fintype κ] (X : κ → FiniteMultiGraph)
    {h : ℝ} (hch : ∀ k, (X k).HasCheegerLowerBound h)
    (f : ∀ k, (X k).vertex → ℝ) (hmed : ∀ k, IsMedian (f k) (1 / 2))
    (hκ : Nonempty κ) :
    ∑ k, ∑ x, |f k x - 1 / 2| ≤ (1 / h) * ∑ k, (X k).edgeVariation (f k) := by
  have hpos : 0 < h := (hch (Classical.choice hκ)).1
  have hmul := median_pinning_mul X hch f hmed
  calc
    ∑ k, ∑ x, |f k x - 1 / 2| ≤
        (∑ k, (X k).edgeVariation (f k)) / h :=
      (le_div_iff₀ hpos).2 (by simpa [mul_comm] using hmul)
    _ = (1 / h) * ∑ k, (X k).edgeVariation (f k) := by ring

end FiniteMultiGraph
end NonsoficGroupsExist
