import NonsoficGroupsExist.EdgeEditing
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Fintype.BigOperators

/-!
# From occurrence witnesses to edit distance

An occurrence-level edit witness is stronger than the multiplicity edit
distance used by the essential-expander interface.  This file proves the
uniform conversion bound `editDistance ≤ 2 * unmatchedCount`.
-/

namespace NonsoficGroupsExist

open scoped BigOperators

namespace FiniteMultiGraph

variable (X : FiniteMultiGraph)

def edgeSetMultiplicity (E : Finset X.edge) (x y : X.vertex) : ℕ :=
  (E.filter fun a ↦
    (X.first a = x ∧ X.second a = y) ∨
      (X.first a = y ∧ X.second a = x)).card

theorem edgeSetMultiplicity_univ (x y : X.vertex) :
    X.edgeSetMultiplicity Finset.univ x y = X.edgeMultiplicity x y := rfl

theorem edgeSetMultiplicity_union {E F : Finset X.edge} (hEF : Disjoint E F)
    (x y : X.vertex) :
    X.edgeSetMultiplicity (E ∪ F) x y =
      X.edgeSetMultiplicity E x y + X.edgeSetMultiplicity F x y := by
  unfold edgeSetMultiplicity
  rw [Finset.filter_union, Finset.card_union_of_disjoint]
  exact Finset.disjoint_filter_filter hEF

theorem sum_edgeSetMultiplicity (E : Finset X.edge) :
    ∑ x, ∑ y, X.edgeSetMultiplicity E x y = 2 * E.card := by
  classical
  calc
    ∑ x, ∑ y, X.edgeSetMultiplicity E x y =
        ∑ x, ∑ y, E.sum (fun a ↦
        if (X.first a = x ∧ X.second a = y) ∨
          (X.first a = y ∧ X.second a = x) then (1 : ℕ) else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      unfold edgeSetMultiplicity
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ =
        ∑ x, E.sum (fun a ↦ ∑ y,
          if (X.first a = x ∧ X.second a = y) ∨
            (X.first a = y ∧ X.second a = x) then (1 : ℕ) else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      exact Finset.sum_comm
    _ = E.sum (fun a ↦ ∑ x, ∑ y,
          if (X.first a = x ∧ X.second a = y) ∨
            (X.first a = y ∧ X.second a = x) then (1 : ℕ) else 0) :=
      Finset.sum_comm
    _ = E.sum (fun _a ↦ (2 : ℕ)) := by
      apply Finset.sum_congr rfl
      intro a _
      have hne : X.first a ≠ X.second a := X.loopless a
      have hpoint (x y : X.vertex) :
          (if (X.first a = x ∧ X.second a = y) ∨
              (X.first a = y ∧ X.second a = x) then (1 : ℕ) else 0) =
            (if X.first a = x ∧ X.second a = y then 1 else 0) +
              (if X.first a = y ∧ X.second a = x then 1 else 0) := by
        by_cases hxy : X.first a = x ∧ X.second a = y
        · by_cases hyx : X.first a = y ∧ X.second a = x
          · exact (hne (hxy.1.trans hyx.2.symm)).elim
          · rw [if_pos (Or.inl hxy), if_pos hxy, if_neg hyx, Nat.add_zero]
        · by_cases hyx : X.first a = y ∧ X.second a = x
          · rw [if_pos (Or.inr hyx), if_neg hxy, if_pos hyx, Nat.zero_add]
          · rw [if_neg (not_or_intro hxy hyx), if_neg hxy, if_neg hyx,
              Nat.zero_add]
      have hfirst :
          (∑ x, ∑ y, if X.first a = x ∧ X.second a = y then (1 : ℕ) else 0) =
            1 := by
        calc
          _ = ∑ x, if X.first a = x then (1 : ℕ) else 0 := by
            apply Finset.sum_congr rfl
            intro x _
            by_cases hx : X.first a = x <;> simp [hx]
          _ = 1 := by simp
      have hsecond :
          (∑ x, ∑ y, if X.first a = y ∧ X.second a = x then (1 : ℕ) else 0) =
            1 := by
        calc
          _ = ∑ x, if X.second a = x then (1 : ℕ) else 0 := by
            apply Finset.sum_congr rfl
            intro x _
            by_cases hx : X.second a = x <;> simp [hx]
          _ = 1 := by simp
      simp_rw [hpoint, Finset.sum_add_distrib]
      rw [hfirst, hsecond]
    _ = 2 * E.card := by simp [mul_comm]

/-- Transporting vertices preserves every unordered-pair multiplicity. -/
theorem transport_edgeMultiplicity (Z : FiniteModel) (e : X.vertex ≃ Z)
    (x y : X.vertex) :
    (X.transport Z e).edgeMultiplicity (e x) (e y) = X.edgeMultiplicity x y := by
  unfold edgeMultiplicity
  congr 1
  ext a
  simp

theorem editDistance_triangle (X Z W : FiniteMultiGraph)
    (e : X.vertex ≃ Z.vertex) (f : Z.vertex ≃ W.vertex) :
    X.editDistance W (e.trans f) ≤ X.editDistance Z e + Z.editDistance W f := by
  unfold editDistance
  calc
    _ ≤ ∑ x, ∑ y,
        (((X.edgeMultiplicity x y - Z.edgeMultiplicity (e x) (e y)) +
          (Z.edgeMultiplicity (e x) (e y) - X.edgeMultiplicity x y)) +
        ((Z.edgeMultiplicity (e x) (e y) -
          W.edgeMultiplicity (f (e x)) (f (e y))) +
          (W.edgeMultiplicity (f (e x)) (f (e y)) -
            Z.edgeMultiplicity (e x) (e y)))) := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      simpa only [Nat.dist, Equiv.trans_apply] using Nat.dist.triangle_inequality
        (X.edgeMultiplicity x y) (Z.edgeMultiplicity (e x) (e y))
          (W.edgeMultiplicity (f (e x)) (f (e y)))
    _ = (∑ x, ∑ y,
        ((X.edgeMultiplicity x y - Z.edgeMultiplicity (e x) (e y)) +
          (Z.edgeMultiplicity (e x) (e y) - X.edgeMultiplicity x y))) +
        ∑ x, ∑ y,
        ((Z.edgeMultiplicity (e x) (e y) -
          W.edgeMultiplicity (f (e x)) (f (e y))) +
          (W.edgeMultiplicity (f (e x)) (f (e y)) -
            Z.edgeMultiplicity (e x) (e y))) := by
      simp_rw [Finset.sum_add_distrib]
    _ = X.editDistance Z e + Z.editDistance W f := by
      congr 1
      unfold editDistance
      exact Fintype.sum_equiv e _ _ fun x ↦
        Fintype.sum_equiv e _ _ fun y ↦ rfl

theorem editDistance_transport_right (X Z : FiniteMultiGraph)
    (e : X.vertex ≃ Z.vertex) :
    X.editDistance (Z.transport X.vertex e.symm) (Equiv.refl X.vertex) =
      X.editDistance Z e := by
  unfold editDistance
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  have h := Z.transport_edgeMultiplicity X.vertex e.symm (e x) (e y)
  have h' : (Z.transport X.vertex e.symm).edgeMultiplicity x y =
      Z.edgeMultiplicity (e x) (e y) := by simpa using h
  simp only [Equiv.refl_apply]
  rw [h']

theorem editDistance_transport_both (X Z : FiniteMultiGraph)
    (W : FiniteModel) (e : X.vertex ≃ Z.vertex) (f : X.vertex ≃ W) :
    (X.transport W f).editDistance (Z.transport W (e.symm.trans f))
      (Equiv.refl W) = X.editDistance Z e := by
  unfold editDistance
  let F : W → W → ℕ := fun x y ↦
    ((X.transport W f).edgeMultiplicity x y -
        (Z.transport W (e.symm.trans f)).edgeMultiplicity x y) +
      ((Z.transport W (e.symm.trans f)).edgeMultiplicity x y -
        (X.transport W f).edgeMultiplicity x y)
  have hsum : (∑ x : W, ∑ y : W, F x y) =
      ∑ x : X.vertex, ∑ y : X.vertex, F (f x) (f y) := by
    symm
    calc
      (∑ x : X.vertex, ∑ y : X.vertex, F (f x) (f y)) =
          ∑ x : X.vertex, ∑ y : W, F (f x) y := by
        apply Finset.sum_congr rfl
        intro x _
        exact Fintype.sum_equiv f _ _ fun y ↦ rfl
      _ = ∑ x : W, ∑ y : W, F x y :=
        Fintype.sum_equiv f _ _ fun x ↦ rfl
  change (∑ x : W, ∑ y : W, F x y) = _
  calc
    _ = ∑ x : X.vertex, ∑ y : X.vertex, F (f x) (f y) := hsum
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      dsimp only [F]
      rw [X.transport_edgeMultiplicity W f x y]
      have h := Z.transport_edgeMultiplicity W (e.symm.trans f) (e x) (e y)
      have h' : (Z.transport W (e.symm.trans f)).edgeMultiplicity (f x) (f y) =
          Z.edgeMultiplicity (e x) (e y) := by simpa using h
      rw [h']

/-- Boundary size can decrease by at most the edit distance, up to the fixed
factor two caused by the unordered multiplicity convention. -/
theorem boundaryCard_transport_le_two_mul_add_editDistance
    (X Z : FiniteMultiGraph) (e : X.vertex ≃ Z.vertex)
    (U : Finset X.vertex) :
    (Z.transport X.vertex e.symm).boundaryCard U ≤
      2 * X.boundaryCard U + X.editDistance Z e := by
  let Z' := Z.transport X.vertex e.symm
  have hdirected (p : X.vertex × X.vertex) :
      Z'.directedMultiplicity p.1 p.2 ≤ Z'.edgeMultiplicity p.1 p.2 :=
    Z'.directedMultiplicity_le_edgeMultiplicity p.1 p.2
  have hpoint (p : X.vertex × X.vertex) :
      Z'.edgeMultiplicity p.1 p.2 ≤
        X.edgeMultiplicity p.1 p.2 +
          (Z'.edgeMultiplicity p.1 p.2 - X.edgeMultiplicity p.1 p.2) := by
    omega
  have hfirst : Z'.boundaryCard U ≤
      ∑ p ∈ X.crossingPairs U,
        (X.edgeMultiplicity p.1 p.2 +
          (Z'.edgeMultiplicity p.1 p.2 - X.edgeMultiplicity p.1 p.2)) := by
    rw [← Z'.sum_directedMultiplicity_crossingPairs U]
    exact Finset.sum_le_sum fun p _ ↦ (hdirected p).trans (hpoint p)
  have hrestricted :
      (∑ p ∈ X.crossingPairs U,
        (Z'.edgeMultiplicity p.1 p.2 - X.edgeMultiplicity p.1 p.2)) ≤
      X.editDistance Z' (Equiv.refl X.vertex) := by
    unfold editDistance
    calc
      (∑ p ∈ X.crossingPairs U,
          (Z'.edgeMultiplicity p.1 p.2 - X.edgeMultiplicity p.1 p.2)) ≤
          ∑ p : X.vertex × X.vertex,
            (Z'.edgeMultiplicity p.1 p.2 - X.edgeMultiplicity p.1 p.2) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ _) (fun _ _ _ ↦ by omega)
      _ ≤ ∑ p : X.vertex × X.vertex,
          ((X.edgeMultiplicity p.1 p.2 - Z'.edgeMultiplicity p.1 p.2) +
            (Z'.edgeMultiplicity p.1 p.2 - X.edgeMultiplicity p.1 p.2)) := by
        exact Finset.sum_le_sum fun p _ ↦ by omega
      _ = ∑ x, ∑ y,
          ((X.edgeMultiplicity x y - Z'.edgeMultiplicity x y) +
            (Z'.edgeMultiplicity x y - X.edgeMultiplicity x y)) := by
        rw [Fintype.sum_prod_type]
  calc
    Z'.boundaryCard U ≤
        ∑ p ∈ X.crossingPairs U,
          (X.edgeMultiplicity p.1 p.2 +
            (Z'.edgeMultiplicity p.1 p.2 - X.edgeMultiplicity p.1 p.2)) := hfirst
    _ = (∑ p ∈ X.crossingPairs U, X.edgeMultiplicity p.1 p.2) +
        ∑ p ∈ X.crossingPairs U,
          (Z'.edgeMultiplicity p.1 p.2 - X.edgeMultiplicity p.1 p.2) := by
      rw [Finset.sum_add_distrib]
    _ ≤ 2 * X.boundaryCard U + X.editDistance Z' (Equiv.refl X.vertex) := by
      rw [X.sum_edgeMultiplicity_crossingPairs]
      omega
    _ = 2 * X.boundaryCard U + X.editDistance Z e := by
      rw [X.editDistance_transport_right Z e]

end FiniteMultiGraph

namespace EdgeEditWitness

variable {X Z : FiniteMultiGraph} {e : X.vertex ≃ Z.vertex}
variable (W : EdgeEditWitness X Z e)

private def sourceKeptMultiplicity (x y : X.vertex) : ℕ :=
  X.edgeSetMultiplicity W.sourceKept x y

private def targetKeptMultiplicity (x y : X.vertex) : ℕ :=
  Z.edgeSetMultiplicity W.targetKept (e x) (e y)

private theorem keptMultiplicity_eq (x y : X.vertex) :
    W.sourceKeptMultiplicity x y = W.targetKeptMultiplicity x y := by
  classical
  unfold sourceKeptMultiplicity targetKeptMultiplicity
    FiniteMultiGraph.edgeSetMultiplicity
  apply Finset.card_bij (fun a ha ↦
    (W.edgeEquiv ⟨a, (Finset.mem_filter.mp ha).1⟩).1)
  · intro a ha
    rw [Finset.mem_filter] at ha ⊢
    refine ⟨(W.edgeEquiv ⟨a, ha.1⟩).2, ?_⟩
    rcases ha.2 with hxy | hyx <;>
      rcases W.preservesEndpoints ⟨a, ha.1⟩ with hp | hp
    · exact Or.inl ⟨hp.1.symm.trans (congrArg e hxy.1),
          hp.2.symm.trans (congrArg e hxy.2)⟩
    · exact Or.inr ⟨hp.2.symm.trans (congrArg e hxy.2),
          hp.1.symm.trans (congrArg e hxy.1)⟩
    · exact Or.inr ⟨hp.1.symm.trans (congrArg e hyx.1),
          hp.2.symm.trans (congrArg e hyx.2)⟩
    · exact Or.inl ⟨hp.2.symm.trans (congrArg e hyx.2),
          hp.1.symm.trans (congrArg e hyx.1)⟩
  · intro a ha b hb hab
    have heq : W.edgeEquiv ⟨a, (Finset.mem_filter.mp ha).1⟩ =
        W.edgeEquiv ⟨b, (Finset.mem_filter.mp hb).1⟩ := Subtype.ext hab
    exact congrArg Subtype.val (W.edgeEquiv.injective heq)
  · intro b hb
    let b' : W.targetKept := ⟨b, (Finset.mem_filter.mp hb).1⟩
    let a := W.edgeEquiv.symm b'
    refine ⟨a.1, ?_, congrArg Subtype.val (W.edgeEquiv.apply_symm_apply b')⟩
    rw [Finset.mem_filter]
    refine ⟨a.2, ?_⟩
    have hb' := (Finset.mem_filter.mp hb).2
    have hp := W.preservesEndpoints a
    have heq : W.edgeEquiv a = b' := W.edgeEquiv.apply_symm_apply b'
    rcases hb' with hxy | hyx <;> rcases hp with hp | hp
    · simp only [heq] at hp
      exact Or.inl ⟨e.injective (hp.1.trans hxy.1),
        e.injective (hp.2.trans hxy.2)⟩
    · simp only [heq] at hp
      exact Or.inr ⟨e.injective (hp.1.trans hxy.2),
        e.injective (hp.2.trans hxy.1)⟩
    · simp only [heq] at hp
      exact Or.inr ⟨e.injective (hp.1.trans hyx.1),
        e.injective (hp.2.trans hyx.2)⟩
    · simp only [heq] at hp
      exact Or.inl ⟨e.injective (hp.1.trans hyx.2),
        e.injective (hp.2.trans hyx.1)⟩

private theorem sourceMultiplicity_split (x y : X.vertex) :
    X.edgeMultiplicity x y = W.sourceKeptMultiplicity x y +
      X.edgeSetMultiplicity W.sourceUnmatched x y := by
  have hdisj : Disjoint W.sourceKept W.sourceUnmatched := by
    exact Finset.disjoint_sdiff
  have hunion : W.sourceKept ∪ W.sourceUnmatched = Finset.univ := by
    simp [sourceUnmatched]
  rw [← X.edgeSetMultiplicity_univ, ← hunion,
    X.edgeSetMultiplicity_union hdisj]
  rfl

private theorem targetMultiplicity_split (x y : X.vertex) :
    Z.edgeMultiplicity (e x) (e y) = W.targetKeptMultiplicity x y +
      Z.edgeSetMultiplicity W.targetUnmatched (e x) (e y) := by
  have hdisj : Disjoint W.targetKept W.targetUnmatched := by
    exact Finset.disjoint_sdiff
  have hunion : W.targetKept ∪ W.targetUnmatched = Finset.univ := by
    simp [targetUnmatched]
  rw [← Z.edgeSetMultiplicity_univ, ← hunion,
    Z.edgeSetMultiplicity_union hdisj]
  rfl

/-- Every unmatched occurrence contributes to at most two ordered endpoint
pairs in the multiplicity edit distance. -/
theorem editDistance_le_two_mul_unmatchedCount :
    X.editDistance Z e ≤ 2 * W.unmatchedCount := by
  classical
  unfold FiniteMultiGraph.editDistance
  have hpoint (x y : X.vertex) :
      (X.edgeMultiplicity x y - Z.edgeMultiplicity (e x) (e y)) +
          (Z.edgeMultiplicity (e x) (e y) - X.edgeMultiplicity x y) ≤
        X.edgeSetMultiplicity W.sourceUnmatched x y +
          Z.edgeSetMultiplicity W.targetUnmatched (e x) (e y) := by
    rw [W.sourceMultiplicity_split x y, W.targetMultiplicity_split x y,
      W.keptMultiplicity_eq x y]
    omega
  calc
    _ ≤ ∑ x, ∑ y, (X.edgeSetMultiplicity W.sourceUnmatched x y +
        Z.edgeSetMultiplicity W.targetUnmatched (e x) (e y)) := by
      exact Finset.sum_le_sum fun x _ ↦ Finset.sum_le_sum fun y _ ↦ hpoint x y
    _ = (∑ x, ∑ y, X.edgeSetMultiplicity W.sourceUnmatched x y) +
        ∑ x, ∑ y, Z.edgeSetMultiplicity W.targetUnmatched (e x) (e y) := by
      simp_rw [Finset.sum_add_distrib]
    _ = 2 * W.sourceUnmatched.card + 2 * W.targetUnmatched.card := by
      rw [X.sum_edgeSetMultiplicity]
      have htransport : (∑ x, ∑ y,
          Z.edgeSetMultiplicity W.targetUnmatched (e x) (e y)) =
          ∑ z, ∑ w, Z.edgeSetMultiplicity W.targetUnmatched z w := by
        exact Fintype.sum_equiv e _ _ fun x ↦
          Fintype.sum_equiv e _ _ fun y ↦ rfl
      rw [htransport, Z.sum_edgeSetMultiplicity]
    _ = 2 * W.unmatchedCount := by
      unfold unmatchedCount
      omega

end EdgeEditWitness
end NonsoficGroupsExist
