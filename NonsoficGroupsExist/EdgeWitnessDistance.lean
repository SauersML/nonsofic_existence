import NonsoficGroupsExist.EdgeEditing

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
  unfold edgeSetMultiplicity
  simp_rw [Finset.card_eq_sum_ones]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset X.vertex))]
  rw [← Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e he
  have hne := X.loopless e
  simp [hne, ne_comm]

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
      omega
    _ = (∑ x, ∑ y,
        ((X.edgeMultiplicity x y - Z.edgeMultiplicity (e x) (e y)) +
          (Z.edgeMultiplicity (e x) (e y) - X.edgeMultiplicity x y))) +
        ∑ x, ∑ y,
        ((Z.edgeMultiplicity (e x) (e y) -
          W.edgeMultiplicity (f (e x)) (f (e y))) +
          (W.edgeMultiplicity (f (e x)) (f (e y)) -
            Z.edgeMultiplicity (e x) (e y))) := by
      simp_rw [Finset.sum_add_distrib]
      ring
    _ = X.editDistance Z e + Z.editDistance W f := by
      congr 1
      unfold editDistance
      rw [Fintype.sum_equiv e _ _ (fun _ ↦ rfl)]
      apply Finset.sum_congr rfl
      intro z _
      rw [Fintype.sum_equiv e _ _ (fun _ ↦ rfl)]

theorem editDistance_transport_right (X Z : FiniteMultiGraph)
    (e : X.vertex ≃ Z.vertex) :
    X.editDistance (Z.transport X.vertex e.symm) (Equiv.refl X.vertex) =
      X.editDistance Z e := by
  rfl

theorem editDistance_transport_both (X Z : FiniteMultiGraph)
    (W : FiniteModel) (e : X.vertex ≃ Z.vertex) (f : X.vertex ≃ W) :
    (X.transport W f).editDistance (Z.transport W (e.symm.trans f))
      (Equiv.refl W) = X.editDistance Z e := by
  unfold editDistance edgeMultiplicity
  change (∑ w : W, ∑ w' : W,
    (((Finset.univ.filter fun a : X.edge ↦
      (f (X.first a) = w ∧ f (X.second a) = w') ∨
      (f (X.first a) = w' ∧ f (X.second a) = w)).card -
    (Finset.univ.filter fun b : Z.edge ↦
      (f (e.symm (Z.first b)) = w ∧ f (e.symm (Z.second b)) = w') ∨
      (f (e.symm (Z.first b)) = w' ∧ f (e.symm (Z.second b)) = w)).card) +
    ((Finset.univ.filter fun b : Z.edge ↦
      (f (e.symm (Z.first b)) = w ∧ f (e.symm (Z.second b)) = w') ∨
      (f (e.symm (Z.first b)) = w' ∧ f (e.symm (Z.second b)) = w)).card -
    (Finset.univ.filter fun a : X.edge ↦
      (f (X.first a) = w ∧ f (X.second a) = w') ∨
      (f (X.first a) = w' ∧ f (X.second a) = w)).card))) = _
  rw [← Fintype.sum_equiv f]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Fintype.sum_equiv f]
  apply Finset.sum_congr rfl
  intro y _
  congr 2 <;> apply Finset.card_congr <;> ext a <;> simp

end FiniteMultiGraph

namespace EdgeEditWitness

variable {X Z : FiniteMultiGraph} {e : X.vertex ≃ Z.vertex}
variable (W : EdgeEditWitness X Z e)

private def sourceKeptMultiplicity (x y : X.vertex) : ℕ :=
  (Finset.univ.filter fun a : W.sourceKept ↦
    (X.first a.1 = x ∧ X.second a.1 = y) ∨
      (X.first a.1 = y ∧ X.second a.1 = x)).card

private def targetKeptMultiplicity (x y : X.vertex) : ℕ :=
  (Finset.univ.filter fun b : W.targetKept ↦
    (Z.first b.1 = e x ∧ Z.second b.1 = e y) ∨
      (Z.first b.1 = e y ∧ Z.second b.1 = e x)).card

private theorem keptMultiplicity_eq (x y : X.vertex) :
    W.sourceKeptMultiplicity x y = W.targetKeptMultiplicity x y := by
  classical
  apply Finset.card_bij
    (s := Finset.univ.filter fun a : W.sourceKept ↦
      (X.first a.1 = x ∧ X.second a.1 = y) ∨
        (X.first a.1 = y ∧ X.second a.1 = x))
    (t := Finset.univ.filter fun b : W.targetKept ↦
      (Z.first b.1 = e x ∧ Z.second b.1 = e y) ∨
        (Z.first b.1 = e y ∧ Z.second b.1 = e x))
    W.edgeEquiv
  · intro a ha
    rw [Finset.mem_filter] at ha ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases ha.2 with hxy | hyx <;> rcases W.preservesEndpoints a with hp | hp
    · exact Or.inl ⟨hp.1.symm.trans (congrArg e hxy.1),
          hp.2.symm.trans (congrArg e hxy.2)⟩
    · exact Or.inr ⟨hp.1.symm.trans (congrArg e hxy.2),
          hp.2.symm.trans (congrArg e hxy.1)⟩
    · exact Or.inr ⟨hp.1.symm.trans (congrArg e hyx.1),
          hp.2.symm.trans (congrArg e hyx.2)⟩
    · exact Or.inl ⟨hp.1.symm.trans (congrArg e hyx.2),
          hp.2.symm.trans (congrArg e hyx.1)⟩
  · intro a _ b _ hab
    exact W.edgeEquiv.injective hab
  · intro b hb
    let a := W.edgeEquiv.symm b
    refine ⟨a, ?_, W.edgeEquiv.apply_symm_apply b⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hb' := (Finset.mem_filter.mp hb).2
    have hp := W.preservesEndpoints a
    have heq : W.edgeEquiv a = b := W.edgeEquiv.apply_symm_apply b
    rcases hb' with hxy | hyx <;> rcases hp with hp | hp
    all_goals
      simp only [heq] at hp
      first
      | exact Or.inl ⟨e.injective (hp.1.trans hxy.1), e.injective (hp.2.trans hxy.2)⟩
      | exact Or.inr ⟨e.injective (hp.1.trans hxy.2), e.injective (hp.2.trans hxy.1)⟩

private theorem sourceMultiplicity_split (x y : X.vertex) :
    X.edgeMultiplicity x y = W.sourceKeptMultiplicity x y +
      X.edgeSetMultiplicity W.sourceUnmatched x y := by
  have hdisj : Disjoint W.sourceKept W.sourceUnmatched := by
    exact Finset.disjoint_sdiff_right
  have hunion : W.sourceKept ∪ W.sourceUnmatched = Finset.univ := by
    simp [sourceUnmatched]
  rw [← X.edgeSetMultiplicity_univ, ← hunion,
    X.edgeSetMultiplicity_union hdisj]
  congr 1
  unfold sourceKeptMultiplicity FiniteMultiGraph.edgeSetMultiplicity
  simpa using Finset.card_attach

private theorem targetMultiplicity_split (x y : X.vertex) :
    Z.edgeMultiplicity (e x) (e y) = W.targetKeptMultiplicity x y +
      Z.edgeSetMultiplicity W.targetUnmatched (e x) (e y) := by
  have hdisj : Disjoint W.targetKept W.targetUnmatched := by
    exact Finset.disjoint_sdiff_right
  have hunion : W.targetKept ∪ W.targetUnmatched = Finset.univ := by
    simp [targetUnmatched]
  rw [← Z.edgeSetMultiplicity_univ, ← hunion,
    Z.edgeSetMultiplicity_union hdisj]
  congr 1
  unfold targetKeptMultiplicity FiniteMultiGraph.edgeSetMultiplicity
  simpa using Finset.card_attach

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
      ring
    _ = 2 * W.sourceUnmatched.card + 2 * W.targetUnmatched.card := by
      rw [X.sum_edgeSetMultiplicity]
      have htransport : (∑ x, ∑ y,
          Z.edgeSetMultiplicity W.targetUnmatched (e x) (e y)) =
          ∑ z, ∑ w, Z.edgeSetMultiplicity W.targetUnmatched z w := by
        rw [e.sum_comp]
        apply Finset.sum_congr rfl
        intro z _
        rw [e.sum_comp]
      rw [htransport, Z.sum_edgeSetMultiplicity]
    _ = 2 * W.unmatchedCount := by
      unfold unmatchedCount
      omega

end EdgeEditWitness
end NonsoficGroupsExist
