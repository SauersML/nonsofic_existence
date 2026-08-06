import NonsoficGroupsExist.Matching.EdgeWitnessDistance
import NonsoficGroupsExist.Matching.Localization
import NonsoficGroupsExist.Criterion.Criterion

/-!
# Generator graphs after completing restricted permutations

Completing the restriction of an ambient permutation to a finite subset only
changes labeled edge occurrences at vertices where the completion disagrees
with the ambient action.  This gives a uniform edit bound between the completed
generator graph and the induced ambient generator graph.
-/

namespace NonsoficGroupsExist

open scoped BigOperators

namespace CompletionGraphEditing

variable {G : Type} [Group G] {Y : FiniteModel}
variable (U : Finset Y) (T : Finset G)
variable (act : G → Equiv.Perm Y) (completed : G → Equiv.Perm U)

private noncomputable def sourceKept :
    Finset (generatorGraph
      { carrier := U, fintype := inferInstance, decidableEq := inferInstance }
      T completed).edge :=
  Finset.univ.filter fun e ↦
    (completed e.1.1.1 e.1.2 : Y) = act e.1.1.1 e.1.2

private noncomputable def targetKept :
    Finset ((generatorGraph Y T act).induce U).edge :=
  Finset.univ.filter fun e ↦
    (completed e.1.1.1.1 ⟨e.1.1.2, e.2.1⟩ : Y) =
      act e.1.1.1.1 e.1.1.2

private noncomputable def edgeEquiv :
    sourceKept U T act completed ≃ targetKept U T act completed where
  toFun e := by
    let t := e.1.1.1.1
    let x : U := e.1.1.2
    have hmove : completed t x ≠ x := (Finset.mem_filter.mp e.1.2).2
    have hagree : (completed t x : Y) = act t x := (Finset.mem_filter.mp e.2).2
    have hambientMove : act t x ≠ x := by
      intro h
      apply hmove
      apply Subtype.ext
      simpa [hagree] using h
    let a : (generatorGraph Y T act).edge :=
      ⟨⟨e.1.1.1, x.1⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hambientMove⟩⟩
    have hend : act t x ∈ U := by rw [← hagree]; exact (completed t x).2
    let b : ((generatorGraph Y T act).induce U).edge :=
      ⟨a, x.2, hend⟩
    exact ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hagree⟩⟩
  invFun e := by
    let t := e.1.1.1.1.1
    let x : U := ⟨e.1.1.1.2, e.1.2.1⟩
    have hagree : (completed t x : Y) = act t x := (Finset.mem_filter.mp e.2).2
    have hmoveAmbient : act t x ≠ x := (Finset.mem_filter.mp e.1.1.2).2
    have hmove : completed t x ≠ x := by
      intro h
      apply hmoveAmbient
      calc
        act t x = (completed t x : Y) := hagree.symm
        _ = x := congrArg Subtype.val h
    let a : (generatorGraph
      { carrier := U, fintype := inferInstance, decidableEq := inferInstance }
      T completed).edge :=
      ⟨⟨e.1.1.1.1, x⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmove⟩⟩
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hagree⟩⟩
  left_inv e := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv e := by apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; rfl

noncomputable def witness : EdgeEditWitness
    (generatorGraph
      { carrier := U, fintype := inferInstance, decidableEq := inferInstance }
      T completed) ((generatorGraph Y T act).induce U) (Equiv.refl U) where
  sourceKept := sourceKept U T act completed
  targetKept := targetKept U T act completed
  edgeEquiv := edgeEquiv U T act completed
  preservesEndpoints := by
    intro e
    have hagree := (Finset.mem_filter.mp e.2).2
    exact Or.inl ⟨rfl, Subtype.ext hagree⟩

theorem editDistance_le :
    (generatorGraph
      { carrier := U, fintype := inferInstance, decidableEq := inferInstance }
      T completed).editDistance ((generatorGraph Y T act).induce U) (Equiv.refl U) ≤
      4 * ∑ t : T, (Finset.univ.filter fun x : U ↦
        (completed t.1 x : Y) ≠ act t.1 x).card := by
  classical
  have hw := (witness U T act completed).editDistance_le_two_mul_unmatchedCount
  have hsource : (witness U T act completed).sourceUnmatched.card ≤
      ∑ t : T, (Finset.univ.filter fun x : U ↦
        (completed t.1 x : Y) ≠ act t.1 x).card := by
    let bad : Finset (T × U) := Finset.univ.filter fun p ↦
      (completed p.1.1 p.2 : Y) ≠ act p.1.1 p.2
    have hcard : bad.card = ∑ t : T, (Finset.univ.filter fun x : U ↦
        (completed t.1 x : Y) ≠ act t.1 x).card := by
      unfold bad
      rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro t _
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [← hcard]
    apply Finset.card_le_card_of_injOn (fun e ↦ e.1)
    · intro e he
      have hbad : (completed e.1.1.1 e.1.2 : Y) ≠ act e.1.1.1 e.1.2 := by
        simpa [EdgeEditWitness.sourceUnmatched, witness, sourceKept] using he
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad⟩
    · intro e _ f _ hef
      exact Subtype.ext hef
  have htarget : (witness U T act completed).targetUnmatched.card ≤
      ∑ t : T, (Finset.univ.filter fun x : U ↦
        (completed t.1 x : Y) ≠ act t.1 x).card := by
    let bad : Finset (T × U) := Finset.univ.filter fun p ↦
      (completed p.1.1 p.2 : Y) ≠ act p.1.1 p.2
    have hcard : bad.card = ∑ t : T, (Finset.univ.filter fun x : U ↦
        (completed t.1 x : Y) ≠ act t.1 x).card := by
      unfold bad
      rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro t _
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [← hcard]
    apply Finset.card_le_card_of_injOn (fun e ↦
      (e.1.1.1, ⟨e.1.1.2, e.2.1⟩))
    · intro e he
      have hbad : (completed e.1.1.1.1 ⟨e.1.1.2, e.2.1⟩ : Y) ≠
          act e.1.1.1.1 e.1.1.2 := by
        simpa [EdgeEditWitness.targetUnmatched, witness, targetKept] using he
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad⟩
    · intro e _ f _ hef
      apply Subtype.ext
      apply Subtype.ext
      have ht : e.1.1.1 = f.1.1.1 :=
        congrArg (fun p : T × U ↦ p.1) hef
      have hx : e.1.1.2 = f.1.1.2 :=
        congrArg (fun p : T × U ↦ (p.2 : Y)) hef
      exact Prod.ext ht hx
  have hu : (witness U T act completed).unmatchedCount ≤
      2 * ∑ t : T, (Finset.univ.filter fun x : U ↦
        (completed t.1 x : Y) ≠ act t.1 x).card := by
    unfold EdgeEditWitness.unmatchedCount
    omega
  exact hw.trans (by omega)

/-- Applying the canonical completion supplied by `Localization` costs at most
four times the number of arcs leaving the subset. -/
theorem canonicalCompletion_editDistance_le :
    let c : G → Equiv.Perm U := fun g ↦
      Classical.choose (Localization.exists_completion_with_bound U (act g))
    (generatorGraph
      { carrier := U, fintype := inferInstance, decidableEq := inferInstance }
      T c).editDistance ((generatorGraph Y T act).induce U) (Equiv.refl U) ≤
      4 * ∑ t : T, (Finset.univ.filter fun x : U ↦ act t.1 x ∉ U).card := by
  dsimp only
  refine (editDistance_le U T act _).trans ?_
  apply Nat.mul_le_mul_left
  apply Finset.sum_le_sum
  intro t _
  exact Localization.exists_completion_with_bound U (act t.1) |>.choose_spec

/-- An internal ambient generator occurrence becomes the identical labeled
occurrence in any completion that agrees on all internal values. -/
noncomputable def internalEdgeToCompleted
    (hagree : ∀ (t : T) (x : U), act t.1 (x : Y) ∈ U →
      (completed t.1 x : Y) = act t.1 x)
    (e : ((generatorGraph Y T act).induce U).edge) :
    (generatorGraph
      { carrier := U, fintype := inferInstance, decidableEq := inferInstance }
      T completed).edge := by
  let t : T := e.1.1.1
  let x : U := ⟨e.1.1.2, e.2.1⟩
  have ha := hagree t x e.2.2
  have hmove : completed t.1 x ≠ x := by
    intro hfix
    exact (generatorGraph Y T act).loopless e.1
      (by
        change (x : Y) = act t.1 x
        calc
          (x : Y) = (completed t.1 x : Y) := congrArg Subtype.val hfix.symm
          _ = act t.1 x := ha)
  exact ⟨(t, x), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmove⟩⟩

theorem internalEdgeToCompleted_injective
    (hagree : ∀ (t : T) (x : U), act t.1 (x : Y) ∈ U →
      (completed t.1 x : Y) = act t.1 x) :
    Function.Injective (internalEdgeToCompleted U T act completed hagree) := by
  intro e f hef
  have harc :
      (internalEdgeToCompleted U T act completed hagree e).1 =
        (internalEdgeToCompleted U T act completed hagree f).1 :=
    congrArg Subtype.val hef
  change (e.1.1.1, (⟨e.1.1.2, e.2.1⟩ : U)) =
    (f.1.1.1, (⟨f.1.1.2, f.2.1⟩ : U)) at harc
  have ht : e.1.1.1 = f.1.1.1 :=
    congrArg (fun p : T × U ↦ p.1) harc
  have hxsub :
      (⟨e.1.1.2, e.2.1⟩ : U) = ⟨f.1.1.2, f.2.1⟩ :=
    congrArg (fun p : T × U ↦ p.2) harc
  have hx : e.1.1.2 = f.1.1.2 := congrArg Subtype.val hxsub
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext ht hx

/-- Every boundary occurrence of the induced ambient generator graph remains
a boundary occurrence after an exact internal completion. -/
theorem induce_boundaryCard_le_completed
    (hagree : ∀ (t : T) (x : U), act t.1 (x : Y) ∈ U →
      (completed t.1 x : Y) = act t.1 x)
    (V : Finset U) :
    ((generatorGraph Y T act).induce U).boundaryCard V ≤
      (generatorGraph
        { carrier := U, fintype := inferInstance, decidableEq := inferInstance }
        T completed).boundaryCard V := by
  classical
  unfold FiniteMultiGraph.boundaryCard
  apply Finset.card_le_card_of_injOn
    (s := ((generatorGraph Y T act).induce U).boundary V)
    (t := (generatorGraph
      { carrier := U, fintype := inferInstance, decidableEq := inferInstance }
      T completed).boundary V)
    (internalEdgeToCompleted U T act completed hagree)
  · intro e he
    have hecut := (Finset.mem_filter.mp he).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hsecond :
        (generatorGraph
          { carrier := U, fintype := inferInstance, decidableEq := inferInstance }
          T completed).second
            (internalEdgeToCompleted U T act completed hagree e) =
          ((generatorGraph Y T act).induce U).second e := by
      apply Subtype.ext
      exact hagree e.1.1.1 ⟨e.1.1.2, e.2.1⟩ e.2.2
    have hfirst :
        (generatorGraph
          { carrier := U, fintype := inferInstance, decidableEq := inferInstance }
          T completed).first
            (internalEdgeToCompleted U T act completed hagree e) =
          ((generatorGraph Y T act).induce U).first e := rfl
    change
      ((generatorGraph
        { carrier := U, fintype := inferInstance, decidableEq := inferInstance }
        T completed).first
          (internalEdgeToCompleted U T act completed hagree e) ∈ V ∧
        (generatorGraph
          { carrier := U, fintype := inferInstance, decidableEq := inferInstance }
          T completed).second
            (internalEdgeToCompleted U T act completed hagree e) ∉ V) ∨
      ((generatorGraph
        { carrier := U, fintype := inferInstance, decidableEq := inferInstance }
        T completed).second
          (internalEdgeToCompleted U T act completed hagree e) ∈ V ∧
        (generatorGraph
          { carrier := U, fintype := inferInstance, decidableEq := inferInstance }
          T completed).first
            (internalEdgeToCompleted U T act completed hagree e) ∉ V)
    rw [hfirst, hsecond]
    exact hecut
  · intro e _ f _ hef
    exact internalEdgeToCompleted_injective U T act completed hagree hef

end CompletionGraphEditing
end NonsoficGroupsExist
