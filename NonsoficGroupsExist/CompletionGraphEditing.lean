import NonsoficGroupsExist.EdgeWitnessDistance
import NonsoficGroupsExist.Localization

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
    (completed e.1.1.1 e.1.1.2 : Y) = act e.1.1.1 e.1.1.2

private noncomputable def targetKept :
    Finset ((generatorGraph Y T act).induce U).edge :=
  Finset.univ.filter fun e ↦
    (completed e.1.1.1.1 ⟨e.1.1.1.2, e.1.2.1⟩ : Y) =
      act e.1.1.1.1 e.1.1.1.2

private noncomputable def edgeEquiv :
    sourceKept U T act completed ≃ targetKept U T act completed where
  toFun e := by
    let t := e.1.1.1.1
    let x : U := e.1.1.1.2
    have hmove : completed t x ≠ x := (Finset.mem_filter.mp e.1.2).2
    have hagree : (completed t x : Y) = act t x := (Finset.mem_filter.mp e.2).2
    have hambientMove : act t x ≠ x := by
      intro h
      apply hmove
      apply Subtype.ext
      simpa [hagree] using h
    let a : (generatorGraph Y T act).edge :=
      ⟨⟨e.1.1.1.1, x.1⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hambientMove⟩⟩
    have hend : act t x ∈ U := by rw [← hagree]; exact (completed t x).2
    let b : ((generatorGraph Y T act).induce U).edge :=
      ⟨a, x.2, hend⟩
    exact ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hagree⟩⟩
  invFun e := by
    let t := e.1.1.1.1.1
    let x : U := ⟨e.1.1.1.1.2, e.1.1.2.1⟩
    have hagree : (completed t x : Y) = act t x := (Finset.mem_filter.mp e.2).2
    have hmoveAmbient : act t x ≠ x := (Finset.mem_filter.mp e.1.1.2).2
    have hmove : completed t x ≠ x := by
      intro h
      apply hmoveAmbient
      simpa [hagree, congrArg Subtype.val h]
    let a : (generatorGraph
      { carrier := U, fintype := inferInstance, decidableEq := inferInstance }
      T completed).edge :=
      ⟨⟨e.1.1.1.1.1, x⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmove⟩⟩
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
  have hw := (witness U T act completed).editDistance_le_two_mul_unmatchedCount
  have hsource : (witness U T act completed).sourceUnmatched.card ≤
      ∑ t : T, (Finset.univ.filter fun x : U ↦
        (completed t.1 x : Y) ≠ act t.1 x).card := by
    apply Finset.card_le_card_of_injOn (fun e ↦ e.1.1)
    · intro e he
      have hnot : e ∉ sourceKept U T act completed := (Finset.mem_sdiff.mp he).2
      have hbad : (completed e.1.1.1 e.1.1.2 : Y) ≠ act e.1.1.1 e.1.1.2 := by
        simpa [sourceKept] using hnot
      simpa only [Fintype.sum_subtype] using
        Finset.mem_biUnion.mpr ⟨e.1.1.1,
          ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad⟩⟩⟩
    · intro e _ f _ hef
      exact Subtype.ext hef
  have htarget : (witness U T act completed).targetUnmatched.card ≤
      ∑ t : T, (Finset.univ.filter fun x : U ↦
        (completed t.1 x : Y) ≠ act t.1 x).card := by
    apply Finset.card_le_card_of_injOn (fun e ↦ e.1.1.1)
    · intro e he
      have hnot : e ∉ targetKept U T act completed := (Finset.mem_sdiff.mp he).2
      have hbad : (completed e.1.1.1.1.1 ⟨e.1.1.1.1.2, e.1.1.2.1⟩ : Y) ≠
          act e.1.1.1.1 e.1.1.1.1.2 := by
        simpa [targetKept] using hnot
      simpa only [Fintype.sum_subtype] using
        Finset.mem_biUnion.mpr ⟨e.1.1.1.1.1,
          ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad⟩⟩⟩
    · intro e _ f _ hef
      apply Subtype.ext
      exact hef
  have hu : (witness U T act completed).unmatchedCount ≤
      2 * ∑ t : T, (Finset.univ.filter fun x : U ↦
        (completed t.1 x : Y) ≠ act t.1 x).card := by
    unfold EdgeEditWitness.unmatchedCount
    omega
  omega

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
  gcongr with t
  exact Localization.exists_completion_with_bound U (act t.1) |>.choose_spec

end CompletionGraphEditing
end NonsoficGroupsExist
