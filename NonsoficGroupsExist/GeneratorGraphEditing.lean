import NonsoficGroupsExist.EdgeWitnessDistance

/-!
# Editing generator graphs when actions disagree

Changing the permutation assigned to a generator at one vertex changes at
most one labeled edge occurrence in each graph.  Consequently the
multiplicity edit distance is at most four times the total number of action
disagreements.
-/

namespace NonsoficGroupsExist

open scoped BigOperators

variable {G : Type} [Group G] {Y : FiniteModel}

namespace GeneratorGraphEditing

variable (T : Finset G) (a b : G → Equiv.Perm Y)

private noncomputable def sourceKept :
    Finset (generatorGraph Y T a).edge :=
  Finset.univ.filter fun e ↦ a e.1.1.1 e.1.1.2 = b e.1.1.1 e.1.1.2

private noncomputable def targetKept :
    Finset (generatorGraph Y T b).edge :=
  Finset.univ.filter fun e ↦ a e.1.1.1 e.1.1.2 = b e.1.1.1 e.1.1.2

private noncomputable def edgeEquiv :
    sourceKept T a b ≃ targetKept T a b where
  toFun e := by
    let p := e.1.1
    have hmoveA : a p.1.1 p.2 ≠ p.2 := (Finset.mem_filter.mp e.1.2).2
    have hab : a p.1.1 p.2 = b p.1.1 p.2 := (Finset.mem_filter.mp e.2).2
    have hmoveB : b p.1.1 p.2 ≠ p.2 := by simpa [← hab] using hmoveA
    let eb : (generatorGraph Y T b).edge :=
      ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmoveB⟩⟩
    exact ⟨eb, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩⟩
  invFun e := by
    let p := e.1.1
    have hmoveB : b p.1.1 p.2 ≠ p.2 := (Finset.mem_filter.mp e.1.2).2
    have hab : a p.1.1 p.2 = b p.1.1 p.2 := (Finset.mem_filter.mp e.2).2
    have hmoveA : a p.1.1 p.2 ≠ p.2 := by simpa [hab] using hmoveB
    let ea : (generatorGraph Y T a).edge :=
      ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmoveA⟩⟩
    exact ⟨ea, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩⟩
  left_inv e := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv e := by apply Subtype.ext; apply Subtype.ext; rfl

noncomputable def witness : EdgeEditWitness
    (generatorGraph Y T a) (generatorGraph Y T b) (Equiv.refl Y) where
  sourceKept := sourceKept T a b
  targetKept := targetKept T a b
  edgeEquiv := edgeEquiv T a b
  preservesEndpoints := by
    intro e
    have hab : a e.1.1.1.1 e.1.1.1.2 = b e.1.1.1.1 e.1.1.1.2 :=
      (Finset.mem_filter.mp e.2).2
    exact Or.inl ⟨rfl, hab⟩

theorem sourceUnmatched_card_le :
    (witness T a b).sourceUnmatched.card ≤
      ∑ t : T, (Finset.univ.filter fun x : Y ↦ a t.1 x ≠ b t.1 x).card := by
  apply Finset.card_le_card_of_injOn (fun e ↦ e.1.1)
  · intro e he
    have hnot : e ∉ sourceKept T a b := (Finset.mem_sdiff.mp he).2
    have hab : a e.1.1.1 e.1.1.2 ≠ b e.1.1.1 e.1.1.2 := by
      simpa [sourceKept] using hnot
    rw [Fintype.sum_subtype]
    exact Finset.mem_biUnion.mpr ⟨e.1.1.1,
      ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩⟩⟩
  · intro e _ f _ hef
    exact Subtype.ext hef

theorem targetUnmatched_card_le :
    (witness T a b).targetUnmatched.card ≤
      ∑ t : T, (Finset.univ.filter fun x : Y ↦ a t.1 x ≠ b t.1 x).card := by
  apply Finset.card_le_card_of_injOn (fun e ↦ e.1.1)
  · intro e he
    have hnot : e ∉ targetKept T a b := (Finset.mem_sdiff.mp he).2
    have hab : a e.1.1.1 e.1.1.2 ≠ b e.1.1.1 e.1.1.2 := by
      simpa [targetKept] using hnot
    rw [Fintype.sum_subtype]
    exact Finset.mem_biUnion.mpr ⟨e.1.1.1,
      ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩⟩⟩
  · intro e _ f _ hef
    exact Subtype.ext hef

theorem editDistance_le :
    (generatorGraph Y T a).editDistance (generatorGraph Y T b) (Equiv.refl Y) ≤
      4 * ∑ t : T,
        (Finset.univ.filter fun x : Y ↦ a t.1 x ≠ b t.1 x).card := by
  have hw := (witness T a b).editDistance_le_two_mul_unmatchedCount
  have hu : (witness T a b).unmatchedCount ≤
      2 * ∑ t : T,
        (Finset.univ.filter fun x : Y ↦ a t.1 x ≠ b t.1 x).card := by
    unfold EdgeEditWitness.unmatchedCount
    omega
  omega

end GeneratorGraphEditing
end NonsoficGroupsExist
