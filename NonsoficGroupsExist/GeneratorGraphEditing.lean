import NonsoficGroupsExist.EdgeWitnessDistance
import NonsoficGroupsExist.Criterion

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

section Transport

variable {Z : FiniteModel}

/-- Conjugate every permutation in an action along a finite-model
equivalence. -/
noncomputable def conjugateAction (e : Y ≃ Z) (a : G → Equiv.Perm Y) :
    G → Equiv.Perm Z := fun g ↦ e.symm.trans ((a g).trans e)

/-- Edge occurrences of a transported generator graph correspond label by
label and source by source to those of the conjugated action. -/
noncomputable def transportEdgeEquiv (e : Y ≃ Z) (a : G → Equiv.Perm Y) :
    (generatorGraph Y T a).edge ≃
      (generatorGraph Z T (conjugateAction e a)).edge where
  toFun u := by
    let t := u.1.1
    let x := u.1.2
    refine ⟨⟨t, e x⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    simpa [conjugateAction] using e.injective.ne (Finset.mem_filter.mp u.2).2
  invFun u := by
    let t := u.1.1
    let x := u.1.2
    refine ⟨⟨t, e.symm x⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    intro h
    apply (Finset.mem_filter.mp u.2).2
    have he := congrArg e h
    simpa [conjugateAction] using he
  left_inv u := by
    apply Subtype.ext
    change (u.1.1, e.symm (e u.1.2)) = u.1
    exact Prod.ext rfl (e.symm_apply_apply u.1.2)
  right_inv u := by
    apply Subtype.ext
    change (u.1.1, e (e.symm u.1.2)) = u.1
    exact Prod.ext rfl (e.apply_symm_apply u.1.2)

@[simp] theorem transportEdgeEquiv_first (e : Y ≃ Z) (a : G → Equiv.Perm Y)
    (u : (generatorGraph Y T a).edge) :
    (generatorGraph Z T (conjugateAction e a)).first
        (transportEdgeEquiv T e a u) =
      e ((generatorGraph Y T a).first u) := by
  change e u.1.2 = e u.1.2
  rfl

@[simp] theorem transportEdgeEquiv_second (e : Y ≃ Z) (a : G → Equiv.Perm Y)
    (u : (generatorGraph Y T a).edge) :
    (generatorGraph Z T (conjugateAction e a)).second
        (transportEdgeEquiv T e a u) =
      e ((generatorGraph Y T a).second u) := by
  change e (a u.1.1.1 (e.symm (e u.1.2))) = e (a u.1.1.1 u.1.2)
  rw [e.symm_apply_apply]

theorem transport_edgeMultiplicity (e : Y ≃ Z) (a : G → Equiv.Perm Y)
    (x y : Z) :
    ((generatorGraph Y T a).transport Z e).edgeMultiplicity x y =
      (generatorGraph Z T (conjugateAction e a)).edgeMultiplicity x y := by
  unfold FiniteMultiGraph.edgeMultiplicity
  apply Finset.card_bij (fun u _ ↦ transportEdgeEquiv T e a u)
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    change ((generatorGraph Z T (conjugateAction e a)).first
          (transportEdgeEquiv T e a u) = x ∧
        (generatorGraph Z T (conjugateAction e a)).second
          (transportEdgeEquiv T e a u) = y) ∨
      ((generatorGraph Z T (conjugateAction e a)).first
          (transportEdgeEquiv T e a u) = y ∧
        (generatorGraph Z T (conjugateAction e a)).second
          (transportEdgeEquiv T e a u) = x)
    rw [transportEdgeEquiv_first, transportEdgeEquiv_second]
    exact hu
  · intro u _ v _ huv
    exact (transportEdgeEquiv T e a).injective huv
  · intro v hv
    let u := (transportEdgeEquiv T e a).symm v
    have huv : transportEdgeEquiv T e a u = v :=
      (transportEdgeEquiv T e a).apply_symm_apply v
    refine ⟨u, ?_, huv⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    have hfirst : e ((generatorGraph Y T a).first u) =
        (generatorGraph Z T (conjugateAction e a)).first v := by
      rw [← huv, transportEdgeEquiv_first]
    have hsecond : e ((generatorGraph Y T a).second u) =
        (generatorGraph Z T (conjugateAction e a)).second v := by
      rw [← huv, transportEdgeEquiv_second]
    rw [hfirst, hsecond]
    exact hv

/-- Transporting the graph or conjugating its action gives the same edit
distance to every graph on the transported vertex model. -/
theorem conjugateAction_editDistance (e : Y ≃ Z) (a : G → Equiv.Perm Y)
    (Q : FiniteMultiGraph) (f : Z ≃ Q.vertex) :
    (generatorGraph Z T (conjugateAction e a)).editDistance Q f =
      ((generatorGraph Y T a).transport Z e).editDistance Q f := by
  unfold FiniteMultiGraph.editDistance
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [transport_edgeMultiplicity]

end Transport

private noncomputable def sourceKept :
    Finset (generatorGraph Y T a).edge :=
  Finset.univ.filter fun e ↦ a e.1.1.1 e.1.2 = b e.1.1.1 e.1.2

private noncomputable def targetKept :
    Finset (generatorGraph Y T b).edge :=
  Finset.univ.filter fun e ↦ a e.1.1.1 e.1.2 = b e.1.1.1 e.1.2

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
    have hab : a e.1.1.1.1 e.1.1.2 = b e.1.1.1.1 e.1.1.2 :=
      (Finset.mem_filter.mp e.2).2
    exact Or.inl ⟨rfl, hab⟩

theorem sourceUnmatched_card_le :
    (witness T a b).sourceUnmatched.card ≤
      ∑ t : T, (Finset.univ.filter fun x : Y ↦ a t.1 x ≠ b t.1 x).card := by
  classical
  let bad : Finset (T × Y) := Finset.univ.filter fun p ↦ a p.1.1 p.2 ≠ b p.1.1 p.2
  have hcard : bad.card =
      ∑ t : T, (Finset.univ.filter fun x : Y ↦ a t.1 x ≠ b t.1 x).card := by
    unfold bad
    rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← hcard]
  apply Finset.card_le_card_of_injOn (fun e ↦ e.1)
  · intro e he
    have hab : a e.1.1.1 e.1.2 ≠ b e.1.1.1 e.1.2 := by
      simpa [EdgeEditWitness.sourceUnmatched, witness, sourceKept] using he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩
  · intro e _ f _ hef
    exact Subtype.ext hef

theorem targetUnmatched_card_le :
    (witness T a b).targetUnmatched.card ≤
      ∑ t : T, (Finset.univ.filter fun x : Y ↦ a t.1 x ≠ b t.1 x).card := by
  classical
  let bad : Finset (T × Y) := Finset.univ.filter fun p ↦ a p.1.1 p.2 ≠ b p.1.1 p.2
  have hcard : bad.card =
      ∑ t : T, (Finset.univ.filter fun x : Y ↦ a t.1 x ≠ b t.1 x).card := by
    unfold bad
    rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← hcard]
  apply Finset.card_le_card_of_injOn (fun e ↦ e.1)
  · intro e he
    have hab : a e.1.1.1 e.1.2 ≠ b e.1.1.1 e.1.2 := by
      simpa [EdgeEditWitness.targetUnmatched, witness, targetKept] using he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩
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
    have hs := sourceUnmatched_card_le T a b
    have ht := targetUnmatched_card_le T a b
    unfold EdgeEditWitness.unmatchedCount
    omega
  exact hw.trans (by omega)

end GeneratorGraphEditing
end NonsoficGroupsExist
