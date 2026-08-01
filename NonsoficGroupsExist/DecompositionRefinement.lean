import NonsoficGroupsExist.ComponentRefinement
import NonsoficGroupsExist.BlockIndex

/-!
# Refinement supplied by an expander decomposition

This specializes the finite component-refinement theorem to the edited graph
and block partition carried by `ExpanderDecomposition`.  Every source block now
has a canonically chosen dominant target block for a fixed compressor
permutation.
-/

namespace NonsoficGroupsExist
namespace ExpanderDecomposition

variable {G : Type} [Group G] {S : SoficApproximation G} {T : Finset G}
variable (D : ExpanderDecomposition S T)

/-- The edited graph, transported to the approximation model. -/
noncomputable abbrev modelGraph (n : ℕ) : FiniteMultiGraph :=
  (D.graph n).transport (S.model n) (D.vertexEquiv n)

/-- The edited graph induced on one component block. -/
noncomputable abbrev componentGraph (n : ℕ) (y : S.model n) : FiniteMultiGraph :=
  (D.modelGraph n).induce ((D.blocks n).block y)

/-- Its vertex type is definitionally the source block. -/
noncomputable abbrev componentVertexEquiv (n : ℕ) (y : S.model n) :
    (D.componentGraph n y).vertex ≃ (D.blocks n).block y :=
  Equiv.refl _

theorem componentGraph_expands (n : ℕ) (y : S.model n) :
    ((D.componentGraph n y).transport
      (blockModel (D.blocks n) y) (D.componentVertexEquiv n y)).HasCheegerLowerBound
        D.cheeger := by
  exact FiniteMultiGraph.transport_hasCheegerLowerBound (D.componentGraph n y)
    (blockModel (D.blocks n) y) (D.componentVertexEquiv n y)
      (by simpa [componentGraph, modelGraph] using D.component_expands n y)

/-- Dominant target selected for a source component and a compressor
permutation. -/
noncomputable def refineAt (Q : BlockStructure (S.model n))
    (q : Equiv.Perm (S.model n)) (y : S.model n) :
    ComponentRefinement (D.componentGraph n y) (D.blocks n) Q q y :=
  refineComponent (D.componentGraph n y) (D.blocks n) Q q y
    (D.componentVertexEquiv n y) (D.componentGraph_expands n y)

/-- The one-component leakage bound furnished by the decomposition. -/
theorem refineAt_leakage (Q : BlockStructure (S.model n))
    (q : Equiv.Perm (S.model n)) (y : S.model n) :
    D.cheeger *
        ((((D.blocks n).block y).image q \ (D.refineAt Q q y).target).card : ℝ) ≤
      4 * (((D.componentGraph n y).transport (blockModel (D.blocks n) y)
        (D.componentVertexEquiv n y)).crossingEdges
          (componentTargetLabel (D.blocks n) Q q y)).card :=
  (D.refineAt Q q y).cheeger_mul_leakage_le_crossing

/-! ### Refinement indexed once per distinct source component -/

/-- The distinct source components at index `n`. -/
abbrev componentIndex (n : ℕ) := BlockIndex (D.blocks n)

/-- A representative vertex chosen only to access the vertex-indexed graph
interface.  The associated block is exactly the indexed component. -/
noncomputable def componentRepresentative (n : ℕ) (C : D.componentIndex n) :
    S.model n :=
  BlockIndex.representative (D.blocks n) C

@[simp] theorem componentRepresentative_block (n : ℕ)
    (C : D.componentIndex n) :
    (D.blocks n).block (D.componentRepresentative n C) = C.block :=
  BlockIndex.block_representative (D.blocks n) C

/-- Dominant target for one distinctly indexed source component. -/
noncomputable def refineBlock (Q : BlockStructure (S.model n))
    (q : Equiv.Perm (S.model n)) (C : D.componentIndex n) :=
  D.refineAt Q q (D.componentRepresentative n C)

/-- The leakage estimate, now indexed over each source component exactly once. -/
theorem refineBlock_leakage (Q : BlockStructure (S.model n))
    (q : Equiv.Perm (S.model n)) (C : D.componentIndex n) :
    D.cheeger * ((C.block.image q \ (D.refineBlock Q q C).target).card : ℝ) ≤
      4 * (((D.componentGraph n (D.componentRepresentative n C)).transport
        (blockModel (D.blocks n) (D.componentRepresentative n C))
          (D.componentVertexEquiv n (D.componentRepresentative n C))).crossingEdges
            (componentTargetLabel (D.blocks n) Q q
              (D.componentRepresentative n C))).card := by
  simpa [refineBlock] using D.refineAt_leakage Q q (D.componentRepresentative n C)

/-- Leakage mass of one distinctly indexed source component. -/
noncomputable def componentLeakage (Q : BlockStructure (S.model n))
    (q : Equiv.Perm (S.model n)) (C : D.componentIndex n) : ℕ :=
  (C.block.image q \ (D.refineBlock Q q C).target).card

/-- The target-block label on the whole edited model graph. -/
def transportedTargetLabel (Q : BlockStructure (S.model n))
    (q : Equiv.Perm (S.model n)) (x : S.model n) : Finset (S.model n) :=
  Q.block (q x)

/-- Crossing occurrences in one component, viewed as occurrences of the whole
edited graph. -/
noncomputable def componentCrossingEdges (Q : BlockStructure (S.model n))
    (q : Equiv.Perm (S.model n)) (C : D.componentIndex n) :
    Finset (D.modelGraph n).edge :=
  Finset.univ.filter fun e ↦
    transportedTargetLabel Q q ((D.modelGraph n).first e) ≠
        transportedTargetLabel Q q ((D.modelGraph n).second e) ∧
      (D.modelGraph n).first e ∈ C.block ∧
      (D.modelGraph n).second e ∈ C.block

@[simp] theorem mem_componentCrossingEdges
    (Q : BlockStructure (S.model n)) (q : Equiv.Perm (S.model n))
    (C : D.componentIndex n) (e : (D.modelGraph n).edge) :
    e ∈ D.componentCrossingEdges Q q C ↔
      e ∈ (D.modelGraph n).crossingEdges (transportedTargetLabel Q q) ∧
        (D.modelGraph n).first e ∈ C.block ∧
        (D.modelGraph n).second e ∈ C.block := by
  simp [componentCrossingEdges]

/-- The induced-component crossing count is exactly the count of the
corresponding ambient edge occurrences. -/
theorem component_crossing_card_eq
    (Q : BlockStructure (S.model n)) (q : Equiv.Perm (S.model n))
    (C : D.componentIndex n) :
    (((D.componentGraph n (D.componentRepresentative n C)).transport
      (blockModel (D.blocks n) (D.componentRepresentative n C))
        (D.componentVertexEquiv n (D.componentRepresentative n C))).crossingEdges
          (componentTargetLabel (D.blocks n) Q q
            (D.componentRepresentative n C))).card =
      (D.componentCrossingEdges Q q C).card := by
  classical
  let y := D.componentRepresentative n C
  apply Finset.card_bij (fun a _ ↦ a.1)
  · intro a ha
    rw [D.mem_componentCrossingEdges]
    have hcross := (FiniteMultiGraph.mem_crossingEdges _ _ a).mp ha
    refine ⟨?_, ?_, ?_⟩
    · apply (FiniteMultiGraph.mem_crossingEdges _ _ a.1).mpr
      have hfirstEndpoint :
          ((D.componentVertexEquiv n (D.componentRepresentative n C))
            ((D.componentGraph n (D.componentRepresentative n C)).first a)).1 =
              (D.modelGraph n).first a.1 := rfl
      have hsecondEndpoint :
          ((D.componentVertexEquiv n (D.componentRepresentative n C))
            ((D.componentGraph n (D.componentRepresentative n C)).second a)).1 =
              (D.modelGraph n).second a.1 := rfl
      change Q.block (q ((D.modelGraph n).first a.1)) ≠
        Q.block (q ((D.modelGraph n).second a.1))
      change Q.block (q ((D.componentVertexEquiv n (D.componentRepresentative n C))
          ((D.componentGraph n (D.componentRepresentative n C)).first a)).1) ≠
        Q.block (q ((D.componentVertexEquiv n (D.componentRepresentative n C))
          ((D.componentGraph n (D.componentRepresentative n C)).second a)).1) at hcross
      rwa [hfirstEndpoint, hsecondEndpoint] at hcross
    · rw [← D.componentRepresentative_block n C]
      exact a.2.1
    · rw [← D.componentRepresentative_block n C]
      exact a.2.2
  · intro a _ b _ hab
    exact Subtype.ext hab
  · intro e he
    rw [D.mem_componentCrossingEdges] at he
    have hfirst : (D.modelGraph n).first e ∈ (D.blocks n).block y := by
      dsimp [y]
      rw [D.componentRepresentative_block n C]
      exact he.2.1
    have hsecond : (D.modelGraph n).second e ∈ (D.blocks n).block y := by
      dsimp [y]
      rw [D.componentRepresentative_block n C]
      exact he.2.2
    let a : (D.componentGraph n y).edge := ⟨e, hfirst, hsecond⟩
    refine ⟨a, ?_, rfl⟩
    apply (FiniteMultiGraph.mem_crossingEdges _ _ a).mpr
    have hcross := (FiniteMultiGraph.mem_crossingEdges _ _ e).mp he.1
    have hfirstEndpoint :
        ((D.componentVertexEquiv n (D.componentRepresentative n C))
          ((D.componentGraph n (D.componentRepresentative n C)).first a)).1 =
            (D.modelGraph n).first e := rfl
    have hsecondEndpoint :
        ((D.componentVertexEquiv n (D.componentRepresentative n C))
          ((D.componentGraph n (D.componentRepresentative n C)).second a)).1 =
            (D.modelGraph n).second e := rfl
    change Q.block (q ((D.componentVertexEquiv n (D.componentRepresentative n C))
        ((D.componentGraph n (D.componentRepresentative n C)).first a)).1) ≠
      Q.block (q ((D.componentVertexEquiv n (D.componentRepresentative n C))
        ((D.componentGraph n (D.componentRepresentative n C)).second a)).1)
    change Q.block (q ((D.modelGraph n).first e)) ≠
      Q.block (q ((D.modelGraph n).second e)) at hcross
    rwa [hfirstEndpoint, hsecondEndpoint]

theorem componentCrossingEdges_pairwise
    (Q : BlockStructure (S.model n)) (q : Equiv.Perm (S.model n)) :
    (↑(Finset.univ : Finset (D.componentIndex n)) : Set (D.componentIndex n)).PairwiseDisjoint
      (D.componentCrossingEdges Q q) := by
  intro C _ E _ hCE
  apply Finset.disjoint_left.mpr
  intro e heC heE
  rw [D.mem_componentCrossingEdges] at heC heE
  have hblocks := BlockIndex.pairwise_disjoint (D.blocks n)
    (Finset.mem_univ C) (Finset.mem_univ E) hCE
  exact Finset.disjoint_left.mp hblocks heC.2.1 heE.2.1

/-- The component crossing sets partition all crossing occurrences because
every edited edge stays inside a unique source component. -/
theorem componentCrossingEdges_biUnion
    (Q : BlockStructure (S.model n)) (q : Equiv.Perm (S.model n)) :
    (Finset.univ : Finset (D.componentIndex n)).biUnion
        (D.componentCrossingEdges Q q) =
      (D.modelGraph n).crossingEdges (transportedTargetLabel Q q) := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨C, _, heC⟩ := Finset.mem_biUnion.mp he
    exact (D.mem_componentCrossingEdges Q q C e).mp heC |>.1
  · intro he
    let C : D.componentIndex n :=
      ⟨(D.blocks n).block ((D.modelGraph n).first e),
        (D.blocks n).block_mem_blocksFinset ((D.modelGraph n).first e)⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨C, Finset.mem_univ C, (D.mem_componentCrossingEdges Q q C e).mpr
      ⟨he, ?_, ?_⟩⟩
    · exact (D.blocks n).self_mem _
    · change (D.modelGraph n).second e ∈
        (D.blocks n).block ((D.modelGraph n).first e)
      rw [D.edge_inside n e]
      exact (D.blocks n).self_mem _

/-- Refined crossing count of one distinctly indexed source component. -/
noncomputable def componentCrossingCount (Q : BlockStructure (S.model n))
    (q : Equiv.Perm (S.model n)) (C : D.componentIndex n) : ℕ :=
  (D.componentCrossingEdges Q q C).card

theorem sum_componentCrossingCount
    (Q : BlockStructure (S.model n)) (q : Equiv.Perm (S.model n)) :
    ∑ C : D.componentIndex n, D.componentCrossingCount Q q C =
      ((D.modelGraph n).crossingEdges (transportedTargetLabel Q q)).card := by
  classical
  have hcard := Finset.card_biUnion (s :=
      (Finset.univ : Finset (D.componentIndex n)))
    (t := D.componentCrossingEdges Q q)
      fun C hC E hE hCE ↦ D.componentCrossingEdges_pairwise Q q hC hE hCE
  rw [D.componentCrossingEdges_biUnion Q q] at hcard
  simpa [componentCrossingCount] using hcard.symm

/-- Summing the componentwise refinement inequalities counts every source
component once. -/
theorem cheeger_mul_totalLeakage_le_crossings
    (Q : BlockStructure (S.model n)) (q : Equiv.Perm (S.model n)) :
    D.cheeger * ∑ C : D.componentIndex n, (D.componentLeakage Q q C : ℝ) ≤
      4 * ∑ C : D.componentIndex n, (D.componentCrossingCount Q q C : ℝ) := by
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_le_sum fun C _ ↦ by
    rw [componentLeakage, componentCrossingCount, ← D.component_crossing_card_eq Q q C]
    exact D.refineBlock_leakage Q q C

/-- The summed refinement estimate with its right-hand side reduced to the
single global crossing count. -/
theorem cheeger_mul_totalLeakage_le_globalCrossing
    (Q : BlockStructure (S.model n)) (q : Equiv.Perm (S.model n)) :
    D.cheeger * ∑ C : D.componentIndex n, (D.componentLeakage Q q C : ℝ) ≤
      4 * (((D.modelGraph n).crossingEdges (transportedTargetLabel Q q)).card : ℝ) := by
  have h := D.cheeger_mul_totalLeakage_le_crossings Q q
  have hsum :
      (∑ C : D.componentIndex n, (D.componentCrossingCount Q q C : ℝ)) =
        (((D.modelGraph n).crossingEdges (transportedTargetLabel Q q)).card : ℝ) := by
    exact_mod_cast D.sum_componentCrossingCount Q q
  rwa [hsum] at h

end ExpanderDecomposition
end NonsoficGroupsExist
