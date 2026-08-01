import NonsoficGroupsExist.BlockTransport
import NonsoficGroupsExist.Refinement

/-!
# Refining one expanding component along a permutation

For a source component `C`, label each vertex `x ∈ C` by the target block
containing `q x`.  Lemma `lem:refine` chooses a dominant target.  Working on
the original induced source graph avoids an unnecessary graph coercion; the
image/intersection identities below show that this is exactly the transported
component calculation in the manuscript.
-/

namespace NonsoficGroupsExist

variable {Y : FiniteModel}

/-- The subtype carried by a block, bundled as a finite model for graph
transport. -/
abbrev blockModel (P : BlockStructure Y) (y : Y) : FiniteModel where
  carrier := P.block y
  fintype := inferInstance
  decidableEq := inferInstance

/-- Target-block label on an induced source component. -/
def componentTargetLabel (P Q : BlockStructure Y) (q : Equiv.Perm Y) (y : Y)
    (x : P.block y) : Finset Y :=
  Q.block (q x.1)

theorem componentTargetLabel_cell_nonempty (X : FiniteMultiGraph)
    (P Q : BlockStructure Y) (q : Equiv.Perm Y) (y : Y)
    (e : X.vertex ≃ P.block y) :
    ((X.transport (blockModel P y) e).cell
      (componentTargetLabel P Q q y) {Q.block (q y)}).Nonempty := by
  let x : P.block y := ⟨y, P.self_mem y⟩
  refine ⟨x, ?_⟩
  rw [FiniteMultiGraph.mem_cell]
  change Q.block (q x.1) ∈ ({Q.block (q y)} : Finset (Finset Y))
  simp [x]

/-- Dominant-target output for one expanding component. -/
structure ComponentRefinement (X : FiniteMultiGraph) (P Q : BlockStructure Y)
    (q : Equiv.Perm Y) (y : Y) where
  vertexEquiv : X.vertex ≃ P.block y
  cheeger : ℝ
  expands : (X.transport (blockModel P y) vertexEquiv).HasCheegerLowerBound cheeger
  target : Finset Y
  target_isBlock : ∃ z, target = Q.block z
  maximal : ∀ D : Finset Y,
    ((X.transport (blockModel P y) vertexEquiv).cell
      (componentTargetLabel P Q q y) {D}).card ≤
    ((X.transport (blockModel P y) vertexEquiv).cell
      (componentTargetLabel P Q q y) {target}).card
  leakage_bound :
    cheeger * (((P.block y).card : ℝ) -
      ((X.transport (blockModel P y) vertexEquiv).cell
        (componentTargetLabel P Q q y) {target}).card) ≤
      4 * ((X.transport (blockModel P y) vertexEquiv).crossingEdges
        (componentTargetLabel P Q q y)).card

/-- Lemma `lem:refine` applied to one nonempty source component. -/
noncomputable def refineComponent (X : FiniteMultiGraph)
    (P Q : BlockStructure Y) (q : Equiv.Perm Y) (y : Y)
    (e : X.vertex ≃ P.block y) {h : ℝ}
    (hexp : (X.transport (blockModel P y) e).HasCheegerLowerBound h) :
    ComponentRefinement X P Q q y := by
  classical
  let Z := X.transport (blockModel P y) e
  have hV : 0 < Fintype.card Z.vertex := by
    change 0 < Fintype.card (P.block y)
    exact Fintype.card_pos_iff.mpr ⟨⟨y, P.self_mem y⟩⟩
  let result := Z.exists_dominant_cell hexp
    (componentTargetLabel P Q q y) hV
  let D := Classical.choose result
  have hspec := Classical.choose_spec result
  have hmax := hspec.1
  have hbound := hspec.2
  have hcell : (Z.cell (componentTargetLabel P Q q y) {D}).Nonempty := by
    have hbase := componentTargetLabel_cell_nonempty X P Q q y e
    have hle := hmax (Q.block (q y))
    exact Finset.card_pos.mp ((Finset.card_pos.mpr hbase).trans_le hle)
  let x := Classical.choose hcell
  have hx := Classical.choose_spec hcell
  have hD : D = Q.block (q x.1) := by
    have hx' : Q.block (q x.1) = D := by
      simpa [componentTargetLabel] using
        (FiniteMultiGraph.mem_cell _ _ _ _ |>.mp hx)
    exact hx'.symm
  exact
    { vertexEquiv := e
      cheeger := h
      expands := hexp
      target := D
      target_isBlock := ⟨q x.1, hD⟩
      maximal := hmax
      leakage_bound := by
        simpa [Z, D, Fintype.card_congr e] using hbound }

namespace ComponentRefinement

variable {X : FiniteMultiGraph} {P Q : BlockStructure Y}
  {q : Equiv.Perm Y} {y : Y}

/-- The dominant cell counts precisely the points of the compressed component
that land in the chosen target. -/
theorem cell_card_eq_image_inter (R : ComponentRefinement X P Q q y) :
    ((X.transport (blockModel P y) R.vertexEquiv).cell
      (componentTargetLabel P Q q y) {R.target}).card =
      ((P.block y).image q ∩ R.target).card := by
  classical
  let f : (X.transport (blockModel P y) R.vertexEquiv).vertex → Y :=
    fun x ↦ q x.1
  apply Finset.card_bij (fun x _ ↦ f x)
  · intro x hx
    have hx' : componentTargetLabel P Q q y x = R.target := by
      simpa using (FiniteMultiGraph.mem_cell _ _ _ _ |>.mp hx)
    apply Finset.mem_inter.mpr
    refine ⟨Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩, ?_⟩
    rw [← hx']
    exact Q.self_mem _
  · intro x₁ _ x₂ _ heq
    apply Subtype.ext
    exact q.injective heq
  · intro z hz
    obtain ⟨hzimage, hztarget⟩ := Finset.mem_inter.mp hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hzimage
    let a' : P.block y := ⟨a, ha⟩
    refine ⟨a', ?_, by simp [f, a']⟩
    rw [FiniteMultiGraph.mem_cell, Finset.mem_singleton]
    obtain ⟨t, ht⟩ := R.target_isBlock
    rw [ht] at hztarget ⊢
    exact Q.eq_of_mem t (q a) hztarget

/-- Exact leakage cardinality in image coordinates. -/
theorem image_sdiff_target_card (R : ComponentRefinement X P Q q y) :
    ((P.block y).image q \ R.target).card =
      (P.block y).card -
        ((X.transport (blockModel P y) R.vertexEquiv).cell
          (componentTargetLabel P Q q y) {R.target}).card := by
  rw [Finset.card_sdiff, R.cell_card_eq_image_inter,
    Finset.card_image_of_injective _ q.injective]
  congr 1
  rw [Finset.inter_comm]

end ComponentRefinement
end NonsoficGroupsExist
