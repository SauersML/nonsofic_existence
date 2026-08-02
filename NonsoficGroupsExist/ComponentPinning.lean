import NonsoficGroupsExist.NormalizedComponents
import NonsoficGroupsExist.Pinning

/-!
# Pinning on the ambient expander components

This is the direct componentwise application of Lemma `lem:pin`.  The only
remaining estimate needed by the matching argument is therefore an upper bound
for the displayed total edge variation.
-/

namespace NonsoficGroupsExist
namespace ExpanderDecomposition

open scoped BigOperators

variable {G : Type} [Group G] {S : SoficApproximation G} {T : Finset G}

/-- Every edge of the edited graph belongs to the uniquely indexed component
containing its first endpoint. -/
noncomputable def edgeComponentEquiv (D : ExpanderDecomposition S T) (n : ℕ) :
    (Σ B : D.componentIndex n,
      (D.componentGraph n (D.componentRepresentative n B)).edge) ≃
        (D.modelGraph n).edge := by
  let forget : (Σ B : D.componentIndex n,
      (D.componentGraph n (D.componentRepresentative n B)).edge) →
        (D.modelGraph n).edge := fun a ↦ a.2.1
  apply Equiv.ofBijective forget
  constructor
  · rintro ⟨B, a⟩ ⟨C, b⟩ hab
    have habval : a.1 = b.1 := by
      simpa only [forget] using hab
    have hBCval : B.block = C.block := by
      calc
        B.block = (D.blocks n).block ((D.modelGraph n).first a.1) :=
          (((D.blocks n).eq_of_mem _ _ a.2.1).trans
            (D.componentRepresentative_block n B)).symm
        _ = (D.blocks n).block ((D.modelGraph n).first b.1) := by rw [habval]
        _ = C.block := ((D.blocks n).eq_of_mem _ _ b.2.1).trans
          (D.componentRepresentative_block n C)
    have hBC : B = C := Subtype.ext hBCval
    subst C
    have hab' : a = b := Subtype.ext habval
    subst b
    rfl
  · intro e
    let B : D.componentIndex n :=
      ⟨(D.blocks n).block ((D.modelGraph n).first e),
        (D.blocks n).block_mem_blocksFinset ((D.modelGraph n).first e)⟩
    have hfirst : (D.modelGraph n).first e ∈ B.block := (D.blocks n).self_mem _
    have hsecond : (D.modelGraph n).second e ∈ B.block := by
      change (D.modelGraph n).second e ∈
        (D.blocks n).block ((D.modelGraph n).first e)
      rw [D.edge_inside n e]
      exact (D.blocks n).self_mem _
    refine ⟨⟨B, ⟨e, ?_, ?_⟩⟩, rfl⟩
    · simpa only [D.componentRepresentative_block n B] using hfirst
    · simpa only [D.componentRepresentative_block n B] using hsecond

/-- The ambient component graph indexed without repetition. -/
noncomputable abbrev indexedComponentGraph (D : ExpanderDecomposition S T)
    (n : ℕ) (B : D.componentIndex n) : FiniteMultiGraph :=
  ((D.componentGraph n (D.componentRepresentative n B)).transport
      (blockModel (D.blocks n) (D.componentRepresentative n B))
      (D.componentVertexEquiv n (D.componentRepresentative n B))).transport
    (indexedBlockModel (D.blocks n) B)
    (representativeBlockEquiv (D.blocks n) B)

theorem indexedComponentGraph_expands (D : ExpanderDecomposition S T)
    (n : ℕ) (B : D.componentIndex n) :
    (D.indexedComponentGraph n B).HasCheegerLowerBound D.cheeger := by
  exact FiniteMultiGraph.transport_hasCheegerLowerBound
    ((D.componentGraph n (D.componentRepresentative n B)).transport
      (blockModel (D.blocks n) (D.componentRepresentative n B))
      (D.componentVertexEquiv n (D.componentRepresentative n B)))
    (indexedBlockModel (D.blocks n) B)
    (representativeBlockEquiv (D.blocks n) B)
    (D.componentGraph_expands n (D.componentRepresentative n B))

/-- Componentwise co-area pinning of the normalized inner-block sizes. -/
theorem normalized_pinning_mul (D : ExpanderDecomposition S T)
    (P : ∀ n, BlockStructure (S.model n)) (n : ℕ) :
    D.cheeger *
        ∑ B : D.componentIndex n,
          ∑ x : indexedBlockModel (D.blocks n) B,
            |normalizedSize (P n) (D.blocks n) (x : S.model n) - 1 / 2| ≤
      ∑ B : D.componentIndex n,
        (D.indexedComponentGraph n B).edgeVariation
          (fun x ↦ normalizedSize (P n) (D.blocks n) (x : S.model n)) := by
  exact FiniteMultiGraph.median_pinning_mul
    (fun B : D.componentIndex n ↦ D.indexedComponentGraph n B)
    (h := D.cheeger)
    (fun B ↦ FiniteMultiGraph.transport_hasCheegerLowerBound
      ((D.componentGraph n (D.componentRepresentative n B)).transport
        (blockModel (D.blocks n) (D.componentRepresentative n B))
        (D.componentVertexEquiv n (D.componentRepresentative n B)))
      (indexedBlockModel (D.blocks n) B)
      (representativeBlockEquiv (D.blocks n) B)
      (D.componentGraph_expands n (D.componentRepresentative n B)))
    (fun B x ↦ normalizedSize (P n) (D.blocks n) (x : S.model n))
    (fun B ↦ normalizedSize_isMedian_on_block (P n) (D.blocks n) B)

/-- The left side of pinning counts every model vertex exactly once. -/
theorem normalized_pinning_global (D : ExpanderDecomposition S T)
    (P : ∀ n, BlockStructure (S.model n)) (n : ℕ) :
    D.cheeger *
        ∑ y : S.model n,
          |normalizedSize (P n) (D.blocks n) y - 1 / 2| ≤
      ∑ B : D.componentIndex n,
        (D.indexedComponentGraph n B).edgeVariation
          (fun x ↦ normalizedSize (P n) (D.blocks n) (x : S.model n)) := by
  rw [← BlockIndex.sum_sum (D.blocks n)
    (fun y ↦ |normalizedSize (P n) (D.blocks n) y - 1 / 2|)]
  exact D.normalized_pinning_mul P n

/-- Summing edge variation over the indexed induced components recovers the
variation of the whole edited graph. -/
theorem sum_indexedComponent_edgeVariation (D : ExpanderDecomposition S T)
    (f : S.model n → ℝ) :
    (∑ B : D.componentIndex n,
      (D.indexedComponentGraph n B).edgeVariation (fun x ↦ f (x : S.model n))) =
        (D.modelGraph n).edgeVariation f := by
  classical
  change (∑ B : D.componentIndex n,
      ∑ a : (D.componentGraph n (D.componentRepresentative n B)).edge,
        |f ((D.modelGraph n).first a.1) - f ((D.modelGraph n).second a.1)|) =
    ∑ a : (D.modelGraph n).edge,
      |f ((D.modelGraph n).first a) - f ((D.modelGraph n).second a)|
  rw [← Fintype.sum_sigma']
  exact Fintype.sum_equiv (D.edgeComponentEquiv n) _ _ fun _ ↦ rfl

/-- Once the compressor calculation makes the total edge variation negligible,
the normalized component-size deviation is negligible. -/
theorem normalizedDeviation_negligible (D : ExpanderDecomposition S T)
    (P : ∀ n, BlockStructure (S.model n))
    (hvariation : Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      fun n ↦ ∑ B : D.componentIndex n,
        (D.indexedComponentGraph n B).edgeVariation
          (fun x ↦ normalizedSize (P n) (D.blocks n) (x : S.model n))) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      fun n ↦ ∑ y : S.model n,
        |normalizedSize (P n) (D.blocks n) y - 1 / 2| := by
  have hscaled := Negligible.const_mul (1 / D.cheeger) hvariation
  refine Vanishing.squeeze (fun n ↦ div_nonneg (by positivity) (by positivity))
    (fun n ↦ ?_) hscaled
  have hpin := D.normalized_pinning_global P n
  have hle :
      (∑ y : S.model n,
        |normalizedSize (P n) (D.blocks n) y - 1 / 2|) ≤
        (1 / D.cheeger) *
          ∑ B : D.componentIndex n,
            (D.indexedComponentGraph n B).edgeVariation
              (fun x ↦ normalizedSize (P n) (D.blocks n) (x : S.model n)) := by
    calc
      (∑ y : S.model n,
          |normalizedSize (P n) (D.blocks n) y - 1 / 2|) ≤
          (∑ B : D.componentIndex n,
            (D.indexedComponentGraph n B).edgeVariation
              (fun x ↦ normalizedSize (P n) (D.blocks n) (x : S.model n))) /
                D.cheeger := (le_div_iff₀ D.cheeger_pos).2 (by
          simpa [mul_comm] using hpin)
      _ = (1 / D.cheeger) *
          ∑ B : D.componentIndex n,
            (D.indexedComponentGraph n B).edgeVariation
              (fun x ↦ normalizedSize (P n) (D.blocks n) (x : S.model n)) := by
        ring
  apply div_le_div_of_nonneg_right hle
  positivity

/-- Global edge variation is the sole analytic hypothesis needed after the
componentwise median has been chosen. -/
theorem normalizedDeviation_negligible_of_global
    (D : ExpanderDecomposition S T)
    (P : ∀ n, BlockStructure (S.model n))
    (hvariation : Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      fun n ↦ (D.modelGraph n).edgeVariation
        (normalizedSize (P n) (D.blocks n))) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      fun n ↦ ∑ y : S.model n,
        |normalizedSize (P n) (D.blocks n) y - 1 / 2| := by
  apply D.normalizedDeviation_negligible P
  apply Negligible.congr hvariation
  intro n
  exact (D.sum_indexedComponent_edgeVariation
    (normalizedSize (P n) (D.blocks n))).symm

end ExpanderDecomposition
end NonsoficGroupsExist
