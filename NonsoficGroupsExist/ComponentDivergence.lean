import NonsoficGroupsExist.BlockIndex
import NonsoficGroupsExist.BlockWordCrossing
import NonsoficGroupsExist.MatchedComponents
import NonsoficGroupsExist.SoficErrors

/-!
# Bounded components have negligible mass

This is Lemma `lem:diverge` of the manuscript.  If every fixed group element
crosses a block partition on only `o(|Yₙ|)` vertices, then an infinite group
cannot place a positive proportion of a sofic approximation in uniformly
bounded blocks.  For `M`, use `M+1` distinct group elements.  On a block of
size at most `M`, either one of their arcs crosses the block or two images
collide; both error families are negligible.
-/

namespace NonsoficGroupsExist

variable {G : Type} [Group G] [Infinite G]

/-- Vertices lying in blocks of size at most `M`. -/
def smallBlockVertices {Y : FiniteModel} (P : BlockStructure Y) (M : ℕ) :
    Finset Y :=
  Finset.univ.filter fun x ↦ P.size x ≤ M

/-- The cardinality of the bounded-block locus is the sum of the sizes of
the distinct bounded blocks. -/
theorem sum_smallBlock_card {Y : FiniteModel} (P : BlockStructure Y) (M : ℕ) :
    (∑ B : BlockIndex P,
      if (B.block.card : ℝ) ≤ M then (B.block.card : ℝ) else 0) =
      ((smallBlockVertices P M).card : ℝ) := by
  classical
  unfold smallBlockVertices
  rw [← BlockIndex.sum_card_filter P (fun x ↦ P.size x ≤ M)]
  apply Finset.sum_congr rfl
  intro B _
  have hsize (x : indexedBlockModel P B) : P.size x.1 = B.block.card := by
    unfold BlockStructure.size
    exact congrArg Finset.card
      ((P.eq_of_mem (BlockIndex.representative P B) x.1 (by
        simpa only [BlockIndex.block_representative] using x.2)).trans
        (BlockIndex.block_representative P B))
  by_cases hB : (B.block.card : ℝ) ≤ M
  · have hBnat : B.block.card ≤ M := by exact_mod_cast hB
    rw [if_pos hB]
    have hall : Finset.univ.filter (fun x : indexedBlockModel P B ↦
        P.size x.1 ≤ M) = Finset.univ := by
      apply Finset.filter_eq_self.mpr
      intro x _
      simpa only [hsize x] using hBnat
    rw [hall]
    simp only [Finset.card_univ, Fintype.card_coe]
  · have hBnat : ¬ B.block.card ≤ M := by exact_mod_cast hB
    rw [if_neg hB]
    have hempty : Finset.univ.filter (fun x : indexedBlockModel P B ↦
        P.size x.1 ≤ M) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro x _
      simpa only [hsize x] using hBnat
    rw [hempty]
    simp

namespace SoficApproximation

variable (S : SoficApproximation G)
variable (P : ∀ n, BlockStructure (S.model n))

private noncomputable def witness (_S : SoficApproximation G) (i : ℕ) : G :=
  Infinite.natEmbedding G i

private theorem witness_injective : Function.Injective (S.witness : ℕ → G) :=
  (Infinite.natEmbedding G).injective

private noncomputable def crossingUnion (M n : ℕ) : Finset (S.model n) :=
  Finset.univ.biUnion fun i : Fin (M + 1) ↦
    wordCrossing (P n) (S.map n (S.witness i))

private noncomputable def collisionUnion (M n : ℕ) : Finset (S.model n) :=
  Finset.univ.biUnion fun i : Fin (M + 1) ↦
    (Finset.univ.filter fun j : Fin (M + 1) ↦ i ≠ j).biUnion fun j ↦
      S.collisionError n (S.witness i) (S.witness j)

private theorem smallBlockVertices_subset_errors (M n : ℕ) :
    smallBlockVertices (P n) M ⊆ S.crossingUnion P M n ∪ S.collisionUnion M n := by
  classical
  intro x hx
  simp only [smallBlockVertices, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  change ((P n).block x).card ≤ M at hx
  by_cases hc : x ∈ S.crossingUnion P M n
  · exact Finset.mem_union_left _ hc
  by_cases hp : x ∈ S.collisionUnion M n
  · exact Finset.mem_union_right _ hp
  exfalso
  have hstay : ∀ i : Fin (M + 1), S.map n (S.witness i) x ∈ (P n).block x := by
    intro i
    have hnot : x ∉ wordCrossing (P n) (S.map n (S.witness i)) := by
      intro hi
      apply hc
      apply Finset.mem_biUnion.mpr
      exact ⟨i, Finset.mem_univ i, hi⟩
    have heq : (P n).block (S.map n (S.witness i) x) = (P n).block x := by
      simpa [wordCrossing] using hnot
    rw [← heq]
    exact (P n).self_mem _
  have hinj : Function.Injective fun i : Fin (M + 1) ↦ S.map n (S.witness i) x := by
    intro i j hij
    by_cases hij' : i = j
    · exact hij'
    · exfalso
      apply hp
      apply Finset.mem_biUnion.mpr
      refine ⟨i, Finset.mem_univ i, ?_⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hij'⟩, ?_⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hij⟩
  let images : Finset (S.model n) :=
    Finset.univ.image fun i : Fin (M + 1) ↦ S.map n (S.witness i) x
  have himages : images ⊆ (P n).block x := by
    intro y hy
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
    exact hstay i
  have hcardImages : images.card = M + 1 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have := Finset.card_le_card himages
  rw [hcardImages] at this
  omega

private theorem smallBlockVertices_card_le (M n : ℕ) :
    (smallBlockVertices (P n) M).card ≤
      (∑ i : Fin (M + 1),
        (wordCrossing (P n) (S.map n (S.witness i))).card) +
      ∑ i : Fin (M + 1), ∑ j ∈ Finset.univ.filter fun j : Fin (M + 1) ↦ i ≠ j,
        (S.collisionError n (S.witness i) (S.witness j)).card := by
  classical
  have hs := Finset.card_le_card (S.smallBlockVertices_subset_errors P M n)
  have hu := Finset.card_union_le (S.crossingUnion P M n) (S.collisionUnion M n)
  have hc : (S.crossingUnion P M n).card ≤
      ∑ i : Fin (M + 1),
        (wordCrossing (P n) (S.map n (S.witness i))).card := by
    exact Finset.card_biUnion_le
  have hp : (S.collisionUnion M n).card ≤
      ∑ i : Fin (M + 1), ∑ j ∈ Finset.univ.filter fun j : Fin (M + 1) ↦ i ≠ j,
        (S.collisionError n (S.witness i) (S.witness j)).card := by
    refine (Finset.card_biUnion_le).trans (Finset.sum_le_sum fun i _ ↦ ?_)
    exact Finset.card_biUnion_le
  omega

/-- **Lemma `lem:diverge`.**  The total mass in blocks of any fixed bounded
size is negligible. -/
theorem smallBlockVertices_negligible
    (hcross : ∀ g : G, Negligible
      (fun n ↦ (Fintype.card (S.model n) : ℝ))
      fun n ↦ ((wordCrossing (P n) (S.map n g)).card : ℝ))
    (M : ℕ) : Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      fun n ↦ ((smallBlockVertices (P n) M).card : ℝ) := by
  let I := Finset.univ (α := Fin (M + 1))
  have hcrossSum : Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      fun n ↦ ∑ i ∈ I,
        ((wordCrossing (P n) (S.map n (S.witness i))).card : ℝ) :=
    Negligible.sum I _ fun i _ ↦ hcross (S.witness i)
  have hcollision : ∀ i : Fin (M + 1), Negligible
      (fun n ↦ (Fintype.card (S.model n) : ℝ))
      fun n ↦ ∑ j ∈ I.filter fun j ↦ i ≠ j,
        ((S.collisionError n (S.witness i) (S.witness j)).card : ℝ) := by
    intro i
    exact Negligible.sum (I.filter fun j ↦ i ≠ j) _ fun j hj ↦
      S.collisionError_negligible (S.witness i) (S.witness j)
        (S.witness_injective.ne fun hij ↦
          (Finset.mem_filter.mp hj).2 (Fin.ext hij))
  have hcollisionSum : Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      fun n ↦ ∑ i ∈ I, ∑ j ∈ I.filter fun j ↦ i ≠ j,
        ((S.collisionError n (S.witness i) (S.witness j)).card : ℝ) :=
    Negligible.sum I _ fun i _ ↦ hcollision i
  have hsum := Negligible.add hcrossSum hcollisionSum
  refine Vanishing.squeeze (fun n ↦ div_nonneg (by positivity) (by positivity))
    (fun n ↦ ?_) hsum
  have hcard := S.smallBlockVertices_card_le P M n
  have hcast : ((smallBlockVertices (P n) M).card : ℝ) ≤
      (∑ i : Fin (M + 1),
        ((wordCrossing (P n) (S.map n (S.witness i))).card : ℝ)) +
      ∑ i : Fin (M + 1), ∑ j ∈ Finset.univ.filter fun j : Fin (M + 1) ↦ i ≠ j,
        ((S.collisionError n (S.witness i) (S.witness j)).card : ℝ) := by
    exact_mod_cast hcard
  apply div_le_div_of_nonneg_right hcast
  positivity

end SoficApproximation

namespace ExpanderDecomposition

variable {G : Type} [Group G]
variable {S : SoficApproximation G} {T : Finset G}

/-- Equation `eq:gamma-inv` propagated from generators to every fixed group
element. -/
theorem all_almost_invariant (D : ExpanderDecomposition S T)
    (hsymm : ∀ g ∈ T, g⁻¹ ∈ T)
    (hgen : Subgroup.closure (T : Set G) = ⊤) (g : G) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      fun n ↦ ((wordCrossing (D.blocks n) (S.map n g)).card : ℝ) := by
  apply S.all_wordCrossing_negligible D.blocks T hsymm hgen
  intro t ht
  simpa [wordCrossing] using D.almost_invariant t ht

/-- Lemma `lem:diverge` specialized to the component partition supplied by
Kun's decomposition. -/
theorem smallBlockVertices_negligible [Infinite G]
    (D : ExpanderDecomposition S T)
    (hsymm : ∀ g ∈ T, g⁻¹ ∈ T)
    (hgen : Subgroup.closure (T : Set G) = ⊤) (M : ℕ) :
    Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
      fun n ↦ ((smallBlockVertices (D.blocks n) M).card : ℝ) :=
  S.smallBlockVertices_negligible D.blocks (D.all_almost_invariant hsymm hgen) M

end ExpanderDecomposition
end NonsoficGroupsExist
