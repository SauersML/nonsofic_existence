import NonsoficGroupsExist.BlockWordCrossing
import NonsoficGroupsExist.KunBadBlocks

/-!
# Almost invariance after isolating bad Kun blocks

Refining a block-saturated exceptional locus to singletons can create a new
partition crossing only at an exceptional vertex or at its permutation
preimage.  Thus the refinement costs at most twice the exceptional mass.
-/

namespace NonsoficGroupsExist
namespace KunRefinedInvariance

open KunBadBlocks

/-- Every crossing newly created by singletonizing bad blocks is incident,
before or after applying the permutation, to the bad-vertex locus. -/
theorem wordCrossing_singletonizeBadBlocks_subset
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (E : Finset X.vertex) (K : ℕ) (p : Equiv.Perm X.vertex) :
    wordCrossing (singletonizeBadBlocks X P E K) p ⊆
      (wordCrossing P p ∪ badVertices X P E K) ∪
        permutationPreimage p (badVertices X P E K) := by
  classical
  intro y hy
  have hyCross := (mem_wordCrossing
    (singletonizeBadBlocks X P E K) p y).mp hy
  by_cases hyBad : y ∈ badVertices X P E K
  · exact Finset.mem_union_left _
      (Finset.mem_union_right _ hyBad)
  by_cases hpyBad : p y ∈ badVertices X P E K
  · exact Finset.mem_union_right _ (by
      simpa [permutationPreimage] using hpyBad)
  · apply Finset.mem_union_left _
    apply Finset.mem_union_left _
    apply (mem_wordCrossing P p y).mpr
    intro hsame
    apply hyCross
    rw [singletonizeBadBlocks_block_of_good X P E K hpyBad,
      singletonizeBadBlocks_block_of_good X P E K hyBad, hsame]

/-- Singletonizing bad blocks increases the crossing count of any permutation
by at most twice the number of bad vertices. -/
theorem card_wordCrossing_singletonizeBadBlocks_le
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (E : Finset X.vertex) (K : ℕ) (p : Equiv.Perm X.vertex) :
    (wordCrossing (singletonizeBadBlocks X P E K) p).card ≤
      (wordCrossing P p).card + 2 * (badVertices X P E K).card := by
  classical
  have hsubset := Finset.card_le_card
    (wordCrossing_singletonizeBadBlocks_subset X P E K p)
  have houter := Finset.card_union_le
    (wordCrossing P p ∪ badVertices X P E K)
    (permutationPreimage p (badVertices X P E K))
  have hinner := Finset.card_union_le
    (wordCrossing P p) (badVertices X P E K)
  rw [permutationPreimage_card] at houter
  omega

end KunRefinedInvariance
end NonsoficGroupsExist
