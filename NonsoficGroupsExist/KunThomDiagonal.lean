import NonsoficGroupsExist.KazhdanImprovement
import NonsoficGroupsExist.BlockWordCrossing
import NonsoficGroupsExist.KazhdanFiniteModel

/-!
# Localized errors for the Kun--Thom diagonal action

The graph of a permutation has only `|Y|` points inside `Y × Y`.  Therefore
the diagonal-action error must be charged on that graph, rather than against
all `|Y|^2` pairs.  This module proves the required localized operator bound:
replacing a permutation by another one on the diagonal action changes a
permutation-graph indicator by squared norm at most four times their ordinary
disagreement count on `Y`.
-/

namespace NonsoficGroupsExist
namespace KunThomDiagonal

open KazhdanFiniteModel
open KazhdanImprovement
open scoped symmDiff

section Generic

variable {Y : Type*} [DecidableEq Y]

/-- Points of `U` on which two permutations disagree. -/
def restrictedPermutationDisagreement (U : Finset Y)
    (p q : Equiv.Perm Y) : Finset Y :=
  U.filter fun y ↦ p y ≠ q y

@[simp] theorem mem_restrictedPermutationDisagreement
    (U : Finset Y) (p q : Equiv.Perm Y) (y : Y) :
    y ∈ restrictedPermutationDisagreement U p q ↔
      y ∈ U ∧ p y ≠ q y := by
  simp [restrictedPermutationDisagreement]

/-- Images of `U` can differ only through points of `U` where the two maps
differ; global permutation errors outside `U` are irrelevant. -/
theorem symmDiff_image_subset_restrictedDisagreement_images
    (U : Finset Y) (p q : Equiv.Perm Y) :
    (U.map p.toEmbedding) ∆ (U.map q.toEmbedding) ⊆
      (restrictedPermutationDisagreement U p q).map p.toEmbedding ∪
        (restrictedPermutationDisagreement U p q).map q.toEmbedding := by
  intro y hy
  rw [Finset.mem_symmDiff] at hy
  rcases hy with ⟨hp, hnq⟩ | ⟨hq, hnp⟩
  · rw [Finset.mem_map] at hp
    obtain ⟨x, hx, rfl⟩ := hp
    apply Finset.mem_union_left
    rw [Finset.mem_map]
    refine ⟨x, (mem_restrictedPermutationDisagreement U p q x).2
      ⟨hx, ?_⟩, rfl⟩
    intro heq
    exact hnq (Finset.mem_map.mpr ⟨x, hx, heq.symm⟩)
  · rw [Finset.mem_map] at hq
    obtain ⟨x, hx, rfl⟩ := hq
    apply Finset.mem_union_right
    rw [Finset.mem_map]
    refine ⟨x, (mem_restrictedPermutationDisagreement U p q x).2
      ⟨hx, ?_⟩, rfl⟩
    intro heq
    exact hnp (Finset.mem_map.mpr ⟨x, hx, heq⟩)

theorem card_symmDiff_images_le_two_mul_restrictedDisagreement
    (U : Finset Y) (p q : Equiv.Perm Y) :
    ((U.map p.toEmbedding) ∆ (U.map q.toEmbedding)).card ≤
      2 * (restrictedPermutationDisagreement U p q).card := by
  calc
    ((U.map p.toEmbedding) ∆ (U.map q.toEmbedding)).card ≤
        ((restrictedPermutationDisagreement U p q).map p.toEmbedding ∪
          (restrictedPermutationDisagreement U p q).map q.toEmbedding).card :=
      Finset.card_le_card
        (symmDiff_image_subset_restrictedDisagreement_images U p q)
    _ ≤ ((restrictedPermutationDisagreement U p q).map p.toEmbedding).card +
        ((restrictedPermutationDisagreement U p q).map q.toEmbedding).card :=
      Finset.card_union_le _ _
    _ = 2 * (restrictedPermutationDisagreement U p q).card := by
      simp only [Finset.card_map]
      omega

/-- Localized replacement error for centered characteristic vectors. -/
theorem norm_permutationOperators_centeredIndicator_sub_sq_le_restricted
    [Fintype Y]
    (U : Finset Y) (p q : Equiv.Perm Y) :
    ‖permutationOperator p (centeredIndicator U) -
        permutationOperator q (centeredIndicator U)‖ ^ 2 ≤
      2 * (restrictedPermutationDisagreement U p q).card := by
  rw [permutationOperators_centeredIndicator_sub,
    permutationOperator_indicator, permutationOperator_indicator,
    norm_indicator_sub_sq]
  exact_mod_cast
    card_symmDiff_images_le_two_mul_restrictedDisagreement U p q

end Generic

section Diagonal

variable {Y : Type*}

/-- The diagonal action of one permutation on ordered pairs. -/
def diagonalPerm (p : Equiv.Perm Y) : Equiv.Perm (Y × Y) :=
  p.prodCongr p

@[simp] theorem diagonalPerm_apply (p : Equiv.Perm Y) (z : Y × Y) :
    diagonalPerm p z = (p z.1, p z.2) := rfl

@[simp] theorem diagonalPerm_mul (p q : Equiv.Perm Y) :
    diagonalPerm (p * q) = diagonalPerm p * diagonalPerm q := by
  ext z <;> rfl

@[simp] theorem diagonalPerm_one :
    diagonalPerm (1 : Equiv.Perm Y) = 1 := by
  ext z <;> rfl

@[simp] theorem diagonalPerm_inv (p : Equiv.Perm Y) :
    diagonalPerm p⁻¹ = (diagonalPerm p)⁻¹ := by
  ext z <;> rfl

end Diagonal

section GraphDisagreement

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- Source vertices where two diagonal actions disagree on the graph of `c`. -/
def graphDiagonalDisagreement (c p q : Equiv.Perm Y) : Finset Y :=
  Finset.univ.filter fun x ↦
    diagonalPerm p (x, c x) ≠ diagonalPerm q (x, c x)

end GraphDisagreement

variable {Y : FiniteModel}

theorem graphDiagonalDisagreement_subset
    (c p q : Equiv.Perm Y) :
    graphDiagonalDisagreement c p q ⊆
      permutationDisagreement p q ∪
        permutationPreimage c (permutationDisagreement p q) := by
  intro x hx
  simp only [graphDiagonalDisagreement, Finset.mem_filter, Finset.mem_univ,
    true_and, diagonalPerm_apply] at hx
  rw [Finset.mem_union]
  by_cases hfirst : p x ≠ q x
  · exact Or.inl ((mem_permutationDisagreement p q x).2 hfirst)
  · right
    rw [permutationPreimage, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, (mem_permutationDisagreement p q (c x)).2 ?_⟩
    intro hsecond
    exact hx (Prod.ext (not_ne_iff.mp hfirst) hsecond)

theorem card_graphDiagonalDisagreement_le
    (c p q : Equiv.Perm Y) :
    (graphDiagonalDisagreement c p q).card ≤
      2 * (permutationDisagreement p q).card := by
  have hsubset := Finset.card_le_card
    (graphDiagonalDisagreement_subset c p q)
  have hunion := Finset.card_union_le (permutationDisagreement p q)
    (permutationPreimage c (permutationDisagreement p q))
  rw [permutationPreimage_card] at hunion
  omega

/-- Restricting diagonal disagreement to a permutation graph is exactly the
source disagreement set above. -/
theorem card_restrictedDiagonalDisagreement_eq
    (c p q : Equiv.Perm Y) :
    (restrictedPermutationDisagreement (permutationGraph Y c)
      (diagonalPerm p) (diagonalPerm q)).card =
        (graphDiagonalDisagreement c p q).card := by
  apply Finset.card_bij (fun z _ ↦ z.1)
  · intro z hz
    rw [mem_restrictedPermutationDisagreement] at hz
    have hgraph := (mem_permutationGraph Y c z).1 hz.1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hzEq : z = (z.1, c z.1) := Prod.ext rfl hgraph
    rw [hzEq] at hz
    exact hz.2
  · intro z hz w hw hfirst
    have hzdata := (mem_restrictedPermutationDisagreement
      (permutationGraph Y c) (diagonalPerm p) (diagonalPerm q) z).1 hz
    have hwdata := (mem_restrictedPermutationDisagreement
      (permutationGraph Y c) (diagonalPerm p) (diagonalPerm q) w).1 hw
    have hzc := (mem_permutationGraph Y c z).1 hzdata.1
    have hwc := (mem_permutationGraph Y c w).1 hwdata.1
    apply Prod.ext hfirst
    calc
      z.2 = c z.1 := hzc
      _ = c w.1 := congrArg c hfirst
      _ = w.2 := hwc.symm
  · intro x hx
    refine ⟨(x, c x), ?_, rfl⟩
    rw [mem_restrictedPermutationDisagreement]
    refine ⟨(mem_permutationGraph Y c _).2 rfl, ?_⟩
    simp only [graphDiagonalDisagreement, Finset.mem_filter, Finset.mem_univ,
      true_and] at hx
    exact hx

/-- The key `O(|Y|)` diagonal operator-error estimate used in the
Kun--Thom GNS compactness argument. -/
theorem norm_diagonal_centeredIndicator_sub_sq_le
    (c p q : Equiv.Perm Y) :
    ‖permutationOperator (diagonalPerm p)
          (centeredIndicator (permutationGraph Y c)) -
        permutationOperator (diagonalPerm q)
          (centeredIndicator (permutationGraph Y c))‖ ^ 2 ≤
      4 * (permutationDisagreement p q).card := by
  calc
    ‖permutationOperator (diagonalPerm p)
          (centeredIndicator (permutationGraph Y c)) -
        permutationOperator (diagonalPerm q)
          (centeredIndicator (permutationGraph Y c))‖ ^ 2 ≤
        2 * (restrictedPermutationDisagreement (permutationGraph Y c)
          (diagonalPerm p) (diagonalPerm q)).card :=
      norm_permutationOperators_centeredIndicator_sub_sq_le_restricted
        (permutationGraph Y c) (diagonalPerm p) (diagonalPerm q)
    _ = 2 * (graphDiagonalDisagreement c p q).card := by
      rw [card_restrictedDiagonalDisagreement_eq]
    _ ≤ 4 * (permutationDisagreement p q).card := by
      have h := card_graphDiagonalDisagreement_le c p q
      have hreal : ((graphDiagonalDisagreement c p q).card : ℝ) ≤
          2 * (permutationDisagreement p q).card := by
        exact_mod_cast h
      linarith

end KunThomDiagonal
end NonsoficGroupsExist
