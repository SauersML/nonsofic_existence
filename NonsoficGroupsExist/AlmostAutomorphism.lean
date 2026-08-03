import NonsoficGroupsExist.Sofic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Order

/-!
# Almost automorphisms of finite labeled permutation graphs

This module begins the kernel-checked replacement for the Kun--Thom input.
It formalizes the elementary separation mechanism behind their Lemma 4.1:
the agreement set of two label-preserving permutations can have boundary only
where at least one of the permutations fails to preserve a label.
-/

namespace NonsoficGroupsExist
namespace AlmostAutomorphism

variable (Y : FiniteModel)

/-- Label occurrences on a finite permutation graph. -/
abbrev Arc := Equiv.Perm Y × Y

/-- Label occurrences on which `c` fails to commute with the label. -/
def badArcs (S : Finset (Equiv.Perm Y)) (c : Equiv.Perm Y) :
    Finset (Arc Y) :=
  (S.product Finset.univ).filter fun p ↦ c (p.1 p.2) ≠ p.1 (c p.2)

@[simp] theorem mem_badArcs (S : Finset (Equiv.Perm Y))
    (c : Equiv.Perm Y) (p : Arc Y) :
    p ∈ badArcs Y S c ↔ p.1 ∈ S ∧ c (p.1 p.2) ≠ p.1 (c p.2) := by
  simp [badArcs]

/-- The directed label boundary of a set of vertices.  Both orientations are
retained when the label set is symmetric. -/
def directedBoundary (S : Finset (Equiv.Perm Y)) (A : Finset Y) :
    Finset (Arc Y) :=
  (S.product Finset.univ).filter fun p ↦
    (p.2 ∈ A ∧ p.1 p.2 ∉ A) ∨ (p.2 ∉ A ∧ p.1 p.2 ∈ A)

@[simp] theorem mem_directedBoundary (S : Finset (Equiv.Perm Y))
    (A : Finset Y) (p : Arc Y) :
    p ∈ directedBoundary Y S A ↔
      p.1 ∈ S ∧ ((p.2 ∈ A ∧ p.1 p.2 ∉ A) ∨
        (p.2 ∉ A ∧ p.1 p.2 ∈ A)) := by
  simp [directedBoundary]

/-- Vertices on which two permutations agree. -/
def agreement (c d : Equiv.Perm Y) : Finset Y :=
  Finset.univ.filter fun x ↦ c x = d x

@[simp] theorem mem_agreement (c d : Equiv.Perm Y) (x : Y) :
    x ∈ agreement Y c d ↔ c x = d x := by
  simp [agreement]

/-- Vertices on which two permutations disagree. -/
def disagreement (c d : Equiv.Perm Y) : Finset Y :=
  Finset.univ.filter fun x ↦ c x ≠ d x

@[simp] theorem mem_disagreement (c d : Equiv.Perm Y) (x : Y) :
    x ∈ disagreement Y c d ↔ c x ≠ d x := by
  simp [disagreement]

/-- Every label arc crossing the agreement set is bad for at least one of the
two permutations. -/
theorem directedBoundary_agreement_subset_badArcs_union
    (S : Finset (Equiv.Perm Y)) (c d : Equiv.Perm Y) :
    directedBoundary Y S (agreement Y c d) ⊆
      badArcs Y S c ∪ badArcs Y S d := by
  intro p hp
  rw [mem_directedBoundary] at hp
  rcases hp with ⟨hpS, hp⟩
  by_cases hc : c (p.1 p.2) ≠ p.1 (c p.2)
  · exact Finset.mem_union_left _ ((mem_badArcs Y S c p).2 ⟨hpS, hc⟩)
  by_cases hd : d (p.1 p.2) ≠ p.1 (d p.2)
  · exact Finset.mem_union_right _ ((mem_badArcs Y S d p).2 ⟨hpS, hd⟩)
  have hc' : c (p.1 p.2) = p.1 (c p.2) := not_ne_iff.mp hc
  have hd' : d (p.1 p.2) = p.1 (d p.2) := not_ne_iff.mp hd
  rcases hp with ⟨hx, hsx⟩ | ⟨hx, hsx⟩
  · have hxd : c p.2 = d p.2 := (mem_agreement Y c d p.2).1 hx
    have hsxd : c (p.1 p.2) ≠ d (p.1 p.2) := by
      simpa using hsx
    exfalso
    apply hsxd
    calc
      c (p.1 p.2) = p.1 (c p.2) := hc'
      _ = p.1 (d p.2) := congrArg p.1 hxd
      _ = d (p.1 p.2) := hd'.symm
  · have hxd : c p.2 ≠ d p.2 := by
      simpa using hx
    have hsxd : c (p.1 p.2) = d (p.1 p.2) :=
      (mem_agreement Y c d (p.1 p.2)).1 hsx
    exfalso
    apply hxd
    apply p.1.injective
    calc
      p.1 (c p.2) = c (p.1 p.2) := hc'.symm
      _ = d (p.1 p.2) := hsxd
      _ = p.1 (d p.2) := hd'

/-- Boundary size of the agreement set is bounded by the combined labeled
defects. -/
theorem card_directedBoundary_agreement_le
    (S : Finset (Equiv.Perm Y)) (c d : Equiv.Perm Y) :
    (directedBoundary Y S (agreement Y c d)).card ≤
      (badArcs Y S c).card + (badArcs Y S d).card := by
  exact (Finset.card_le_card
    (directedBoundary_agreement_subset_badArcs_union Y S c d)).trans
      (Finset.card_union_le _ _)

/-- Agreement and disagreement partition the vertex set. -/
theorem agreement_union_disagreement (c d : Equiv.Perm Y) :
    agreement Y c d ∪ disagreement Y c d = Finset.univ := by
  ext x
  by_cases h : c x = d x <;> simp [h]

theorem agreement_disjoint_disagreement (c d : Equiv.Perm Y) :
    Disjoint (agreement Y c d) (disagreement Y c d) := by
  exact Finset.disjoint_left.mpr fun x hx hy ↦
    (mem_disagreement Y c d x).1 hy ((mem_agreement Y c d x).1 hx)

/-- Hamming-count decomposition into agreement and disagreement vertices. -/
theorem card_agreement_add_card_disagreement (c d : Equiv.Perm Y) :
    (agreement Y c d).card + (disagreement Y c d).card = Fintype.card Y := by
  rw [← Finset.card_union_of_disjoint (agreement_disjoint_disagreement Y c d),
    agreement_union_disagreement]
  exact Finset.card_univ

theorem disagreement_eq_compl_agreement (c d : Equiv.Perm Y) :
    disagreement Y c d = Finset.univ \ agreement Y c d := by
  ext x
  by_cases h : c x = d x <;> simp [h]

theorem directedBoundary_compl (S : Finset (Equiv.Perm Y)) (A : Finset Y) :
    directedBoundary Y S (Finset.univ \ A) = directedBoundary Y S A := by
  ext p
  simp only [mem_directedBoundary, Finset.mem_sdiff, Finset.mem_univ, true_and]
  by_cases hx : p.2 ∈ A <;> by_cases hsx : p.1 p.2 ∈ A <;> simp [hx, hsx]

/-- Uniform directed edge expansion for a finite labeled permutation graph. -/
def HasDirectedExpansion (S : Finset (Equiv.Perm Y)) (h : ℝ) : Prop :=
  0 < h ∧ ∀ A : Finset Y, A.Nonempty →
    2 * A.card ≤ Fintype.card Y →
      h * A.card ≤ (directedBoundary Y S A).card

/-- Kun--Thom separation: on an expanding labeled graph, two permutations
with sufficiently few combined label defects cannot have both a large
agreement set and a large disagreement set. -/
theorem agreement_or_disagreement_small
    (S : Finset (Equiv.Perm Y)) {h : ℝ}
    (hexp : HasDirectedExpansion Y S h) (c d : Equiv.Perm Y)
    (m : ℕ) (hm : 0 < m)
    (hbad : (((badArcs Y S c).card + (badArcs Y S d).card : ℕ) : ℝ) <
      h * m) :
    (agreement Y c d).card < m ∨ (disagreement Y c d).card < m := by
  by_contra hsmall
  push Not at hsmall
  have hagree_nonempty : (agreement Y c d).Nonempty :=
    Finset.card_pos.mp (hm.trans_le hsmall.1)
  have hdisagree_nonempty : (disagreement Y c d).Nonempty :=
    Finset.card_pos.mp (hm.trans_le hsmall.2)
  have hboundary := card_directedBoundary_agreement_le Y S c d
  by_cases hhalf : 2 * (agreement Y c d).card ≤ Fintype.card Y
  · have hexpand := hexp.2 (agreement Y c d) hagree_nonempty hhalf
    have hmcast : (m : ℝ) ≤ ((agreement Y c d).card : ℝ) := by
      exact_mod_cast hsmall.1
    have hscale : h * m ≤ h * (agreement Y c d).card :=
      mul_le_mul_of_nonneg_left hmcast hexp.1.le
    have hboundarycast : ((directedBoundary Y S (agreement Y c d)).card : ℝ) ≤
        ((badArcs Y S c).card + (badArcs Y S d).card : ℕ) := by
      exact_mod_cast hboundary
    linarith
  · have hhalf' : 2 * (disagreement Y c d).card ≤ Fintype.card Y := by
      have hpartition := card_agreement_add_card_disagreement Y c d
      omega
    have hexpand := hexp.2 (disagreement Y c d) hdisagree_nonempty hhalf'
    have hmcast : (m : ℝ) ≤ ((disagreement Y c d).card : ℝ) := by
      exact_mod_cast hsmall.2
    have hscale : h * m ≤ h * (disagreement Y c d).card :=
      mul_le_mul_of_nonneg_left hmcast hexp.1.le
    have hboundaries :
        directedBoundary Y S (disagreement Y c d) =
          directedBoundary Y S (agreement Y c d) := by
      rw [disagreement_eq_compl_agreement, directedBoundary_compl]
    have hboundarycast : ((directedBoundary Y S (disagreement Y c d)).card : ℝ) ≤
        ((badArcs Y S c).card + (badArcs Y S d).card : ℕ) := by
      rw [hboundaries]
      exact_mod_cast hboundary
    linarith

end AlmostAutomorphism
end NonsoficGroupsExist
