import NonsoficGroupsExist.FiniteGraph
import Mathlib.Tactic.Linarith

/-!
# Removing the additive error from expansion

An additive Cheeger inequality need not control very small vertex sets.  This
module formalizes the maximal-cut repair used in the manuscript: remove a
maximum-cardinality sparse cut, then prove that the induced complement has a
genuine Cheeger lower bound.  The near-half case is recorded with the exact
finite numerical inequality needed by the argument; in an asymptotic
application it follows from negligibility of the additive error and of the
removed set.
-/

namespace NonsoficGroupsExist
namespace MaximalCutRepair

open FiniteMultiGraph

/-- A nonempty set of at most half the vertices whose boundary is smaller
than the requested expansion constant. -/
def IsSparseCut (X : FiniteMultiGraph) (c : ℝ) (U : Finset X.vertex) : Prop :=
  U.Nonempty ∧ 2 * U.card ≤ Fintype.card X.vertex ∧
    (X.boundaryCard U : ℝ) < c * U.card

/-- There is a maximum-cardinality sparse cut, with the empty set used when
there are no sparse cuts. -/
theorem exists_maximalSparseCut (X : FiniteMultiGraph) (c : ℝ) :
    ∃ B : Finset X.vertex,
      (B.Nonempty → IsSparseCut X c B) ∧
      ∀ U : Finset X.vertex, IsSparseCut X c U → U.card ≤ B.card := by
  classical
  let candidates := (Finset.univ : Finset (Finset X.vertex)).filter
    (IsSparseCut X c)
  by_cases hc : candidates.Nonempty
  · obtain ⟨B, hBmem, hBmax⟩ :=
      Finset.exists_max_image candidates Finset.card hc
    have hBsparse : IsSparseCut X c B := by
      exact (Finset.mem_filter.mp hBmem).2
    refine ⟨B, fun _ ↦ hBsparse, fun U hU ↦ ?_⟩
    exact hBmax U (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hU⟩)
  · refine ⟨∅, fun h ↦ (Finset.not_nonempty_empty h).elim, fun U hU ↦ ?_⟩
    exfalso
    apply hc
    exact ⟨U, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hU⟩⟩

/-- A fixed maximum sparse cut. -/
noncomputable def sparseCut (X : FiniteMultiGraph) (c : ℝ) :
    Finset X.vertex :=
  Classical.choose (exists_maximalSparseCut X c)

theorem sparseCut_sparse (X : FiniteMultiGraph) (c : ℝ)
    (hB : (sparseCut X c).Nonempty) :
    IsSparseCut X c (sparseCut X c) :=
  (Classical.choose_spec (exists_maximalSparseCut X c)).1 hB

theorem sparseCut_maximal (X : FiniteMultiGraph) (c : ℝ)
    (U : Finset X.vertex) (hU : IsSparseCut X c U) :
    U.card ≤ (sparseCut X c).card :=
  (Classical.choose_spec (exists_maximalSparseCut X c)).2 U hU

/-- The complement of the maximum sparse cut. -/
noncomputable def retained (X : FiniteMultiGraph) (c : ℝ) :
    Finset X.vertex := Finset.univ \ sparseCut X c

theorem sparseCut_disjoint_retained (X : FiniteMultiGraph) (c : ℝ) :
    Disjoint (sparseCut X c) (retained X c) := by
  apply Finset.disjoint_left.mpr
  intro x hxB hxR
  exact (Finset.mem_sdiff.mp hxR).2 hxB

theorem sparseCut_union_retained (X : FiniteMultiGraph) (c : ℝ) :
    sparseCut X c ∪ retained X c = Finset.univ := by
  simp [retained]

theorem retained_card (X : FiniteMultiGraph) (c : ℝ) :
    (retained X c).card =
      Fintype.card X.vertex - (sparseCut X c).card := by
  unfold retained
  rw [Finset.card_sdiff,
    Finset.inter_eq_left.mpr (Finset.subset_univ (sparseCut X c)),
    Finset.card_univ]

/-- Lift a vertex set in an induced graph to the ambient vertex type. -/
def ambientSet (X : FiniteMultiGraph) (Z : Finset X.vertex)
    (U : Finset (X.induce Z).vertex) : Finset X.vertex :=
  U.map (Function.Embedding.subtype _)

theorem ambientSet_card (X : FiniteMultiGraph) (Z : Finset X.vertex)
    (U : Finset (X.induce Z).vertex) :
    (ambientSet X Z U).card = U.card := by
  exact Finset.card_map _

theorem ambientSet_subset (X : FiniteMultiGraph) (Z : Finset X.vertex)
    (U : Finset (X.induce Z).vertex) : ambientSet X Z U ⊆ Z := by
  intro x hx
  obtain ⟨x', _, rfl⟩ := Finset.mem_map.mp hx
  exact x'.2

@[simp] theorem mem_ambientSet (X : FiniteMultiGraph) (Z : Finset X.vertex)
    (U : Finset (X.induce Z).vertex) (x : (X.induce Z).vertex) :
    x.1 ∈ ambientSet X Z U ↔ x ∈ U := by
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_map.mp hx
    have hyeq : y = x := Subtype.ext hyx
    rw [← hyeq]
    exact hy
  · intro hx
    exact Finset.mem_map.mpr ⟨x, hx, rfl⟩

/-- Ambient boundary edges of a lifted set either remain boundary edges in
the induced graph or leave the inducing vertex set. -/
theorem boundaryCard_ambientSet_le_induce_add_complement
    (X : FiniteMultiGraph) (Z : Finset X.vertex)
    (U : Finset (X.induce Z).vertex) :
    X.boundaryCard (ambientSet X Z U) ≤
      (X.induce Z).boundaryCard U + X.boundaryCard (Finset.univ \ Z) := by
  classical
  let internal : Finset X.edge :=
    ((X.induce Z).boundary U).map
      ⟨fun e ↦ e.1, fun _ _ h ↦ Subtype.ext h⟩
  have hsubset : X.boundary (ambientSet X Z U) ⊆
      internal ∪ X.boundary (Finset.univ \ Z) := by
    intro e he
    have hecut := (Finset.mem_filter.mp he).2
    have hUsub := ambientSet_subset X Z U
    by_cases hfirstZ : X.first e ∈ Z
    · by_cases hsecondZ : X.second e ∈ Z
      · have hmem (x : X.vertex) (hx : x ∈ Z) :
            (⟨x, hx⟩ : (X.induce Z).vertex) ∈ U ↔
              x ∈ ambientSet X Z U := by
          exact (mem_ambientSet X Z U ⟨x, hx⟩).symm
        have heinduced :
            (⟨e, hfirstZ, hsecondZ⟩ : (X.induce Z).edge) ∈
              (X.induce Z).boundary U := by
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          rcases hecut with h | h
          · exact Or.inl ⟨(hmem _ hfirstZ).mpr h.1,
                fun hs ↦ h.2 ((hmem _ hsecondZ).mp hs)⟩
          · exact Or.inr ⟨(hmem _ hsecondZ).mpr h.1,
                fun hs ↦ h.2 ((hmem _ hfirstZ).mp hs)⟩
        exact Finset.mem_union_left _ (Finset.mem_map.mpr
          ⟨⟨e, hfirstZ, hsecondZ⟩, heinduced, rfl⟩)
      · have hfirstU : X.first e ∈ ambientSet X Z U := by
          rcases hecut with h | h
          · exact h.1
          · exact False.elim (hsecondZ (hUsub h.1))
        have hcompSecond : X.second e ∈ Finset.univ \ Z := by simp [hsecondZ]
        have hcompFirst : X.first e ∉ Finset.univ \ Z := by simp [hfirstZ]
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, Or.inr ⟨hcompSecond, hcompFirst⟩⟩)
    · have hsecondU : X.second e ∈ ambientSet X Z U := by
        rcases hecut with h | h
        · exact False.elim (hfirstZ (hUsub h.1))
        · exact h.1
      have hsecondZ : X.second e ∈ Z := hUsub hsecondU
      have hcompFirst : X.first e ∈ Finset.univ \ Z := by simp [hfirstZ]
      have hcompSecond : X.second e ∉ Finset.univ \ Z := by simp [hsecondZ]
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, Or.inl ⟨hcompFirst, hcompSecond⟩⟩)
  calc
    X.boundaryCard (ambientSet X Z U) ≤ (internal ∪
        X.boundary (Finset.univ \ Z)).card := Finset.card_le_card hsubset
    _ ≤ internal.card + (X.boundary (Finset.univ \ Z)).card :=
      Finset.card_union_le _ _
    _ = (X.induce Z).boundaryCard U +
        X.boundaryCard (Finset.univ \ Z) := by
      rw [show internal.card = ((X.induce Z).boundary U).card by
        exact Finset.card_map _]
      rfl

/-- Joining a lifted set to the removed complement costs no more than the
two separate boundaries: an edge leaving their union must leave one of the
two pieces. -/
theorem boundaryCard_union_complement_le
    (X : FiniteMultiGraph) (Z : Finset X.vertex)
    (U : Finset (X.induce Z).vertex) :
    X.boundaryCard (ambientSet X Z U ∪ (Finset.univ \ Z)) ≤
      (X.induce Z).boundaryCard U + X.boundaryCard (Finset.univ \ Z) := by
  classical
  let internal : Finset X.edge :=
    ((X.induce Z).boundary U).map
      ⟨fun e ↦ e.1, fun _ _ h ↦ Subtype.ext h⟩
  have hUsub := ambientSet_subset X Z U
  have hsubset : X.boundary (ambientSet X Z U ∪ (Finset.univ \ Z)) ⊆
      internal ∪ X.boundary (Finset.univ \ Z) := by
    intro e he
    have hecut := (Finset.mem_filter.mp he).2
    have houtside (x : X.vertex)
        (hx : x ∉ ambientSet X Z U ∪ (Finset.univ \ Z)) : x ∈ Z := by
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and,
        not_or] at hx
      exact Decidable.not_not.mp hx.2
    rcases hecut with h | h
    · have hsecondZ := houtside _ h.2
      rcases Finset.mem_union.mp h.1 with hfirstU | hfirstB
      · have hfirstZ := hUsub hfirstU
        have hmem (x : X.vertex) (hx : x ∈ Z) :
            (⟨x, hx⟩ : (X.induce Z).vertex) ∈ U ↔
              x ∈ ambientSet X Z U := by
          exact (mem_ambientSet X Z U ⟨x, hx⟩).symm
        have heind : (⟨e, hfirstZ, hsecondZ⟩ : (X.induce Z).edge) ∈
            (X.induce Z).boundary U := by
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_univ _, Or.inl ⟨(hmem _ hfirstZ).mpr hfirstU,
            fun hs ↦ h.2 (Finset.mem_union_left _ ((hmem _ hsecondZ).mp hs))⟩⟩
        exact Finset.mem_union_left _ (Finset.mem_map.mpr
          ⟨⟨e, hfirstZ, hsecondZ⟩, heind, rfl⟩)
      · have hsecondB : X.second e ∉ Finset.univ \ Z := by simp [hsecondZ]
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, Or.inl ⟨hfirstB, hsecondB⟩⟩)
    · have hfirstZ := houtside _ h.2
      rcases Finset.mem_union.mp h.1 with hsecondU | hsecondB
      · have hsecondZ := hUsub hsecondU
        have hmem (x : X.vertex) (hx : x ∈ Z) :
            (⟨x, hx⟩ : (X.induce Z).vertex) ∈ U ↔
              x ∈ ambientSet X Z U := by
          exact (mem_ambientSet X Z U ⟨x, hx⟩).symm
        have heind : (⟨e, hfirstZ, hsecondZ⟩ : (X.induce Z).edge) ∈
            (X.induce Z).boundary U := by
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_univ _, Or.inr ⟨(hmem _ hsecondZ).mpr hsecondU,
            fun hs ↦ h.2 (Finset.mem_union_left _ ((hmem _ hfirstZ).mp hs))⟩⟩
        exact Finset.mem_union_left _ (Finset.mem_map.mpr
          ⟨⟨e, hfirstZ, hsecondZ⟩, heind, rfl⟩)
      · have hfirstB : X.first e ∉ Finset.univ \ Z := by simp [hfirstZ]
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, Or.inr ⟨hsecondB, hfirstB⟩⟩)
  calc
    X.boundaryCard (ambientSet X Z U ∪ (Finset.univ \ Z)) ≤
        (internal ∪ X.boundary (Finset.univ \ Z)).card :=
      Finset.card_le_card hsubset
    _ ≤ internal.card + (X.boundary (Finset.univ \ Z)).card :=
      Finset.card_union_le _ _
    _ = (X.induce Z).boundaryCard U +
        X.boundaryCard (Finset.univ \ Z) := by
      rw [show internal.card = ((X.induce Z).boundary U).card by
        exact Finset.card_map _]
      rfl

/-- The additive inequality bounds the maximum sparse cut quantitatively. -/
theorem sparseCut_card_bound (X : FiniteMultiGraph) {γ c a : ℝ}
    (ha : 0 ≤ a)
    (hadd : ∀ U : Finset X.vertex, U.Nonempty →
      2 * U.card ≤ Fintype.card X.vertex →
      γ * (U.card : ℝ) ≤ (X.boundaryCard U : ℝ) +
        a * Fintype.card X.vertex) :
    (γ - c) * ((sparseCut X c).card : ℝ) ≤
      a * Fintype.card X.vertex := by
  by_cases hB : (sparseCut X c).Nonempty
  · have hsparse := sparseCut_sparse X c hB
    have haddB := hadd (sparseCut X c) hB hsparse.2.1
    linarith [hsparse.2.2]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hB]
    simp
    positivity

/-- Maximal-cut repair.  The last inequality is precisely the finite
near-half estimate; it is automatic eventually when `a` and the removed
proportion tend to zero while `γ - c` stays positive. -/
theorem induce_retained_hasCheegerLowerBound
    (X : FiniteMultiGraph) {γ c a d : ℝ}
    (hc : 0 < c) (hgap : c < γ)
    (hadd : ∀ U : Finset X.vertex, U.Nonempty →
      2 * U.card ≤ Fintype.card X.vertex →
      γ * (U.card : ℝ) ≤ (X.boundaryCard U : ℝ) +
        a * Fintype.card X.vertex)
    (hdegree : (X.boundaryCard (sparseCut X c) : ℝ) ≤
      d * (sparseCut X c).card)
    (hnear : 2 * (a * Fintype.card X.vertex +
        d * (sparseCut X c).card) ≤
      (γ - c) * ((Fintype.card X.vertex : ℝ) -
        2 * (sparseCut X c).card)) :
    (X.induce (retained X c)).HasCheegerLowerBound c := by
  classical
  refine ⟨hc, ?_⟩
  intro U hU hhalf
  let U₀ := ambientSet X (retained X c) U
  let B := sparseCut X c
  have hUcard : U₀.card = U.card := ambientSet_card X _ U
  have hU₀ : U₀.Nonempty := by
    obtain ⟨x, hx⟩ := hU
    exact ⟨x.1, Finset.mem_map.mpr ⟨x, hx, rfl⟩⟩
  have hUsub : U₀ ⊆ retained X c := ambientSet_subset X _ U
  have hUB : Disjoint U₀ B := by
    apply Finset.disjoint_left.mpr
    intro x hxU hxB
    exact Finset.disjoint_left.mp (sparseCut_disjoint_retained X c) hxB (hUsub hxU)
  have hretainedCard : (retained X c).card =
      Fintype.card X.vertex - B.card := retained_card X c
  by_cases hunionHalf : 2 * (U₀ ∪ B).card ≤ Fintype.card X.vertex
  · by_contra hboundary
    have hboundarylt : ((X.induce (retained X c)).boundaryCard U : ℝ) <
        c * U.card := lt_of_not_ge hboundary
    have hunionNe : (U₀ ∪ B).Nonempty := hU₀.mono Finset.subset_union_left
    have hBboundary : B.Nonempty → (X.boundaryCard B : ℝ) < c * B.card :=
      fun hB ↦ (sparseCut_sparse X c hB).2.2
    have hunionBoundary := boundaryCard_union_complement_le
      X (retained X c) U
    have hcomplement : Finset.univ \ retained X c = B := by
      simp [retained, B]
    rw [hcomplement] at hunionBoundary
    have hunionBoundaryReal :
        (X.boundaryCard (ambientSet X (retained X c) U ∪ B) : ℝ) ≤
          (X.induce (retained X c)).boundaryCard U + X.boundaryCard B := by
      exact_mod_cast hunionBoundary
    have hunionEq : U₀ ∪ B =
        ambientSet X (retained X c) U ∪ B := rfl
    have hunionSparse : IsSparseCut X c (U₀ ∪ B) := by
      refine ⟨hunionNe, hunionHalf, ?_⟩
      by_cases hB : B.Nonempty
      · have hcardUnion : (U₀ ∪ B).card = U₀.card + B.card :=
          Finset.card_union_of_disjoint hUB
        rw [hunionEq] at hunionBoundary
        rw [hunionEq] at hunionBoundaryReal
        rw [hcardUnion, hUcard]
        push_cast
        linarith [hBboundary hB, hunionBoundaryReal]
      · have hBeq : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
        rw [hBeq] at hunionBoundaryReal ⊢
        have hempty : X.boundaryCard (∅ : Finset X.vertex) = 0 := by
          simp [FiniteMultiGraph.boundaryCard, FiniteMultiGraph.boundary]
        rw [hempty, Nat.cast_zero, add_zero] at hunionBoundaryReal
        simp only [Finset.union_empty] at hunionBoundaryReal ⊢
        change (X.boundaryCard (ambientSet X (retained X c) U) : ℝ) ≤
          (X.induce (retained X c)).boundaryCard U at hunionBoundaryReal
        change X.boundaryCard U₀ < c * (U₀.card : ℝ)
        rw [hUcard]
        linarith
    have hmax := sparseCut_maximal X c (U₀ ∪ B) hunionSparse
    have hcardUnion : (U₀ ∪ B).card = U₀.card + B.card :=
      Finset.card_union_of_disjoint hUB
    change (U₀ ∪ B).card ≤ B.card at hmax
    have hlt : B.card < (U₀ ∪ B).card := by
      rw [hcardUnion]
      exact Nat.lt_add_of_pos_left (Finset.card_pos.mpr hU₀)
    exact (not_lt_of_ge hmax) hlt
  · have hUhalfAmbient : 2 * U₀.card ≤ Fintype.card X.vertex := by
      have hvertex : Fintype.card (X.induce (retained X c)).vertex =
          (retained X c).card := by simp [FiniteMultiGraph.induce]
      rw [hvertex] at hhalf
      calc
        2 * U₀.card = 2 * U.card := by rw [hUcard]
        _ ≤ (retained X c).card := hhalf
        _ ≤ Fintype.card X.vertex := Finset.card_le_univ _
    have haddU := hadd U₀ hU₀ hUhalfAmbient
    have hambient := boundaryCard_ambientSet_le_induce_add_complement
      X (retained X c) U
    have hcomplement : Finset.univ \ retained X c = B := by
      simp [retained, B]
    rw [hcomplement] at hambient
    have hunionLarge : Fintype.card X.vertex < 2 * (U₀.card + B.card) := by
      rw [Finset.card_union_of_disjoint hUB] at hunionHalf
      omega
    have hgapPos : 0 < γ - c := sub_pos.mpr hgap
    have hlargeReal : (Fintype.card X.vertex : ℝ) - 2 * B.card <
        2 * U₀.card := by
      have hlargeCast : (Fintype.card X.vertex : ℝ) <
          2 * ((U₀.card : ℝ) + B.card) := by exact_mod_cast hunionLarge
      linarith
    have herror : a * Fintype.card X.vertex + d * B.card <
        (γ - c) * U₀.card := by
      have hscaled := mul_lt_mul_of_pos_left hlargeReal hgapPos
      nlinarith [hnear]
    have hambientReal : (X.boundaryCard U₀ : ℝ) ≤
        (X.induce (retained X c)).boundaryCard U + X.boundaryCard B := by
      simpa [U₀] using (show
        (X.boundaryCard (ambientSet X (retained X c) U) : ℝ) ≤
          (X.induce (retained X c)).boundaryCard U + X.boundaryCard B by
            exact_mod_cast hambient)
    rw [← hUcard]
    linarith

end MaximalCutRepair
end NonsoficGroupsExist
