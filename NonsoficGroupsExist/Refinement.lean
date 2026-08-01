import NonsoficGroupsExist.FiniteGraph
import Mathlib.Tactic.Linarith

/-!
# Expander refinement

This file formalizes Lemma `lem:refine` of the manuscript: on a graph all of
whose cuts expand, any partition of the vertices whose crossing edges are few
must have one dominant part.  Only the two-case greedy argument of the
manuscript is used; no probabilistic or spectral input appears.

The partition is presented as a labelling `part : V → ι`; `cell part T` is the
union of the parts labelled by `T`, and `crossingEdges part` is the multiset of
edges whose endpoints carry different labels.
-/

namespace NonsoficGroupsExist
namespace FiniteMultiGraph

variable {ι : Type*} [DecidableEq ι]

/-- Edge occurrences joining different parts. -/
def crossingEdges (X : FiniteMultiGraph) (part : X.vertex → ι) : Finset X.edge :=
  Finset.univ.filter fun e ↦ part (X.first e) ≠ part (X.second e)

/-- The union of the parts labelled by `T`. -/
def cell (X : FiniteMultiGraph) (part : X.vertex → ι) (T : Finset ι) :
    Finset X.vertex :=
  Finset.univ.filter fun x ↦ part x ∈ T

@[simp] theorem mem_cell (X : FiniteMultiGraph) (part : X.vertex → ι)
    (T : Finset ι) (x : X.vertex) : x ∈ X.cell part T ↔ part x ∈ T := by
  simp [cell]

@[simp] theorem cell_empty (X : FiniteMultiGraph) (part : X.vertex → ι) :
    X.cell part (∅ : Finset ι) = ∅ := by
  ext x
  simp

theorem cell_insert (X : FiniteMultiGraph) (part : X.vertex → ι)
    (i : ι) (T : Finset ι) :
    X.cell part (insert i T) = X.cell part {i} ∪ X.cell part T := by
  ext x
  simp

theorem cell_disjoint (X : FiniteMultiGraph) (part : X.vertex → ι)
    {i : ι} {T : Finset ι} (hi : i ∉ T) :
    Disjoint (X.cell part {i}) (X.cell part T) := by
  apply Finset.disjoint_left.mpr
  intro x hx hx'
  rw [mem_cell] at hx hx'
  rw [Finset.mem_singleton] at hx
  exact hi (hx ▸ hx')

theorem cell_compl (X : FiniteMultiGraph) [Fintype ι] (part : X.vertex → ι)
    (T : Finset ι) :
    X.cell part (Finset.univ \ T) = Finset.univ \ X.cell part T := by
  ext x
  simp

/-- Every boundary edge of a union of parts joins two different parts. -/
theorem boundary_cell_subset_crossingEdges (X : FiniteMultiGraph)
    (part : X.vertex → ι) (T : Finset ι) :
    X.boundary (X.cell part T) ⊆ X.crossingEdges part := by
  intro e he
  simp only [boundary, Finset.mem_filter, Finset.mem_univ, true_and, mem_cell] at he
  simp only [crossingEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  intro heq
  rcases he with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact h₂ (heq ▸ h₁)
  · exact h₂ (heq.symm ▸ h₁)

/-- A union of parts occupying at most half the graph has boundary at most the
crossing count; combined with expansion this bounds its size. -/
theorem cell_card_le_crossing (X : FiniteMultiGraph) {h : ℝ}
    (hch : X.HasCheegerLowerBound h) (part : X.vertex → ι) (T : Finset ι)
    (hne : (X.cell part T).Nonempty)
    (hhalf : 2 * (X.cell part T).card ≤ Fintype.card X.vertex) :
    h * (X.cell part T).card ≤ (X.crossingEdges part).card := by
  have hcheeger := hch.2 _ hne hhalf
  have hsub : (X.boundaryCard (X.cell part T) : ℝ) ≤ (X.crossingEdges part).card := by
    exact_mod_cast Finset.card_le_card
      (boundary_cell_subset_crossingEdges X part T)
  linarith

/-- The comparison step used three times in the proof of Lemma `lem:refine`. -/
theorem le_crossing_of_cell (X : FiniteMultiGraph) {h : ℝ}
    (hch : X.HasCheegerLowerBound h) (part : X.vertex → ι) (T : Finset ι)
    (hne : (X.cell part T).Nonempty)
    (hhalf : 2 * (X.cell part T).card ≤ Fintype.card X.vertex)
    (D : ℝ) (hD : D ≤ 4 * (X.cell part T).card) :
    h * D ≤ 4 * (X.crossingEdges part).card := by
  have hcell := cell_card_le_crossing X hch part T hne hhalf
  have hpos := hch.1
  nlinarith [hcell, hpos, hD]

/-- **Lemma `lem:refine`.**  On a graph whose cuts expand with constant `h`,
every labelling has a part `i₀` of maximal size whose complement is at most
`4e/h`, where `e` is the number of crossing edges. -/
theorem exists_dominant_cell (X : FiniteMultiGraph) {h : ℝ}
    (hch : X.HasCheegerLowerBound h) [Fintype ι] [Nonempty ι]
    (part : X.vertex → ι) (hV : 0 < Fintype.card X.vertex) :
    ∃ i₀ : ι,
      (∀ i : ι, (X.cell part {i}).card ≤ (X.cell part {i₀}).card) ∧
        h * ((Fintype.card X.vertex : ℝ) - (X.cell part {i₀}).card) ≤
          4 * (X.crossingEdges part).card := by
  classical
  obtain ⟨i₀, -, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset ι)
      (fun i ↦ (X.cell part {i}).card) Finset.univ_nonempty
  have hmax' : ∀ i : ι, (X.cell part {i}).card ≤ (X.cell part {i₀}).card :=
    fun i ↦ hmax i (Finset.mem_univ i)
  refine ⟨i₀, hmax', ?_⟩
  set V : ℕ := Fintype.card X.vertex with hVdef
  set A : Finset X.vertex := X.cell part {i₀} with hAdef
  have hAle : A.card ≤ V := by
    simpa [hVdef] using Finset.card_le_univ A
  have hcross_nonneg : (0 : ℝ) ≤ (X.crossingEdges part).card := by positivity
  have hpos := hch.1
  by_cases hbig : V ≤ 2 * A.card
  · -- The dominant part already occupies at least half the graph.
    set W : Finset X.vertex := X.cell part (Finset.univ \ {i₀}) with hWdef
    have hWcompl : W = Finset.univ \ A := by
      rw [hWdef, hAdef, cell_compl]
    have hWcard : W.card = V - A.card := by
      rw [hWcompl, Finset.card_sdiff, Finset.card_univ]
      simp [hVdef]
    have hWhalf : 2 * W.card ≤ V := by
      rw [hWcard]; omega
    rcases Finset.eq_empty_or_nonempty W with hWe | hWne
    · have : A.card = V := by
        have : W.card = 0 := by rw [hWe]; simp
        rw [hWcard] at this
        omega
      rw [this]
      simp only [sub_self, mul_zero]
      positivity
    · have hcast : ((V : ℝ) - A.card) = (W.card : ℝ) := by
        rw [hWcard, Nat.cast_sub hAle]
      rw [hcast]
      exact le_crossing_of_cell X hch part _ hWne hWhalf _ (by
        have : (0 : ℝ) ≤ (W.card : ℝ) := by positivity
        linarith)
  · -- No part occupies half the graph; accumulate parts greedily.
    have hbig' : 2 * A.card < V := lt_of_not_ge hbig
    have hsmall : ∀ i : ι, 2 * (X.cell part {i}).card < V := fun i ↦
      lt_of_le_of_lt (Nat.mul_le_mul_left 2 (hmax' i)) hbig'
    set cand : Finset (Finset ι) :=
      (Finset.univ : Finset (Finset ι)).filter
        fun T ↦ 4 * (X.cell part T).card < V with hcanddef
    have hcand_ne : cand.Nonempty := by
      refine ⟨∅, ?_⟩
      simp [hcanddef, hV]
    obtain ⟨T, hTmem, hTmax⟩ :=
      Finset.exists_max_image cand (fun T ↦ (X.cell part T).card) hcand_ne
    have hTlt : 4 * (X.cell part T).card < V := by
      simpa [hcanddef] using hTmem
    have hTne_univ : ∃ x : X.vertex, x ∉ X.cell part T := by
      by_contra hcon
      push Not at hcon
      have huniv : X.cell part T = Finset.univ :=
        Finset.eq_univ_iff_forall.mpr hcon
      rw [huniv, Finset.card_univ] at hTlt
      omega
    obtain ⟨x, hx⟩ := hTne_univ
    set p : ι := part x with hpdef
    have hpT : p ∉ T := by
      intro hmem
      apply hx
      rw [mem_cell]
      simpa [← hpdef] using hmem
    set W' : Finset X.vertex := X.cell part (insert p T) with hW'def
    have hxW' : x ∈ W' := by
      simp [hW'def, hpdef]
    have hW'ne : W'.Nonempty := ⟨x, hxW'⟩
    have hW'card :
        W'.card = (X.cell part {p}).card + (X.cell part T).card := by
      rw [hW'def, cell_insert, Finset.card_union_of_disjoint (cell_disjoint X part hpT)]
    have hgrow : (X.cell part T).card < W'.card := by
      have hxp : x ∈ X.cell part {p} := by simp [hpdef]
      have : 0 < (X.cell part {p}).card := Finset.card_pos.mpr ⟨x, hxp⟩
      omega
    have hW'lower : V ≤ 4 * W'.card := by
      by_contra hcon
      push Not at hcon
      have hmem : insert p T ∈ cand := by
        simp only [hcanddef, Finset.mem_filter, Finset.mem_univ, true_and]
        simpa [hW'def] using hcon
      have := hTmax _ hmem
      simp only [hW'def] at hgrow
      omega
    have hW'upper : 4 * W'.card < 3 * V := by
      have hp := hsmall p
      rw [hW'card]
      omega
    by_cases hhalf : 2 * W'.card ≤ V
    · refine le_crossing_of_cell X hch part _ hW'ne hhalf _ ?_
      have hcast : (V : ℝ) ≤ 4 * (W'.card : ℝ) := by exact_mod_cast hW'lower
      have hA : (0 : ℝ) ≤ (A.card : ℝ) := by positivity
      linarith
    · push Not at hhalf
      set W'' : Finset X.vertex := X.cell part (Finset.univ \ insert p T) with hW''def
      have hW''compl : W'' = Finset.univ \ W' := by
        rw [hW''def, hW'def, cell_compl]
      have hW''card : W''.card = V - W'.card := by
        rw [hW''compl, Finset.card_sdiff, Finset.card_univ]
        simp [hVdef]
      have hW'lt : W'.card < V := by omega
      have hW''ne : W''.Nonempty := by
        apply Finset.card_pos.mp
        rw [hW''card]
        omega
      have hW''half : 2 * W''.card ≤ V := by
        rw [hW''card]; omega
      refine le_crossing_of_cell X hch part _ hW''ne hW''half _ ?_
      have hcast : (V : ℝ) < 4 * (W''.card : ℝ) := by
        have hnat : V < 4 * W''.card := by
          rw [hW''card]; omega
        exact_mod_cast hnat
      have hA : (0 : ℝ) ≤ (A.card : ℝ) := by positivity
      linarith

end FiniteMultiGraph
end NonsoficGroupsExist
