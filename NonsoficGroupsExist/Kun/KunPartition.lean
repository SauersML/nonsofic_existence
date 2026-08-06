import NonsoficGroupsExist.Kun.KunUniformRounding

/-!
# The finite minimal-cut step in Kun's partition construction

The expander partition is built by repeatedly choosing a smallest nonempty
low-boundary subset of the vertices not yet assigned.  This file isolates the
finite minimization argument and the consequences of replacing that set by a
nearby set with much smaller boundary.
-/

namespace NonsoficGroupsExist
namespace KunPartition

open FiniteMultiGraph
open scoped symmDiff

variable {X : FiniteMultiGraph}

/-- Nonempty subsets of `R` whose boundary ratio is strictly below `γ`. -/
noncomputable def lowCutSubsets (X : FiniteMultiGraph) (R : Finset X.vertex)
    (γ : ℝ) : Finset (Finset X.vertex) :=
  R.powerset.filter fun T ↦
    T.Nonempty ∧ (X.boundaryCard T : ℝ) < γ * T.card

@[simp] theorem mem_lowCutSubsets (T R : Finset X.vertex) (γ : ℝ) :
    T ∈ lowCutSubsets X R γ ↔
      T ⊆ R ∧ T.Nonempty ∧ (X.boundaryCard T : ℝ) < γ * T.card := by
  classical
  simp [lowCutSubsets]

/-- Every nonempty finite family of finite sets has a member of minimum
cardinality.  We minimize the finite image in `ℕ`, avoiding any arbitrary
ordering of the vertex type. -/
theorem exists_min_card_member {α : Type*}
    (C : Finset (Finset α)) (hC : C.Nonempty) :
    ∃ T ∈ C, ∀ U ∈ C, T.card ≤ U.card := by
  classical
  let sizes : Finset ℕ := C.image Finset.card
  have hsizes : sizes.Nonempty := hC.image _
  let m : ℕ := sizes.min' hsizes
  have hm : m ∈ sizes := Finset.min'_mem sizes hsizes
  obtain ⟨T, hTC, hTm⟩ := Finset.mem_image.mp hm
  refine ⟨T, hTC, fun U hUC ↦ ?_⟩
  have hU : U.card ∈ sizes := Finset.mem_image.mpr ⟨U, hUC, rfl⟩
  have hmin : m ≤ U.card := Finset.min'_le sizes U.card hU
  simpa [m, hTm] using hmin

/-- A bad subset can be chosen smallest among all bad subsets of the current
remainder. -/
theorem exists_minimal_lowCutSubset (R : Finset X.vertex) (γ : ℝ)
    (hbad : (lowCutSubsets X R γ).Nonempty) :
    ∃ T : Finset X.vertex,
      T ⊆ R ∧ T.Nonempty ∧
      (X.boundaryCard T : ℝ) < γ * T.card ∧
      ∀ U : Finset X.vertex, U ⊆ R → U.Nonempty →
        (X.boundaryCard U : ℝ) < γ * U.card → T.card ≤ U.card := by
  obtain ⟨T, hT, hmin⟩ :=
    exists_min_card_member (lowCutSubsets X R γ) hbad
  have hTp := (mem_lowCutSubsets T R γ).1 hT
  refine ⟨T, hTp.1, hTp.2.1, hTp.2.2, fun U hUR hU hcut ↦ ?_⟩
  exact hmin U ((mem_lowCutSubsets U R γ).2 ⟨hUR, hU, hcut⟩)

/-- The selected smallest low-cut set.  Its existence argument is an input,
but in the recursion that argument is obtained by deciding the finite family
`lowCutSubsets`. -/
noncomputable def minimalLowCutSubset (R : Finset X.vertex) (γ : ℝ)
    (hbad : (lowCutSubsets X R γ).Nonempty) : Finset X.vertex :=
  Classical.choose (exists_minimal_lowCutSubset R γ hbad)

theorem minimalLowCutSubset_spec (R : Finset X.vertex) (γ : ℝ)
    (hbad : (lowCutSubsets X R γ).Nonempty) :
    minimalLowCutSubset R γ hbad ⊆ R ∧
      (minimalLowCutSubset R γ hbad).Nonempty ∧
      (X.boundaryCard (minimalLowCutSubset R γ hbad) : ℝ) <
        γ * (minimalLowCutSubset R γ hbad).card ∧
      ∀ U : Finset X.vertex, U ⊆ R → U.Nonempty →
        (X.boundaryCard U : ℝ) < γ * U.card →
        (minimalLowCutSubset R γ hbad).card ≤ U.card :=
  Classical.choose_spec (exists_minimal_lowCutSubset R γ hbad)

/-- A set within one-third symmetric difference of a nonempty set meets it. -/
theorem inter_nonempty_of_symmDiff_lt_third
    (T W : Finset X.vertex) (hT : T.Nonempty)
    (hclose : ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3) :
    (T ∩ W).Nonempty := by
  classical
  have hTpos : (0 : ℝ) < T.card := by
    exact_mod_cast Finset.card_pos.mpr hT
  have hdiffReal : ((W ∆ T).card : ℝ) < T.card := by linarith
  have hdiff : (W ∆ T).card < T.card := by exact_mod_cast hdiffReal
  have hsub : T \ W ⊆ W ∆ T := by
    intro x hx
    have hx' := Finset.mem_sdiff.mp hx
    exact Finset.mem_symmDiff.mpr (Or.inr ⟨hx'.1, hx'.2⟩)
  have hle := Finset.card_le_card hsub
  have hsplit := Finset.card_sdiff_add_card_inter T W
  exact Finset.card_pos.mp (by omega)

/-- A one-third replacement has fewer than twice as many vertices as its
input. -/
theorem card_lt_two_mul_of_symmDiff_lt_third
    (T W : Finset X.vertex) (hT : T.Nonempty)
    (hclose : ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3) :
    W.card < 2 * T.card := by
  classical
  have hWT : W \ T ⊆ W ∆ T := by
    intro x hx
    have hx' := Finset.mem_sdiff.mp hx
    exact Finset.mem_symmDiff.mpr (Or.inl ⟨hx'.1, hx'.2⟩)
  have hinter : (W ∩ T).card ≤ T.card :=
    Finset.card_le_card Finset.inter_subset_right
  have hsplit := Finset.card_sdiff_add_card_inter W T
  have hWle : W.card ≤ (W ∆ T).card + T.card := by
    have := Finset.card_le_card hWT
    omega
  have hTpos : (0 : ℝ) < T.card := by
    exact_mod_cast Finset.card_pos.mpr hT
  have hWleReal : (W.card : ℝ) ≤
      ((W ∆ T).card : ℝ) + (T.card : ℝ) := by
    exact_mod_cast hWle
  have hWreal : (W.card : ℝ) < 2 * T.card := by
    exact lt_of_le_of_lt hWleReal (by linarith)
  exact_mod_cast hWreal

/-- When the input is disjoint from the already assigned vertices, the new
piece retains more than half of the input. -/
theorem card_lt_two_mul_replacementPiece
    (A T W : Finset X.vertex) (hTrest : T ⊆ Finset.univ \ A)
    (hclose : ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3) :
    T.card < 2 * (W \ A).card := by
  classical
  have hsub : T \ W ⊆ W ∆ T := by
    intro x hx
    have hx' := Finset.mem_sdiff.mp hx
    exact Finset.mem_symmDiff.mpr (Or.inr ⟨hx'.1, hx'.2⟩)
  have hle := Finset.card_le_card hsub
  have hthreeReal : (3 : ℝ) * ((T \ W).card : ℝ) < T.card := by
    have hcast : ((T \ W).card : ℝ) ≤ (W ∆ T).card := by
      exact_mod_cast hle
    linarith
  have hthree : 3 * (T \ W).card < T.card := by exact_mod_cast hthreeReal
  have hsplit := Finset.card_sdiff_add_card_inter T W
  have hinterPiece : T ∩ W ⊆ W \ A := by
    intro x hx
    have hxT := (Finset.mem_inter.mp hx).1
    have hxW := (Finset.mem_inter.mp hx).2
    exact Finset.mem_sdiff.mpr
      ⟨hxW, (Finset.mem_sdiff.mp (hTrest hxT)).2⟩
  have hinterCard := Finset.card_le_card hinterPiece
  omega

/-- The new piece in Kun's recursion is nonempty and inherits the uniform
lower cut bound from minimality of the original bad set.  Boundary here is
still measured in the original graph; the subsequent graph-edit step turns
this into component expansion. -/
theorem replacementPiece_expands
    (A T W : Finset X.vertex) (γ : ℝ)
    (hTrest : T ⊆ Finset.univ \ A) (hT : T.Nonempty)
    (hminimal : ∀ U : Finset X.vertex,
      U ⊆ Finset.univ \ A → U.Nonempty →
      (X.boundaryCard U : ℝ) < γ * U.card → T.card ≤ U.card)
    (hclose : ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3) :
    let P := W \ A
    P.Nonempty ∧ P.card < 2 * T.card ∧ T.card < 2 * P.card ∧
      ∀ U : Finset X.vertex, U ⊆ P → U.Nonempty →
        2 * U.card ≤ P.card →
        γ * U.card ≤ X.boundaryCard U := by
  classical
  dsimp only
  have hmeet := inter_nonempty_of_symmDiff_lt_third T W hT hclose
  have hP : (W \ A).Nonempty := by
    obtain ⟨x, hx⟩ := hmeet
    have hxT := (Finset.mem_inter.mp hx).1
    have hxW := (Finset.mem_inter.mp hx).2
    have hxA : x ∉ A := (Finset.mem_sdiff.mp (hTrest hxT)).2
    exact ⟨x, Finset.mem_sdiff.mpr ⟨hxW, hxA⟩⟩
  have hPcard : (W \ A).card < 2 * T.card :=
    lt_of_le_of_lt (Finset.card_le_card Finset.sdiff_subset)
      (card_lt_two_mul_of_symmDiff_lt_third T W hT hclose)
  have hTcard : T.card < 2 * (W \ A).card :=
    card_lt_two_mul_replacementPiece A T W hTrest hclose
  refine ⟨hP, hPcard, hTcard, fun U hUP hU hhalf ↦ ?_⟩
  have hUR : U ⊆ Finset.univ \ A := by
    intro x hx
    have hxP := hUP hx
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hxP).2⟩
  by_contra hbound
  have hlow : (X.boundaryCard U : ℝ) < γ * U.card := lt_of_not_ge hbound
  have hTU := hminimal U hUR hU hlow
  omega

theorem disjoint_base_of_subset_remainder
    (B A T : Finset X.vertex) (hBA : B ⊆ A)
    (hT : T ⊆ Finset.univ \ A) : Disjoint T B := by
  apply Finset.disjoint_left.mpr
  intro x hxT hxB
  exact (Finset.mem_sdiff.mp (hT hxT)).2 (hBA hxB)

/-- Choice of the small-boundary replacement attached to the selected
minimum low-cut set at one stage of the recursion. -/
noncomputable def chosenReplacement
    (B A : Finset X.vertex) (γ α : ℝ) (hBA : B ⊆ A)
    (hbad : (lowCutSubsets X (Finset.univ \ A) γ).Nonempty)
    (replace : ∀ T : Finset X.vertex, T.Nonempty → Disjoint T B →
      (X.boundaryCard T : ℝ) < γ * T.card →
      ∃ W : Finset X.vertex,
        ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3 ∧
        (X.boundaryCard W : ℝ) < α * T.card) : Finset X.vertex := by
  let T := minimalLowCutSubset (Finset.univ \ A) γ hbad
  have hT := minimalLowCutSubset_spec (Finset.univ \ A) γ hbad
  exact Classical.choose
    (replace T hT.2.1 (disjoint_base_of_subset_remainder B A T hBA hT.1)
      hT.2.2.1)

theorem chosenReplacement_spec
    (B A : Finset X.vertex) (γ α : ℝ) (hBA : B ⊆ A)
    (hbad : (lowCutSubsets X (Finset.univ \ A) γ).Nonempty)
    (replace : ∀ T : Finset X.vertex, T.Nonempty → Disjoint T B →
      (X.boundaryCard T : ℝ) < γ * T.card →
      ∃ W : Finset X.vertex,
        ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3 ∧
        (X.boundaryCard W : ℝ) < α * T.card) :
    let T := minimalLowCutSubset (Finset.univ \ A) γ hbad
    (((chosenReplacement B A γ α hBA hbad replace ∆ T).card : ℝ) <
        (T.card : ℝ) / 3) ∧
      (X.boundaryCard (chosenReplacement B A γ α hBA hbad replace) : ℝ) <
        α * T.card := by
  dsimp only
  exact Classical.choose_spec
    (replace _ (minimalLowCutSubset_spec (Finset.univ \ A) γ hbad).2.1
      (disjoint_base_of_subset_remainder B A _ hBA
        (minimalLowCutSubset_spec (Finset.univ \ A) γ hbad).1)
      (minimalLowCutSubset_spec (Finset.univ \ A) γ hbad).2.2.1)

/-- One new block: use the chosen replacement when the remainder has a
low-cut set, and otherwise consume the whole remainder as the final block. -/
noncomputable def nextPiece
    (B A : Finset X.vertex) (γ α : ℝ) (hBA : B ⊆ A)
    (replace : ∀ T : Finset X.vertex, T.Nonempty → Disjoint T B →
      (X.boundaryCard T : ℝ) < γ * T.card →
      ∃ W : Finset X.vertex,
        ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3 ∧
        (X.boundaryCard W : ℝ) < α * T.card) : Finset X.vertex :=
  if hbad : (lowCutSubsets X (Finset.univ \ A) γ).Nonempty then
    chosenReplacement B A γ α hBA hbad replace \ A
  else
    Finset.univ \ A

theorem nextPiece_subset_remainder
    (B A : Finset X.vertex) (γ α : ℝ) (hBA : B ⊆ A)
    (replace : ∀ T : Finset X.vertex, T.Nonempty → Disjoint T B →
      (X.boundaryCard T : ℝ) < γ * T.card →
      ∃ W : Finset X.vertex,
        ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3 ∧
        (X.boundaryCard W : ℝ) < α * T.card) :
    nextPiece B A γ α hBA replace ⊆ Finset.univ \ A := by
  classical
  intro x hx
  unfold nextPiece at hx
  split at hx
  · exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hx).2⟩
  · exact hx

theorem nextPiece_nonempty_of_ne_univ
    (B A : Finset X.vertex) (γ α : ℝ) (hBA : B ⊆ A)
    (replace : ∀ T : Finset X.vertex, T.Nonempty → Disjoint T B →
      (X.boundaryCard T : ℝ) < γ * T.card →
      ∃ W : Finset X.vertex,
        ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3 ∧
        (X.boundaryCard W : ℝ) < α * T.card)
    (hA : A ≠ Finset.univ) :
    (nextPiece B A γ α hBA replace).Nonempty := by
  classical
  unfold nextPiece
  split
  next hbad =>
    let T := minimalLowCutSubset (Finset.univ \ A) γ hbad
    let W := chosenReplacement B A γ α hBA hbad replace
    have hT := minimalLowCutSubset_spec (Finset.univ \ A) γ hbad
    have hW := chosenReplacement_spec B A γ α hBA hbad replace
    exact (replacementPiece_expands A T W γ hT.1 hT.2.1 hT.2.2.2
      hW.1).1
  next hbad =>
    by_contra hrest
    have hempty : Finset.univ \ A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hrest
    apply hA
    ext x
    have hx : x ∉ Finset.univ \ A := by simp [hempty]
    simpa using hx

theorem nextPiece_expands
    (B A : Finset X.vertex) (γ α : ℝ) (hBA : B ⊆ A)
    (replace : ∀ T : Finset X.vertex, T.Nonempty → Disjoint T B →
      (X.boundaryCard T : ℝ) < γ * T.card →
      ∃ W : Finset X.vertex,
        ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3 ∧
        (X.boundaryCard W : ℝ) < α * T.card) :
    ∀ U : Finset X.vertex,
      U ⊆ nextPiece B A γ α hBA replace → U.Nonempty →
      2 * U.card ≤ (nextPiece B A γ α hBA replace).card →
      γ * U.card ≤ X.boundaryCard U := by
  classical
  intro U hU hUne hhalf
  unfold nextPiece at hU hhalf
  split at hU
  next hbad =>
    rw [dif_pos hbad] at hhalf
    let T := minimalLowCutSubset (Finset.univ \ A) γ hbad
    let W := chosenReplacement B A γ α hBA hbad replace
    have hT := minimalLowCutSubset_spec (Finset.univ \ A) γ hbad
    have hW := chosenReplacement_spec B A γ α hBA hbad replace
    exact (replacementPiece_expands A T W γ hT.1 hT.2.1 hT.2.2.2
      hW.1).2.2.2 U hU hUne hhalf
  next hbad =>
    rw [dif_neg hbad] at hhalf
    by_contra hbound
    apply hbad
    refine ⟨U, (mem_lowCutSubsets U (Finset.univ \ A) γ).2 ?_⟩
    exact ⟨hU, hUne, lt_of_not_ge hbound⟩

/-- Recursion state together with the invariant that the initial exceptional
set remains assigned. -/
abbrev AssignmentState (B : Finset X.vertex) := {A : Finset X.vertex // B ⊆ A}

noncomputable def advanceState
    (B : Finset X.vertex) (γ α : ℝ)
    (replace : ∀ T : Finset X.vertex, T.Nonempty → Disjoint T B →
      (X.boundaryCard T : ℝ) < γ * T.card →
      ∃ W : Finset X.vertex,
        ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3 ∧
        (X.boundaryCard W : ℝ) < α * T.card)
    (state : AssignmentState B) : AssignmentState B :=
  ⟨state.1 ∪ nextPiece B state.1 γ α state.2 replace,
    state.2.trans Finset.subset_union_left⟩

/-- The assigned vertices after `i` recursive partition steps. -/
noncomputable def assignedAt
    (B : Finset X.vertex) (γ α : ℝ)
    (replace : ∀ T : Finset X.vertex, T.Nonempty → Disjoint T B →
      (X.boundaryCard T : ℝ) < γ * T.card →
      ∃ W : Finset X.vertex,
        ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3 ∧
        (X.boundaryCard W : ℝ) < α * T.card) :
    ℕ → AssignmentState B
  | 0 => ⟨B, fun _ h ↦ h⟩
  | i + 1 => advanceState B γ α replace (assignedAt B γ α replace i)

@[simp] theorem assignedAt_zero
    (B : Finset X.vertex) (γ α : ℝ)
    (replace : ∀ T : Finset X.vertex, T.Nonempty → Disjoint T B →
      (X.boundaryCard T : ℝ) < γ * T.card →
      ∃ W : Finset X.vertex,
        ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3 ∧
        (X.boundaryCard W : ℝ) < α * T.card) :
    (assignedAt B γ α replace 0).1 = B := rfl

@[simp] theorem assignedAt_succ
    (B : Finset X.vertex) (γ α : ℝ)
    (replace : ∀ T : Finset X.vertex, T.Nonempty → Disjoint T B →
      (X.boundaryCard T : ℝ) < γ * T.card →
      ∃ W : Finset X.vertex,
        ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3 ∧
        (X.boundaryCard W : ℝ) < α * T.card)
    (i : ℕ) :
    (assignedAt B γ α replace (i + 1)).1 =
      (assignedAt B γ α replace i).1 ∪
        nextPiece B (assignedAt B γ α replace i).1 γ α
          (assignedAt B γ α replace i).2 replace := rfl

theorem assignedAt_mono_step
    (B : Finset X.vertex) (γ α : ℝ)
    (replace : ∀ T : Finset X.vertex, T.Nonempty → Disjoint T B →
      (X.boundaryCard T : ℝ) < γ * T.card →
      ∃ W : Finset X.vertex,
        ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3 ∧
        (X.boundaryCard W : ℝ) < α * T.card)
    (i : ℕ) :
    (assignedAt B γ α replace i).1 ⊆
      (assignedAt B γ α replace (i + 1)).1 := by
  rw [assignedAt_succ]
  exact Finset.subset_union_left

theorem nextPiece_disjoint_assigned
    (B : Finset X.vertex) (γ α : ℝ)
    (replace : ∀ T : Finset X.vertex, T.Nonempty → Disjoint T B →
      (X.boundaryCard T : ℝ) < γ * T.card →
      ∃ W : Finset X.vertex,
        ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3 ∧
        (X.boundaryCard W : ℝ) < α * T.card)
    (i : ℕ) :
    Disjoint (assignedAt B γ α replace i).1
      (nextPiece B (assignedAt B γ α replace i).1 γ α
        (assignedAt B γ α replace i).2 replace) := by
  apply Finset.disjoint_left.mpr
  intro x hxA hxP
  have hxrest := nextPiece_subset_remainder B
    (assignedAt B γ α replace i).1 γ α
    (assignedAt B γ α replace i).2 replace hxP
  exact (Finset.mem_sdiff.mp hxrest).2 hxA

theorem assignedAt_card_succ
    (B : Finset X.vertex) (γ α : ℝ)
    (replace : ∀ T : Finset X.vertex, T.Nonempty → Disjoint T B →
      (X.boundaryCard T : ℝ) < γ * T.card →
      ∃ W : Finset X.vertex,
        ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3 ∧
        (X.boundaryCard W : ℝ) < α * T.card)
    (i : ℕ) :
    (assignedAt B γ α replace (i + 1)).1.card =
      (assignedAt B γ α replace i).1.card +
        (nextPiece B (assignedAt B γ α replace i).1 γ α
          (assignedAt B γ α replace i).2 replace).card := by
  rw [assignedAt_succ]
  exact Finset.card_union_of_disjoint
    (nextPiece_disjoint_assigned B γ α replace i)

theorem assignedAt_sdiff_eq_nextPiece
    (B : Finset X.vertex) (γ α : ℝ)
    (replace : ∀ T : Finset X.vertex, T.Nonempty → Disjoint T B →
      (X.boundaryCard T : ℝ) < γ * T.card →
      ∃ W : Finset X.vertex,
        ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3 ∧
        (X.boundaryCard W : ℝ) < α * T.card)
    (i : ℕ) :
    (assignedAt B γ α replace (i + 1)).1 \
        (assignedAt B γ α replace i).1 =
      nextPiece B (assignedAt B γ α replace i).1 γ α
        (assignedAt B γ α replace i).2 replace := by
  rw [assignedAt_succ]
  ext x
  constructor
  · intro hx
    have hx' := Finset.mem_sdiff.mp hx
    rcases Finset.mem_union.mp hx'.1 with hxA | hxP
    · exact False.elim (hx'.2 hxA)
    · exact hxP
  · intro hxP
    have hrest := nextPiece_subset_remainder B
      (assignedAt B γ α replace i).1 γ α
      (assignedAt B γ α replace i).2 replace hxP
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_union_right _ hxP, (Finset.mem_sdiff.mp hrest).2⟩

theorem base_card_add_sum_nextPiece
    (B : Finset X.vertex) (γ α : ℝ)
    (replace : ∀ T : Finset X.vertex, T.Nonempty → Disjoint T B →
      (X.boundaryCard T : ℝ) < γ * T.card →
      ∃ W : Finset X.vertex,
        ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3 ∧
        (X.boundaryCard W : ℝ) < α * T.card) :
    ∀ m : ℕ,
      B.card + ∑ i ∈ Finset.range m,
        (nextPiece B (assignedAt B γ α replace i).1 γ α
          (assignedAt B γ α replace i).2 replace).card =
        (assignedAt B γ α replace m).1.card := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, assignedAt_card_succ]
      omega

theorem sum_nextPiece_card_le_vertices
    (B : Finset X.vertex) (γ α : ℝ)
    (replace : ∀ T : Finset X.vertex, T.Nonempty → Disjoint T B →
      (X.boundaryCard T : ℝ) < γ * T.card →
      ∃ W : Finset X.vertex,
        ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3 ∧
        (X.boundaryCard W : ℝ) < α * T.card)
    (m : ℕ) :
    ∑ i ∈ Finset.range m,
      (nextPiece B (assignedAt B γ α replace i).1 γ α
        (assignedAt B γ α replace i).2 replace).card ≤
      Fintype.card X.vertex := by
  have hsum := base_card_add_sum_nextPiece B γ α replace m
  have hcard := Finset.card_le_univ (assignedAt B γ α replace m).1
  omega

theorem assignedAt_card_strict_of_ne_univ
    (B : Finset X.vertex) (γ α : ℝ)
    (replace : ∀ T : Finset X.vertex, T.Nonempty → Disjoint T B →
      (X.boundaryCard T : ℝ) < γ * T.card →
      ∃ W : Finset X.vertex,
        ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3 ∧
        (X.boundaryCard W : ℝ) < α * T.card)
    (i : ℕ) (hne : (assignedAt B γ α replace i).1 ≠ Finset.univ) :
    (assignedAt B γ α replace i).1.card <
      (assignedAt B γ α replace (i + 1)).1.card := by
  let A := (assignedAt B γ α replace i).1
  let P := nextPiece B A γ α (assignedAt B γ α replace i).2 replace
  have hP : P.Nonempty := nextPiece_nonempty_of_ne_univ B A γ α
    (assignedAt B γ α replace i).2 replace hne
  have hPA : P ⊆ Finset.univ \ A :=
    nextPiece_subset_remainder B A γ α
      (assignedAt B γ α replace i).2 replace
  have hdisj : Disjoint A P := by
    apply Finset.disjoint_left.mpr
    intro x hxA hxP
    exact (Finset.mem_sdiff.mp (hPA hxP)).2 hxA
  rw [assignedAt_succ, Finset.card_union_of_disjoint hdisj]
  exact Nat.lt_add_of_pos_right (Finset.card_pos.mpr hP)

/-- After at most the number of vertices many steps, every vertex has been
assigned. -/
theorem assignedAt_card_lower
    (B : Finset X.vertex) (γ α : ℝ)
    (replace : ∀ T : Finset X.vertex, T.Nonempty → Disjoint T B →
      (X.boundaryCard T : ℝ) < γ * T.card →
      ∃ W : Finset X.vertex,
        ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3 ∧
        (X.boundaryCard W : ℝ) < α * T.card) :
    ∀ i : ℕ, i ≤ Fintype.card X.vertex →
      i ≤ (assignedAt B γ α replace i).1.card := by
  intro i hi
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
      have hi' : i ≤ Fintype.card X.vertex := Nat.le_trans (Nat.le_succ i) hi
      have ih' := ih hi'
      by_cases hfull : (assignedAt B γ α replace i).1 = Finset.univ
      · have hmono := Finset.card_le_card
          (assignedAt_mono_step B γ α replace i)
        have hcard : (assignedAt B γ α replace i).1.card =
            Fintype.card X.vertex := by rw [hfull, Finset.card_univ]
        omega
      · have hstrict := assignedAt_card_strict_of_ne_univ
          B γ α replace i hfull
        omega

theorem assignedAt_card_vertices_eq_univ
    (B : Finset X.vertex) (γ α : ℝ)
    (replace : ∀ T : Finset X.vertex, T.Nonempty → Disjoint T B →
      (X.boundaryCard T : ℝ) < γ * T.card →
      ∃ W : Finset X.vertex,
        ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3 ∧
        (X.boundaryCard W : ℝ) < α * T.card) :
    (assignedAt B γ α replace (Fintype.card X.vertex)).1 = Finset.univ := by
  apply Finset.eq_univ_of_card
  exact le_antisymm (Finset.card_le_univ _)
    (assignedAt_card_lower B γ α replace _ le_rfl)

theorem assignedAt_mono
    (B : Finset X.vertex) (γ α : ℝ)
    (replace : ∀ T : Finset X.vertex, T.Nonempty → Disjoint T B →
      (X.boundaryCard T : ℝ) < γ * T.card →
      ∃ W : Finset X.vertex,
        ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3 ∧
        (X.boundaryCard W : ℝ) < α * T.card)
    {i j : ℕ} (hij : i ≤ j) :
    (assignedAt B γ α replace i).1 ⊆
      (assignedAt B γ α replace j).1 := by
  induction j generalizing i with
  | zero =>
      have hi : i = 0 := Nat.eq_zero_of_le_zero hij
      subst i
      exact Finset.Subset.rfl
  | succ j ih =>
      by_cases heq : i = j + 1
      · subst i
        exact Finset.Subset.rfl
      · have hij' : i ≤ j := by omega
        exact (ih hij').trans (assignedAt_mono_step B γ α replace j)

/-- Every vertex is assigned by the terminal finite stage. -/
theorem exists_mem_assignedAt
    (B : Finset X.vertex) (γ α : ℝ)
    (replace : ∀ T : Finset X.vertex, T.Nonempty → Disjoint T B →
      (X.boundaryCard T : ℝ) < γ * T.card →
      ∃ W : Finset X.vertex,
        ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3 ∧
        (X.boundaryCard W : ℝ) < α * T.card)
    (y : X.vertex) :
    ∃ i : ℕ, y ∈ (assignedAt B γ α replace i).1 :=
  ⟨Fintype.card X.vertex, by
    rw [assignedAt_card_vertices_eq_univ B γ α replace]
    exact Finset.mem_univ y⟩

/-- First stage at which a vertex is assigned. -/
noncomputable def entryTime
    (B : Finset X.vertex) (γ α : ℝ)
    (replace : ∀ T : Finset X.vertex, T.Nonempty → Disjoint T B →
      (X.boundaryCard T : ℝ) < γ * T.card →
      ∃ W : Finset X.vertex,
        ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3 ∧
        (X.boundaryCard W : ℝ) < α * T.card)
    (y : X.vertex) : ℕ :=
  Nat.find (exists_mem_assignedAt B γ α replace y)

theorem entryTime_mem
    (B : Finset X.vertex) (γ α : ℝ)
    (replace : ∀ T : Finset X.vertex, T.Nonempty → Disjoint T B →
      (X.boundaryCard T : ℝ) < γ * T.card →
      ∃ W : Finset X.vertex,
        ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3 ∧
        (X.boundaryCard W : ℝ) < α * T.card)
    (y : X.vertex) :
    y ∈ (assignedAt B γ α replace (entryTime B γ α replace y)).1 := by
  unfold entryTime
  exact Nat.find_spec (exists_mem_assignedAt B γ α replace y)

theorem entryTime_not_mem_of_lt
    (B : Finset X.vertex) (γ α : ℝ)
    (replace : ∀ T : Finset X.vertex, T.Nonempty → Disjoint T B →
      (X.boundaryCard T : ℝ) < γ * T.card →
      ∃ W : Finset X.vertex,
        ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3 ∧
        (X.boundaryCard W : ℝ) < α * T.card)
    (y : X.vertex) {i : ℕ} (hi : i < entryTime B γ α replace y) :
    y ∉ (assignedAt B γ α replace i).1 := by
  unfold entryTime at hi
  exact Nat.find_min (exists_mem_assignedAt B γ α replace y) hi

theorem mem_assignedAt_iff_entryTime_le
    (B : Finset X.vertex) (γ α : ℝ)
    (replace : ∀ T : Finset X.vertex, T.Nonempty → Disjoint T B →
      (X.boundaryCard T : ℝ) < γ * T.card →
      ∃ W : Finset X.vertex,
        ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3 ∧
        (X.boundaryCard W : ℝ) < α * T.card)
    (y : X.vertex) (i : ℕ) :
    y ∈ (assignedAt B γ α replace i).1 ↔
      entryTime B γ α replace y ≤ i := by
  constructor
  · intro hy
    unfold entryTime
    exact Nat.find_min' (exists_mem_assignedAt B γ α replace y) hy
  · intro hle
    exact assignedAt_mono B γ α replace hle
      (entryTime_mem B γ α replace y)

theorem entryTime_le_card
    (B : Finset X.vertex) (γ α : ℝ)
    (replace : ∀ T : Finset X.vertex, T.Nonempty → Disjoint T B →
      (X.boundaryCard T : ℝ) < γ * T.card →
      ∃ W : Finset X.vertex,
        ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3 ∧
        (X.boundaryCard W : ℝ) < α * T.card)
    (y : X.vertex) :
    entryTime B γ α replace y ≤ Fintype.card X.vertex := by
  unfold entryTime
  apply Nat.find_min' (exists_mem_assignedAt B γ α replace y)
  rw [assignedAt_card_vertices_eq_univ B γ α replace]
  exact Finset.mem_univ y

theorem entryTime_eq_zero_iff
    (B : Finset X.vertex) (γ α : ℝ)
    (replace : ∀ T : Finset X.vertex, T.Nonempty → Disjoint T B →
      (X.boundaryCard T : ℝ) < γ * T.card →
      ∃ W : Finset X.vertex,
        ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3 ∧
        (X.boundaryCard W : ℝ) < α * T.card)
    (y : X.vertex) :
    entryTime B γ α replace y = 0 ↔ y ∈ B := by
  constructor
  · intro hzero
    have hmem := entryTime_mem B γ α replace y
    simpa [hzero] using hmem
  · intro hy
    have hle : entryTime B γ α replace y ≤ 0 := by
      unfold entryTime
      apply Nat.find_min' (exists_mem_assignedAt B γ α replace y)
      simpa using hy
    omega

/-- Exceptional vertices receive singleton labels; every other vertex is
labelled by the first genuine recursive piece containing it. -/
noncomputable def partitionLabel
    (B : Finset X.vertex) (γ α : ℝ)
    (replace : ∀ T : Finset X.vertex, T.Nonempty → Disjoint T B →
      (X.boundaryCard T : ℝ) < γ * T.card →
      ∃ W : Finset X.vertex,
        ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3 ∧
        (X.boundaryCard W : ℝ) < α * T.card)
    (y : X.vertex) : X.vertex ⊕ ℕ :=
  if y ∈ B then Sum.inl y else Sum.inr (entryTime B γ α replace y)

/-- The finite block structure produced by the recursion. -/
noncomputable def blockStructure
    (B : Finset X.vertex) (γ α : ℝ)
    (replace : ∀ T : Finset X.vertex, T.Nonempty → Disjoint T B →
      (X.boundaryCard T : ℝ) < γ * T.card →
      ∃ W : Finset X.vertex,
        ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3 ∧
        (X.boundaryCard W : ℝ) < α * T.card) : BlockStructure X.vertex where
  block y := Finset.univ.filter fun z ↦
    partitionLabel B γ α replace z = partitionLabel B γ α replace y
  self_mem y := by simp
  eq_of_mem x y hy := by
    have hlabel : partitionLabel B γ α replace y =
        partitionLabel B γ α replace x := by simpa using hy
    ext z
    simp [hlabel]

theorem blockStructure_block_eq_iff_label_eq
    (B : Finset X.vertex) (γ α : ℝ)
    (replace : ∀ T : Finset X.vertex, T.Nonempty → Disjoint T B →
      (X.boundaryCard T : ℝ) < γ * T.card →
      ∃ W : Finset X.vertex,
        ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3 ∧
        (X.boundaryCard W : ℝ) < α * T.card)
    (x y : X.vertex) :
    (blockStructure B γ α replace).block x =
        (blockStructure B γ α replace).block y ↔
      partitionLabel B γ α replace x = partitionLabel B γ α replace y := by
  constructor
  · intro hblocks
    have hy : y ∈ (blockStructure B γ α replace).block x := by
      rw [hblocks]
      exact (blockStructure B γ α replace).self_mem y
    have hlabel : partitionLabel B γ α replace y =
        partitionLabel B γ α replace x := by
      simpa [blockStructure] using hy
    exact hlabel.symm
  · intro hlabel
    ext z
    simp [blockStructure, hlabel]

theorem blockStructure_block_of_mem_base
    (B : Finset X.vertex) (γ α : ℝ)
    (replace : ∀ T : Finset X.vertex, T.Nonempty → Disjoint T B →
      (X.boundaryCard T : ℝ) < γ * T.card →
      ∃ W : Finset X.vertex,
        ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3 ∧
        (X.boundaryCard W : ℝ) < α * T.card)
    {y : X.vertex} (hy : y ∈ B) :
    (blockStructure B γ α replace).block y = {y} := by
  classical
  ext z
  simp only [blockStructure, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · intro hlabel
    by_cases hz : z ∈ B
    · simpa [partitionLabel, hz, hy] using hlabel
    · simp [partitionLabel, hz, hy] at hlabel
  · intro hzy
    subst z
    rfl

theorem entryTime_eq_succ_iff_mem_piece
    (B : Finset X.vertex) (γ α : ℝ)
    (replace : ∀ T : Finset X.vertex, T.Nonempty → Disjoint T B →
      (X.boundaryCard T : ℝ) < γ * T.card →
      ∃ W : Finset X.vertex,
        ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3 ∧
        (X.boundaryCard W : ℝ) < α * T.card)
    {y : X.vertex} (hy : y ∉ B) (i : ℕ) :
    entryTime B γ α replace y = i + 1 ↔
      y ∈ (assignedAt B γ α replace (i + 1)).1 \
        (assignedAt B γ α replace i).1 := by
  constructor
  · intro hentry
    apply Finset.mem_sdiff.mpr
    constructor
    · simpa [hentry] using entryTime_mem B γ α replace y
    · exact entryTime_not_mem_of_lt B γ α replace y (by omega)
  · intro hyPiece
    have hymem := (Finset.mem_sdiff.mp hyPiece).1
    have hynot := (Finset.mem_sdiff.mp hyPiece).2
    have hle : entryTime B γ α replace y ≤ i + 1 := by
      unfold entryTime
      exact Nat.find_min' _ hymem
    have hpos : 0 < entryTime B γ α replace y := by
      have := (entryTime_eq_zero_iff B γ α replace y).not.mpr hy
      omega
    by_contra hne
    have hsmall : entryTime B γ α replace y ≤ i := by omega
    have hentrymem := entryTime_mem B γ α replace y
    exact hynot (assignedAt_mono B γ α replace hsmall hentrymem)

theorem blockStructure_block_of_entryTime_succ
    (B : Finset X.vertex) (γ α : ℝ)
    (replace : ∀ T : Finset X.vertex, T.Nonempty → Disjoint T B →
      (X.boundaryCard T : ℝ) < γ * T.card →
      ∃ W : Finset X.vertex,
        ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3 ∧
        (X.boundaryCard W : ℝ) < α * T.card)
    {y : X.vertex} (hy : y ∉ B) {i : ℕ}
    (hentry : entryTime B γ α replace y = i + 1) :
    (blockStructure B γ α replace).block y =
      nextPiece B (assignedAt B γ α replace i).1 γ α
        (assignedAt B γ α replace i).2 replace := by
  classical
  let A := (assignedAt B γ α replace i).1
  let P := nextPiece B A γ α (assignedAt B γ α replace i).2 replace
  have hPsub : P ⊆ Finset.univ \ A :=
    nextPiece_subset_remainder B A γ α
      (assignedAt B γ α replace i).2 replace
  have hpiece :
      (assignedAt B γ α replace (i + 1)).1 \ A = P := by
    rw [assignedAt_succ]
    ext z
    constructor
    · intro hz
      have hz' := Finset.mem_sdiff.mp hz
      rcases Finset.mem_union.mp hz'.1 with hzA | hzP
      · exact False.elim (hz'.2 hzA)
      · exact hzP
    · intro hzP
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_union_right A hzP, (Finset.mem_sdiff.mp (hPsub hzP)).2⟩
  ext z
  simp only [blockStructure, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hz : z ∈ B
  · rw [partitionLabel, if_pos hz, partitionLabel, if_neg hy]
    change (Sum.inl z = Sum.inr (entryTime B γ α replace y) ↔ z ∈ P)
    constructor
    · intro h
      cases h
    · intro hzP
      have hzrest := hPsub hzP
      exact False.elim ((Finset.mem_sdiff.mp hzrest).2
        ((assignedAt B γ α replace i).2 hz))
  · simp only [partitionLabel, hz, hy, if_false, Sum.inr.injEq]
    rw [hentry, entryTime_eq_succ_iff_mem_piece B γ α replace hz i]
    simpa [A, P] using (Finset.ext_iff.mp hpiece z)

/-- Every nonexceptional recursive block has the uniform global cut lower
bound selected at the beginning of the construction. -/
theorem blockStructure_block_expands
    (B : Finset X.vertex) (γ α : ℝ)
    (replace : ∀ T : Finset X.vertex, T.Nonempty → Disjoint T B →
      (X.boundaryCard T : ℝ) < γ * T.card →
      ∃ W : Finset X.vertex,
        ((W ∆ T).card : ℝ) < (T.card : ℝ) / 3 ∧
        (X.boundaryCard W : ℝ) < α * T.card)
    (y : X.vertex) :
    ∀ U : Finset X.vertex,
      U ⊆ (blockStructure B γ α replace).block y → U.Nonempty →
      2 * U.card ≤ ((blockStructure B γ α replace).block y).card →
      γ * U.card ≤ X.boundaryCard U := by
  intro U hU hUne hhalf
  by_cases hy : y ∈ B
  · rw [blockStructure_block_of_mem_base B γ α replace hy] at hU hhalf
    simp only [Finset.card_singleton] at hhalf
    have hcard : U.card ≤ 1 := by
      simpa using Finset.card_le_card hU
    have hpos : 0 < U.card := Finset.card_pos.mpr hUne
    omega
  · have htime : 0 < entryTime B γ α replace y := by
      have := (entryTime_eq_zero_iff B γ α replace y).not.mpr hy
      omega
    obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt htime)
    rw [blockStructure_block_of_entryTime_succ B γ α replace hy hi] at hU hhalf
    exact nextPiece_expands B (assignedAt B γ α replace i).1 γ α
      (assignedAt B γ α replace i).2 replace U hU hUne hhalf

end KunPartition
end NonsoficGroupsExist
