import NonsoficGroupsExist.Sofic.NearActionFolner
import NonsoficGroupsExist.Matching.Localization

/-!
# Finite sofic models from Pestov near actions

This file completes the reverse direction of the Elek--Szabó
characterization.  The Tarski--Hall theorem supplies a finite set with small
boundary, chosen outside every near-action defect relevant to a prescribed
finite multiplication table.  Each restricted partial permutation is then
completed to a permutation of that finite set.
-/

namespace NonsoficGroupsExist

open Set
open scoped BigOperators Pointwise

universe u

namespace EssentiallyFreeNearAction

variable {G : Type u} [Group G] {X : Type}

noncomputable section

local instance instDecidableEqG : DecidableEq G := Classical.decEq G
local instance instDecidableEqX : DecidableEq X := Classical.decEq X

/-- Failure set of the near identity law. -/
def identityError (A : EssentiallyFreeNearAction G X) : Set X :=
  {x | A.act 1 x ≠ x}

/-- Failure set of a prescribed multiplication law. -/
def multiplicationError (A : EssentiallyFreeNearAction G X) (g h : G) : Set X :=
  {x | A.act (g * h) x ≠ A.act g (A.act h x)}

/-- Fixed points of a prescribed representative. -/
def fixedPoints (A : EssentiallyFreeNearAction G X) (g : G) : Set X :=
  {x | A.act g x = x}

theorem measure_identityError (A : EssentiallyFreeNearAction G X) :
    A.measure (A.identityError) = 0 := A.identity_ae

theorem measure_multiplicationError (A : EssentiallyFreeNearAction G X) (g h : G) :
    A.measure (A.multiplicationError g h) = 0 := A.multiplicative_ae g h

theorem measure_fixedPoints (A : EssentiallyFreeNearAction G X) {g : G} (hg : g ≠ 1) :
    A.measure (A.fixedPoints g) = 0 := A.essentially_free g hg

/-- Ordered pairs of distinct elements of a finite test set. -/
def distinctPairs (F : Finset G) : Finset (G × G) :=
  (F ×ˢ F).filter fun z ↦ z.1 ≠ z.2

/-- The finite union of all null defects needed for a model on `F`.

Besides multiplication defects for pairs in `F`, it includes the three
defects which turn equality of the representatives of distinct `g,h` into a
fixed point of `h⁻¹g`.
-/
def modelNullSet (A : EssentiallyFreeNearAction G X) (F : Finset G) : Set X :=
  A.identityError ∪
    (⋃ z ∈ F ×ˢ F, A.multiplicationError z.1 z.2) ∪
    (⋃ z ∈ distinctPairs F,
      A.multiplicationError z.2⁻¹ z.1 ∪
      A.multiplicationError z.2⁻¹ z.2 ∪ A.fixedPoints (z.2⁻¹ * z.1))

theorem measure_modelNullSet (A : EssentiallyFreeNearAction G X) (F : Finset G) :
    A.measure (A.modelNullSet F) = 0 := by
  classical
  have hmul : A.measure (⋃ z ∈ F ×ˢ F, A.multiplicationError z.1 z.2) = 0 := by
    apply A.measure.biUnion_finset_eq_zero
    intro z hz
    exact A.measure_multiplicationError z.1 z.2
  have hsepPiece : ∀ z ∈ distinctPairs F,
      A.measure (A.multiplicationError z.2⁻¹ z.1 ∪
        A.multiplicationError z.2⁻¹ z.2 ∪ A.fixedPoints (z.2⁻¹ * z.1)) = 0 := by
    intro z hz
    have hne : z.1 ≠ z.2 := by
      change z ∈ (F ×ˢ F).filter (fun z ↦ z.1 ≠ z.2) at hz
      exact (Finset.mem_filter.mp hz).2
    have hprod : z.2⁻¹ * z.1 ≠ 1 := by
      intro heq
      apply hne
      have := congrArg (fun q : G ↦ z.2 * q) heq
      simpa [mul_assoc] using this
    exact A.measure.union_eq_zero
      (A.measure.union_eq_zero
        (A.measure_multiplicationError z.2⁻¹ z.1)
        (A.measure_multiplicationError z.2⁻¹ z.2))
      (A.measure_fixedPoints hprod)
  have hsep : A.measure (⋃ z ∈ distinctPairs F,
      A.multiplicationError z.2⁻¹ z.1 ∪
      A.multiplicationError z.2⁻¹ z.2 ∪ A.fixedPoints (z.2⁻¹ * z.1)) = 0 := by
    exact A.measure.biUnion_finset_eq_zero (distinctPairs F) _ hsepPiece
  exact A.measure.union_eq_zero
    (A.measure.union_eq_zero A.measure_identityError hmul) hsep

theorem multiplicationError_subset_modelNullSet
    (A : EssentiallyFreeNearAction G X) {F : Finset G}
    {g h : G} (hg : g ∈ F) (hh : h ∈ F) :
    A.multiplicationError g h ⊆ A.modelNullSet F := by
  intro x hx
  change (x ∈ A.identityError ∨
      x ∈ ⋃ z ∈ F ×ˢ F, A.multiplicationError z.1 z.2) ∨
    x ∈ ⋃ z ∈ distinctPairs F,
      A.multiplicationError z.2⁻¹ z.1 ∪
      A.multiplicationError z.2⁻¹ z.2 ∪ A.fixedPoints (z.2⁻¹ * z.1)
  apply Or.inl
  apply Or.inr
  apply Set.mem_iUnion.mpr
  refine ⟨(g, h), Set.mem_iUnion.mpr ⟨Finset.mem_product.mpr ⟨hg, hh⟩, ?_⟩⟩
  exact hx

theorem separation_good
    (A : EssentiallyFreeNearAction G X) {F : Finset G}
    {g h : G} (hg : g ∈ F) (hh : h ∈ F) (hgh : g ≠ h)
    {x : X} (hx : x ∉ A.modelNullSet F) : A.act g x ≠ A.act h x := by
  intro heq
  let z : G × G := (g, h)
  have hz : z ∈ distinctPairs F := by
    change z ∈ (F ×ˢ F).filter (fun z ↦ z.1 ≠ z.2)
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hg, hh⟩, hgh⟩
  have hnotSep : x ∉ A.multiplicationError h⁻¹ g ∪
      A.multiplicationError h⁻¹ h ∪ A.fixedPoints (h⁻¹ * g) := by
    intro hmem
    apply hx
    change (x ∈ A.identityError ∨
        x ∈ ⋃ z ∈ F ×ˢ F, A.multiplicationError z.1 z.2) ∨
      x ∈ ⋃ z ∈ distinctPairs F,
        A.multiplicationError z.2⁻¹ z.1 ∪
        A.multiplicationError z.2⁻¹ z.2 ∪ A.fixedPoints (z.2⁻¹ * z.1)
    apply Or.inr
    apply Set.mem_iUnion.mpr
    refine ⟨z, Set.mem_iUnion.mpr ⟨hz, ?_⟩⟩
    exact hmem
  have hnot1 : x ∉ A.identityError := by
    intro hmem
    apply hx
    change (x ∈ A.identityError ∨
        x ∈ ⋃ z ∈ F ×ˢ F, A.multiplicationError z.1 z.2) ∨
      x ∈ ⋃ z ∈ distinctPairs F,
        A.multiplicationError z.2⁻¹ z.1 ∪
        A.multiplicationError z.2⁻¹ z.2 ∪ A.fixedPoints (z.2⁻¹ * z.1)
    exact Or.inl (Or.inl hmem)
  have hmulG : A.act (h⁻¹ * g) x = A.act h⁻¹ (A.act g x) := by
    exact not_ne_iff.mp (fun hmem ↦ hnotSep (Or.inl (Or.inl hmem)))
  have hmulH : A.act (h⁻¹ * h) x = A.act h⁻¹ (A.act h x) := by
    exact not_ne_iff.mp (fun hmem ↦ hnotSep (Or.inl (Or.inr hmem)))
  have hone : A.act 1 x = x := not_ne_iff.mp hnot1
  have hfixed : A.act (h⁻¹ * g) x = x := by
    calc
      A.act (h⁻¹ * g) x = A.act h⁻¹ (A.act g x) := hmulG
      _ = A.act h⁻¹ (A.act h x) := congrArg (A.act h⁻¹) heq
      _ = A.act (h⁻¹ * h) x := hmulH.symm
      _ = A.act 1 x := by simp
      _ = x := hone
  apply hnotSep
  exact Or.inr hfixed

/-! ## Completion on a finite subset -/

/-- A fixed completion of the restriction of an ambient permutation to `D`. -/
noncomputable def completedPerm (D : Finset X) (p : Equiv.Perm X) : Equiv.Perm D :=
  Classical.choose (Localization.exists_completion D p)

theorem completedPerm_agrees (D : Finset X) (p : Equiv.Perm X) (x : D)
    (hx : p (x : X) ∈ D) :
    (completedPerm D p x : X) = p x :=
  Classical.choose_spec (Localization.exists_completion D p) x hx

/-- Points where the chosen completion differs from the ambient map. -/
noncomputable def completionError (D : Finset X) (p : Equiv.Perm X) : Finset D :=
  Finset.univ.filter fun x : D ↦ (completedPerm D p x : X) ≠ p x

/-- Sources whose image under the ambient permutation leaves `D`. -/
noncomputable def sourceBoundary (D : Finset X) (p : Equiv.Perm X) : Finset D :=
  Finset.univ.filter fun x : D ↦ p (x : X) ∉ D

theorem completionError_subset_sourceBoundary (D : Finset X) (p : Equiv.Perm X) :
    completionError D p ⊆ sourceBoundary D p := by
  intro x hx
  simp only [completionError, sourceBoundary, Finset.mem_filter, Finset.mem_univ,
    true_and] at hx ⊢
  intro hin
  exact hx (completedPerm_agrees D p x hin)

theorem card_sourceBoundary_eq_escape (D : Finset X) (p : Equiv.Perm X) :
    (sourceBoundary D p).card = (TarskiHall.escape p D).card := by
  let imageBoundary : Finset X :=
    (sourceBoundary D p).image fun x : D ↦ p (x : X)
  have himage : imageBoundary = TarskiHall.escape p D := by
    ext y
    constructor
    · intro hy
      change y ∈ (sourceBoundary D p).image (fun x : D ↦ p (x : X)) at hy
      obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
      have hxout : p (x : X) ∉ D := by
        simpa [sourceBoundary] using hx
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨x, x.2, hxy⟩,
        hxy ▸ hxout⟩
    · intro hy
      obtain ⟨hyImage, hyOut⟩ := Finset.mem_sdiff.mp hy
      obtain ⟨x, hxD, hxy⟩ := Finset.mem_image.mp hyImage
      let xD : D := ⟨x, hxD⟩
      change y ∈ (sourceBoundary D p).image (fun x : D ↦ p (x : X))
      apply Finset.mem_image.mpr
      refine ⟨xD, ?_, hxy⟩
      simp [sourceBoundary, xD, hxy, hyOut]
  calc
    (sourceBoundary D p).card = imageBoundary.card :=
      (Finset.card_image_of_injective _ (p.injective.comp Subtype.val_injective)).symm
    _ = (TarskiHall.escape p D).card := congrArg Finset.card himage

theorem card_completionError_le_escape (D : Finset X) (p : Equiv.Perm X) :
    (completionError D p).card ≤ (TarskiHall.escape p D).card := by
  rw [← card_sourceBoundary_eq_escape]
  exact Finset.card_le_card (completionError_subset_sourceBoundary D p)

/-! ## Error bookkeeping for the completed maps -/

/-- The finite model carried by a nonempty finite subset. -/
abbrev finsetModel (D : Finset X) : FiniteModel where
  carrier := D
  fintype := inferInstance
  decidableEq := inferInstance

@[simp] theorem card_finsetModel (D : Finset X) :
    Fintype.card (finsetModel D) = D.card := by
  simp [finsetModel]

/-- The completed representative of a group element on `D`. -/
noncomputable def completedAct (A : EssentiallyFreeNearAction G X)
    (D : Finset X) (g : G) : Equiv.Perm D :=
  completedPerm D (A.act g)

/-- Points where a completed action map differs from its ambient representative. -/
noncomputable def disagreement (A : EssentiallyFreeNearAction G X)
    (D : Finset X) (g : G) : Finset D :=
  completionError D (A.act g)

/-- Pullback of an error set by one of the completed permutations. -/
noncomputable def disagreementPreimage (A : EssentiallyFreeNearAction G X)
    (D : Finset X) (g h : G) : Finset D :=
  Finset.univ.filter fun x ↦ completedAct A D h x ∈ disagreement A D g

theorem disagreementPreimage_card (A : EssentiallyFreeNearAction G X)
    (D : Finset X) (g h : G) :
    (disagreementPreimage A D g h).card = (disagreement A D g).card := by
  let p := completedAct A D h
  have himage : disagreementPreimage A D g h = (disagreement A D g).image p.symm := by
    ext x
    simp only [disagreementPreimage, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image]
    constructor
    · intro hx
      exact ⟨p x, hx, p.symm_apply_apply x⟩
    · rintro ⟨y, hy, hxy⟩
      have hyx : y = p x := by
        have := congrArg p hxy
        simpa using this
      rw [← hyx]
      exact hy
  rw [himage, Finset.card_image_of_injective _ p.symm.injective]

/-- Multiplication failures after completing all three partial maps. -/
noncomputable def completedMultiplicationBad
    (A : EssentiallyFreeNearAction G X) (D : Finset X) (g h : G) : Finset D :=
  Finset.univ.filter fun x ↦
    completedAct A D (g * h) x ≠ completedAct A D g (completedAct A D h x)

theorem completedMultiplicationBad_subset
    (A : EssentiallyFreeNearAction G X) {F : Finset G} (D : Finset X)
    (hgood : ∀ x : D, (x : X) ∉ A.modelNullSet F)
    {g h : G} (hg : g ∈ F) (hh : h ∈ F) :
    completedMultiplicationBad A D g h ⊆
      disagreement A D (g * h) ∪ disagreement A D h ∪
        disagreementPreimage A D g h := by
  intro x hx
  simp only [completedMultiplicationBad, disagreement, disagreementPreimage,
    completionError, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union] at hx ⊢
  by_cases hgh : (completedAct A D (g * h) x : X) ≠ A.act (g * h) x
  · exact Or.inl (Or.inl hgh)
  by_cases hhd : (completedAct A D h x : X) ≠ A.act h x
  · exact Or.inl (Or.inr hhd)
  by_cases hgd : (completedAct A D g (completedAct A D h x) : X) ≠
      A.act g (completedAct A D h x : X)
  · exact Or.inr hgd
  exfalso
  apply hx
  apply Subtype.ext
  rw [not_ne_iff.mp hgh, not_ne_iff.mp hgd, not_ne_iff.mp hhd]
  have hmul : A.act (g * h) (x : X) = A.act g (A.act h x) := by
    apply not_ne_iff.mp
    intro herr
    exact hgood x (multiplicationError_subset_modelNullSet A hg hh herr)
  exact hmul

theorem completedMultiplicationBad_card_le
    (A : EssentiallyFreeNearAction G X) {F : Finset G} (D : Finset X)
    (hgood : ∀ x : D, (x : X) ∉ A.modelNullSet F)
    {g h : G} (hg : g ∈ F) (hh : h ∈ F) :
    (completedMultiplicationBad A D g h).card ≤
      (disagreement A D (g * h)).card + (disagreement A D h).card +
        (disagreement A D g).card := by
  have hs := Finset.card_le_card (completedMultiplicationBad_subset A D hgood hg hh)
  have h1 := Finset.card_union_le (disagreement A D (g * h)) (disagreement A D h)
  have h2 := Finset.card_union_le
    (disagreement A D (g * h) ∪ disagreement A D h) (disagreementPreimage A D g h)
  rw [disagreementPreimage_card] at h2
  omega

/-- Agreements between completed maps representing distinct elements. -/
noncomputable def completedAgreement
    (A : EssentiallyFreeNearAction G X) (D : Finset X) (g h : G) : Finset D :=
  Finset.univ.filter fun x ↦ completedAct A D g x = completedAct A D h x

theorem completedAgreement_subset
    (A : EssentiallyFreeNearAction G X) {F : Finset G} (D : Finset X)
    (hgood : ∀ x : D, (x : X) ∉ A.modelNullSet F)
    {g h : G} (hg : g ∈ F) (hh : h ∈ F) (hgh : g ≠ h) :
    completedAgreement A D g h ⊆ disagreement A D g ∪ disagreement A D h := by
  intro x hx
  simp only [completedAgreement, disagreement, completionError, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_union] at hx ⊢
  by_cases hgd : (completedAct A D g x : X) ≠ A.act g x
  · exact Or.inl hgd
  by_cases hhd : (completedAct A D h x : X) ≠ A.act h x
  · exact Or.inr hhd
  exfalso
  have hamb : A.act g (x : X) = A.act h x := by
    rw [← not_ne_iff.mp hgd, ← not_ne_iff.mp hhd]
    exact congrArg Subtype.val hx
  exact (A.separation_good hg hh hgh (hgood x)) hamb

theorem completedAgreement_card_le
    (A : EssentiallyFreeNearAction G X) {F : Finset G} (D : Finset X)
    (hgood : ∀ x : D, (x : X) ∉ A.modelNullSet F)
    {g h : G} (hg : g ∈ F) (hh : h ∈ F) (hgh : g ≠ h) :
    (completedAgreement A D g h).card ≤
      (disagreement A D g).card + (disagreement A D h).card :=
  (Finset.card_le_card (completedAgreement_subset A D hgood hg hh hgh)).trans
    (Finset.card_union_le _ _)

theorem hammingDistance_completed_mul
    (A : EssentiallyFreeNearAction G X) (D : Finset X) (g h : G) :
    hammingDistance (finsetModel D) (completedAct A D (g * h))
        (completedAct A D g * completedAct A D h) =
      ((completedMultiplicationBad A D g h).card : ℝ) / D.card := by
  unfold hammingDistance hammingDisagreement completedMultiplicationBad
  rw [card_finsetModel]
  congr 2

theorem hammingDistance_completed_pair
    (A : EssentiallyFreeNearAction G X) (D : Finset X) (hDne : D.Nonempty)
    (g h : G) :
    hammingDistance (finsetModel D) (completedAct A D g) (completedAct A D h) =
      1 - ((completedAgreement A D g h).card : ℝ) / D.card := by
  unfold hammingDistance hammingDisagreement completedAgreement
  rw [card_finsetModel]
  let moved : Finset D := Finset.univ.filter fun x ↦ completedAct A D g x ≠ completedAct A D h x
  let fixed : Finset D := Finset.univ.filter fun x ↦ completedAct A D g x = completedAct A D h x
  have hpartition : moved.card + fixed.card = D.card := by
    simpa [moved, fixed] using Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset D))
      (p := fun x ↦ completedAct A D g x ≠ completedAct A D h x)
  have hpartitionR : (moved.card : ℝ) + (fixed.card : ℝ) = D.card := by
    exact_mod_cast hpartition
  change (moved.card : ℝ) / D.card = 1 - (fixed.card : ℝ) / D.card
  have hD : D.card ≠ 0 := Nat.ne_of_gt (Finset.card_pos.mpr hDne)
  have hDR : (D.card : ℝ) ≠ 0 := by exact_mod_cast hD
  calc
    (moved.card : ℝ) / D.card =
        ((D.card : ℝ) - fixed.card) / D.card := by
      congr 1
      linarith
    _ = (D.card : ℝ) / D.card - (fixed.card : ℝ) / D.card := by ring
    _ = 1 - (fixed.card : ℝ) / D.card := by rw [div_self hDR]

/-! ## The reverse Elek--Szabó implication -/

/-- An essentially free full-power-set near action supplies every prescribed
finite sofic model. -/
theorem toSoficModel (A : EssentiallyFreeNearAction G X)
    (F : Finset G) (ε : ℝ) (hε : 0 < ε) :
    Nonempty (SoficModel G F ε) := by
  let T : Finset G := tableDomain F
  let P : Finset (Equiv.Perm X) := T.image A.act
  have hP : ∀ p ∈ P, PreservesFullMeasure A.measure p := by
    intro p hp
    change p ∈ T.image A.act at hp
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hp
    exact A.measure_preserving g
  let δ : ℝ := ε / 4
  have hδ : 0 < δ := div_pos hε (by norm_num)
  obtain ⟨D, hDne, hDN, hsmall⟩ :=
    TarskiHall.exists_finite_small_boundary_avoiding_null
      A.measure P hP (A.measure_modelNullSet F) hδ
  have hgood : ∀ x : D, (x : X) ∉ A.modelNullSet F := by
    intro x hxN
    exact Set.disjoint_left.mp hDN x.2 hxN
  have hDposNat : 0 < D.card := Finset.card_pos.mpr hDne
  have hDpos : (0 : ℝ) < D.card := by exact_mod_cast hDposNat
  have hboundary {g : G} (hg : g ∈ T) :
      ((A.disagreement D g).card : ℝ) < δ * D.card := by
    have hleNat := card_completionError_le_escape D (A.act g)
    have hle : ((A.disagreement D g).card : ℝ) ≤
        (TarskiHall.escape (A.act g) D).card := by
      exact_mod_cast hleNat
    have hp : A.act g ∈ P := by
      change A.act g ∈ T.image A.act
      exact Finset.mem_image.mpr ⟨g, hg, rfl⟩
    exact hle.trans_lt (hsmall (A.act g) hp)
  refine ⟨{
    carrier := finsetModel D
    nonempty := by simpa using hDposNat
    map := completedAct A D
    multiplicative := ?_
    separated := ?_ }⟩
  · intro g hg h hh
    have hgT : g ∈ T := by
      change g ∈ tableDomain F
      exact mem_tableDomain_of_mem hg
    have hhT : h ∈ T := by
      change h ∈ tableDomain F
      exact mem_tableDomain_of_mem hh
    have hghT : g * h ∈ T := by
      change g * h ∈ tableDomain F
      exact mul_mem_tableDomain hg hh
    have hbadNat := A.completedMultiplicationBad_card_le D hgood hg hh
    have hbad : ((A.completedMultiplicationBad D g h).card : ℝ) ≤
        (A.disagreement D (g * h)).card + (A.disagreement D h).card +
          (A.disagreement D g).card := by
      exact_mod_cast hbadNat
    have hratio : ((A.completedMultiplicationBad D g h).card : ℝ) / D.card <
        3 * δ := by
      apply (div_lt_iff₀ hDpos).2
      have h₁ := hboundary hghT
      have h₂ := hboundary hhT
      have h₃ := hboundary hgT
      calc
        ((A.completedMultiplicationBad D g h).card : ℝ) ≤
            (A.disagreement D (g * h)).card + (A.disagreement D h).card +
              (A.disagreement D g).card := hbad
        _ < 3 * δ * D.card := by linarith
    rw [A.hammingDistance_completed_mul]
    exact hratio.le.trans (by dsimp [δ]; linarith)
  · intro g hg h hh hgh
    have hgT : g ∈ T := by
      change g ∈ tableDomain F
      exact mem_tableDomain_of_mem hg
    have hhT : h ∈ T := by
      change h ∈ tableDomain F
      exact mem_tableDomain_of_mem hh
    have hagreeNat := A.completedAgreement_card_le D hgood hg hh hgh
    have hagree : ((A.completedAgreement D g h).card : ℝ) ≤
        (A.disagreement D g).card + (A.disagreement D h).card := by
      exact_mod_cast hagreeNat
    have hratio : ((A.completedAgreement D g h).card : ℝ) / D.card < 2 * δ := by
      apply (div_lt_iff₀ hDpos).2
      have h₁ := hboundary hgT
      have h₂ := hboundary hhT
      calc
        ((A.completedAgreement D g h).card : ℝ) ≤
            (A.disagreement D g).card + (A.disagreement D h).card := hagree
        _ < 2 * δ * D.card := by linarith
    rw [A.hammingDistance_completed_pair D hDne]
    have hratioε : ((A.completedAgreement D g h).card : ℝ) / D.card ≤ ε :=
      hratio.le.trans (by dsimp [δ]; linarith)
    linarith

end
end EssentiallyFreeNearAction

/-- **Reverse Elek--Szabó implication.**  A group admitting Pestov's
essentially free near action is sofic.  No countability hypothesis is needed
in this direction. -/
theorem isSofic_of_admitsEssentiallyFreeNearAction
    (G : Type u) [Group G] (hG : AdmitsEssentiallyFreeNearAction G) :
    IsSofic G := by
  obtain ⟨X, ⟨A⟩⟩ := hG
  intro F ε hε
  exact A.toSoficModel F ε hε

/-- **Elek--Szabó characterization (Pestov, Theorem 5.2).**  For a countable
group, soficity is equivalent to admitting an essentially free,
measure-preserving near action on a set carrying a finitely additive
probability measure on its full power set. -/
theorem isSofic_iff_admitsEssentiallyFreeNearAction
    (G : Type u) [Group G] [Countable G] :
    IsSofic G ↔ AdmitsEssentiallyFreeNearAction G := by
  constructor
  · exact admitsEssentiallyFreeNearAction_of_isSofic G
  · exact isSofic_of_admitsEssentiallyFreeNearAction G

end NonsoficGroupsExist
