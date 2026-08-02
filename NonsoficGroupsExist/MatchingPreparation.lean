import NonsoficGroupsExist.GlobalVariation
import NonsoficGroupsExist.SlowThreshold
import NonsoficGroupsExist.FiniteMarkov

/-!
# Preparing the conservative component matching

For the distinguished compressor this file defines the global error density,
chooses a slowly vanishing threshold, and identifies the source components on
which leakage, ambient-component preservation, and both endpoint pinning
estimates hold simultaneously.  The final theorem is the quantitative
symmetric-difference estimate of Proposition `prop:match` for every acceptable
component.
-/

namespace NonsoficGroupsExist

open scoped BigOperators symmDiff

namespace LocalCriterionData

variable {G Γ J : Type} [Group G] [Group Γ] [Group J]
variable (D : LocalCriterionData G Γ J)

noncomputable abbrev distinguishedPerm (n : ℕ) :
    Equiv.Perm (D.approximation.model n) :=
  D.approximation.map n D.setup.distinguished

noncomputable abbrev matchTarget (n : ℕ)
  (B : D.gammaDecomposition.componentIndex n) :
    Finset (D.approximation.model n) :=
  (D.gammaDecomposition.refineBlock (D.gammaDecomposition.blocks n)
    (D.distinguishedPerm n) B).target

noncomputable abbrev matchImage (n : ℕ)
    (B : D.gammaDecomposition.componentIndex n) :
    Finset (D.approximation.model n) :=
  B.block.image (D.distinguishedPerm n)

noncomputable def totalMatchingError (n : ℕ) : ℝ :=
  (∑ y : D.approximation.model n, |D.observable n y - 1 / 2|) +
  (∑ B : D.gammaDecomposition.componentIndex n,
    (D.gammaDecomposition.componentLeakage
      (D.gammaDecomposition.blocks n) (D.distinguishedPerm n) B : ℝ)) +
  ((wordCrossing (D.ambientDecomposition.blocks n)
    (D.distinguishedPerm n)).card : ℝ)

theorem totalMatchingError_nonneg (n : ℕ) : 0 ≤ D.totalMatchingError n := by
  unfold totalMatchingError
  positivity

theorem totalMatchingError_negligible :
    Negligible D.N D.totalMatchingError := by
  have hdev := D.normalizedDeviation_negligible
  have hleak := D.setup.compressorLeakage_negligible D.approximation
    D.gammaDecomposition D.setup.distinguished D.setup.distinguished_mem
  change Negligible D.N (fun n ↦
    ∑ B : D.gammaDecomposition.componentIndex n,
      (D.gammaDecomposition.componentLeakage
        (D.gammaDecomposition.blocks n) (D.distinguishedPerm n) B : ℝ)) at hleak
  have hcross := D.ambientDecomposition.all_almost_invariant
    D.setup.ambientGenerators_symmetric D.setup.ambientGenerators_generate
    D.setup.distinguished
  change Negligible D.N (fun n ↦
    (∑ y : D.approximation.model n, |D.observable n y - 1 / 2|) +
    (∑ B : D.gammaDecomposition.componentIndex n,
      (D.gammaDecomposition.componentLeakage
        (D.gammaDecomposition.blocks n) (D.distinguishedPerm n) B : ℝ)) +
    ((wordCrossing (D.ambientDecomposition.blocks n)
      (D.distinguishedPerm n)).card : ℝ))
  exact Negligible.add (Negligible.add hdev hleak) hcross

noncomputable def matchingErrorDensity (n : ℕ) : ℝ :=
  D.totalMatchingError n / D.N n

theorem matchingErrorDensity_nonneg (n : ℕ) :
    0 ≤ D.matchingErrorDensity n := by
  exact div_nonneg (D.totalMatchingError_nonneg n) (by positivity)

theorem matchingErrorDensity_vanishing :
    Vanishing D.matchingErrorDensity := by
  change Vanishing (fun n ↦ D.totalMatchingError n / D.N n)
  exact D.totalMatchingError_negligible

noncomputable def matchingThreshold (n : ℕ) : ℝ :=
  slowThreshold D.matchingErrorDensity n

theorem matchingThreshold_pos (n : ℕ) : 0 < D.matchingThreshold n :=
  slowThreshold_pos D.matchingErrorDensity n

theorem matchingThreshold_le_one (n : ℕ) : D.matchingThreshold n ≤ 1 := by
  unfold matchingThreshold slowThreshold
  apply (div_le_one (by positivity)).2
  norm_num

theorem matchingThreshold_vanishing : Vanishing D.matchingThreshold :=
  slowThreshold_vanishing D.matchingErrorDensity D.matchingErrorDensity_vanishing

theorem scaledMatchingError_vanishing :
    Vanishing fun n ↦ D.totalMatchingError n / D.matchingThreshold n / D.N n := by
  have h := error_div_slowThreshold_vanishing D.matchingErrorDensity
    D.matchingErrorDensity_nonneg D.matchingErrorDensity_vanishing
  apply Vanishing.congr h
  intro n
  rw [matchingThreshold]
  rw [matchingErrorDensity]
  ring

/-- Bad points inside one source component. -/
noncomputable def localMatchingBad (n : ℕ) (η : ℝ)
    (B : D.gammaDecomposition.componentIndex n) :
    Finset (indexedBlockModel (D.gammaDecomposition.blocks n) B) :=
  Finset.univ.filter fun x ↦
    η < |D.observable n x.1 - 1 / 2| ∨
    η < |D.observable n (D.distinguishedPerm n x.1) - 1 / 2| ∨
    D.distinguishedPerm n x.1 ∉ D.matchTarget n B ∨
    (D.ambientDecomposition.blocks n).block (D.distinguishedPerm n x.1) ≠
      (D.ambientDecomposition.blocks n).block x.1

/-- A source component is acceptable when its total leakage is below the
threshold fraction and at least one point satisfies all pointwise estimates. -/
def ComponentAcceptable (n : ℕ) (η : ℝ)
    (B : D.gammaDecomposition.componentIndex n) : Prop :=
  (D.gammaDecomposition.componentLeakage
      (D.gammaDecomposition.blocks n) (D.distinguishedPerm n) B : ℝ) ≤
      η * B.block.card ∧
    (D.localMatchingBad n η B).card < B.block.card

theorem exists_goodPoint {n : ℕ} {η : ℝ}
    {B : D.gammaDecomposition.componentIndex n}
    (hB : D.ComponentAcceptable n η B) :
    ∃ x : indexedBlockModel (D.gammaDecomposition.blocks n) B,
      |D.observable n x.1 - 1 / 2| ≤ η ∧
      |D.observable n (D.distinguishedPerm n x.1) - 1 / 2| ≤ η ∧
      D.distinguishedPerm n x.1 ∈ D.matchTarget n B ∧
      (D.ambientDecomposition.blocks n).block (D.distinguishedPerm n x.1) =
        (D.ambientDecomposition.blocks n).block x.1 := by
  classical
  have hproper : D.localMatchingBad n η B ⊂ Finset.univ := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, ?_⟩
    intro heq
    have hcard := congrArg Finset.card heq
    have huniv : (Finset.univ : Finset
      (indexedBlockModel (D.gammaDecomposition.blocks n) B)).card = B.block.card := by
      simp [indexedBlockModel]
    have hlt := hB.2
    omega
  obtain ⟨x, _, hx⟩ := Finset.exists_of_ssubset hproper
  simp only [localMatchingBad, Finset.mem_filter, Finset.mem_univ, true_and,
    not_or, not_lt, not_not] at hx
  exact ⟨x, hx.1, hx.2.1, hx.2.2.1, hx.2.2.2⟩

private theorem source_observable_eq {n : ℕ}
    (B : D.gammaDecomposition.componentIndex n)
    (x : indexedBlockModel (D.gammaDecomposition.blocks n) B) :
    let A : BlockIndex (D.ambientDecomposition.blocks n) :=
      ⟨(D.ambientDecomposition.blocks n).block x.1,
        (D.ambientDecomposition.blocks n).block_mem_blocksFinset x.1⟩
    D.observable n x.1 = medianNormalize
      (componentMedian (D.gammaDecomposition.blocks n)
        (D.ambientDecomposition.blocks n) A : ℝ) B.block.card := by
  classical
  dsimp only [observable, normalizedSize]
  congr 1
  have hmem : x.1 ∈
      (D.gammaDecomposition.blocks n).block
        (BlockIndex.representative (D.gammaDecomposition.blocks n) B) := by
    simpa only [BlockIndex.block_representative] using x.2
  exact_mod_cast congrArg Finset.card
    (((D.gammaDecomposition.blocks n).eq_of_mem _ _ hmem).trans
      (BlockIndex.block_representative (D.gammaDecomposition.blocks n) B))

private theorem target_observable_eq {n : ℕ}
    (B : D.gammaDecomposition.componentIndex n)
    (x : indexedBlockModel (D.gammaDecomposition.blocks n) B)
    (htarget : D.distinguishedPerm n x.1 ∈ D.matchTarget n B)
    (hamb : (D.ambientDecomposition.blocks n).block (D.distinguishedPerm n x.1) =
      (D.ambientDecomposition.blocks n).block x.1) :
    let A : BlockIndex (D.ambientDecomposition.blocks n) :=
      ⟨(D.ambientDecomposition.blocks n).block x.1,
        (D.ambientDecomposition.blocks n).block_mem_blocksFinset x.1⟩
    D.observable n (D.distinguishedPerm n x.1) = medianNormalize
      (componentMedian (D.gammaDecomposition.blocks n)
        (D.ambientDecomposition.blocks n) A : ℝ) (D.matchTarget n B).card := by
  classical
  obtain ⟨z, hz⟩ :=
    (D.gammaDecomposition.refineBlock (D.gammaDecomposition.blocks n)
      (D.distinguishedPerm n) B).target_isBlock
  have hP : (D.gammaDecomposition.blocks n).block (D.distinguishedPerm n x.1) =
      D.matchTarget n B := by
    change (D.gammaDecomposition.blocks n).block (D.distinguishedPerm n x.1) =
      (D.gammaDecomposition.refineBlock (D.gammaDecomposition.blocks n)
        (D.distinguishedPerm n) B).target
    rw [hz]
    exact ((D.gammaDecomposition.blocks n).eq_of_mem z _ (by simpa [hz] using htarget))
  let Aq : BlockIndex (D.ambientDecomposition.blocks n) :=
    ⟨(D.ambientDecomposition.blocks n).block (D.distinguishedPerm n x.1),
      (D.ambientDecomposition.blocks n).block_mem_blocksFinset _⟩
  let A : BlockIndex (D.ambientDecomposition.blocks n) :=
    ⟨(D.ambientDecomposition.blocks n).block x.1,
      (D.ambientDecomposition.blocks n).block_mem_blocksFinset _⟩
  have hA : Aq = A := Subtype.ext hamb
  change medianNormalize
      (componentMedian (D.gammaDecomposition.blocks n)
        (D.ambientDecomposition.blocks n) Aq : ℝ)
      ((D.gammaDecomposition.blocks n).size (D.distinguishedPerm n x.1) : ℝ) = _
  rw [hA]
  congr 1
  exact_mod_cast congrArg Finset.card hP

/-- Proposition `prop:match`(ii) for every acceptable component. -/
theorem acceptable_symmDiff_le {n : ℕ} {η : ℝ}
    (hη : 0 ≤ η) (hηsmall : 2 * η < 1)
    (B : D.gammaDecomposition.componentIndex n)
    (hB : D.ComponentAcceptable n η B) :
    ((D.matchImage n B ∆ D.matchTarget n B).card : ℝ) ≤
      (2 * η + 8 * η / (1 - 2 * η) ^ 2) * B.block.card := by
  obtain ⟨x, hxsource, hxtarget, hxmem, hxambient⟩ := D.exists_goodPoint hB
  let A : BlockIndex (D.ambientDecomposition.blocks n) :=
    ⟨(D.ambientDecomposition.blocks n).block x.1,
      (D.ambientDecomposition.blocks n).block_mem_blocksFinset x.1⟩
  have hm : (0 : ℝ) < componentMedian (D.gammaDecomposition.blocks n)
      (D.ambientDecomposition.blocks n) A := by
    exact_mod_cast componentMedian_pos _ _ A
  apply symmDiff_le_of_pinned hm hη hηsmall B.block
    (D.matchTarget n B) (D.matchImage n B)
  · exact Finset.card_image_of_injective B.block (D.distinguishedPerm n).injective
  · simpa [A, D.source_observable_eq B x] using hxsource
  · simpa [A, D.target_observable_eq B x hxmem hxambient] using hxtarget
  · change ((D.gammaDecomposition.componentLeakage
        (D.gammaDecomposition.blocks n) (D.distinguishedPerm n) B : ℕ) : ℝ) ≤
      η * B.block.card
    exact hB.1

/-! ### Negligible discarded component mass -/

noncomputable def pinBad (n : ℕ) (η : ℝ) :
    Finset (D.approximation.model n) :=
  Finset.univ.filter fun x ↦ η < |D.observable n x - 1 / 2|

theorem pinBad_markov (n : ℕ) {η : ℝ} (hη : 0 ≤ η) :
    η * ((D.pinBad n η).card : ℝ) ≤
      ∑ x : D.approximation.model n, |D.observable n x - 1 / 2| := by
  simpa only [pinBad] using threshold_mul_card_le_sum
    (fun x : D.approximation.model n ↦ |D.observable n x - 1 / 2|)
    (fun _ ↦ abs_nonneg _) hη

/-- Points in one source component which miss the target selected using the
ambient component partition. -/
noncomputable def localLeakageBad (n : ℕ)
    (B : D.gammaDecomposition.componentIndex n) :
    Finset (indexedBlockModel (D.gammaDecomposition.blocks n) B) :=
  Finset.univ.filter fun x ↦
    D.distinguishedPerm n x.1 ∉ D.matchTarget n B

theorem localLeakageBad_card (n : ℕ)
    (B : D.gammaDecomposition.componentIndex n) :
    (D.localLeakageBad n B).card =
      D.gammaDecomposition.componentLeakage
        (D.gammaDecomposition.blocks n) (D.distinguishedPerm n) B := by
  classical
  unfold localLeakageBad ExpanderDecomposition.componentLeakage matchTarget
  apply Finset.card_bij (fun x _ ↦ D.distinguishedPerm n x.1)
  · intro x hx
    rw [Finset.mem_filter] at hx
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩, hx.2⟩
  · intro x _ y _ hxy
    exact Subtype.ext ((D.distinguishedPerm n).injective hxy)
  · intro y hy
    obtain ⟨hyimage, hytarget⟩ := Finset.mem_sdiff.mp hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hyimage
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hytarget⟩

theorem sum_localMatchingBad_le (n : ℕ) (η : ℝ) :
    (∑ B : D.gammaDecomposition.componentIndex n,
      ((D.localMatchingBad n η B).card : ℝ)) ≤
      2 * (D.pinBad n η).card +
      ∑ B : D.gammaDecomposition.componentIndex n,
        (D.gammaDecomposition.componentLeakage
          (D.gammaDecomposition.blocks n) (D.distinguishedPerm n) B : ℝ) +
      ((wordCrossing (D.ambientDecomposition.blocks n)
        (D.distinguishedPerm n)).card : ℝ) := by
  classical
  let P := D.gammaDecomposition.blocks n
  let Q := D.ambientDecomposition.blocks n
  let q := D.distinguishedPerm n
  let p₁ : D.approximation.model n → Prop :=
    fun x ↦ η < |D.observable n x - 1 / 2|
  let p₂ : D.approximation.model n → Prop :=
    fun x ↦ η < |D.observable n (q x) - 1 / 2|
  let p₄ : D.approximation.model n → Prop :=
    fun x ↦ Q.block (q x) ≠ Q.block x
  have hblock (B : D.gammaDecomposition.componentIndex n) :
      ((D.localMatchingBad n η B).card : ℝ) ≤
        ((Finset.univ.filter fun x : indexedBlockModel P B ↦ p₁ x.1).card : ℝ) +
        ((Finset.univ.filter fun x : indexedBlockModel P B ↦ p₂ x.1).card : ℝ) +
        ((D.localLeakageBad n B).card : ℝ) +
        ((Finset.univ.filter fun x : indexedBlockModel P B ↦ p₄ x.1).card : ℝ) := by
    let F₁ : Finset (indexedBlockModel P B) :=
      Finset.univ.filter fun x ↦ p₁ x.1
    let F₂ : Finset (indexedBlockModel P B) :=
      Finset.univ.filter fun x ↦ p₂ x.1
    let F₃ : Finset (indexedBlockModel P B) :=
      Finset.univ.filter fun x ↦ q x.1 ∉ D.matchTarget n B
    let F₄ : Finset (indexedBlockModel P B) :=
      Finset.univ.filter fun x ↦ p₄ x.1
    have hunion : (F₁ ∪ (F₂ ∪ (F₃ ∪ F₄))).card ≤
        F₁.card + F₂.card + F₃.card + F₄.card := by
      have h₁ := Finset.card_union_le F₁ (F₂ ∪ (F₃ ∪ F₄))
      have h₂ := Finset.card_union_le F₂ (F₃ ∪ F₄)
      have h₃ := Finset.card_union_le F₃ F₄
      omega
    have hnat : (D.localMatchingBad n η B).card ≤
        (Finset.univ.filter fun x : indexedBlockModel P B ↦ p₁ x.1).card +
        (Finset.univ.filter fun x : indexedBlockModel P B ↦ p₂ x.1).card +
        (D.localLeakageBad n B).card +
        (Finset.univ.filter fun x : indexedBlockModel P B ↦ p₄ x.1).card := by
      unfold localMatchingBad localLeakageBad
      simp only [p₁, p₂, p₄, P, Q, q]
      rw [Finset.filter_or, Finset.filter_or, Finset.filter_or]
      simpa only [F₁, F₂, F₃, F₄] using hunion
    exact_mod_cast hnat
  have hsum := Finset.sum_le_sum fun B (_ : B ∈ (Finset.univ : Finset _)) ↦ hblock B
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have hp₁ := BlockIndex.sum_card_filter P p₁
  have hp₂ := BlockIndex.sum_card_filter P p₂
  have hp₂card : ((Finset.univ.filter p₂).card : ℝ) = (D.pinBad n η).card := by
    have heq : Finset.univ.filter p₂ = permutationPreimage q (D.pinBad n η) := by
      ext x
      simp [p₂, permutationPreimage, pinBad]
    rw [heq, permutationPreimage_card]
  have hleak : (∑ B : D.gammaDecomposition.componentIndex n,
      ((D.localLeakageBad n B).card : ℝ)) =
      ∑ B : D.gammaDecomposition.componentIndex n,
        (D.gammaDecomposition.componentLeakage P q B : ℝ) := by
    apply Finset.sum_congr rfl
    intro B _
    rw [D.localLeakageBad_card n B]
  have hp₄ := BlockIndex.sum_card_filter P p₄
  have hp₁card : ((Finset.univ.filter p₁).card : ℝ) = (D.pinBad n η).card := by
    rfl
  have hp₄card : ((Finset.univ.filter p₄).card : ℝ) =
      ((wordCrossing Q q).card : ℝ) := by rfl
  rw [hp₁, hp₂, hleak, hp₄] at hsum
  calc
    _ ≤ ((Finset.univ.filter p₁).card : ℝ) +
        ((Finset.univ.filter p₂).card : ℝ) +
        (∑ B : D.gammaDecomposition.componentIndex n,
          (D.gammaDecomposition.componentLeakage P q B : ℝ)) +
        ((Finset.univ.filter p₄).card : ℝ) := hsum
    _ = _ := by rw [hp₁card, hp₂card, hp₄card]; ring

noncomputable def acceptableComponents (n : ℕ) (η : ℝ) :
    Finset (D.gammaDecomposition.componentIndex n) := by
  classical
  exact Finset.univ.filter fun B ↦ D.ComponentAcceptable n η B

theorem mem_acceptableComponents {n : ℕ} {η : ℝ}
    {B : D.gammaDecomposition.componentIndex n} :
    B ∈ D.acceptableComponents n η ↔ D.ComponentAcceptable n η B := by
  classical
  simp [acceptableComponents]

noncomputable def discardedComponentMass (n : ℕ) (η : ℝ) : ℝ :=
  ∑ B ∈ (Finset.univ \ D.acceptableComponents n η), (B.block.card : ℝ)

theorem threshold_mul_discardedComponentMass_le (n : ℕ) {η : ℝ}
    (hη : 0 ≤ η) (hηone : η ≤ 1) :
    η * D.discardedComponentMass n η ≤ 2 * D.totalMatchingError n := by
  classical
  let P := D.gammaDecomposition.blocks n
  let Q := D.ambientDecomposition.blocks n
  let q := D.distinguishedPerm n
  let leak : D.gammaDecomposition.componentIndex n → ℝ := fun B ↦
    D.gammaDecomposition.componentLeakage P q B
  let bad : D.gammaDecomposition.componentIndex n → ℝ := fun B ↦
    (D.localMatchingBad n η B).card
  let L : Finset (D.gammaDecomposition.componentIndex n) :=
    Finset.univ.filter fun B ↦ η * B.block.card < leak B
  let V : Finset (D.gammaDecomposition.componentIndex n) :=
    Finset.univ.filter fun B ↦ B.block.card ≤ bad B
  have hdiscard : Finset.univ \ D.acceptableComponents n η ⊆ L ∪ V := by
    intro B hB
    rcases Finset.mem_sdiff.mp hB with ⟨_, hnotmem⟩
    have hnot : ¬D.ComponentAcceptable n η B := by
      exact fun hacc ↦ hnotmem (D.mem_acceptableComponents.mpr hacc)
    rw [Finset.mem_union]
    by_cases hle : leak B ≤ η * B.block.card
    · right
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      by_contra hbad
      apply hnot
      constructor
      · simpa [leak, P, q] using hle
      · have hbad' : bad B < B.block.card := lt_of_not_ge hbad
        exact_mod_cast hbad'
    · left
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by simpa [L] using lt_of_not_ge hle⟩
  have hmass : D.discardedComponentMass n η ≤
      (∑ B ∈ L, (B.block.card : ℝ)) + ∑ B ∈ V, (B.block.card : ℝ) := by
    unfold discardedComponentMass
    calc
      _ ≤ ∑ B ∈ L ∪ V, (B.block.card : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hdiscard (fun _ _ _ ↦ by positivity)
      _ ≤ _ := by
        have hdecomp : L ∪ V = L ∪ (V \ L) := by ext B; simp
        have hdisj : Disjoint L (V \ L) := Finset.disjoint_left.mpr (by
          intro B hBL hBV
          exact (Finset.mem_sdiff.mp hBV).2 hBL)
        rw [hdecomp, Finset.sum_union hdisj]
        apply add_le_add_left
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset _ _)
          (fun _ _ _ ↦ by positivity)
  have hL : η * (∑ B ∈ L, (B.block.card : ℝ)) ≤ ∑ B, leak B := by
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ B ∈ L, leak B := by
        apply Finset.sum_le_sum
        intro B hB
        exact (Finset.mem_filter.mp hB).2.le
      _ ≤ ∑ B, leak B :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ ↦ by positivity)
  have hV : (∑ B ∈ V, (B.block.card : ℝ)) ≤ ∑ B, bad B := by
    calc
      _ ≤ ∑ B ∈ V, bad B := by
        apply Finset.sum_le_sum
        intro B hB
        exact (Finset.mem_filter.mp hB).2
      _ ≤ ∑ B, bad B :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ ↦ by positivity)
  have hlocal := D.sum_localMatchingBad_le n η
  have hpin := D.pinBad_markov n hη
  have hnonnegMass : 0 ≤ D.discardedComponentMass n η := by
    unfold discardedComponentMass
    positivity
  calc
    η * D.discardedComponentMass n η ≤
        η * ((∑ B ∈ L, (B.block.card : ℝ)) + ∑ B ∈ V, (B.block.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hmass hη
    _ ≤ (∑ B, leak B) + η * ∑ B, bad B := by
      rw [mul_add]
      exact add_le_add hL (mul_le_mul_of_nonneg_left hV hη)
    _ ≤ (∑ B, leak B) +
        η * (2 * (D.pinBad n η).card + ∑ B, leak B +
          ((wordCrossing Q q).card : ℝ)) := by
      have hbadbound := mul_le_mul_of_nonneg_left
        (by simpa [bad, leak, P, Q, q] using hlocal) hη
      linarith
    _ ≤ 2 * D.totalMatchingError n := by
      have hetaPin : η * (2 * ((D.pinBad n η).card : ℝ)) ≤
          2 * ∑ x : D.approximation.model n, |D.observable n x - 1 / 2| := by
        nlinarith [hpin]
      have hetaRest : η * ((∑ B, leak B) + ((wordCrossing Q q).card : ℝ)) ≤
          (∑ B, leak B) + ((wordCrossing Q q).card : ℝ) := by
        apply mul_le_of_le_one_left (by positivity)
        exact hηone
      unfold totalMatchingError
      dsimp only [leak, P, Q, q]
      nlinarith

theorem discardedComponentMass_negligible :
    Negligible D.N fun n ↦ D.discardedComponentMass n (D.matchingThreshold n) := by
  have hscaled := Vanishing.const_mul 2 D.scaledMatchingError_vanishing
  refine Vanishing.squeeze (fun n ↦ div_nonneg (by
      unfold discardedComponentMass
      positivity) (D.N_nonneg n))
    (fun n ↦ ?_) hscaled
  have hη := D.matchingThreshold_pos n
  have hbound := D.threshold_mul_discardedComponentMass_le n hη.le
    (D.matchingThreshold_le_one n)
  calc
    D.discardedComponentMass n (D.matchingThreshold n) / D.N n ≤
        (2 * D.totalMatchingError n / D.matchingThreshold n) / D.N n := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact (le_div_iff₀ hη).2 (by simpa [mul_comm] using hbound)
    _ = 2 * (D.totalMatchingError n / D.matchingThreshold n / D.N n) := by ring

theorem acceptableComponentMass_eq (n : ℕ) (η : ℝ) :
    (∑ B ∈ D.acceptableComponents n η, (B.block.card : ℝ)) +
      D.discardedComponentMass n η = D.N n := by
  classical
  unfold discardedComponentMass
  change (∑ B ∈ D.acceptableComponents n η, (B.block.card : ℝ)) +
    ∑ B ∈ (D.acceptableComponents n η)ᶜ, (B.block.card : ℝ) = D.N n
  rw [Finset.sum_add_sum_compl]
  exact_mod_cast BlockIndex.sum_card (D.gammaDecomposition.blocks n)

theorem eventually_acceptableComponentMass :
    ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
      0 < D.N n ∧
      D.matchingThreshold n < 1 / 256 ∧
      (1 / 2 : ℝ) * D.N n ≤
        ∑ B ∈ D.acceptableComponents n (D.matchingThreshold n),
          (B.block.card : ℝ) := by
  obtain ⟨Ne, hNe⟩ := D.discardedComponentMass_negligible (1 / 2) (by norm_num)
  obtain ⟨Nc, hNc⟩ := D.approximation.card_tendsToInfinity 1
  obtain ⟨Nt, hNt⟩ := D.matchingThreshold_vanishing (1 / 256) (by norm_num)
  refine ⟨max Ne (max Nc Nt), fun n hn ↦ ?_⟩
  have hcardNat : 1 ≤ Fintype.card (D.approximation.model n) :=
    hNc n ((le_max_left Nc Nt).trans ((le_max_right Ne _).trans hn))
  have hcard : 0 < D.N n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hcardNat)
  have herrAbs := hNe n ((le_max_left Ne _).trans hn)
  have hetaAbs := hNt n ((le_max_right Nc Nt).trans ((le_max_right Ne _).trans hn))
  have heta : D.matchingThreshold n < 1 / 256 := by
    simpa [abs_of_pos (D.matchingThreshold_pos n)] using hetaAbs
  have herr : D.discardedComponentMass n (D.matchingThreshold n) / D.N n < 1 / 2 :=
    lt_of_abs_lt herrAbs
  have herr' : D.discardedComponentMass n (D.matchingThreshold n) <
      (1 / 2) * D.N n := by
    rw [div_lt_iff₀ hcard] at herr
    simpa [mul_comm] using herr
  have hmass := D.acceptableComponentMass_eq n (D.matchingThreshold n)
  exact ⟨hcard, heta, by linarith⟩

noncomputable def matchingStart : ℕ :=
  Classical.choose D.eventually_acceptableComponentMass

theorem matchingStart_spec (n : ℕ) (hn : D.matchingStart ≤ n) :
    0 < D.N n ∧
    D.matchingThreshold n < 1 / 256 ∧
    (1 / 2 : ℝ) * D.N n ≤
      ∑ B ∈ D.acceptableComponents n (D.matchingThreshold n),
        (B.block.card : ℝ) :=
  Classical.choose_spec D.eventually_acceptableComponentMass n hn

noncomputable def matchingIndex (n : ℕ) : ℕ := n + D.matchingStart

theorem matchingIndex_ge_start (n : ℕ) : D.matchingStart ≤ D.matchingIndex n := by
  unfold matchingIndex
  omega

theorem matchingIndex_card_pos (n : ℕ) : 0 < D.N (D.matchingIndex n) :=
  (D.matchingStart_spec _ (D.matchingIndex_ge_start n)).1

theorem matchingIndex_threshold_small (n : ℕ) :
    D.matchingThreshold (D.matchingIndex n) < 1 / 256 :=
  (D.matchingStart_spec _ (D.matchingIndex_ge_start n)).2.1

theorem matchingIndex_mass (n : ℕ) :
    (1 / 2 : ℝ) * D.N (D.matchingIndex n) ≤
      ∑ B ∈ D.acceptableComponents (D.matchingIndex n)
        (D.matchingThreshold (D.matchingIndex n)), (B.block.card : ℝ) :=
  (D.matchingStart_spec _ (D.matchingIndex_ge_start n)).2.2

theorem matchingIndex_candidates_nonempty (n : ℕ) :
    (D.acceptableComponents (D.matchingIndex n)
      (D.matchingThreshold (D.matchingIndex n))).Nonempty := by
  by_contra hne
  have hmass := D.matchingIndex_mass n
  rw [Finset.not_nonempty_iff_eq_empty.mp hne] at hmass
  simp only [Finset.sum_empty] at hmass
  nlinarith [D.matchingIndex_card_pos n]

noncomputable def matchingCoefficient (η : ℝ) : ℝ :=
  2 * η + 8 * η / (1 - 2 * η) ^ 2

theorem matchingCoefficient_nonneg {η : ℝ} (hη : 0 ≤ η) :
    0 ≤ matchingCoefficient η := by
  unfold matchingCoefficient
  positivity

theorem matchingCoefficient_le {η : ℝ} (hη : 0 ≤ η) (hηsmall : η ≤ 1 / 4) :
    matchingCoefficient η ≤ 34 * η := by
  have hbase : (1 / 4 : ℝ) ≤ (1 - 2 * η) ^ 2 := by
    have : 1 / 2 ≤ 1 - 2 * η := by linarith
    nlinarith
  have hden : 0 < (1 - 2 * η) ^ 2 := lt_of_lt_of_le (by norm_num) hbase
  have hfrac : 8 * η / (1 - 2 * η) ^ 2 ≤ 32 * η := by
    rw [div_le_iff₀ hden]
    nlinarith
  unfold matchingCoefficient
  linarith

theorem matchingCoefficient_vanishing :
    Vanishing fun n ↦ matchingCoefficient (D.matchingThreshold n) := by
  have hupper := Vanishing.const_mul 34 D.matchingThreshold_vanishing
  obtain ⟨N, hN⟩ := D.matchingThreshold_vanishing (1 / 4) (by norm_num)
  refine Vanishing.squeeze_eventually hupper N (fun n hn ↦ ⟨?_, ?_⟩)
  · exact matchingCoefficient_nonneg (D.matchingThreshold_pos n).le
  · apply matchingCoefficient_le (D.matchingThreshold_pos n).le
    exact (lt_of_abs_lt (hN n hn)).le

theorem acceptable_symmDiff_sum_negligible :
    Negligible (fun n ↦ D.N (D.matchingIndex n)) fun n ↦
      ∑ B ∈ D.acceptableComponents (D.matchingIndex n)
        (D.matchingThreshold (D.matchingIndex n)),
        ((D.matchImage (D.matchingIndex n) B ∆
          D.matchTarget (D.matchingIndex n) B).card : ℝ) := by
  have hcoeff := Vanishing.shift D.matchingCoefficient_vanishing D.matchingStart
  refine Vanishing.squeeze (fun n ↦ div_nonneg (by positivity) (by positivity))
    (fun n ↦ ?_) hcoeff
  let k := D.matchingIndex n
  let η := D.matchingThreshold k
  have hη : 0 ≤ η := (D.matchingThreshold_pos k).le
  have hηsmall : 2 * η < 1 := by
    have := D.matchingIndex_threshold_small n
    dsimp only [η, k] at *
    linarith
  have hsum : (∑ B ∈ D.acceptableComponents k η,
      ((D.matchImage k B ∆ D.matchTarget k B).card : ℝ)) ≤
      matchingCoefficient η * D.N k := by
    calc
      _ ≤ ∑ B ∈ D.acceptableComponents k η,
          matchingCoefficient η * B.block.card := by
        apply Finset.sum_le_sum
        intro B hB
        simpa only [matchingCoefficient] using D.acceptable_symmDiff_le hη hηsmall B
          (D.mem_acceptableComponents.mp hB)
      _ = matchingCoefficient η *
          ∑ B ∈ D.acceptableComponents k η, (B.block.card : ℝ) := by
        rw [Finset.mul_sum]
      _ ≤ matchingCoefficient η * D.N k := by
        apply mul_le_mul_of_nonneg_left _ (matchingCoefficient_nonneg hη)
        have hsub : ∑ B ∈ D.acceptableComponents k η, B.block.card ≤
            ∑ B : D.gammaDecomposition.componentIndex k, B.block.card :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun _ _ _ ↦ by positivity)
        rw [BlockIndex.sum_card] at hsub
        exact_mod_cast hsub
  have hN : 0 < D.N k := D.matchingIndex_card_pos n
  calc
    (∑ B ∈ D.acceptableComponents k η,
        ((D.matchImage k B ∆ D.matchTarget k B).card : ℝ)) / D.N k ≤
      (matchingCoefficient η * D.N k) / D.N k :=
        div_le_div_of_nonneg_right hsum hN.le
    _ = matchingCoefficient η := by field_simp

theorem acceptable_target_dominates (n : ℕ)
    (B : D.gammaDecomposition.componentIndex n)
    (hstart : D.matchingStart ≤ n)
    (hB : B ∈ D.acceptableComponents n (D.matchingThreshold n)) :
    2 * (D.matchImage n B ∆ D.matchTarget n B).card <
      (D.matchTarget n B).card := by
  have heta : 0 ≤ D.matchingThreshold n := (D.matchingThreshold_pos n).le
  have hetasmall : 2 * D.matchingThreshold n < 1 := by
    have hnsmall := (D.matchingStart_spec n hstart).2.1
    linarith
  have hsym := D.acceptable_symmDiff_le heta hetasmall B
    (D.mem_acceptableComponents.mp hB)
  have hcoeff : matchingCoefficient (D.matchingThreshold n) < 1 / 6 := by
    have hsmall := (D.matchingStart_spec n hstart).2.1
    have hle := matchingCoefficient_le heta (le_trans hsmall.le (by norm_num))
    nlinarith
  have hCpos : (0 : ℝ) < B.block.card := by
    exact_mod_cast (BlockIndex.block_nonempty (D.gammaDecomposition.blocks n) B).card_pos
  have hsreal : ((D.matchImage n B ∆ D.matchTarget n B).card : ℝ) <
      (1 / 6) * B.block.card := by
    exact hsym.trans_lt (mul_lt_mul_of_pos_right hcoeff hCpos)
  have hsubset : D.matchImage n B ⊆
      (D.matchImage n B ∆ D.matchTarget n B) ∪ D.matchTarget n B := by
    intro x hx
    by_cases hxt : x ∈ D.matchTarget n B
    · exact Finset.mem_union_right _ hxt
    · exact Finset.mem_union_left _ (by
        rw [Finset.mem_symmDiff]
        exact Or.inl ⟨hx, hxt⟩)
  have hcard := (Finset.card_le_card hsubset).trans
    (Finset.card_union_le _ _)
  have himage : (D.matchImage n B).card = B.block.card :=
    Finset.card_image_of_injective _ (D.distinguishedPerm n).injective
  rw [himage] at hcard
  have hcardReal : (B.block.card : ℝ) ≤
      (D.matchImage n B ∆ D.matchTarget n B).card + (D.matchTarget n B).card := by
    exact_mod_cast hcard
  exact_mod_cast (by linarith :
    (2 : ℝ) * (D.matchImage n B ∆ D.matchTarget n B).card <
      (D.matchTarget n B).card)

/-- The acceptable targets are pairwise distinct at every shifted index. -/
theorem acceptableTargets_injOn (n : ℕ) :
    Set.InjOn (D.matchTarget (D.matchingIndex n))
      (D.acceptableComponents (D.matchingIndex n)
        (D.matchingThreshold (D.matchingIndex n)) :
          Set (D.gammaDecomposition.componentIndex (D.matchingIndex n))) := by
  classical
  intro B hB C hC htarget
  by_contra hBC
  have hsource : Disjoint (D.matchImage (D.matchingIndex n) B)
      (D.matchImage (D.matchingIndex n) C) := by
    apply Finset.disjoint_left.mpr
    intro z hzB hzC
    obtain ⟨x, hxB, rfl⟩ := Finset.mem_image.mp hzB
    obtain ⟨y, hyC, hxy⟩ := Finset.mem_image.mp hzC
    have hxy' : x = y := (D.distinguishedPerm (D.matchingIndex n)).injective hxy.symm
    subst y
    have hd : Disjoint B.block C.block :=
      (BlockIndex.pairwise_disjoint
        (D.gammaDecomposition.blocks (D.matchingIndex n)))
        (Finset.mem_univ B) (Finset.mem_univ C) (Subtype.coe_injective.ne hBC)
    exact Finset.disjoint_left.mp hd hxB hyC
  have hdomB := D.acceptable_target_dominates _ B (D.matchingIndex_ge_start n) hB
  have hdomC := D.acceptable_target_dominates _ C (D.matchingIndex_ge_start n) hC
  rw [← htarget] at hdomC
  exact matching_injective _ _ (D.matchTarget (D.matchingIndex n) B) hsource hdomB hdomC

noncomputable def matchImageEmbedding (n : ℕ) :
    D.gammaDecomposition.componentIndex n ↪
      Finset (D.approximation.model n) where
  toFun B := D.matchImage n B
  inj' := by
    intro B C h
    apply Subtype.ext
    change B.block.image (D.distinguishedPerm n) =
      C.block.image (D.distinguishedPerm n) at h
    exact Finset.image_injective (D.distinguishedPerm n).injective h

noncomputable def acceptableImages (n : ℕ) :
    Finset (Finset (D.approximation.model (D.matchingIndex n))) :=
  (D.acceptableComponents (D.matchingIndex n)
    (D.matchingThreshold (D.matchingIndex n))).map
      (D.matchImageEmbedding (D.matchingIndex n))

noncomputable def sourceOfImage (n : ℕ)
    (U : Finset (D.approximation.model (D.matchingIndex n))) :
    D.gammaDecomposition.componentIndex (D.matchingIndex n) :=
  let B := Classical.choose (D.matchingIndex_candidates_nonempty n)
  letI : Nonempty (D.gammaDecomposition.componentIndex (D.matchingIndex n)) := ⟨B⟩
  Function.invFun (D.matchImageEmbedding (D.matchingIndex n)) U

noncomputable def targetOfImage (n : ℕ)
    (U : Finset (D.approximation.model (D.matchingIndex n))) :
    Finset (D.approximation.model (D.matchingIndex n)) :=
  D.matchTarget (D.matchingIndex n) (D.sourceOfImage n U)

theorem sourceOfImage_matchImage (n : ℕ)
    (B : D.gammaDecomposition.componentIndex (D.matchingIndex n)) :
    D.sourceOfImage n (D.matchImage (D.matchingIndex n) B) = B := by
  let B₀ := Classical.choose (D.matchingIndex_candidates_nonempty n)
  letI : Nonempty (D.gammaDecomposition.componentIndex (D.matchingIndex n)) := ⟨B₀⟩
  exact Function.leftInverse_invFun (D.matchImageEmbedding (D.matchingIndex n)).injective B

theorem acceptableImages_source (n : ℕ) {U}
    (hU : U ∈ D.acceptableImages n) :
    ∃ B ∈ D.acceptableComponents (D.matchingIndex n)
        (D.matchingThreshold (D.matchingIndex n)),
      U = D.matchImage (D.matchingIndex n) B ∧ D.sourceOfImage n U = B := by
  obtain ⟨B, hB, rfl⟩ := Finset.mem_map.mp hU
  exact ⟨B, hB, rfl, D.sourceOfImage_matchImage n B⟩

theorem acceptableImages_are_blocks (n : ℕ) :
    ∀ U ∈ D.acceptableImages n, ∃ y,
      U = ((D.gammaDecomposition.blocks (D.matchingIndex n)).transportEquiv
        (D.distinguishedPerm (D.matchingIndex n))).block y := by
  intro U hU
  obtain ⟨B, _, rfl, _⟩ := D.acceptableImages_source n hU
  refine ⟨D.distinguishedPerm (D.matchingIndex n)
    (BlockIndex.representative (D.gammaDecomposition.blocks (D.matchingIndex n)) B), ?_⟩
  change D.matchImage (D.matchingIndex n) B =
    ((D.gammaDecomposition.blocks (D.matchingIndex n)).block
      (BlockIndex.representative (D.gammaDecomposition.blocks (D.matchingIndex n)) B)).image
        (D.distinguishedPerm (D.matchingIndex n))
  rw [BlockIndex.block_representative]

theorem targetOfImage_isBlock (n : ℕ) :
    ∀ U ∈ D.acceptableImages n, ∃ y,
      D.targetOfImage n U = (D.gammaDecomposition.blocks (D.matchingIndex n)).block y := by
  intro U hU
  obtain ⟨B, _, rfl, hsource⟩ := D.acceptableImages_source n hU
  rw [targetOfImage, hsource]
  obtain ⟨y, hy⟩ :=
    (D.gammaDecomposition.refineBlock
      (D.gammaDecomposition.blocks (D.matchingIndex n))
      (D.distinguishedPerm (D.matchingIndex n)) B).target_isBlock
  exact ⟨y, hy⟩

theorem targetOfImage_injOn (n : ℕ) :
    Set.InjOn (D.targetOfImage n)
      (D.acceptableImages n : Set (Finset
        (D.approximation.model (D.matchingIndex n)))) := by
  intro U hU V hV hUV
  obtain ⟨B, hB, rfl, hsourceB⟩ := D.acceptableImages_source n hU
  obtain ⟨C, hC, rfl, hsourceC⟩ := D.acceptableImages_source n hV
  rw [targetOfImage, hsourceB, targetOfImage, hsourceC] at hUV
  have hBC := D.acceptableTargets_injOn n hB hC hUV
  subst C
  rfl

theorem acceptableImages_discarded_card (n : ℕ) :
    (((Finset.univ : Finset (D.approximation.model (D.matchingIndex n))) \
      matchedRetainedSupport (D.acceptableImages n)).card : ℝ) =
      D.discardedComponentMass (D.matchingIndex n)
        (D.matchingThreshold (D.matchingIndex n)) := by
  classical
  let P : BlockStructure (D.approximation.model (D.matchingIndex n)) :=
    (D.gammaDecomposition.blocks (D.matchingIndex n)).transportEquiv
    (D.distinguishedPerm (D.matchingIndex n))
  have hret := matchedRetainedSupport_card P (D.acceptableImages n)
    (D.acceptableImages_are_blocks n)
  have hsumMap : (∑ U ∈ D.acceptableImages n, U.card) =
      ∑ B ∈ D.acceptableComponents (D.matchingIndex n)
        (D.matchingThreshold (D.matchingIndex n)), B.block.card := by
    unfold acceptableImages
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro B hB
    change (D.matchImage (D.matchingIndex n) B).card = B.block.card
    rw [Finset.card_image_of_injective _
      (D.distinguishedPerm (D.matchingIndex n)).injective]
    rfl
  have hret' := hret.trans hsumMap
  have huniv := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (matchedRetainedSupport (D.acceptableImages n)))
  rw [hret'] at huniv
  have hunivReal :
      ((((Finset.univ : Finset
          (D.approximation.model (D.matchingIndex n))) \
        matchedRetainedSupport (D.acceptableImages n)).card : ℝ) +
        ∑ B ∈ D.acceptableComponents (D.matchingIndex n)
          (D.matchingThreshold (D.matchingIndex n)), (B.block.card : ℝ)) =
        D.N (D.matchingIndex n) := by
    exact_mod_cast huniv
  have hmass := D.acceptableComponentMass_eq (D.matchingIndex n)
    (D.matchingThreshold (D.matchingIndex n))
  linarith

theorem acceptableImages_discarded_negligible :
    Negligible (fun n ↦ D.N (D.matchingIndex n)) fun n ↦
      (((Finset.univ : Finset (D.approximation.model (D.matchingIndex n))) \
        matchedRetainedSupport (D.acceptableImages n)).card : ℝ) := by
  apply Negligible.congr
    (Negligible.shift D.discardedComponentMass_negligible D.matchingStart)
  intro n
  rw [D.acceptableImages_discarded_card]
  rfl

theorem acceptableImages_defect_sum_eq (n : ℕ) :
    (∑ U ∈ D.acceptableImages n, (U ∆ D.targetOfImage n U).card) =
      ∑ B ∈ D.acceptableComponents (D.matchingIndex n)
        (D.matchingThreshold (D.matchingIndex n)),
        (D.matchImage (D.matchingIndex n) B ∆
          D.matchTarget (D.matchingIndex n) B).card := by
  classical
  unfold acceptableImages
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro B hB
  change (D.matchImage (D.matchingIndex n) B ∆
    D.targetOfImage n (D.matchImage (D.matchingIndex n) B)).card = _
  rw [targetOfImage, D.sourceOfImage_matchImage]

theorem acceptableImages_defect_negligible :
    Negligible (fun n ↦ D.N (D.matchingIndex n)) fun n ↦
      ((∑ U ∈ D.acceptableImages n,
        (U ∆ D.targetOfImage n U).card : ℕ) : ℝ) := by
  apply Negligible.congr D.acceptable_symmDiff_sum_negligible
  intro n
  push_cast
  exact_mod_cast (D.acceptableImages_defect_sum_eq n).symm

theorem matchedCore_missing_negligible :
    Negligible (fun n ↦ D.N (D.matchingIndex n)) fun n ↦
      (((Finset.univ : Finset (D.approximation.model (D.matchingIndex n))) \
        matchedCore (D.acceptableImages n) (D.targetOfImage n)).card : ℝ) := by
  exact NonsoficGroupsExist.matchedCore_missing_negligible
    (fun n ↦ D.N (D.matchingIndex n))
    (fun n ↦ D.matchingIndex_card_pos n)
    (fun n ↦ (D.gammaDecomposition.blocks (D.matchingIndex n)).transportEquiv
      (D.distinguishedPerm (D.matchingIndex n)))
    D.acceptableImages D.acceptableImages_are_blocks D.targetOfImage
    D.acceptableImages_discarded_negligible D.acceptableImages_defect_negligible

noncomputable abbrev transportedBlocks (n : ℕ) :
    BlockStructure (D.approximation.model (D.matchingIndex n)) :=
  (D.gammaDecomposition.blocks (D.matchingIndex n)).transportEquiv
    (D.distinguishedPerm (D.matchingIndex n))

noncomputable abbrev localizedProductAct (n : ℕ) (g : Γ × J) :
    Equiv.Perm (D.approximation.model (D.matchingIndex n)) :=
  D.approximation.map (D.matchingIndex n) (D.setup.productEmbedding g)

/-- Every fixed element of the embedded product almost preserves the
transported source-component partition. -/
theorem transportedBlocks_almost_invariant (g : Γ × J) :
    Negligible (fun n ↦ D.N (D.matchingIndex n)) fun n ↦
      ((wordCrossing (D.transportedBlocks n) (D.localizedProductAct n g)).card : ℝ) := by
  have htarget0 := D.gammaDecomposition.all_almost_invariant
    D.setup.generatorsΓ_symmetric D.setup.generatorsΓ_generate
    (D.setup.compressedEnd D.setup.distinguished D.setup.distinguished_mem g.1 *
      D.setup.embedJ g.2)
  have htarget : Negligible (fun n ↦ D.N (D.matchingIndex n)) fun n ↦
      ((wordCrossing (D.gammaDecomposition.blocks (D.matchingIndex n))
        (D.localizedProductAct n g)).card : ℝ) := by
    apply Negligible.congr (Negligible.shift htarget0 D.matchingStart)
    intro n
    rw [localizedProductAct, D.setup.productEmbedding_eq_embedΓ]
    rfl
  exact NonsoficGroupsExist.wordCrossing_negligible
    (fun n ↦ D.N (D.matchingIndex n))
    (fun n ↦ D.matchingIndex_card_pos n)
    D.transportedBlocks
    (fun n ↦ D.gammaDecomposition.blocks (D.matchingIndex n))
    D.acceptableImages D.acceptableImages_are_blocks D.targetOfImage
    D.targetOfImage_isBlock D.targetOfImage_injOn (fun n ↦ D.localizedProductAct n g)
    D.matchedCore_missing_negligible htarget

end LocalCriterionData

end NonsoficGroupsExist
