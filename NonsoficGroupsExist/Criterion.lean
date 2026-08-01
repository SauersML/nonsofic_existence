import NonsoficGroupsExist.MedianNormalization
import NonsoficGroupsExist.Refinement
import NonsoficGroupsExist.Selection
import NonsoficGroupsExist.Localization
import NonsoficGroupsExist.PermutationConservation
import NonsoficGroupsExist.LEF
import NonsoficGroupsExist.Kazhdan
import Mathlib.Data.Fintype.Prod

/-!
# The compression--centralizer criterion

This file assembles Section `sec:criterion`.  The finite quantitative content
of Sections `subsec:onesided`--`subsec:matching` is proved here in full:

* `BlockStructure` -- the component partitions `𝒫ₙ` and `ℬₙ` of
  Section `subsec:partitions`;
* `onesided_drop` -- the one-sided estimate along a compressor arc;
* `card_ratio_of_pinned`, `symmDiff_le_of_pinned` -- Proposition
  `prop:match`(ii), the passage from pinning to almost-bijective matching;
* `matching_injective` -- Proposition `prop:match`(iii).

The two external inputs of the manuscript are isolated as explicit interfaces
rather than being assumed silently:

* `ExpanderDecomposition` records the conclusion of Kun's theorem
  (Theorem `thm:kun`) in the form used in Section `subsec:partitions`;
* `KunThomHypothesis` records the conclusion of the Kun--Thom theorem
  (Theorem `thm:kunthom`) in the essential form invoked at the end of the proof
  of Theorem `thm:local`.

`compression_centralizer` is the manuscript's Theorem `thm:D` relative to these
two interfaces together with the matching certificate produced by
Sections `subsec:matching`--`subsec:selection`.
-/

namespace NonsoficGroupsExist

open scoped BigOperators symmDiff

/-! ### Component partitions -/

/-- A partition of a finite model into blocks, presented by the block map.
This is how the manuscript carries `𝒫ₙ` and `ℬₙ`. -/
structure BlockStructure (Y : FiniteModel) where
  block : Y → Finset Y
  self_mem : ∀ y, y ∈ block y
  eq_of_mem : ∀ x y, y ∈ block x → block y = block x

namespace BlockStructure

variable {Y : FiniteModel} (P : BlockStructure Y)

/-- The size `s(y)` of the block of `y`. -/
def size (y : Y) : ℕ := (P.block y).card

theorem size_pos (y : Y) : 0 < P.size y :=
  Finset.card_pos.mpr ⟨y, P.self_mem y⟩

theorem one_le_size (y : Y) : (1 : ℝ) ≤ P.size y := by
  exact_mod_cast P.size_pos y

theorem size_eq_of_mem {x y : Y} (h : y ∈ P.block x) : P.size y = P.size x := by
  rw [size, size, P.eq_of_mem x y h]

/-- Two blocks are equal or disjoint. -/
theorem block_disjoint {x y : Y} (h : P.block x ≠ P.block y) :
    Disjoint (P.block x) (P.block y) := by
  classical
  apply Finset.disjoint_left.mpr
  intro z hzx hzy
  exact h ((P.eq_of_mem x z hzx).symm.trans (P.eq_of_mem y z hzy))

end BlockStructure

/-! ### The normalization and its one-sided estimate -/

variable {α : Type*} [DecidableEq α]

/-- The one-sided estimate of Section `subsec:median`: if the compressed image
of a block of size `c` lands in a target of size at least `c - e`, then the
normalization drops by at most `e/c`. -/
theorem onesided_drop {m c d e : ℝ} (hm : 1 ≤ m) (hc : 0 < c) (hd : 0 ≤ d)
    (he : 0 ≤ e) (hleak : c - e ≤ d) :
    medianNormalize m c - medianNormalize m d ≤ e / c := by
  have hδ : 0 ≤ e / c := div_nonneg he hc.le
  refine medianNormalize_loss hm hc.le hδ ?_ hd
  have : (1 - e / c) * c = c - e := by
    field_simp
  linarith [this]

/-- Pinning bounds the ratio of two sizes normalized by the same median.  This
is equation `eq:ratio` of the manuscript. -/
theorem card_ratio_of_pinned {m c d η : ℝ} (hm : 0 < m) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hηsmall : 2 * η < 1)
    (hpinC : |medianNormalize m c - 1 / 2| ≤ η)
    (hpinD : |medianNormalize m d - 1 / 2| ≤ η) :
    (1 - 2 * η) ^ 2 * d ≤ (1 + 2 * η) ^ 2 * c := by
  have hC := (medianNormalize_ratio hm hc hpinC).1
  have hD := (medianNormalize_ratio hm hd hpinD).2
  have hη : 0 ≤ η := (abs_nonneg _).trans hpinC
  have hminus : 0 ≤ 1 - 2 * η := by linarith
  have hplus : 0 ≤ 1 + 2 * η := by linarith
  calc
    (1 - 2 * η) ^ 2 * d = (1 - 2 * η) * ((1 - 2 * η) * d) := by ring
    _ ≤ (1 - 2 * η) * ((1 + 2 * η) * m) :=
      mul_le_mul_of_nonneg_left hD hminus
    _ = (1 + 2 * η) * ((1 - 2 * η) * m) := by ring
    _ ≤ (1 + 2 * η) * ((1 + 2 * η) * c) :=
      mul_le_mul_of_nonneg_left hC hplus
    _ = (1 + 2 * η) ^ 2 * c := by ring

/-- **Proposition `prop:match`(ii).**  A compressed block that leaks at most a
`η`-fraction of its mass, and whose size and target size are both pinned at the
ambient median, differs from its target by an `O(η)`-fraction. -/
theorem symmDiff_le_of_pinned {m η : ℝ} (hm : 0 < m) (hηnonneg : 0 ≤ η)
    (hηsmall : 2 * η < 1) (C D U : Finset α) (hUC : U.card = C.card)
    (hpinC : |medianNormalize m C.card - 1 / 2| ≤ η)
    (hpinD : |medianNormalize m D.card - 1 / 2| ≤ η)
    (hleak : ((U \ D).card : ℝ) ≤ η * C.card) :
    ((U ∆ D).card : ℝ) ≤ (2 * η + 8 * η / (1 - 2 * η) ^ 2) * C.card := by
  classical
  have hden : 0 < (1 - 2 * η) ^ 2 := by
    have : 0 < 1 - 2 * η := by linarith
    positivity
  have hη8 : 0 ≤ 8 * η := mul_nonneg (by norm_num) hηnonneg
  have hcast : ((U ∆ D).card : ℝ) ≤
      2 * ((U \ D).card : ℝ) + ((D.card : ℝ) - U.card) := by
    have := card_symmDiff_le U D ((U \ D).card) le_rfl
    exact_mod_cast this
  have hratio :=
    card_ratio_of_pinned hm (by positivity : (0 : ℝ) ≤ (C.card : ℝ))
      (by positivity : (0 : ℝ) ≤ (D.card : ℝ)) hηsmall hpinC hpinD
  have hgap : (1 - 2 * η) ^ 2 * ((D.card : ℝ) - C.card) ≤ 8 * η * C.card := by
    nlinarith [hratio, hη8]
  have hgap' : (D.card : ℝ) - C.card ≤ 8 * η / (1 - 2 * η) ^ 2 * C.card := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hden]
    nlinarith [hgap]
  have hUcast : ((U.card : ℝ)) = (C.card : ℝ) := by exact_mod_cast hUC
  calc
    ((U ∆ D).card : ℝ) ≤ 2 * ((U \ D).card : ℝ) + ((D.card : ℝ) - U.card) := hcast
    _ ≤ 2 * (η * C.card) + ((D.card : ℝ) - C.card) := by
      rw [hUcast]; linarith [hleak]
    _ ≤ 2 * (η * C.card) + 8 * η / (1 - 2 * η) ^ 2 * C.card := by linarith
    _ = (2 * η + 8 * η / (1 - 2 * η) ^ 2) * C.card := by ring

/-- **Proposition `prop:match`(iii).**  Two disjoint compressed blocks cannot
both match the same target. -/
theorem matching_injective (U₁ U₂ D : Finset α) (hdisj : Disjoint U₁ U₂)
    (h₁ : 2 * (U₁ ∆ D).card < D.card) (h₂ : 2 * (U₂ ∆ D).card < D.card) :
    False :=
  dominant_intersection_unique U₁ U₂ D hdisj
    (dominant_of_small_symmDiff U₁ D h₁) (dominant_of_small_symmDiff U₂ D h₂)

/-! ### The external interfaces -/

/-- The loopless generator multigraph of a finite permutation model.  Its edge
type consists of generator/vertex arc occurrences, so parallel edges and labels
are retained and fixed-point loops are discarded. -/
noncomputable abbrev generatorGraph {G : Type} [Group G] (Y : FiniteModel)
    (T : Finset G) (act : G → Equiv.Perm Y) : FiniteMultiGraph := by
  classical
  letI : Fintype T := Fintype.ofFinset T (fun _ ↦ Iff.rfl)
  let arcs : Finset (T × Y) :=
    Finset.univ.filter fun p ↦ act p.1.1 p.2 ≠ p.2
  exact
    { vertex := Y
      edge :=
        { carrier := ↥arcs
          fintype := Fintype.ofFinset arcs (fun _ ↦ Iff.rfl)
          decidableEq := Classical.decEq _ }
      first := fun a ↦ a.1.2
      second := fun a ↦ act a.1.1.1 a.1.2
      loopless := fun a ↦ by
        have ha0 := a.2
        change a.1 ∈
          (Finset.univ.filter fun p : T × Y ↦ act p.1.1 p.2 ≠ p.2) at ha0
        have ha : act a.1.1.1 a.1.2 ≠ a.1.2 := (Finset.mem_filter.mp ha0).2
        exact ha.symm }

/-- The generator graph has the model itself as its vertex type. -/
noncomputable def generatorGraphVertexEquiv {G : Type} [Group G]
    (Y : FiniteModel) (T : Finset G) (act : G → Equiv.Perm Y) :
    (generatorGraph Y T act).vertex ≃ Y := by
  change Y ≃ Y
  exact Equiv.refl Y

/-- The conclusion of Kun's theorem (Theorem `thm:kun`) in the form used in
Section `subsec:partitions`: after `o(|Yₙ|)` edge edits the generator graphs
split into uniformly expanding components, and the resulting block partition is
almost invariant under every generator. -/
structure ExpanderDecomposition {G : Type} [Group G]
    (S : SoficApproximation G) (T : Finset G) where
  blocks : ∀ n, BlockStructure (S.model n)
  cheeger : ℝ
  cheeger_pos : 0 < cheeger
  graph : ℕ → FiniteMultiGraph
  vertexEquiv : ∀ n, (graph n).vertex ≃ S.model n
  /-- The edited graph is occurrence-close to the actual generator graph. -/
  edit_negligible : Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
    fun n ↦ ((generatorGraph (S.model n) T (S.map n)).editDistance
      ((graph n).transport (S.model n) (vertexEquiv n)) (Equiv.refl _) : ℕ)
  /-- Occurrence-level realization of the edge edits, preserving every kept
  parallel occurrence and its unordered endpoint pair. -/
  editWitness : ∀ n, EdgeEditWitness
    (generatorGraph (S.model n) T (S.map n))
      ((graph n).transport (S.model n) (vertexEquiv n)) (Equiv.refl _)
  unmatched_negligible : Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
    fun n ↦ ((editWitness n).unmatchedCount : ℝ)
  /-- Every edited edge stays inside one block. -/
  edge_inside : ∀ n (e : ((graph n).transport (S.model n) (vertexEquiv n)).edge),
    (blocks n).block (((graph n).transport (S.model n) (vertexEquiv n)).first e) =
      (blocks n).block (((graph n).transport (S.model n) (vertexEquiv n)).second e)
  /-- Each induced component has the uniform Cheeger bound. -/
  component_expands : ∀ n (y : S.model n),
    (((graph n).transport (S.model n) (vertexEquiv n)).induce
      ((blocks n).block y)).HasCheegerLowerBound cheeger
  /-- Almost invariance, equation `eq:gamma-inv`. -/
  almost_invariant : ∀ t ∈ T, Negligible (fun n ↦ (Fintype.card (S.model n) : ℝ))
    fun n ↦ ((Finset.univ.filter fun y : S.model n ↦
      (blocks n).block (S.map n t y) ≠ (blocks n).block y).card : ℝ)

/-- The certificate produced by Sections `subsec:matching`--`subsec:selection`:
a localized sofic approximation of `K × J` whose `K`-generator graphs form an
essential expander sequence. -/
structure MatchingCertificate (K J : Type) [Group K] [Group J] where
  generatorsK : Finset K
  generatorsK_generate : Subgroup.closure (generatorsK : Set K) = ⊤
  generatorsJ : Finset J
  generatorsJ_generate : Subgroup.closure (generatorsJ : Set J) = ⊤
  infiniteK : Infinite K
  approx : SoficApproximation (K × J)
  graphs : ℕ → FiniteMultiGraph
  vertexEquiv : ∀ n, (graphs n).vertex ≃ approx.model n
  cheeger : ℝ
  cheeger_pos : 0 < cheeger
  expands : ∀ n, (graphs n).HasCheegerLowerBound cheeger
  edit_negligible : Negligible (fun n ↦ (Fintype.card (approx.model n) : ℝ))
    fun n ↦ ((generatorGraph (approx.model n) generatorsK
      (fun k ↦ approx.map n (k, 1))).editDistance (graphs n)
        ((generatorGraphVertexEquiv (approx.model n) generatorsK
          (fun k ↦ approx.map n (k, 1))).trans (vertexEquiv n).symm) : ℕ)

/-- The conclusion of the Kun--Thom theorem (Theorem `thm:kunthom`) for the
fixed groups `K,J`.  Property `(T)` of `K` is deliberately kept in this named
external hypothesis; every finite and asymptotic premise consumed by the
theorem is explicit in `MatchingCertificate`. -/
def KunThomHypothesis (K J : Type) [Group K] [Group J] : Prop :=
  HasKazhdanPropertyT K → ∀ _ : MatchingCertificate K J, IsLEF J

/-- **Theorem `thm:D`, relative to the two cited external theorems.**  Given the
Kun--Thom obstruction and the matching certificate manufactured by the
compression mechanism, the commuting subgroup is LEF. -/
theorem compression_centralizer (K J : Type) [Group K] [Group J]
    (hKT : KunThomHypothesis K J) (hT : HasKazhdanPropertyT K)
    (cert : MatchingCertificate K J) : IsLEF J :=
  hKT hT cert

end NonsoficGroupsExist
