import NonsoficGroupsExist.Matching.MedianNormalization
import NonsoficGroupsExist.Matching.Refinement
import NonsoficGroupsExist.Matching.Selection
import NonsoficGroupsExist.Matching.Localization
import NonsoficGroupsExist.Matching.PermutationConservation
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Fintype.BigOperators
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

`ExpanderDecomposition` and `MatchingCertificate` are reusable interfaces
between stages of the proof.  Their inhabitants are constructed by the Kun
decomposition and matching modules before the closed criterion is applied;
this module does not treat their existence as an external premise of the
headline theorem.
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

/-! ### Data used by the matching development -/

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

/-- A generator multigraph has degree at most twice the number of labels:
at a fixed vertex there is at most one outgoing and one incoming occurrence
for each permutation label. -/
theorem generatorGraph_degree_le {G : Type} [Group G]
    (Y : FiniteModel) (T : Finset G) (act : G → Equiv.Perm Y)
    (x : Y) : (generatorGraph Y T act).degree x ≤ 2 * T.card := by
  classical
  let f : {e : (generatorGraph Y T act).edge //
      e ∈ (generatorGraph Y T act).incidentEdges x} → T × Bool := fun e ↦
    if (generatorGraph Y T act).first e.1 = x then
      (e.1.1.1, false)
    else
      (e.1.1.1, true)
  have hf : Function.Injective f := by
    intro e e' heq
    by_cases he : (generatorGraph Y T act).first e.1 = x
    · have he' : (generatorGraph Y T act).first e'.1 = x := by
        by_contra hne'
        have htag := congrArg (fun z : T × Bool ↦ z.2) heq
        rw [show f e = (e.1.1.1, false) from dif_pos he,
          show f e' = (e'.1.1.1, true) from dif_neg hne'] at htag
        exact Bool.noConfusion htag
      have hs : e.1.1.1 = e'.1.1.1 := by
        have hfirst := congrArg (fun z : T × Bool ↦ z.1) heq
        rw [show f e = (e.1.1.1, false) from dif_pos he,
          show f e' = (e'.1.1.1, false) from dif_pos he'] at hfirst
        exact hfirst
      apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext hs (he.trans he'.symm)
    · have he' : (generatorGraph Y T act).first e'.1 ≠ x := by
        intro he'x
        have htag := congrArg (fun z : T × Bool ↦ z.2) heq
        rw [show f e = (e.1.1.1, true) from dif_neg he,
          show f e' = (e'.1.1.1, false) from dif_pos he'x] at htag
        exact Bool.noConfusion htag
      have hs : e.1.1.1 = e'.1.1.1 := by
        have hfirst := congrArg (fun z : T × Bool ↦ z.1) heq
        rw [show f e = (e.1.1.1, true) from dif_neg he,
          show f e' = (e'.1.1.1, true) from dif_neg he'] at hfirst
        exact hfirst
      have hsecond : (generatorGraph Y T act).second e.1 = x := by
        have hi := (Finset.mem_filter.mp e.2).2
        exact hi.resolve_left he
      have hsecond' : (generatorGraph Y T act).second e'.1 = x := by
        have hi := (Finset.mem_filter.mp e'.2).2
        exact hi.resolve_left he'
      have hsval : e.1.1.1.1 = e'.1.1.1.1 := congrArg Subtype.val hs
      change act e.1.1.1.1 e.1.1.2 = x at hsecond
      change act e'.1.1.1.1 e'.1.1.2 = x at hsecond'
      have hsource : e.1.1.2 = e'.1.1.2 := by
        rw [hsval] at hsecond
        apply (act e'.1.1.1.1).injective
        exact hsecond.trans hsecond'.symm
      apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext hs hsource
  have hcard := Fintype.card_le_of_injective f hf
  simpa [FiniteMultiGraph.degree, Fintype.card_coe, Fintype.card_prod,
    Nat.mul_comm]
    using hcard

theorem generatorGraph_hasDegreeBound {G : Type} [Group G]
    (Y : FiniteModel) (T : Finset G) (act : G → Equiv.Perm Y) :
    (generatorGraph Y T act).HasDegreeBound (2 * T.card) :=
  generatorGraph_degree_le Y T act

/-- An expander decomposition in the precise form consumed by the subsequent
finite matching argument.  `KunDecomposition` constructs this data from
property `(T)`; this structure merely records the resulting interface. -/
structure ExpanderDecomposition {G : Type} [Group G]
    (S : SoficApproximation G) (T : Finset G) where
  blocks : ∀ n, BlockStructure (S.model n)
  cheeger : ℝ
  cheeger_pos : 0 < cheeger
  graph : ℕ → FiniteMultiGraph
  vertexEquiv : ∀ n, (graph n).vertex ≃ S.model n
  degreeBound : ℕ
  degree_le : ∀ n, (graph n).HasDegreeBound degreeBound
  /-- The edited graph is occurrence-close to the actual generator graph. -/
  edit_negligible : S.cardScale.Negligible
    fun n ↦ ((generatorGraph (S.model n) T (S.map n)).editDistance
      ((graph n).transport (S.model n) (vertexEquiv n)) (Equiv.refl _) : ℕ)
  /-- Occurrence-level realization of the edge edits, preserving every kept
  parallel occurrence and its unordered endpoint pair. -/
  editWitness : ∀ n, EdgeEditWitness
    (generatorGraph (S.model n) T (S.map n))
      ((graph n).transport (S.model n) (vertexEquiv n)) (Equiv.refl _)
  unmatched_negligible : S.cardScale.Negligible
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
  almost_invariant : ∀ t ∈ T, S.cardScale.Negligible
    fun n ↦ ((Finset.univ.filter fun y : S.model n ↦
      (blocks n).block (S.map n t y) ≠ (blocks n).block y).card : ℝ)

/-- A localized sofic approximation of `K × J` whose `K`-generator graphs form
an essential expander sequence.  The structure records the output of the
finite matching construction; it does not imply the Kun--Thom conclusion. -/
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
  edit_negligible : approx.cardScale.Negligible
    fun n ↦ ((generatorGraph (approx.model n) generatorsK
      (fun k ↦ approx.map n (k, 1))).editDistance (graphs n)
        ((generatorGraphVertexEquiv (approx.model n) generatorsK
          (fun k ↦ approx.map n (k, 1))).trans (vertexEquiv n).symm) : ℕ)

/-- **Definition `def:essential`.**  A sequence of graphs is an *essential
expander sequence* along a diverging vertex scale when it is edit-equivalent
to an expander sequence: graphs identified vertex by vertex with it, carrying
one uniform positive Cheeger bound, at negligible edit distance.

Two points are conventions rather than differences.  The vertex sets are
identified by an explicit equivalence instead of being equal on the nose,
which is how every graph in this library carries its vertex set; and the
divergence `|V(Xₙ)| → ∞` of the printed definition is carried by the
`AsymptoticScale` against which the edit count is negligible, rather than
restated.

One point is a deliberate difference, recorded in the manuscript's margin
note: the printed definition restricts to bounded-degree sequences, and this
predicate does not.  It is therefore strictly weaker as a definition.  The
sequences it is applied to are `T`-generator graphs, whose degree is at most
`2|T|` by `generatorGraph_hasDegreeBound`, so the omitted bound is a
hypothesis that is always available and never used. -/
def IsEssentialExpanderSequence (scale : AsymptoticScale)
    (X : ℕ → FiniteMultiGraph) : Prop :=
  ∃ (Y : ℕ → FiniteMultiGraph) (e : ∀ n, (X n).vertex ≃ (Y n).vertex) (h : ℝ),
    0 < h ∧ (∀ n, (Y n).HasCheegerLowerBound h) ∧
      scale.Negligible fun n ↦ ((X n).editDistance (Y n) (e n) : ℕ)

/-- The `K`-generator graphs of a matching certificate are an essential
expander sequence.  This is what the certificate's expansion and edit fields
say, and it is why `MatchingCertificate` is the formal content of
Definition `def:essential`: the fields are the existential witnesses. -/
theorem MatchingCertificate.isEssentialExpanderSequence {K J : Type} [Group K]
    [Group J] (C : MatchingCertificate K J) :
    IsEssentialExpanderSequence C.approx.cardScale
      (fun n ↦ generatorGraph (C.approx.model n) C.generatorsK
        (fun k ↦ C.approx.map n (k, 1))) :=
  ⟨C.graphs,
    fun n ↦ (generatorGraphVertexEquiv (C.approx.model n) C.generatorsK
      (fun k ↦ C.approx.map n (k, 1))).trans (C.vertexEquiv n).symm,
    C.cheeger, C.cheeger_pos, C.expands, C.edit_negligible⟩

end NonsoficGroupsExist
