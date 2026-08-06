import NonsoficGroupsExist.Matching.DirectedCoarea
import Mathlib.Logic.Equiv.Fintype

/-!
# Finite rounding for the Kazhdan improvement argument

This module formalizes the finite relation-to-permutation part of the
Kun--Thom improvement theorem.  A relation close to the graph of a
permutation contains a large partial permutation; that partial permutation is
extended to a genuine permutation without changing any retained graph point.
-/

namespace NonsoficGroupsExist
namespace KazhdanImprovement

open AlmostAutomorphism
open AlmostAutomorphism.ClusterData

variable (Y : FiniteModel)

/-- The graph of a permutation as a finite binary relation. -/
def permutationGraph (c : Equiv.Perm Y) : Finset (Y × Y) :=
  Finset.univ.image fun x ↦ (x, c x)

@[simp] theorem mem_permutationGraph (c : Equiv.Perm Y) (p : Y × Y) :
    p ∈ permutationGraph Y c ↔ p.2 = c p.1 := by
  constructor
  · intro hp
    rw [permutationGraph, Finset.mem_image] at hp
    obtain ⟨x, _, rfl⟩ := hp
    rfl
  · intro hp
    rw [permutationGraph, Finset.mem_image]
    exact ⟨p.1, Finset.mem_univ _, Prod.ext rfl hp.symm⟩

@[simp] theorem card_permutationGraph (c : Equiv.Perm Y) :
    (permutationGraph Y c).card = Fintype.card Y := by
  rw [permutationGraph, Finset.card_image_iff.mpr]
  · simp
  · intro x _ y _ hxy
    exact congrArg Prod.fst hxy

/-- Sources whose original permutation-graph point is absent from a relation. -/
def missingSources (U : Finset (Y × Y)) (c : Equiv.Perm Y) : Finset Y :=
  Finset.univ.filter fun x ↦ (x, c x) ∉ U

@[simp] theorem mem_missingSources (U : Finset (Y × Y))
    (c : Equiv.Perm Y) (x : Y) :
    x ∈ missingSources Y U c ↔ (x, c x) ∉ U := by
  simp [missingSources]

theorem card_missingSources (U : Finset (Y × Y)) (c : Equiv.Perm Y) :
    (missingSources Y U c).card = (permutationGraph Y c \ U).card := by
  let f : Y ↪ Y × Y := ⟨fun x ↦ (x, c x), fun _ _ h ↦ congrArg Prod.fst h⟩
  have himage : (missingSources Y U c).map f = permutationGraph Y c \ U := by
    ext p
    constructor
    · intro hp
      rw [Finset.mem_map] at hp
      obtain ⟨x, hx, rfl⟩ := hp
      rw [Finset.mem_sdiff]
      refine ⟨mem_permutationGraph Y c _ |>.2 rfl, ?_⟩
      change (x, c x) ∉ U
      simpa [missingSources] using hx
    · intro hp
      rw [Finset.mem_sdiff] at hp
      obtain ⟨hgraph, hU⟩ := hp
      rw [mem_permutationGraph] at hgraph
      rw [Finset.mem_map]
      refine ⟨p.1, ?_, ?_⟩
      · rw [mem_missingSources]
        intro hpU
        apply hU
        have hpEq : (p.1, c p.1) = p := Prod.ext rfl hgraph.symm
        simpa [hpEq] using hpU
      · exact Prod.ext rfl hgraph.symm
  rw [← himage, Finset.card_map]

/-- A partial copy of `c`, with domain restricted to graph points retained by
`U`, extends to a permutation of the whole finite set. -/
theorem exists_permutation_agreeing_on_retained
    (U : Finset (Y × Y)) (c : Equiv.Perm Y) :
    ∃ c' : Equiv.Perm Y, ∀ x, (x, c x) ∈ U → c' x = c x := by
  let A := {x : Y // (x, c x) ∈ U}
  let inclusion : A → Y := fun x ↦ x.1
  let image : A → Y := fun x ↦ c x.1
  have hinclusion : Function.Injective inclusion := fun _ _ h ↦ Subtype.ext h
  have himage : Function.Injective image := fun _ _ h ↦
    Subtype.ext (c.injective h)
  obtain ⟨c', hc'⟩ :=
    Equiv.Perm.exists_extending_pair inclusion image hinclusion himage
  refine ⟨c', fun x hx ↦ ?_⟩
  exact hc' ⟨x, hx⟩

/-- A fixed choice of the finite permutation extension. -/
noncomputable def roundRelation (U : Finset (Y × Y))
    (c : Equiv.Perm Y) : Equiv.Perm Y :=
  Classical.choose (exists_permutation_agreeing_on_retained Y U c)

theorem roundRelation_eq_of_mem (U : Finset (Y × Y))
    (c : Equiv.Perm Y) (x : Y) (hx : (x, c x) ∈ U) :
    roundRelation Y U c x = c x :=
  Classical.choose_spec (exists_permutation_agreeing_on_retained Y U c) x hx

theorem roundRelation_disagreement_subset_missingSources
    (U : Finset (Y × Y)) (c : Equiv.Perm Y) :
    (Finset.univ.filter fun x ↦ roundRelation Y U c x ≠ c x) ⊆
      missingSources Y U c := by
  intro x hx
  rw [mem_missingSources]
  intro hmem
  have hne : roundRelation Y U c x ≠ c x := by simpa using hx
  exact hne (roundRelation_eq_of_mem Y U c x hmem)

theorem hammingDistance_roundRelation_le
    (U : Finset (Y × Y)) (c : Equiv.Perm Y) :
    hammingDistance Y (roundRelation Y U c) c ≤
      ((permutationGraph Y c \ U).card : ℝ) / Fintype.card Y := by
  unfold hammingDistance
  unfold hammingDisagreement
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hcard :
      (Finset.univ.filter fun x ↦ roundRelation Y U c x ≠ c x).card ≤
        (permutationGraph Y c \ U).card := by
    rw [← card_missingSources Y U c]
    exact Finset.card_le_card
      (roundRelation_disagreement_subset_missingSources Y U c)
  exact_mod_cast hcard

/-! ### Comparing relation boundaries with permutation defects -/

/-- The diagonal action of a label on a binary relation. -/
def diagonalAction (s : Equiv.Perm Y) (p : Y × Y) : Y × Y :=
  (s p.1, s p.2)

/-- Generator-tagged directed boundary occurrences of a binary relation for
the diagonal action.  Retaining the label tag avoids losing multiplicity when
two generators happen to induce the same finite permutation. -/
def relationBoundary (S : Finset (Equiv.Perm Y)) (U : Finset (Y × Y)) :
    Finset (Equiv.Perm Y × (Y × Y)) :=
  (S.product Finset.univ).filter fun p ↦
    (p.2 ∈ U ∧ diagonalAction Y p.1 p.2 ∉ U) ∨
      (p.2 ∉ U ∧ diagonalAction Y p.1 p.2 ∈ U)

@[simp] theorem mem_relationBoundary (S : Finset (Equiv.Perm Y))
    (U : Finset (Y × Y)) (p : Equiv.Perm Y × (Y × Y)) :
    p ∈ relationBoundary Y S U ↔ p.1 ∈ S ∧
      ((p.2 ∈ U ∧ diagonalAction Y p.1 p.2 ∉ U) ∨
        (p.2 ∉ U ∧ diagonalAction Y p.1 p.2 ∈ U)) := by
  simp [relationBoundary]

/-- Boundary occurrences directed out of a relation. -/
def leavingRelationBoundary (S : Finset (Equiv.Perm Y))
    (U : Finset (Y × Y)) : Finset (Equiv.Perm Y × (Y × Y)) :=
  (relationBoundary Y S U).filter fun p ↦ p.2 ∈ U

/-- Boundary occurrences directed into a relation. -/
def enteringRelationBoundary (S : Finset (Equiv.Perm Y))
    (U : Finset (Y × Y)) : Finset (Equiv.Perm Y × (Y × Y)) :=
  (relationBoundary Y S U).filter fun p ↦ p.2 ∉ U

theorem relationBoundary_subset_leaving_union_entering
    (S : Finset (Equiv.Perm Y)) (U : Finset (Y × Y)) :
    relationBoundary Y S U ⊆
      leavingRelationBoundary Y S U ∪ enteringRelationBoundary Y S U := by
  intro p hp
  by_cases hU : p.2 ∈ U
  · exact Finset.mem_union_left _ (by simp [leavingRelationBoundary, hp, hU])
  · exact Finset.mem_union_right _ (by simp [enteringRelationBoundary, hp, hU])

/-- Forget the relation target coordinate and retain the label and source. -/
def relationSourceArc (p : Equiv.Perm Y × (Y × Y)) : Arc Y :=
  (p.1, p.2.1)

theorem relationSourceArc_injectiveOn_leaving_graph
    (S : Finset (Equiv.Perm Y)) (c : Equiv.Perm Y) :
    Set.InjOn (relationSourceArc Y)
      (leavingRelationBoundary Y S (permutationGraph Y c) :
        Set (Equiv.Perm Y × (Y × Y))) := by
  intro p hp q hq heq
  have hpdata : p ∈ relationBoundary Y S (permutationGraph Y c) ∧
      p.2 ∈ permutationGraph Y c := by
    simpa [leavingRelationBoundary] using hp
  have hqdata : q ∈ relationBoundary Y S (permutationGraph Y c) ∧
      q.2 ∈ permutationGraph Y c := by
    simpa [leavingRelationBoundary] using hq
  have hpgraph := hpdata.2
  have hqgraph := hqdata.2
  have hs : p.1 = q.1 :=
    congrArg (fun r : Arc Y ↦ r.1) heq
  have hx : p.2.1 = q.2.1 :=
    congrArg (fun r : Arc Y ↦ r.2) heq
  have hp2 := (mem_permutationGraph Y c p.2).1 hpgraph
  have hq2 := (mem_permutationGraph Y c q.2).1 hqgraph
  apply Prod.ext hs
  apply Prod.ext hx
  calc
    p.2.2 = c p.2.1 := hp2
    _ = c q.2.1 := congrArg c hx
    _ = q.2.2 := hq2.symm

theorem image_relationSourceArc_leaving_graph_subset_badArcs
    (S : Finset (Equiv.Perm Y)) (c : Equiv.Perm Y) :
    (leavingRelationBoundary Y S (permutationGraph Y c)).image
        (relationSourceArc Y) ⊆ badArcs Y S c := by
  intro a ha
  rw [Finset.mem_image] at ha
  obtain ⟨p, hp, rfl⟩ := ha
  have hpdata : p ∈ relationBoundary Y S (permutationGraph Y c) ∧
      p.2 ∈ permutationGraph Y c := by
    simpa [leavingRelationBoundary] using hp
  have hboundary := (mem_relationBoundary Y S (permutationGraph Y c) p).1
    hpdata.1
  have hleave : diagonalAction Y p.1 p.2 ∉ permutationGraph Y c := by
    rcases hboundary.2 with hout | hin
    · exact hout.2
    · exact (hin.1 hpdata.2).elim
  rw [mem_badArcs]
  refine ⟨hboundary.1, ?_⟩
  have hpgraph := (mem_permutationGraph Y c p.2).1 hpdata.2
  change c (p.1 p.2.1) ≠ p.1 (c p.2.1)
  intro heq
  apply hleave
  rw [mem_permutationGraph]
  dsimp [diagonalAction]
  simpa [hpgraph] using heq.symm

theorem card_leaving_graph_le_badArcs
    (S : Finset (Equiv.Perm Y)) (c : Equiv.Perm Y) :
    (leavingRelationBoundary Y S (permutationGraph Y c)).card ≤
      (badArcs Y S c).card := by
  have himage :
      ((leavingRelationBoundary Y S (permutationGraph Y c)).image
        (relationSourceArc Y)).card =
          (leavingRelationBoundary Y S (permutationGraph Y c)).card :=
    Finset.card_image_iff.mpr fun p hp q hq heq ↦
      relationSourceArc_injectiveOn_leaving_graph Y S c hp hq heq
  rw [← himage]
  exact Finset.card_le_card
    (image_relationSourceArc_leaving_graph_subset_badArcs Y S c)

theorem relationSourceArc_injectiveOn_entering_graph
    (S : Finset (Equiv.Perm Y)) (c : Equiv.Perm Y) :
    Set.InjOn (relationSourceArc Y)
      (enteringRelationBoundary Y S (permutationGraph Y c) :
        Set (Equiv.Perm Y × (Y × Y))) := by
  intro p hp q hq heq
  have hpdata : p ∈ relationBoundary Y S (permutationGraph Y c) ∧
      p.2 ∉ permutationGraph Y c := by
    simpa [enteringRelationBoundary] using hp
  have hqdata : q ∈ relationBoundary Y S (permutationGraph Y c) ∧
      q.2 ∉ permutationGraph Y c := by
    simpa [enteringRelationBoundary] using hq
  have hs : p.1 = q.1 :=
    congrArg (fun r : Arc Y ↦ r.1) heq
  have hx : p.2.1 = q.2.1 :=
    congrArg (fun r : Arc Y ↦ r.2) heq
  have hpenter := (mem_relationBoundary Y S (permutationGraph Y c) p).1
    hpdata.1
  have hqenter := (mem_relationBoundary Y S (permutationGraph Y c) q).1
    hqdata.1
  have hptarget : diagonalAction Y p.1 p.2 ∈ permutationGraph Y c := by
    rcases hpenter.2 with hout | hin
    · exact (hpdata.2 hout.1).elim
    · exact hin.2
  have hqtarget : diagonalAction Y q.1 q.2 ∈ permutationGraph Y c := by
    rcases hqenter.2 with hout | hin
    · exact (hqdata.2 hout.1).elim
    · exact hin.2
  have hpEq := (mem_permutationGraph Y c _).1 hptarget
  have hqEq := (mem_permutationGraph Y c _).1 hqtarget
  apply Prod.ext hs
  apply Prod.ext hx
  apply p.1.injective
  change p.1 p.2.2 = p.1 q.2.2
  calc
    p.1 p.2.2 = c (p.1 p.2.1) := hpEq
    _ = c (q.1 q.2.1) := by rw [hs, hx]
    _ = q.1 q.2.2 := hqEq.symm
    _ = p.1 q.2.2 := by rw [hs]

theorem image_relationSourceArc_entering_graph_subset_badArcs
    (S : Finset (Equiv.Perm Y)) (c : Equiv.Perm Y) :
    (enteringRelationBoundary Y S (permutationGraph Y c)).image
        (relationSourceArc Y) ⊆ badArcs Y S c := by
  intro a ha
  rw [Finset.mem_image] at ha
  obtain ⟨p, hp, rfl⟩ := ha
  have hpdata : p ∈ relationBoundary Y S (permutationGraph Y c) ∧
      p.2 ∉ permutationGraph Y c := by
    simpa [enteringRelationBoundary] using hp
  have hboundary := (mem_relationBoundary Y S (permutationGraph Y c) p).1
    hpdata.1
  have htarget : diagonalAction Y p.1 p.2 ∈ permutationGraph Y c := by
    rcases hboundary.2 with hout | hin
    · exact (hpdata.2 hout.1).elim
    · exact hin.2
  rw [mem_badArcs]
  refine ⟨hboundary.1, ?_⟩
  have htargetEq := (mem_permutationGraph Y c _).1 htarget
  change c (p.1 p.2.1) ≠ p.1 (c p.2.1)
  intro hgood
  apply hpdata.2
  rw [mem_permutationGraph]
  apply p.1.injective
  calc
    p.1 p.2.2 = c (p.1 p.2.1) := htargetEq
    _ = p.1 (c p.2.1) := hgood

theorem card_entering_graph_le_badArcs
    (S : Finset (Equiv.Perm Y)) (c : Equiv.Perm Y) :
    (enteringRelationBoundary Y S (permutationGraph Y c)).card ≤
      (badArcs Y S c).card := by
  have himage :
      ((enteringRelationBoundary Y S (permutationGraph Y c)).image
        (relationSourceArc Y)).card =
          (enteringRelationBoundary Y S (permutationGraph Y c)).card :=
    Finset.card_image_iff.mpr fun p hp q hq heq ↦
      relationSourceArc_injectiveOn_entering_graph Y S c hp hq heq
  rw [← himage]
  exact Finset.card_le_card
    (image_relationSourceArc_entering_graph_subset_badArcs Y S c)

/-- The diagonal boundary of a permutation graph is at most twice the
permutation's label-commutation defect. -/
theorem card_relationBoundary_permutationGraph_le
    (S : Finset (Equiv.Perm Y)) (c : Equiv.Perm Y) :
    (relationBoundary Y S (permutationGraph Y c)).card ≤
      2 * (badArcs Y S c).card := by
  have hcover := Finset.card_le_card
    (relationBoundary_subset_leaving_union_entering Y S (permutationGraph Y c))
  have hunion := Finset.card_union_le
    (leavingRelationBoundary Y S (permutationGraph Y c))
    (enteringRelationBoundary Y S (permutationGraph Y c))
  have hleave := card_leaving_graph_le_badArcs Y S c
  have henter := card_entering_graph_le_badArcs Y S c
  omega

/-- A product can fail to preserve a label only where the right factor fails,
or at the right-factor translate of a defect of the left factor. -/
theorem badArcs_mul_subset
    (S : Finset (Equiv.Perm Y)) (a b : Equiv.Perm Y) :
    badArcs Y S (a * b) ⊆
      badArcs Y S b ∪
        (badArcs Y S a).map (inverseDefectEquiv Y b⁻¹).toEmbedding := by
  intro p hp
  have hpdata := (mem_badArcs Y S (a * b) p).1 hp
  by_cases hb : b (p.1 p.2) ≠ p.1 (b p.2)
  · exact Finset.mem_union_left _ <|
      (mem_badArcs Y S b p).2 ⟨hpdata.1, hb⟩
  · apply Finset.mem_union_right
    rw [Finset.mem_map]
    let q : Arc Y := (p.1, b p.2)
    refine ⟨q, ?_, ?_⟩
    · rw [mem_badArcs]
      refine ⟨hpdata.1, ?_⟩
      intro ha
      apply hpdata.2
      simp only [Equiv.Perm.coe_mul, Function.comp_apply]
      rw [not_ne_iff.mp hb, ha]
    · simp [q, inverseDefectEquiv]

theorem card_badArcs_mul_le
    (S : Finset (Equiv.Perm Y)) (a b : Equiv.Perm Y) :
    (badArcs Y S (a * b)).card ≤
      (badArcs Y S a).card + (badArcs Y S b).card := by
  have hsubset := Finset.card_le_card (badArcs_mul_subset Y S a b)
  have hunion := Finset.card_union_le (badArcs Y S b)
    ((badArcs Y S a).map (inverseDefectEquiv Y b⁻¹).toEmbedding)
  rw [Finset.card_map] at hunion
  omega

/-! ### Indicator-function form of the relation estimates -/

/-- The real indicator of a finite binary relation. -/
noncomputable def relationIndicator (U : Finset (Y × Y)) (p : Y × Y) : ℝ :=
  if p ∈ U then 1 else 0

/-- Unnormalized `ℓ¹` variation under the tagged diagonal generator action. -/
noncomputable def relationVariation (S : Finset (Equiv.Perm Y))
    (f : Y × Y → ℝ) : ℝ :=
  ∑ p ∈ S.product (Finset.univ : Finset (Y × Y)),
    |f (diagonalAction Y p.1 p.2) - f p.2|

theorem relationVariation_indicator
    (S : Finset (Equiv.Perm Y)) (U : Finset (Y × Y)) :
    relationVariation Y S (relationIndicator Y U) =
      (relationBoundary Y S U).card := by
  classical
  rw [relationVariation, Finset.card_eq_sum_ones]
  rw [Nat.cast_sum]
  unfold relationBoundary
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hq : p.2 ∈ U <;>
    by_cases hr : diagonalAction Y p.1 p.2 ∈ U <;>
      simp [relationIndicator, hq, hr, abs_of_nonneg, abs_of_nonpos]

/-- Unnormalized `ℓ¹` distance on functions over the finite relation space. -/
noncomputable def relationL1Distance (f g : Y × Y → ℝ) : ℝ :=
  ∑ p : Y × Y, |f p - g p|

theorem relationL1Distance_indicator
    (U V : Finset (Y × Y)) :
    relationL1Distance Y (relationIndicator Y U) (relationIndicator Y V) =
      ((U \ V).card + (V \ U).card : ℕ) := by
  classical
  rw [relationL1Distance]
  have hsum :
      ∑ p : Y × Y,
          |relationIndicator Y U p - relationIndicator Y V p| =
        ∑ p ∈ (Finset.univ : Finset (Y × Y)),
          if (p ∈ U ∧ p ∉ V) ∨ (p ∈ V ∧ p ∉ U) then (1 : ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro p _
    by_cases hU : p ∈ U <;> by_cases hV : p ∈ V <;>
      simp [relationIndicator, hU, hV, abs_of_nonneg, abs_of_nonpos]
  rw [hsum]
  rw [← Finset.sum_filter]
  have hfilter :
      (Finset.univ.filter fun p : Y × Y ↦
        (p ∈ U ∧ p ∉ V) ∨ (p ∈ V ∧ p ∉ U)) =
          (U \ V) ∪ (V \ U) := by
    ext p
    simp [and_or_left]
  rw [hfilter, Finset.sum_const, nsmul_eq_mul]
  have hdisjoint : Disjoint (U \ V) (V \ U) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    rw [Finset.mem_sdiff] at hp hq
    exact hp.2 hq.1
  rw [Finset.card_union_of_disjoint hdisjoint]
  norm_num

/-! ### Small-defect cluster candidates

The expansion constant controls separation of clusters, whereas the defect
parameter controls which almost automorphisms are admitted.  These parameters
must be independent: Kun's improvement theorem starts with a sufficiently
small defect depending on its constants, not with the largest defect for which
the separation lemma happens to hold. -/

/-- A permutation and its inverse each fail to preserve fewer than an
`ε`-fraction of the labeled arcs. -/
def IsEpsilonGood (S : Finset (Equiv.Perm Y)) (ε : ℝ)
    (c : Equiv.Perm Y) : Prop :=
  ((badArcs Y S c).card : ℝ) < ε * Fintype.card Y ∧
    ((badArcs Y S c⁻¹).card : ℝ) < ε * Fintype.card Y

noncomputable def epsilonGoodCandidates
    (S : Finset (Equiv.Perm Y)) (ε : ℝ) : Finset (Equiv.Perm Y) := by
  classical
  exact Finset.univ.filter (IsEpsilonGood Y S ε)

@[simp] theorem mem_epsilonGoodCandidates
    (S : Finset (Equiv.Perm Y)) (ε : ℝ) (c : Equiv.Perm Y) :
    c ∈ epsilonGoodCandidates Y S ε ↔ IsEpsilonGood Y S ε c := by
  simp [epsilonGoodCandidates]

/-- Cluster data with a defect budget independent of the expansion scale. -/
noncomputable def clusterData_of_epsilonRounding
    (S : Finset (Equiv.Perm Y)) {h ε : ℝ}
    (m : ℕ) (hm : 0 < m)
    (hsize : 5 * m ≤ Fintype.card Y)
    (hexp : HasDirectedExpansionAtScale Y S h m)
    (hε : 0 < ε)
    (hseparation : 2 * ε * Fintype.card Y < h * m)
    (round : Equiv.Perm Y → Equiv.Perm Y)
    (hroundGood : ∀ a, IsEpsilonGood Y S ε a →
      ∀ b, IsEpsilonGood Y S ε b →
        IsEpsilonGood Y S ε (round (a * b)))
    (hroundClose : ∀ a, IsEpsilonGood Y S ε a →
      ∀ b, IsEpsilonGood Y S ε b →
        hammingDistance Y (a * b) (round (a * b)) <
          (m : ℝ) / Fintype.card Y) : ClusterData Y where
  radius := (m : ℝ) / Fintype.card Y
  radius_pos := by
    have hmReal : (0 : ℝ) < m := by exact_mod_cast hm
    have hcard : (0 : ℝ) < Fintype.card Y := by
      exact_mod_cast (show 0 < Fintype.card Y by omega)
    exact div_pos hmReal hcard
  candidate := epsilonGoodCandidates Y S ε
  one_mem := by
    rw [mem_epsilonGoodCandidates]
    have hcard : (0 : ℝ) < Fintype.card Y := by
      exact_mod_cast (show 0 < Fintype.card Y by omega)
    have hthreshold : 0 < ε * Fintype.card Y := mul_pos hε hcard
    constructor <;> simpa [IsEpsilonGood, badArcs] using hthreshold
  inv_mem := by
    intro c hc
    rw [mem_epsilonGoodCandidates] at hc ⊢
    simpa [IsEpsilonGood] using hc.symm
  round := round
  round_product_mem := by
    intro a ha b hb
    rw [mem_epsilonGoodCandidates] at ha hb ⊢
    exact hroundGood a ha b hb
  round_product_close := by
    intro a ha b hb
    rw [mem_epsilonGoodCandidates] at ha hb
    exact hroundClose a ha b hb
  gap := by
    intro a ha b hb
    rw [mem_epsilonGoodCandidates] at ha hb
    apply hammingDistance_small_or_four_mul_le Y S a b m hm hsize hexp
    have hsum :
        (((badArcs Y S a).card + (badArcs Y S b).card : ℕ) : ℝ) <
          2 * ε * Fintype.card Y := by
      norm_num [Nat.cast_add]
      linarith [ha.1, hb.1]
    exact hsum.trans hseparation

variable {K J : Type} [Group K] [Group J]

theorem productMap_isEpsilonGood_eventually
    (A : SoficApproximation (K × J)) (T : Finset K)
    {ε : ℝ} (hε : 0 < ε) (j : J) :
    ∃ N : ℕ, ∀ n ≥ N,
      IsEpsilonGood (A.model n) (productLabels A n T) ε
        (A.map n (1, j)) := by
  have hdefect := badArcs_productLabels_negligible A T j
  obtain ⟨Ndefect, hNdefect⟩ := hdefect ε hε
  obtain ⟨Ncard, hNcard⟩ := A.card_tendsToInfinity 1
  refine ⟨max Ndefect Ncard, fun n hn ↦ ?_⟩
  have hnd : Ndefect ≤ n := (le_max_left _ _).trans hn
  have hnc : Ncard ≤ n := (le_max_right _ _).trans hn
  have hcardNat : 0 < Fintype.card (A.model n) := by
    have := hNcard n hnc
    omega
  have hcardReal : (0 : ℝ) < Fintype.card (A.model n) := by
    exact_mod_cast hcardNat
  have hratio := hNdefect n hnd
  rw [abs_of_nonneg (div_nonneg (by positivity) hcardReal.le)] at hratio
  rw [div_lt_iff₀ hcardReal] at hratio
  refine ⟨hratio, ?_⟩
  rw [card_badArcs_inv]
  exact hratio

theorem productMap_isEpsilonGood_on_finset_eventually
    (A : SoficApproximation (K × J)) (T : Finset K)
    {ε : ℝ} (hε : 0 < ε) (F : Finset J) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ j ∈ F,
      IsEpsilonGood (A.model n) (productLabels A n T) ε
        (A.map n (1, j)) := by
  exact eventually_finset F
    (fun j n ↦ IsEpsilonGood (A.model n) (productLabels A n T) ε
      (A.map n (1, j)))
    (fun j _ ↦ productMap_isEpsilonGood_eventually A T hε j)

/-- Kun--Thom's finite cluster argument with the mathematically necessary
small defect parameter separated from the expansion constant. -/
theorem isLEF_of_product_epsilonRounding
    (A : SoficApproximation (K × J)) (T : Finset K)
    {h ε : ℝ} (hε : 0 < ε) (hsmall : 20 * ε < h)
    (hexp : ∃ Nexp, ∀ n ≥ Nexp,
      HasDirectedExpansionAtScale (A.model n) (productLabels A n T) h
        (clusterScale (A.model n)))
    (hround : ∃ Nround, ∀ n ≥ Nround,
      ∃ round : Equiv.Perm (A.model n) → Equiv.Perm (A.model n),
        (∀ a, IsEpsilonGood (A.model n) (productLabels A n T) ε a →
          ∀ b, IsEpsilonGood (A.model n) (productLabels A n T) ε b →
          IsEpsilonGood (A.model n) (productLabels A n T) ε
            (round (a * b))) ∧
        (∀ a, IsEpsilonGood (A.model n) (productLabels A n T) ε a →
          ∀ b, IsEpsilonGood (A.model n) (productLabels A n T) ε b →
          hammingDistance (A.model n) (a * b) (round (a * b)) <
            clusterRadius (A.model n))) : IsLEF J := by
  intro s
  obtain ⟨Nexp, hNexp⟩ := hexp
  obtain ⟨Nround, hNround⟩ := hround
  obtain ⟨Ngood, hNgood⟩ :=
    productMap_isEpsilonGood_on_finset_eventually A T hε (finiteControl s)
  obtain ⟨Nmul, hNmul⟩ :=
    productMap_mul_close_on_finset_eventually A s
      (show (0 : ℝ) < 1 / 10 by norm_num)
  obtain ⟨Nsep, hNsep⟩ := productMap_separated_on_finset_eventually A s
  obtain ⟨None, hNone⟩ := A.map_one_close (1 / 10) (by norm_num)
  obtain ⟨Ncard, hNcard⟩ := A.card_tendsToInfinity 10
  let n := max Nexp
    (max Nround (max Ngood (max Nmul (max Nsep (max None Ncard)))))
  have hnexp : Nexp ≤ n := by dsimp [n]; omega
  have hnround : Nround ≤ n := by dsimp [n]; omega
  have hngood : Ngood ≤ n := by dsimp [n]; omega
  have hnmul : Nmul ≤ n := by dsimp [n]; omega
  have hnsep : Nsep ≤ n := by dsimp [n]; omega
  have hnone : None ≤ n := by dsimp [n]; omega
  have hncard : Ncard ≤ n := by dsimp [n]; omega
  have hcard : 10 ≤ Fintype.card (A.model n) := hNcard n hncard
  have hm : 0 < clusterScale (A.model n) :=
    clusterScale_pos _ (by omega)
  have hfive := five_mul_clusterScale_le (A.model n)
  have hexpn := hNexp n hnexp
  obtain ⟨round, hroundGood, hroundClose⟩ := hNround n hnround
  have hcardScale : Fintype.card (A.model n) ≤
      10 * clusterScale (A.model n) := by
    unfold clusterScale
    omega
  have hcardScaleReal : (Fintype.card (A.model n) : ℝ) ≤
      10 * clusterScale (A.model n) := by exact_mod_cast hcardScale
  have hmReal : (0 : ℝ) < clusterScale (A.model n) := by exact_mod_cast hm
  have hseparation :
      2 * ε * Fintype.card (A.model n) <
        h * clusterScale (A.model n) := by
    have hle : 2 * ε * Fintype.card (A.model n) ≤
        20 * ε * clusterScale (A.model n) := by
      nlinarith [hcardScaleReal]
    have hlt : 20 * ε * clusterScale (A.model n) <
        h * clusterScale (A.model n) := by
      exact mul_lt_mul_of_pos_right hsmall hmReal
    exact hle.trans_lt hlt
  let D : ClusterData (A.model n) := clusterData_of_epsilonRounding
    (A.model n) (productLabels A n T) (clusterScale (A.model n)) hm hfive
      hexpn hε hseparation round hroundGood hroundClose
  have hradius : D.radius = clusterRadius (A.model n) := rfl
  have hradiusLower : (1 : ℝ) / 10 ≤ D.radius := by
    rw [hradius]
    exact one_tenth_le_clusterRadius _ hcard
  have hradiusUpper : D.radius ≤ (1 : ℝ) / 5 := by
    rw [hradius]
    exact clusterRadius_le_one_fifth _ (by omega)
  apply localEmbedding_of_finite_stage (A.model n) D s
    (fun j ↦ A.map n (1, j))
  · dsimp [D, clusterData_of_epsilonRounding]
    rw [mem_epsilonGoodCandidates]
    simpa using hNgood n hngood 1 (one_mem_finiteControl s)
  · intro x hx
    dsimp [D, clusterData_of_epsilonRounding]
    rw [mem_epsilonGoodCandidates]
    exact hNgood n hngood x (mem_finiteControl hx)
  · intro x hx y hy
    dsimp [D, clusterData_of_epsilonRounding]
    rw [mem_epsilonGoodCandidates]
    exact hNgood n hngood (x * y) (mul_mem_finiteControl hx hy)
  · have hone : hammingDistance (A.model n) (A.map n (1, 1)) 1 < 1 / 10 := by
      change hammingDistance (A.model n) (A.map n (1 : K × J)) 1 < 1 / 10
      exact hNone n hnone
    linarith
  · intro x hx y hy
    have hmul := hNmul n hnmul x hx y hy
    linarith
  · intro x hx y hy hxy
    have hsep := hNsep n hnsep x hx y hy hxy
    linarith

/-! ### Fiber control for repairing a low-boundary relation -/

def rowFiber (U : Finset (Y × Y)) (x : Y) : Finset Y :=
  Finset.univ.filter fun y ↦ (x, y) ∈ U

def rowDegree (U : Finset (Y × Y)) (x : Y) : ℕ :=
  (rowFiber Y U x).card

def badRows (U : Finset (Y × Y)) : Finset Y :=
  Finset.univ.filter fun x ↦ rowDegree Y U x ≠ 1

@[simp] theorem mem_rowFiber (U : Finset (Y × Y)) (x y : Y) :
    y ∈ rowFiber Y U x ↔ (x, y) ∈ U := by
  simp [rowFiber]

@[simp] theorem mem_badRows (U : Finset (Y × Y)) (x : Y) :
    x ∈ badRows Y U ↔ rowDegree Y U x ≠ 1 := by
  simp [badRows]

theorem exists_extra_in_row_of_bad_of_graph_mem
    (U : Finset (Y × Y)) (c : Equiv.Perm Y) (x : Y)
    (hbad : rowDegree Y U x ≠ 1) (hgraph : (x, c x) ∈ U) :
    ∃ y : Y, (x, y) ∈ U ∧ y ≠ c x := by
  by_contra h
  push Not at h
  have hfiber : rowFiber Y U x = {c x} := by
    ext y
    constructor
    · intro hy
      rw [mem_rowFiber] at hy
      simp [h y hy]
    · intro hy
      rw [Finset.mem_singleton] at hy
      subst y
      exact (mem_rowFiber Y U x (c x)).2 hgraph
  apply hbad
  rw [rowDegree, hfiber]
  simp

/-- Choose an excess point in a bad row when the original graph point is
retained; elsewhere use the original graph point as a harmless default. -/
noncomputable def rowRepairWitness
    (U : Finset (Y × Y)) (c : Equiv.Perm Y) (x : Y) : Y := by
  classical
  exact if h : rowDegree Y U x ≠ 1 ∧ (x, c x) ∈ U then
    Classical.choose
      (exists_extra_in_row_of_bad_of_graph_mem Y U c x h.1 h.2)
  else c x

theorem rowRepairWitness_mem_of_bad_of_graph_mem
    (U : Finset (Y × Y)) (c : Equiv.Perm Y) (x : Y)
    (hbad : rowDegree Y U x ≠ 1) (hgraph : (x, c x) ∈ U) :
    (x, rowRepairWitness Y U c x) ∈ U ∧
      rowRepairWitness Y U c x ≠ c x := by
  rw [rowRepairWitness, dif_pos ⟨hbad, hgraph⟩]
  exact Classical.choose_spec
    (exists_extra_in_row_of_bad_of_graph_mem Y U c x hbad hgraph)

/-- Each non-singleton row is witnessed by a distinct missing or excess point
relative to the original permutation graph. -/
noncomputable def badRowEditEmbedding
    (U : Finset (Y × Y)) (c : Equiv.Perm Y) :
    {x // x ∈ badRows Y U} ↪ Y × Y where
  toFun x := (x.1, if (x.1, c x.1) ∈ U then
      rowRepairWitness Y U c x.1 else c x.1)
  inj' := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg Prod.fst hxy

theorem badRowEditEmbedding_apply_of_mem
    (U : Finset (Y × Y)) (c : Equiv.Perm Y)
    (x : {x // x ∈ badRows Y U}) (hx : (x.1, c x.1) ∈ U) :
    badRowEditEmbedding Y U c x =
      (x.1, rowRepairWitness Y U c x.1) := by
  simp [badRowEditEmbedding, hx]

theorem badRowEditEmbedding_apply_of_not_mem
    (U : Finset (Y × Y)) (c : Equiv.Perm Y)
    (x : {x // x ∈ badRows Y U}) (hx : (x.1, c x.1) ∉ U) :
    badRowEditEmbedding Y U c x = (x.1, c x.1) := by
  simp [badRowEditEmbedding, hx]

theorem image_badRowEditEmbedding_subset_edits
    (U : Finset (Y × Y)) (c : Equiv.Perm Y) :
    (badRows Y U).attach.map (badRowEditEmbedding Y U c) ⊆
      (permutationGraph Y c \ U) ∪ (U \ permutationGraph Y c) := by
  intro p hp
  rw [Finset.mem_map] at hp
  obtain ⟨x, _, rfl⟩ := hp
  have hbad := (mem_badRows Y U x.1).1 x.2
  by_cases hgraph : (x.1, c x.1) ∈ U
  · rw [badRowEditEmbedding_apply_of_mem Y U c x hgraph]
    rw [Finset.mem_union]
    right
    rw [Finset.mem_sdiff]
    have hw := rowRepairWitness_mem_of_bad_of_graph_mem Y U c x.1 hbad hgraph
    refine ⟨hw.1, ?_⟩
    rw [mem_permutationGraph]
    exact hw.2
  · rw [badRowEditEmbedding_apply_of_not_mem Y U c x hgraph]
    rw [Finset.mem_union]
    left
    rw [Finset.mem_sdiff]
    refine ⟨?_, hgraph⟩
    exact (mem_permutationGraph Y c _).2 rfl

theorem card_badRows_le_edits
    (U : Finset (Y × Y)) (c : Equiv.Perm Y) :
    (badRows Y U).card ≤
      (permutationGraph Y c \ U).card +
        (U \ permutationGraph Y c).card := by
  have hatt : (badRows Y U).attach.card = (badRows Y U).card :=
    Finset.card_attach
  rw [← hatt, ← Finset.card_map (f := badRowEditEmbedding Y U c)]
  calc
    ((badRows Y U).attach.map (badRowEditEmbedding Y U c)).card ≤
        ((permutationGraph Y c \ U) ∪
          (U \ permutationGraph Y c)).card :=
      Finset.card_le_card (image_badRowEditEmbedding_subset_edits Y U c)
    _ ≤ (permutationGraph Y c \ U).card +
        (U \ permutationGraph Y c).card := Finset.card_union_le _ _

def columnFiber (U : Finset (Y × Y)) (y : Y) : Finset Y :=
  Finset.univ.filter fun x ↦ (x, y) ∈ U

def columnDegree (U : Finset (Y × Y)) (y : Y) : ℕ :=
  (columnFiber Y U y).card

def badColumns (U : Finset (Y × Y)) : Finset Y :=
  Finset.univ.filter fun y ↦ columnDegree Y U y ≠ 1

@[simp] theorem mem_columnFiber (U : Finset (Y × Y)) (x y : Y) :
    x ∈ columnFiber Y U y ↔ (x, y) ∈ U := by
  simp [columnFiber]

@[simp] theorem mem_badColumns (U : Finset (Y × Y)) (y : Y) :
    y ∈ badColumns Y U ↔ columnDegree Y U y ≠ 1 := by
  simp [badColumns]

theorem exists_extra_in_column_of_bad_of_graph_mem
    (U : Finset (Y × Y)) (c : Equiv.Perm Y) (y : Y)
    (hbad : columnDegree Y U y ≠ 1) (hgraph : (c.symm y, y) ∈ U) :
    ∃ x : Y, (x, y) ∈ U ∧ x ≠ c.symm y := by
  by_contra h
  push Not at h
  have hfiber : columnFiber Y U y = {c.symm y} := by
    ext x
    constructor
    · intro hx
      rw [mem_columnFiber] at hx
      simp [h x hx]
    · intro hx
      rw [Finset.mem_singleton] at hx
      subst x
      exact (mem_columnFiber Y U (c.symm y) y).2 hgraph
  apply hbad
  rw [columnDegree, hfiber]
  simp

noncomputable def columnRepairWitness
    (U : Finset (Y × Y)) (c : Equiv.Perm Y) (y : Y) : Y := by
  classical
  exact if h : columnDegree Y U y ≠ 1 ∧ (c.symm y, y) ∈ U then
    Classical.choose
      (exists_extra_in_column_of_bad_of_graph_mem Y U c y h.1 h.2)
  else c.symm y

theorem columnRepairWitness_mem_of_bad_of_graph_mem
    (U : Finset (Y × Y)) (c : Equiv.Perm Y) (y : Y)
    (hbad : columnDegree Y U y ≠ 1) (hgraph : (c.symm y, y) ∈ U) :
    (columnRepairWitness Y U c y, y) ∈ U ∧
      columnRepairWitness Y U c y ≠ c.symm y := by
  rw [columnRepairWitness, dif_pos ⟨hbad, hgraph⟩]
  exact Classical.choose_spec
    (exists_extra_in_column_of_bad_of_graph_mem Y U c y hbad hgraph)

noncomputable def badColumnEditEmbedding
    (U : Finset (Y × Y)) (c : Equiv.Perm Y) :
    {y // y ∈ badColumns Y U} ↪ Y × Y where
  toFun y := (if (c.symm y.1, y.1) ∈ U then
      columnRepairWitness Y U c y.1 else c.symm y.1, y.1)
  inj' := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg Prod.snd hxy

theorem badColumnEditEmbedding_apply_of_mem
    (U : Finset (Y × Y)) (c : Equiv.Perm Y)
    (y : {y // y ∈ badColumns Y U}) (hy : (c.symm y.1, y.1) ∈ U) :
    badColumnEditEmbedding Y U c y =
      (columnRepairWitness Y U c y.1, y.1) := by
  simp [badColumnEditEmbedding, hy]

theorem badColumnEditEmbedding_apply_of_not_mem
    (U : Finset (Y × Y)) (c : Equiv.Perm Y)
    (y : {y // y ∈ badColumns Y U}) (hy : (c.symm y.1, y.1) ∉ U) :
    badColumnEditEmbedding Y U c y = (c.symm y.1, y.1) := by
  simp [badColumnEditEmbedding, hy]

theorem image_badColumnEditEmbedding_subset_edits
    (U : Finset (Y × Y)) (c : Equiv.Perm Y) :
    (badColumns Y U).attach.map (badColumnEditEmbedding Y U c) ⊆
      (permutationGraph Y c \ U) ∪ (U \ permutationGraph Y c) := by
  intro p hp
  rw [Finset.mem_map] at hp
  obtain ⟨y, _, rfl⟩ := hp
  have hbad := (mem_badColumns Y U y.1).1 y.2
  by_cases hgraph : (c.symm y.1, y.1) ∈ U
  · rw [badColumnEditEmbedding_apply_of_mem Y U c y hgraph]
    rw [Finset.mem_union]
    right
    rw [Finset.mem_sdiff]
    have hw := columnRepairWitness_mem_of_bad_of_graph_mem
      Y U c y.1 hbad hgraph
    refine ⟨hw.1, ?_⟩
    rw [mem_permutationGraph]
    intro heq
    apply hw.2
    apply c.injective
    simpa using heq.symm
  · rw [badColumnEditEmbedding_apply_of_not_mem Y U c y hgraph]
    rw [Finset.mem_union]
    left
    rw [Finset.mem_sdiff]
    refine ⟨?_, hgraph⟩
    rw [mem_permutationGraph]
    simp

theorem card_badColumns_le_edits
    (U : Finset (Y × Y)) (c : Equiv.Perm Y) :
    (badColumns Y U).card ≤
      (permutationGraph Y c \ U).card +
        (U \ permutationGraph Y c).card := by
  have hatt : (badColumns Y U).attach.card = (badColumns Y U).card :=
    Finset.card_attach
  rw [← hatt, ← Finset.card_map (f := badColumnEditEmbedding Y U c)]
  calc
    ((badColumns Y U).attach.map (badColumnEditEmbedding Y U c)).card ≤
        ((permutationGraph Y c \ U) ∪
          (U \ permutationGraph Y c)).card :=
      Finset.card_le_card (image_badColumnEditEmbedding_subset_edits Y U c)
    _ ≤ (permutationGraph Y c \ U).card +
        (U \ permutationGraph Y c).card := Finset.card_union_le _ _

theorem badFibers_at_most_half_of_edits
    (U : Finset (Y × Y)) (c : Equiv.Perm Y)
    (hedits : 2 * ((permutationGraph Y c \ U).card +
      (U \ permutationGraph Y c).card) ≤ Fintype.card Y) :
    2 * (badRows Y U).card ≤ Fintype.card Y ∧
      2 * (badColumns Y U).card ≤ Fintype.card Y := by
  have hrows := card_badRows_le_edits Y U c
  have hcolumns := card_badColumns_le_edits Y U c
  omega

/-- Points lying in a singleton row and a singleton column form the graph of
a partial bijection. -/
def relationCore (U : Finset (Y × Y)) : Finset (Y × Y) :=
  U.filter fun p ↦ rowDegree Y U p.1 = 1 ∧ columnDegree Y U p.2 = 1

@[simp] theorem mem_relationCore (U : Finset (Y × Y)) (p : Y × Y) :
    p ∈ relationCore Y U ↔ p ∈ U ∧
      rowDegree Y U p.1 = 1 ∧ columnDegree Y U p.2 = 1 := by
  simp [relationCore]

theorem relationCore_right_unique
    (U : Finset (Y × Y)) {x y z : Y}
    (hy : (x, y) ∈ relationCore Y U) (hz : (x, z) ∈ relationCore Y U) :
    y = z := by
  have hydata := (mem_relationCore Y U (x, y)).1 hy
  have hzdata := (mem_relationCore Y U (x, z)).1 hz
  have hyfiber := (mem_rowFiber Y U x y).2 hydata.1
  have hzfiber := (mem_rowFiber Y U x z).2 hzdata.1
  have heq : (rowFiber Y U x).card = 1 := hydata.2.1
  have hcard : (rowFiber Y U x).card ≤ 1 := heq.le
  exact Finset.card_le_one.mp hcard y hyfiber z hzfiber

theorem relationCore_left_unique
    (U : Finset (Y × Y)) {x y z : Y}
    (hx : (x, z) ∈ relationCore Y U) (hy : (y, z) ∈ relationCore Y U) :
    x = y := by
  have hxdata := (mem_relationCore Y U (x, z)).1 hx
  have hydata := (mem_relationCore Y U (y, z)).1 hy
  have hxfiber := (mem_columnFiber Y U x z).2 hxdata.1
  have hyfiber := (mem_columnFiber Y U y z).2 hydata.1
  have heq : (columnFiber Y U z).card = 1 := hxdata.2.2
  have hcard : (columnFiber Y U z).card ≤ 1 := heq.le
  exact Finset.card_le_one.mp hcard x hxfiber y hyfiber

def coreSources (U : Finset (Y × Y)) : Finset Y :=
  (relationCore Y U).image Prod.fst

theorem exists_core_target (U : Finset (Y × Y))
    (x : {x // x ∈ coreSources Y U}) :
    ∃ y : Y, (x.1, y) ∈ relationCore Y U := by
  have hx := x.2
  simp only [coreSources, Finset.mem_image] at hx
  obtain ⟨p, hp, hpx⟩ := hx
  refine ⟨p.2, ?_⟩
  convert hp using 1
  exact Prod.ext hpx.symm rfl

noncomputable def coreTarget (U : Finset (Y × Y))
    (x : {x // x ∈ coreSources Y U}) : Y :=
  Classical.choose (exists_core_target Y U x)

theorem coreTarget_mem (U : Finset (Y × Y))
    (x : {x // x ∈ coreSources Y U}) :
    (x.1, coreTarget Y U x) ∈ relationCore Y U :=
  Classical.choose_spec (exists_core_target Y U x)

theorem coreTarget_injective (U : Finset (Y × Y)) :
    Function.Injective (coreTarget Y U) := by
  intro x y hxy
  apply Subtype.ext
  exact relationCore_left_unique Y U (coreTarget_mem Y U x)
    (hxy ▸ coreTarget_mem Y U y)

/-- The partial bijection carried by the singleton-fiber core extends to a
permutation of the whole finite model. -/
theorem exists_permutation_agreeing_on_core (U : Finset (Y × Y)) :
    ∃ c : Equiv.Perm Y, ∀ p ∈ relationCore Y U, c p.1 = p.2 := by
  let A := {x // x ∈ coreSources Y U}
  let inclusion : A → Y := fun x ↦ x.1
  let target : A → Y := fun x ↦ coreTarget Y U x
  have hinclusion : Function.Injective inclusion := fun _ _ h ↦ Subtype.ext h
  have htarget : Function.Injective target := coreTarget_injective Y U
  obtain ⟨c, hc⟩ :=
    Equiv.Perm.exists_extending_pair inclusion target hinclusion htarget
  refine ⟨c, fun p hp ↦ ?_⟩
  have hsource : p.1 ∈ coreSources Y U := by
    rw [coreSources, Finset.mem_image]
    exact ⟨p, hp, rfl⟩
  let x : A := ⟨p.1, hsource⟩
  have hcx := hc x
  have htargetCore := coreTarget_mem Y U x
  have hunique := relationCore_right_unique Y U htargetCore hp
  exact hcx.trans hunique

noncomputable def repairRelation (U : Finset (Y × Y)) : Equiv.Perm Y :=
  Classical.choose (exists_permutation_agreeing_on_core Y U)

theorem repairRelation_eq_of_mem_core (U : Finset (Y × Y))
    (p : Y × Y) (hp : p ∈ relationCore Y U) :
    repairRelation Y U p.1 = p.2 :=
  Classical.choose_spec (exists_permutation_agreeing_on_core Y U) p hp

theorem core_subset_permutationGraph_repairRelation (U : Finset (Y × Y)) :
    relationCore Y U ⊆ permutationGraph Y (repairRelation Y U) := by
  intro p hp
  rw [mem_permutationGraph]
  exact (repairRelation_eq_of_mem_core Y U p hp).symm

/-- Sources whose original targets lie in a non-singleton column. -/
def badTargetSources (U : Finset (Y × Y))
    (c : Equiv.Perm Y) : Finset Y :=
  (badColumns Y U).map c.symm.toEmbedding

@[simp] theorem mem_badTargetSources (U : Finset (Y × Y))
    (c : Equiv.Perm Y) (x : Y) :
    x ∈ badTargetSources Y U c ↔ c x ∈ badColumns Y U := by
  constructor
  · intro hx
    rw [badTargetSources, Finset.mem_map] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    have hyx : y = c x := by
      simpa using congrArg c hxy
    simpa [hyx] using hy
  · intro hx
    rw [badTargetSources, Finset.mem_map]
    exact ⟨c x, hx, by simp⟩

@[simp] theorem card_badTargetSources (U : Finset (Y × Y))
    (c : Equiv.Perm Y) :
    (badTargetSources Y U c).card = (badColumns Y U).card := by
  simp [badTargetSources]

theorem repairRelation_disagreement_subset
    (U : Finset (Y × Y)) (c : Equiv.Perm Y) :
    hammingDisagreement (repairRelation Y U) c ⊆
      missingSources Y U c ∪
        (badRows Y U ∪ badTargetSources Y U c) := by
  intro x hx
  have hne := (mem_hammingDisagreement (repairRelation Y U) c x).1 hx
  by_cases hgraph : (x, c x) ∈ U
  · by_cases hrow : rowDegree Y U x = 1
    · by_cases hcol : columnDegree Y U (c x) = 1
      · exfalso
        apply hne
        exact repairRelation_eq_of_mem_core Y U (x, c x)
          ((mem_relationCore Y U (x, c x)).2 ⟨hgraph, hrow, hcol⟩)
      · exact Finset.mem_union_right _ <| Finset.mem_union_right _ <|
          (mem_badTargetSources Y U c x).2 ((mem_badColumns Y U (c x)).2 hcol)
    · exact Finset.mem_union_right _ <| Finset.mem_union_left _ <|
        (mem_badRows Y U x).2 hrow
  · exact Finset.mem_union_left _ <| (mem_missingSources Y U c x).2 hgraph

theorem card_repairRelation_disagreement_le
    (U : Finset (Y × Y)) (c : Equiv.Perm Y) :
    (hammingDisagreement (repairRelation Y U) c).card ≤
      (permutationGraph Y c \ U).card +
        2 * ((permutationGraph Y c \ U).card +
          (U \ permutationGraph Y c).card) := by
  have hcover := Finset.card_le_card (repairRelation_disagreement_subset Y U c)
  have hunion₁ := Finset.card_union_le (missingSources Y U c)
    (badRows Y U ∪ badTargetSources Y U c)
  have hunion₂ := Finset.card_union_le (badRows Y U) (badTargetSources Y U c)
  have hmissing := card_missingSources Y U c
  have hrows := card_badRows_le_edits Y U c
  have hcolumns := card_badColumns_le_edits Y U c
  rw [card_badTargetSources] at hunion₂
  omega

theorem hammingDistance_repairRelation_le
    (U : Finset (Y × Y)) (c : Equiv.Perm Y) :
    hammingDistance Y (repairRelation Y U) c ≤
      (((permutationGraph Y c \ U).card +
        2 * ((permutationGraph Y c \ U).card +
          (U \ permutationGraph Y c).card) : ℕ) : ℝ) /
            Fintype.card Y := by
  rw [hammingDistance]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast card_repairRelation_disagreement_le Y U c

theorem missingSources_repairRelation_subset
    (U : Finset (Y × Y)) (c : Equiv.Perm Y) :
    missingSources Y U (repairRelation Y U) ⊆
      hammingDisagreement (repairRelation Y U) c ∪ missingSources Y U c := by
  intro x hx
  rw [mem_missingSources] at hx
  by_cases hne : repairRelation Y U x ≠ c x
  · exact Finset.mem_union_left _
      ((mem_hammingDisagreement (repairRelation Y U) c x).2 hne)
  · apply Finset.mem_union_right
    rw [mem_missingSources]
    simpa [not_ne_iff.mp hne] using hx

theorem card_graph_repair_missing_le
    (U : Finset (Y × Y)) (c : Equiv.Perm Y) :
    (permutationGraph Y (repairRelation Y U) \ U).card ≤
      (hammingDisagreement (repairRelation Y U) c).card +
        (permutationGraph Y c \ U).card := by
  rw [← card_missingSources Y U (repairRelation Y U),
    ← card_missingSources Y U c]
  exact (Finset.card_le_card (missingSources_repairRelation_subset Y U c)).trans
    (Finset.card_union_le _ _)

def disagreementGraph (r c : Equiv.Perm Y) : Finset (Y × Y) :=
  (hammingDisagreement r c).map
    ⟨fun x ↦ (x, c x), fun _ _ h ↦ congrArg Prod.fst h⟩

@[simp] theorem card_disagreementGraph (r c : Equiv.Perm Y) :
    (disagreementGraph Y r c).card = (hammingDisagreement r c).card := by
  simp [disagreementGraph]

theorem repairRelation_excess_subset
    (U : Finset (Y × Y)) (c : Equiv.Perm Y) :
    U \ permutationGraph Y (repairRelation Y U) ⊆
      (U \ permutationGraph Y c) ∪
        disagreementGraph Y (repairRelation Y U) c := by
  intro p hp
  rw [Finset.mem_sdiff] at hp
  by_cases horiginal : p ∈ permutationGraph Y c
  · apply Finset.mem_union_right
    rw [disagreementGraph, Finset.mem_map]
    have hc := (mem_permutationGraph Y c p).1 horiginal
    refine ⟨p.1, ?_, ?_⟩
    · rw [mem_hammingDisagreement]
      intro heq
      apply hp.2
      rw [mem_permutationGraph]
      exact hc.trans heq.symm
    · exact Prod.ext rfl hc.symm
  · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hp.1, horiginal⟩)

theorem card_graph_repair_excess_le
    (U : Finset (Y × Y)) (c : Equiv.Perm Y) :
    (U \ permutationGraph Y (repairRelation Y U)).card ≤
      (U \ permutationGraph Y c).card +
        (hammingDisagreement (repairRelation Y U) c).card := by
  have hsubset := Finset.card_le_card (repairRelation_excess_subset Y U c)
  have hunion := Finset.card_union_le (U \ permutationGraph Y c)
    (disagreementGraph Y (repairRelation Y U) c)
  rw [card_disagreementGraph] at hunion
  omega

theorem card_repairRelation_edits_le
    (U : Finset (Y × Y)) (c : Equiv.Perm Y) :
    (permutationGraph Y (repairRelation Y U) \ U).card +
      (U \ permutationGraph Y (repairRelation Y U)).card ≤
        7 * ((permutationGraph Y c \ U).card +
          (U \ permutationGraph Y c).card) := by
  have hmissing := card_graph_repair_missing_le Y U c
  have hexcess := card_graph_repair_excess_le Y U c
  have hdisagreement := card_repairRelation_disagreement_le Y U c
  omega

/-- Bad arcs whose graph point and its diagonal translate lie on opposite
sides of the relation. -/
def crossingBadArcs (S : Finset (Equiv.Perm Y)) (U : Finset (Y × Y))
    (c : Equiv.Perm Y) : Finset (Arc Y) :=
  (badArcs Y S c).filter fun p ↦
    ((p.2, c p.2) ∈ U ∧ (p.1 p.2, p.1 (c p.2)) ∉ U) ∨
      ((p.2, c p.2) ∉ U ∧ (p.1 p.2, p.1 (c p.2)) ∈ U)

/-- Bad arcs whose source graph point and diagonal translate are both absent
from the relation. -/
def missingBadArcs (S : Finset (Equiv.Perm Y)) (U : Finset (Y × Y))
    (c : Equiv.Perm Y) : Finset (Arc Y) :=
  (badArcs Y S c).filter fun p ↦
    (p.2, c p.2) ∉ U ∧ (p.1 p.2, p.1 (c p.2)) ∉ U

/-- Bad arcs whose source graph point and diagonal translate are both in the
relation.  Since the arc is bad, the translated point is excess relation
mass, not a point of the permutation graph. -/
def excessBadArcs (S : Finset (Equiv.Perm Y)) (U : Finset (Y × Y))
    (c : Equiv.Perm Y) : Finset (Arc Y) :=
  (badArcs Y S c).filter fun p ↦
    (p.2, c p.2) ∈ U ∧ (p.1 p.2, p.1 (c p.2)) ∈ U

/-- The three cases above exhaust every defect of a permutation relative to
a comparison relation. -/
theorem badArcs_subset_crossing_union_missing_union_excess
    (S : Finset (Equiv.Perm Y)) (U : Finset (Y × Y))
    (c : Equiv.Perm Y) :
    badArcs Y S c ⊆
      crossingBadArcs Y S U c ∪
        (missingBadArcs Y S U c ∪ excessBadArcs Y S U c) := by
  intro p hp
  by_cases hq : (p.2, c p.2) ∈ U
  · by_cases hr : (p.1 p.2, p.1 (c p.2)) ∈ U
    · exact Finset.mem_union_right _ <| Finset.mem_union_right _ <| by
        simp [excessBadArcs, hp, hq, hr]
    · exact Finset.mem_union_left _ <| by
        simp [crossingBadArcs, hp, hq, hr]
  · by_cases hr : (p.1 p.2, p.1 (c p.2)) ∈ U
    · exact Finset.mem_union_left _ <| by
        simp [crossingBadArcs, hp, hq, hr]
    · exact Finset.mem_union_right _ <| Finset.mem_union_left _ <| by
        simp [missingBadArcs, hp, hq, hr]

/-- Insert an arc as its source point on the graph of `c`. -/
def graphArcEmbedding (c : Equiv.Perm Y) :
    Arc Y ↪ Equiv.Perm Y × (Y × Y) where
  toFun p := (p.1, (p.2, c p.2))
  inj' := by
    intro p q hpq
    have hs : p.1 = q.1 :=
      congrArg (fun r : Equiv.Perm Y × (Y × Y) ↦ r.1) hpq
    have hx : p.2 = q.2 :=
      congrArg (fun r : Equiv.Perm Y × (Y × Y) ↦ r.2.1) hpq
    exact Prod.ext hs hx

theorem card_crossingBadArcs_le_relationBoundary
    (S : Finset (Equiv.Perm Y)) (U : Finset (Y × Y))
    (c : Equiv.Perm Y) :
    (crossingBadArcs Y S U c).card ≤ (relationBoundary Y S U).card := by
  rw [← Finset.card_map (f := graphArcEmbedding Y c)]
  apply Finset.card_le_card
  intro q hq
  rw [Finset.mem_map] at hq
  obtain ⟨p, hp, rfl⟩ := hq
  rw [mem_relationBoundary]
  have hpdata : p ∈ badArcs Y S c ∧
      (((p.2, c p.2) ∈ U ∧ (p.1 p.2, p.1 (c p.2)) ∉ U) ∨
        ((p.2, c p.2) ∉ U ∧ (p.1 p.2, p.1 (c p.2)) ∈ U)) := by
    simpa [crossingBadArcs] using hp
  have hpbad := hpdata.1
  have hpS := (mem_badArcs Y S c p).1 hpbad |>.1
  refine ⟨hpS, ?_⟩
  change ((p.2, c p.2) ∈ U ∧ (p.1 p.2, p.1 (c p.2)) ∉ U) ∨
    ((p.2, c p.2) ∉ U ∧ (p.1 p.2, p.1 (c p.2)) ∈ U)
  exact hpdata.2

theorem missingBadArcs_subset_product_missingSources
    (S : Finset (Equiv.Perm Y)) (U : Finset (Y × Y))
    (c : Equiv.Perm Y) :
    missingBadArcs Y S U c ⊆ S.product (missingSources Y U c) := by
  intro p hp
  have hpdata : p ∈ badArcs Y S c ∧
      (p.2, c p.2) ∉ U ∧ (p.1 p.2, p.1 (c p.2)) ∉ U := by
    simpa [missingBadArcs] using hp
  have hpbad := hpdata.1
  have hpS := (mem_badArcs Y S c p).1 hpbad |>.1
  exact Finset.mem_product.mpr
    ⟨hpS, (mem_missingSources Y U c p.2).2 hpdata.2.1⟩

theorem card_missingBadArcs_le
    (S : Finset (Equiv.Perm Y)) (U : Finset (Y × Y))
    (c : Equiv.Perm Y) :
    (missingBadArcs Y S U c).card ≤
      S.card * (permutationGraph Y c \ U).card := by
  calc
    (missingBadArcs Y S U c).card ≤
        (S.product (missingSources Y U c)).card :=
      Finset.card_le_card (missingBadArcs_subset_product_missingSources Y S U c)
    _ = S.card * (permutationGraph Y c \ U).card := by
      change (S ×ˢ missingSources Y U c).card = _
      rw [Finset.card_product, card_missingSources]

/-- Move an arc's graph point diagonally by its label. -/
def translatedGraphArcEmbedding (c : Equiv.Perm Y) :
    Arc Y ↪ Equiv.Perm Y × (Y × Y) where
  toFun p := (p.1, (p.1 p.2, p.1 (c p.2)))
  inj' := by
    intro p q hpq
    have hs : p.1 = q.1 :=
      congrArg (fun r : Equiv.Perm Y × (Y × Y) ↦ r.1) hpq
    apply Prod.ext hs
    apply p.1.injective
    have hfirst : p.1 p.2 = q.1 q.2 := congrArg (fun r ↦ r.2.1) hpq
    simpa [hs] using hfirst

theorem mapped_excessBadArcs_subset_product_excess
    (S : Finset (Equiv.Perm Y)) (U : Finset (Y × Y))
    (c : Equiv.Perm Y) :
    (excessBadArcs Y S U c).map (translatedGraphArcEmbedding Y c) ⊆
      S.product (U \ permutationGraph Y c) := by
  intro q hq
  rw [Finset.mem_map] at hq
  obtain ⟨p, hp, rfl⟩ := hq
  dsimp [translatedGraphArcEmbedding]
  rw [Finset.mem_product, Finset.mem_sdiff]
  have hpdata : p ∈ badArcs Y S c ∧
      (p.2, c p.2) ∈ U ∧ (p.1 p.2, p.1 (c p.2)) ∈ U := by
    simpa [excessBadArcs] using hp
  have hpbad := hpdata.1
  have hdata := (mem_badArcs Y S c p).1 hpbad
  refine ⟨hdata.1, hpdata.2.2, ?_⟩
  rw [mem_permutationGraph]
  exact hdata.2.symm

theorem card_excessBadArcs_le
    (S : Finset (Equiv.Perm Y)) (U : Finset (Y × Y))
    (c : Equiv.Perm Y) :
    (excessBadArcs Y S U c).card ≤
      S.card * (U \ permutationGraph Y c).card := by
  rw [← Finset.card_map (f := translatedGraphArcEmbedding Y c)]
  calc
    ((excessBadArcs Y S U c).map
        (translatedGraphArcEmbedding Y c)).card ≤
        (S.product (U \ permutationGraph Y c)).card :=
      Finset.card_le_card (mapped_excessBadArcs_subset_product_excess Y S U c)
    _ = S.card * (U \ permutationGraph Y c).card := by
      change (S ×ˢ (U \ permutationGraph Y c)).card = _
      exact Finset.card_product S (U \ permutationGraph Y c)

/-- A relation with small diagonal boundary and small symmetric difference
from a permutation graph gives a permutation with few commutation defects. -/
theorem card_badArcs_le_relationBoundary_add_edits
    (S : Finset (Equiv.Perm Y)) (U : Finset (Y × Y))
    (c : Equiv.Perm Y) :
    (badArcs Y S c).card ≤ (relationBoundary Y S U).card +
      S.card * ((permutationGraph Y c \ U).card +
        (U \ permutationGraph Y c).card) := by
  have hcover := badArcs_subset_crossing_union_missing_union_excess Y S U c
  have hcardCover := Finset.card_le_card hcover
  have hunion₁ := Finset.card_union_le (crossingBadArcs Y S U c)
    (missingBadArcs Y S U c ∪ excessBadArcs Y S U c)
  have hunion₂ := Finset.card_union_le (missingBadArcs Y S U c)
    (excessBadArcs Y S U c)
  have hcross := card_crossingBadArcs_le_relationBoundary Y S U c
  have hmissing := card_missingBadArcs_le Y S U c
  have hexcess := card_excessBadArcs_le Y S U c
  rw [Nat.mul_add]
  omega

/-- The singleton-core repair has controlled commutation defect.  This bound
uses only finite combinatorics; the later expander-fiber argument sharpens the
edit term from the original relation error to its new boundary error. -/
theorem card_badArcs_repairRelation_le
    (S : Finset (Equiv.Perm Y)) (U : Finset (Y × Y))
    (c : Equiv.Perm Y) :
    (badArcs Y S (repairRelation Y U)).card ≤
      (relationBoundary Y S U).card +
        7 * S.card * ((permutationGraph Y c \ U).card +
          (U \ permutationGraph Y c).card) := by
  have hbase := card_badArcs_le_relationBoundary_add_edits Y S U
    (repairRelation Y U)
  have hedits := card_repairRelation_edits_le Y U c
  nlinarith

/-! ### Projection variation -/

/-- Points in a row whose membership changes under one diagonal label step. -/
def rowTransition (U : Finset (Y × Y)) (s : Equiv.Perm Y) (x : Y) :
    Finset Y :=
  Finset.univ.filter fun y ↦
    ((x, y) ∈ U) ≠ ((s x, s y) ∈ U)

/-- The pullback to row `x` of the relation fiber over `s x`. -/
def nextRowFiber (U : Finset (Y × Y)) (s : Equiv.Perm Y) (x : Y) :
    Finset Y :=
  Finset.univ.filter fun y ↦ (s x, s y) ∈ U

theorem card_nextRowFiber (U : Finset (Y × Y))
    (s : Equiv.Perm Y) (x : Y) :
    (nextRowFiber Y U s x).card = rowDegree Y U (s x) := by
  let e : Y ↪ Y := s.toEmbedding
  have hmap : (nextRowFiber Y U s x).map e = rowFiber Y U (s x) := by
    ext z
    constructor
    · intro hz
      rw [Finset.mem_map] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      rw [show y ∈ nextRowFiber Y U s x ↔ (s x, s y) ∈ U by
        simp [nextRowFiber]] at hy
      rw [mem_rowFiber]
      change (s x, s y) ∈ U
      exact hy
    · intro hz
      rw [Finset.mem_map]
      refine ⟨s.symm z, ?_, by simp [e]⟩
      simpa [nextRowFiber, rowFiber] using hz
  rw [rowDegree, ← hmap, Finset.card_map]

theorem rowTransition_eq_filter_membership_ne
    (U : Finset (Y × Y)) (s : Equiv.Perm Y) (x : Y) :
    rowTransition Y U s x = Finset.univ.filter fun y ↦
      (y ∈ rowFiber Y U x) ≠ (y ∈ nextRowFiber Y U s x) := by
  ext y
  simp [rowTransition, rowFiber, nextRowFiber]

theorem natDist_card_le_membership_changes
    {α : Type} [Fintype α] [DecidableEq α] (A B : Finset α) :
    Nat.dist A.card B.card ≤
      (Finset.univ.filter fun x ↦ (x ∈ A) ≠ (x ∈ B)).card := by
  let D := Finset.univ.filter fun x ↦ (x ∈ A) ≠ (x ∈ B)
  have hD : D = (A \ B) ∪ (B \ A) := by
    ext x
    by_cases hA : x ∈ A <;> by_cases hB : x ∈ B <;>
      simp [D, hA, hB]
  have hdisjoint : Disjoint (A \ B) (B \ A) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    rw [Finset.mem_sdiff] at hx hy
    exact hx.2 hy.1
  have hAcard := Finset.card_sdiff_add_card_inter A B
  have hBcard := Finset.card_sdiff_add_card_inter B A
  have hinter : (A ∩ B).card = (B ∩ A).card := by
    rw [Finset.inter_comm]
  rw [show (Finset.univ.filter fun x ↦ (x ∈ A) ≠ (x ∈ B)) = D from rfl,
    hD, Finset.card_union_of_disjoint hdisjoint]
  by_cases hle : A.card ≤ B.card
  · rw [Nat.dist_eq_sub_of_le hle]
    omega
  · have hle' : B.card ≤ A.card := by omega
    rw [Nat.dist_eq_sub_of_le_right hle']
    omega

theorem rowDegree_dist_le_transition
    (U : Finset (Y × Y)) (s : Equiv.Perm Y) (x : Y) :
    Nat.dist (rowDegree Y U x) (rowDegree Y U (s x)) ≤
      (rowTransition Y U s x).card := by
  rw [← card_nextRowFiber Y U s x,
    rowDegree, rowTransition_eq_filter_membership_ne]
  exact natDist_card_le_membership_changes
    (rowFiber Y U x) (nextRowFiber Y U s x)

theorem sum_card_rowTransition
    (S : Finset (Equiv.Perm Y)) (U : Finset (Y × Y)) :
    ∑ p ∈ S.product (Finset.univ : Finset Y),
      (rowTransition Y U p.1 p.2).card =
        (relationBoundary Y S U).card := by
  classical
  have hfiber := Finset.sum_card_fiberwise_eq_card_filter
    (relationBoundary Y S U) (S.product (Finset.univ : Finset Y))
      (fun p : Equiv.Perm Y × (Y × Y) ↦ (p.1, p.2.1))
  calc
    ∑ p ∈ S.product (Finset.univ : Finset Y),
        (rowTransition Y U p.1 p.2).card =
      ∑ p ∈ S.product (Finset.univ : Finset Y),
        ((relationBoundary Y S U).filter fun q ↦
          (q.1, q.2.1) = p).card := by
      apply Finset.sum_congr rfl
      intro p hp
      rcases p with ⟨s, x⟩
      have hs : s ∈ S := (Finset.mem_product.mp hp).1
      let e : Y ↪ Equiv.Perm Y × (Y × Y) :=
        ⟨fun y ↦ (s, (x, y)), fun _ _ h ↦ congrArg (fun q ↦ q.2.2) h⟩
      rw [← Finset.card_map (f := e)]
      apply congrArg Finset.card
      ext q
      constructor
      · intro hq
        rw [Finset.mem_map] at hq
        obtain ⟨z, hz, rfl⟩ := hq
        rw [Finset.mem_filter]
        refine ⟨?_, rfl⟩
        rw [mem_relationBoundary]
        refine ⟨hs, ?_⟩
        dsimp [e, diagonalAction]
        by_cases h₁ : (x, z) ∈ U <;> by_cases h₂ : (s x, s z) ∈ U <;>
          simp [rowTransition, h₁, h₂] at hz ⊢
      · intro hq
        rw [Finset.mem_filter] at hq
        obtain ⟨hboundary, heq⟩ := hq
        have hlabel : q.1 = s := congrArg Prod.fst heq
        have hsource : q.2.1 = x := congrArg Prod.snd heq
        let z := q.2.2
        have hqEq : q = (s, (x, z)) :=
          Prod.ext hlabel (Prod.ext hsource rfl)
        rw [hqEq] at hboundary ⊢
        rw [Finset.mem_map]
        refine ⟨z, ?_, rfl⟩
        have hcross := (mem_relationBoundary Y S U _).1 hboundary |>.2
        by_cases h₁ : (x, z) ∈ U <;> by_cases h₂ : (s x, s z) ∈ U <;>
          simp [rowTransition, diagonalAction, h₁, h₂] at hcross ⊢
    _ = ((relationBoundary Y S U).filter fun q ↦
        (q.1, q.2.1) ∈ S.product (Finset.univ : Finset Y)).card := hfiber
    _ = (relationBoundary Y S U).card := by
      apply congrArg Finset.card
      ext q
      simp only [Finset.mem_filter]
      constructor
      · exact fun hq ↦ hq.1
      · intro hq
        refine ⟨hq, Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩⟩
        exact (mem_relationBoundary Y S U q).1 hq |>.1

def rowDegreeVariation (S : Finset (Equiv.Perm Y))
    (U : Finset (Y × Y)) : ℕ :=
  ∑ p ∈ S.product (Finset.univ : Finset Y),
    Nat.dist (rowDegree Y U p.2) (rowDegree Y U (p.1 p.2))

theorem rowDegreeVariation_le_relationBoundary
    (S : Finset (Equiv.Perm Y)) (U : Finset (Y × Y)) :
    rowDegreeVariation Y S U ≤ (relationBoundary Y S U).card := by
  calc
    rowDegreeVariation Y S U ≤
        ∑ p ∈ S.product (Finset.univ : Finset Y),
          (rowTransition Y U p.1 p.2).card := by
      unfold rowDegreeVariation
      apply Finset.sum_le_sum
      intro p _
      exact rowDegree_dist_le_transition Y U p.1 p.2
    _ = (relationBoundary Y S U).card := sum_card_rowTransition Y S U

/-- Total distance of row multiplicities from the value one. -/
def rowFiberDeviation (U : Finset (Y × Y)) : ℕ :=
  ∑ x : Y, Nat.dist (rowDegree Y U x) 1

/-- Total distance of column multiplicities from the value one. -/
def columnFiberDeviation (U : Finset (Y × Y)) : ℕ :=
  ∑ y : Y, Nat.dist (columnDegree Y U y) 1

theorem one_le_dist_one_of_ne_one {d : ℕ} (hd : d ≠ 1) :
    1 ≤ Nat.dist d 1 := by
  by_cases hd0 : d = 0
  · subst d
    decide
  · have htwo : 2 ≤ d := by omega
    rw [Nat.dist_eq_sub_of_le_right (by omega)]
    omega

theorem value_le_two_mul_dist_one_of_ne_one {d : ℕ} (hd : d ≠ 1) :
    d ≤ 2 * Nat.dist d 1 := by
  by_cases hd0 : d = 0
  · simp [hd0]
  · have htwo : 2 ≤ d := by omega
    rw [Nat.dist_eq_sub_of_le_right (by omega)]
    omega

theorem card_badRows_le_rowFiberDeviation (U : Finset (Y × Y)) :
    (badRows Y U).card ≤ rowFiberDeviation Y U := by
  calc
    (badRows Y U).card = ∑ _ ∈ badRows Y U, 1 := by simp
    _ ≤ ∑ x ∈ badRows Y U, Nat.dist (rowDegree Y U x) 1 := by
      apply Finset.sum_le_sum
      intro x hx
      exact one_le_dist_one_of_ne_one ((mem_badRows Y U x).1 hx)
    _ ≤ ∑ x : Y, Nat.dist (rowDegree Y U x) 1 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ ↦ Nat.zero_le _)
    _ = rowFiberDeviation Y U := rfl

theorem card_badColumns_le_columnFiberDeviation (U : Finset (Y × Y)) :
    (badColumns Y U).card ≤ columnFiberDeviation Y U := by
  calc
    (badColumns Y U).card = ∑ _ ∈ badColumns Y U, 1 := by simp
    _ ≤ ∑ y ∈ badColumns Y U, Nat.dist (columnDegree Y U y) 1 := by
      apply Finset.sum_le_sum
      intro y hy
      exact one_le_dist_one_of_ne_one ((mem_badColumns Y U y).1 hy)
    _ ≤ ∑ y : Y, Nat.dist (columnDegree Y U y) 1 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ ↦ Nat.zero_le _)
    _ = columnFiberDeviation Y U := rfl

theorem sum_badRows_rowDegree_le (U : Finset (Y × Y)) :
    ∑ x ∈ badRows Y U, rowDegree Y U x ≤ 2 * rowFiberDeviation Y U := by
  calc
    ∑ x ∈ badRows Y U, rowDegree Y U x ≤
        ∑ x ∈ badRows Y U, 2 * Nat.dist (rowDegree Y U x) 1 := by
      apply Finset.sum_le_sum
      intro x hx
      exact value_le_two_mul_dist_one_of_ne_one ((mem_badRows Y U x).1 hx)
    _ = 2 * ∑ x ∈ badRows Y U, Nat.dist (rowDegree Y U x) 1 := by
      rw [Finset.mul_sum]
    _ ≤ 2 * rowFiberDeviation Y U := by
      apply Nat.mul_le_mul_left
      unfold rowFiberDeviation
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ ↦ Nat.zero_le _)

theorem sum_badColumns_columnDegree_le (U : Finset (Y × Y)) :
    ∑ y ∈ badColumns Y U, columnDegree Y U y ≤
      2 * columnFiberDeviation Y U := by
  calc
    ∑ y ∈ badColumns Y U, columnDegree Y U y ≤
        ∑ y ∈ badColumns Y U, 2 * Nat.dist (columnDegree Y U y) 1 := by
      apply Finset.sum_le_sum
      intro y hy
      exact value_le_two_mul_dist_one_of_ne_one ((mem_badColumns Y U y).1 hy)
    _ = 2 * ∑ y ∈ badColumns Y U, Nat.dist (columnDegree Y U y) 1 := by
      rw [Finset.mul_sum]
    _ ≤ 2 * columnFiberDeviation Y U := by
      apply Nat.mul_le_mul_left
      unfold columnFiberDeviation
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ ↦ Nat.zero_le _)

def columnTransition (U : Finset (Y × Y)) (s : Equiv.Perm Y) (y : Y) :
    Finset Y :=
  Finset.univ.filter fun x ↦
    ((x, y) ∈ U) ≠ ((s x, s y) ∈ U)

def nextColumnFiber (U : Finset (Y × Y))
    (s : Equiv.Perm Y) (y : Y) : Finset Y :=
  Finset.univ.filter fun x ↦ (s x, s y) ∈ U

theorem card_nextColumnFiber (U : Finset (Y × Y))
    (s : Equiv.Perm Y) (y : Y) :
    (nextColumnFiber Y U s y).card = columnDegree Y U (s y) := by
  let e : Y ↪ Y := s.toEmbedding
  have hmap : (nextColumnFiber Y U s y).map e = columnFiber Y U (s y) := by
    ext z
    constructor
    · intro hz
      rw [Finset.mem_map] at hz
      obtain ⟨x, hx, rfl⟩ := hz
      rw [show x ∈ nextColumnFiber Y U s y ↔ (s x, s y) ∈ U by
        simp [nextColumnFiber]] at hx
      rw [mem_columnFiber]
      change (s x, s y) ∈ U
      exact hx
    · intro hz
      rw [Finset.mem_map]
      refine ⟨s.symm z, ?_, by simp [e]⟩
      simpa [nextColumnFiber, columnFiber] using hz
  rw [columnDegree, ← hmap, Finset.card_map]

theorem columnTransition_eq_filter_membership_ne
    (U : Finset (Y × Y)) (s : Equiv.Perm Y) (y : Y) :
    columnTransition Y U s y = Finset.univ.filter fun x ↦
      (x ∈ columnFiber Y U y) ≠ (x ∈ nextColumnFiber Y U s y) := by
  ext x
  simp [columnTransition, columnFiber, nextColumnFiber]

theorem columnDegree_dist_le_transition
    (U : Finset (Y × Y)) (s : Equiv.Perm Y) (y : Y) :
    Nat.dist (columnDegree Y U y) (columnDegree Y U (s y)) ≤
      (columnTransition Y U s y).card := by
  rw [← card_nextColumnFiber Y U s y,
    columnDegree, columnTransition_eq_filter_membership_ne]
  exact natDist_card_le_membership_changes
    (columnFiber Y U y) (nextColumnFiber Y U s y)

theorem sum_card_columnTransition
    (S : Finset (Equiv.Perm Y)) (U : Finset (Y × Y)) :
    ∑ p ∈ S.product (Finset.univ : Finset Y),
      (columnTransition Y U p.1 p.2).card =
        (relationBoundary Y S U).card := by
  classical
  have hfiber := Finset.sum_card_fiberwise_eq_card_filter
    (relationBoundary Y S U) (S.product (Finset.univ : Finset Y))
      (fun p : Equiv.Perm Y × (Y × Y) ↦ (p.1, p.2.2))
  calc
    ∑ p ∈ S.product (Finset.univ : Finset Y),
        (columnTransition Y U p.1 p.2).card =
      ∑ p ∈ S.product (Finset.univ : Finset Y),
        ((relationBoundary Y S U).filter fun q ↦
          (q.1, q.2.2) = p).card := by
      apply Finset.sum_congr rfl
      intro p hp
      rcases p with ⟨s, y⟩
      have hs : s ∈ S := (Finset.mem_product.mp hp).1
      let e : Y ↪ Equiv.Perm Y × (Y × Y) :=
        ⟨fun x ↦ (s, (x, y)), fun _ _ h ↦ congrArg (fun q ↦ q.2.1) h⟩
      rw [← Finset.card_map (f := e)]
      apply congrArg Finset.card
      ext q
      constructor
      · intro hq
        rw [Finset.mem_map] at hq
        obtain ⟨x, hx, rfl⟩ := hq
        rw [Finset.mem_filter]
        refine ⟨?_, rfl⟩
        rw [mem_relationBoundary]
        refine ⟨hs, ?_⟩
        dsimp [e, diagonalAction]
        by_cases h₁ : (x, y) ∈ U <;> by_cases h₂ : (s x, s y) ∈ U <;>
          simp [columnTransition, h₁, h₂] at hx ⊢
      · intro hq
        rw [Finset.mem_filter] at hq
        obtain ⟨hboundary, heq⟩ := hq
        have hlabel : q.1 = s := congrArg Prod.fst heq
        have htarget : q.2.2 = y := congrArg Prod.snd heq
        let x := q.2.1
        have hqEq : q = (s, (x, y)) :=
          Prod.ext hlabel (Prod.ext rfl htarget)
        rw [hqEq] at hboundary ⊢
        rw [Finset.mem_map]
        refine ⟨x, ?_, rfl⟩
        have hcross := (mem_relationBoundary Y S U _).1 hboundary |>.2
        by_cases h₁ : (x, y) ∈ U <;> by_cases h₂ : (s x, s y) ∈ U <;>
          simp [columnTransition, diagonalAction, h₁, h₂] at hcross ⊢
    _ = ((relationBoundary Y S U).filter fun q ↦
        (q.1, q.2.2) ∈ S.product (Finset.univ : Finset Y)).card := hfiber
    _ = (relationBoundary Y S U).card := by
      apply congrArg Finset.card
      ext q
      simp only [Finset.mem_filter]
      constructor
      · exact fun hq ↦ hq.1
      · intro hq
        refine ⟨hq, Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩⟩
        exact (mem_relationBoundary Y S U q).1 hq |>.1

def columnDegreeVariation (S : Finset (Equiv.Perm Y))
    (U : Finset (Y × Y)) : ℕ :=
  ∑ p ∈ S.product (Finset.univ : Finset Y),
    Nat.dist (columnDegree Y U p.2) (columnDegree Y U (p.1 p.2))

theorem columnDegreeVariation_le_relationBoundary
    (S : Finset (Equiv.Perm Y)) (U : Finset (Y × Y)) :
    columnDegreeVariation Y S U ≤ (relationBoundary Y S U).card := by
  calc
    columnDegreeVariation Y S U ≤
        ∑ p ∈ S.product (Finset.univ : Finset Y),
          (columnTransition Y U p.1 p.2).card := by
      unfold columnDegreeVariation
      apply Finset.sum_le_sum
      intro p _
      exact columnDegree_dist_le_transition Y U p.1 p.2
    _ = (relationBoundary Y S U).card := sum_card_columnTransition Y S U

/-- Directed `ℓ¹` variation of a natural-valued function under the labels. -/
def natLabelVariation (S : Finset (Equiv.Perm Y)) (g : Y → ℕ) : ℕ :=
  ∑ p ∈ S.product (Finset.univ : Finset Y),
    Nat.dist (g p.2) (g (p.1 p.2))

/-- The median-one instance of the standard `ℓ¹` Poincaré inequality.  This
is proved from a Cheeger bound below; it is named separately because it is the
exact finite statement used twice for the row and column multiplicities. -/
def HasL1PoincareAtOne (S : Finset (Equiv.Perm Y)) (h : ℝ) : Prop :=
  0 < h ∧ ∀ g : Y → ℕ,
    2 * (Finset.univ.filter fun x ↦ g x < 1).card ≤ Fintype.card Y →
    2 * (Finset.univ.filter fun x ↦ 1 < g x).card ≤ Fintype.card Y →
    h * (∑ x : Y, Nat.dist (g x) 1 : ℕ) ≤ natLabelVariation Y S g

theorem abs_natCast_sub_natCast_eq_dist (a b : ℕ) :
    |(a : ℝ) - (b : ℝ)| = (Nat.dist a b : ℝ) := by
  rcases le_total a b with hab | hba
  · rw [Nat.dist_eq_sub_of_le hab, abs_of_nonpos]
    · rw [Nat.cast_sub hab]
      ring
    · exact sub_nonpos.mpr (by exact_mod_cast hab)
  · rw [Nat.dist_eq_sub_of_le_right hba, abs_of_nonneg]
    · rw [Nat.cast_sub hba]
    · exact sub_nonneg.mpr (by exact_mod_cast hba)

theorem hasL1PoincareAtOne_of_cheeger
    (S : Finset (Equiv.Perm Y)) {h : ℝ}
    (hcheeger : DirectedCoarea.HasCheegerLowerBound Y S h) :
    HasL1PoincareAtOne Y S h := by
  refine ⟨hcheeger.1, ?_⟩
  intro g hlower hupper
  have hmedian : FiniteMultiGraph.IsMedian (fun x ↦ (g x : ℝ)) 1 := by
    constructor
    · have heq : (Finset.univ.filter fun x ↦ (1 : ℝ) < (g x : ℝ)) =
          Finset.univ.filter fun x ↦ (1 : ℕ) < g x := by
        ext x
        simp
      rw [heq]
      exact hupper
    · have heq : (Finset.univ.filter fun x ↦ (g x : ℝ) < (1 : ℝ)) =
          Finset.univ.filter fun x ↦ g x < (1 : ℕ) := by
        ext x
        simp
      rw [heq]
      exact hlower
  have hcoarea := DirectedCoarea.coarea_mul Y S hcheeger
    (fun x ↦ (g x : ℝ)) 1 hmedian
  have hsum : (∑ x, |(g x : ℝ) - 1|) =
      (↑(∑ x, Nat.dist (g x) 1) : ℝ) := by
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro x _
    simpa only [Nat.cast_one] using abs_natCast_sub_natCast_eq_dist (g x) 1
  have hvariation : DirectedCoarea.variation Y S (fun x ↦ (g x : ℝ)) =
      (natLabelVariation Y S g : ℝ) := by
    rw [DirectedCoarea.variation, natLabelVariation]
    push_cast
    apply Finset.sum_congr rfl
    intro p _
    exact abs_natCast_sub_natCast_eq_dist (g p.2) (g (p.1 p.2))
  rwa [hsum, hvariation] at hcoarea

theorem small_lower_level_of_badRows
    (U : Finset (Y × Y))
    (hhalf : 2 * (badRows Y U).card ≤ Fintype.card Y) :
    2 * (Finset.univ.filter fun x ↦ rowDegree Y U x < 1).card ≤
      Fintype.card Y := by
  apply (Nat.mul_le_mul_left 2 <| Finset.card_le_card ?_).trans hhalf
  intro x hx
  rw [Finset.mem_filter] at hx
  rw [mem_badRows]
  omega

theorem small_upper_level_of_badRows
    (U : Finset (Y × Y))
    (hhalf : 2 * (badRows Y U).card ≤ Fintype.card Y) :
    2 * (Finset.univ.filter fun x ↦ 1 < rowDegree Y U x).card ≤
      Fintype.card Y := by
  apply (Nat.mul_le_mul_left 2 <| Finset.card_le_card ?_).trans hhalf
  intro x hx
  rw [Finset.mem_filter] at hx
  rw [mem_badRows]
  omega

theorem small_lower_level_of_badColumns
    (U : Finset (Y × Y))
    (hhalf : 2 * (badColumns Y U).card ≤ Fintype.card Y) :
    2 * (Finset.univ.filter fun y ↦ columnDegree Y U y < 1).card ≤
      Fintype.card Y := by
  apply (Nat.mul_le_mul_left 2 <| Finset.card_le_card ?_).trans hhalf
  intro y hy
  rw [Finset.mem_filter] at hy
  rw [mem_badColumns]
  omega

theorem small_upper_level_of_badColumns
    (U : Finset (Y × Y))
    (hhalf : 2 * (badColumns Y U).card ≤ Fintype.card Y) :
    2 * (Finset.univ.filter fun y ↦ 1 < columnDegree Y U y).card ≤
      Fintype.card Y := by
  apply (Nat.mul_le_mul_left 2 <| Finset.card_le_card ?_).trans hhalf
  intro y hy
  rw [Finset.mem_filter] at hy
  rw [mem_badColumns]
  omega

theorem rowFiberDeviation_mul_le_boundary
    (S : Finset (Equiv.Perm Y)) (U : Finset (Y × Y)) {h : ℝ}
    (hP : HasL1PoincareAtOne Y S h)
    (hhalf : 2 * (badRows Y U).card ≤ Fintype.card Y) :
    h * rowFiberDeviation Y U ≤ (relationBoundary Y S U).card := by
  have hcoarea := hP.2 (rowDegree Y U)
    (small_lower_level_of_badRows Y U hhalf)
    (small_upper_level_of_badRows Y U hhalf)
  have hvariation := rowDegreeVariation_le_relationBoundary Y S U
  exact hcoarea.trans (by exact_mod_cast hvariation)

theorem columnFiberDeviation_mul_le_boundary
    (S : Finset (Equiv.Perm Y)) (U : Finset (Y × Y)) {h : ℝ}
    (hP : HasL1PoincareAtOne Y S h)
    (hhalf : 2 * (badColumns Y U).card ≤ Fintype.card Y) :
    h * columnFiberDeviation Y U ≤ (relationBoundary Y S U).card := by
  have hcoarea := hP.2 (columnDegree Y U)
    (small_lower_level_of_badColumns Y U hhalf)
    (small_upper_level_of_badColumns Y U hhalf)
  have hvariation := columnDegreeVariation_le_relationBoundary Y S U
  exact hcoarea.trans (by exact_mod_cast hvariation)

/-! ### Boundary-only control of the singleton-core repair -/

/-- Relation points lying in a non-singleton row. -/
def badRowPoints (U : Finset (Y × Y)) : Finset (Y × Y) :=
  U.filter fun p ↦ p.1 ∈ badRows Y U

/-- Relation points lying in a non-singleton column. -/
def badColumnPoints (U : Finset (Y × Y)) : Finset (Y × Y) :=
  U.filter fun p ↦ p.2 ∈ badColumns Y U

theorem card_row_filter (U : Finset (Y × Y)) (x : Y) :
    (U.filter fun p ↦ p.1 = x).card = rowDegree Y U x := by
  let e : Y ↪ Y × Y :=
    ⟨fun y ↦ (x, y), fun _ _ h ↦ congrArg Prod.snd h⟩
  have hmap : (rowFiber Y U x).map e = U.filter fun p ↦ p.1 = x := by
    ext p
    constructor
    · intro hp
      rw [Finset.mem_map] at hp
      obtain ⟨y, hy, rfl⟩ := hp
      rw [Finset.mem_filter]
      change (x, y) ∈ U ∧ x = x
      exact ⟨(mem_rowFiber Y U x y).1 hy, rfl⟩
    · intro hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hpU, hpfirst⟩ := hp
      rw [Finset.mem_map]
      refine ⟨p.2, ?_, ?_⟩
      · rw [mem_rowFiber]
        rw [← hpfirst]
        exact hpU
      · exact Prod.ext hpfirst.symm rfl
  rw [← hmap, Finset.card_map]
  rfl

theorem card_column_filter (U : Finset (Y × Y)) (y : Y) :
    (U.filter fun p ↦ p.2 = y).card = columnDegree Y U y := by
  let e : Y ↪ Y × Y :=
    ⟨fun x ↦ (x, y), fun _ _ h ↦ congrArg Prod.fst h⟩
  have hmap : (columnFiber Y U y).map e = U.filter fun p ↦ p.2 = y := by
    ext p
    constructor
    · intro hp
      rw [Finset.mem_map] at hp
      obtain ⟨x, hx, rfl⟩ := hp
      rw [Finset.mem_filter]
      change (x, y) ∈ U ∧ y = y
      exact ⟨(mem_columnFiber Y U x y).1 hx, rfl⟩
    · intro hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hpU, hpsecond⟩ := hp
      rw [Finset.mem_map]
      refine ⟨p.1, ?_, ?_⟩
      · rw [mem_columnFiber]
        rw [← hpsecond]
        exact hpU
      · exact Prod.ext rfl hpsecond.symm
  rw [← hmap, Finset.card_map]
  rfl

theorem card_badRowPoints_eq_sum (U : Finset (Y × Y)) :
    (badRowPoints Y U).card =
      ∑ x ∈ badRows Y U, rowDegree Y U x := by
  have hfiber := Finset.sum_card_fiberwise_eq_card_filter U
    (badRows Y U) Prod.fst
  rw [show badRowPoints Y U = U.filter (fun p ↦ p.1 ∈ badRows Y U) from rfl,
    ← hfiber]
  apply Finset.sum_congr rfl
  intro x _
  exact card_row_filter Y U x

theorem card_badColumnPoints_eq_sum (U : Finset (Y × Y)) :
    (badColumnPoints Y U).card =
      ∑ y ∈ badColumns Y U, columnDegree Y U y := by
  have hfiber := Finset.sum_card_fiberwise_eq_card_filter U
    (badColumns Y U) Prod.snd
  rw [show badColumnPoints Y U =
      U.filter (fun p ↦ p.2 ∈ badColumns Y U) from rfl, ← hfiber]
  apply Finset.sum_congr rfl
  intro y _
  exact card_column_filter Y U y

theorem repairRelation_excess_subset_badPoints (U : Finset (Y × Y)) :
    U \ permutationGraph Y (repairRelation Y U) ⊆
      badRowPoints Y U ∪ badColumnPoints Y U := by
  intro p hp
  rw [Finset.mem_sdiff] at hp
  by_cases hrow : p.1 ∈ badRows Y U
  · apply Finset.mem_union_left
    exact Finset.mem_filter.mpr ⟨hp.1, hrow⟩
  by_cases hcolumn : p.2 ∈ badColumns Y U
  · apply Finset.mem_union_right
    exact Finset.mem_filter.mpr ⟨hp.1, hcolumn⟩
  exfalso
  apply hp.2
  apply core_subset_permutationGraph_repairRelation Y U
  rw [mem_relationCore]
  exact ⟨hp.1, (not_ne_iff.mp ((mem_badRows Y U p.1).not.mp hrow)),
    not_ne_iff.mp ((mem_badColumns Y U p.2).not.mp hcolumn)⟩

theorem card_repairRelation_excess_le_deviation (U : Finset (Y × Y)) :
    (U \ permutationGraph Y (repairRelation Y U)).card ≤
      2 * rowFiberDeviation Y U + 2 * columnFiberDeviation Y U := by
  have hsubset := Finset.card_le_card
    (repairRelation_excess_subset_badPoints Y U)
  have hunion := Finset.card_union_le (badRowPoints Y U) (badColumnPoints Y U)
  rw [card_badRowPoints_eq_sum, card_badColumnPoints_eq_sum] at hunion
  have hrows := sum_badRows_rowDegree_le Y U
  have hcolumns := sum_badColumns_columnDegree_le Y U
  omega

/-- Missing repaired graph sources whose relation row is nevertheless a
singleton. -/
noncomputable def goodMissingSources (U : Finset (Y × Y)) : Finset Y :=
  missingSources Y U (repairRelation Y U) \ badRows Y U

theorem exists_row_point_of_goodMissing (U : Finset (Y × Y))
    (x : {x // x ∈ goodMissingSources Y U}) :
    ∃ y : Y, (x.1, y) ∈ U := by
  have hxgood := (Finset.mem_sdiff.mp x.2).2
  have hdegree : rowDegree Y U x.1 = 1 :=
    not_ne_iff.mp ((mem_badRows Y U x.1).not.mp hxgood)
  have hnonempty : (rowFiber Y U x.1).Nonempty := by
    apply Finset.card_pos.mp
    rw [show (rowFiber Y U x.1).card = 1 by simpa [rowDegree] using hdegree]
    decide
  obtain ⟨y, hy⟩ := hnonempty
  exact ⟨y, (mem_rowFiber Y U x.1 y).1 hy⟩

noncomputable def goodMissingTarget (U : Finset (Y × Y))
    (x : {x // x ∈ goodMissingSources Y U}) : Y :=
  Classical.choose (exists_row_point_of_goodMissing Y U x)

theorem goodMissingTarget_mem (U : Finset (Y × Y))
    (x : {x // x ∈ goodMissingSources Y U}) :
    (x.1, goodMissingTarget Y U x) ∈ U :=
  Classical.choose_spec (exists_row_point_of_goodMissing Y U x)

noncomputable def goodMissingPointEmbedding (U : Finset (Y × Y)) :
    {x // x ∈ goodMissingSources Y U} ↪ Y × Y where
  toFun x := (x.1, goodMissingTarget Y U x)
  inj' := by
    intro x y hxy
    exact Subtype.ext (congrArg Prod.fst hxy)

theorem goodMissingTarget_badColumn (U : Finset (Y × Y))
    (x : {x // x ∈ goodMissingSources Y U}) :
    goodMissingTarget Y U x ∈ badColumns Y U := by
  rw [mem_badColumns]
  intro hcolumn
  have hxgood := (Finset.mem_sdiff.mp x.2).2
  have hrow : rowDegree Y U x.1 = 1 :=
    not_ne_iff.mp ((mem_badRows Y U x.1).not.mp hxgood)
  have hcore : (x.1, goodMissingTarget Y U x) ∈ relationCore Y U :=
    (mem_relationCore Y U _).2
      ⟨goodMissingTarget_mem Y U x, hrow, hcolumn⟩
  have hrepair := repairRelation_eq_of_mem_core Y U _ hcore
  have hmissing := (mem_missingSources Y U (repairRelation Y U) x.1).1
    (Finset.mem_sdiff.mp x.2).1
  apply hmissing
  simpa [hrepair] using goodMissingTarget_mem Y U x

theorem image_goodMissingPointEmbedding_subset_badColumnPoints
    (U : Finset (Y × Y)) :
    (goodMissingSources Y U).attach.map (goodMissingPointEmbedding Y U) ⊆
      badColumnPoints Y U := by
  intro p hp
  rw [Finset.mem_map] at hp
  obtain ⟨x, _, rfl⟩ := hp
  change (x.1, goodMissingTarget Y U x) ∈ badColumnPoints Y U
  exact Finset.mem_filter.mpr
    ⟨goodMissingTarget_mem Y U x, goodMissingTarget_badColumn Y U x⟩

theorem card_goodMissingSources_le_badColumnPoints (U : Finset (Y × Y)) :
    (goodMissingSources Y U).card ≤ (badColumnPoints Y U).card := by
  rw [← Finset.card_attach, ← Finset.card_map]
  exact Finset.card_le_card
    (image_goodMissingPointEmbedding_subset_badColumnPoints Y U)

theorem missingSources_repair_subset_badRows_union_good (U : Finset (Y × Y)) :
    missingSources Y U (repairRelation Y U) ⊆
      badRows Y U ∪ goodMissingSources Y U := by
  intro x hx
  by_cases hbad : x ∈ badRows Y U
  · exact Finset.mem_union_left _ hbad
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx, hbad⟩)

theorem card_repairRelation_missing_le_deviation (U : Finset (Y × Y)) :
    (permutationGraph Y (repairRelation Y U) \ U).card ≤
      rowFiberDeviation Y U + 2 * columnFiberDeviation Y U := by
  rw [← card_missingSources]
  have hsubset := Finset.card_le_card
    (missingSources_repair_subset_badRows_union_good Y U)
  have hunion := Finset.card_union_le (badRows Y U) (goodMissingSources Y U)
  have hgood := card_goodMissingSources_le_badColumnPoints Y U
  rw [card_badColumnPoints_eq_sum] at hgood
  have hrows := card_badRows_le_rowFiberDeviation Y U
  have hcolumns := sum_badColumns_columnDegree_le Y U
  omega

theorem card_repairRelation_edits_le_deviation (U : Finset (Y × Y)) :
    (permutationGraph Y (repairRelation Y U) \ U).card +
      (U \ permutationGraph Y (repairRelation Y U)).card ≤
        3 * rowFiberDeviation Y U + 4 * columnFiberDeviation Y U := by
  have hmissing := card_repairRelation_missing_le_deviation Y U
  have hexcess := card_repairRelation_excess_le_deviation Y U
  omega

theorem repairRelation_edits_mul_le_boundary
    (S : Finset (Equiv.Perm Y)) (U : Finset (Y × Y)) {h : ℝ}
    (hP : HasL1PoincareAtOne Y S h)
    (hrows : 2 * (badRows Y U).card ≤ Fintype.card Y)
    (hcolumns : 2 * (badColumns Y U).card ≤ Fintype.card Y) :
    h * ((permutationGraph Y (repairRelation Y U) \ U).card +
      (U \ permutationGraph Y (repairRelation Y U)).card) ≤
        7 * (relationBoundary Y S U).card := by
  have heditsNat := card_repairRelation_edits_le_deviation Y U
  have hedits :
      (((permutationGraph Y (repairRelation Y U) \ U).card +
        (U \ permutationGraph Y (repairRelation Y U)).card : ℕ) : ℝ) ≤
          3 * rowFiberDeviation Y U + 4 * columnFiberDeviation Y U := by
    exact_mod_cast heditsNat
  have hrow := rowFiberDeviation_mul_le_boundary Y S U hP hrows
  have hcolumn := columnFiberDeviation_mul_le_boundary Y S U hP hcolumns
  have hh : 0 ≤ h := hP.1.le
  have hmul := mul_le_mul_of_nonneg_left hedits hh
  calc
    h * ((permutationGraph Y (repairRelation Y U) \ U).card +
        (U \ permutationGraph Y (repairRelation Y U)).card) =
        h * (((permutationGraph Y (repairRelation Y U) \ U).card +
          (U \ permutationGraph Y (repairRelation Y U)).card : ℕ) : ℝ) := by
            norm_num
    _ ≤ h * (3 * rowFiberDeviation Y U + 4 * columnFiberDeviation Y U) := hmul
    _ = 3 * (h * rowFiberDeviation Y U) +
        4 * (h * columnFiberDeviation Y U) := by ring
    _ ≤ 3 * (relationBoundary Y S U).card +
        4 * (relationBoundary Y S U).card := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hrow (by norm_num))
            (mul_le_mul_of_nonneg_left hcolumn (by norm_num))
    _ = 7 * (relationBoundary Y S U).card := by ring

/-- Once row and column multiplicities have median one, the repaired
permutation's commutation defect is controlled solely by the relation
boundary; no pre-existing nearby permutation appears in this estimate. -/
theorem repairRelation_badArcs_mul_le_boundary
    (S : Finset (Equiv.Perm Y)) (U : Finset (Y × Y)) {h : ℝ}
    (hP : HasL1PoincareAtOne Y S h)
    (hrows : 2 * (badRows Y U).card ≤ Fintype.card Y)
    (hcolumns : 2 * (badColumns Y U).card ≤ Fintype.card Y) :
    h * (badArcs Y S (repairRelation Y U)).card ≤
      (h + 7 * S.card) * (relationBoundary Y S U).card := by
  have hbase := card_badArcs_le_relationBoundary_add_edits Y S U
    (repairRelation Y U)
  have hedits := repairRelation_edits_mul_le_boundary Y S U hP hrows hcolumns
  have hh : 0 ≤ h := hP.1.le
  have hbaseReal :
      ((badArcs Y S (repairRelation Y U)).card : ℝ) ≤
        (relationBoundary Y S U).card +
          S.card * ((permutationGraph Y (repairRelation Y U) \ U).card +
            (U \ permutationGraph Y (repairRelation Y U)).card) := by
    exact_mod_cast hbase
  have hmul := mul_le_mul_of_nonneg_left hbaseReal hh
  nlinarith

theorem repairRelation_isEpsilonGood_of_boundary
    (S : Finset (Equiv.Perm Y)) (U : Finset (Y × Y)) {h ε : ℝ}
    (hP : HasL1PoincareAtOne Y S h)
    (hrows : 2 * (badRows Y U).card ≤ Fintype.card Y)
    (hcolumns : 2 * (badColumns Y U).card ≤ Fintype.card Y)
    (hboundary :
      (h + 7 * S.card) * (relationBoundary Y S U).card <
        h * (ε * Fintype.card Y)) :
    IsEpsilonGood Y S ε (repairRelation Y U) := by
  have hcontrol := repairRelation_badArcs_mul_le_boundary
    Y S U hP hrows hcolumns
  have hbad : ((badArcs Y S (repairRelation Y U)).card : ℝ) <
      ε * Fintype.card Y := by
    nlinarith [hP.1]
  refine ⟨hbad, ?_⟩
  rw [card_badArcs_inv]
  exact hbad

theorem repairRelation_isEpsilonGood_of_close_relation
    (S : Finset (Equiv.Perm Y)) (U : Finset (Y × Y))
    (c : Equiv.Perm Y) {h ε : ℝ}
    (hP : HasL1PoincareAtOne Y S h)
    (hedits : 2 * ((permutationGraph Y c \ U).card +
      (U \ permutationGraph Y c).card) ≤ Fintype.card Y)
    (hboundary :
      (h + 7 * S.card) * (relationBoundary Y S U).card <
        h * (ε * Fintype.card Y)) :
    IsEpsilonGood Y S ε (repairRelation Y U) := by
  obtain ⟨hrows, hcolumns⟩ := badFibers_at_most_half_of_edits Y U c hedits
  exact repairRelation_isEpsilonGood_of_boundary
    Y S U hP hrows hcolumns hboundary

theorem hammingDistance_repairRelation_lt
    (U : Finset (Y × Y)) (c : Equiv.Perm Y) {r : ℝ}
    (hcardY : 0 < Fintype.card Y)
    (hedits :
      (((permutationGraph Y c \ U).card +
        2 * ((permutationGraph Y c \ U).card +
          (U \ permutationGraph Y c).card) : ℕ) : ℝ) <
            r * Fintype.card Y) :
    hammingDistance Y (repairRelation Y U) c < r := by
  refine (hammingDistance_repairRelation_le Y U c).trans_lt ?_
  have hcardReal : (0 : ℝ) < Fintype.card Y := by exact_mod_cast hcardY
  rw [div_lt_iff₀ hcardReal]
  exact hedits

theorem missingSources_roundRelation_subset
    (U : Finset (Y × Y)) (c : Equiv.Perm Y) :
    missingSources Y U (roundRelation Y U c) ⊆ missingSources Y U c := by
  intro x hx
  rw [mem_missingSources] at hx ⊢
  intro hxc
  have hround := roundRelation_eq_of_mem Y U c x hxc
  exact hx (by simpa [hround] using hxc)

theorem excess_roundRelation_subset
    (U : Finset (Y × Y)) (c : Equiv.Perm Y) :
    U \ permutationGraph Y (roundRelation Y U c) ⊆
      U \ permutationGraph Y c := by
  intro p hp
  rw [Finset.mem_sdiff] at hp ⊢
  refine ⟨hp.1, ?_⟩
  intro hpc
  have hc := (mem_permutationGraph Y c p).1 hpc
  have hpEq : p = (p.1, c p.1) := Prod.ext rfl hc
  have hretained : (p.1, c p.1) ∈ U := by simpa [← hpEq] using hp.1
  have hround := roundRelation_eq_of_mem Y U c p.1 hretained
  apply hp.2
  rw [mem_permutationGraph]
  exact hc.trans hround.symm

theorem card_missing_roundRelation_le
    (U : Finset (Y × Y)) (c : Equiv.Perm Y) :
    (permutationGraph Y (roundRelation Y U c) \ U).card ≤
      (permutationGraph Y c \ U).card := by
  rw [← card_missingSources Y U (roundRelation Y U c),
    ← card_missingSources Y U c]
  exact Finset.card_le_card (missingSources_roundRelation_subset Y U c)

/-- The permutation obtained by finite matching repair has no more label
defects than the relation boundary plus its original symmetric-difference
budget. -/
theorem card_badArcs_roundRelation_le
    (S : Finset (Equiv.Perm Y)) (U : Finset (Y × Y))
    (c : Equiv.Perm Y) :
    (badArcs Y S (roundRelation Y U c)).card ≤
      (relationBoundary Y S U).card +
        S.card * ((permutationGraph Y c \ U).card +
          (U \ permutationGraph Y c).card) := by
  have hbase := card_badArcs_le_relationBoundary_add_edits Y S U
    (roundRelation Y U c)
  have hmissing := card_missing_roundRelation_le Y U c
  have hexcess := Finset.card_le_card (excess_roundRelation_subset Y U c)
  nlinarith

/-- The integer error budget contributed by a relation's boundary and its
symmetric difference from a permutation graph. -/
def relationErrorBudget (S : Finset (Equiv.Perm Y))
    (U : Finset (Y × Y)) (c : Equiv.Perm Y) : ℕ :=
  (relationBoundary Y S U).card +
    S.card * ((permutationGraph Y c \ U).card +
      (U \ permutationGraph Y c).card)

theorem roundRelation_isGood
    (S : Finset (Equiv.Perm Y)) {h : ℝ} (m : ℕ)
    (U : Finset (Y × Y)) (c : Equiv.Perm Y)
    (hbudget : (relationErrorBudget Y S U c : ℝ) < h * m / 2) :
    IsGood Y S h m (roundRelation Y U c) := by
  have hcard := card_badArcs_roundRelation_le Y S U c
  have hcard' : (badArcs Y S (roundRelation Y U c)).card ≤
      relationErrorBudget Y S U c := by
    simpa [relationErrorBudget] using hcard
  have hbad : ((badArcs Y S (roundRelation Y U c)).card : ℝ) <
      h * m / 2 := by
    apply lt_of_le_of_lt (b := (relationErrorBudget Y S U c : ℝ))
    · exact_mod_cast hcard'
    · exact hbudget
  refine ⟨hbad, ?_⟩
  rw [card_badArcs_inv]
  exact hbad

theorem roundRelation_close
    (U : Finset (Y × Y)) (c : Equiv.Perm Y) (m : ℕ)
    (hcardY : 0 < Fintype.card Y)
    (hmissing : (permutationGraph Y c \ U).card < m) :
    hammingDistance Y c (roundRelation Y U c) <
      (m : ℝ) / Fintype.card Y := by
  rw [hammingDistance_comm]
  refine (hammingDistance_roundRelation_le Y U c).trans_lt ?_
  have hmissingReal : ((permutationGraph Y c \ U).card : ℝ) < m := by
    exact_mod_cast hmissing
  have hcardReal : (0 : ℝ) < Fintype.card Y := by exact_mod_cast hcardY
  exact div_lt_div_of_pos_right hmissingReal hcardReal

/-- Finite Kun--Thom improvement after the property-(T) step has supplied,
for each product of good almost automorphisms, a nearby binary relation with
small diagonal boundary.  Unlike `ClusterData`, the hypotheses here are the
raw finite estimates that the Kazhdan argument must prove. -/
noncomputable def clusterData_of_relationImprovement
    (S : Finset (Equiv.Perm Y)) {h : ℝ}
    (m : ℕ) (hm : 0 < m)
    (hsize : 5 * m ≤ Fintype.card Y)
    (hexp : HasDirectedExpansionAtScale Y S h m)
    (improve : Equiv.Perm Y → Finset (Y × Y))
    (hbudget : ∀ a, IsGood Y S h m a → ∀ b, IsGood Y S h m b →
      (relationErrorBudget Y S (improve (a * b)) (a * b) : ℝ) < h * m / 2)
    (hmissing : ∀ a, IsGood Y S h m a → ∀ b, IsGood Y S h m b →
      (permutationGraph Y (a * b) \ improve (a * b)).card < m) :
    ClusterData Y :=
  clusterData_of_rounding Y S m hm hsize hexp
    (fun c ↦ roundRelation Y (improve c) c)
    (fun a ha b hb ↦ roundRelation_isGood Y S m (improve (a * b))
      (a * b) (hbudget a ha b hb))
    (fun a ha b hb ↦ roundRelation_close Y (improve (a * b))
      (a * b) m (by omega) (hmissing a ha b hb))

variable {K J : Type} [Group K] [Group J]

/-- The complete Kun--Thom finite-group conclusion from the raw relation
improvement estimates.  This is the boundary at which the still-to-be-proved
Kazhdan analytic theorem plugs into the already formalized finite argument. -/
theorem isLEF_of_product_relationImprovement
    (A : SoficApproximation (K × J)) (T : Finset K) {h : ℝ} (hh : 0 < h)
    (hexp : ∃ Nexp, ∀ n ≥ Nexp,
      HasDirectedExpansionAtScale (A.model n) (productLabels A n T) h
        (clusterScale (A.model n)))
    (himprove : ∃ Nimp, ∀ n ≥ Nimp,
      ∃ improve : Equiv.Perm (A.model n) →
          Finset (A.model n × A.model n),
        (∀ a, IsGood (A.model n) (productLabels A n T) h
              (clusterScale (A.model n)) a →
          ∀ b, IsGood (A.model n) (productLabels A n T) h
              (clusterScale (A.model n)) b →
          (relationErrorBudget (A.model n) (productLabels A n T)
              (improve (a * b)) (a * b) : ℝ) <
            h * clusterScale (A.model n) / 2) ∧
        (∀ a, IsGood (A.model n) (productLabels A n T) h
              (clusterScale (A.model n)) a →
          ∀ b, IsGood (A.model n) (productLabels A n T) h
              (clusterScale (A.model n)) b →
          (permutationGraph (A.model n) (a * b) \ improve (a * b)).card <
            clusterScale (A.model n))) :
    IsLEF J := by
  apply AlmostAutomorphism.ClusterData.isLEF_of_product_rounding A T hh hexp
  obtain ⟨Nimp, hNimp⟩ := himprove
  refine ⟨Nimp, fun n hn ↦ ?_⟩
  obtain ⟨improve, hbudget, hmissing⟩ := hNimp n hn
  let round : Equiv.Perm (A.model n) → Equiv.Perm (A.model n) :=
    fun c ↦ roundRelation (A.model n) (improve c) c
  refine ⟨round, ?_, ?_⟩
  · intro a ha b hb
    exact roundRelation_isGood (A.model n) (productLabels A n T)
      (clusterScale (A.model n)) (improve (a * b)) (a * b)
      (hbudget a ha b hb)
  · intro a ha b hb
    change hammingDistance (A.model n) (a * b)
      (roundRelation (A.model n) (improve (a * b)) (a * b)) <
        clusterRadius (A.model n)
    apply roundRelation_close (A.model n) (improve (a * b)) (a * b)
      (clusterScale (A.model n))
    · have hm := hmissing a ha b hb
      unfold clusterScale at hm
      omega
    · exact hmissing a ha b hb

end KazhdanImprovement
end NonsoficGroupsExist
