import NonsoficGroupsExist.AlmostAutomorphism
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
