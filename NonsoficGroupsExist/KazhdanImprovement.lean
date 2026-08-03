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

end KazhdanImprovement
end NonsoficGroupsExist
