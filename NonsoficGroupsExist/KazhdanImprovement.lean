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

end KazhdanImprovement
end NonsoficGroupsExist
