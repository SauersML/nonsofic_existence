import NonsoficGroupsExist.SoficErrors
import NonsoficGroupsExist.LEF
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Order
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Algebra.Group.End
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm

/-!
# Almost automorphisms of finite labeled permutation graphs

This module begins the kernel-checked replacement for the Kun--Thom input.
It formalizes the elementary separation mechanism behind their Lemma 4.1:
the agreement set of two label-preserving permutations can have boundary only
where at least one of the permutations fails to preserve a label.
-/

namespace NonsoficGroupsExist
namespace AlmostAutomorphism

variable (Y : FiniteModel)

/-- Finitely many eventual assertions admit one common threshold. -/
theorem eventually_finset {ι : Type*} (s : Finset ι) (P : ι → ℕ → Prop)
    (h : ∀ i ∈ s, ∃ N, ∀ n ≥ N, P i n) :
    ∃ N, ∀ n ≥ N, ∀ i ∈ s, P i n := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert i s hi ih =>
      obtain ⟨Ni, hNi⟩ := h i (Finset.mem_insert_self i s)
      obtain ⟨Ns, hNs⟩ := ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj)
      refine ⟨max Ni Ns, fun n hn j hj ↦ ?_⟩
      rw [Finset.mem_insert] at hj
      rcases hj with rfl | hj
      · exact hNi n ((le_max_left _ _).trans hn)
      · exact hNs n ((le_max_right _ _).trans hn) j hj

/-- Label occurrences on a finite permutation graph. -/
abbrev Arc := Equiv.Perm Y × Y

/-- Label occurrences on which `c` fails to commute with the label. -/
def badArcs (S : Finset (Equiv.Perm Y)) (c : Equiv.Perm Y) :
    Finset (Arc Y) :=
  (S.product Finset.univ).filter fun p ↦ c (p.1 p.2) ≠ p.1 (c p.2)

@[simp] theorem mem_badArcs (S : Finset (Equiv.Perm Y))
    (c : Equiv.Perm Y) (p : Arc Y) :
    p ∈ badArcs Y S c ↔ p.1 ∈ S ∧ c (p.1 p.2) ≠ p.1 (c p.2) := by
  simp [badArcs]

/-- Reindex an arc by a permutation on its source vertex. -/
def inverseDefectEquiv (c : Equiv.Perm Y) : Arc Y ≃ Arc Y where
  toFun p := (p.1, c p.2)
  invFun p := (p.1, c⁻¹ p.2)
  left_inv p := by simp
  right_inv p := by simp

theorem image_badArcs_inverseDefectEquiv (S : Finset (Equiv.Perm Y))
    (c : Equiv.Perm Y) :
    (badArcs Y S c).map (inverseDefectEquiv Y c).toEmbedding =
      badArcs Y S c⁻¹ := by
  ext p
  constructor
  · intro hp
    rw [Finset.mem_map] at hp
    obtain ⟨⟨s, x⟩, hq, rfl⟩ := hp
    rw [mem_badArcs] at hq ⊢
    refine ⟨hq.1, ?_⟩
    dsimp [inverseDefectEquiv]
    simp only [Equiv.symm_apply_apply]
    change c⁻¹ (s (c x)) ≠ s x
    intro heq
    apply hq.2
    have hc := congrArg c heq
    simpa using hc.symm
  · intro hp
    rcases p with ⟨s, x⟩
    rw [mem_badArcs] at hp
    rw [Finset.mem_map]
    let q : Arc Y := (s, c⁻¹ x)
    refine ⟨q, ?_, ?_⟩
    · rw [mem_badArcs]
      refine ⟨hp.1, ?_⟩
      dsimp [q]
      simp only [Equiv.apply_symm_apply]
      change c (s (c⁻¹ x)) ≠ s x
      intro heq
      apply hp.2
      have hc := congrArg (c⁻¹ : Equiv.Perm Y) heq
      simpa using hc.symm
    · simp [q, inverseDefectEquiv]

theorem card_badArcs_inv (S : Finset (Equiv.Perm Y)) (c : Equiv.Perm Y) :
    (badArcs Y S c⁻¹).card = (badArcs Y S c).card := by
  rw [← image_badArcs_inverseDefectEquiv]
  exact Finset.card_map _

/-! ### Defects coming from a product sofic approximation -/

variable {K J : Type} [Group K] [Group J]

/-- The finite set of permutations assigned to a fixed set of generators of
the first factor. -/
noncomputable def productLabels (A : SoficApproximation (K × J)) (n : ℕ)
    (T : Finset K) : Finset (Equiv.Perm (A.model n)) := by
  classical
  exact T.image fun k ↦ A.map n (k, 1)

/-- Generator-tagged failures of commutation between the first-factor labels
and the permutation assigned to `(1,j)`. -/
noncomputable def centralizerDefectPairs (A : SoficApproximation (K × J))
    (n : ℕ) (T : Finset K) (j : J) : Finset (T × A.model n) := by
  classical
  exact (Finset.univ : Finset T).biUnion fun t ↦
    ({t} : Finset T) ×ˢ A.commutationError n (1, j) (t.1, 1)

theorem badArcs_productLabels_eq_image
    (A : SoficApproximation (K × J)) (n : ℕ) (T : Finset K) (j : J) :
    badArcs (A.model n) (productLabels A n T) (A.map n (1, j)) =
      (centralizerDefectPairs A n T j).image fun p ↦
        (A.map n (p.1.1, 1), p.2) := by
  classical
  ext p
  simp only [mem_badArcs, productLabels, centralizerDefectPairs,
    Finset.mem_image, Finset.mem_biUnion, Finset.mem_univ,
    Finset.mem_product, Finset.mem_singleton, true_and,
    SoficApproximation.commutationError, Finset.mem_filter]
  constructor
  · rintro ⟨⟨k, hk, hlabel⟩, hbad⟩
    let t : T := ⟨k, hk⟩
    refine ⟨(t, p.2), ⟨t, ⟨rfl, ?_⟩⟩, ?_⟩
    · simpa [t, hlabel] using hbad
    · simp [t, hlabel]
  · rintro ⟨⟨qt, qx⟩, ⟨t, ⟨hqt, hq⟩⟩, rfl⟩
    change qt = t at hqt
    subst qt
    refine ⟨⟨t.1, t.2, rfl⟩, ?_⟩
    simpa [SoficApproximation.commutationError] using hq

theorem card_badArcs_productLabels_le
    (A : SoficApproximation (K × J)) (n : ℕ) (T : Finset K) (j : J) :
    (badArcs (A.model n) (productLabels A n T) (A.map n (1, j))).card ≤
      ∑ t : T, (A.commutationError n (1, j) (t.1, 1)).card := by
  classical
  rw [badArcs_productLabels_eq_image]
  refine Finset.card_image_le.trans ?_
  calc
    (centralizerDefectPairs A n T j).card ≤
        ∑ t : T,
          (({t} : Finset T) ×ˢ
            A.commutationError n (1, j) (t.1, 1)).card :=
      Finset.card_biUnion_le
    _ = ∑ t : T, (A.commutationError n (1, j) (t.1, 1)).card := by
      apply Finset.sum_congr rfl
      intro t _
      rw [Finset.card_product]
      simp

/-- For every fixed element of the second factor, failure to preserve the
first-factor labels has negligible density. -/
theorem badArcs_productLabels_negligible
    (A : SoficApproximation (K × J)) (T : Finset K) (j : J) :
    Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ((badArcs (A.model n) (productLabels A n T) (A.map n (1, j))).card : ℝ) := by
  let errors : T → ℕ → ℝ := fun t n ↦
    ((A.commutationError n (1, j) (t.1, 1)).card : ℝ)
  have herrors : ∀ t : T,
      Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) (errors t) := by
    intro t
    apply A.commutationError_negligible
    rw [commute_iff_eq]
    ext <;> simp
  have hsum : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ))
      (fun n ↦ ∑ t : T, errors t n) := by
    apply Negligible.sum (Finset.univ : Finset T)
    intro t _
    exact herrors t
  apply Negligible.mono_nonneg
    (fun _ ↦ by positivity) (fun _ ↦ by positivity) _ hsum
  intro n
  dsimp [errors]
  exact_mod_cast card_badArcs_productLabels_le A n T j

/-- The one-fifth cluster scale used in the original Kun--Thom argument. -/
def clusterScale (Y : FiniteModel) : ℕ := Fintype.card Y / 5

theorem clusterScale_pos (hcard : 5 ≤ Fintype.card Y) :
    0 < clusterScale Y := by
  unfold clusterScale
  omega

theorem five_mul_clusterScale_le :
    5 * clusterScale Y ≤ Fintype.card Y := by
  unfold clusterScale
  omega

noncomputable def clusterRadius (Y : FiniteModel) : ℝ :=
  (clusterScale Y : ℝ) / Fintype.card Y

theorem one_tenth_le_clusterRadius (hcard : 10 ≤ Fintype.card Y) :
    (1 : ℝ) / 10 ≤ clusterRadius Y := by
  have hcardReal : (0 : ℝ) < Fintype.card Y := by
    exact_mod_cast (show 0 < Fintype.card Y by omega)
  have hfloorNat : Fintype.card Y ≤ 10 * clusterScale Y := by
    unfold clusterScale
    omega
  have hfloorReal : (Fintype.card Y : ℝ) ≤ 10 * clusterScale Y := by
    exact_mod_cast hfloorNat
  rw [clusterRadius, le_div_iff₀ hcardReal]
  linarith

theorem clusterRadius_le_one_fifth (hcard : 0 < Fintype.card Y) :
    clusterRadius Y ≤ (1 : ℝ) / 5 := by
  have hcardReal : (0 : ℝ) < Fintype.card Y := by exact_mod_cast hcard
  rw [clusterRadius, div_le_iff₀ hcardReal]
  have hscale : (5 : ℝ) * clusterScale Y ≤ Fintype.card Y := by
    exact_mod_cast five_mul_clusterScale_le Y
  linarith

/-- The directed label boundary of a set of vertices.  Both orientations are
retained when the label set is symmetric. -/
def directedBoundary (S : Finset (Equiv.Perm Y)) (A : Finset Y) :
    Finset (Arc Y) :=
  (S.product Finset.univ).filter fun p ↦
    (p.2 ∈ A ∧ p.1 p.2 ∉ A) ∨ (p.2 ∉ A ∧ p.1 p.2 ∈ A)

@[simp] theorem mem_directedBoundary (S : Finset (Equiv.Perm Y))
    (A : Finset Y) (p : Arc Y) :
    p ∈ directedBoundary Y S A ↔
      p.1 ∈ S ∧ ((p.2 ∈ A ∧ p.1 p.2 ∉ A) ∨
        (p.2 ∉ A ∧ p.1 p.2 ∈ A)) := by
  simp [directedBoundary]

/-- Vertices on which two permutations agree. -/
def agreement (c d : Equiv.Perm Y) : Finset Y :=
  Finset.univ.filter fun x ↦ c x = d x

@[simp] theorem mem_agreement (c d : Equiv.Perm Y) (x : Y) :
    x ∈ agreement Y c d ↔ c x = d x := by
  simp [agreement]

/-- Vertices on which two permutations disagree. -/
def disagreement (c d : Equiv.Perm Y) : Finset Y :=
  Finset.univ.filter fun x ↦ c x ≠ d x

@[simp] theorem mem_disagreement (c d : Equiv.Perm Y) (x : Y) :
    x ∈ disagreement Y c d ↔ c x ≠ d x := by
  simp [disagreement]

/-- Every label arc crossing the agreement set is bad for at least one of the
two permutations. -/
theorem directedBoundary_agreement_subset_badArcs_union
    (S : Finset (Equiv.Perm Y)) (c d : Equiv.Perm Y) :
    directedBoundary Y S (agreement Y c d) ⊆
      badArcs Y S c ∪ badArcs Y S d := by
  intro p hp
  rw [mem_directedBoundary] at hp
  rcases hp with ⟨hpS, hp⟩
  by_cases hc : c (p.1 p.2) ≠ p.1 (c p.2)
  · exact Finset.mem_union_left _ ((mem_badArcs Y S c p).2 ⟨hpS, hc⟩)
  by_cases hd : d (p.1 p.2) ≠ p.1 (d p.2)
  · exact Finset.mem_union_right _ ((mem_badArcs Y S d p).2 ⟨hpS, hd⟩)
  have hc' : c (p.1 p.2) = p.1 (c p.2) := not_ne_iff.mp hc
  have hd' : d (p.1 p.2) = p.1 (d p.2) := not_ne_iff.mp hd
  rcases hp with ⟨hx, hsx⟩ | ⟨hx, hsx⟩
  · have hxd : c p.2 = d p.2 := (mem_agreement Y c d p.2).1 hx
    have hsxd : c (p.1 p.2) ≠ d (p.1 p.2) := by
      simpa using hsx
    exfalso
    apply hsxd
    calc
      c (p.1 p.2) = p.1 (c p.2) := hc'
      _ = p.1 (d p.2) := congrArg p.1 hxd
      _ = d (p.1 p.2) := hd'.symm
  · have hxd : c p.2 ≠ d p.2 := by
      simpa using hx
    have hsxd : c (p.1 p.2) = d (p.1 p.2) :=
      (mem_agreement Y c d (p.1 p.2)).1 hsx
    exfalso
    apply hxd
    apply p.1.injective
    calc
      p.1 (c p.2) = c (p.1 p.2) := hc'.symm
      _ = d (p.1 p.2) := hsxd
      _ = p.1 (d p.2) := hd'

/-- Boundary size of the agreement set is bounded by the combined labeled
defects. -/
theorem card_directedBoundary_agreement_le
    (S : Finset (Equiv.Perm Y)) (c d : Equiv.Perm Y) :
    (directedBoundary Y S (agreement Y c d)).card ≤
      (badArcs Y S c).card + (badArcs Y S d).card := by
  exact (Finset.card_le_card
    (directedBoundary_agreement_subset_badArcs_union Y S c d)).trans
      (Finset.card_union_le _ _)

/-- Agreement and disagreement partition the vertex set. -/
theorem agreement_union_disagreement (c d : Equiv.Perm Y) :
    agreement Y c d ∪ disagreement Y c d = Finset.univ := by
  ext x
  by_cases h : c x = d x <;> simp [h]

theorem agreement_disjoint_disagreement (c d : Equiv.Perm Y) :
    Disjoint (agreement Y c d) (disagreement Y c d) := by
  exact Finset.disjoint_left.mpr fun x hx hy ↦
    (mem_disagreement Y c d x).1 hy ((mem_agreement Y c d x).1 hx)

/-- Hamming-count decomposition into agreement and disagreement vertices. -/
theorem card_agreement_add_card_disagreement (c d : Equiv.Perm Y) :
    (agreement Y c d).card + (disagreement Y c d).card = Fintype.card Y := by
  rw [← Finset.card_union_of_disjoint (agreement_disjoint_disagreement Y c d),
    agreement_union_disagreement]
  exact Finset.card_univ

theorem disagreement_eq_compl_agreement (c d : Equiv.Perm Y) :
    disagreement Y c d = Finset.univ \ agreement Y c d := by
  ext x
  by_cases h : c x = d x <;> simp [h]

theorem directedBoundary_compl (S : Finset (Equiv.Perm Y)) (A : Finset Y) :
    directedBoundary Y S (Finset.univ \ A) = directedBoundary Y S A := by
  ext p
  simp only [mem_directedBoundary, Finset.mem_sdiff, Finset.mem_univ, true_and]
  by_cases hx : p.2 ∈ A <;> by_cases hsx : p.1 p.2 ∈ A <;> simp [hx, hsx]

/-- Directed expansion only at and above the cluster scale.  This is the exact
range used in the separation argument and, unlike expansion down to singleton
sets, is stable under a negligible number of edge edits. -/
def HasDirectedExpansionAtScale (S : Finset (Equiv.Perm Y)) (h : ℝ)
    (m : ℕ) : Prop :=
  0 < h ∧ ∀ A : Finset Y, m ≤ A.card →
    2 * A.card ≤ Fintype.card Y →
      h * A.card ≤ (directedBoundary Y S A).card

/-- Kun--Thom separation: on an expanding labeled graph, two permutations
with sufficiently few combined label defects cannot have both a large
agreement set and a large disagreement set. -/
theorem agreement_or_disagreement_small
    (S : Finset (Equiv.Perm Y)) {h : ℝ} (c d : Equiv.Perm Y)
    (m : ℕ)
    (hexp : HasDirectedExpansionAtScale Y S h m)
    (hbad : (((badArcs Y S c).card + (badArcs Y S d).card : ℕ) : ℝ) <
      h * m) :
    (agreement Y c d).card < m ∨ (disagreement Y c d).card < m := by
  by_contra hsmall
  push Not at hsmall
  have hboundary := card_directedBoundary_agreement_le Y S c d
  by_cases hhalf : 2 * (agreement Y c d).card ≤ Fintype.card Y
  · have hexpand := hexp.2 (agreement Y c d) hsmall.1 hhalf
    have hmcast : (m : ℝ) ≤ ((agreement Y c d).card : ℝ) := by
      exact_mod_cast hsmall.1
    have hscale : h * m ≤ h * (agreement Y c d).card :=
      mul_le_mul_of_nonneg_left hmcast hexp.1.le
    have hboundarycast : ((directedBoundary Y S (agreement Y c d)).card : ℝ) ≤
        ((badArcs Y S c).card + (badArcs Y S d).card : ℕ) := by
      exact_mod_cast hboundary
    linarith
  · have hhalf' : 2 * (disagreement Y c d).card ≤ Fintype.card Y := by
      have hpartition := card_agreement_add_card_disagreement Y c d
      omega
    have hexpand := hexp.2 (disagreement Y c d) hsmall.2 hhalf'
    have hmcast : (m : ℝ) ≤ ((disagreement Y c d).card : ℝ) := by
      exact_mod_cast hsmall.2
    have hscale : h * m ≤ h * (disagreement Y c d).card :=
      mul_le_mul_of_nonneg_left hmcast hexp.1.le
    have hboundaries :
        directedBoundary Y S (disagreement Y c d) =
          directedBoundary Y S (agreement Y c d) := by
      rw [disagreement_eq_compl_agreement, directedBoundary_compl]
    have hboundarycast : ((directedBoundary Y S (disagreement Y c d)).card : ℝ) ≤
        ((badArcs Y S c).card + (badArcs Y S d).card : ℕ) := by
      rw [hboundaries]
      exact_mod_cast hboundary
    linarith

theorem hammingDistance_eq_disagreement_card (c d : Equiv.Perm Y) :
    hammingDistance Y c d =
      ((disagreement Y c d).card : ℝ) / Fintype.card Y := by
  rfl

/-- Normalized form of the Kun--Thom separation estimate.  If the graph has
at least five times the chosen small-set scale, two sufficiently good almost
automorphisms are either within `m / |Y|` in Hamming distance or at least four
times that far apart. -/
theorem hammingDistance_small_or_four_mul_le
    (S : Finset (Equiv.Perm Y)) {h : ℝ} (c d : Equiv.Perm Y)
    (m : ℕ) (hm : 0 < m) (hsize : 5 * m ≤ Fintype.card Y)
    (hexp : HasDirectedExpansionAtScale Y S h m)
    (hbad : (((badArcs Y S c).card + (badArcs Y S d).card : ℕ) : ℝ) <
      h * m) :
    hammingDistance Y c d < (m : ℝ) / Fintype.card Y ∨
      4 * ((m : ℝ) / Fintype.card Y) ≤ hammingDistance Y c d := by
  have hcardNat : 0 < Fintype.card Y := by omega
  have hcardReal : (0 : ℝ) < Fintype.card Y := by exact_mod_cast hcardNat
  rcases agreement_or_disagreement_small Y S c d m hexp hbad with
    hagree | hdisagree
  · right
    have hfourNat : 4 * m ≤ (disagreement Y c d).card := by
      have hpartition := card_agreement_add_card_disagreement Y c d
      omega
    have hfourReal : (4 : ℝ) * m ≤ ((disagreement Y c d).card : ℝ) := by
      exact_mod_cast hfourNat
    rw [hammingDistance_eq_disagreement_card]
    rw [show 4 * ((m : ℝ) / Fintype.card Y) =
      ((4 : ℝ) * m) / Fintype.card Y by ring]
    exact div_le_div_of_nonneg_right hfourReal hcardReal.le
  · left
    have hdisagreeReal : ((disagreement Y c d).card : ℝ) < m := by
      exact_mod_cast hdisagree
    rw [hammingDistance_eq_disagreement_card]
    exact div_lt_div_of_pos_right hdisagreeReal hcardReal

theorem hammingDistance_mul_mul_le (a b c d : Equiv.Perm Y) :
    hammingDistance Y (a * b) (c * d) ≤
      hammingDistance Y a c + hammingDistance Y b d := by
  calc
    hammingDistance Y (a * b) (c * d) ≤
        hammingDistance Y (a * b) (c * b) +
          hammingDistance Y (c * b) (c * d) :=
      hammingDistance_triangle Y _ _ _
    _ = hammingDistance Y a c + hammingDistance Y b d := by
      rw [hammingDistance_right_invariant, hammingDistance_left_invariant]

theorem hammingDistance_inv (a b : Equiv.Perm Y) :
    hammingDistance Y a⁻¹ b⁻¹ = hammingDistance Y a b := by
  calc
    hammingDistance Y a⁻¹ b⁻¹ =
        hammingDistance Y (a⁻¹ * b) (b⁻¹ * b) := by
      rw [hammingDistance_right_invariant]
    _ = hammingDistance Y 1 (a⁻¹ * b) := by
      rw [inv_mul_cancel, hammingDistance_comm]
    _ = hammingDistance Y a b := by
      rw [← hammingDistance_left_invariant Y a⁻¹ a b, inv_mul_cancel]

/-! ### Finite groups of almost-automorphism clusters -/

/-- Abstract finite-stage data produced by the Kun--Thom improvement theorem.
`candidate` is the finite set of sufficiently good almost automorphisms;
`round` improves a product back into that set. -/
structure ClusterData where
  radius : ℝ
  radius_pos : 0 < radius
  candidate : Finset (Equiv.Perm Y)
  one_mem : 1 ∈ candidate
  inv_mem : ∀ c ∈ candidate, c⁻¹ ∈ candidate
  round : Equiv.Perm Y → Equiv.Perm Y
  round_product_mem : ∀ a ∈ candidate, ∀ b ∈ candidate,
    round (a * b) ∈ candidate
  round_product_close : ∀ a ∈ candidate, ∀ b ∈ candidate,
    hammingDistance Y (a * b) (round (a * b)) < radius
  gap : ∀ a ∈ candidate, ∀ b ∈ candidate,
    hammingDistance Y a b < radius ∨
      4 * radius ≤ hammingDistance Y a b

/-- The symmetric defect condition used for cluster representatives.  The
inverse clause makes inverse closure literal without assuming that the chosen
label set is symmetric at this finite stage. -/
def IsGood (S : Finset (Equiv.Perm Y)) (h : ℝ) (m : ℕ)
    (c : Equiv.Perm Y) : Prop :=
  ((badArcs Y S c).card : ℝ) < h * m / 2 ∧
    ((badArcs Y S c⁻¹).card : ℝ) < h * m / 2

/-- A small normalized centralizer defect puts a permutation and its inverse
in the symmetric candidate set at the one-fifth scale. -/
theorem isGood_clusterScale_of_ratio_lt
    (S : Finset (Equiv.Perm Y)) {h : ℝ} (hh : 0 < h)
    (c : Equiv.Perm Y) (hcard : 10 ≤ Fintype.card Y)
    (hratio : ((badArcs Y S c).card : ℝ) / Fintype.card Y < h / 20) :
    IsGood Y S h (clusterScale Y) c := by
  have hcardReal : (0 : ℝ) < Fintype.card Y := by
    exact_mod_cast (show 0 < Fintype.card Y by omega)
  have hfloorNat : Fintype.card Y ≤ 10 * clusterScale Y := by
    unfold clusterScale
    omega
  have hfloorReal : (Fintype.card Y : ℝ) ≤ 10 * clusterScale Y := by
    exact_mod_cast hfloorNat
  have hbad : ((badArcs Y S c).card : ℝ) <
      h * clusterScale Y / 2 := by
    rw [div_lt_iff₀ hcardReal] at hratio
    have hscaled : h / 20 * Fintype.card Y ≤
        h / 20 * (10 * clusterScale Y) :=
      mul_le_mul_of_nonneg_left hfloorReal (by positivity)
    calc
      ((badArcs Y S c).card : ℝ) < h / 20 * Fintype.card Y := hratio
      _ ≤ h / 20 * (10 * clusterScale Y) := hscaled
      _ = h * clusterScale Y / 2 := by ring
  refine ⟨hbad, ?_⟩
  rw [card_badArcs_inv]
  exact hbad

/-- Every fixed second-factor element is eventually a good almost
automorphism for the first-factor labels. -/
theorem productMap_isGood_eventually
    (A : SoficApproximation (K × J)) (T : Finset K) {h : ℝ} (hh : 0 < h)
    (j : J) : ∃ N : ℕ, ∀ n ≥ N,
      IsGood (A.model n) (productLabels A n T) h
        (clusterScale (A.model n)) (A.map n (1, j)) := by
  have hdefect := badArcs_productLabels_negligible A T j
  obtain ⟨Ndefect, hNdefect⟩ := hdefect (h / 20) (by positivity)
  obtain ⟨Ncard, hNcard⟩ := A.card_tendsToInfinity 10
  refine ⟨max Ndefect Ncard, fun n hn ↦ ?_⟩
  have hnd : Ndefect ≤ n := (le_max_left _ _).trans hn
  have hnc : Ncard ≤ n := (le_max_right _ _).trans hn
  have hcard := hNcard n hnc
  apply isGood_clusterScale_of_ratio_lt (A.model n)
    (productLabels A n T) hh (A.map n (1, j)) hcard
  have habs := hNdefect n hnd
  rw [abs_of_nonneg (div_nonneg (by positivity) (by positivity))] at habs
  exact habs

theorem productMap_isGood_on_finset_eventually
    (A : SoficApproximation (K × J)) (T : Finset K) {h : ℝ} (hh : 0 < h)
    (F : Finset J) : ∃ N : ℕ, ∀ n ≥ N, ∀ j ∈ F,
      IsGood (A.model n) (productLabels A n T) h
        (clusterScale (A.model n)) (A.map n (1, j)) := by
  exact eventually_finset F
    (fun j n ↦ IsGood (A.model n) (productLabels A n T) h
      (clusterScale (A.model n)) (A.map n (1, j)))
    (fun j _ ↦ productMap_isGood_eventually A T hh j)

/-- Approximate multiplicativity is uniform on each fixed finite subset of
the second factor. -/
theorem productMap_mul_close_on_finset_eventually
    (A : SoficApproximation (K × J)) (F : Finset J) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ F, ∀ y ∈ F,
      hammingDistance (A.model n) (A.map n (1, x * y))
        (A.map n (1, x) * A.map n (1, y)) < ε := by
  obtain ⟨N, hN⟩ := eventually_finset (F.product F)
    (fun p n ↦ hammingDistance (A.model n) (A.map n (1, p.1 * p.2))
      (A.map n (1, p.1) * A.map n (1, p.2)) < ε) (by
        intro p hp
        obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
        simpa using A.asymptoticallyMultiplicative (1, p.1) (1, p.2) ε hε)
  exact ⟨N, fun n hn x hx y hy ↦ hN n hn (x, y)
    (Finset.mem_product.mpr ⟨hx, hy⟩)⟩

theorem productMap_pair_separated_eventually
    (A : SoficApproximation (K × J)) {x y : J} (hxy : x ≠ y) :
    ∃ N : ℕ, ∀ n ≥ N,
      9 / 10 < hammingDistance (A.model n) (A.map n (1, x)) (A.map n (1, y)) := by
  have hpneq : ((1 : K), x) ≠ ((1 : K), y) := by simpa using hxy
  exact A.map_pair_separated_eventually hpneq

/-- Asymptotic faithfulness is uniform over distinct pairs in a fixed finite
subset of the second factor. -/
theorem productMap_separated_on_finset_eventually
    (A : SoficApproximation (K × J)) (F : Finset J) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ F, ∀ y ∈ F, x ≠ y →
      9 / 10 < hammingDistance (A.model n) (A.map n (1, x)) (A.map n (1, y)) := by
  obtain ⟨N, hN⟩ := eventually_finset (F.product F)
    (fun p n ↦ p.1 ≠ p.2 →
      9 / 10 < hammingDistance (A.model n)
        (A.map n (1, p.1)) (A.map n (1, p.2))) (by
      intro p _
      by_cases hp : p.1 = p.2
      · exact ⟨0, fun _ _ hne ↦ (hne hp).elim⟩
      · obtain ⟨Np, hNp⟩ := productMap_pair_separated_eventually A hp
        exact ⟨Np, fun n hn _ ↦ hNp n hn⟩)
  exact ⟨N, fun n hn x hx y hy hxy ↦
    hN n hn (x, y) (Finset.mem_product.mpr ⟨hx, hy⟩) hxy⟩

/-- Distinct first-factor generators are eventually assigned distinct
permutations, so forgetting their tags loses no boundary occurrences. -/
theorem firstFactorLabels_injective_eventually
    (A : SoficApproximation (K × J)) (T : Finset K) :
    ∃ N : ℕ, ∀ n ≥ N,
      Set.InjOn (fun k : K ↦ A.map n (k, 1)) (T : Set K) := by
  obtain ⟨N, hN⟩ := eventually_finset (T.product T)
    (fun p n ↦ p.1 ≠ p.2 → A.map n (p.1, 1) ≠ A.map n (p.2, 1)) (by
      intro p _
      by_cases hp : p.1 = p.2
      · exact ⟨0, fun _ _ hne ↦ (hne hp).elim⟩
      · have hp' : (p.1, (1 : J)) ≠ (p.2, 1) := by simpa using hp
        obtain ⟨Np, hNp⟩ := A.map_pair_separated_eventually hp'
        refine ⟨Np, fun n hn _ heq ↦ ?_⟩
        have hsep := hNp n hn
        rw [heq, hammingDistance_self] at hsep
        norm_num at hsep)
  refine ⟨N, fun n hn x hx y hy hmap ↦ ?_⟩
  by_contra hxy
  exact hN n hn (x, y) (Finset.mem_product.mpr ⟨hx, hy⟩) hxy hmap

noncomputable def goodCandidates (S : Finset (Equiv.Perm Y)) (h : ℝ)
    (m : ℕ) : Finset (Equiv.Perm Y) := by
  classical
  exact Finset.univ.filter (IsGood Y S h m)

@[simp] theorem mem_goodCandidates (S : Finset (Equiv.Perm Y)) (h : ℝ)
    (m : ℕ) (c : Equiv.Perm Y) :
    c ∈ goodCandidates Y S h m ↔ IsGood Y S h m c := by
  simp [goodCandidates]

/-- Construct the finite cluster group data from a genuine rounding operation.
The two rounding assumptions mention only products of good permutations, which
is the exact scope supplied by the Kun--Thom improvement argument. -/
noncomputable def clusterData_of_rounding
    (S : Finset (Equiv.Perm Y)) {h : ℝ}
    (m : ℕ) (hm : 0 < m)
    (hsize : 5 * m ≤ Fintype.card Y)
    (hexp : HasDirectedExpansionAtScale Y S h m)
    (round : Equiv.Perm Y → Equiv.Perm Y)
    (hroundGood : ∀ a, IsGood Y S h m a → ∀ b, IsGood Y S h m b →
      IsGood Y S h m (round (a * b)))
    (hroundClose : ∀ a, IsGood Y S h m a → ∀ b, IsGood Y S h m b →
      hammingDistance Y (a * b) (round (a * b)) <
        (m : ℝ) / Fintype.card Y) : ClusterData Y where
  radius := (m : ℝ) / Fintype.card Y
  radius_pos := by
    have hmReal : (0 : ℝ) < m := by exact_mod_cast hm
    have hcard : (0 : ℝ) < Fintype.card Y := by
      exact_mod_cast (show 0 < Fintype.card Y by omega)
    exact div_pos hmReal hcard
  candidate := goodCandidates Y S h m
  one_mem := by
    rw [mem_goodCandidates]
    have hthreshold : 0 < h * (m : ℝ) / 2 := by
      have hmReal : (0 : ℝ) < m := by exact_mod_cast hm
      exact div_pos (mul_pos hexp.1 hmReal) (by norm_num)
    constructor <;> simpa [IsGood, badArcs] using hthreshold
  inv_mem := by
    intro c hc
    rw [mem_goodCandidates] at hc ⊢
    simpa [IsGood] using hc.symm
  round := round
  round_product_mem := by
    intro a ha b hb
    rw [mem_goodCandidates] at ha hb ⊢
    exact hroundGood a ha b hb
  round_product_close := by
    intro a ha b hb
    rw [mem_goodCandidates] at ha hb
    exact hroundClose a ha b hb
  gap := by
    intro a ha b hb
    rw [mem_goodCandidates] at ha hb
    apply hammingDistance_small_or_four_mul_le Y S a b m hm hsize hexp
    dsimp [IsGood] at ha hb
    norm_num [Nat.cast_add]
    linarith [ha.1, hb.1]

namespace ClusterData

variable (D : ClusterData Y)

abbrev Candidate := {p : Equiv.Perm Y // p ∈ D.candidate}

noncomputable instance candidateFintype : Fintype D.Candidate :=
  Fintype.ofFinset D.candidate fun _ ↦ Iff.rfl

/-- Being in the same small Hamming cluster. -/
def Near (a b : D.Candidate) : Prop :=
  hammingDistance Y a.1 b.1 < D.radius

theorem near_refl (a : D.Candidate) : Near Y D a a := by
  simp [Near, D.radius_pos]

theorem near_symm {a b : D.Candidate} (h : Near Y D a b) : Near Y D b a := by
  simpa [Near, hammingDistance_comm] using h

theorem near_trans {a b c : D.Candidate}
    (hab : Near Y D a b) (hbc : Near Y D b c) : Near Y D a c := by
  have htri := hammingDistance_triangle Y a.1 b.1 c.1
  have hlt : hammingDistance Y a.1 c.1 < 2 * D.radius := by
    dsimp [Near] at hab hbc
    linarith
  rcases D.gap a.1 a.2 c.1 c.2 with hac | hfar
  · exact hac
  · exfalso
    linarith [D.radius_pos]

theorem near_of_distance_lt_four {a b : D.Candidate}
    (h : hammingDistance Y a.1 b.1 < 4 * D.radius) : Near Y D a b := by
  rcases D.gap a.1 a.2 b.1 b.2 with hnear | hfar
  · exact hnear
  · exfalso
    linarith

def nearSetoid : Setoid D.Candidate where
  r := Near Y D
  iseqv := ⟨near_refl Y D, fun {_ _} h ↦ near_symm Y D h,
    fun {_ _ _} hab hbc ↦ near_trans Y D hab hbc⟩

/-- The finite quotient of good almost automorphisms by small Hamming
distance. -/
abbrev Cluster := Quotient D.nearSetoid

private def roundedMul (a b : D.Candidate) : D.Candidate :=
  ⟨D.round (a.1 * b.1), D.round_product_mem a.1 a.2 b.1 b.2⟩

private theorem roundedMul_congr {a a' b b' : D.Candidate}
    (ha : Near Y D a a') (hb : Near Y D b b') :
    Near Y D (roundedMul Y D a b) (roundedMul Y D a' b') := by
  have hra := D.round_product_close a.1 a.2 b.1 b.2
  have hrb := D.round_product_close a'.1 a'.2 b'.1 b'.2
  have hmul := hammingDistance_mul_mul_le Y a.1 b.1 a'.1 b'.1
  have htri₁ := hammingDistance_triangle Y
    (D.round (a.1 * b.1)) (a.1 * b.1) (a'.1 * b'.1)
  have htri₂ := hammingDistance_triangle Y
    (D.round (a.1 * b.1)) (a'.1 * b'.1) (D.round (a'.1 * b'.1))
  have hclose₁ : hammingDistance Y (D.round (a.1 * b.1)) (a.1 * b.1) <
      D.radius := by simpa [hammingDistance_comm] using hra
  have hlt : hammingDistance Y (D.round (a.1 * b.1))
      (D.round (a'.1 * b'.1)) < 4 * D.radius := by
    dsimp [Near] at ha hb
    linarith
  rcases D.gap _ (D.round_product_mem a.1 a.2 b.1 b.2)
      _ (D.round_product_mem a'.1 a'.2 b'.1 b'.2) with hnear | hfar
  · exact hnear
  · exfalso
    linarith

private theorem inv_congr {a b : D.Candidate} (h : Near Y D a b) :
    Near Y D (⟨a.1⁻¹, D.inv_mem a.1 a.2⟩ : D.Candidate)
      ⟨b.1⁻¹, D.inv_mem b.1 b.2⟩ := by
  simpa [Near, hammingDistance_inv] using h

noncomputable instance : One D.Cluster :=
  ⟨Quotient.mk D.nearSetoid ⟨1, D.one_mem⟩⟩

noncomputable instance : Mul D.Cluster :=
  ⟨Quotient.map₂ (roundedMul Y D) fun _ _ ha _ _ hb ↦
    roundedMul_congr Y D ha hb⟩

noncomputable instance : Inv D.Cluster :=
  ⟨Quotient.map
    (fun a : D.Candidate ↦ ⟨a.1⁻¹, D.inv_mem a.1 a.2⟩)
    (fun _ _ h ↦ inv_congr Y D h)⟩

@[simp] theorem mk_mul_mk (a b : D.Candidate) :
    (Quotient.mk D.nearSetoid a : D.Cluster) * Quotient.mk D.nearSetoid b =
      Quotient.mk D.nearSetoid (roundedMul Y D a b) := rfl

@[simp] theorem mk_inv (a : D.Candidate) :
    (Quotient.mk D.nearSetoid a : D.Cluster)⁻¹ =
      Quotient.mk D.nearSetoid
        (⟨a.1⁻¹, D.inv_mem a.1 a.2⟩ : D.Candidate) := rfl

private theorem roundedMul_one_left (a : D.Candidate) :
    Near Y D (roundedMul Y D ⟨1, D.one_mem⟩ a) a := by
  have h := D.round_product_close (1 : Equiv.Perm Y) D.one_mem a.1 a.2
  simpa [roundedMul, Near, hammingDistance_comm] using h

private theorem roundedMul_inv_left (a : D.Candidate) :
    Near Y D (roundedMul Y D
      (⟨a.1⁻¹, D.inv_mem a.1 a.2⟩ : D.Candidate) a) ⟨1, D.one_mem⟩ := by
  have h := D.round_product_close a.1⁻¹ (D.inv_mem a.1 a.2) a.1 a.2
  simpa [roundedMul, Near, hammingDistance_comm] using h

private theorem roundedMul_assoc (a b c : D.Candidate) :
    Near Y D (roundedMul Y D (roundedMul Y D a b) c)
      (roundedMul Y D a (roundedMul Y D b c)) := by
  have hab := D.round_product_close a.1 a.2 b.1 b.2
  have hbc := D.round_product_close b.1 b.2 c.1 c.2
  have hl := D.round_product_close
    (D.round (a.1 * b.1)) (D.round_product_mem a.1 a.2 b.1 b.2) c.1 c.2
  have hr := D.round_product_close
    a.1 a.2 (D.round (b.1 * c.1))
      (D.round_product_mem b.1 b.2 c.1 c.2)
  let abc : Equiv.Perm Y := a.1 * b.1 * c.1
  have hleftInner : hammingDistance Y
      (D.round (a.1 * b.1) * c.1) abc < D.radius := by
    rw [hammingDistance_right_invariant]
    simpa [hammingDistance_comm] using hab
  have hrightInner : hammingDistance Y
      (a.1 * D.round (b.1 * c.1)) abc < D.radius := by
    simpa [abc, mul_assoc, hammingDistance_left_invariant,
      hammingDistance_comm] using hbc
  have hleft : hammingDistance Y
      (D.round (D.round (a.1 * b.1) * c.1)) abc < 2 * D.radius := by
    have ht := hammingDistance_triangle Y
      (D.round (D.round (a.1 * b.1) * c.1))
      (D.round (a.1 * b.1) * c.1) abc
    have hl' : hammingDistance Y
        (D.round (D.round (a.1 * b.1) * c.1))
        (D.round (a.1 * b.1) * c.1) < D.radius := by
      simpa [hammingDistance_comm] using hl
    linarith
  have hright : hammingDistance Y abc
      (D.round (a.1 * D.round (b.1 * c.1))) < 2 * D.radius := by
    have ht := hammingDistance_triangle Y abc
      (a.1 * D.round (b.1 * c.1))
      (D.round (a.1 * D.round (b.1 * c.1)))
    have hrightInner' : hammingDistance Y abc
        (a.1 * D.round (b.1 * c.1)) < D.radius := by
      simpa [hammingDistance_comm] using hrightInner
    linarith
  have htotal := hammingDistance_triangle Y
    (D.round (D.round (a.1 * b.1) * c.1)) abc
    (D.round (a.1 * D.round (b.1 * c.1)))
  have hlt : hammingDistance Y
      (D.round (D.round (a.1 * b.1) * c.1))
      (D.round (a.1 * D.round (b.1 * c.1))) < 4 * D.radius := by
    linarith
  rcases D.gap _
      (D.round_product_mem (D.round (a.1 * b.1))
        (D.round_product_mem a.1 a.2 b.1 b.2) c.1 c.2)
      _ (D.round_product_mem a.1 a.2 (D.round (b.1 * c.1))
        (D.round_product_mem b.1 b.2 c.1 c.2)) with hnear | hfar
  · exact hnear
  · exfalso
    change 4 * D.radius ≤ hammingDistance Y
      (D.round (D.round (a.1 * b.1) * c.1))
      (D.round (a.1 * D.round (b.1 * c.1))) at hfar
    linarith

noncomputable instance : Group D.Cluster := Group.ofLeftAxioms
  (fun x y z ↦ by
    induction x using Quotient.inductionOn with
    | _ a =>
      induction y using Quotient.inductionOn with
      | _ b =>
        induction z using Quotient.inductionOn with
        | _ c => exact Quotient.sound (roundedMul_assoc Y D a b c))
  (fun x ↦ by
    induction x using Quotient.inductionOn with
    | _ a => exact Quotient.sound (roundedMul_one_left Y D a))
  (fun x ↦ by
    induction x using Quotient.inductionOn with
    | _ a => exact Quotient.sound (roundedMul_inv_left Y D a))

noncomputable instance : Fintype D.Cluster := Fintype.ofFinite D.Cluster

/-- Send a good almost automorphism to its small-distance cluster. -/
def classOf (a : D.Candidate) : D.Cluster := Quotient.mk D.nearSetoid a

theorem classOf_eq_iff {a b : D.Candidate} :
    classOf Y D a = classOf Y D b ↔ Near Y D a b := by
  exact Quotient.eq_iff_equiv

/-- A locally multiplicative and locally injective map into the cluster group
gives an LEF model after the finite cluster group is represented by its left
regular action. -/
theorem localEmbedding_of_cluster {J : Type*} [Group J]
    (s : Finset J) (f : J → D.Candidate)
    (hone : Near Y D (f 1) ⟨1, D.one_mem⟩)
    (hmul : ∀ x ∈ s, ∀ y ∈ s,
      Near Y D (f (x * y)) (roundedMul Y D (f x) (f y)))
    (hinj : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ¬ Near Y D (f x) (f y)) :
    ∃ (n : ℕ) (φ : J → Equiv.Perm (Fin n)),
      Set.InjOn φ (s : Set J) ∧ LocalMultiplicativeOn s φ := by
  let q : J → D.Cluster := fun j ↦ classOf Y D (f j)
  have q_one : q 1 = 1 := by
    exact Quotient.sound hone
  have q_mul : ∀ x ∈ s, ∀ y ∈ s, q (x * y) = q x * q y := by
    intro x hx y hy
    exact Quotient.sound (hmul x hx y hy)
  have q_inj : Set.InjOn q (s : Set J) := by
    intro x hx y hy hxy
    by_contra hne
    exact hinj x hx y hy hne ((classOf_eq_iff Y D).1 hxy)
  let e : D.Cluster ≃ Fin (Fintype.card D.Cluster) := Fintype.equivFin _
  let regular : D.Cluster → Equiv.Perm (Fin (Fintype.card D.Cluster)) :=
    fun g ↦ e.symm.trans ((Equiv.mulLeft g).trans e)
  have regular_inj : Function.Injective regular := by
    intro a b hab
    have hpoint := Equiv.congr_fun hab (e 1)
    apply e.injective
    simpa [regular, e] using hpoint
  have regular_one : regular 1 = 1 := by
    ext x
    simp [regular, e]
  have regular_mul (a b : D.Cluster) : regular (a * b) = regular a * regular b := by
    ext x
    simp [regular, e]
  refine ⟨Fintype.card D.Cluster, fun j ↦ regular (q j), ?_, ?_⟩
  · exact regular_inj.injOn.comp q_inj (Set.mapsTo_univ _ _)
  · refine ⟨?_, ?_⟩
    · rw [q_one, regular_one]
    · intro x hx y hy
      calc
        regular (q (x * y)) = regular (q x * q y) :=
          congrArg regular (q_mul x hx y hy)
        _ = regular (q x) * regular (q y) := regular_mul _ _

/-- The finite-stage criterion used in the Kun--Thom proof.  It asks only for
good representatives of `1`, the tested elements, and their tested products;
the map on every other group element is harmlessly sent to the identity
candidate. -/
theorem localEmbedding_of_finite_stage {J : Type*} [Group J]
    (s : Finset J) (p : J → Equiv.Perm Y)
    (hmemOne : p 1 ∈ D.candidate)
    (hmem : ∀ x ∈ s, p x ∈ D.candidate)
    (hmemMul : ∀ x ∈ s, ∀ y ∈ s, p (x * y) ∈ D.candidate)
    (hone : hammingDistance Y (p 1) 1 < 4 * D.radius)
    (hmul : ∀ x ∈ s, ∀ y ∈ s,
      hammingDistance Y (p (x * y)) (p x * p y) < 3 * D.radius)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
      4 * D.radius ≤ hammingDistance Y (p x) (p y)) :
    ∃ (n : ℕ) (φ : J → Equiv.Perm (Fin n)),
      Set.InjOn φ (s : Set J) ∧ LocalMultiplicativeOn s φ := by
  let f : J → D.Candidate := fun j ↦
    if hj : p j ∈ D.candidate then ⟨p j, hj⟩ else ⟨1, D.one_mem⟩
  have f_one : f 1 = ⟨p 1, hmemOne⟩ := by
    simp [f, hmemOne]
  have f_mem (x : J) (hx : x ∈ s) : f x = ⟨p x, hmem x hx⟩ := by
    simp [f, hmem x hx]
  have f_mul (x : J) (hx : x ∈ s) (y : J) (hy : y ∈ s) :
      f (x * y) = ⟨p (x * y), hmemMul x hx y hy⟩ := by
    simp [f, hmemMul x hx y hy]
  apply localEmbedding_of_cluster Y D s f
  · apply near_of_distance_lt_four Y D
    simpa [f_one] using hone
  · intro x hx y hy
    apply near_of_distance_lt_four Y D
    have hround := D.round_product_close (p x) (hmem x hx) (p y) (hmem y hy)
    have hmul' := hmul x hx y hy
    have htri := hammingDistance_triangle Y
      (p (x * y)) (p x * p y) (D.round (p x * p y))
    simpa [f_mul x hx y hy, f_mem x hx, f_mem y hy, roundedMul] using
      (show hammingDistance Y (p (x * y)) (D.round (p x * p y)) <
          4 * D.radius by linarith)
  · intro x hx y hy hxy hnear
    have hnear' : hammingDistance Y (p x) (p y) < D.radius := by
      simpa [Near, f_mem x hx, f_mem y hy] using hnear
    have hfar := hsep x hx y hy hxy
    linarith [D.radius_pos]

noncomputable def finiteControl {J : Type*} [Group J] (s : Finset J) : Finset J := by
  classical
  exact insert 1 (s ∪ (s.product s).image fun p ↦ p.1 * p.2)

@[simp] theorem one_mem_finiteControl {J : Type*} [Group J] (s : Finset J) :
    1 ∈ finiteControl s := by
  simp [finiteControl]

theorem mem_finiteControl {J : Type*} [Group J] {s : Finset J} {x : J}
    (hx : x ∈ s) : x ∈ finiteControl s := by
  simp [finiteControl, hx]

theorem mul_mem_finiteControl {J : Type*} [Group J] {s : Finset J} {x y : J}
    (hx : x ∈ s) (hy : y ∈ s) : x * y ∈ finiteControl s := by
  simp only [finiteControl, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
  right
  right
  exact ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩

/-- Kernel-checked Kun--Thom assembly after isolating the sole deep input:
products of good almost automorphisms can eventually be rounded back to good
ones within the one-fifth Hamming radius.  No property-(T) assumption is hidden
in this theorem; the subsequent improvement theorem must prove `hround`. -/
theorem isLEF_of_product_rounding
    (A : SoficApproximation (K × J)) (T : Finset K) {h : ℝ} (hh : 0 < h)
    (hexp : ∃ Nexp, ∀ n ≥ Nexp,
      HasDirectedExpansionAtScale (A.model n) (productLabels A n T) h
        (clusterScale (A.model n)))
    (hround : ∃ Nround, ∀ n ≥ Nround,
      ∃ round : Equiv.Perm (A.model n) → Equiv.Perm (A.model n),
        (∀ a, IsGood (A.model n) (productLabels A n T) h
            (clusterScale (A.model n)) a →
          ∀ b, IsGood (A.model n) (productLabels A n T) h
            (clusterScale (A.model n)) b →
          IsGood (A.model n) (productLabels A n T) h
            (clusterScale (A.model n)) (round (a * b))) ∧
        (∀ a, IsGood (A.model n) (productLabels A n T) h
            (clusterScale (A.model n)) a →
          ∀ b, IsGood (A.model n) (productLabels A n T) h
            (clusterScale (A.model n)) b →
          hammingDistance (A.model n) (a * b) (round (a * b)) <
            clusterRadius (A.model n))) : IsLEF J := by
  intro s
  obtain ⟨Nexp, hNexp⟩ := hexp
  obtain ⟨Nround, hNround⟩ := hround
  obtain ⟨Ngood, hNgood⟩ :=
    productMap_isGood_on_finset_eventually A T hh (finiteControl s)
  obtain ⟨Nmul, hNmul⟩ :=
    productMap_mul_close_on_finset_eventually A s (show (0 : ℝ) < 1 / 10 by norm_num)
  obtain ⟨Nsep, hNsep⟩ := productMap_separated_on_finset_eventually A s
  obtain ⟨None, hNone⟩ := A.map_one_close (1 / 10) (by norm_num)
  obtain ⟨Ncard, hNcard⟩ := A.card_tendsToInfinity 10
  let n := max Nexp (max Nround (max Ngood (max Nmul (max Nsep (max None Ncard)))))
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
  let D : ClusterData (A.model n) := clusterData_of_rounding (A.model n)
    (productLabels A n T) (clusterScale (A.model n)) hm hfive hexpn
      round hroundGood hroundClose
  have hradius : D.radius = clusterRadius (A.model n) := rfl
  have hradiusLower : (1 : ℝ) / 10 ≤ D.radius := by
    rw [hradius]
    exact one_tenth_le_clusterRadius _ hcard
  have hradiusUpper : D.radius ≤ (1 : ℝ) / 5 := by
    rw [hradius]
    exact clusterRadius_le_one_fifth _ (by omega)
  apply localEmbedding_of_finite_stage (A.model n) D s (fun j ↦ A.map n (1, j))
  · dsimp [D, clusterData_of_rounding]
    rw [mem_goodCandidates]
    simpa using hNgood n hngood 1 (one_mem_finiteControl s)
  · intro x hx
    dsimp [D, clusterData_of_rounding]
    rw [mem_goodCandidates]
    exact hNgood n hngood x (mem_finiteControl hx)
  · intro x hx y hy
    dsimp [D, clusterData_of_rounding]
    rw [mem_goodCandidates]
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

/-- Finite-stage cluster models for every finite subset are exactly enough to
prove that a group is LEF.  Later analytic modules must construct all of this
data from a concrete essential-expander sofic approximation. -/
theorem isLEF_of_cluster_models {J : Type*} [Group J]
    (hmodels : ∀ s : Finset J,
      ∃ (Y : FiniteModel) (D : ClusterData Y) (f : J → D.Candidate),
        Near Y D (f 1) ⟨1, D.one_mem⟩ ∧
        (∀ x ∈ s, ∀ y ∈ s,
          Near Y D (f (x * y)) (roundedMul Y D (f x) (f y))) ∧
        (∀ x ∈ s, ∀ y ∈ s, x ≠ y → ¬ Near Y D (f x) (f y))) :
    IsLEF J := by
  intro s
  obtain ⟨Y, D, f, hone, hmul, hinj⟩ := hmodels s
  exact localEmbedding_of_cluster Y D s f hone hmul hinj

end ClusterData

end AlmostAutomorphism
end NonsoficGroupsExist
