import NonsoficGroupsExist.Sofic.NearAction
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Finset.SymmDiff

/-!
# The Tarski--Hall finite-set theorem for near actions

This file proves the hard compactness step in the Elek--Szabó
characterization.  If a finite family of permutations preserves a finitely
additive probability on the full power set, then, away from any prescribed
null set, it has a nonempty finite set with arbitrarily small one-sided
boundary under every permutation in the family.

The proof is Tarski's paradoxical-decomposition argument.  If no such finite
set exists, repeated finite expansion gives a factor-two neighbourhood.
Infinite Hall marriage then embeds two disjoint copies of a conull set into
the whole space, piecewise by measure-preserving permutations.  Finite
additivity assigns measure two to their disjoint union, a contradiction.
-/

namespace NonsoficGroupsExist

open Set
open scoped BigOperators Pointwise

universe u

namespace FullFinitelyAdditiveProbability

variable {X : Type u} (m : FullFinitelyAdditiveProbability X)

/-- A subset of a null set is null. -/
theorem eq_zero_of_subset {A B : Set X} (hAB : A ⊆ B) (hB : m B = 0) :
    m A = 0 := by
  have hle := m.mono hAB
  have hnonneg := m.nonnegative A
  linarith

/-- A finite union of null sets is null. -/
theorem biUnion_finset_eq_zero {ι : Type*} (s : Finset ι) (A : ι → Set X)
    (hA : ∀ i ∈ s, m (A i) = 0) : m (⋃ i ∈ s, A i) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hi0 : m (A i) = 0 := hA i (Finset.mem_insert_self i s)
      have hs0 : m (⋃ j ∈ s, A j) = 0 :=
        ih fun j hj ↦ hA j (Finset.mem_insert_of_mem hj)
      let B : Set X := ⋃ j ∈ s, A j
      have hdiff : m (A i \ B) = 0 :=
        m.eq_zero_of_subset Set.sdiff_subset hi0
      have hdis : Disjoint (A i \ B) B := Set.disjoint_sdiff_left
      have hunion : (⋃ j ∈ insert i s, A j) = (A i \ B) ∪ B := by
        calc
          (⋃ j ∈ insert i s, A j) = A i ∪ B := by simp [B]
          _ = (A i \ B) ∪ B := by
            ext x
            by_cases hx : x ∈ B <;> simp [hx]
      rw [hunion, m.union_of_disjoint_apply hdis, hdiff, hs0, zero_add]

/-- The union of two null sets is null. -/
theorem union_eq_zero {A B : Set X} (hA : m A = 0) (hB : m B = 0) :
    m (A ∪ B) = 0 := by
  classical
  have h := m.biUnion_finset_eq_zero ({false, true} : Finset Bool)
    (fun b ↦ if b then A else B) (by
      intro b hb
      cases b <;> simp [hA, hB])
  have heq : (⋃ b ∈ ({false, true} : Finset Bool), if b then A else B) = A ∪ B := by
    ext x
    simp [or_comm]
  rwa [heq] at h

/-- A finite disjoint union has measure equal to the finite sum. -/
theorem measure_biUnion_finset {ι : Type*} (s : Finset ι) (A : ι → Set X)
    (hdis : Set.Pairwise (↑s) fun i j ↦ Disjoint (A i) (A j)) :
    m (⋃ i ∈ s, A i) = ∑ i ∈ s, m (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hAi : Disjoint (A i) (⋃ j ∈ s, A j) := by
        rw [Set.disjoint_iUnion_right]
        intro j
        rw [Set.disjoint_iUnion_right]
        intro hj
        exact hdis (Finset.mem_insert_self i s)
          (Finset.mem_insert_of_mem hj) (fun hij ↦ hi (hij ▸ hj))
      have hs : Set.Pairwise (↑s) fun j k ↦ Disjoint (A j) (A k) := by
        intro j hj k hk hjk
        exact hdis (Finset.mem_insert_of_mem hj)
          (Finset.mem_insert_of_mem hk) hjk
      have hunion : (⋃ j ∈ insert i s, A j) = A i ∪ ⋃ j ∈ s, A j := by
        simp
      rw [hunion, m.union_of_disjoint_apply hAi, ih hs, Finset.sum_insert hi]

/-- Removing a null set does not change measure. -/
theorem measure_diff_of_null {A N : Set X} (hN : m N = 0) :
    m (A \ N) = m A := by
  have hdis : Disjoint (A \ N) (A ∩ N) := by
    rw [Set.disjoint_left]
    intro x hx hxi
    exact hx.2 hxi.2
  have hunion : (A \ N) ∪ (A ∩ N) = A := by
    ext x
    simp only [Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  have hinter : m (A ∩ N) = 0 :=
    m.eq_zero_of_subset Set.inter_subset_right hN
  calc
    m (A \ N) = m (A \ N) + m (A ∩ N) := by rw [hinter, add_zero]
    _ = m A := by rw [← m.union_of_disjoint_apply hdis, hunion]

theorem measure_compl_of_null {N : Set X} (hN : m N = 0) : m Nᶜ = 1 := by
  apply m.eq_one_of_compl_eq_zero
  simpa using hN

end FullFinitelyAdditiveProbability

/-! ## Measure-preserving permutations and finite words -/

/-- A permutation preserves a full-power-set finitely additive probability. -/
def PreservesFullMeasure {X : Type u} (m : FullFinitelyAdditiveProbability X)
    (p : Equiv.Perm X) : Prop :=
  ∀ A : Set X, m (p '' A) = m A

namespace PreservesFullMeasure

variable {X : Type u} {m : FullFinitelyAdditiveProbability X}

theorem one : PreservesFullMeasure m 1 := by
  intro A
  simp

theorem mul {p q : Equiv.Perm X} (hp : PreservesFullMeasure m p)
    (hq : PreservesFullMeasure m q) : PreservesFullMeasure m (p * q) := by
  intro A
  change m ((fun x ↦ p (q x)) '' A) = m A
  rw [← Set.image_image, hp, hq]

theorem inv {p : Equiv.Perm X} (hp : PreservesFullMeasure m p) :
    PreservesFullMeasure m p⁻¹ := by
  intro A
  have h := hp (p.symm '' A)
  have himage : p '' (p.symm '' A) = A := p.image_symm_image A
  rw [himage] at h
  exact h.symm

theorem preimage {p : Equiv.Perm X} (hp : PreservesFullMeasure m p)
    (A : Set X) : m (p ⁻¹' A) = m A := by
  have heq : p ⁻¹' A = p.symm '' A := by
    ext x
    simp
  rw [heq]
  exact hp.inv A

end PreservesFullMeasure

namespace TarskiHall

noncomputable section

variable {X : Type u}

local instance instDecidableEqX : DecidableEq X := Classical.decEq X
local instance instDecidableEqPerm : DecidableEq (Equiv.Perm X) := Classical.decEq _

/-- Permutation words of exactly `n` letters from `K`.  If `1 ∈ K`, these
sets are increasing in `n`, since shorter words can be padded by identities. -/
def words (K : Finset (Equiv.Perm X)) : ℕ → Finset (Equiv.Perm X)
  | 0 => {1}
  | n + 1 => K.biUnion fun p ↦ (words K n).image fun q ↦ p * q

@[simp] theorem words_zero (K : Finset (Equiv.Perm X)) : words K 0 = {1} := rfl

theorem mem_words_succ {K : Finset (Equiv.Perm X)} {n : ℕ}
    {p q : Equiv.Perm X} (hp : p ∈ K) (hq : q ∈ words K n) :
    p * q ∈ words K (n + 1) := by
  unfold words
  apply Finset.mem_biUnion.mpr
  refine ⟨p, hp, Finset.mem_image.mpr ?_⟩
  exact ⟨q, hq, rfl⟩

theorem words_mono_step {K : Finset (Equiv.Perm X)} (h1 : 1 ∈ K) (n : ℕ) :
    words K n ⊆ words K (n + 1) := by
  intro q hq
  simpa using mem_words_succ h1 hq

theorem words_mono {K : Finset (Equiv.Perm X)} (h1 : 1 ∈ K)
    {a b : ℕ} (hab : a ≤ b) : words K a ⊆ words K b := by
  induction b, hab using Nat.le_induction with
  | base => exact fun _ h ↦ h
  | succ b hab ih => exact fun q hq ↦ words_mono_step h1 b (ih hq)

/-- The finite `n`-step neighbourhood of `F`. -/
def reachable (K : Finset (Equiv.Perm X)) (n : ℕ) (F : Finset X) : Finset X :=
  (words K n).biUnion fun p ↦ F.image p

theorem subset_reachable {K : Finset (Equiv.Perm X)} (h1 : 1 ∈ K)
    (n : ℕ) (F : Finset X) : F ⊆ reachable K n F := by
  intro x hx
  have hmem : (1 : Equiv.Perm X) ∈ words K n := by
    exact words_mono h1 (Nat.zero_le n) (by simp)
  exact Finset.mem_biUnion.mpr ⟨1, hmem, by simpa using hx⟩

theorem reachable_mono_words {K : Finset (Equiv.Perm X)} (h1 : 1 ∈ K)
    {a b : ℕ} (hab : a ≤ b) (F : Finset X) :
    reachable K a F ⊆ reachable K b F := by
  intro x hx
  obtain ⟨p, hp, hxp⟩ := Finset.mem_biUnion.mp hx
  exact Finset.mem_biUnion.mpr ⟨p, words_mono h1 hab hp, hxp⟩

theorem image_reachable_subset_succ {K : Finset (Equiv.Perm X)}
    {p : Equiv.Perm X} (hp : p ∈ K) (n : ℕ) (F : Finset X) :
    (reachable K n F).image p ⊆ reachable K (n + 1) F := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  rw [reachable] at hx
  obtain ⟨q, hq, hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨z, hz, hqz⟩ := Finset.mem_image.mp hx
  subst x
  apply Finset.mem_biUnion.mpr
  refine ⟨p * q, mem_words_succ hp hq, ?_⟩
  exact Finset.mem_image.mpr ⟨z, hz, by simp [Equiv.Perm.mul_apply]⟩

theorem reachable_union_singletons (K : Finset (Equiv.Perm X)) (n : ℕ)
    (F : Finset X) :
    reachable K n F = F.biUnion fun x ↦ reachable K n {x} := by
  ext y
  constructor
  · intro hy
    rw [reachable] at hy
    obtain ⟨p, hp, hy⟩ := Finset.mem_biUnion.mp hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
    apply Finset.mem_biUnion.mpr
    refine ⟨x, hx, ?_⟩
    rw [reachable]
    apply Finset.mem_biUnion.mpr
    exact ⟨p, hp, Finset.mem_image.mpr ⟨x, by simp, hxy⟩⟩
  · intro hy
    obtain ⟨x, hx, hy⟩ := Finset.mem_biUnion.mp hy
    rw [reachable] at hy ⊢
    obtain ⟨p, hp, hy⟩ := Finset.mem_biUnion.mp hy
    obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp hy
    have hzx : z = x := by simpa using hz
    subst z
    exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_image.mpr ⟨x, hx, hzy⟩⟩

/-- Points whose whole `n`-step `K`-neighbourhood avoids `N`. -/
def goodSet (K : Finset (Equiv.Perm X)) (n : ℕ) (N : Set X) : Set X :=
  {x | ∀ p ∈ words K n, p x ∉ N}

theorem reachable_disjoint_null {K : Finset (Equiv.Perm X)} {n : ℕ}
    {N : Set X} {F : Finset X} (hF : ∀ x ∈ F, x ∈ goodSet K n N) :
    Disjoint (↑(reachable K n F) : Set X) N := by
  rw [Set.disjoint_left]
  intro y hy hN
  change y ∈ reachable K n F at hy
  rw [reachable] at hy
  obtain ⟨p, hp, hy⟩ := Finset.mem_biUnion.mp hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  exact hF x hx p hp hN

/-- Every word in measure-preserving generators preserves the measure. -/
theorem words_preserve {m : FullFinitelyAdditiveProbability X}
    {K : Finset (Equiv.Perm X)}
    (hK : ∀ p ∈ K, PreservesFullMeasure m p) {n : ℕ} {q : Equiv.Perm X}
    (hq : q ∈ words K n) : PreservesFullMeasure m q := by
  induction n generalizing q with
  | zero =>
      rw [words_zero] at hq
      have hq1 : q = 1 := Finset.mem_singleton.mp hq
      subst q
      exact PreservesFullMeasure.one
  | succ n ih =>
      rw [words] at hq
      obtain ⟨p, hp, hq⟩ := Finset.mem_biUnion.mp hq
      obtain ⟨r, hr, hpr⟩ := Finset.mem_image.mp hq
      have hpres := (hK p hp).mul (ih hr)
      rw [hpr] at hpres
      exact hpres

/-- The complement of `goodSet` is a finite union of null preimages, hence is
null. -/
theorem measure_compl_goodSet_eq_zero (m : FullFinitelyAdditiveProbability X)
    {K : Finset (Equiv.Perm X)} (hK : ∀ p ∈ K, PreservesFullMeasure m p)
    (n : ℕ) {N : Set X} (hN : m N = 0) :
    m (goodSet K n N)ᶜ = 0 := by
  classical
  have heq : (goodSet K n N)ᶜ = ⋃ p ∈ words K n, p ⁻¹' N := by
    ext x
    simp [goodSet]
  rw [heq]
  apply m.biUnion_finset_eq_zero
  intro p hp
  rw [(words_preserve hK hp).preimage]
  exact hN

theorem measure_goodSet_eq_one (m : FullFinitelyAdditiveProbability X)
    {K : Finset (Equiv.Perm X)} (hK : ∀ p ∈ K, PreservesFullMeasure m p)
    (n : ℕ) {N : Set X} (hN : m N = 0) :
    m (goodSet K n N) = 1 := by
  exact m.eq_one_of_compl_eq_zero (measure_compl_goodSet_eq_zero m hK n hN)

theorem goodSet_nonempty (m : FullFinitelyAdditiveProbability X)
    {K : Finset (Equiv.Perm X)} (hK : ∀ p ∈ K, PreservesFullMeasure m p)
    (n : ℕ) {N : Set X} (hN : m N = 0) :
    (goodSet K n N).Nonempty := by
  by_contra hempty
  have hone := measure_goodSet_eq_one m hK n hN
  rw [Set.not_nonempty_iff_eq_empty.mp hempty] at hone
  simp at hone

/-! ## Finite expansion -/

/-- The part of `p F` that escapes `F`. -/
def escape (p : Equiv.Perm X) (F : Finset X) : Finset X := F.image p \ F

/-- Adding one generator step contains the previous neighbourhood together
with all points escaping from it under any chosen generator. -/
theorem card_reachable_add_escape_le {K : Finset (Equiv.Perm X)}
    (h1 : 1 ∈ K) {p : Equiv.Perm X} (hp : p ∈ K) (n : ℕ) (F : Finset X) :
    (reachable K n F).card + (escape p (reachable K n F)).card ≤
      (reachable K (n + 1) F).card := by
  let L := reachable K n F
  have hL : L ⊆ reachable K (n + 1) F :=
    reachable_mono_words h1 (Nat.le_succ n) F
  have hE : escape p L ⊆ reachable K (n + 1) F := by
    intro x hx
    exact image_reachable_subset_succ hp n F (Finset.mem_sdiff.mp hx).1
  have hunion : L ∪ escape p L ⊆ reachable K (n + 1) F :=
    Finset.union_subset hL hE
  have hcard : L.card + (escape p L).card ≤ (reachable K (n + 1) F).card := by
    calc
      L.card + (escape p L).card = (L ∪ escape p L).card := by
        rw [Finset.card_union_of_disjoint]
        exact Finset.disjoint_sdiff
      _ ≤ (reachable K (n + 1) F).card := Finset.card_le_card hunion
  simpa [L] using hcard

/-- If every nonempty finite set avoiding `N` expands by a factor
`1 + δ`, then the `n`-step neighbourhood of an avoiding set has the
corresponding exponential lower bound. -/
theorem pow_mul_card_le_reachable
    {K P : Finset (Equiv.Perm X)} (h1 : 1 ∈ K) (hPK : P ⊆ K)
    {N : Set X} {δ : ℝ} (hδ : 0 ≤ δ)
    (hexpand : ∀ L : Finset X, L.Nonempty → Disjoint (↑L : Set X) N →
      ∃ p ∈ P, δ * (L.card : ℝ) ≤ (escape p L).card)
    (F : Finset X) (hF : F.Nonempty) (n : ℕ)
    (havoid : ∀ k ≤ n, Disjoint (↑(reachable K k F) : Set X) N) :
    (1 + δ) ^ n * (F.card : ℝ) ≤ (reachable K n F).card := by
  induction n with
  | zero => simp [reachable]
  | succ n ih =>
      let L := reachable K n F
      have hFnL : F ⊆ L := subset_reachable h1 n F
      have hLne : L.Nonempty := hF.mono hFnL
      obtain ⟨p, hpP, hp⟩ := hexpand L hLne (havoid n (Nat.le_succ n))
      have hpK : p ∈ K := hPK hpP
      have hcardNat := card_reachable_add_escape_le h1 hpK n F
      have hcardReal : (L.card : ℝ) + (escape p L).card ≤
          ((reachable K (n + 1) F).card : ℝ) := by
        exact_mod_cast hcardNat
      have hgrow : (1 + δ) * (L.card : ℝ) ≤
          ((reachable K (n + 1) F).card : ℝ) := by
        calc
          (1 + δ) * (L.card : ℝ) = (L.card : ℝ) + δ * L.card := by ring
          _ ≤ (L.card : ℝ) + (escape p L).card := by linarith
          _ ≤ ((reachable K (n + 1) F).card : ℝ) := hcardReal
      calc
        (1 + δ) ^ (n + 1) * (F.card : ℝ) =
            (1 + δ) * ((1 + δ) ^ n * F.card) := by ring
        _ ≤ (1 + δ) * (L.card : ℝ) := by
          exact mul_le_mul_of_nonneg_left (ih (fun k hk ↦ havoid k (hk.trans (Nat.le_succ n))))
            (by linarith)
        _ ≤ ((reachable K (n + 1) F).card : ℝ) := hgrow

/-! ## The finitely additive obstruction to a paradoxical matching -/

/-- Two disjoint copies of a measure-one set cannot be embedded into the
ambient set by finitely many measure-preserving pieces.  This is the precise
finite-additivity contradiction used after Hall's theorem. -/
theorem no_piecewise_double_embedding
    (m : FullFinitelyAdditiveProbability X) (A : Set X) (hA : m A = 1)
    (W : Finset (Equiv.Perm X))
    (hW : ∀ q ∈ W, PreservesFullMeasure m q)
    (f : {x // x ∈ A} × Bool → X) (hf : Function.Injective f)
    (label : {x // x ∈ A} → Bool → Equiv.Perm X)
    (hlabelW : ∀ a b, label a b ∈ W)
    (hlabel : ∀ a b, label a b a.1 = f (a, b)) : False := by
  let piece (b : Bool) (q : Equiv.Perm X) : Set X :=
    {x | ∃ hx : x ∈ A, label ⟨x, hx⟩ b = q}
  have hpiece_union (b : Bool) : (⋃ q ∈ W, piece b q) = A := by
    ext x
    constructor
    · intro hx
      obtain ⟨q, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hqW, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hxA, _⟩ := hx
      exact hxA
    · intro hx
      apply Set.mem_iUnion.mpr
      refine ⟨label ⟨x, hx⟩ b, ?_⟩
      apply Set.mem_iUnion.mpr
      exact ⟨hlabelW ⟨x, hx⟩ b, hx, rfl⟩
  have hpiece_disjoint (b : Bool) :
      Set.Pairwise (↑W) fun q r ↦ Disjoint (piece b q) (piece b r) := by
    intro q hq r hr hqr
    rw [Set.disjoint_left]
    intro x hxq hxr
    obtain ⟨hxA, hxqlabel⟩ := hxq
    obtain ⟨hxA', hxrlabel⟩ := hxr
    have hsub : (⟨x, hxA⟩ : {x // x ∈ A}) = ⟨x, hxA'⟩ := Subtype.ext rfl
    apply hqr
    calc
      q = label ⟨x, hxA⟩ b := hxqlabel.symm
      _ = label ⟨x, hxA'⟩ b := by rw [hsub]
      _ = r := hxrlabel
  let covered (b : Bool) : Set X := ⋃ q ∈ W, Set.image q (piece b q)
  have himage_disjoint (b : Bool) :
      Set.Pairwise (↑W : Set (Equiv.Perm X)) fun q r ↦
        Disjoint (Set.image q (piece b q)) (Set.image r (piece b r)) := by
    intro q hq r hr hqr
    rw [Set.disjoint_left]
    intro y hyq hyr
    obtain ⟨x, hxpiece, hxy⟩ := hyq
    obtain ⟨z, hzpiece, hzy⟩ := hyr
    obtain ⟨hxA, hxlabel⟩ := hxpiece
    obtain ⟨hzA, hzlabel⟩ := hzpiece
    have hfx : f (⟨x, hxA⟩, b) = y := by
      rw [← hlabel ⟨x, hxA⟩ b, hxlabel, hxy]
    have hfz : f (⟨z, hzA⟩, b) = y := by
      rw [← hlabel ⟨z, hzA⟩ b, hzlabel, hzy]
    have hpairs : ((⟨x, hxA⟩ : {x // x ∈ A}), b) =
        ((⟨z, hzA⟩ : {x // x ∈ A}), b) := hf (hfx.trans hfz.symm)
    have hsub : (⟨x, hxA⟩ : {x // x ∈ A}) = ⟨z, hzA⟩ :=
      congrArg Prod.fst hpairs
    apply hqr
    calc
      q = label ⟨x, hxA⟩ b := hxlabel.symm
      _ = label ⟨z, hzA⟩ b := by rw [hsub]
      _ = r := hzlabel
  have hcovered (b : Bool) : m (covered b) = 1 := by
    calc
      m (covered b) = ∑ q ∈ W, m (q '' piece b q) := by
        exact m.measure_biUnion_finset W (fun q ↦ q '' piece b q) (himage_disjoint b)
      _ = ∑ q ∈ W, m (piece b q) := by
        apply Finset.sum_congr rfl
        intro q hq
        exact hW q hq (piece b q)
      _ = m (⋃ q ∈ W, piece b q) := by
        symm
        exact m.measure_biUnion_finset W (piece b) (hpiece_disjoint b)
      _ = 1 := by rw [hpiece_union, hA]
  have hcovered_disjoint : Disjoint (covered false) (covered true) := by
    rw [Set.disjoint_left]
    intro y hyfalse hytrue
    change y ∈ (⋃ q ∈ W, Set.image q (piece false q)) at hyfalse
    change y ∈ (⋃ q ∈ W, Set.image q (piece true q)) at hytrue
    obtain ⟨q, hyfalse⟩ := Set.mem_iUnion.mp hyfalse
    obtain ⟨hqW, hyfalse⟩ := Set.mem_iUnion.mp hyfalse
    obtain ⟨x, hxpiece, hxy⟩ := hyfalse
    obtain ⟨r, hytrue⟩ := Set.mem_iUnion.mp hytrue
    obtain ⟨hrW, hytrue⟩ := Set.mem_iUnion.mp hytrue
    obtain ⟨z, hzpiece, hzy⟩ := hytrue
    obtain ⟨hxA, hxlabel⟩ := hxpiece
    obtain ⟨hzA, hzlabel⟩ := hzpiece
    have hfx : f (⟨x, hxA⟩, false) = y := by
      rw [← hlabel ⟨x, hxA⟩ false, hxlabel, hxy]
    have hfz : f (⟨z, hzA⟩, true) = y := by
      rw [← hlabel ⟨z, hzA⟩ true, hzlabel, hzy]
    have hpairs : ((⟨x, hxA⟩ : {x // x ∈ A}), false) =
        ((⟨z, hzA⟩ : {x // x ∈ A}), true) :=
      hf (hfx.trans hfz.symm)
    have hbool : false = true := congrArg Prod.snd hpairs
    exact Bool.false_ne_true hbool
  have hunion_measure : m (covered false ∪ covered true) = 2 := by
    rw [m.union_of_disjoint_apply hcovered_disjoint, hcovered, hcovered]
    norm_num
  have hle := m.le_one (covered false ∪ covered true)
  rw [hunion_measure] at hle
  norm_num at hle

/-! ## The Tarski--Hall finite-set theorem -/

/-- A finite family of measure-preserving permutations has a nonempty finite
set with arbitrarily small one-sided boundary, and that finite set may be
chosen to avoid any prescribed null set.  This is the compactness theorem
used by Elek--Szabó in the reverse implication of their characterization. -/
theorem exists_finite_small_boundary_avoiding_null
    (m : FullFinitelyAdditiveProbability X) (P : Finset (Equiv.Perm X))
    (hP : ∀ p ∈ P, PreservesFullMeasure m p)
    {N : Set X} (hN : m N = 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ F : Finset X, F.Nonempty ∧ Disjoint (↑F : Set X) N ∧
      ∀ p ∈ P, ((escape p F).card : ℝ) < δ * F.card := by
  by_contra hcontra
  have hexpand : ∀ L : Finset X, L.Nonempty → Disjoint (↑L : Set X) N →
      ∃ p ∈ P, δ * (L.card : ℝ) ≤ (escape p L).card := by
    intro L hLne hLN
    by_contra hnone
    have hsmall : ∀ p ∈ P, ((escape p L).card : ℝ) < δ * L.card := by
      intro p hp
      exact lt_of_not_ge (fun hge ↦ hnone ⟨p, hp, hge⟩)
    exact hcontra ⟨L, hLne, hLN, hsmall⟩
  obtain ⟨r, hr⟩ :=
    Real.exists_natCast_add_one_lt_pow_of_one_lt (show (1 : ℝ) < 1 + δ by linarith)
  have hr0 : r ≠ 0 := by
    intro hrzero
    subst r
    norm_num at hr
  have htwo : (2 : ℝ) ≤ (1 + δ) ^ r := by
    have htwoNat : 2 ≤ r + 1 := Nat.succ_le_succ (Nat.one_le_iff_ne_zero.mpr hr0)
    have htwoCast : (2 : ℝ) ≤ (r + 1 : ℕ) := by exact_mod_cast htwoNat
    norm_num at htwoCast
    exact htwoCast.trans hr.le
  let K : Finset (Equiv.Perm X) := insert 1 P
  have h1K : (1 : Equiv.Perm X) ∈ K := Finset.mem_insert_self _ _
  have hPK : P ⊆ K := Finset.subset_insert 1 P
  have hK : ∀ q ∈ K, PreservesFullMeasure m q := by
    intro q hq
    change q ∈ insert 1 P at hq
    rw [Finset.mem_insert] at hq
    rcases hq with rfl | hq
    · exact PreservesFullMeasure.one
    · exact hP q hq
  let A : Set X := goodSet K r N
  have hA : m A = 1 := measure_goodSet_eq_one m hK r hN
  let neighbours : {x // x ∈ A} × Bool → Finset X :=
    fun a ↦ reachable K r {a.1.1}
  have hHall : ∀ S : Finset ({x // x ∈ A} × Bool),
      S.card ≤ (S.biUnion neighbours).card := by
    intro S
    let L : Finset X := S.image fun a ↦ a.1.1
    have hSle : S.card ≤ 2 * L.card := by
      let embed : {x // x ∈ A} × Bool → X × Bool := fun a ↦ (a.1.1, a.2)
      have hinj : Function.Injective embed := by
        intro a b hab
        apply Prod.ext
        · apply Subtype.ext
          exact congrArg (fun y : X × Bool ↦ y.1) hab
        · exact congrArg (fun y : X × Bool ↦ y.2) hab
      have himage : S.image embed ⊆ L ×ˢ {false, true} := by
        intro y hy
        obtain ⟨a, haS, rfl⟩ := Finset.mem_image.mp hy
        apply Finset.mem_product.mpr
        exact ⟨Finset.mem_image.mpr ⟨a, haS, rfl⟩, by cases a.2 <;> simp⟩
      calc
        S.card = (S.image embed).card :=
          (Finset.card_image_of_injective S hinj).symm
        _ ≤ (L ×ˢ {false, true}).card := Finset.card_le_card himage
        _ = 2 * L.card := by simp [mul_comm]
    have hneighbours : S.biUnion neighbours = reachable K r L := by
      rw [reachable_union_singletons]
      ext y
      simp only [Finset.mem_biUnion]
      constructor
      · rintro ⟨a, haS, hay⟩
        refine ⟨a.1.1, Finset.mem_image.mpr ⟨a, haS, rfl⟩, ?_⟩
        exact hay
      · rintro ⟨x, hxL, hxy⟩
        obtain ⟨a, haS, hax⟩ := Finset.mem_image.mp hxL
        subst x
        exact ⟨a, haS, hxy⟩
    by_cases hSempty : S = ∅
    · simp [hSempty]
    · have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSempty
      have hLne : L.Nonempty := by
        obtain ⟨a, haS⟩ := hSne
        exact ⟨a.1.1, Finset.mem_image.mpr ⟨a, haS, rfl⟩⟩
      have hLgood : ∀ x ∈ L, x ∈ goodSet K r N := by
        intro x hxL
        obtain ⟨a, haS, hax⟩ := Finset.mem_image.mp hxL
        subst x
        exact a.1.2
      have havoid : ∀ k ≤ r, Disjoint (↑(reachable K k L) : Set X) N := by
        intro k hk
        apply reachable_disjoint_null
        intro x hxL q hq
        exact hLgood x hxL q (words_mono h1K hk hq)
      have hexponential : (1 + δ) ^ r * (L.card : ℝ) ≤
          (reachable K r L).card :=
        pow_mul_card_le_reachable h1K hPK hδ.le hexpand L hLne r havoid
      have hdoubleReal : (2 : ℝ) * L.card ≤ (reachable K r L).card :=
        calc
          (2 : ℝ) * L.card ≤ (1 + δ) ^ r * L.card := by
            exact mul_le_mul_of_nonneg_right htwo (Nat.cast_nonneg L.card)
          _ ≤ (reachable K r L).card := hexponential
      have hdoubleNat : 2 * L.card ≤ (reachable K r L).card := by
        exact_mod_cast hdoubleReal
      rw [hneighbours]
      exact hSle.trans hdoubleNat
  obtain ⟨f, hf, hfmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective neighbours).mp hHall
  have hchoice (a : {x // x ∈ A}) (b : Bool) :
      ∃ q ∈ words K r, q a.1 = f (a, b) := by
    have hfnear := hfmem (a, b)
    change f (a, b) ∈ reachable K r {a.1} at hfnear
    rw [reachable] at hfnear
    obtain ⟨q, hq, hfnear⟩ := Finset.mem_biUnion.mp hfnear
    obtain ⟨x, hx, hxf⟩ := Finset.mem_image.mp hfnear
    have hxa : x = a.1 := by simpa using hx
    subst x
    exact ⟨q, hq, hxf⟩
  let label (a : {x // x ∈ A}) (b : Bool) : Equiv.Perm X :=
    Classical.choose (hchoice a b)
  have hlabelW (a : {x // x ∈ A}) (b : Bool) : label a b ∈ words K r :=
    (Classical.choose_spec (hchoice a b)).1
  have hlabel (a : {x // x ∈ A}) (b : Bool) :
      label a b a.1 = f (a, b) :=
    (Classical.choose_spec (hchoice a b)).2
  exact no_piecewise_double_embedding m A hA (words K r)
    (fun q hq ↦ words_preserve hK hq) f hf label hlabelW hlabel

end
end TarskiHall

end NonsoficGroupsExist
