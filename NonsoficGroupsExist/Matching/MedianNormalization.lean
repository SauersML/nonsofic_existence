import NonsoficGroupsExist.Matching.Pinning
import Mathlib.Order.SymmDiff
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Median normalization

This file formalizes the quantitative core of Section `subsec:median` and
Section `subsec:matching` of the manuscript: the normalization

  `f(y) = s(y) / (s(y) + m)`

where `s(y)` is the size of the `Γ`-component of `y` and `m` is a
vertex-weighted median of `s` on the ambient component of `y`.

Four facts are proved, and they are exactly the four places where the
manuscript computes:

* `medianNormalize_lt_one`, `medianNormalize_increasing`: the normalization is
  increasing with values in `[0,1)`, so `1/2` is a median of `f` as soon as `m`
  is a median of `s` (equation `eq:f`);
* `medianNormalize_loss`: equation `eq:fracloss`, the one-sided loss estimate
  along a compressor arc;
* `medianNormalize_ratio`: the inversion of the pinning estimate, giving
  equation `eq:ratio`;
* `card_symmDiff_eq`, `dominant_intersection_unique`: the two counting steps of
  Proposition `prop:match`, namely its parts (ii) and (iii).
-/

namespace NonsoficGroupsExist

open scoped symmDiff

/-- The median normalization `t ↦ t/(t+m)` of equation `eq:f`. -/
noncomputable def medianNormalize (m t : ℝ) : ℝ := t / (t + m)

theorem medianNormalize_nonneg {m t : ℝ} (hm : 0 < m) (ht : 0 ≤ t) :
    0 ≤ medianNormalize m t := by
  apply div_nonneg ht
  linarith

theorem medianNormalize_lt_one {m t : ℝ} (hm : 0 < m) (ht : 0 ≤ t) :
    medianNormalize m t < 1 := by
  rw [medianNormalize, div_lt_one (by linarith)]
  linarith

/-- Monotonicity of the normalization on nonnegative sizes. -/
theorem medianNormalize_increasing {m : ℝ} (hm : 0 < m) :
    ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      (a < b ↔ medianNormalize m a < medianNormalize m b) := by
  intro a b ha hb
  have hA : 0 < a + m := by linarith
  have hB : 0 < b + m := by linarith
  rw [medianNormalize, medianNormalize, div_lt_div_iff₀ hA hB]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- **Equation `eq:fracloss`.**  If a compressed component loses at most a
`δ`-fraction of its size, the normalization drops by at most `δ`. -/
theorem medianNormalize_loss {m a a' δ : ℝ} (hm : 1 ≤ m) (ha' : 0 ≤ a')
    (hδ : 0 ≤ δ) (ha : (1 - δ) * a' ≤ a) (ha0 : 0 ≤ a) :
    medianNormalize m a' - medianNormalize m a ≤ δ := by
  have hA : 0 < a + m := by linarith
  have hA' : 0 < a' + m := by linarith
  rw [medianNormalize, medianNormalize, div_sub_div _ _ (ne_of_gt hA') (ne_of_gt hA),
    div_le_iff₀ (by positivity)]
  have hnum : a' * (a + m) - a * (a' + m) = m * (a' - a) := by ring
  rw [mul_comm (a' + m) a, hnum]
  have hm0 : 0 ≤ m := by linarith
  have hdiff : a' - a ≤ δ * a' := by nlinarith [ha]
  have hprod : m * a' ≤ (a' + m) * (a + m) := by
    nlinarith [mul_nonneg ha' ha0, mul_nonneg hm0 ha0, sq_nonneg m]
  calc
    m * (a' - a) ≤ m * (δ * a') := mul_le_mul_of_nonneg_left hdiff hm0
    _ = δ * (m * a') := by ring
    _ ≤ δ * ((a' + m) * (a + m)) := mul_le_mul_of_nonneg_left hprod hδ

/-- **Inversion of the pinning estimate.**  A vertex whose normalization is
within `η` of `1/2` has component size within a factor `(1+2η)/(1-2η)` of the
ambient median. -/
theorem medianNormalize_ratio {m a η : ℝ} (hm : 0 < m) (ha : 0 ≤ a)
    (hη : |medianNormalize m a - 1 / 2| ≤ η) :
    (1 - 2 * η) * m ≤ (1 + 2 * η) * a ∧ (1 - 2 * η) * a ≤ (1 + 2 * η) * m := by
  have hA : 0 < a + m := by linarith
  have hkey : medianNormalize m a - 1 / 2 = (a - m) / (2 * (a + m)) := by
    rw [medianNormalize]
    field_simp
    ring
  rw [hkey, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * (a + m)),
    div_le_iff₀ (by positivity)] at hη
  constructor
  · have h := neg_abs_le (a - m)
    nlinarith [hη, h]
  · have h := le_abs_self (a - m)
    nlinarith [hη, h]

section Counting

variable {α : Type*} [DecidableEq α]

/-- The exact counting identity behind Proposition `prop:match`(ii). -/
theorem card_symmDiff_add_two_mul_inter (U D : Finset α) :
    (U ∆ D).card + 2 * (U ∩ D).card = U.card + D.card := by
  classical
  have hdisj : Disjoint (U \ D) (D \ U) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1
  have hsym : (U ∆ D).card = (U \ D).card + (D \ U).card := by
    rw [Finset.symmDiff_def, Finset.card_union_of_disjoint hdisj]
  have hU := Finset.card_sdiff_add_card_inter U D
  have hD := Finset.card_sdiff_add_card_inter D U
  rw [Finset.inter_comm D U] at hD
  omega

/-- Proposition `prop:match`(ii): a nearly contained image of the same size has
small symmetric difference with its target. -/
theorem card_symmDiff_le (U D : Finset α) (e : ℕ) (hleak : (U \ D).card ≤ e) :
    ((U ∆ D).card : ℤ) ≤ 2 * e + ((D.card : ℤ) - U.card) := by
  classical
  have hdisj : Disjoint (U \ D) (D \ U) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1
  have hsym : (U ∆ D).card = (U \ D).card + (D \ U).card := by
    rw [Finset.symmDiff_def, Finset.card_union_of_disjoint hdisj]
  have hU := Finset.card_sdiff_add_card_inter U D
  have hD := Finset.card_sdiff_add_card_inter D U
  rw [Finset.inter_comm D U] at hD
  omega

/-- Proposition `prop:match`(iii): two disjoint sets cannot both occupy more
than half of a third set.  This is what makes the matching injective. -/
theorem dominant_intersection_unique (P Q D : Finset α) (hdisj : Disjoint P Q)
    (hP : D.card < 2 * (P ∩ D).card) (hQ : D.card < 2 * (Q ∩ D).card) : False := by
  classical
  have hparts : Disjoint (P ∩ D) (Q ∩ D) :=
    Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left hdisj)
  have hsub : (P ∩ D) ∪ (Q ∩ D) ⊆ D := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.mem_inter.mp hx).2
    · exact (Finset.mem_inter.mp hx).2
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hparts] at hcard
  omega

/-- A target is dominated by a source whose symmetric difference with it is less
than half its size; this is the hypothesis under which the previous lemma is
applied in Section `subsec:matching`. -/
theorem dominant_of_small_symmDiff (U D : Finset α)
    (hsmall : 2 * (U ∆ D).card < D.card) :
    D.card < 2 * (U ∩ D).card := by
  have hkey := card_symmDiff_add_two_mul_inter U D
  have hDU : (D \ U).card ≤ (U ∆ D).card := by
    apply Finset.card_le_card
    intro x hx
    rw [Finset.mem_symmDiff]
    obtain ⟨hxD, hxU⟩ := Finset.mem_sdiff.mp hx
    exact Or.inr ⟨hxD, hxU⟩
  have hD := Finset.card_sdiff_add_card_inter D U
  rw [Finset.inter_comm D U] at hD
  omega

end Counting

end NonsoficGroupsExist
