import NonsoficGroupsExist.AlmostAutomorphism

/-!
# Directed coarea for finite permutation graphs

This module proves the finite layer-cake inequality for the directed,
generator-tagged boundary used in the Kun--Thom argument.  It is the exact
directed analogue of `FiniteMultiGraph.nonnegative_coarea`.
-/

namespace NonsoficGroupsExist
namespace DirectedCoarea

open AlmostAutomorphism
open scoped BigOperators

variable (Y : FiniteModel)

noncomputable def superlevel (g : Y → ℝ) (t : ℝ) : Finset Y :=
  Finset.univ.filter fun x ↦ t < g x

noncomputable def variation (S : Finset (Equiv.Perm Y))
    (g : Y → ℝ) : ℝ :=
  ∑ p ∈ S.product (Finset.univ : Finset Y), |g p.2 - g (p.1 p.2)|

def HasCheegerLowerBound (S : Finset (Equiv.Perm Y)) (h : ℝ) : Prop :=
  0 < h ∧ ∀ U : Finset Y, U.Nonempty →
    2 * U.card ≤ Fintype.card Y →
      h * U.card ≤ (directedBoundary Y S U).card

theorem sum_eq_layer_add_peel (g : Y → ℝ) (m : ℝ)
    (hg : ∀ x, 0 ≤ g x) (hm : 0 ≤ m)
    (hmin : ∀ x, 0 < g x → m ≤ g x) :
    ∑ x, g x = m * (superlevel Y g 0).card +
      ∑ x, FiniteMultiGraph.peel m (g x) := by
  calc
    ∑ x, g x = ∑ x,
        ((if 0 < g x then m else 0) + FiniteMultiGraph.peel m (g x)) := by
      apply Finset.sum_congr rfl
      intro x _
      exact FiniteMultiGraph.value_eq_layer_add_peel (hg x) hm (hmin x)
    _ = (∑ x, if 0 < g x then m else 0) +
        ∑ x, FiniteMultiGraph.peel m (g x) := Finset.sum_add_distrib
    _ = m * (superlevel Y g 0).card +
        ∑ x, FiniteMultiGraph.peel m (g x) := by
      congr 1
      rw [← Finset.sum_filter]
      simp [superlevel, mul_comm]

theorem variation_eq_layer_add_peel
    (S : Finset (Equiv.Perm Y)) (g : Y → ℝ) (m : ℝ)
    (hg : ∀ x, 0 ≤ g x) (hm : 0 ≤ m)
    (hmin : ∀ x, 0 < g x → m ≤ g x) :
    variation Y S g = m * (directedBoundary Y S (superlevel Y g 0)).card +
      variation Y S (fun x ↦ FiniteMultiGraph.peel m (g x)) := by
  calc
    variation Y S g = ∑ p ∈ S.product (Finset.univ : Finset Y),
        (m * (if (0 < g p.2 ∧ ¬ 0 < g (p.1 p.2)) ∨
          (0 < g (p.1 p.2) ∧ ¬ 0 < g p.2) then 1 else 0) +
          |FiniteMultiGraph.peel m (g p.2) -
            FiniteMultiGraph.peel m (g (p.1 p.2))|) := by
      unfold variation
      apply Finset.sum_congr rfl
      intro p _
      exact FiniteMultiGraph.abs_sub_eq_layer_add_peel
        (hg _) (hg _) hm (hmin _) (hmin _)
    _ = m * (∑ p ∈ S.product (Finset.univ : Finset Y),
        if (0 < g p.2 ∧ ¬ 0 < g (p.1 p.2)) ∨
          (0 < g (p.1 p.2) ∧ ¬ 0 < g p.2) then 1 else 0) +
        variation Y S (fun x ↦ FiniteMultiGraph.peel m (g x)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      rfl
    _ = m * (directedBoundary Y S (superlevel Y g 0)).card +
        variation Y S (fun x ↦ FiniteMultiGraph.peel m (g x)) := by
      congr 2
      rw [← Finset.sum_filter]
      have hfilter :
          (S.product (Finset.univ : Finset Y)).filter (fun p ↦
            (0 < g p.2 ∧ ¬ 0 < g (p.1 p.2)) ∨
              (0 < g (p.1 p.2) ∧ ¬ 0 < g p.2)) =
            directedBoundary Y S (superlevel Y g 0) := by
        ext p
        simp [directedBoundary, superlevel, and_comm]
      rw [hfilter, Finset.card_eq_sum_ones, Nat.cast_sum]
      norm_num

/-- Finite directed layer-cake inequality, proved by recursively peeling the
least positive value. -/
theorem nonnegative_coarea (S : Finset (Equiv.Perm Y)) {h : ℝ}
    (hcheeger : HasCheegerLowerBound Y S h) (g : Y → ℝ)
    (hg : ∀ x, 0 ≤ g x)
    (hsmall : ∀ t, 0 ≤ t →
      2 * (superlevel Y g t).card ≤ Fintype.card Y) :
    h * ∑ x, g x ≤ variation Y S g := by
  classical
  let U := superlevel Y g 0
  by_cases hU : U.Nonempty
  · let values := U.image g
    have hvalues : values.Nonempty := hU.image g
    let m := values.min' hvalues
    have hm_mem : m ∈ values := Finset.min'_mem values hvalues
    obtain ⟨x₀, hx₀U, hx₀m⟩ := Finset.mem_image.mp hm_mem
    have hx₀pos : 0 < g x₀ := by simpa [U, superlevel] using hx₀U
    have hmpos : 0 < m := by simpa [hx₀m] using hx₀pos
    have hm : 0 ≤ m := hmpos.le
    have hmin : ∀ x, 0 < g x → m ≤ g x := by
      intro x hx
      apply Finset.min'_le values (g x)
      exact Finset.mem_image.mpr
        ⟨x, by simpa [U, superlevel] using hx, rfl⟩
    let g' : Y → ℝ := fun x ↦ FiniteMultiGraph.peel m (g x)
    have hg' : ∀ x, 0 ≤ g' x := fun x ↦ FiniteMultiGraph.peel_nonnegative _ _
    have hlevels (t : ℝ) (ht : 0 ≤ t) :
        superlevel Y g' t = superlevel Y g (t + m) := by
      ext x
      simp [g', superlevel, FiniteMultiGraph.peel, ht, lt_sub_iff_add_lt]
    have hsmall' : ∀ t, 0 ≤ t →
        2 * (superlevel Y g' t).card ≤ Fintype.card Y := by
      intro t ht
      rw [hlevels t ht]
      exact hsmall (t + m) (add_nonneg ht hm)
    have hsupport_subset : superlevel Y g' 0 ⊆ U := by
      intro x hx
      have hx' : 0 < g x - m := by
        simpa [g', superlevel, FiniteMultiGraph.peel] using hx
      have hxpos : 0 < g x := hm.trans_lt (sub_pos.mp hx')
      simpa [U, superlevel] using hxpos
    have hx₀_not : x₀ ∉ superlevel Y g' 0 := by
      simp [g', superlevel, FiniteMultiGraph.peel, hx₀m]
    have hsupport_ne : superlevel Y g' 0 ≠ U := by
      intro heq
      exact hx₀_not (heq.symm ▸ hx₀U)
    have hdecrease : (superlevel Y g' 0).card < U.card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
        ⟨hsupport_subset, hsupport_ne⟩)
    have hinduction : h * ∑ x, g' x ≤ variation Y S g' :=
      nonnegative_coarea S hcheeger g' hg' hsmall'
    have hboundary : h * U.card ≤ (directedBoundary Y S U).card :=
      hcheeger.2 U hU (by simpa [U] using hsmall 0 le_rfl)
    have hlayer : m * (h * U.card) ≤
        m * (directedBoundary Y S U).card :=
      mul_le_mul_of_nonneg_left hboundary hm
    rw [sum_eq_layer_add_peel Y g m hg hm hmin,
      variation_eq_layer_add_peel Y S g m hg hm hmin]
    change h * (m * U.card + ∑ x, g' x) ≤
      m * (directedBoundary Y S U).card + variation Y S g'
    calc
      h * (m * U.card + ∑ x, g' x) =
          m * (h * U.card) + h * ∑ x, g' x := by ring
      _ ≤ m * (directedBoundary Y S U).card + variation Y S g' :=
        add_le_add hlayer hinduction
  · have hgzero : ∀ x, g x = 0 := by
      intro x
      have hnot : ¬ 0 < g x := by
        intro hx
        exact hU ⟨x, by simpa [U, superlevel] using hx⟩
      exact le_antisymm (not_lt.mp hnot) (hg x)
    simp [hgzero, variation]
termination_by (superlevel Y g 0).card
decreasing_by simpa [U] using hdecrease

/-- The directed `ℓ1` coarea estimate centered at a median. -/
theorem coarea_mul (S : Finset (Equiv.Perm Y)) {h : ℝ}
    (hcheeger : HasCheegerLowerBound Y S h) (f : Y → ℝ) (c : ℝ)
    (hc : FiniteMultiGraph.IsMedian f c) :
    h * ∑ x, |f x - c| ≤ variation Y S f := by
  let gp : Y → ℝ := fun x ↦ FiniteMultiGraph.positivePart (f x - c)
  let gn : Y → ℝ := fun x ↦ FiniteMultiGraph.negativePart (f x - c)
  have hgp : ∀ x, 0 ≤ gp x := fun x ↦ le_max_right _ _
  have hgn : ∀ x, 0 ≤ gn x := fun x ↦ le_max_right _ _
  have hsmallp : ∀ t, 0 ≤ t →
      2 * (superlevel Y gp t).card ≤ Fintype.card Y := by
    intro t ht
    have hsubset : superlevel Y gp t ⊆
        Finset.univ.filter (fun x ↦ c < f x) := by
      intro x hx
      have htx : t < f x - c := by
        have hx' : t < max (f x - c) 0 := by
          simpa [gp, FiniteMultiGraph.positivePart, superlevel] using hx
        exact (lt_max_iff.mp hx').resolve_right (not_lt_of_ge ht)
      have hcx : c < f x := by
        have : t + c < f x := lt_sub_iff_add_lt.mp htx
        exact (le_add_of_nonneg_left ht).trans_lt (by simpa [add_comm] using this)
      simpa using hcx
    exact (Nat.mul_le_mul_left 2 (Finset.card_le_card hsubset)).trans hc.1
  have hsmalln : ∀ t, 0 ≤ t →
      2 * (superlevel Y gn t).card ≤ Fintype.card Y := by
    intro t ht
    have hsubset : superlevel Y gn t ⊆
        Finset.univ.filter (fun x ↦ f x < c) := by
      intro x hx
      have htx : t < -(f x - c) := by
        have hx' : t < max (-(f x - c)) 0 := by
          simpa [gn, FiniteMultiGraph.negativePart, superlevel] using hx
        exact (lt_max_iff.mp hx').resolve_right (not_lt_of_ge ht)
      have hxc : f x < c := by
        have : t + f x < c := by
          rw [neg_sub] at htx
          exact lt_sub_iff_add_lt.mp htx
        exact (le_add_of_nonneg_left ht).trans_lt (by simpa [add_comm] using this)
      simpa using hxc
    exact (Nat.mul_le_mul_left 2 (Finset.card_le_card hsubset)).trans hc.2
  have hp := nonnegative_coarea Y S hcheeger gp hgp hsmallp
  have hn := nonnegative_coarea Y S hcheeger gn hgn hsmalln
  have hsum : (∑ x, |f x - c|) = (∑ x, gp x) + ∑ x, gn x := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    exact FiniteMultiGraph.abs_eq_positivePart_add_negativePart (f x - c)
  have hedge : variation Y S gp + variation Y S gn = variation Y S f := by
    rw [variation, variation, variation, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    rw [show gp p.2 = FiniteMultiGraph.positivePart (f p.2 - c) by rfl,
      show gp (p.1 p.2) =
        FiniteMultiGraph.positivePart (f (p.1 p.2) - c) by rfl,
      show gn p.2 = FiniteMultiGraph.negativePart (f p.2 - c) by rfl,
      show gn (p.1 p.2) =
        FiniteMultiGraph.negativePart (f (p.1 p.2) - c) by rfl,
      FiniteMultiGraph.positivePart_edge_add_negativePart_edge]
    congr 1
    ring
  calc
    h * ∑ x, |f x - c| = h * ((∑ x, gp x) + ∑ x, gn x) := by rw [hsum]
    _ = h * ∑ x, gp x + h * ∑ x, gn x := by ring
    _ ≤ variation Y S gp + variation Y S gn := add_le_add hp hn
    _ = variation Y S f := hedge

end DirectedCoarea
end NonsoficGroupsExist
