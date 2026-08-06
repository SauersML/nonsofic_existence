import NonsoficGroupsExist.Matching.DirectedCoarea
import NonsoficGroupsExist.KunThom.KunThomParameters

/-!
# The Kun--Thom theorem for an exactly expanding product approximation

This module closes the analytic and finite-group argument when the
first-factor labeled graphs themselves have a uniform Cheeger bound.  The
remaining essential-expander localization theorem will feed this exact form
after removing the negligible edit locus.
-/

namespace NonsoficGroupsExist
namespace KunThomTheorem

open AlmostAutomorphism
open DirectedCoarea
open KazhdanGNS
open KazhdanImprovement
open KunThomParameters
open KunThomRounding
open scoped symmDiff

variable {K J : Type} [Group K] [Group J]

theorem card_productLabels_of_injective
    (A : SoficApproximation (K × J)) (n : ℕ) (S : Finset K)
    (hinj : Set.InjOn (fun k : K ↦ A.map n (k, (1 : J))) (S : Set K)) :
    (productLabels A n S).card = S.card := by
  classical
  unfold productLabels
  rw [Finset.card_image_iff.mpr]
  intro x hx y hy hxy
  exact hinj hx hy hxy

theorem card_sdiff_add_card_sdiff_eq_symmDiff
    {α : Type} [DecidableEq α] (U V : Finset α) :
    (V \ U).card + (U \ V).card = (U ∆ V).card := by
  have hdisj : Disjoint (U \ V) (V \ U) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1
  rw [Finset.symmDiff_def, Finset.card_union_of_disjoint hdisj]
  omega

theorem repairBudget_le_three_symmDiff (missing excess : ℕ) :
    ((missing + 2 * (missing + excess) : ℕ) : ℝ) ≤
      3 * ((missing + excess : ℕ) : ℝ) := by
  norm_cast
  omega

theorem directedExpansionAtScale_of_cheeger
    (Y : FiniteModel) (S : Finset (Equiv.Perm Y)) {h : ℝ}
    (hcheeger : DirectedCoarea.HasCheegerLowerBound Y S h)
    (m : ℕ) (hm : 0 < m) :
    HasDirectedExpansionAtScale Y S h m := by
  refine ⟨hcheeger.1, fun U hmU hhalf ↦ ?_⟩
  exact hcheeger.2 U (Finset.card_pos.mp (hm.trans_le hmU)) hhalf

/-- Kun--Thom's expander-centralizer theorem when the labeled first-factor
graphs have an exact uniform Cheeger lower bound.  Every numerical parameter
is constructed internally from the Kazhdan and Cheeger constants. -/
theorem isLEF_of_exactProductExpansion
    {Q : Finset K} {κ h : ℝ} (hQ : IsKazhdanPair.{0, 0} K Q κ)
    (S : Finset K) (hQS : Q ⊆ S) (hone : 1 ∈ S) (hκone : κ ≤ 1)
    (A : SoficApproximation (K × J)) (hh : 0 < h)
    (hcheeger : ∃ N : ℕ, ∀ n ≥ N,
      DirectedCoarea.HasCheegerLowerBound
        (A.model n) (productLabels A n S) h) :
    IsLEF J := by
  obtain ⟨hq0, hq1⟩ := kazhdanFactor_nonneg_lt_one hQ S hone hκone
  obtain ⟨k, η, δ, β, hk, hη, hδ, hβ, hsmall, hclose,
      hrepairBoundary, hcoarea⟩ :=
    exists_improvementParameters hq0 hq1 hh S.card
      (Finset.card_pos.mpr ⟨1, hone⟩)
  obtain ⟨Nrelation, hNrelation⟩ :=
    exists_pairProduct_relation_eventually hQ S hQS hone hκone A
      k hk hδ hβ hcoarea
  obtain ⟨Ncheeger, hNcheeger⟩ := hcheeger
  obtain ⟨Ninjective, hNinjective⟩ :=
    firstFactorLabels_injective_eventually A S
  obtain ⟨Ncard, hNcard⟩ := A.card_tendsToInfinity 10
  have hexp : ∃ Nexp, ∀ n ≥ Nexp,
      HasDirectedExpansionAtScale (A.model n) (productLabels A n S) h
        (clusterScale (A.model n)) := by
    refine ⟨max Ncheeger Ncard, fun n hn ↦ ?_⟩
    have hncheeger : Ncheeger ≤ n := (le_max_left _ _).trans hn
    have hncard : Ncard ≤ n := (le_max_right _ _).trans hn
    exact directedExpansionAtScale_of_cheeger
      (A.model n) (productLabels A n S) (hNcheeger n hncheeger)
      (clusterScale (A.model n))
      (clusterScale_pos (A.model n) (by have := hNcard n hncard; omega))
  have hround : ∃ Nround, ∀ n ≥ Nround,
      ∃ round : Equiv.Perm (A.model n) → Equiv.Perm (A.model n),
        (∀ a, IsEpsilonGood (A.model n) (productLabels A n S) η a →
          ∀ b, IsEpsilonGood (A.model n) (productLabels A n S) η b →
          IsEpsilonGood (A.model n) (productLabels A n S) η
            (round (a * b))) ∧
        (∀ a, IsEpsilonGood (A.model n) (productLabels A n S) η a →
          ∀ b, IsEpsilonGood (A.model n) (productLabels A n S) η b →
          hammingDistance (A.model n) (a * b) (round (a * b)) <
            clusterRadius (A.model n)) := by
    let Nround := max Nrelation (max Ncheeger (max Ninjective Ncard))
    refine ⟨Nround, fun n hn ↦ ?_⟩
    have hnrelation : Nrelation ≤ n := by dsimp [Nround] at hn; omega
    have hncheeger : Ncheeger ≤ n := by dsimp [Nround] at hn; omega
    have hninjective : Ninjective ≤ n := by dsimp [Nround] at hn; omega
    have hncard : Ncard ≤ n := by dsimp [Nround] at hn; omega
    have hcard : 10 ≤ Fintype.card (A.model n) := hNcard n hncard
    have hcardPos : 0 < Fintype.card (A.model n) := by omega
    have hinjective := hNinjective n hninjective
    have hlabelCard : (productLabels A n S).card = S.card :=
      card_productLabels_of_injective A n S hinjective
    let admissible (c : Equiv.Perm (A.model n))
        (U : Finset (A.model n × A.model n)) : Prop :=
      (((U ∆ permutationGraph (A.model n) c).card : ℝ) <
        36 * k ^ 2 * (S.card : ℝ)⁻¹ * η *
          Fintype.card (A.model n)) ∧
      (((relationBoundary (A.model n) (productLabels A n S) U).card : ℝ) <
        β * Fintype.card (A.model n))
    let improve : Equiv.Perm (A.model n) →
        Finset (A.model n × A.model n) := fun c ↦
      if hc : ∃ U, admissible c U then Classical.choose hc
      else permutationGraph (A.model n) c
    have improve_spec (c : Equiv.Perm (A.model n))
        (hc : ∃ U, admissible c U) : admissible c (improve c) := by
      dsimp [improve]
      rw [dif_pos hc]
      exact Classical.choose_spec hc
    let round : Equiv.Perm (A.model n) → Equiv.Perm (A.model n) :=
      fun c ↦ repairRelation (A.model n) (improve c)
    refine ⟨round, ?_, ?_⟩
    · intro a ha b hb
      have hexists : ∃ U, admissible (a * b) U := by
        simpa [admissible] using
          hNrelation n hnrelation hinjective hcardPos ha hb
      obtain ⟨hrelationClose, hrelationBoundary⟩ :=
        improve_spec (a * b) hexists
      have hdiffReal :
          (((permutationGraph (A.model n) (a * b) \ improve (a * b)).card +
            (improve (a * b) \ permutationGraph (A.model n) (a * b)).card : ℕ) : ℝ) <
              36 * k ^ 2 * (S.card : ℝ)⁻¹ * η *
                Fintype.card (A.model n) := by
        rw [card_sdiff_add_card_sdiff_eq_symmDiff]
        exact hrelationClose
      have hcardReal : (0 : ℝ) < Fintype.card (A.model n) := by
        exact_mod_cast hcardPos
      have hthreeDiff :
          3 * (((permutationGraph (A.model n) (a * b) \ improve (a * b)).card +
            (improve (a * b) \ permutationGraph (A.model n) (a * b)).card : ℕ) : ℝ) <
              (1 : ℝ) / 10 * Fintype.card (A.model n) := by
        have hscaled := mul_lt_mul_of_pos_left hdiffReal (by norm_num : (0 : ℝ) < 3)
        have hparameter := mul_lt_mul_of_pos_right hclose hcardReal
        nlinarith
      have hedits :
          2 * ((permutationGraph (A.model n) (a * b) \ improve (a * b)).card +
            (improve (a * b) \ permutationGraph (A.model n) (a * b)).card) ≤
              Fintype.card (A.model n) := by
        have htwoReal :
            (2 * ((permutationGraph (A.model n) (a * b) \ improve (a * b)).card +
              (improve (a * b) \ permutationGraph (A.model n) (a * b)).card) : ℕ) <
                Fintype.card (A.model n) := by
          exact_mod_cast (show
            2 * (((permutationGraph (A.model n) (a * b) \ improve (a * b)).card +
              (improve (a * b) \ permutationGraph (A.model n) (a * b)).card : ℕ) : ℝ) <
                Fintype.card (A.model n) by nlinarith)
        omega
      have hP : HasL1PoincareAtOne (A.model n)
          (productLabels A n S) h :=
        hasL1PoincareAtOne_of_cheeger (A.model n) (productLabels A n S)
          (hNcheeger n hncheeger)
      have hboundaryNeeded :
          (h + 7 * (productLabels A n S).card) *
              (relationBoundary (A.model n) (productLabels A n S)
                (improve (a * b))).card <
            h * (η * Fintype.card (A.model n)) := by
        rw [hlabelCard]
        have hcoefficient : 0 < h + 7 * (S.card : ℝ) := by positivity
        calc
          (h + 7 * (S.card : ℝ)) *
              ((relationBoundary (A.model n) (productLabels A n S)
                (improve (a * b))).card : ℝ) <
            (h + 7 * (S.card : ℝ)) *
              (β * Fintype.card (A.model n)) :=
                mul_lt_mul_of_pos_left hrelationBoundary hcoefficient
          _ = ((h + 7 * (S.card : ℝ)) * β) *
              Fintype.card (A.model n) := by ring
          _ < (h * η) * Fintype.card (A.model n) :=
            mul_lt_mul_of_pos_right hrepairBoundary hcardReal
          _ = h * (η * Fintype.card (A.model n)) := by ring
      change IsEpsilonGood (A.model n) (productLabels A n S) η
        (repairRelation (A.model n) (improve (a * b)))
      exact repairRelation_isEpsilonGood_of_close_relation
        (A.model n) (productLabels A n S) (improve (a * b)) (a * b)
          hP hedits hboundaryNeeded
    · intro a ha b hb
      have hexists : ∃ U, admissible (a * b) U := by
        simpa [admissible] using
          hNrelation n hnrelation hinjective hcardPos ha hb
      obtain ⟨hrelationClose, _hrelationBoundary⟩ :=
        improve_spec (a * b) hexists
      let missing : ℕ :=
        (permutationGraph (A.model n) (a * b) \ improve (a * b)).card
      let excess : ℕ :=
        (improve (a * b) \ permutationGraph (A.model n) (a * b)).card
      have hdiffReal :
          ((missing + excess : ℕ) : ℝ) <
              36 * k ^ 2 * (S.card : ℝ)⁻¹ * η *
                Fintype.card (A.model n) := by
        dsimp [missing, excess]
        rw [card_sdiff_add_card_sdiff_eq_symmDiff]
        exact hrelationClose
      have hcardReal : (0 : ℝ) < Fintype.card (A.model n) := by
        exact_mod_cast hcardPos
      have hthreeDiff :
          3 * ((missing + excess : ℕ) : ℝ) <
              (1 : ℝ) / 10 * Fintype.card (A.model n) := by
        have hscaled := mul_lt_mul_of_pos_left hdiffReal (by norm_num : (0 : ℝ) < 3)
        have hparameter := mul_lt_mul_of_pos_right hclose hcardReal
        nlinarith
      have hmissing :
          ((missing + 2 * (missing + excess) : ℕ) : ℝ) <
            clusterRadius (A.model n) * Fintype.card (A.model n) := by
        have hmissingLe :
            ((missing + 2 * (missing + excess) : ℕ) : ℝ) ≤
              3 * ((missing + excess : ℕ) : ℝ) := by
          exact repairBudget_le_three_symmDiff missing excess
        have hradius := one_tenth_le_clusterRadius (A.model n) hcard
        have hradiusScaled := mul_le_mul_of_nonneg_right hradius hcardReal.le
        exact hmissingLe.trans_lt (hthreeDiff.trans_le hradiusScaled)
      change hammingDistance (A.model n) (a * b)
        (repairRelation (A.model n) (improve (a * b))) <
          clusterRadius (A.model n)
      have hrepair : hammingDistance (A.model n)
          (repairRelation (A.model n) (improve (a * b))) (a * b) <
            clusterRadius (A.model n) := by
        apply hammingDistance_repairRelation_lt
          (A.model n) (improve (a * b)) (a * b) hcardPos
        change ((missing + 2 * (missing + excess) : ℕ) : ℝ) <
          clusterRadius (A.model n) * Fintype.card (A.model n)
        exact hmissing
      simpa only [hammingDistance_comm] using hrepair
  exact isLEF_of_product_epsilonRounding A S hη hsmall hexp hround

end KunThomTheorem
end NonsoficGroupsExist
