import NonsoficGroupsExist.KunThomFiniteMarkov
import NonsoficGroupsExist.KunGeneratorGraph
import NonsoficGroupsExist.KunRounding

/-!
# Threshold rounding for the Kun--Thom diagonal trajectory

The diagonal action lives on `Y × Y`, but the initial permutation graph has
only `|Y|` points.  This module keeps that graph-scale normalization while
passing from the centered trajectory used by the Kazhdan argument to the
uncentered `[0,1]`-valued trajectory required by coarea thresholding.
-/

namespace NonsoficGroupsExist
namespace KunThomRounding

open KazhdanFiniteModel
open KazhdanGNS
open KazhdanImprovement
open KunGeneratorGraph
open KunThomFiniteMarkov
open AlmostAutomorphism
open FiniteMultiGraph
open scoped symmDiff

variable {K J : Type} [Group K] [Group J]

/-- Genuine diagonal Markov iteration started at the indicator of a
permutation graph. -/
noncomputable def pairIndicatorIterate
    (A : SoficApproximation (K × J)) (n : ℕ)
    (c : Equiv.Perm (A.model n)) (S : Finset K) (k : ℕ) :
    EuclideanSpace ℝ (pairModel (A.model n)) :=
  ((finiteModelAverage (pairModel (A.model n)) (pairMap A n) S)^[k])
    (indicator (permutationGraph (A.model n) c))

theorem pairIndicatorIterate_succ
    (A : SoficApproximation (K × J)) (n : ℕ)
    (c : Equiv.Perm (A.model n)) (S : Finset K) (k : ℕ) :
    pairIndicatorIterate A n c S (k + 1) =
      finiteModelAverage (pairModel (A.model n)) (pairMap A n) S
        (pairIndicatorIterate A n c S k) := by
  rw [pairIndicatorIterate, pairIndicatorIterate,
    Function.iterate_succ_apply']

/-- Every diagonal indicator iterate remains pointwise in `[0,1]`. -/
theorem pairIndicatorIterate_between_zero_one
    (A : SoficApproximation (K × J)) (n : ℕ)
    (c : Equiv.Perm (A.model n)) (S : Finset K) (hS : S.Nonempty)
    (k : ℕ) (z : pairModel (A.model n)) :
    0 ≤ pairIndicatorIterate A n c S k z ∧
      pairIndicatorIterate A n c S k z ≤ 1 := by
  induction k generalizing z with
  | zero =>
      by_cases hz : z ∈ permutationGraph (A.model n) c <;>
        simp [pairIndicatorIterate, indicator_apply, hz]
  | succ k ih =>
      rw [pairIndicatorIterate_succ]
      exact finiteModelAverage_between_zero_one
        (pairModel (A.model n)) (pairMap A n) S hS
        (pairIndicatorIterate A n c S k)
        (fun z ↦ (ih z).1) (fun z ↦ (ih z).2) z

/-- The diagonal Markov trajectory preserves the `|Y|` mass of its initial
permutation graph. -/
theorem sum_pairIndicatorIterate
    (A : SoficApproximation (K × J)) (n : ℕ)
    (c : Equiv.Perm (A.model n)) (S : Finset K) (hS : S.Nonempty)
    (k : ℕ) :
    ∑ z, pairIndicatorIterate A n c S k z =
      Fintype.card (A.model n) := by
  induction k with
  | zero =>
      rw [pairIndicatorIterate]
      simp only [Function.iterate_zero_apply]
      have hsum (U : Finset (pairModel (A.model n))) :
          ∑ z, indicator U z = (U.card : ℝ) := by
        simp [indicator_apply]
      rw [hsum, card_permutationGraph]
  | succ k ih =>
      rw [pairIndicatorIterate_succ,
        sum_finiteModelAverage (pairModel (A.model n)) (pairMap A n) S hS,
        ih]

/-- The squared norm of every diagonal indicator iterate is at most the
graph size, not the ambient pair-space size. -/
theorem norm_pairIndicatorIterate_sq_le_card
    (A : SoficApproximation (K × J)) (n : ℕ)
    (c : Equiv.Perm (A.model n)) (S : Finset K) (hS : S.Nonempty)
    (k : ℕ) :
    ‖pairIndicatorIterate A n c S k‖ ^ 2 ≤
      Fintype.card (A.model n) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    ∑ z, (pairIndicatorIterate A n c S k z) ^ 2 ≤
        ∑ z, pairIndicatorIterate A n c S k z := by
      apply Finset.sum_le_sum
      intro z _
      obtain ⟨hz0, hz1⟩ :=
        pairIndicatorIterate_between_zero_one A n c S hS k z
      nlinarith [mul_nonneg hz0 (sub_nonneg.mpr hz1)]
    _ = Fintype.card (A.model n) :=
      sum_pairIndicatorIterate A n c S hS k

/-- Centered and uncentered diagonal trajectories differ by the same constant
at every time. -/
theorem finiteModelAverageIterate_eq_pairIndicatorIterate_sub
    (A : SoficApproximation (K × J)) (n : ℕ)
    (c : Equiv.Perm (A.model n)) (S : Finset K) (hS : S.Nonempty)
    (k : ℕ) :
    KunThomFiniteMarkov.finiteModelAverageIterate A n c S k =
      pairIndicatorIterate A n c S k -
        (((permutationGraph (A.model n) c).card : ℝ) /
          Fintype.card (pairModel (A.model n))) • constantVector 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [KunThomFiniteMarkov.finiteModelAverageIterate_succ,
        pairIndicatorIterate_succ,
        ih, finiteModelAverage_sub, finiteModelAverage_smul,
        finiteModelAverage_constantVector
          (pairModel (A.model n)) (pairMap A n) S hS]

/-- Consecutive displacement vectors are identical before and after
centering. -/
theorem finiteModelAverageIterate_displacement_eq_pairIndicator
    (A : SoficApproximation (K × J)) (n : ℕ)
    (c : Equiv.Perm (A.model n)) (S : Finset K) (hS : S.Nonempty)
    (k : ℕ) :
    KunThomFiniteMarkov.finiteModelAverageIterate A n c S (k + 1) -
        KunThomFiniteMarkov.finiteModelAverageIterate A n c S k =
      pairIndicatorIterate A n c S (k + 1) -
        pairIndicatorIterate A n c S k := by
  rw [finiteModelAverageIterate_eq_pairIndicatorIterate_sub A n c S hS,
    finiteModelAverageIterate_eq_pairIndicatorIterate_sub A n c S hS]
  abel

/-- Diagonal indicator displacement norms are nonincreasing along the genuine
finite trajectory. -/
theorem norm_pairIndicatorIterate_displacement_le_initial
    (A : SoficApproximation (K × J)) (n : ℕ)
    (c : Equiv.Perm (A.model n)) (S : Finset K) (hS : S.Nonempty)
    (k : ℕ) :
    ‖pairIndicatorIterate A n c S (k + 1) -
        pairIndicatorIterate A n c S k‖ ≤
      ‖pairIndicatorIterate A n c S 1 -
        pairIndicatorIterate A n c S 0‖ := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
      rw [pairIndicatorIterate_succ, pairIndicatorIterate_succ,
        ← finiteModelAverage_sub]
      exact (norm_finiteModelAverage_le
        (pairModel (A.model n)) (pairMap A n) S hS _).trans (by
          simpa [pairIndicatorIterate_succ] using ih)

/-- A `k`-step diagonal indicator trajectory moves by at most `k` times its
initial displacement. -/
theorem norm_pairIndicatorIterate_sub_le
    (A : SoficApproximation (K × J)) (n : ℕ)
    (c : Equiv.Perm (A.model n)) (S : Finset K) (hS : S.Nonempty)
    (k : ℕ) :
    ‖pairIndicatorIterate A n c S k -
        indicator (permutationGraph (A.model n) c)‖ ≤
      k * ‖pairIndicatorIterate A n c S 1 -
        pairIndicatorIterate A n c S 0‖ := by
  calc
    ‖pairIndicatorIterate A n c S k -
        indicator (permutationGraph (A.model n) c)‖ ≤
      ∑ i ∈ Finset.range k,
        ‖pairIndicatorIterate A n c S (i + 1) -
          pairIndicatorIterate A n c S i‖ := by
        exact KunRounding.norm_iterate_sub_le_sum
          (finiteModelAverage (pairModel (A.model n)) (pairMap A n) S)
          (indicator (permutationGraph (A.model n) c)) k
    _ ≤ ∑ _i ∈ Finset.range k,
        ‖pairIndicatorIterate A n c S 1 -
          pairIndicatorIterate A n c S 0‖ :=
      Finset.sum_le_sum fun i _ ↦
        norm_pairIndicatorIterate_displacement_le_initial
          A n c S hS i
    _ = k * ‖pairIndicatorIterate A n c S 1 -
        pairIndicatorIterate A n c S 0‖ := by simp

/-- Thresholding between one third and two thirds changes the input
permutation graph by at most nine times the trajectory's squared movement. -/
theorem card_pairSuperlevel_symmDiff_le
    (A : SoficApproximation (K × J)) (n : ℕ)
    (c : Equiv.Perm (A.model n)) (S : Finset K) (k : ℕ) (t : ℝ)
    (ht0 : (1 : ℝ) / 3 < t) (ht1 : t < (2 : ℝ) / 3) :
    (((KunRounding.superlevelSet (pairIndicatorIterate A n c S k) t) ∆
        permutationGraph (A.model n) c).card : ℝ) ≤
      9 * ‖pairIndicatorIterate A n c S k -
        indicator (permutationGraph (A.model n) c)‖ ^ 2 :=
  KunRounding.card_superlevelSet_symmDiff_le
    (pairIndicatorIterate A n c S k)
    (permutationGraph (A.model n) c) t ht0 ht1

/-- Quantitative proximity of a thresholded diagonal iterate to its input
graph, expressed through the initial tagged generator cut. -/
theorem card_pairSuperlevel_symmDiff_le_cut
    (A : SoficApproximation (K × J)) (n : ℕ)
    (c : Equiv.Perm (A.model n)) (S : Finset K) (hS : S.Nonempty)
    (k : ℕ) (t : ℝ) (ht0 : (1 : ℝ) / 3 < t)
    (ht1 : t < (2 : ℝ) / 3) :
    (((KunRounding.superlevelSet (pairIndicatorIterate A n c S k) t) ∆
        permutationGraph (A.model n) c).card : ℝ) ≤
      9 * k ^ 2 * (S.card : ℝ)⁻¹ *
        generatorCutSize (pairModel (A.model n)) (pairMap A n) S
          (permutationGraph (A.model n) c) := by
  have hpath := norm_pairIndicatorIterate_sub_le A n c S hS k
  have hright : 0 ≤ (k : ℝ) *
      ‖pairIndicatorIterate A n c S 1 -
        pairIndicatorIterate A n c S 0‖ := by positivity
  have hpathSq := (sq_le_sq₀ (norm_nonneg _) hright).2 hpath
  have hinitial :
      ‖pairIndicatorIterate A n c S 1 -
          pairIndicatorIterate A n c S 0‖ ^ 2 ≤
        (S.card : ℝ)⁻¹ *
          generatorCutSize (pairModel (A.model n)) (pairMap A n) S
            (permutationGraph (A.model n) c) := by
    simpa [pairIndicatorIterate] using
      norm_finiteModelAverage_indicator_sub_sq_le
        (pairModel (A.model n)) (pairMap A n) S hS
        (permutationGraph (A.model n) c)
  calc
    (((KunRounding.superlevelSet (pairIndicatorIterate A n c S k) t) ∆
        permutationGraph (A.model n) c).card : ℝ) ≤
      9 * ‖pairIndicatorIterate A n c S k -
        indicator (permutationGraph (A.model n) c)‖ ^ 2 :=
      card_pairSuperlevel_symmDiff_le A n c S k t ht0 ht1
    _ ≤ 9 * ((k : ℝ) *
        ‖pairIndicatorIterate A n c S 1 -
          pairIndicatorIterate A n c S 0‖) ^ 2 := by gcongr
    _ ≤ 9 * k ^ 2 * ((S.card : ℝ)⁻¹ *
        generatorCutSize (pairModel (A.model n)) (pairMap A n) S
          (permutationGraph (A.model n) c)) := by
      calc
        9 * ((k : ℝ) *
            ‖pairIndicatorIterate A n c S 1 -
              pairIndicatorIterate A n c S 0‖) ^ 2 =
          9 * k ^ 2 *
            ‖pairIndicatorIterate A n c S 1 -
              pairIndicatorIterate A n c S 0‖ ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hinitial (by positivity)
    _ = 9 * k ^ 2 * (S.card : ℝ)⁻¹ *
        generatorCutSize (pairModel (A.model n)) (pairMap A n) S
          (permutationGraph (A.model n) c) := by ring

/-- Once distinct group generators have distinct assigned first-factor
permutations, the occurrence boundary of the diagonal generator graph is
exactly the tagged relation boundary used by the repair argument. -/
theorem boundaryCard_pairGeneratorGraph_eq_relationBoundary
    (A : SoficApproximation (K × J)) (n : ℕ) (S : Finset K)
    (hinj : Set.InjOn (fun k : K ↦ A.map n (k, (1 : J))) (S : Set K))
    (U : Finset (pairModel (A.model n))) :
    (generatorGraph (pairModel (A.model n)) S (pairMap A n)).boundaryCard U =
      (relationBoundary (A.model n) (productLabels A n S) U).card := by
  classical
  let X := generatorGraph (pairModel (A.model n)) S (pairMap A n)
  unfold boundaryCard
  apply Finset.card_bij (fun e _ ↦ (A.map n (e.1.1.1, (1 : J)), e.1.2))
  · intro e he
    rw [mem_relationBoundary]
    refine ⟨?_, ?_⟩
    · apply Finset.mem_image.mpr
      exact ⟨e.1.1.1, e.1.1.2, rfl⟩
    · have hcross := (Finset.mem_filter.mp he).2
      change (e.1.2 ∈ U ∧ pairMap A n e.1.1.1 e.1.2 ∉ U) ∨
        (pairMap A n e.1.1.1 e.1.2 ∈ U ∧ e.1.2 ∉ U) at hcross
      rcases hcross with hcross | hcross
      · exact Or.inl (by simpa [diagonalAction, pairMap] using hcross)
      · exact Or.inr (by
          simpa [diagonalAction, pairMap] using ⟨hcross.2, hcross.1⟩)
  · intro e _ f _ hef
    have hfirst : e.1.1 = f.1.1 := Subtype.ext
      (hinj e.1.1.2 f.1.1.2
        (congrArg (fun q : Equiv.Perm (A.model n) ×
          pairModel (A.model n) ↦ q.1) hef))
    have hsecond : e.1.2 = f.1.2 :=
      congrArg (fun q : Equiv.Perm (A.model n) ×
        pairModel (A.model n) ↦ q.2) hef
    have hval : e.1 = f.1 := Prod.ext hfirst hsecond
    exact Subtype.ext hval
  · intro p hp
    have hpdata := (mem_relationBoundary
      (A.model n) (productLabels A n S) U p).1 hp
    rw [productLabels, Finset.mem_image] at hpdata
    obtain ⟨s, hs, hlabel⟩ := hpdata.1
    rw [← hlabel] at hpdata
    let t : S := ⟨s, hs⟩
    have hmove : pairMap A n s p.2 ≠ p.2 := by
      intro hfix
      have hfix' : diagonalAction (A.model n)
          (A.map n (s, (1 : J))) p.2 = p.2 := by
        simpa [diagonalAction, pairMap] using hfix
      rcases hpdata.2 with hcross | hcross
      · apply hcross.2
        rw [hfix']
        exact hcross.1
      · apply hcross.1
        rw [← hfix']
        exact hcross.2
    let e : X.edge :=
      ⟨(t, p.2), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmove⟩⟩
    refine ⟨e, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases hpdata.2 with hcross | hcross
      · exact Or.inl (by
          simpa [X, e, t, diagonalAction, pairMap] using hcross)
      · exact Or.inr (by
          simpa [X, e, t, diagonalAction, pairMap] using
            ⟨hcross.2, hcross.1⟩)
    · exact Prod.ext hlabel (by rfl)

/-- Equivalent generator-cut form of the preceding boundary identity. -/
theorem generatorCutSize_pair_eq_relationBoundary
    (A : SoficApproximation (K × J)) (n : ℕ) (S : Finset K)
    (hinj : Set.InjOn (fun k : K ↦ A.map n (k, (1 : J))) (S : Set K))
    (U : Finset (pairModel (A.model n))) :
    generatorCutSize (pairModel (A.model n)) (pairMap A n) S U =
      (relationBoundary (A.model n) (productLabels A n S) U).card := by
  rw [← boundaryCard_generatorGraph]
  exact boundaryCard_pairGeneratorGraph_eq_relationBoundary A n S hinj U

/-- The graph-scale Kazhdan contraction transfers verbatim to the uncentered
diagonal indicator trajectory. -/
theorem pairIndicatorDisplacementNormSq_eventually_lt
    {Q : Finset K} {ε : ℝ} (hQ : IsKazhdanPair.{0, 0} K Q ε)
    (S : Finset K) (hQS : Q ⊆ S) (hone : 1 ∈ S) (hεone : ε ≤ 1)
    (A : SoficApproximation (K × J)) (k : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ c : Equiv.Perm (A.model n),
      ‖pairIndicatorIterate A n c S (k + 1) -
          pairIndicatorIterate A n c S k‖ ^ 2 /
          Fintype.card (A.model n) <
        4 * (1 - ε ^ 2 / (4 * S.card)) ^ (2 * k) *
          (‖pairIndicatorIterate A n c S 1 -
            pairIndicatorIterate A n c S 0‖ ^ 2 /
              Fintype.card (A.model n)) + δ := by
  obtain ⟨N, hN⟩ :=
    KunThomFiniteMarkov.finiteModelAveragingDisplacementNormSq_eventually_lt
      hQ S hQS hone hεone A k δ hδ
  refine ⟨N, fun n hn c ↦ ?_⟩
  have h := hN n hn c
  unfold KunThomFiniteMarkov.finiteModelAveragingDisplacementNormSq at h
  rw [finiteModelAverageIterate_displacement_eq_pairIndicator
      A n c S ⟨1, hone⟩ k,
    finiteModelAverageIterate_displacement_eq_pairIndicator
      A n c S ⟨1, hone⟩ 0] at h
  exact h

/-- Coarea thresholding of a diagonal indicator iterate, with every term
measured at the permutation-graph scale. -/
theorem exists_threshold_pairIndicator_boundary_sq
    (A : SoficApproximation (K × J)) (n : ℕ)
    (c : Equiv.Perm (A.model n)) (S : Finset K) (hS : S.Nonempty)
    (k : ℕ) :
    ∃ t : ℝ, (1 : ℝ) / 3 < t ∧ t < (2 : ℝ) / 3 ∧
      ((1 : ℝ) / 3) * ((2 : ℝ) / 3 - (1 : ℝ) / 3) ^ 2 *
          ((generatorGraph (pairModel (A.model n)) S (pairMap A n)).boundaryCard
            ((generatorGraph (pairModel (A.model n)) S (pairMap A n)).superlevel
              (pairIndicatorIterate A n c S k) t) : ℝ) ^ 2 ≤
        4 * (S.card : ℝ) ^ 2 * Fintype.card (A.model n) *
          ‖pairIndicatorIterate A n c S k‖ *
          ‖pairIndicatorIterate A n c S (k + 1) -
            pairIndicatorIterate A n c S k‖ := by
  have hf (z : pairModel (A.model n)) :
      0 ≤ pairIndicatorIterate A n c S k z :=
    (pairIndicatorIterate_between_zero_one A n c S hS k z).1
  obtain ⟨t, ht0, ht1, ht⟩ :=
    exists_generatorGraph_boundary_sq_le_markov
      (pairModel (A.model n)) S hS (pairMap A n)
      (pairIndicatorIterate A n c S k)
      ((1 : ℝ) / 3) ((2 : ℝ) / 3) (by norm_num) (by norm_num) hf
  refine ⟨t, ht0, ht1, ?_⟩
  rw [sum_pairIndicatorIterate A n c S hS k] at ht
  simpa [pairIndicatorIterate_succ] using ht

end KunThomRounding
end NonsoficGroupsExist
