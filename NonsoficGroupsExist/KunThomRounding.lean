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

/-- The diagonal cut of a product of two `ε`-almost centralizing
permutations is smaller than `4 ε |Y|`.  This is the finite estimate used at
the entrance to the Kun--Thom improvement argument: multiplication doubles
the commutation defect, and passing from a permutation graph to its diagonal
boundary doubles it once more. -/
theorem generatorCutSize_pair_product_lt
    (A : SoficApproximation (K × J)) (n : ℕ) (S : Finset K)
    (hinj : Set.InjOn (fun k : K ↦ A.map n (k, (1 : J))) (S : Set K))
    {ε : ℝ} {a b : Equiv.Perm (A.model n)}
    (ha : IsEpsilonGood (A.model n) (productLabels A n S) ε a)
    (hb : IsEpsilonGood (A.model n) (productLabels A n S) ε b) :
    (generatorCutSize (pairModel (A.model n)) (pairMap A n) S
        (permutationGraph (A.model n) (a * b)) : ℝ) <
      4 * ε * Fintype.card (A.model n) := by
  let labels := productLabels A n S
  have hmulNat := card_badArcs_mul_le (A.model n) labels a b
  have hmul : ((badArcs (A.model n) labels (a * b)).card : ℝ) ≤
      (badArcs (A.model n) labels a).card +
        (badArcs (A.model n) labels b).card := by
    exact_mod_cast hmulNat
  have hboundaryNat := card_relationBoundary_permutationGraph_le
    (A.model n) labels (a * b)
  have hboundary :
      ((relationBoundary (A.model n) labels
        (permutationGraph (A.model n) (a * b))).card : ℝ) ≤
          2 * (badArcs (A.model n) labels (a * b)).card := by
    exact_mod_cast hboundaryNat
  rw [generatorCutSize_pair_eq_relationBoundary A n S hinj]
  dsimp [labels] at ha hb hmul hboundary ⊢
  linarith [ha.1, hb.1]

/-- A thresholded `k`-step diagonal trajectory remains quantitatively close
to the product permutation graph.  Unlike an arbitrary relation certificate,
this bound is derived from the two input almost-centralizer defects. -/
theorem card_pairSuperlevel_product_symmDiff_lt
    (A : SoficApproximation (K × J)) (n : ℕ) (S : Finset K)
    (hS : S.Nonempty)
    (hinj : Set.InjOn (fun k : K ↦ A.map n (k, (1 : J))) (S : Set K))
    {ε : ℝ} {a b : Equiv.Perm (A.model n)}
    (ha : IsEpsilonGood (A.model n) (productLabels A n S) ε a)
    (hb : IsEpsilonGood (A.model n) (productLabels A n S) ε b)
    (k : ℕ) (hk : 0 < k) (t : ℝ)
    (ht0 : (1 : ℝ) / 3 < t) (ht1 : t < (2 : ℝ) / 3) :
    (((KunRounding.superlevelSet
        (pairIndicatorIterate A n (a * b) S k) t) ∆
          permutationGraph (A.model n) (a * b)).card : ℝ) <
      36 * k ^ 2 * (S.card : ℝ)⁻¹ * ε *
        Fintype.card (A.model n) := by
  have hclose := card_pairSuperlevel_symmDiff_le_cut
    A n (a * b) S hS k t ht0 ht1
  have hcut := generatorCutSize_pair_product_lt A n S hinj ha hb
  have hcoefficient : 0 < 9 * (k : ℝ) ^ 2 * (S.card : ℝ)⁻¹ := by
    have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
    have hcard : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
    positivity
  calc
    (((KunRounding.superlevelSet
        (pairIndicatorIterate A n (a * b) S k) t) ∆
          permutationGraph (A.model n) (a * b)).card : ℝ) ≤
        9 * k ^ 2 * (S.card : ℝ)⁻¹ *
          generatorCutSize (pairModel (A.model n)) (pairMap A n) S
            (permutationGraph (A.model n) (a * b)) := hclose
    _ < 9 * k ^ 2 * (S.card : ℝ)⁻¹ *
          (4 * ε * Fintype.card (A.model n)) :=
      mul_lt_mul_of_pos_left hcut hcoefficient
    _ = 36 * k ^ 2 * (S.card : ℝ)⁻¹ * ε *
          Fintype.card (A.model n) := by ring

/-- The initial diagonal Markov displacement of a product is controlled at
the graph scale by the two input almost-centralizer defects. -/
theorem pairIndicator_initialDisplacement_sq_div_lt
    (A : SoficApproximation (K × J)) (n : ℕ) (S : Finset K)
    (hS : S.Nonempty)
    (hinj : Set.InjOn (fun k : K ↦ A.map n (k, (1 : J))) (S : Set K))
    (hcard : 0 < Fintype.card (A.model n))
    {ε : ℝ} {a b : Equiv.Perm (A.model n)}
    (ha : IsEpsilonGood (A.model n) (productLabels A n S) ε a)
    (hb : IsEpsilonGood (A.model n) (productLabels A n S) ε b) :
    ‖pairIndicatorIterate A n (a * b) S 1 -
        pairIndicatorIterate A n (a * b) S 0‖ ^ 2 /
          Fintype.card (A.model n) <
      4 * (S.card : ℝ)⁻¹ * ε := by
  have hinitial :
      ‖pairIndicatorIterate A n (a * b) S 1 -
          pairIndicatorIterate A n (a * b) S 0‖ ^ 2 ≤
        (S.card : ℝ)⁻¹ *
          generatorCutSize (pairModel (A.model n)) (pairMap A n) S
            (permutationGraph (A.model n) (a * b)) := by
    simpa [pairIndicatorIterate] using
      norm_finiteModelAverage_indicator_sub_sq_le
        (pairModel (A.model n)) (pairMap A n) S hS
        (permutationGraph (A.model n) (a * b))
  have hcut := generatorCutSize_pair_product_lt A n S hinj ha hb
  have hcardReal : (0 : ℝ) < Fintype.card (A.model n) := by
    exact_mod_cast hcard
  have hScard : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  rw [div_lt_iff₀ hcardReal]
  calc
    ‖pairIndicatorIterate A n (a * b) S 1 -
        pairIndicatorIterate A n (a * b) S 0‖ ^ 2 ≤
      (S.card : ℝ)⁻¹ *
        generatorCutSize (pairModel (A.model n)) (pairMap A n) S
          (permutationGraph (A.model n) (a * b)) := hinitial
    _ < (S.card : ℝ)⁻¹ *
        (4 * ε * Fintype.card (A.model n)) :=
      mul_lt_mul_of_pos_left hcut (inv_pos.mpr hScard)
    _ = (4 * (S.card : ℝ)⁻¹ * ε) *
        Fintype.card (A.model n) := by ring

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

/-- Uniform graph-scale contraction for products of two `η`-almost
centralizing permutations.  The right-hand side is now entirely numerical;
the initial displacement has been eliminated using the product-cut bound. -/
theorem pairProductDisplacementNormSq_eventually_lt
    {Q : Finset K} {κ : ℝ} (hQ : IsKazhdanPair.{0, 0} K Q κ)
    (S : Finset K) (hQS : Q ⊆ S) (hone : 1 ∈ S) (hκone : κ ≤ 1)
    (A : SoficApproximation (K × J)) (k : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N,
      Set.InjOn (fun x : K ↦ A.map n (x, (1 : J))) (S : Set K) →
      0 < Fintype.card (A.model n) →
      ∀ {η : ℝ} {a b : Equiv.Perm (A.model n)},
        IsEpsilonGood (A.model n) (productLabels A n S) η a →
        IsEpsilonGood (A.model n) (productLabels A n S) η b →
        ‖pairIndicatorIterate A n (a * b) S (k + 1) -
            pairIndicatorIterate A n (a * b) S k‖ ^ 2 /
              Fintype.card (A.model n) <
          16 * (1 - κ ^ 2 / (4 * S.card)) ^ (2 * k) *
              (S.card : ℝ)⁻¹ * η + δ := by
  obtain ⟨N, hN⟩ := pairIndicatorDisplacementNormSq_eventually_lt
    hQ S hQS hone hκone A k δ hδ
  refine ⟨N, fun n hn hinj hcard η a b ha hb ↦ ?_⟩
  have hcontraction := hN n hn (a * b)
  have hinitial := pairIndicator_initialDisplacement_sq_div_lt
    A n S ⟨1, hone⟩ hinj hcard ha hb
  obtain ⟨hbase, _⟩ :=
    kazhdanFactor_nonneg_lt_one hQ S hone hκone
  have hcoefficient :
      0 ≤ 4 * (1 - κ ^ 2 / (4 * S.card)) ^ (2 * k) :=
    mul_nonneg (by norm_num) (pow_nonneg hbase _)
  calc
    ‖pairIndicatorIterate A n (a * b) S (k + 1) -
        pairIndicatorIterate A n (a * b) S k‖ ^ 2 /
          Fintype.card (A.model n) <
      4 * (1 - κ ^ 2 / (4 * S.card)) ^ (2 * k) *
          (‖pairIndicatorIterate A n (a * b) S 1 -
            pairIndicatorIterate A n (a * b) S 0‖ ^ 2 /
              Fintype.card (A.model n)) + δ := hcontraction
    _ ≤ 4 * (1 - κ ^ 2 / (4 * S.card)) ^ (2 * k) *
          (4 * (S.card : ℝ)⁻¹ * η) + δ := by
      simpa [add_comm] using add_le_add_right
        (mul_le_mul_of_nonneg_left hinitial.le hcoefficient) δ
    _ = 16 * (1 - κ ^ 2 / (4 * S.card)) ^ (2 * k) *
          (S.card : ℝ)⁻¹ * η + δ := by ring

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

/-- A normalized displacement bound yields a threshold relation with a
prescribed boundary fraction.  The fourth-power numerical hypothesis is the
result of squaring the coarea estimate and using the graph-scale norm bound
`‖f_k‖² ≤ |Y|`; it contains no hidden asymptotic premise. -/
theorem exists_threshold_pairIndicator_boundary_lt
    (A : SoficApproximation (K × J)) (n : ℕ)
    (c : Equiv.Perm (A.model n)) (S : Finset K) (hS : S.Nonempty)
    (k : ℕ) (hcard : 0 < Fintype.card (A.model n))
    {θ β : ℝ} (hβ : 0 < β)
    (hdisplacement :
      ‖pairIndicatorIterate A n c S (k + 1) -
          pairIndicatorIterate A n c S k‖ ^ 2 /
            Fintype.card (A.model n) < θ)
    (hnumerical :
      16 * (S.card : ℝ) ^ 4 * θ <
        (((1 : ℝ) / 3) * (((2 : ℝ) / 3) - (1 : ℝ) / 3) ^ 2) ^ 2 *
          β ^ 4) :
    ∃ t : ℝ, (1 : ℝ) / 3 < t ∧ t < (2 : ℝ) / 3 ∧
      ((generatorGraph (pairModel (A.model n)) S (pairMap A n)).boundaryCard
          ((generatorGraph (pairModel (A.model n)) S (pairMap A n)).superlevel
            (pairIndicatorIterate A n c S k) t) : ℝ) <
        β * Fintype.card (A.model n) := by
  obtain ⟨t, ht0, ht1, ht⟩ :=
    exists_threshold_pairIndicator_boundary_sq A n c S hS k
  refine ⟨t, ht0, ht1, ?_⟩
  let N : ℝ := Fintype.card (A.model n)
  let s : ℝ := S.card
  let f : ℝ := ‖pairIndicatorIterate A n c S k‖
  let d : ℝ := ‖pairIndicatorIterate A n c S (k + 1) -
    pairIndicatorIterate A n c S k‖
  let B : ℝ :=
    (generatorGraph (pairModel (A.model n)) S (pairMap A n)).boundaryCard
      ((generatorGraph (pairModel (A.model n)) S (pairMap A n)).superlevel
        (pairIndicatorIterate A n c S k) t)
  let q : ℝ := ((1 : ℝ) / 3) *
    (((2 : ℝ) / 3) - (1 : ℝ) / 3) ^ 2
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast hcard
  have hs : 0 < s := by
    dsimp [s]
    exact_mod_cast hS.card_pos
  have hf0 : 0 ≤ f := norm_nonneg _
  have hd0 : 0 ≤ d := norm_nonneg _
  have hB0 : 0 ≤ B := by positivity
  have hq : 0 < q := by
    dsimp [q]
    norm_num
  have hfnorm : f ^ 2 ≤ N := by
    dsimp [f, N]
    exact norm_pairIndicatorIterate_sq_le_card A n c S hS k
  have hdnorm : d ^ 2 < θ * N := by
    change d ^ 2 / N < θ at hdisplacement
    rwa [div_lt_iff₀ hN] at hdisplacement
  have hfd : f ^ 2 * d ^ 2 < N * (θ * N) := by
    calc
      f ^ 2 * d ^ 2 ≤ N * d ^ 2 :=
        mul_le_mul_of_nonneg_right hfnorm (sq_nonneg d)
      _ < N * (θ * N) := mul_lt_mul_of_pos_left hdnorm hN
  change q * B ^ 2 ≤ 4 * s ^ 2 * N * f * d at ht
  by_contra hnot
  have hB : β * N ≤ B := le_of_not_gt hnot
  have hright :
      (4 * s ^ 2 * N * f * d) ^ 2 <
        (q * (β * N) ^ 2) ^ 2 := by
    calc
      (4 * s ^ 2 * N * f * d) ^ 2 =
          16 * s ^ 4 * N ^ 2 * (f ^ 2 * d ^ 2) := by ring
      _ < 16 * s ^ 4 * N ^ 2 * (N * (θ * N)) :=
        mul_lt_mul_of_pos_left hfd (by positivity)
      _ = (16 * s ^ 4 * θ) * N ^ 4 := by ring
      _ < (q ^ 2 * β ^ 4) * N ^ 4 := by
        apply mul_lt_mul_of_pos_right _ (pow_pos hN 4)
        simpa [s, q] using hnumerical
      _ = (q * (β * N) ^ 2) ^ 2 := by ring
  have hleft0 : 0 ≤ q * B ^ 2 := mul_nonneg hq.le (sq_nonneg B)
  have hright0 : 0 ≤ 4 * s ^ 2 * N * f * d := by positivity
  have hcoareaSq :
      (q * B ^ 2) ^ 2 ≤ (4 * s ^ 2 * N * f * d) ^ 2 :=
    (sq_le_sq₀ hleft0 hright0).2 ht
  have hbase0 : 0 ≤ β * N := mul_nonneg hβ.le hN.le
  have hbaseSq : (β * N) ^ 2 ≤ B ^ 2 :=
    (sq_le_sq₀ hbase0 hB0).2 hB
  have hscaled : q * (β * N) ^ 2 ≤ q * B ^ 2 :=
    mul_le_mul_of_nonneg_left hbaseSq hq.le
  have hscaled0 : 0 ≤ q * (β * N) ^ 2 :=
    mul_nonneg hq.le (sq_nonneg _)
  have hscaledSq :
      (q * (β * N) ^ 2) ^ 2 ≤ (q * B ^ 2) ^ 2 :=
    (sq_le_sq₀ hscaled0 hleft0).2 hscaled
  linarith

/-- The complete finite relation-improvement output of the diagonal
Kazhdan/coarea argument.  For products of two `η`-almost centralizers it
constructs a relation that is both close to the product permutation graph and
has a prescribed small diagonal boundary. -/
theorem exists_pairProduct_relation_eventually
    {Q : Finset K} {κ : ℝ} (hQ : IsKazhdanPair.{0, 0} K Q κ)
    (S : Finset K) (hQS : Q ⊆ S) (hone : 1 ∈ S) (hκone : κ ≤ 1)
    (A : SoficApproximation (K × J))
    (k : ℕ) (hk : 0 < k) {δ η β : ℝ}
    (hδ : 0 < δ) (hβ : 0 < β)
    (hnumerical :
      16 * (S.card : ℝ) ^ 4 *
          (16 * (1 - κ ^ 2 / (4 * S.card)) ^ (2 * k) *
              (S.card : ℝ)⁻¹ * η + δ) <
        (((1 : ℝ) / 3) * (((2 : ℝ) / 3) - (1 : ℝ) / 3) ^ 2) ^ 2 *
          β ^ 4) :
    ∃ N : ℕ, ∀ n ≥ N,
      Set.InjOn (fun x : K ↦ A.map n (x, (1 : J))) (S : Set K) →
      0 < Fintype.card (A.model n) →
      ∀ {a b : Equiv.Perm (A.model n)},
        IsEpsilonGood (A.model n) (productLabels A n S) η a →
        IsEpsilonGood (A.model n) (productLabels A n S) η b →
        ∃ U : Finset (A.model n × A.model n),
          (((U ∆ permutationGraph (A.model n) (a * b)).card : ℝ) <
            36 * k ^ 2 * (S.card : ℝ)⁻¹ * η *
              Fintype.card (A.model n)) ∧
          (((relationBoundary (A.model n) (productLabels A n S) U).card : ℝ) <
            β * Fintype.card (A.model n)) := by
  obtain ⟨N, hN⟩ := pairProductDisplacementNormSq_eventually_lt
    hQ S hQS hone hκone A k δ hδ
  refine ⟨N, fun n hn hinj hcard a b ha hb ↦ ?_⟩
  have hdisplacement := hN n hn hinj hcard ha hb
  obtain ⟨t, ht0, ht1, hboundary⟩ :=
    exists_threshold_pairIndicator_boundary_lt
      A n (a * b) S ⟨1, hone⟩ k hcard hβ hdisplacement hnumerical
  let U : Finset (A.model n × A.model n) :=
    (generatorGraph (pairModel (A.model n)) S (pairMap A n)).superlevel
      (pairIndicatorIterate A n (a * b) S k) t
  refine ⟨U, ?_, ?_⟩
  · simpa [U, FiniteMultiGraph.superlevel, KunRounding.superlevelSet] using
      card_pairSuperlevel_product_symmDiff_lt
      A n S ⟨1, hone⟩ hinj ha hb k hk t ht0 ht1
  · rw [← boundaryCard_pairGeneratorGraph_eq_relationBoundary
      A n S hinj U]
    simpa [U] using hboundary

end KunThomRounding
end NonsoficGroupsExist
