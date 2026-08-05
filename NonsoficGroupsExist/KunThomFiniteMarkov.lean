import NonsoficGroupsExist.KunThomCorrelation
import NonsoficGroupsExist.AlmostAutomorphism

/-!
# Finite diagonal Markov transfer for Kun--Thom

Exact group-word averages in the graph-scale GNS argument must be compared
with the genuine averages of the assigned finite permutations.  Approximate
multiplication is charged only on the permutation graph, using the localized
diagonal estimate, and all norms are divided by `|Y|`.
-/

namespace NonsoficGroupsExist
namespace KunThomFiniteMarkov

open KazhdanFiniteModel
open KazhdanGNS
open KazhdanImprovement
open KunThomDiagonal
open AlmostAutomorphism

variable {K J : Type} [Group K] [Group J]

/-- The ordered-pair carrier bundled as a finite permutation model. -/
abbrev pairModel (Y : FiniteModel) : FiniteModel where
  carrier := Y × Y
  fintype := inferInstance
  decidableEq := inferInstance

/-- The assigned first-factor permutation acting diagonally on ordered pairs. -/
def pairMap (A : SoficApproximation (K × J)) (n : ℕ) (g : K) :
    Equiv.Perm (pairModel (A.model n)) :=
  diagonalPerm (A.map n (g, 1))

/-- Cauchy--Schwarz for a finite average with an arbitrary positive
normalizing scale. -/
theorem norm_average_sq_div_scale_le {I E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Finset I) (hS : S.Nonempty) (e : I → E)
    (D δ : ℝ) (hD : 0 < D)
    (he : ∀ i ∈ S, ‖e i‖ ^ 2 / D ≤ δ) :
    ‖(S.card : ℝ)⁻¹ • ∑ i ∈ S, e i‖ ^ 2 / D ≤ δ := by
  have hScardNat : 0 < S.card := Finset.card_pos.mpr hS
  have hScard : (0 : ℝ) < S.card := by exact_mod_cast hScardNat
  have he' (i : I) (hi : i ∈ S) : ‖e i‖ ^ 2 ≤ δ * D :=
    (div_le_iff₀ hD).mp (he i hi)
  have hsumSq : ∑ i ∈ S, ‖e i‖ ^ 2 ≤ (S.card : ℝ) * (δ * D) := by
    calc
      ∑ i ∈ S, ‖e i‖ ^ 2 ≤ ∑ _i ∈ S, δ * D :=
        Finset.sum_le_sum fun i hi ↦ he' i hi
      _ = (S.card : ℝ) * (δ * D) := by simp
  have hcauchy :
      (∑ i ∈ S, ‖e i‖) ^ 2 ≤
        (S.card : ℝ) * ∑ i ∈ S, ‖e i‖ ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq S
      (fun _ ↦ (1 : ℝ)) (fun i ↦ ‖e i‖)
  have htriangle :
      ‖(S.card : ℝ)⁻¹ • ∑ i ∈ S, e i‖ ≤
        (S.card : ℝ)⁻¹ * ∑ i ∈ S, ‖e i‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hScard)]
    gcongr
    exact norm_sum_le _ _
  have hsumNonneg : 0 ≤ ∑ i ∈ S, ‖e i‖ :=
    Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hright : 0 ≤ (S.card : ℝ)⁻¹ * ∑ i ∈ S, ‖e i‖ :=
    mul_nonneg (inv_nonneg.mpr hScard.le) hsumNonneg
  have htriangleSq := (sq_le_sq₀ (norm_nonneg _) hright).2 htriangle
  calc
    ‖(S.card : ℝ)⁻¹ • ∑ i ∈ S, e i‖ ^ 2 / D ≤
        ((S.card : ℝ)⁻¹ * ∑ i ∈ S, ‖e i‖) ^ 2 / D :=
      div_le_div_of_nonneg_right htriangleSq hD.le
    _ ≤ ((S.card : ℝ)⁻¹ ^ 2 *
        ((S.card : ℝ) * ∑ i ∈ S, ‖e i‖ ^ 2)) / D := by
      gcongr
      nlinarith [hcauchy]
    _ ≤ ((S.card : ℝ)⁻¹ ^ 2 *
        ((S.card : ℝ) * ((S.card : ℝ) * (δ * D)))) / D := by
      gcongr
    _ = δ := by field_simp

/-- A fixed finite exact translation and its composed finite-model
translation differ by `o(|Y_n|)`, uniformly over every permutation graph. -/
theorem finiteTranslation_hilbert_error_eventually
    (A : SoficApproximation (K × J)) (s : K) (a : K →₀ ℝ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ c : Equiv.Perm (A.model n),
      ‖finiteExactTranslation (pairModel (A.model n)) (pairMap A n)
          (permutationGraph (A.model n) c) s a -
        finiteComposedTranslation (pairModel (A.model n)) (pairMap A n)
          (permutationGraph (A.model n) c) s a‖ ^ 2 /
        Fintype.card (A.model n) < δ := by
  classical
  let R : ℝ := ∑ g ∈ a.support, |a g| ^ 2
  let m : ℝ := a.support.card
  let η : ℝ := δ / (R * m + 1)
  have hR : 0 ≤ R := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hm : 0 ≤ m := by positivity
  have hden : 0 < R * m + 1 := by positivity
  have hη : 0 < η := div_pos hδ hden
  have htol : 0 < η / 4 := by positivity
  obtain ⟨Nerr, hNerr⟩ := eventually_finset a.support
    (fun g n ↦ hammingDistance (A.model n)
      (A.map n (s * g, (1 : J)))
      (A.map n (s, 1) * A.map n (g, 1)) < η / 4) (by
        intro g hg
        simpa using A.asymptoticallyMultiplicative
          (s, (1 : J)) (g, 1) (η / 4) htol)
  obtain ⟨Ncard, hNcard⟩ := A.card_tendsToInfinity 1
  refine ⟨max Nerr Ncard, fun n hn c ↦ ?_⟩
  have hnerr : Nerr ≤ n := (le_max_left _ _).trans hn
  have hncard : Ncard ≤ n := (le_max_right _ _).trans hn
  have hcardNat : 0 < Fintype.card (A.model n) := by
    have := hNcard n hncard
    omega
  have hcard : (0 : ℝ) < Fintype.card (A.model n) := by
    exact_mod_cast hcardNat
  let e : K → EuclideanSpace ℝ (pairModel (A.model n)) := fun g ↦
    permutationOperator (pairMap A n (s * g))
        (centeredIndicator (permutationGraph (A.model n) c)) -
      permutationOperator (pairMap A n s * pairMap A n g)
        (centeredIndicator (permutationGraph (A.model n) c))
  have herr (g : K) (hg : g ∈ a.support) :
      ‖e g‖ ^ 2 / Fintype.card (A.model n) ≤ η := by
    have hlocal := norm_diagonal_centeredIndicator_sub_sq_le c
      (A.map n (s * g, (1 : J)))
      (A.map n (s, 1) * A.map n (g, 1))
    have hdist := hNerr n hnerr g hg
    calc
      ‖e g‖ ^ 2 / Fintype.card (A.model n) ≤
          (4 * ((hammingDisagreement
            (A.map n (s * g, (1 : J)))
            (A.map n (s, 1) * A.map n (g, 1))).card : ℝ)) /
              Fintype.card (A.model n) := by
        apply div_le_div_of_nonneg_right
        · simpa [e, pairMap, diagonalPerm_mul] using hlocal
        · exact hcard.le
      _ = 4 * hammingDistance (A.model n)
          (A.map n (s * g, (1 : J)))
          (A.map n (s, 1) * A.map n (g, 1)) := by
        rw [hammingDistance]
        ring
      _ ≤ η := by linarith
  have herr' (g : K) (hg : g ∈ a.support) :
      ‖e g‖ ^ 2 ≤ η * Fintype.card (A.model n) :=
    (div_le_iff₀ hcard).mp (herr g hg)
  have hsumErr : ∑ g ∈ a.support, ‖e g‖ ^ 2 ≤
      m * (η * Fintype.card (A.model n)) := by
    calc
      ∑ g ∈ a.support, ‖e g‖ ^ 2 ≤
          ∑ _g ∈ a.support, η * Fintype.card (A.model n) :=
        Finset.sum_le_sum fun g hg ↦ herr' g hg
      _ = m * (η * Fintype.card (A.model n)) := by simp [m]
  have hcauchy :
      (∑ g ∈ a.support, |a g| * ‖e g‖) ^ 2 ≤
        R * ∑ g ∈ a.support, ‖e g‖ ^ 2 := by
    simpa [R] using Finset.sum_mul_sq_le_sq_mul_sq a.support
      (fun g ↦ |a g|) (fun g ↦ ‖e g‖)
  have htriangle := norm_finiteTranslation_sub_le
    (pairModel (A.model n)) (pairMap A n)
      (permutationGraph (A.model n) c) s a
  change ‖finiteExactTranslation (pairModel (A.model n)) (pairMap A n)
      (permutationGraph (A.model n) c) s a -
    finiteComposedTranslation (pairModel (A.model n)) (pairMap A n)
      (permutationGraph (A.model n) c) s a‖ ≤
        ∑ g ∈ a.support, |a g| * ‖e g‖ at htriangle
  have hsumNonneg : 0 ≤ ∑ g ∈ a.support, |a g| * ‖e g‖ :=
    Finset.sum_nonneg fun _ _ ↦ mul_nonneg (abs_nonneg _) (norm_nonneg _)
  have htriangleSq := (sq_le_sq₀ (norm_nonneg _) hsumNonneg).2 htriangle
  calc
    ‖finiteExactTranslation (pairModel (A.model n)) (pairMap A n)
        (permutationGraph (A.model n) c) s a -
      finiteComposedTranslation (pairModel (A.model n)) (pairMap A n)
        (permutationGraph (A.model n) c) s a‖ ^ 2 /
          Fintype.card (A.model n) ≤
      (∑ g ∈ a.support, |a g| * ‖e g‖) ^ 2 /
        Fintype.card (A.model n) :=
      div_le_div_of_nonneg_right htriangleSq hcard.le
    _ ≤ (R * ∑ g ∈ a.support, ‖e g‖ ^ 2) /
        Fintype.card (A.model n) :=
      div_le_div_of_nonneg_right hcauchy hcard.le
    _ ≤ (R * (m * (η * Fintype.card (A.model n)))) /
        Fintype.card (A.model n) := by gcongr
    _ = R * m * η := by field_simp
    _ < δ := by
      dsimp [η]
      rw [show R * m * (δ / (R * m + 1)) =
        (R * m * δ) / (R * m + 1) by ring,
        div_lt_iff₀ hden]
      nlinarith [mul_nonneg hR hm]

/-- One exact averaging step and one genuine finite diagonal Markov step are
uniformly close on every permutation graph. -/
theorem finiteAveragingStep_hilbert_error_eventually
    (A : SoficApproximation (K × J)) (S : Finset K) (hS : S.Nonempty)
    (k : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ c : Equiv.Perm (A.model n),
      ‖finiteFinsuppCombination (pairModel (A.model n)) (pairMap A n)
          (permutationGraph (A.model n) c)
          (averagingCoefficients S (k + 1)) -
        finiteModelAverage (pairModel (A.model n)) (pairMap A n) S
          (finiteFinsuppCombination (pairModel (A.model n)) (pairMap A n)
            (permutationGraph (A.model n) c)
            (averagingCoefficients S k))‖ ^ 2 /
        Fintype.card (A.model n) < δ := by
  classical
  let a := averagingCoefficients S k
  let η := δ / 2
  have hη : 0 < η := by dsimp [η]; linarith
  have hηδ : η < δ := by dsimp [η]; linarith
  have hall (T : Finset K) :
      ∃ N : ℕ, ∀ n ≥ N, ∀ s ∈ T, ∀ c : Equiv.Perm (A.model n),
        ‖finiteExactTranslation (pairModel (A.model n)) (pairMap A n)
            (permutationGraph (A.model n) c) s a -
          finiteComposedTranslation (pairModel (A.model n)) (pairMap A n)
            (permutationGraph (A.model n) c) s a‖ ^ 2 /
          Fintype.card (A.model n) < η := by
    induction T using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | @insert s T hst ih =>
        obtain ⟨Ns, hNs⟩ := finiteTranslation_hilbert_error_eventually
          A s a η hη
        obtain ⟨NT, hNT⟩ := ih
        refine ⟨max Ns NT, fun n hn t ht c ↦ ?_⟩
        rcases Finset.mem_insert.mp ht with rfl | ht
        · exact hNs n ((le_max_left _ _).trans hn) c
        · exact hNT n ((le_max_right _ _).trans hn) t ht c
  obtain ⟨Nerr, hNerr⟩ := hall S
  obtain ⟨Ncard, hNcard⟩ := A.card_tendsToInfinity 1
  refine ⟨max Nerr Ncard, fun n hn c ↦ ?_⟩
  have hnerr : Nerr ≤ n := (le_max_left _ _).trans hn
  have hncard : Ncard ≤ n := (le_max_right _ _).trans hn
  have hcard : (0 : ℝ) < Fintype.card (A.model n) := by
    have := hNcard n hncard
    positivity
  let e : K → EuclideanSpace ℝ (pairModel (A.model n)) := fun s ↦
    finiteExactTranslation (pairModel (A.model n)) (pairMap A n)
        (permutationGraph (A.model n) c) s a -
      finiteComposedTranslation (pairModel (A.model n)) (pairMap A n)
        (permutationGraph (A.model n) c) s a
  have he (s : K) (hs : s ∈ S) :
      ‖e s‖ ^ 2 / Fintype.card (A.model n) ≤ η :=
    (hNerr n hnerr s hs c).le
  rw [finiteAveragingStep_sub_eq]
  change ‖(S.card : ℝ)⁻¹ • ∑ s ∈ S, e s‖ ^ 2 /
      Fintype.card (A.model n) < δ
  exact (norm_average_sq_div_scale_le S hS e
    (Fintype.card (A.model n)) η hcard he).trans_lt hηδ

/-- The assigned identity acts negligibly on every permutation graph at the
graph scale. -/
theorem sofic_one_hilbert_error_eventually
    (A : SoficApproximation (K × J)) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ c : Equiv.Perm (A.model n),
      ‖permutationOperator (pairMap A n 1)
          (centeredIndicator (permutationGraph (A.model n) c)) -
        centeredIndicator (permutationGraph (A.model n) c)‖ ^ 2 /
          Fintype.card (A.model n) < δ := by
  obtain ⟨N, hN⟩ := A.map_one_close (δ / 4) (by positivity)
  obtain ⟨Ncard, hNcard⟩ := A.card_tendsToInfinity 1
  refine ⟨max N Ncard, fun n hn c ↦ ?_⟩
  have hnmap : N ≤ n := (le_max_left _ _).trans hn
  have hncard : Ncard ≤ n := (le_max_right _ _).trans hn
  have hcard : (0 : ℝ) < Fintype.card (A.model n) := by
    have := hNcard n hncard
    positivity
  have hlocal := norm_diagonal_centeredIndicator_sub_sq_le c
    (A.map n ((1 : K), (1 : J))) 1
  calc
    ‖permutationOperator (pairMap A n 1)
          (centeredIndicator (permutationGraph (A.model n) c)) -
        centeredIndicator (permutationGraph (A.model n) c)‖ ^ 2 /
          Fintype.card (A.model n) ≤
      (4 * ((hammingDisagreement
        (A.map n ((1 : K), (1 : J))) 1).card : ℝ)) /
          Fintype.card (A.model n) := by
      apply div_le_div_of_nonneg_right
      · simpa [pairMap, permutationOperator_one] using hlocal
      · exact hcard.le
    _ = 4 * hammingDistance (A.model n)
        (A.map n ((1 : K), (1 : J))) 1 := by
      rw [hammingDistance]
      ring
    _ < δ := by
      have hclose : hammingDistance (A.model n)
          (A.map n ((1 : K), (1 : J))) 1 < δ / 4 := by
        have hclose' := hN n hnmap
        change hammingDistance (A.model n)
          (A.map n ((1 : K), (1 : J))) 1 < δ / 4 at hclose'
        exact hclose'
      linarith

/-- Genuine diagonal Markov iteration started at a centered permutation
graph. -/
noncomputable def finiteModelAverageIterate
    (A : SoficApproximation (K × J)) (n : ℕ)
    (c : Equiv.Perm (A.model n)) (S : Finset K) (k : ℕ) :
    EuclideanSpace ℝ (pairModel (A.model n)) :=
  ((finiteModelAverage (pairModel (A.model n)) (pairMap A n) S)^[k])
    (centeredIndicator (permutationGraph (A.model n) c))

theorem finiteModelAverageIterate_succ
    (A : SoficApproximation (K × J)) (n : ℕ)
    (c : Equiv.Perm (A.model n)) (S : Finset K) (k : ℕ) :
    finiteModelAverageIterate A n c S (k + 1) =
      finiteModelAverage (pairModel (A.model n)) (pairMap A n) S
        (finiteModelAverageIterate A n c S k) := by
  rw [finiteModelAverageIterate, finiteModelAverageIterate,
    Function.iterate_succ_apply']

/-- At every fixed time, exact group-word averaging tracks the genuine
diagonal finite-model average uniformly over all permutation graphs. -/
theorem finiteAveragingIterate_hilbert_error_eventually
    (A : SoficApproximation (K × J)) (S : Finset K) (hS : S.Nonempty)
    (k : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ c : Equiv.Perm (A.model n),
      ‖finiteFinsuppCombination (pairModel (A.model n)) (pairMap A n)
          (permutationGraph (A.model n) c) (averagingCoefficients S k) -
        finiteModelAverageIterate A n c S k‖ ^ 2 /
          Fintype.card (A.model n) < δ := by
  induction k generalizing δ with
  | zero =>
      obtain ⟨N, hN⟩ := sofic_one_hilbert_error_eventually A δ hδ
      refine ⟨N, fun n hn c ↦ ?_⟩
      simpa [finiteModelAverageIterate, averagingCoefficients,
        finiteFinsuppCombination, pairMap] using hN n hn c
  | succ k ih =>
      let η := δ / 4
      have hη : 0 < η := by dsimp [η]; linarith
      obtain ⟨Nstep, hNstep⟩ :=
        finiteAveragingStep_hilbert_error_eventually A S hS k η hη
      obtain ⟨Nprev, hNprev⟩ := ih η hη
      obtain ⟨Ncard, hNcard⟩ := A.card_tendsToInfinity 1
      refine ⟨max (max Nstep Nprev) Ncard, fun n hn c ↦ ?_⟩
      have hnboth : max Nstep Nprev ≤ n := (le_max_left _ _).trans hn
      have hnstep : Nstep ≤ n := (le_max_left _ _).trans hnboth
      have hnprev : Nprev ≤ n := (le_max_right _ _).trans hnboth
      have hncard : Ncard ≤ n := (le_max_right _ _).trans hn
      have hcard : (0 : ℝ) < Fintype.card (A.model n) := by
        have := hNcard n hncard
        positivity
      let Ck := finiteFinsuppCombination (pairModel (A.model n))
        (pairMap A n) (permutationGraph (A.model n) c)
          (averagingCoefficients S k)
      let Cnext := finiteFinsuppCombination (pairModel (A.model n))
        (pairMap A n) (permutationGraph (A.model n) c)
          (averagingCoefficients S (k + 1))
      let Xk := finiteModelAverageIterate A n c S k
      let step := Cnext - finiteModelAverage
        (pairModel (A.model n)) (pairMap A n) S Ck
      let previous := Ck - Xk
      have hstep : ‖step‖ ^ 2 / Fintype.card (A.model n) < η :=
        hNstep n hnstep c
      have hprevious : ‖previous‖ ^ 2 /
          Fintype.card (A.model n) < η := hNprev n hnprev c
      have hdecomp :
          Cnext - finiteModelAverageIterate A n c S (k + 1) =
            step + finiteModelAverage (pairModel (A.model n))
              (pairMap A n) S previous := by
        rw [finiteModelAverageIterate_succ, finiteModelAverage_sub]
        simp only [step]
        abel
      have hnorm :
          ‖Cnext - finiteModelAverageIterate A n c S (k + 1)‖ ≤
            ‖step‖ + ‖previous‖ := by
        rw [hdecomp]
        exact (norm_add_le _ _).trans
          (add_le_add_right
            (norm_finiteModelAverage_le (pairModel (A.model n))
              (pairMap A n) S hS previous) ‖step‖)
      have hright : 0 ≤ ‖step‖ + ‖previous‖ :=
        add_nonneg (norm_nonneg _) (norm_nonneg _)
      have hsq := (sq_le_sq₀ (norm_nonneg _) hright).2 hnorm
      calc
        ‖Cnext - finiteModelAverageIterate A n c S (k + 1)‖ ^ 2 /
            Fintype.card (A.model n) ≤
          (‖step‖ + ‖previous‖) ^ 2 / Fintype.card (A.model n) :=
          div_le_div_of_nonneg_right hsq hcard.le
        _ ≤ (2 * ‖step‖ ^ 2 + 2 * ‖previous‖ ^ 2) /
            Fintype.card (A.model n) := by
          apply div_le_div_of_nonneg_right _ hcard.le
          nlinarith [sq_nonneg (‖step‖ - ‖previous‖)]
        _ = 2 * (‖step‖ ^ 2 / Fintype.card (A.model n)) +
            2 * (‖previous‖ ^ 2 / Fintype.card (A.model n)) := by ring
        _ < δ := by dsimp [η] at hstep hprevious; linarith

/-- Displacement transfer between two trajectories, normalized at an
arbitrary positive scale. -/
theorem displacement_sq_div_scale_le_of_close
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (D : ℝ) (hD : 0 < D) (C₀ C₁ X₀ X₁ : E) :
    ‖X₁ - X₀‖ ^ 2 / D ≤
      2 * (‖C₁ - C₀‖ ^ 2 / D) +
      4 * (‖C₀ - X₀‖ ^ 2 / D) +
      4 * (‖C₁ - X₁‖ ^ 2 / D) := by
  have hdecomp : X₁ - X₀ =
      (C₁ - C₀) + ((C₀ - X₀) + -(C₁ - X₁)) := by abel
  rw [hdecomp]
  calc
    ‖(C₁ - C₀) + ((C₀ - X₀) + -(C₁ - X₁))‖ ^ 2 / D ≤
      (2 * ‖C₁ - C₀‖ ^ 2 +
        2 * ‖(C₀ - X₀) + -(C₁ - X₁)‖ ^ 2) / D :=
      div_le_div_of_nonneg_right
        (norm_add_sq_le_two (C₁ - C₀) ((C₀ - X₀) + -(C₁ - X₁)))
        hD.le
    _ ≤ (2 * ‖C₁ - C₀‖ ^ 2 +
        2 * (2 * ‖C₀ - X₀‖ ^ 2 + 2 * ‖C₁ - X₁‖ ^ 2)) / D := by
      apply div_le_div_of_nonneg_right _ hD.le
      gcongr
      simpa only [norm_neg] using
        norm_add_sq_le_two (C₀ - X₀) (-(C₁ - X₁))
    _ = 2 * (‖C₁ - C₀‖ ^ 2 / D) +
        4 * (‖C₀ - X₀‖ ^ 2 / D) +
        4 * (‖C₁ - X₁‖ ^ 2 / D) := by ring

/-- Exact displacement coefficients evaluate to the difference of successive
exact graph-scale averages. -/
theorem exact_displacement_eq
    (A : SoficApproximation (K × J)) (n : ℕ)
    (c : Equiv.Perm (A.model n)) (S : Finset K) (k : ℕ) :
    KunThomCorrelation.finiteAveragingDisplacementNormSq A n c S k =
      ‖finiteFinsuppCombination (pairModel (A.model n)) (pairMap A n)
          (permutationGraph (A.model n) c) (averagingCoefficients S (k + 1)) -
        finiteFinsuppCombination (pairModel (A.model n)) (pairMap A n)
          (permutationGraph (A.model n) c) (averagingCoefficients S k)‖ ^ 2 /
          Fintype.card (A.model n) := by
  rw [KunThomCorrelation.finiteAveragingDisplacementNormSq,
    KunThomCorrelation.scaledCombinationNormSq]
  simp only [KunThomCorrelation.graphVector, id_eq]
  change ‖∑ x ∈ (averagingDisplacementCoefficients S k).support,
      (averagingDisplacementCoefficients S k) x •
        permutationOperator (pairMap A n x)
          (centeredIndicator (permutationGraph (A.model n) c))‖ ^ 2 /
      Fintype.card (A.model n) = _
  rw [← finiteFinsuppCombination_eq_sum,
    averagingDisplacementCoefficients, map_sub]

/-- Genuine consecutive diagonal Markov displacement at graph scale. -/
noncomputable def finiteModelAveragingDisplacementNormSq
    (A : SoficApproximation (K × J)) (n : ℕ)
    (c : Equiv.Perm (A.model n)) (S : Finset K) (k : ℕ) : ℝ :=
  ‖finiteModelAverageIterate A n c S (k + 1) -
      finiteModelAverageIterate A n c S k‖ ^ 2 /
    Fintype.card (A.model n)

/-- Genuine diagonal Markov displacements inherit the Kazhdan contraction. -/
theorem finiteModelAveragingDisplacementNormSq_eventually_lt
    {Q : Finset K} {ε : ℝ} (hQ : IsKazhdanPair.{0, 0} K Q ε)
    (S : Finset K) (hQS : Q ⊆ S) (hone : 1 ∈ S) (hεone : ε ≤ 1)
    (A : SoficApproximation (K × J)) (k : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ c : Equiv.Perm (A.model n),
      finiteModelAveragingDisplacementNormSq A n c S k <
        4 * (1 - ε ^ 2 / (4 * S.card)) ^ (2 * k) *
          finiteModelAveragingDisplacementNormSq A n c S 0 + δ := by
  classical
  let F : ℝ := (1 - ε ^ 2 / (4 * S.card)) ^ (2 * k)
  have hScard : (0 : ℝ) < S.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, hone⟩
  have hεsq : ε ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg ε, hQ.1, hεone]
  have hden : (0 : ℝ) < 4 * S.card := mul_pos (by norm_num) hScard
  have hdenOne : (1 : ℝ) ≤ 4 * S.card := by
    have : (1 : ℝ) ≤ S.card := by
      exact_mod_cast Finset.card_pos.mpr ⟨1, hone⟩
    nlinarith
  have hfrac : ε ^ 2 / (4 * S.card) ≤ 1 := by
    rw [div_le_one hden]
    exact hεsq.trans hdenOne
  have hF : 0 ≤ F := pow_nonneg (sub_nonneg.mpr hfrac) _
  let η : ℝ := δ / (16 * F + 11)
  have hdenη : 0 < 16 * F + 11 := by positivity
  have hη : 0 < η := div_pos hδ hdenη
  have hbudget : (16 * F + 10) * η < δ := by
    dsimp [η]
    rw [show (16 * F + 10) * (δ / (16 * F + 11)) =
      ((16 * F + 10) * δ) / (16 * F + 11) by ring,
      div_lt_iff₀ hdenη]
    nlinarith
  obtain ⟨Nexact, hNexact⟩ :=
    KunThomCorrelation.finiteAveragingDisplacementNormSq_eventually_lt
      hQ S hQS hone hεone A k η hη
  obtain ⟨Nk, hNk⟩ :=
    finiteAveragingIterate_hilbert_error_eventually A S ⟨1, hone⟩ k η hη
  obtain ⟨Nk1, hNk1⟩ :=
    finiteAveragingIterate_hilbert_error_eventually A S ⟨1, hone⟩ (k + 1) η hη
  obtain ⟨N0, hN0⟩ :=
    finiteAveragingIterate_hilbert_error_eventually A S ⟨1, hone⟩ 0 η hη
  obtain ⟨N1, hN1⟩ :=
    finiteAveragingIterate_hilbert_error_eventually A S ⟨1, hone⟩ 1 η hη
  obtain ⟨Ncard, hNcard⟩ := A.card_tendsToInfinity 1
  let N := max Nexact (max Nk (max Nk1 (max N0 (max N1 Ncard))))
  refine ⟨N, fun n hn c ↦ ?_⟩
  have hnexact : Nexact ≤ n := by dsimp [N] at hn; omega
  have hnk : Nk ≤ n := by dsimp [N] at hn; omega
  have hnk1 : Nk1 ≤ n := by dsimp [N] at hn; omega
  have hn0 : N0 ≤ n := by dsimp [N] at hn; omega
  have hn1 : N1 ≤ n := by dsimp [N] at hn; omega
  have hncard : Ncard ≤ n := by dsimp [N] at hn; omega
  have hcard : (0 : ℝ) < Fintype.card (A.model n) := by
    have := hNcard n hncard
    positivity
  let C : ℕ → EuclideanSpace ℝ (pairModel (A.model n)) := fun t ↦
    finiteFinsuppCombination (pairModel (A.model n)) (pairMap A n)
      (permutationGraph (A.model n) c) (averagingCoefficients S t)
  let X : ℕ → EuclideanSpace ℝ (pairModel (A.model n)) := fun t ↦
    finiteModelAverageIterate A n c S t
  have hCk : ‖C k - X k‖ ^ 2 / Fintype.card (A.model n) < η := hNk n hnk c
  have hCk1 : ‖C (k + 1) - X (k + 1)‖ ^ 2 /
      Fintype.card (A.model n) < η := hNk1 n hnk1 c
  have hC0 : ‖C 0 - X 0‖ ^ 2 / Fintype.card (A.model n) < η := hN0 n hn0 c
  have hC1 : ‖C 1 - X 1‖ ^ 2 / Fintype.card (A.model n) < η := hN1 n hn1 c
  have hexact := hNexact n hnexact c
  rw [exact_displacement_eq, exact_displacement_eq] at hexact
  change ‖C (k + 1) - C k‖ ^ 2 / Fintype.card (A.model n) <
      F * (‖C 1 - C 0‖ ^ 2 / Fintype.card (A.model n)) + η at hexact
  have hkTransfer := displacement_sq_div_scale_le_of_close
    (Fintype.card (A.model n) : ℝ) hcard (C k) (C (k + 1)) (X k) (X (k + 1))
  have h0Transfer := displacement_sq_div_scale_le_of_close
    (Fintype.card (A.model n) : ℝ) hcard (X 0) (X 1) (C 0) (C 1)
  change finiteModelAveragingDisplacementNormSq A n c S k <
    4 * F * finiteModelAveragingDisplacementNormSq A n c S 0 + δ
  change ‖X (k + 1) - X k‖ ^ 2 / Fintype.card (A.model n) <
    4 * F * (‖X 1 - X 0‖ ^ 2 / Fintype.card (A.model n)) + δ
  change ‖C 1 - C 0‖ ^ 2 / Fintype.card (A.model n) ≤
    2 * (‖X 1 - X 0‖ ^ 2 / Fintype.card (A.model n)) +
    4 * (‖X 0 - C 0‖ ^ 2 / Fintype.card (A.model n)) +
    4 * (‖X 1 - C 1‖ ^ 2 / Fintype.card (A.model n)) at h0Transfer
  rw [norm_sub_rev (X 0) (C 0), norm_sub_rev (X 1) (C 1)] at h0Transfer
  have h0scaled := mul_le_mul_of_nonneg_left h0Transfer
    (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hF)
  nlinarith

end KunThomFiniteMarkov
end NonsoficGroupsExist
