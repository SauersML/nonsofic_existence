import NonsoficGroupsExist.KazhdanGNS

/-!
# Genuine finite Markov iterates

This module transfers the exact group-word estimates from the GNS compactness
argument to the Markov operators actually defined by a sofic approximation.
It is separate from the GNS construction so that the expensive foundational
module remains cached while the finite transfer is developed.
-/

namespace NonsoficGroupsExist
namespace KazhdanGNS

open KazhdanFiniteModel
open scoped InnerProductSpace

universe u

variable {G : Type u} [Group G]

/-- The permutation assigned to the identity acts negligibly on every
centered indicator, uniformly over the subset. -/
theorem sofic_one_hilbert_error_eventually
    (A : SoficApproximation G) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ U : Finset (A.model n),
      ‖permutationOperator (A.map n 1) (centeredIndicator U) -
          centeredIndicator U‖ ^ 2 / Fintype.card (A.model n) < δ := by
  obtain ⟨Nerr, hNerr⟩ := A.map_one_close (δ / 2) (half_pos hδ)
  obtain ⟨Ncard, hNcard⟩ := A.card_tendsToInfinity 1
  refine ⟨max Nerr Ncard, fun n hn U ↦ ?_⟩
  have hnerr : Nerr ≤ n := (le_max_left _ _).trans hn
  have hncard : Ncard ≤ n := (le_max_right _ _).trans hn
  have hcard : 0 < Fintype.card (A.model n) := by
    have := hNcard n hncard
    omega
  letI : Nonempty (A.model n) := Fintype.card_pos_iff.mp hcard
  have hbound :=
    normalized_norm_permutationOperators_centeredIndicator_sub_sq_le
      (A.map n 1) 1 U
  rw [permutationOperator_one] at hbound
  exact hbound.trans_lt (by linarith [hNerr n hnerr])

/-- The actual `k`-step Markov iterate in a finite sofic model, started at the
centered indicator itself. -/
noncomputable def finiteModelAverageIterate
    (A : SoficApproximation G) (n : ℕ) (U : Finset (A.model n))
    (S : Finset G) (k : ℕ) : EuclideanSpace ℝ (A.model n) :=
  ((finiteModelAverage (A.model n) (A.map n) S)^[k])
    (centeredIndicator U)

/-- Successor time for the actual finite-model Markov iterate. -/
theorem finiteModelAverageIterate_succ
    (A : SoficApproximation G) (n : ℕ) (U : Finset (A.model n))
    (S : Finset G) (k : ℕ) :
    finiteModelAverageIterate A n U S (k + 1) =
      finiteModelAverage (A.model n) (A.map n) S
        (finiteModelAverageIterate A n U S k) := by
  rw [finiteModelAverageIterate, finiteModelAverageIterate,
    Function.iterate_succ_apply']

/-- At every fixed time, the exact group-word vector is uniformly close to
the genuine finite-model Markov iterate. -/
theorem finiteAveragingIterate_hilbert_error_eventually
    (A : SoficApproximation G) (S : Finset G) (hS : S.Nonempty)
    (k : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ U : Finset (A.model n),
      ‖finiteFinsuppCombination (A.model n) (A.map n) U
            (averagingCoefficients S k) -
          finiteModelAverageIterate A n U S k‖ ^ 2 /
        Fintype.card (A.model n) < δ := by
  induction k generalizing δ with
  | zero =>
      obtain ⟨N, hN⟩ := sofic_one_hilbert_error_eventually A δ hδ
      refine ⟨N, fun n hn U ↦ ?_⟩
      simpa [finiteModelAverageIterate, averagingCoefficients,
        finiteFinsuppCombination] using hN n hn U
  | succ k ih =>
      let η := δ / 4
      have hη : 0 < η := by dsimp [η]; linarith
      obtain ⟨Nstep, hNstep⟩ :=
        finiteAveragingStep_hilbert_error_eventually A S hS k η hη
      obtain ⟨Nprev, hNprev⟩ := ih η hη
      obtain ⟨Ncard, hNcard⟩ := A.card_tendsToInfinity 1
      refine ⟨max Nstep (max Nprev Ncard), fun n hn U ↦ ?_⟩
      have hnstep : Nstep ≤ n := by omega
      have hnprev : Nprev ≤ n := by omega
      have hncard : Ncard ≤ n := by omega
      have hcardNat : 0 < Fintype.card (A.model n) :=
        Nat.zero_lt_of_lt (hNcard n hncard)
      have hcard : (0 : ℝ) < Fintype.card (A.model n) := by
        exact_mod_cast hcardNat
      let Ck := finiteFinsuppCombination (A.model n) (A.map n) U
        (averagingCoefficients S k)
      let Cnext := finiteFinsuppCombination (A.model n) (A.map n) U
        (averagingCoefficients S (k + 1))
      let Xk := finiteModelAverageIterate A n U S k
      let step := Cnext -
        finiteModelAverage (A.model n) (A.map n) S Ck
      let previous := Ck - Xk
      have hstep : ‖step‖ ^ 2 / Fintype.card (A.model n) < η := by
        exact hNstep n hnstep U
      have hprevious :
          ‖previous‖ ^ 2 / Fintype.card (A.model n) < η := by
        exact hNprev n hnprev U
      have hdecomp :
          Cnext - finiteModelAverageIterate A n U S (k + 1) =
            step + finiteModelAverage (A.model n) (A.map n) S previous := by
        rw [finiteModelAverageIterate_succ, finiteModelAverage_sub]
        simp only [step]
        abel
      have hnorm :
          ‖Cnext - finiteModelAverageIterate A n U S (k + 1)‖ ≤
            ‖step‖ + ‖previous‖ := by
        rw [hdecomp]
        exact (norm_add_le _ _).trans
          (add_le_add_right
            (norm_finiteModelAverage_le (A.model n) (A.map n) S hS previous)
            ‖step‖)
      have hright : 0 ≤ ‖step‖ + ‖previous‖ :=
        add_nonneg (norm_nonneg _) (norm_nonneg _)
      have hsq := (sq_le_sq₀ (norm_nonneg _) hright).2 hnorm
      change ‖Cnext - finiteModelAverageIterate A n U S (k + 1)‖ ^ 2 /
          Fintype.card (A.model n) < δ
      calc
        ‖Cnext - finiteModelAverageIterate A n U S (k + 1)‖ ^ 2 /
            Fintype.card (A.model n) ≤
          (‖step‖ + ‖previous‖) ^ 2 /
            Fintype.card (A.model n) :=
          div_le_div_of_nonneg_right hsq hcard.le
        _ ≤ (2 * ‖step‖ ^ 2 + 2 * ‖previous‖ ^ 2) /
            Fintype.card (A.model n) := by
          apply div_le_div_of_nonneg_right _ hcard.le
          nlinarith [sq_nonneg (‖step‖ - ‖previous‖)]
        _ = 2 * (‖step‖ ^ 2 / Fintype.card (A.model n)) +
            2 * (‖previous‖ ^ 2 / Fintype.card (A.model n)) := by ring
        _ < δ := by
          dsimp [η] at hstep hprevious
          linarith

omit [Group G] in
/-- Squared norm of a sum, in the form used to transfer displacement bounds
between nearby finite-model trajectories. -/
theorem norm_add_sq_le_two
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (x y : E) : ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have hnorm := norm_add_le x y
  have hright : 0 ≤ ‖x‖ + ‖y‖ :=
    add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hsq := (sq_le_sq₀ (norm_nonneg _) hright).2 hnorm
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

omit [Group G] in
/-- Consecutive displacements of two nearby trajectories differ by at most
the two endpoint errors. -/
theorem normalized_displacement_le_of_close
    (M : FiniteModel) (hcard : (0 : ℝ) < Fintype.card M)
    (C₀ C₁ X₀ X₁ : EuclideanSpace ℝ M) :
    ‖X₁ - X₀‖ ^ 2 / Fintype.card M ≤
      2 * (‖C₁ - C₀‖ ^ 2 / Fintype.card M) +
      4 * (‖C₀ - X₀‖ ^ 2 / Fintype.card M) +
      4 * (‖C₁ - X₁‖ ^ 2 / Fintype.card M) := by
  have hdecomp : X₁ - X₀ =
      (C₁ - C₀) + ((C₀ - X₀) + -(C₁ - X₁)) := by abel
  rw [hdecomp]
  calc
    ‖(C₁ - C₀) + ((C₀ - X₀) + -(C₁ - X₁))‖ ^ 2 /
        Fintype.card M ≤
      (2 * ‖C₁ - C₀‖ ^ 2 +
        2 * ‖(C₀ - X₀) + -(C₁ - X₁)‖ ^ 2) /
          Fintype.card M :=
      div_le_div_of_nonneg_right
        (norm_add_sq_le_two (C₁ - C₀) ((C₀ - X₀) + -(C₁ - X₁))) hcard.le
    _ ≤ (2 * ‖C₁ - C₀‖ ^ 2 +
        2 * (2 * ‖C₀ - X₀‖ ^ 2 + 2 * ‖C₁ - X₁‖ ^ 2)) /
          Fintype.card M := by
      apply div_le_div_of_nonneg_right _ hcard.le
      gcongr
      simpa only [norm_neg] using
        norm_add_sq_le_two (C₀ - X₀) (-(C₁ - X₁))
    _ = 2 * (‖C₁ - C₀‖ ^ 2 / Fintype.card M) +
        4 * (‖C₀ - X₀‖ ^ 2 / Fintype.card M) +
        4 * (‖C₁ - X₁‖ ^ 2 / Fintype.card M) := by ring

/-- The exact-word displacement coefficients evaluate to the difference of
the two consecutive exact-word vectors in every finite model. -/
theorem finiteFinsuppCombination_averagingDisplacementCoefficients
    (A : SoficApproximation G) (n : ℕ) (U : Finset (A.model n))
    (S : Finset G) (k : ℕ) :
    finiteFinsuppCombination (A.model n) (A.map n) U
        (averagingDisplacementCoefficients S k) =
      finiteFinsuppCombination (A.model n) (A.map n) U
          (averagingCoefficients S (k + 1)) -
        finiteFinsuppCombination (A.model n) (A.map n) U
          (averagingCoefficients S k) := by
  simp [averagingDisplacementCoefficients]

/-- Normalized squared displacement between consecutive genuine finite-model
Markov iterates. -/
noncomputable def finiteModelAveragingDisplacementNormSq
    (A : SoficApproximation G) (n : ℕ) (U : Finset (A.model n))
    (S : Finset G) (k : ℕ) : ℝ :=
  ‖finiteModelAverageIterate A n U S (k + 1) -
      finiteModelAverageIterate A n U S k‖ ^ 2 /
    Fintype.card (A.model n)

/-- At time zero this is exactly the one-step displacement of the centered
indicator under the genuine finite-model Markov operator. -/
theorem finiteModelAveragingDisplacementNormSq_zero
    (A : SoficApproximation G) (n : ℕ) (U : Finset (A.model n))
    (S : Finset G) :
    finiteModelAveragingDisplacementNormSq A n U S 0 =
      ‖finiteModelAverage (A.model n) (A.map n) S (centeredIndicator U) -
          centeredIndicator U‖ ^ 2 / Fintype.card (A.model n) := by
  simp [finiteModelAveragingDisplacementNormSq,
    finiteModelAverageIterate]

/-- The genuine finite-model Markov displacements inherit the GNS
contraction.  The harmless factor `4` comes from transferring both endpoints
between the exact-word and actual trajectories. -/
theorem finiteModelAveragingDisplacementNormSq_eventually_lt
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, u} G Q ε)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S) (hεone : ε ≤ 1)
    (A : SoficApproximation G) (k : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ U : Finset (A.model n),
      finiteModelAveragingDisplacementNormSq A n U S k <
        4 * (1 - ε ^ 2 / (4 * S.card)) ^ (2 * k) *
          finiteModelAveragingDisplacementNormSq A n U S 0 + δ := by
  classical
  let F : ℝ := (1 - ε ^ 2 / (4 * S.card)) ^ (2 * k)
  have hScardNat : 0 < S.card := Finset.card_pos.mpr ⟨1, hone⟩
  have hScard : (0 : ℝ) < S.card := by exact_mod_cast hScardNat
  have hεsq : ε ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg ε, hQ.1, hεone]
  have hdenS : (0 : ℝ) < 4 * S.card := mul_pos (by norm_num) hScard
  have hdenOne : (1 : ℝ) ≤ 4 * S.card := by
    have : (1 : ℝ) ≤ S.card := by exact_mod_cast hScardNat
    nlinarith
  have hfrac : ε ^ 2 / (4 * S.card) ≤ 1 := by
    rw [div_le_one hdenS]
    exact hεsq.trans hdenOne
  have hbase : 0 ≤ 1 - ε ^ 2 / (4 * S.card) := by linarith
  have hF : 0 ≤ F := pow_nonneg hbase _
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
    finiteAveragingDisplacementNormSq_eventually_lt
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
  refine ⟨N, fun n hn U ↦ ?_⟩
  have hnexact : Nexact ≤ n := by dsimp [N] at hn; omega
  have hnk : Nk ≤ n := by dsimp [N] at hn; omega
  have hnk1 : Nk1 ≤ n := by dsimp [N] at hn; omega
  have hn0 : N0 ≤ n := by dsimp [N] at hn; omega
  have hn1 : N1 ≤ n := by dsimp [N] at hn; omega
  have hncard : Ncard ≤ n := by dsimp [N] at hn; omega
  have hcardNat : 0 < Fintype.card (A.model n) :=
    Nat.zero_lt_of_lt (hNcard n hncard)
  have hcard : (0 : ℝ) < Fintype.card (A.model n) := by
    exact_mod_cast hcardNat
  let C : ℕ → EuclideanSpace ℝ (A.model n) := fun t ↦
    finiteFinsuppCombination (A.model n) (A.map n) U
      (averagingCoefficients S t)
  let X : ℕ → EuclideanSpace ℝ (A.model n) := fun t ↦
    finiteModelAverageIterate A n U S t
  let e : ℕ → ℝ := fun t ↦ ‖C t - X t‖ ^ 2 / Fintype.card (A.model n)
  have hek : e k < η := hNk n hnk U
  have hek1 : e (k + 1) < η := hNk1 n hnk1 U
  have he0 : e 0 < η := hN0 n hn0 U
  have he1 : e 1 < η := hN1 n hn1 U
  have hexact (t : ℕ) :
      finiteAveragingDisplacementNormSq A n U S t =
        ‖C (t + 1) - C t‖ ^ 2 / Fintype.card (A.model n) := by
    rw [finiteAveragingDisplacementNormSq_eq_norm,
      finiteFinsuppCombination_averagingDisplacementCoefficients]
  have hmodelK :
      finiteModelAveragingDisplacementNormSq A n U S k ≤
        2 * finiteAveragingDisplacementNormSq A n U S k +
          4 * e k + 4 * e (k + 1) := by
    rw [finiteModelAveragingDisplacementNormSq, hexact]
    exact normalized_displacement_le_of_close
      (A.model n) hcard (C k) (C (k + 1)) (X k) (X (k + 1))
  have hExactK :
      finiteAveragingDisplacementNormSq A n U S k <
        F * finiteAveragingDisplacementNormSq A n U S 0 + η := by
    exact hNexact n hnexact U
  have hExact0 :
      finiteAveragingDisplacementNormSq A n U S 0 ≤
        2 * finiteModelAveragingDisplacementNormSq A n U S 0 +
          4 * e 0 + 4 * e 1 := by
    rw [hexact, finiteModelAveragingDisplacementNormSq]
    have h := normalized_displacement_le_of_close
      (A.model n) hcard (X 0) (X 1) (C 0) (C 1)
    rw [norm_sub_rev (X 0) (C 0), norm_sub_rev (X 1) (C 1)] at h
    exact h
  have h2F : 0 ≤ 2 * F := mul_nonneg (by norm_num) hF
  have hscaled := mul_le_mul_of_nonneg_left hExact0 h2F
  have hTwiceExactK := mul_lt_mul_of_pos_left hExactK (by norm_num : (0 : ℝ) < 2)
  have h8F : 0 ≤ 8 * F := mul_nonneg (by norm_num) hF
  have he0scaled := mul_le_mul_of_nonneg_left he0.le h8F
  have he1scaled := mul_le_mul_of_nonneg_left he1.le h8F
  change finiteModelAveragingDisplacementNormSq A n U S k <
      4 * F * finiteModelAveragingDisplacementNormSq A n U S 0 + δ
  have hintermediate :
      finiteModelAveragingDisplacementNormSq A n U S k <
        4 * F * finiteModelAveragingDisplacementNormSq A n U S 0 +
          (16 * F + 10) * η := by
    nlinarith only [hmodelK, hTwiceExactK, hscaled, hek, hek1,
      he0scaled, he1scaled]
  exact hintermediate.trans_le (by linarith only [hbudget])

/-- The basic Kazhdan averaging factor lies in `[0,1)`. -/
theorem kazhdanFactor_nonneg_lt_one
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, u} G Q ε)
    (S : Finset G) (hone : 1 ∈ S) (hεone : ε ≤ 1) :
    0 ≤ 1 - ε ^ 2 / (4 * S.card) ∧
      1 - ε ^ 2 / (4 * S.card) < 1 := by
  have hScardNat : 0 < S.card := Finset.card_pos.mpr ⟨1, hone⟩
  have hScard : (0 : ℝ) < S.card := by exact_mod_cast hScardNat
  have hden : (0 : ℝ) < 4 * S.card := mul_pos (by norm_num) hScard
  have hfracPos : 0 < ε ^ 2 / (4 * S.card) :=
    div_pos (sq_pos_of_pos hQ.1) hden
  let c : ℝ := 1 - ε ^ 2 / (4 * S.card)
  have hcNonneg : 0 ≤ c := by
    have hεsq : ε ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg ε, hQ.1, hεone]
    have hdenOne : (1 : ℝ) ≤ 4 * S.card := by
      have : (1 : ℝ) ≤ S.card := by exact_mod_cast hScardNat
      nlinarith
    have hfrac : ε ^ 2 / (4 * S.card) ≤ 1 := by
      rw [div_le_one hden]
      exact hεsq.trans hdenOne
    dsimp [c]
    linarith
  have hcLt : c < 1 := by dsimp [c]; linarith
  exact ⟨hcNonneg, hcLt⟩

/-- A Kazhdan contraction factor becomes smaller than any prescribed positive
constant after a fixed number of squared averaging steps. -/
theorem exists_four_mul_kazhdanFactor_pow_lt
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, u} G Q ε)
    (S : Finset G) (hone : 1 ∈ S) (hεone : ε ≤ 1)
    (η : ℝ) (hη : 0 < η) :
    ∃ k : ℕ,
      0 ≤ 4 * (1 - ε ^ 2 / (4 * S.card)) ^ (2 * k) ∧
      4 * (1 - ε ^ 2 / (4 * S.card)) ^ (2 * k) < η := by
  obtain ⟨hcNonneg, hcLt⟩ :=
    kazhdanFactor_nonneg_lt_one hQ S hone hεone
  let c : ℝ := 1 - ε ^ 2 / (4 * S.card)
  let r : ℝ := min 1 (Real.sqrt (η / 4))
  have hηdiv : 0 < η / 4 := div_pos hη (by norm_num)
  have hr : 0 < r := lt_min (by norm_num) (Real.sqrt_pos.2 hηdiv)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hr hcLt
  refine ⟨k, mul_nonneg (by norm_num) (pow_nonneg hcNonneg _), ?_⟩
  have hpow : c ^ (2 * k) = (c ^ k) ^ 2 := by
    rw [show 2 * k = k * 2 by omega, pow_mul]
  have hksqrt : c ^ k < Real.sqrt (η / 4) :=
    hk.trans_le (min_le_right _ _)
  have hkSq : (c ^ k) ^ 2 < (Real.sqrt (η / 4)) ^ 2 :=
    (sq_lt_sq₀ (pow_nonneg hcNonneg _) (Real.sqrt_nonneg _)).2 hksqrt
  have hsqrtSq : (Real.sqrt (η / 4)) ^ 2 = η / 4 :=
    Real.sq_sqrt hηdiv.le
  rw [hpow]
  nlinarith

/-- A Kazhdan contraction factor becomes smaller than `1/4` after a fixed
number of squared averaging steps. -/
theorem exists_four_mul_kazhdanFactor_pow_lt_one
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, u} G Q ε)
    (S : Finset G) (hone : 1 ∈ S) (hεone : ε ≤ 1) :
    ∃ k : ℕ,
      0 ≤ 4 * (1 - ε ^ 2 / (4 * S.card)) ^ (2 * k) ∧
      4 * (1 - ε ^ 2 / (4 * S.card)) ^ (2 * k) < 1 := by
  exact exists_four_mul_kazhdanFactor_pow_lt
    hQ S hone hεone 1 (by norm_num)

/-- Property `(T)` supplies a contraction coefficient below any prescribed
positive target. -/
theorem finiteModel_markovContraction_lt
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, u} G Q ε)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S) (hεone : ε ≤ 1)
    (A : SoficApproximation G) (θ : ℝ) (hθ : 0 < θ) :
    ∃ k : ℕ, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < θ ∧
      ∀ δ : ℝ, 0 < δ →
        ∃ N : ℕ, ∀ n ≥ N, ∀ U : Finset (A.model n),
          finiteModelAveragingDisplacementNormSq A n U S k <
            ρ * finiteModelAveragingDisplacementNormSq A n U S 0 + δ := by
  obtain ⟨k, hk0, hk1⟩ :=
    exists_four_mul_kazhdanFactor_pow_lt hQ S hone hεone θ hθ
  let ρ : ℝ := 4 * (1 - ε ^ 2 / (4 * S.card)) ^ (2 * k)
  refine ⟨k, ρ, hk0, hk1, fun δ hδ ↦ ?_⟩
  simpa [ρ, mul_assoc] using
    finiteModelAveragingDisplacementNormSq_eventually_lt
      hQ S hQS hone hεone A k δ hδ

/-- Property `(T)` therefore supplies a fixed strict contraction of genuine
finite-model Markov displacements, uniformly over every centered indicator
and with an arbitrarily small additive error. -/
theorem finiteModel_strictMarkovContraction
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, u} G Q ε)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S) (hεone : ε ≤ 1)
    (A : SoficApproximation G) :
    ∃ k : ℕ, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ δ : ℝ, 0 < δ →
        ∃ N : ℕ, ∀ n ≥ N, ∀ U : Finset (A.model n),
          finiteModelAveragingDisplacementNormSq A n U S k <
            ρ * finiteModelAveragingDisplacementNormSq A n U S 0 + δ := by
  exact finiteModel_markovContraction_lt
    hQ S hQS hone hεone A 1 (by norm_num)

/-- Unsquared Markov contraction with coefficient below any prescribed
positive target. -/
theorem finiteModel_markovNormContraction_lt
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, u} G Q ε)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S) (hεone : ε ≤ 1)
    (A : SoficApproximation G) (θ : ℝ) (hθ : 0 < θ) :
    ∃ k : ℕ, ∃ c : ℝ, 0 ≤ c ∧ c < θ ∧
      ∀ α : ℝ, 0 < α →
        ∃ N : ℕ, ∀ n ≥ N, ∀ U : Finset (A.model n),
          ‖finiteModelAverageIterate A n U S (k + 1) -
              finiteModelAverageIterate A n U S k‖ <
            c * ‖finiteModelAverageIterate A n U S 1 -
              finiteModelAverageIterate A n U S 0‖ +
            α * Real.sqrt (Fintype.card (A.model n) : ℝ) := by
  obtain ⟨k, ρ, hρ0, hρ1, hcontract⟩ :=
    finiteModel_markovContraction_lt
      hQ S hQS hone hεone A (θ ^ 2) (sq_pos_of_pos hθ)
  let c := Real.sqrt ρ
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hcsq : c ^ 2 = ρ := Real.sq_sqrt hρ0
  have hc1 : c < θ := by
    apply (sq_lt_sq₀ hc0 hθ.le).mp
    simpa [hcsq] using hρ1
  refine ⟨k, c, hc0, hc1, fun α hα ↦ ?_⟩
  obtain ⟨Nerr, hNerr⟩ := hcontract (α ^ 2) (sq_pos_of_pos hα)
  obtain ⟨Ncard, hNcard⟩ := A.card_tendsToInfinity 1
  refine ⟨max Nerr Ncard, fun n hn U ↦ ?_⟩
  have hnerr : Nerr ≤ n := (le_max_left _ _).trans hn
  have hncard : Ncard ≤ n := (le_max_right _ _).trans hn
  have hcardNat : 0 < Fintype.card (A.model n) :=
    Nat.zero_lt_of_lt (hNcard n hncard)
  have hcard : (0 : ℝ) < Fintype.card (A.model n) := by
    exact_mod_cast hcardNat
  let a := ‖finiteModelAverageIterate A n U S (k + 1) -
    finiteModelAverageIterate A n U S k‖
  let b := ‖finiteModelAverageIterate A n U S 1 -
    finiteModelAverageIterate A n U S 0‖
  have hsquared := hNerr n hnerr U
  change a ^ 2 / Fintype.card (A.model n) <
      ρ * (b ^ 2 / Fintype.card (A.model n)) + α ^ 2 at hsquared
  have hsquared' : a ^ 2 <
      ρ * b ^ 2 + α ^ 2 * Fintype.card (A.model n) := by
    have := (div_lt_iff₀ hcard).mp hsquared
    field_simp at this
    nlinarith
  have hcardSqrt : Real.sqrt (Fintype.card (A.model n) : ℝ) ^ 2 =
      Fintype.card (A.model n) := Real.sq_sqrt hcard.le
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have hsqrtCard0 : 0 ≤ Real.sqrt (Fintype.card (A.model n) : ℝ) :=
    Real.sqrt_nonneg _
  change a < c * b + α * Real.sqrt (Fintype.card (A.model n) : ℝ)
  nlinarith [mul_nonneg hc0 hb0, mul_nonneg hα.le hsqrtCard0,
    sq_nonneg (c * b + α * Real.sqrt (Fintype.card (A.model n) : ℝ))]

/-- Unsquared form of the strict Markov contraction, matching the analytic
hypothesis in Kun's finite rounding theorem. -/
theorem finiteModel_strictMarkovNormContraction
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, u} G Q ε)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S) (hεone : ε ≤ 1)
    (A : SoficApproximation G) :
    ∃ k : ℕ, ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧
      ∀ α : ℝ, 0 < α →
        ∃ N : ℕ, ∀ n ≥ N, ∀ U : Finset (A.model n),
          ‖finiteModelAverageIterate A n U S (k + 1) -
              finiteModelAverageIterate A n U S k‖ <
            c * ‖finiteModelAverageIterate A n U S 1 -
              finiteModelAverageIterate A n U S 0‖ +
            α * Real.sqrt (Fintype.card (A.model n) : ℝ) := by
  exact finiteModel_markovNormContraction_lt
    hQ S hQS hone hεone A 1 (by norm_num)

end KazhdanGNS
end NonsoficGroupsExist
