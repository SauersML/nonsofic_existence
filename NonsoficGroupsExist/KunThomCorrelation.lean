import NonsoficGroupsExist.KunThomDiagonal
import NonsoficGroupsExist.SoficTransfer
import NonsoficGroupsExist.KazhdanGNS

/-!
# Correlations at the Hilbert--Schmidt scale

A permutation graph in `Y × Y` has `|Y|` points, so Kun--Thom correlations
are normalized by `|Y|`.  The localized diagonal estimate makes approximate
multiplication vanish at exactly this scale.
-/

namespace NonsoficGroupsExist
namespace KunThomCorrelation

open KazhdanFiniteModel
open KazhdanImprovement
open KunThomDiagonal

variable {Y : FiniteModel}

/-- The centered characteristic vector of a permutation graph. -/
noncomputable def graphVector (c : Equiv.Perm Y) :
    EuclideanSpace ℝ (Y × Y) :=
  centeredIndicator (permutationGraph Y c)

theorem norm_graphVector_sq_le (c : Equiv.Perm Y) :
    ‖graphVector c‖ ^ 2 ≤ Fintype.card Y := by
  by_cases hcardZero : Fintype.card Y = 0
  · haveI : IsEmpty Y := Fintype.card_eq_zero_iff.mp hcardZero
    have hzero : graphVector c = 0 := Subsingleton.elim _ _
    simp [hzero]
  letI : Nonempty Y :=
    Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hcardZero)
  rw [graphVector, norm_centeredIndicator_sq, card_permutationGraph]
  have hcard : (0 : ℝ) < Fintype.card Y := by
    exact_mod_cast Nat.pos_of_ne_zero hcardZero
  have hdensity : (0 : ℝ) ≤
      (Fintype.card Y : ℝ) / Fintype.card (Y × Y) := by positivity
  nlinarith

/-- Matrix coefficient of a diagonal permutation, normalized by `|Y|`. -/
noncomputable def scaledPermutationCorrelation (c p : Equiv.Perm Y) : ℝ :=
  inner ℝ (graphVector c)
      (permutationOperator (diagonalPerm p) (graphVector c)) /
    Fintype.card Y

/-- Coefficient assigned to a group element by an approximate action. -/
noncomputable def scaledCorrelation {G : Type*}
    (τ : G → Equiv.Perm Y) (c : Equiv.Perm Y) (g : G) : ℝ :=
  scaledPermutationCorrelation c (τ g)

/-- Gram coefficient between two diagonal translates of a permutation graph. -/
noncomputable def scaledGramCorrelation {G : Type*}
    (τ : G → Equiv.Perm Y) (c : Equiv.Perm Y) (g h : G) : ℝ :=
  inner ℝ
      (permutationOperator (diagonalPerm (τ g)) (graphVector c))
      (permutationOperator (diagonalPerm (τ h)) (graphVector c)) /
    Fintype.card Y

/-- Gram coefficients are coefficients of the relative assigned
permutation, without assuming that the assignment is multiplicative. -/
theorem scaledGramCorrelation_eq_relative {G : Type*}
    (τ : G → Equiv.Perm Y) (c : Equiv.Perm Y) (g h : G) :
    scaledGramCorrelation τ c g h =
      inner ℝ (graphVector c)
          (permutationOperator ((diagonalPerm (τ g))⁻¹ *
            diagonalPerm (τ h)) (graphVector c)) /
        Fintype.card Y := by
  unfold scaledGramCorrelation
  let x := graphVector c
  have hop :
      permutationOperator (diagonalPerm (τ g))
          (permutationOperator ((diagonalPerm (τ g))⁻¹ *
            diagonalPerm (τ h)) x) =
        permutationOperator (diagonalPerm (τ h)) x := by
    have hcomp := congrArg
      (fun e : EuclideanSpace ℝ (Y × Y) ≃ₗᵢ[ℝ]
          EuclideanSpace ℝ (Y × Y) ↦ e x)
      (permutationOperator_mul (diagonalPerm (τ g))
        ((diagonalPerm (τ g))⁻¹ * diagonalPerm (τ h))).symm
    simpa using hcomp
  have hinner :
      inner ℝ (permutationOperator (diagonalPerm (τ g)) x)
          (permutationOperator (diagonalPerm (τ h)) x) =
        inner ℝ x (permutationOperator ((diagonalPerm (τ g))⁻¹ *
          diagonalPerm (τ h)) x) := by
    rw [← hop]
    exact (permutationOperator (diagonalPerm (τ g))).inner_map_map _ _
  exact congrArg (fun z : ℝ ↦ z / Fintype.card Y) hinner

theorem scaledGramCorrelation_comm {G : Type*}
    (τ : G → Equiv.Perm Y) (c : Equiv.Perm Y) (g h : G) :
    scaledGramCorrelation τ c g h = scaledGramCorrelation τ c h g := by
  unfold scaledGramCorrelation
  rw [real_inner_comm]

/-- Squared norm of a finite combination of diagonal translates, normalized
at the permutation-graph scale. -/
noncomputable def scaledCombinationNormSq {G I : Type*}
    (F : Finset I) (a : I → ℝ) (τ : G → Equiv.Perm Y)
    (c : Equiv.Perm Y) (w : I → G) : ℝ :=
  ‖∑ i ∈ F, a i •
      permutationOperator (diagonalPerm (τ (w i))) (graphVector c)‖ ^ 2 /
    Fintype.card Y

theorem scaledCombinationNormSq_eq_gram {G I : Type*}
    (F : Finset I) (a : I → ℝ) (τ : G → Equiv.Perm Y)
    (c : Equiv.Perm Y) (w : I → G) :
    scaledCombinationNormSq F a τ c w =
      ∑ i ∈ F, ∑ j ∈ F,
        a i * a j * scaledGramCorrelation τ c (w i) (w j) := by
  classical
  unfold scaledCombinationNormSq scaledGramCorrelation
  rw [← real_inner_self_eq_norm_sq]
  simp_rw [sum_inner, inner_sum, real_inner_smul_left,
    real_inner_smul_right]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem scaledGramCorrelation_quadratic_nonneg {G I : Type*}
    (F : Finset I) (a : I → ℝ) (τ : G → Equiv.Perm Y)
    (c : Equiv.Perm Y) (w : I → G) :
    0 ≤ ∑ i ∈ F, ∑ j ∈ F,
      a i * a j * scaledGramCorrelation τ c (w i) (w j) := by
  rw [← scaledCombinationNormSq_eq_gram]
  exact div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

/-- Every scaled coefficient lies in `[-1,1]`. -/
theorem abs_scaledPermutationCorrelation_le_one (c p : Equiv.Perm Y) :
    |scaledPermutationCorrelation c p| ≤ 1 := by
  by_cases hcardZero : Fintype.card Y = 0
  · simp [scaledPermutationCorrelation, hcardZero]
  have hcard : (0 : ℝ) < Fintype.card Y := by
    exact_mod_cast Nat.pos_of_ne_zero hcardZero
  have hinner := abs_real_inner_le_norm (graphVector c)
    (permutationOperator (diagonalPerm p) (graphVector c))
  rw [(permutationOperator (diagonalPerm p)).norm_map] at hinner
  rw [scaledPermutationCorrelation, abs_div, abs_of_pos hcard]
  calc
    |inner ℝ (graphVector c)
        (permutationOperator (diagonalPerm p) (graphVector c))| /
          Fintype.card Y ≤
      (‖graphVector c‖ * ‖graphVector c‖) / Fintype.card Y :=
        div_le_div_of_nonneg_right hinner hcard.le
    _ = ‖graphVector c‖ ^ 2 / Fintype.card Y := by ring
    _ ≤ 1 := (div_le_one hcard).2 (norm_graphVector_sq_le c)

theorem abs_scaledGramCorrelation_le_one {G : Type*}
    (τ : G → Equiv.Perm Y) (c : Equiv.Perm Y) (g h : G) :
    |scaledGramCorrelation τ c g h| ≤ 1 := by
  by_cases hcardZero : Fintype.card Y = 0
  · simp [scaledGramCorrelation, hcardZero]
  have hcard : (0 : ℝ) < Fintype.card Y := by
    exact_mod_cast Nat.pos_of_ne_zero hcardZero
  have hinner := abs_real_inner_le_norm
    (permutationOperator (diagonalPerm (τ g)) (graphVector c))
    (permutationOperator (diagonalPerm (τ h)) (graphVector c))
  rw [(permutationOperator (diagonalPerm (τ g))).norm_map,
    (permutationOperator (diagonalPerm (τ h))).norm_map] at hinner
  rw [scaledGramCorrelation, abs_div, abs_of_pos hcard]
  calc
    |inner ℝ (permutationOperator (diagonalPerm (τ g)) (graphVector c))
        (permutationOperator (diagonalPerm (τ h)) (graphVector c))| /
          Fintype.card Y ≤
      (‖graphVector c‖ * ‖graphVector c‖) / Fintype.card Y :=
        div_le_div_of_nonneg_right hinner hcard.le
    _ = ‖graphVector c‖ ^ 2 / Fintype.card Y := by ring
    _ ≤ 1 := (div_le_one hcard).2 (norm_graphVector_sq_le c)

/-- Localized diagonal replacement controls scaled correlation error. -/
theorem abs_scaledPermutationCorrelation_sub_sq_le [Nonempty Y]
    (c p q : Equiv.Perm Y) :
    |scaledPermutationCorrelation c p -
        scaledPermutationCorrelation c q| ^ 2 ≤
      4 * hammingDistance Y p q := by
  let x := graphVector c
  let d := permutationOperator (diagonalPerm p) x -
    permutationOperator (diagonalPerm q) x
  have hcard : (0 : ℝ) < Fintype.card Y := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Y)
  have hinner : |inner ℝ x d| ≤ ‖x‖ * ‖d‖ :=
    abs_real_inner_le_norm x d
  have hinnerSq : |inner ℝ x d| ^ 2 ≤ (‖x‖ * ‖d‖) ^ 2 := by
    have hright : 0 ≤ ‖x‖ * ‖d‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    nlinarith [abs_nonneg (inner ℝ x d)]
  have hx : ‖x‖ ^ 2 / Fintype.card Y ≤ 1 := by
    exact (div_le_one hcard).2 (norm_graphVector_sq_le c)
  have hdRaw := norm_diagonal_centeredIndicator_sub_sq_le c p q
  have hd : ‖d‖ ^ 2 / Fintype.card Y ≤
      4 * hammingDistance Y p q := by
    have hdisagree : ((permutationDisagreement p q).card : ℝ) /
        Fintype.card Y = hammingDistance Y p q := by
      rw [hammingDistance_eq_permutationDisagreement_ratio]
    calc
      ‖d‖ ^ 2 / Fintype.card Y ≤
          (4 * ((permutationDisagreement p q).card : ℝ)) /
            Fintype.card Y := by
        apply div_le_div_of_nonneg_right
        · simpa [d, x, graphVector] using hdRaw
        · exact hcard.le
      _ = 4 * hammingDistance Y p q := by rw [← hdisagree]; ring
  have hquot : |inner ℝ x d| ^ 2 / (Fintype.card Y : ℝ) ^ 2 ≤
      (‖x‖ ^ 2 / Fintype.card Y) *
        (‖d‖ ^ 2 / Fintype.card Y) := by
    calc
      |inner ℝ x d| ^ 2 / (Fintype.card Y : ℝ) ^ 2 ≤
          (‖x‖ * ‖d‖) ^ 2 / (Fintype.card Y : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hinnerSq (sq_nonneg _)
      _ = (‖x‖ ^ 2 / Fintype.card Y) *
          (‖d‖ ^ 2 / Fintype.card Y) := by ring
  have hproduct : (‖x‖ ^ 2 / Fintype.card Y) *
      (‖d‖ ^ 2 / Fintype.card Y) ≤
        4 * hammingDistance Y p q := by
    calc
      (‖x‖ ^ 2 / Fintype.card Y) *
          (‖d‖ ^ 2 / Fintype.card Y) ≤
        1 * (‖d‖ ^ 2 / Fintype.card Y) := by
          exact mul_le_mul_of_nonneg_right hx
            (div_nonneg (sq_nonneg _) hcard.le)
      _ ≤ 1 * (4 * hammingDistance Y p q) :=
        mul_le_mul_of_nonneg_left hd zero_le_one
      _ = 4 * hammingDistance Y p q := one_mul _
  change
    |inner ℝ x (permutationOperator (diagonalPerm p) x) /
          Fintype.card Y -
        inner ℝ x (permutationOperator (diagonalPerm q) x) /
          Fintype.card Y| ^ 2 ≤ _
  rw [← sub_div, abs_div, abs_of_pos hcard, div_pow]
  have hrewrite :
      inner ℝ x (permutationOperator (diagonalPerm p) x) -
          inner ℝ x (permutationOperator (diagonalPerm q) x) =
        inner ℝ x d := by
    simp [d, inner_sub_right]
  rw [hrewrite]
  exact hquot.trans hproduct

variable {K J : Type} [Group K] [Group J]

/-- In a sofic approximation of `K × J`, the scaled relative coefficient
of any sequence of permutation graphs approaches its Gram coefficient. -/
theorem relativeCorrelation_approaches_gram_eventually
    (A : SoficApproximation (K × J))
    (c : ∀ n, Equiv.Perm (A.model n))
    (g h : K) (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n ≥ N,
      |scaledCorrelation (fun k ↦ A.map n (k, 1)) (c n) (g⁻¹ * h) -
        scaledGramCorrelation (fun k ↦ A.map n (k, 1)) (c n) g h| < η := by
  have htol : 0 < η ^ 2 / 4 := by positivity
  obtain ⟨Nclose, hNclose⟩ :=
    sofic_inv_mul_close_eventually A (g, (1 : J)) (h, 1)
      (η ^ 2 / 4) htol
  obtain ⟨Ncard, hNcard⟩ := A.card_tendsToInfinity 1
  refine ⟨max Nclose Ncard, fun n hn ↦ ?_⟩
  have hnclose : Nclose ≤ n := (le_max_left _ _).trans hn
  have hncard : Ncard ≤ n := (le_max_right _ _).trans hn
  have hcardNat : 0 < Fintype.card (A.model n) := by
    have := hNcard n hncard
    omega
  letI : Nonempty (A.model n) := Fintype.card_pos_iff.mp hcardNat
  let p := A.map n (g⁻¹ * h, (1 : J))
  let q := (A.map n (g, (1 : J)))⁻¹ * A.map n (h, 1)
  have hclose : hammingDistance (A.model n) p q < η ^ 2 / 4 := by
    simpa [p, q] using hNclose n hnclose
  have hsquare := abs_scaledPermutationCorrelation_sub_sq_le (c n) p q
  have habs : 0 ≤ |scaledPermutationCorrelation (c n) p -
      scaledPermutationCorrelation (c n) q| := abs_nonneg _
  have hlt : |scaledPermutationCorrelation (c n) p -
      scaledPermutationCorrelation (c n) q| ^ 2 < η ^ 2 := by
    nlinarith
  have hresult : |scaledPermutationCorrelation (c n) p -
      scaledPermutationCorrelation (c n) q| < η := by
    nlinarith [sq_nonneg
      (|scaledPermutationCorrelation (c n) p -
        scaledPermutationCorrelation (c n) q| - η)]
  have hgram :
      scaledGramCorrelation (fun k ↦ A.map n (k, (1 : J))) (c n) g h =
        scaledPermutationCorrelation (c n) q := by
    rw [scaledGramCorrelation_eq_relative, scaledPermutationCorrelation]
    simp only [q, diagonalPerm_mul, diagonalPerm_inv]
  rw [scaledCorrelation, hgram]
  simpa [p] using hresult

/-! ### The limiting positive-definite function -/

/-- Hyperreal scaled coefficient of a sequence of permutation graphs. -/
noncomputable def correlationHyperreal
    (A : SoficApproximation (K × J))
    (c : ∀ n, Equiv.Perm (A.model n)) (g : K) : Hyperreal :=
  Hyperreal.ofSeq fun n ↦
    scaledCorrelation (fun k ↦ A.map n (k, 1)) (c n) g

/-- Hyperreal Gram coefficient of the corresponding diagonal translates. -/
noncomputable def gramCorrelationHyperreal
    (A : SoficApproximation (K × J))
    (c : ∀ n, Equiv.Perm (A.model n)) (g h : K) : Hyperreal :=
  Hyperreal.ofSeq fun n ↦
    scaledGramCorrelation (fun k ↦ A.map n (k, 1)) (c n) g h

theorem correlationHyperreal_finite
    (A : SoficApproximation (K × J))
    (c : ∀ n, Equiv.Perm (A.model n)) (g : K) :
    0 ≤ ArchimedeanClass.mk (correlationHyperreal A c g) := by
  apply ArchimedeanClass.mk_nonneg_of_le_of_le_of_archimedean
    Hyperreal.coeRingHom (r := (-1 : ℝ)) (s := (1 : ℝ))
  · change Hyperreal.ofSeq (fun _ : ℕ ↦ (-1 : ℝ)) ≤
      Hyperreal.ofSeq (fun n ↦
        scaledCorrelation (fun k ↦ A.map n (k, 1)) (c n) g)
    rw [Hyperreal.ofSeq_le_ofSeq]
    exact Filter.Eventually.of_forall fun n ↦ by
      exact (abs_le.mp (abs_scaledPermutationCorrelation_le_one
        (c n) (A.map n (g, 1)))).1
  · change Hyperreal.ofSeq (fun n ↦
        scaledCorrelation (fun k ↦ A.map n (k, 1)) (c n) g) ≤
      Hyperreal.ofSeq (fun _ : ℕ ↦ (1 : ℝ))
    rw [Hyperreal.ofSeq_le_ofSeq]
    exact Filter.Eventually.of_forall fun n ↦ by
      exact (abs_le.mp (abs_scaledPermutationCorrelation_le_one
        (c n) (A.map n (g, 1)))).2

theorem gramCorrelationHyperreal_finite
    (A : SoficApproximation (K × J))
    (c : ∀ n, Equiv.Perm (A.model n)) (g h : K) :
    0 ≤ ArchimedeanClass.mk (gramCorrelationHyperreal A c g h) := by
  apply ArchimedeanClass.mk_nonneg_of_le_of_le_of_archimedean
    Hyperreal.coeRingHom (r := (-1 : ℝ)) (s := (1 : ℝ))
  · change Hyperreal.ofSeq (fun _ : ℕ ↦ (-1 : ℝ)) ≤
      Hyperreal.ofSeq (fun n ↦
        scaledGramCorrelation (fun k ↦ A.map n (k, 1)) (c n) g h)
    rw [Hyperreal.ofSeq_le_ofSeq]
    exact Filter.Eventually.of_forall fun n ↦ by
      exact (abs_le.mp (abs_scaledGramCorrelation_le_one
        (fun k ↦ A.map n (k, 1)) (c n) g h)).1
  · change Hyperreal.ofSeq (fun n ↦
        scaledGramCorrelation (fun k ↦ A.map n (k, 1)) (c n) g h) ≤
      Hyperreal.ofSeq (fun _ : ℕ ↦ (1 : ℝ))
    rw [Hyperreal.ofSeq_le_ofSeq]
    exact Filter.Eventually.of_forall fun n ↦ by
      exact (abs_le.mp (abs_scaledGramCorrelation_le_one
        (fun k ↦ A.map n (k, 1)) (c n) g h)).2

theorem gramCorrelationHyperreal_comm
    (A : SoficApproximation (K × J))
    (c : ∀ n, Equiv.Perm (A.model n)) (g h : K) :
    gramCorrelationHyperreal A c g h =
      gramCorrelationHyperreal A c h g := by
  apply congrArg Hyperreal.ofSeq
  funext n
  exact scaledGramCorrelation_comm
    (fun k ↦ A.map n (k, 1)) (c n) g h

theorem correlation_sub_gram_tendsto_zero
    (A : SoficApproximation (K × J))
    (c : ∀ n, Equiv.Perm (A.model n)) (g h : K) :
    Filter.Tendsto
      (fun n ↦
        scaledCorrelation (fun k ↦ A.map n (k, 1)) (c n) (g⁻¹ * h) -
          scaledGramCorrelation (fun k ↦ A.map n (k, 1)) (c n) g h)
      Filter.atTop (nhds 0) := by
  refine Metric.tendsto_atTop.mpr fun η hη ↦ ?_
  obtain ⟨N, hN⟩ :=
    relativeCorrelation_approaches_gram_eventually A c g h η hη
  refine ⟨N, fun n hn ↦ ?_⟩
  simpa only [dist_zero_right, Real.norm_eq_abs] using hN n hn

theorem correlationHyperreal_sub_gram_mk_pos
    (A : SoficApproximation (K × J))
    (c : ∀ n, Equiv.Perm (A.model n)) (g h : K) :
    0 < ArchimedeanClass.mk
      (correlationHyperreal A c (g⁻¹ * h) -
        gramCorrelationHyperreal A c g h) := by
  change 0 < ArchimedeanClass.mk (Hyperreal.ofSeq (fun n ↦
    scaledCorrelation (fun k ↦ A.map n (k, 1)) (c n) (g⁻¹ * h) -
      scaledGramCorrelation (fun k ↦ A.map n (k, 1)) (c n) g h))
  apply Hyperreal.archimedeanClassMk_pos_of_tendsto
  rw [Hyperreal.tendsto_ofSeq]
  exact (correlation_sub_gram_tendsto_zero A c g h).mono_left
    Nat.hyperfilter_le_atTop

/-- Standard-part correlation of a permutation-graph sequence. -/
noncomputable def limitingCorrelation
    (A : SoficApproximation (K × J))
    (c : ∀ n, Equiv.Perm (A.model n)) (g : K) : ℝ :=
  ArchimedeanClass.stdPart (correlationHyperreal A c g)

theorem limitingCorrelation_inv_mul_eq_stdPart_gram
    (A : SoficApproximation (K × J))
    (c : ∀ n, Equiv.Perm (A.model n)) (g h : K) :
    limitingCorrelation A c (g⁻¹ * h) =
      ArchimedeanClass.stdPart (gramCorrelationHyperreal A c g h) := by
  have hc := correlationHyperreal_finite A c (g⁻¹ * h)
  have hg := gramCorrelationHyperreal_finite A c g h
  have hsmall := correlationHyperreal_sub_gram_mk_pos A c g h
  have hzero : ArchimedeanClass.stdPart
      (correlationHyperreal A c (g⁻¹ * h) -
        gramCorrelationHyperreal A c g h) = 0 :=
    ArchimedeanClass.stdPart_eq_zero.mpr hsmall.ne'
  have hsub := ArchimedeanClass.stdPart_sub hc hg
  rw [hzero] at hsub
  unfold limitingCorrelation
  exact sub_eq_zero.mp hsub.symm

theorem limitingCorrelation_inv_mul_comm
    (A : SoficApproximation (K × J))
    (c : ∀ n, Equiv.Perm (A.model n)) (g h : K) :
    limitingCorrelation A c (g⁻¹ * h) =
      limitingCorrelation A c (h⁻¹ * g) := by
  rw [limitingCorrelation_inv_mul_eq_stdPart_gram A c g h,
    limitingCorrelation_inv_mul_eq_stdPart_gram A c h g,
    gramCorrelationHyperreal_comm A c g h]

/-- The scaled limiting correlation is positive definite. -/
theorem limitingCorrelation_isPositiveDefinite
    (A : SoficApproximation (K × J))
    (c : ∀ n, Equiv.Perm (A.model n)) :
    IsPositiveDefinite (limitingCorrelation A c) := by
  refine ⟨limitingCorrelation_inv_mul_comm A c, ?_⟩
  intro F a
  classical
  let term : K → K → Hyperreal := fun i j ↦
    ((a i * a j : ℝ) : Hyperreal) * gramCorrelationHyperreal A c i j
  let q : Hyperreal := ∑ i ∈ F, ∑ j ∈ F, term i j
  have hterm (i j : K) : 0 ≤ ArchimedeanClass.mk (term i j) :=
    hyperreal_mul_finite (hyperreal_coe_finite (a i * a j))
      (gramCorrelationHyperreal_finite A c i j)
  have hinner (i : K) :
      0 ≤ ArchimedeanClass.mk (∑ j ∈ F, term i j) :=
    hyperreal_finset_sum_finite F (term i) (fun j _ ↦ hterm i j)
  have hqfinite : 0 ≤ ArchimedeanClass.mk q :=
    hyperreal_finset_sum_finite F (fun i ↦ ∑ j ∈ F, term i j)
      (fun i _ ↦ hinner i)
  have hq : q = Hyperreal.ofSeq (fun n ↦ ∑ i ∈ F, ∑ j ∈ F,
      a i * a j *
        scaledGramCorrelation (fun k ↦ A.map n (k, 1)) (c n) i j) := by
    change (∑ i ∈ F, ∑ j ∈ F,
        ofSeqRingHom (fun _ ↦ a i * a j) *
          ofSeqRingHom (fun n ↦ scaledGramCorrelation
            (fun k ↦ A.map n (k, 1)) (c n) i j)) =
      ofSeqRingHom (fun n ↦ ∑ i ∈ F, ∑ j ∈ F, a i * a j *
        scaledGramCorrelation (fun k ↦ A.map n (k, 1)) (c n) i j)
    rw [show (fun n ↦ ∑ i ∈ F, ∑ j ∈ F, a i * a j *
        scaledGramCorrelation (fun k ↦ A.map n (k, 1)) (c n) i j) =
      ∑ i ∈ F, ∑ j ∈ F, fun n ↦ a i * a j *
        scaledGramCorrelation (fun k ↦ A.map n (k, 1)) (c n) i j by
          funext n
          simp]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← map_mul]
    congr 1
  have hqnonneg : 0 ≤ q := by
    rw [hq]
    change Hyperreal.ofSeq (fun _ : ℕ ↦ (0 : ℝ)) ≤
      Hyperreal.ofSeq (fun n ↦ ∑ i ∈ F, ∑ j ∈ F,
        a i * a j *
          scaledGramCorrelation (fun k ↦ A.map n (k, 1)) (c n) i j)
    rw [Hyperreal.ofSeq_le_ofSeq]
    exact Filter.Eventually.of_forall fun n ↦
      scaledGramCorrelation_quadratic_nonneg F a
        (fun k ↦ A.map n (k, 1)) (c n) id
  have hstdnonneg : 0 ≤ ArchimedeanClass.stdPart q :=
    ArchimedeanClass.le_stdPart_of_le Hyperreal.coeRingHom hqfinite hqnonneg
  have hstd : ArchimedeanClass.stdPart q =
      ∑ i ∈ F, ∑ j ∈ F,
        a i * a j * limitingCorrelation A c (i⁻¹ * j) := by
    calc
      ArchimedeanClass.stdPart q =
          ∑ i ∈ F, ArchimedeanClass.stdPart (∑ j ∈ F, term i j) :=
        stdPart_finset_sum F (fun i ↦ ∑ j ∈ F, term i j)
          (fun i _ ↦ hinner i)
      _ = ∑ i ∈ F, ∑ j ∈ F,
          ArchimedeanClass.stdPart (term i j) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact stdPart_finset_sum F (term i) (fun j _ ↦ hterm i j)
      _ = ∑ i ∈ F, ∑ j ∈ F,
          a i * a j * limitingCorrelation A c (i⁻¹ * j) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [ArchimedeanClass.stdPart_mul
          (hyperreal_coe_finite (a i * a j))
          (gramCorrelationHyperreal_finite A c i j),
          Hyperreal.stdPart_coe,
          ← limitingCorrelation_inv_mul_eq_stdPart_gram A c i j]
  rw [← hstd]
  exact hstdnonneg

/-! ### Kazhdan contraction at the graph scale -/

/-- Bundle the proved scaled correlation for the GNS construction. -/
noncomputable def limitingPositiveDefiniteFunction
    (A : SoficApproximation (K × J))
    (c : ∀ n, Equiv.Perm (A.model n)) :
    KazhdanGNS.PositiveDefiniteFunction K where
  toFun := limitingCorrelation A c
  isPositiveDefinite := limitingCorrelation_isPositiveDefinite A c

/-- Hyperreal Gram norm of a fixed finite cyclic combination. -/
noncomputable def combinationNormSqHyperreal {I : Type*}
    (A : SoficApproximation (K × J))
    (c : ∀ n, Equiv.Perm (A.model n))
    (F : Finset I) (w : I → K) (a : I → ℝ) : Hyperreal :=
  ∑ i ∈ F, ∑ j ∈ F,
    ((a i * a j : ℝ) : Hyperreal) *
      gramCorrelationHyperreal A c (w i) (w j)

theorem combinationNormSqHyperreal_eq_ofSeq {I : Type*}
    (A : SoficApproximation (K × J))
    (c : ∀ n, Equiv.Perm (A.model n))
    (F : Finset I) (w : I → K) (a : I → ℝ) :
    combinationNormSqHyperreal A c F w a = Hyperreal.ofSeq (fun n ↦
      scaledCombinationNormSq F a (fun k ↦ A.map n (k, 1)) (c n) w) := by
  classical
  change (∑ i ∈ F, ∑ j ∈ F,
      ofSeqRingHom (fun _ ↦ a i * a j) *
        ofSeqRingHom (fun n ↦ scaledGramCorrelation
          (fun k ↦ A.map n (k, 1)) (c n) (w i) (w j))) =
    ofSeqRingHom (fun n ↦
      scaledCombinationNormSq F a
        (fun k ↦ A.map n (k, 1)) (c n) w)
  rw [show (fun n ↦ scaledCombinationNormSq F a
      (fun k ↦ A.map n (k, 1)) (c n) w) =
    ∑ i ∈ F, ∑ j ∈ F, fun n ↦ a i * a j *
      scaledGramCorrelation
        (fun k ↦ A.map n (k, 1)) (c n) (w i) (w j) by
      funext n
      rw [scaledCombinationNormSq_eq_gram]
      simp]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← map_mul]
  congr 1

theorem combinationNormSqHyperreal_finite {I : Type*}
    (A : SoficApproximation (K × J))
    (c : ∀ n, Equiv.Perm (A.model n))
    (F : Finset I) (w : I → K) (a : I → ℝ) :
    0 ≤ ArchimedeanClass.mk (combinationNormSqHyperreal A c F w a) := by
  apply hyperreal_finset_sum_finite F
  intro i hi
  apply hyperreal_finset_sum_finite F
  intro j hj
  exact hyperreal_mul_finite (hyperreal_coe_finite (a i * a j))
    (gramCorrelationHyperreal_finite A c (w i) (w j))

theorem stdPart_combinationNormSqHyperreal {I : Type*}
    (A : SoficApproximation (K × J))
    (c : ∀ n, Equiv.Perm (A.model n))
    (F : Finset I) (w : I → K) (a : I → ℝ) :
    ArchimedeanClass.stdPart (combinationNormSqHyperreal A c F w a) =
      ‖KazhdanGNS.indexedCombination
        (limitingPositiveDefiniteFunction A c) F w a‖ ^ 2 := by
  classical
  let term : I → I → Hyperreal := fun i j ↦
    ((a i * a j : ℝ) : Hyperreal) *
      gramCorrelationHyperreal A c (w i) (w j)
  have hterm (i j : I) : 0 ≤ ArchimedeanClass.mk (term i j) :=
    hyperreal_mul_finite (hyperreal_coe_finite (a i * a j))
      (gramCorrelationHyperreal_finite A c (w i) (w j))
  have hinner (i : I) :
      0 ≤ ArchimedeanClass.mk (∑ j ∈ F, term i j) :=
    hyperreal_finset_sum_finite F (term i) fun j _ ↦ hterm i j
  rw [KazhdanGNS.norm_indexedCombination_sq]
  change ArchimedeanClass.stdPart
      (∑ i ∈ F, ∑ j ∈ F, term i j) = _
  calc
    ArchimedeanClass.stdPart (∑ i ∈ F, ∑ j ∈ F, term i j) =
        ∑ i ∈ F, ArchimedeanClass.stdPart (∑ j ∈ F, term i j) :=
      stdPart_finset_sum F (fun i ↦ ∑ j ∈ F, term i j)
        (fun i _ ↦ hinner i)
    _ = ∑ i ∈ F, ∑ j ∈ F,
        ArchimedeanClass.stdPart (term i j) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact stdPart_finset_sum F (term i) fun j _ ↦ hterm i j
    _ = ∑ i ∈ F, ∑ j ∈ F,
        a i * a j * limitingCorrelation A c ((w i)⁻¹ * w j) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [ArchimedeanClass.stdPart_mul
        (hyperreal_coe_finite (a i * a j))
        (gramCorrelationHyperreal_finite A c (w i) (w j)),
        Hyperreal.stdPart_coe,
        ← limitingCorrelation_inv_mul_eq_stdPart_gram A c (w i) (w j)]

theorem stdPart_averagingDisplacementNormSq
    (A : SoficApproximation (K × J))
    (c : ∀ n, Equiv.Perm (A.model n)) (S : Finset K) (k : ℕ) :
    let d := KazhdanGNS.averagingDisplacementCoefficients S k
    ArchimedeanClass.stdPart
        (combinationNormSqHyperreal A c d.support id d) =
      ‖((IsKazhdanPair.orbitAverage S
          (KazhdanGNS.representation
            (limitingPositiveDefiniteFunction A c)))^[k + 1])
          (KazhdanGNS.kernelVector (limitingPositiveDefiniteFunction A c) 1) -
        ((IsKazhdanPair.orbitAverage S
          (KazhdanGNS.representation
            (limitingPositiveDefiniteFunction A c)))^[k])
          (KazhdanGNS.kernelVector
            (limitingPositiveDefiniteFunction A c) 1)‖ ^ 2 := by
  let p := limitingPositiveDefiniteFunction A c
  let d := KazhdanGNS.averagingDisplacementCoefficients S k
  dsimp only
  rw [stdPart_combinationNormSqHyperreal]
  rw [← KazhdanGNS.finsuppCombination_eq_indexed]
  have h := KazhdanGNS.iterate_orbitAverage_succ_sub_eq_finsuppCombination
    p S k
  dsimp only at h ⊢
  rw [h]

theorem stdPart_averagingDisplacementNormSq_le
    {Q : Finset K} {ε : ℝ} (hQ : IsKazhdanPair.{0, 0} K Q ε)
    (S : Finset K) (hQS : Q ⊆ S) (hone : 1 ∈ S) (hεone : ε ≤ 1)
    (A : SoficApproximation (K × J))
    (c : ∀ n, Equiv.Perm (A.model n)) (k : ℕ) :
    let dk := KazhdanGNS.averagingDisplacementCoefficients S k
    let d0 := KazhdanGNS.averagingDisplacementCoefficients S 0
    ArchimedeanClass.stdPart
        (combinationNormSqHyperreal A c dk.support id dk) ≤
      (1 - ε ^ 2 / (4 * S.card)) ^ (2 * k) *
        ArchimedeanClass.stdPart
          (combinationNormSqHyperreal A c d0.support id d0) := by
  let p := limitingPositiveDefiniteFunction A c
  let Av := IsKazhdanPair.orbitAverage S (KazhdanGNS.representation p)
  let factor : ℝ := 1 - ε ^ 2 / (4 * S.card)
  have hnorm := KazhdanOrthogonal.norm_iterate_orbitAverage_succ_sub_le
    hQ S hQS hone hεone (KazhdanGNS.representation p)
      (KazhdanGNS.kernelVector p 1) k
  dsimp only at hnorm
  have hcardNat : 0 < S.card := Finset.card_pos.mpr ⟨1, hone⟩
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hcardNat
  have hεsq : ε ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg ε, hQ.1, hεone]
  have hden : (0 : ℝ) < 4 * S.card := mul_pos (by norm_num) hcard
  have hdenOne : (1 : ℝ) ≤ 4 * S.card := by
    have : (1 : ℝ) ≤ S.card := by exact_mod_cast hcardNat
    nlinarith
  have hfrac : ε ^ 2 / (4 * S.card) ≤ 1 := by
    rw [div_le_one hden]
    exact hεsq.trans hdenOne
  have hfactor : 0 ≤ factor := by dsimp [factor]; linarith
  have hsq :
      ‖(Av^[k + 1]) (KazhdanGNS.kernelVector p 1) -
          (Av^[k]) (KazhdanGNS.kernelVector p 1)‖ ^ 2 ≤
        factor ^ (2 * k) *
          ‖Av (KazhdanGNS.kernelVector p 1) -
            KazhdanGNS.kernelVector p 1‖ ^ 2 := by
    have hleft : 0 ≤ ‖(Av^[k + 1]) (KazhdanGNS.kernelVector p 1) -
        (Av^[k]) (KazhdanGNS.kernelVector p 1)‖ := norm_nonneg _
    have hright : 0 ≤ factor ^ k *
        ‖Av (KazhdanGNS.kernelVector p 1) -
          KazhdanGNS.kernelVector p 1‖ :=
      mul_nonneg (pow_nonneg hfactor k) (norm_nonneg _)
    have hsquare := (sq_le_sq₀ hleft hright).2 hnorm
    calc
      ‖(Av^[k + 1]) (KazhdanGNS.kernelVector p 1) -
          (Av^[k]) (KazhdanGNS.kernelVector p 1)‖ ^ 2 ≤
          (factor ^ k * ‖Av (KazhdanGNS.kernelVector p 1) -
            KazhdanGNS.kernelVector p 1‖) ^ 2 := hsquare
      _ = factor ^ (2 * k) *
          ‖Av (KazhdanGNS.kernelVector p 1) -
            KazhdanGNS.kernelVector p 1‖ ^ 2 := by ring
  dsimp only
  rw [stdPart_averagingDisplacementNormSq,
    stdPart_averagingDisplacementNormSq]
  simpa [Av, p] using hsq

/-- Exact-word displacement norm in the diagonal pair model, normalized by
the size of the underlying permutation model. -/
noncomputable def finiteAveragingDisplacementNormSq
    (A : SoficApproximation (K × J)) (n : ℕ)
    (c : Equiv.Perm (A.model n)) (S : Finset K) (k : ℕ) : ℝ :=
  let d := KazhdanGNS.averagingDisplacementCoefficients S k
  scaledCombinationNormSq d.support d
    (fun g ↦ A.map n (g, 1)) c id

theorem combinationNormSqHyperreal_displacement_eq_ofSeq
    (A : SoficApproximation (K × J))
    (c : ∀ n, Equiv.Perm (A.model n)) (S : Finset K) (k : ℕ) :
    let d := KazhdanGNS.averagingDisplacementCoefficients S k
    combinationNormSqHyperreal A c d.support id d =
      Hyperreal.ofSeq (fun n ↦
        finiteAveragingDisplacementNormSq A n (c n) S k) := by
  exact combinationNormSqHyperreal_eq_ofSeq A c
    (KazhdanGNS.averagingDisplacementCoefficients S k).support id
    (KazhdanGNS.averagingDisplacementCoefficients S k)

/-- Uniform exact-word Kazhdan contraction over all permutation graphs. -/
theorem finiteAveragingDisplacementNormSq_eventually_lt
    {Q : Finset K} {ε : ℝ} (hQ : IsKazhdanPair.{0, 0} K Q ε)
    (S : Finset K) (hQS : Q ⊆ S) (hone : 1 ∈ S) (hεone : ε ≤ 1)
    (A : SoficApproximation (K × J)) (k : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ c : Equiv.Perm (A.model n),
      finiteAveragingDisplacementNormSq A n c S k <
        (1 - ε ^ 2 / (4 * S.card)) ^ (2 * k) *
          finiteAveragingDisplacementNormSq A n c S 0 + δ := by
  classical
  by_contra h
  push Not at h
  choose φ hφ c hbad using h
  let B := A.reindex φ hφ
  let c' : ∀ n, Equiv.Perm (B.model n) := fun n ↦ c n
  let dk := KazhdanGNS.averagingDisplacementCoefficients S k
  let d0 := KazhdanGNS.averagingDisplacementCoefficients S 0
  let factor : ℝ := (1 - ε ^ 2 / (4 * S.card)) ^ (2 * k)
  let Hk : Hyperreal := combinationNormSqHyperreal B c' dk.support id dk
  let H0 : Hyperreal := combinationNormSqHyperreal B c' d0.support id d0
  have hHkfinite : 0 ≤ ArchimedeanClass.mk Hk :=
    combinationNormSqHyperreal_finite B c' dk.support id dk
  have hH0finite : 0 ≤ ArchimedeanClass.mk H0 :=
    combinationNormSqHyperreal_finite B c' d0.support id d0
  have hfactorfinite : 0 ≤ ArchimedeanClass.mk ((factor : ℝ) : Hyperreal) :=
    hyperreal_coe_finite factor
  have hprodFinite :
      0 ≤ ArchimedeanClass.mk (((factor : ℝ) : Hyperreal) * H0) :=
    hyperreal_mul_finite hfactorfinite hH0finite
  have hdiffFinite :
      0 ≤ ArchimedeanClass.mk (Hk - ((factor : ℝ) : Hyperreal) * H0) :=
    KazhdanGNS.hyperreal_sub_finite hHkfinite hprodFinite
  have hhyper : ((δ : ℝ) : Hyperreal) ≤
      Hk - ((factor : ℝ) : Hyperreal) * H0 := by
    rw [show Hk = Hyperreal.ofSeq (fun n ↦
        finiteAveragingDisplacementNormSq B n (c' n) S k) by
          exact combinationNormSqHyperreal_displacement_eq_ofSeq B c' S k,
      show H0 = Hyperreal.ofSeq (fun n ↦
        finiteAveragingDisplacementNormSq B n (c' n) S 0) by
          exact combinationNormSqHyperreal_displacement_eq_ofSeq B c' S 0]
    change Hyperreal.ofSeq (fun _ : ℕ ↦ δ) ≤ Hyperreal.ofSeq (fun n ↦
      finiteAveragingDisplacementNormSq B n (c' n) S k -
        factor * finiteAveragingDisplacementNormSq B n (c' n) S 0)
    rw [Hyperreal.ofSeq_le_ofSeq]
    exact Filter.Eventually.of_forall fun n ↦ by
      have hn := hbad n
      change factor * finiteAveragingDisplacementNormSq B n (c' n) S 0 + δ ≤
        finiteAveragingDisplacementNormSq B n (c' n) S k at hn
      linarith
  have hstdLower : δ ≤ ArchimedeanClass.stdPart
      (Hk - ((factor : ℝ) : Hyperreal) * H0) :=
    ArchimedeanClass.le_stdPart_of_le Hyperreal.coeRingHom hdiffFinite hhyper
  rw [ArchimedeanClass.stdPart_sub hHkfinite hprodFinite,
    ArchimedeanClass.stdPart_mul hfactorfinite hH0finite,
    Hyperreal.stdPart_coe] at hstdLower
  have hlimit := stdPart_averagingDisplacementNormSq_le
    hQ S hQS hone hεone B c' k
  change ArchimedeanClass.stdPart Hk ≤
    factor * ArchimedeanClass.stdPart H0 at hlimit
  linarith

end KunThomCorrelation
end NonsoficGroupsExist
