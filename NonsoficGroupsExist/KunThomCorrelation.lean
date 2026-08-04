import NonsoficGroupsExist.KunThomDiagonal
import NonsoficGroupsExist.SoficTransfer

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

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- The centered characteristic vector of a permutation graph. -/
noncomputable def graphVector (c : Equiv.Perm Y) :
    EuclideanSpace ℝ (Y × Y) :=
  centeredIndicator (permutationGraph Y c)

theorem norm_graphVector_sq_le [Nonempty Y] (c : Equiv.Perm Y) :
    ‖graphVector c‖ ^ 2 ≤ Fintype.card Y := by
  rw [graphVector, norm_centeredIndicator_sq, card_permutationGraph]
  have hcard : (0 : ℝ) < Fintype.card Y := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Y)
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

/-- Every scaled coefficient lies in `[-1,1]`. -/
theorem abs_scaledPermutationCorrelation_le_one [Nonempty Y]
    (c p : Equiv.Perm Y) :
    |scaledPermutationCorrelation c p| ≤ 1 := by
  have hcard : (0 : ℝ) < Fintype.card Y := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Y)
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

variable {K J : Type*} [Group K] [Group J]

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
  refine ⟨Nclose, fun n hn ↦ ?_⟩
  have hcardNat : 0 < Fintype.card (A.model n) := (A.model n).nonempty
  letI : Nonempty (A.model n) := Fintype.card_pos_iff.mp hcardNat
  let p := A.map n (g⁻¹ * h, (1 : J))
  let q := (A.map n (g, (1 : J)))⁻¹ * A.map n (h, 1)
  have hclose : hammingDistance (A.model n) p q < η ^ 2 / 4 := by
    simpa [p, q] using hNclose n hn
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
  rw [scaledCorrelation, scaledPermutationCorrelation,
    scaledGramCorrelation_eq_relative]
  simpa [p, q] using hresult

end KunThomCorrelation
end NonsoficGroupsExist
