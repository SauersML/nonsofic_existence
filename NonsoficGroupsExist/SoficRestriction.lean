import NonsoficGroupsExist.LocalizedApproximation
import NonsoficGroupsExist.SoficErrors
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Removing a negligible set from a sofic approximation

If a negligible set of vertices is deleted from every model, restrictions of
the original permutations can be completed on the complements.  This module
proves that the complements still diverge and that every normalized error
remains negligible, then applies the existing completion theorem.
-/

namespace NonsoficGroupsExist
namespace SoficRestriction

variable {H : Type} [Group H]

noncomputable def retained (A : SoficApproximation H)
    (removed : ∀ n, Finset (A.model n)) (n : ℕ) : Finset (A.model n) :=
  Finset.univ \ removed n

theorem retained_card (A : SoficApproximation H)
    (removed : ∀ n, Finset (A.model n)) (n : ℕ) :
    (retained A removed n).card =
      Fintype.card (A.model n) - (removed n).card := by
  unfold retained
  rw [Finset.card_sdiff,
    Finset.inter_eq_left.mpr (Finset.subset_univ (removed n)),
    Finset.card_univ]

theorem eventually_two_mul_removed_le
    (A : SoficApproximation H) (removed : ∀ n, Finset (A.model n))
    (hremoved : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ))
      fun n ↦ ((removed n).card : ℝ)) :
    ∃ N, ∀ n ≥ N, 2 * (removed n).card ≤ Fintype.card (A.model n) := by
  obtain ⟨Nsmall, hNsmall⟩ := hremoved (1 / 2 : ℝ) (by norm_num)
  obtain ⟨Ncard, hNcard⟩ := A.card_tendsToInfinity 1
  refine ⟨max Nsmall Ncard, fun n hn ↦ ?_⟩
  have hnsmall := (le_max_left Nsmall Ncard).trans hn
  have hncard := (le_max_right Nsmall Ncard).trans hn
  have hcardNat : 0 < Fintype.card (A.model n) :=
    lt_of_lt_of_le Nat.zero_lt_one (hNcard n hncard)
  have hcard : (0 : ℝ) < Fintype.card (A.model n) := by exact_mod_cast hcardNat
  have hratio := lt_of_abs_lt (hNsmall n hnsmall)
  have hratio' : ((removed n).card : ℝ) /
      Fintype.card (A.model n) < 1 / 2 := hratio
  rw [div_lt_iff₀ hcard] at hratio'
  exact_mod_cast (show (2 : ℝ) * (removed n).card ≤
      Fintype.card (A.model n) by linarith)

theorem retained_card_diverges
    (A : SoficApproximation H) (removed : ∀ n, Finset (A.model n))
    (hremoved : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ))
      fun n ↦ ((removed n).card : ℝ)) :
    Diverges fun n ↦ ((retained A removed n).card : ℝ) := by
  obtain ⟨Nhalf, hNhalf⟩ := eventually_two_mul_removed_le A removed hremoved
  intro M
  obtain ⟨k : ℕ, hk : 2 * max M 0 ≤ k⟩ := exists_nat_ge (2 * max M 0)
  obtain ⟨Ncard, hNcard⟩ := A.card_tendsToInfinity k
  refine ⟨max Nhalf Ncard, fun n hn ↦ ?_⟩
  have hhalf := hNhalf n ((le_max_left Nhalf Ncard).trans hn)
  have hcard := hNcard n ((le_max_right Nhalf Ncard).trans hn)
  have hretained := retained_card A removed n
  have htwice : k ≤ 2 * (retained A removed n).card := by
    rw [hretained]
    omega
  have hreal : 2 * max M 0 ≤
      2 * ((retained A removed n).card : ℝ) := by
    exact hk.trans (by exact_mod_cast htwice)
  exact le_trans (le_max_left M 0) (by linarith)

/-- A nonnegative negligible numerator remains negligible after replacing the
ambient cardinality by the complement of a negligible removed set. -/
theorem negligible_over_retained
    (A : SoficApproximation H) (removed : ∀ n, Finset (A.model n))
    (hremoved : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ))
      fun n ↦ ((removed n).card : ℝ))
    (e : ℕ → ℝ) (he0 : ∀ n, 0 ≤ e n)
    (he : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) e) :
    Negligible (fun n ↦ ((retained A removed n).card : ℝ)) e := by
  obtain ⟨Nhalf, hNhalf⟩ := eventually_two_mul_removed_le A removed hremoved
  obtain ⟨Ncard, hNcard⟩ := A.card_tendsToInfinity 1
  intro ε hε
  obtain ⟨Ne, hNe⟩ := he (ε / 2) (by positivity)
  refine ⟨max Nhalf (max Ncard Ne), fun n hn ↦ ?_⟩
  have hhalf := hNhalf n ((le_max_left Nhalf (max Ncard Ne)).trans hn)
  have hcardNat : 0 < Fintype.card (A.model n) :=
    lt_of_lt_of_le Nat.zero_lt_one
      (hNcard n ((le_max_left Ncard Ne).trans
        ((le_max_right Nhalf (max Ncard Ne)).trans hn)))
  have heSmall := hNe n ((le_max_right Ncard Ne).trans
    ((le_max_right Nhalf (max Ncard Ne)).trans hn))
  have hretainedCard := retained_card A removed n
  have hretainedNat : 0 < (retained A removed n).card := by
    rw [hretainedCard]
    omega
  have hcard : (0 : ℝ) < Fintype.card (A.model n) := by exact_mod_cast hcardNat
  have hretained : (0 : ℝ) < (retained A removed n).card := by
    exact_mod_cast hretainedNat
  have hhalfReal : (Fintype.card (A.model n) : ℝ) / 2 ≤
      (retained A removed n).card := by
    rw [hretainedCard]
    rw [Nat.cast_sub (by omega : (removed n).card ≤ Fintype.card (A.model n))]
    have hhalfCast : (2 : ℝ) * (removed n).card ≤
        Fintype.card (A.model n) := by exact_mod_cast hhalf
    linarith
  have heRatio : e n / Fintype.card (A.model n) < ε / 2 := by
    have := lt_of_abs_lt heSmall
    exact this
  have hcompare : e n / (retained A removed n).card ≤
      2 * (e n / Fintype.card (A.model n)) := by
    calc
      e n / (retained A removed n).card ≤
          e n / ((Fintype.card (A.model n) : ℝ) / 2) := by
        exact div_le_div_of_nonneg_left (he0 n) (by positivity) hhalfReal
      _ = 2 * (e n / Fintype.card (A.model n)) := by field_simp
  rw [abs_of_nonneg (div_nonneg (he0 n) hretained.le)]
  exact hcompare.trans_lt (by linarith)

theorem invariant_card_le_removed
    (A : SoficApproximation H) (removed : ∀ n, Finset (A.model n))
    (n : ℕ) (g : H) :
    (Finset.univ.filter fun x : retained A removed n ↦
      A.map n g (x : A.model n) ∉ retained A removed n).card ≤
        (removed n).card := by
  classical
  apply Finset.card_le_card_of_injOn
    (s := Finset.univ.filter fun x : retained A removed n ↦
      A.map n g (x : A.model n) ∉ retained A removed n)
    (t := removed n) (fun x ↦ A.map n g (x : A.model n))
  · intro x hx
    have hout := (Finset.mem_filter.mp hx).2
    have hmem : A.map n g (x : A.model n) ∈ removed n := by
      by_contra hnot
      apply hout
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩
    exact hmem
  · intro x _ y _ hxy
    exact Subtype.ext ((A.map n g).injective hxy)

/-- The ambient sofic approximation localized to complements of a negligible
vertex set. -/
noncomputable def localization
    (A : SoficApproximation H) (removed : ∀ n, Finset (A.model n))
    (hremoved : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ))
      fun n ↦ ((removed n).card : ℝ)) : LocalizedApproximationData H where
  ambient := A.model
  subset := retained A removed
  act := A.map
  card_diverges := retained_card_diverges A removed hremoved
  invariant := by
    intro g
    exact Negligible.mono_nonneg
      (fun _ ↦ by positivity) (fun _ ↦ by positivity)
      (fun n ↦ by exact_mod_cast invariant_card_le_removed A removed n g)
      (negligible_over_retained A removed hremoved
        (fun n ↦ ((removed n).card : ℝ)) (fun _ ↦ by positivity) hremoved)
  multiplicative := by
    intro g h
    let E : ℕ → ℝ := fun n ↦ ((A.multiplicationError n g h).card : ℝ)
    have hE := negligible_over_retained A removed hremoved E
      (fun _ ↦ by positivity) (A.multiplicationError_negligible g h)
    refine Negligible.mono_nonneg (fun _ ↦ by positivity) (fun _ ↦ by positivity)
      (fun n ↦ ?_) hE
    change ((Finset.univ.filter fun x : retained A removed n ↦
      A.map n (g * h) (x : A.model n) ≠
        A.map n g (A.map n h x)).card : ℝ) ≤
      ((A.multiplicationError n g h).card : ℝ)
    exact_mod_cast (show
      (Finset.univ.filter fun x : retained A removed n ↦
        A.map n (g * h) (x : A.model n) ≠
          A.map n g (A.map n h x)).card ≤
        (A.multiplicationError n g h).card by
      apply Finset.card_le_card_of_injOn
        (s := Finset.univ.filter fun x : retained A removed n ↦
          A.map n (g * h) (x : A.model n) ≠
            A.map n g (A.map n h x))
        (t := A.multiplicationError n g h) (fun x ↦ (x : A.model n))
      · intro x hx
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Finset.mem_filter.mp hx).2⟩
      · intro x _ y _ hxy
        exact Subtype.ext hxy)
  faithful := by
    intro g hg
    let E : ℕ → ℝ := fun n ↦ ((A.fixedError n g).card : ℝ)
    have hE := negligible_over_retained A removed hremoved E
      (fun _ ↦ by positivity) (A.fixedError_negligible g hg)
    refine Negligible.mono_nonneg (fun _ ↦ by positivity) (fun _ ↦ by positivity)
      (fun n ↦ ?_) hE
    change ((Finset.univ.filter fun x : retained A removed n ↦
      A.map n g (x : A.model n) = x).card : ℝ) ≤
      ((A.fixedError n g).card : ℝ)
    exact_mod_cast (show
      (Finset.univ.filter fun x : retained A removed n ↦
        A.map n g (x : A.model n) = x).card ≤
        (A.fixedError n g).card by
      apply Finset.card_le_card_of_injOn
        (s := Finset.univ.filter fun x : retained A removed n ↦
          A.map n g (x : A.model n) = x)
        (t := A.fixedError n g) (fun x ↦ (x : A.model n))
      · intro x hx
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Finset.mem_filter.mp hx).2⟩
      · intro x _ y _ hxy
        exact Subtype.ext hxy)

noncomputable def approximation
    (A : SoficApproximation H) (removed : ∀ n, Finset (A.model n))
    (hremoved : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ))
      fun n ↦ ((removed n).card : ℝ)) : SoficApproximation H :=
  (localization A removed hremoved).toSoficApproximation

end SoficRestriction
end NonsoficGroupsExist
