import NonsoficGroupsExist.Sofic.Asymptotics
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# Weighted selection

This file formalizes Lemma `lem:select` of the manuscript: from a family of
blocks carrying a positive proportion of the mass and a family of error weights
whose total is `o(N_n)` for every fixed level, one can select a single block per
index at which *every* error level is negligible relative to the block size, and
whose size diverges.

The manuscript's proof is reproduced in three steps:

* `exists_le_weighted_average` -- the finite pigeonhole step;
* `diagonalLevel` -- the diagonal choice of levels, via `Nat.findGreatest`;
* `exists_selection` -- their combination.

Divergence of the selected block sizes is obtained exactly as in the
manuscript, by feeding the "small blocks carry little mass" hypothesis into the
error family; this is `exists_selection_diverging`.
-/

namespace NonsoficGroupsExist

open scoped BigOperators

/-- Finite pigeonhole: some index has error-to-weight ratio at most the global
weighted average. -/
theorem exists_le_weighted_average {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (w b : ι → ℝ) (hw : ∀ i ∈ s, 0 < w i) :
    ∃ i ∈ s, b i / w i ≤ (∑ j ∈ s, b j) / (∑ j ∈ s, w j) := by
  have hsum : 0 < ∑ j ∈ s, w j := Finset.sum_pos hw hs
  have havg : ∑ i ∈ s, b i ≤
      ∑ i ∈ s, ((∑ j ∈ s, b j) / (∑ j ∈ s, w j)) * w i := by
    rw [← Finset.mul_sum, div_mul_cancel₀ _ hsum.ne']
  obtain ⟨i, hi, hbound⟩ := Finset.exists_le_of_sum_le hs havg
  exact ⟨i, hi, (div_le_iff₀ (hw i hi)).2 hbound⟩

/-- The diagonal level associated with a doubly indexed error array. -/
noncomputable def diagonalLevel (e : ℕ → ℕ → ℝ) (n : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (fun k ↦ e n k < 1 / ((k : ℝ) + 1)) n

theorem diagonalLevel_diverges (e : ℕ → ℕ → ℝ)
    (he : ∀ k, Vanishing fun n ↦ e n k) :
    ∀ k : ℕ, ∃ N : ℕ, ∀ n, N ≤ n → k ≤ diagonalLevel e n := by
  classical
  intro k
  have htol : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  obtain ⟨N₁, hN₁⟩ := he k (1 / ((k : ℝ) + 1)) htol
  refine ⟨max k N₁, fun n hn ↦ ?_⟩
  have hkn : k ≤ n := (le_max_left k N₁).trans hn
  have hspec : e n k < 1 / ((k : ℝ) + 1) :=
    lt_of_abs_lt (hN₁ n ((le_max_right k N₁).trans hn))
  exact Nat.le_findGreatest hkn hspec

theorem diagonalLevel_error (e : ℕ → ℕ → ℝ) (hnonneg : ∀ n k, 0 ≤ e n k)
    (he : ∀ k, Vanishing fun n ↦ e n k) :
    Vanishing fun n ↦ e n (diagonalLevel e n) := by
  classical
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨N₁, hN₁⟩ := diagonalLevel_diverges e he k
  -- the predicate holds at level `0` for large `n`, so `findGreatest` is
  -- attained and its defining inequality is available
  obtain ⟨N₂, hN₂⟩ := he 0 1 (by norm_num)
  refine ⟨max N₁ N₂, fun n hn ↦ ?_⟩
  have hk_le : k ≤ diagonalLevel e n := hN₁ n ((le_max_left N₁ N₂).trans hn)
  have hzero : e n 0 < 1 / ((0 : ℝ) + 1) := by
    have := lt_of_abs_lt (hN₂ n ((le_max_right N₁ N₂).trans hn))
    simpa using this
  have hattained :
      e n (diagonalLevel e n) < 1 / ((diagonalLevel e n : ℝ) + 1) := by
    have :=
      Nat.findGreatest_spec (P := fun k ↦ e n k < 1 / ((k : ℝ) + 1))
        (Nat.zero_le n) (by simpa using hzero)
    simpa [diagonalLevel] using this
  have hmono : 1 / ((diagonalLevel e n : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) := by
    apply one_div_le_one_div_of_le (by positivity)
    have : (k : ℝ) ≤ (diagonalLevel e n : ℝ) := by exact_mod_cast hk_le
    linarith
  rw [abs_of_nonneg (hnonneg n _)]
  calc
    e n (diagonalLevel e n) < 1 / ((diagonalLevel e n : ℝ) + 1) := hattained
    _ ≤ 1 / ((k : ℝ) + 1) := hmono
    _ < ε := by simpa using hk

/-- **Lemma `lem:select`.**  A single block can be chosen per index at which
every fixed error level is negligible relative to the block size. -/
theorem exists_selection {β : ℕ → Type*}
    (I : ∀ n, Finset (β n)) (size : ∀ n, β n → ℝ) (E : ℕ → ∀ n, β n → ℝ)
    (N : ℕ → ℝ) (hN : ∀ n, 0 < N n) (hne : ∀ n, (I n).Nonempty)
    (hsize : ∀ n, ∀ i ∈ I n, 0 < size n i)
    (herr_nonneg : ∀ r n, ∀ i ∈ I n, 0 ≤ E r n i)
    (hmono : ∀ r r' n i, r ≤ r' → E r n i ≤ E r' n i)
    (hmass : ∀ n, (1 / 2) * N n ≤ ∑ i ∈ I n, size n i)
    (herr : ∀ r, Negligible N fun n ↦ ∑ i ∈ I n, E r n i) :
    ∃ sel : ∀ n, β n, (∀ n, sel n ∈ I n) ∧
      (∀ r, Vanishing fun n ↦ E r n (sel n) / size n (sel n)) := by
  classical
  set e : ℕ → ℕ → ℝ :=
    fun n r ↦ (∑ i ∈ I n, E r n i) / (∑ i ∈ I n, size n i) with hedef
  have hsizesum : ∀ n, 0 < ∑ i ∈ I n, size n i := fun n ↦
    Finset.sum_pos (hsize n) (hne n)
  have he_nonneg : ∀ n k, 0 ≤ e n k := by
    intro n k
    apply div_nonneg _ (hsizesum n).le
    exact Finset.sum_nonneg fun i hi ↦ herr_nonneg k n i hi
  have he_vanishing : ∀ k, Vanishing fun n ↦ e n k := by
    intro k
    refine Vanishing.squeeze (fun n ↦ he_nonneg n k) (fun n ↦ ?_)
      (Negligible.const_mul 2 (herr k))
    have hmassn := hmass n
    have hnum : 0 ≤ ∑ i ∈ I n, E k n i :=
      Finset.sum_nonneg fun i hi ↦ herr_nonneg k n i hi
    have hhalf : 0 < (1 / 2) * N n := by
      have := hN n; linarith
    calc
      e n k ≤ (∑ i ∈ I n, E k n i) / ((1 / 2) * N n) := by
        apply div_le_div_of_nonneg_left hnum hhalf hmassn
      _ = 2 * ((∑ i ∈ I n, E k n i) / N n) := by
        field_simp
      _ = (fun n ↦ 2 * ∑ i ∈ I n, E k n i) n / N n := by
        rw [mul_div_assoc]
  have hdiag := diagonalLevel_error e he_nonneg he_vanishing
  have hdiverge := diagonalLevel_diverges e he_vanishing
  have hchoice : ∀ n, ∃ i ∈ I n,
      E (diagonalLevel e n) n i / size n i ≤ e n (diagonalLevel e n) := by
    intro n
    simpa [hedef] using
      exists_le_weighted_average (I n) (hne n) (size n)
        (E (diagonalLevel e n) n) (hsize n)
  choose sel hsel hselbound using hchoice
  refine ⟨sel, hsel, ?_⟩
  intro r
  obtain ⟨N₀, hN₀⟩ := hdiverge r
  refine Vanishing.squeeze_eventually hdiag N₀ (fun n hn ↦ ⟨?_, ?_⟩)
  · exact div_nonneg (herr_nonneg r n _ (hsel n)) (hsize n _ (hsel n)).le
  · have hle : r ≤ diagonalLevel e n := hN₀ n hn
    calc
      E r n (sel n) / size n (sel n) ≤
          E (diagonalLevel e n) n (sel n) / size n (sel n) := by
        apply div_le_div_of_nonneg_right (hmono r _ n _ hle)
        exact (hsize n _ (hsel n)).le
      _ ≤ e n (diagonalLevel e n) := hselbound n

/-- The manuscript's divergence conclusion.  Feeding the mass carried by small
blocks into the error family forces the selected block sizes to diverge. -/
theorem exists_selection_diverging {β : ℕ → Type*}
    (I : ∀ n, Finset (β n)) (size : ∀ n, β n → ℝ) (E : ℕ → ∀ n, β n → ℝ)
    (N : ℕ → ℝ) (hN : ∀ n, 0 < N n) (hne : ∀ n, (I n).Nonempty)
    (hsize : ∀ n, ∀ i ∈ I n, 0 < size n i)
    (herr_nonneg : ∀ r n, ∀ i ∈ I n, 0 ≤ E r n i)
    (hmono : ∀ r r' n i, r ≤ r' → E r n i ≤ E r' n i)
    (hmass : ∀ n, (1 / 2) * N n ≤ ∑ i ∈ I n, size n i)
    (herr : ∀ r, Negligible N fun n ↦ ∑ i ∈ I n, E r n i)
    (hsmall : ∀ M : ℕ, Negligible N fun n ↦
      ∑ i ∈ I n, (if size n i ≤ M then size n i else 0)) :
    ∃ sel : ∀ n, β n, (∀ n, sel n ∈ I n) ∧
      (∀ r, Vanishing fun n ↦ E r n (sel n) / size n (sel n)) ∧
      Diverges fun n ↦ size n (sel n) := by
  classical
  set E' : ℕ → ∀ n, β n → ℝ :=
    fun r n i ↦ E r n i + (if size n i ≤ r then size n i else 0) with hE'
  have hE'_nonneg : ∀ r n, ∀ i ∈ I n, 0 ≤ E' r n i := by
    intro r n i hi
    have := herr_nonneg r n i hi
    have hsz := (hsize n i hi).le
    by_cases hc : size n i ≤ r <;> simp [hE', hc] <;> linarith
  have hE'_mono : ∀ r r' n i, r ≤ r' → E' r n i ≤ E' r' n i := by
    intro r r' n i hrr
    have hbase := hmono r r' n i hrr
    have hcast : (r : ℝ) ≤ r' := by exact_mod_cast hrr
    by_cases hc : size n i ≤ (r : ℝ)
    · have hc' : size n i ≤ (r' : ℝ) := hc.trans hcast
      simp [hE', hc, hc']
      linarith
    · by_cases hc' : size n i ≤ (r' : ℝ) <;> simp [hE', hc, hc'] <;> linarith
  have hE'_sum : ∀ r, Negligible N fun n ↦ ∑ i ∈ I n, E' r n i := by
    intro r
    refine Negligible.congr (Negligible.add (herr r) (hsmall r)) ?_
    intro n
    rw [← Finset.sum_add_distrib]
  obtain ⟨sel, hsel, hbound⟩ :=
    exists_selection I size E' N hN hne hsize hE'_nonneg hE'_mono hmass hE'_sum
  refine ⟨sel, hsel, ?_, ?_⟩
  · intro r
    refine Vanishing.squeeze (fun n ↦ ?_) (fun n ↦ ?_) (hbound r)
    · exact div_nonneg (herr_nonneg r n _ (hsel n)) (hsize n _ (hsel n)).le
    · apply div_le_div_of_nonneg_right _ (hsize n _ (hsel n)).le
      have : 0 ≤ (if size n (sel n) ≤ (r : ℝ) then size n (sel n) else 0) := by
        by_cases hc : size n (sel n) ≤ (r : ℝ) <;>
          simp [hc, (hsize n _ (hsel n)).le]
      simp only [hE']
      linarith
  · intro M
    obtain ⟨k, hk⟩ := exists_nat_gt M
    obtain ⟨N₀, hN₀⟩ := hbound k 1 (by norm_num)
    refine ⟨N₀, fun n hn ↦ ?_⟩
    have hlt := lt_of_abs_lt (hN₀ n hn)
    have hpos := hsize n _ (hsel n)
    by_contra hcon
    push Not at hcon
    have hle : size n (sel n) ≤ (k : ℝ) := le_of_lt (hcon.trans hk)
    have hone : (1 : ℝ) ≤ E' k n (sel n) / size n (sel n) := by
      rw [le_div_iff₀ hpos]
      have hnn := herr_nonneg k n _ (hsel n)
      simp only [hE', if_pos hle]
      linarith
    linarith

end NonsoficGroupsExist
