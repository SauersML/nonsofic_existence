import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Vanishing sequences and negligible densities

Every asymptotic statement in the manuscript has the shape `= o(|Y_n|)`.  This
file provides the single bookkeeping API used for all of them, in the explicit
epsilon--eventually form used throughout this development (no filters).

`Vanishing a` is `a n → 0`; `Negligible N e` is `e n = o(N n)`, i.e. the
normalized quantity `e n / N n` vanishes.  Together with `Diverges` these three
predicates carry every `o(N_n)` estimate of Sections 3--4 of the manuscript.
-/

namespace NonsoficGroupsExist

open scoped BigOperators

/-- A real sequence tending to zero, in explicit form. -/
def Vanishing (a : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → |a n| < ε

/-- A real sequence tending to `+∞`, in explicit form. -/
def Diverges (a : ℕ → ℝ) : Prop :=
  ∀ M : ℝ, ∃ N : ℕ, ∀ n, N ≤ n → M ≤ a n

namespace Vanishing

/-- A pointwise cofinal reindexing preserves convergence to zero. -/
theorem reindex {a : ℕ → ℝ} (ha : Vanishing a) (φ : ℕ → ℕ)
    (hφ : ∀ n, n ≤ φ n) : Vanishing fun n ↦ a (φ n) := by
  intro ε hε
  obtain ⟨N, hN⟩ := ha ε hε
  exact ⟨N, fun n hn ↦ hN (φ n) (hn.trans (hφ n))⟩

/-- Removing finitely many initial terms preserves convergence to zero. -/
theorem shift {a : ℕ → ℝ} (ha : Vanishing a) (k : ℕ) :
    Vanishing fun n ↦ a (n + k) := by
  intro ε hε
  obtain ⟨N, hN⟩ := ha ε hε
  exact ⟨N, fun n hn ↦ hN (n + k) (hn.trans (Nat.le_add_right n k))⟩

theorem zero : Vanishing (fun _ ↦ (0 : ℝ)) := by
  intro ε hε
  exact ⟨0, fun n _ ↦ by simpa using hε⟩

theorem congr {a b : ℕ → ℝ} (ha : Vanishing a) (hab : ∀ n, a n = b n) :
    Vanishing b := by
  intro ε hε
  obtain ⟨N, hN⟩ := ha ε hε
  exact ⟨N, fun n hn ↦ by simpa [hab n] using hN n hn⟩

theorem add {a b : ℕ → ℝ} (ha : Vanishing a) (hb : Vanishing b) :
    Vanishing (fun n ↦ a n + b n) := by
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := ha (ε / 2) (by positivity)
  obtain ⟨N₂, hN₂⟩ := hb (ε / 2) (by positivity)
  refine ⟨max N₁ N₂, fun n hn ↦ ?_⟩
  have h₁ := hN₁ n ((le_max_left N₁ N₂).trans hn)
  have h₂ := hN₂ n ((le_max_right N₁ N₂).trans hn)
  calc
    |a n + b n| ≤ |a n| + |b n| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add h₁ h₂
    _ = ε := by ring

theorem const_mul (c : ℝ) {a : ℕ → ℝ} (ha : Vanishing a) :
    Vanishing (fun n ↦ c * a n) := by
  intro ε hε
  have hpos : 0 < ε / (|c| + 1) := by positivity
  obtain ⟨N, hN⟩ := ha (ε / (|c| + 1)) hpos
  refine ⟨N, fun n hn ↦ ?_⟩
  have hstep := hN n hn
  have habs : |c * a n| = |c| * |a n| := abs_mul _ _
  have hle : |c| * |a n| ≤ (|c| + 1) * |a n| := by
    have := abs_nonneg (a n)
    nlinarith
  have hlt : (|c| + 1) * |a n| < (|c| + 1) * (ε / (|c| + 1)) := by
    apply mul_lt_mul_of_pos_left hstep
    positivity
  have hcancel : (|c| + 1) * (ε / (|c| + 1)) = ε := by
    field_simp
  rw [habs]
  calc
    |c| * |a n| ≤ (|c| + 1) * |a n| := hle
    _ < (|c| + 1) * (ε / (|c| + 1)) := hlt
    _ = ε := hcancel

/-- Squeeze from above by a vanishing sequence. -/
theorem squeeze {a b : ℕ → ℝ} (hnonneg : ∀ n, 0 ≤ a n)
    (hle : ∀ n, a n ≤ b n) (hb : Vanishing b) : Vanishing a := by
  intro ε hε
  obtain ⟨N, hN⟩ := hb ε hε
  refine ⟨N, fun n hn ↦ ?_⟩
  have hb' := hN n hn
  have : b n < ε := lt_of_abs_lt hb'
  rw [abs_of_nonneg (hnonneg n)]
  exact lt_of_le_of_lt (hle n) this

/-- Squeeze from above, with the domination required only eventually. -/
theorem squeeze_eventually {a b : ℕ → ℝ} (hb : Vanishing b) (N₀ : ℕ)
    (h : ∀ n, N₀ ≤ n → 0 ≤ a n ∧ a n ≤ b n) : Vanishing a := by
  intro ε hε
  obtain ⟨N, hN⟩ := hb ε hε
  refine ⟨max N N₀, fun n hn ↦ ?_⟩
  obtain ⟨hnonneg, hle⟩ := h n ((le_max_right N N₀).trans hn)
  have hlt : b n < ε := lt_of_abs_lt (hN n ((le_max_left N N₀).trans hn))
  rw [abs_of_nonneg hnonneg]
  exact lt_of_le_of_lt hle hlt

theorem sub {a b : ℕ → ℝ} (ha : Vanishing a) (hb : Vanishing b) :
    Vanishing (fun n ↦ a n - b n) := by
  have := ha.add (hb.const_mul (-1))
  refine this.congr ?_
  intro n
  ring

theorem sum {ι : Type*} (s : Finset ι) (a : ι → ℕ → ℝ)
    (ha : ∀ i ∈ s, Vanishing (a i)) :
    Vanishing (fun n ↦ ∑ i ∈ s, a i n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Vanishing.zero
  | @insert i s hi ih =>
      have hhead : Vanishing (a i) := ha i (Finset.mem_insert_self i s)
      have htail : Vanishing (fun n ↦ ∑ j ∈ s, a j n) :=
        ih fun j hj ↦ ha j (Finset.mem_insert_of_mem hj)
      refine (hhead.add htail).congr ?_
      intro n
      simp [Finset.sum_insert hi]

end Vanishing

namespace Diverges

theorem congr {a b : ℕ → ℝ} (ha : Diverges a) (hab : ∀ n, a n = b n) :
    Diverges b := by
  intro M
  obtain ⟨N, hN⟩ := ha M
  exact ⟨N, fun n hn ↦ by rw [← hab n]; exact hN n hn⟩

/-- Removing finitely many initial terms preserves divergence. -/
theorem shift {a : ℕ → ℝ} (ha : Diverges a) (k : ℕ) :
    Diverges fun n ↦ a (n + k) := by
  intro M
  obtain ⟨N, hN⟩ := ha M
  exact ⟨N, fun n hn ↦ hN (n + k) (hn.trans (Nat.le_add_right n k))⟩

end Diverges

/-- `e n = o(N n)`: the normalized quantity vanishes. -/
def Negligible (N : ℕ → ℝ) (e : ℕ → ℝ) : Prop :=
  Vanishing fun n ↦ e n / N n

namespace Negligible

/-- Reindexing numerator and denominator along a pointwise cofinal map
preserves negligible density. -/
theorem reindex {N e : ℕ → ℝ} (h : Negligible N e) (φ : ℕ → ℕ)
    (hφ : ∀ n, n ≤ φ n) :
    Negligible (fun n ↦ N (φ n)) (fun n ↦ e (φ n)) := by
  exact Vanishing.reindex h φ hφ

/-- Removing finitely many initial terms preserves a negligible-density
estimate, with numerator and denominator shifted together. -/
theorem shift {N e : ℕ → ℝ} (h : Negligible N e) (k : ℕ) :
    Negligible (fun n ↦ N (n + k)) (fun n ↦ e (n + k)) := by
  exact Vanishing.shift h k

variable {N e f : ℕ → ℝ}

theorem zero : Negligible N (fun _ ↦ 0) := by
  refine Vanishing.zero.congr ?_
  intro n
  simp

theorem congr (he : Negligible N e) (hef : ∀ n, e n = f n) : Negligible N f :=
  Vanishing.congr he fun n ↦ by rw [hef n]

theorem add (he : Negligible N e) (hf : Negligible N f) :
    Negligible N (fun n ↦ e n + f n) := by
  refine Vanishing.congr (Vanishing.add he hf) ?_
  intro n
  rw [add_div]

theorem const_mul (c : ℝ) (he : Negligible N e) :
    Negligible N (fun n ↦ c * e n) := by
  refine Vanishing.congr (Vanishing.const_mul c he) ?_
  intro n
  rw [mul_div_assoc]

/-- Monotonicity: a nonnegative quantity dominated by a negligible one is
negligible.  This is the workhorse of every estimate in Section 4. -/
theorem mono (hN : ∀ n, 0 < N n) (hnonneg : ∀ n, 0 ≤ f n)
    (hle : ∀ n, f n ≤ e n) (he : Negligible N e) : Negligible N f := by
  refine Vanishing.squeeze (fun n ↦ ?_) (fun n ↦ ?_) he
  · exact div_nonneg (hnonneg n) (hN n).le
  · exact div_le_div_of_nonneg_right (hle n) (hN n).le

/-- Monotonicity when the normalizing sequence is merely nonnegative.  This
version also covers finitely many empty finite models, where division by zero
is defined to be zero. -/
theorem mono_nonneg (hN : ∀ n, 0 ≤ N n) (hnonneg : ∀ n, 0 ≤ f n)
    (hle : ∀ n, f n ≤ e n) (he : Negligible N e) : Negligible N f := by
  refine Vanishing.squeeze (fun n ↦ div_nonneg (hnonneg n) (hN n))
    (fun n ↦ div_le_div_of_nonneg_right (hle n) (hN n)) he

theorem sum {ι : Type*} (s : Finset ι) (e : ι → ℕ → ℝ)
    (he : ∀ i ∈ s, Negligible N (e i)) :
    Negligible N (fun n ↦ ∑ i ∈ s, e i n) := by
  refine Vanishing.congr (Vanishing.sum s (fun i n ↦ e i n / N n) he) ?_
  intro n
  rw [Finset.sum_div]

end Negligible

end NonsoficGroupsExist
