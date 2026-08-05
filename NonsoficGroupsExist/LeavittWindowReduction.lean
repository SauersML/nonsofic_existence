import NonsoficGroupsExist.LeavittBalancedUnits

/-!
# Window reduction: every unit narrows to degrees between -1 and 1

The first stage of the Laurent half of the rose-graph `K₁`
computation.  Monomials are graded by `|α| - |β|`; the span of a
degree window `[lo, hi]` shrinks under the elementary corner move of
`LeavittGradingSpans`: factoring the positive part as `b·s₀` and
moving with `(v, w) = (-b, s₀)` cuts the top of the window by one
(down to `1`), and dually `(v, w) = (t₀, -c)` raises the bottom (up to
`-1`).  Iterating, every unit whose value has a finite monomial
representation is congruent modulo the diagonal class group to a unit
with degrees in `[-1, 1]`.
-/

namespace NonsoficGroupsExist
namespace LeavittFamily

open MatrixDiagonalization

variable {A : Type*} [Ring A] (L : LeavittFamily A)

/-- Monomials with degree `|α| - |β|` in the window `[lo, hi]`. -/
def degreeMonomials (lo hi : ℤ) : Set A :=
  {x | ∃ a b : List (Fin 2), lo ≤ (a.length : ℤ) - b.length ∧
    (a.length : ℤ) - b.length ≤ hi ∧ x = L.wordS a * L.wordT b}

theorem degreeMonomials_mono {lo lo' hi hi' : ℤ} (h1 : lo' ≤ lo)
    (h2 : hi ≤ hi') :
    L.degreeMonomials lo hi ⊆ L.degreeMonomials lo' hi' := by
  rintro x ⟨a, b, hl, hh, rfl⟩
  exact ⟨a, b, h1.trans hl, hh.trans h2, rfl⟩

section Windows

variable {k : Type*} [Field k] [Algebra k A]

theorem span_degreeMonomials_mono {lo lo' hi hi' : ℤ} (h1 : lo' ≤ lo)
    (h2 : hi ≤ hi') :
    Submodule.span k (L.degreeMonomials lo hi) ≤
      Submodule.span k (L.degreeMonomials lo' hi') :=
  Submodule.span_mono (L.degreeMonomials_mono h1 h2)

/-- Balanced monomials at any depth live in the zero window. -/
theorem span_levelMonomials_le_degree (n : ℕ) :
    Submodule.span k (L.levelMonomials n) ≤
      Submodule.span k (L.degreeMonomials 0 0) := by
  refine Submodule.span_mono ?_
  rw [levelMonomials_eq]
  rintro x ⟨a, b, ha, hb, rfl⟩
  exact ⟨a, b, by omega, by omega, rfl⟩

/-- The zero window is balanced: after padding, every degree-zero
monomial has both words of a common length. -/
theorem span_degree_zero_le_levelSpan {x : A}
    (hx : x ∈ Submodule.span k (L.degreeMonomials 0 0)) :
    ∃ n : ℕ, x ∈ Submodule.span k (L.levelMonomials n) := by
  induction hx using Submodule.span_induction with
  | mem x hxmem =>
      obtain ⟨a, b, hl, hh, rfl⟩ := hxmem
      have hlen : a.length = b.length := by omega
      exact ⟨a.length, Submodule.subset_span (by
        rw [levelMonomials_eq]
        exact ⟨a, b, rfl, hlen.symm, rfl⟩)⟩
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
      obtain ⟨m, hm⟩ := hx
      obtain ⟨n, hn⟩ := hy
      exact ⟨max m n, Submodule.add_mem _
        (L.span_levelMonomials_mono (le_max_left m n) hm)
        (L.span_levelMonomials_mono (le_max_right m n) hn)⟩
  | smul r x _ hx =>
      obtain ⟨n, hn⟩ := hx
      exact ⟨n, Submodule.smul_mem _ r hn⟩

/-- Wrapping a window element between single letters preserves the
window. -/
theorem wrap_mem_span {lo hi : ℤ} (i j : Fin 2) {x : A}
    (hx : x ∈ Submodule.span k (L.degreeMonomials lo hi)) :
    L.s i * x * L.t j ∈ Submodule.span k (L.degreeMonomials lo hi) := by
  induction hx using Submodule.span_induction with
  | mem x hxmem =>
      obtain ⟨a, b, hl, hh, rfl⟩ := hxmem
      refine Submodule.subset_span ⟨i :: a, j :: b, ?_, ?_, ?_⟩
      · simpa using hl
      · simpa using hh
      · rw [L.wordS_cons, L.wordT_cons]
        noncomm_ring
  | zero =>
      rw [mul_zero, zero_mul]
      exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
      rw [mul_add, add_mul]
      exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
      rw [mul_smul_comm, smul_mul_assoc]
      exact Submodule.smul_mem _ r hx

/-- Split off the positive part as a right factor of `s₀`. -/
theorem exists_decomp_top {lo hi : ℤ} {x : A}
    (hx : x ∈ Submodule.span k (L.degreeMonomials lo hi)) :
    ∃ a b : A, x = a + b * L.s 0 ∧
      a ∈ Submodule.span k (L.degreeMonomials lo 0) ∧
      b ∈ Submodule.span k (L.degreeMonomials 0 (hi - 1)) := by
  induction hx using Submodule.span_induction with
  | mem x hxmem =>
      obtain ⟨a, b, hl, hh, rfl⟩ := hxmem
      by_cases hd : (a.length : ℤ) - b.length ≤ 0
      · exact ⟨L.wordS a * L.wordT b, 0, by rw [zero_mul, add_zero],
          Submodule.subset_span ⟨a, b, hl, hd, rfl⟩,
          Submodule.zero_mem _⟩
      · refine ⟨0, L.wordS a * L.wordT (0 :: b), ?_, Submodule.zero_mem _,
          Submodule.subset_span ⟨a, 0 :: b, ?_, ?_, rfl⟩⟩
        · rw [zero_add]
          exact L.monomial_factor_s0 a b
        · simp only [List.length_cons]
          push_cast
          omega
        · simp only [List.length_cons]
          push_cast
          omega
  | zero =>
      exact ⟨0, 0, by rw [zero_mul, add_zero], Submodule.zero_mem _,
        Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
      obtain ⟨ax, bx, hxe, hax, hbx⟩ := hx
      obtain ⟨ay, by', hye, hay, hby⟩ := hy
      exact ⟨ax + ay, bx + by', by rw [hxe, hye, add_mul]; abel,
        Submodule.add_mem _ hax hay, Submodule.add_mem _ hbx hby⟩
  | smul r x _ hx =>
      obtain ⟨a, b, hxe, ha, hb⟩ := hx
      exact ⟨r • a, r • b, by rw [hxe, smul_add, smul_mul_assoc],
        Submodule.smul_mem _ r ha, Submodule.smul_mem _ r hb⟩

/-- Split off the negative part as a left factor of `t₀`. -/
theorem exists_decomp_bot {lo hi : ℤ} {x : A}
    (hx : x ∈ Submodule.span k (L.degreeMonomials lo hi)) :
    ∃ c r : A, x = L.t 0 * c + r ∧
      c ∈ Submodule.span k (L.degreeMonomials (lo + 1) 0) ∧
      r ∈ Submodule.span k (L.degreeMonomials 0 hi) := by
  induction hx using Submodule.span_induction with
  | mem x hxmem =>
      obtain ⟨a, b, hl, hh, rfl⟩ := hxmem
      by_cases hd : 0 ≤ (a.length : ℤ) - b.length
      · exact ⟨0, L.wordS a * L.wordT b, by rw [mul_zero, zero_add],
          Submodule.zero_mem _, Submodule.subset_span ⟨a, b, hd, hh, rfl⟩⟩
      · refine ⟨L.wordS (0 :: a) * L.wordT b, 0, ?_,
          Submodule.subset_span ⟨0 :: a, b, ?_, ?_, rfl⟩,
          Submodule.zero_mem _⟩
        · rw [add_zero]
          exact L.monomial_factor_t0 a b
        · simp only [List.length_cons]
          push_cast
          omega
        · simp only [List.length_cons]
          push_cast
          omega
  | zero =>
      exact ⟨0, 0, by rw [mul_zero, add_zero], Submodule.zero_mem _,
        Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
      obtain ⟨cx, rx, hxe, hcx, hrx⟩ := hx
      obtain ⟨cy, ry, hye, hcy, hry⟩ := hy
      exact ⟨cx + cy, rx + ry, by rw [hxe, hye, mul_add]; abel,
        Submodule.add_mem _ hcx hcy, Submodule.add_mem _ hrx hry⟩
  | smul r x _ hx =>
      obtain ⟨c, r', hxe, hc, hr⟩ := hx
      exact ⟨r • c, r • r', by rw [hxe, smul_add, mul_smul_comm],
        Submodule.smul_mem _ r hc, Submodule.smul_mem _ r hr⟩

/-- The two universal correction terms of the corner move. -/
theorem corner_terms_mem_span {lo hi : ℤ} (hlo : lo ≤ -1) (hhi : 1 ≤ hi) :
    L.s 1 * L.s 0 * L.t 0 ∈
        Submodule.span k (L.degreeMonomials lo hi) ∧
      L.s 0 * L.t 0 * L.t 1 ∈
        Submodule.span k (L.degreeMonomials lo hi) ∧
      L.s 1 * L.t 1 ∈ Submodule.span k (L.degreeMonomials lo hi) := by
  refine ⟨Submodule.subset_span ⟨[1, 0], [0], ?_, ?_, ?_⟩,
    Submodule.subset_span ⟨[0], [1, 0], ?_, ?_, ?_⟩,
    Submodule.subset_span ⟨[1], [1], ?_, ?_, ?_⟩⟩
  · simp; omega
  · simp; omega
  · show L.s 1 * L.s 0 * L.t 0 = L.wordS [1, 0] * L.wordT [0]
    simp [mul_assoc]
  · simp; omega
  · simp; omega
  · show L.s 0 * L.t 0 * L.t 1 = L.wordS [0] * L.wordT [1, 0]
    simp [mul_assoc]
  · simp; omega
  · simp; omega
  · show L.s 1 * L.t 1 = L.wordS [1] * L.wordT [1]
    simp

/-- One corner move cuts the top of the window by one. -/
theorem exists_top_cut [Nontrivial A]
    (hdiv : ∀ x : A, x ≠ 0 → ∃ p q : A, p * x * q = 1)
    {lo hi : ℤ} (hlo : lo ≤ -1) (hhi : 2 ≤ hi) (u : Aˣ)
    (hu : (u : A) ∈ Submodule.span k (L.degreeMonomials lo hi)) :
    ∃ u' : Aˣ, u' * u⁻¹ ∈ stableUnits A ∧
      (u' : A) ∈ Submodule.span k (L.degreeMonomials lo (hi - 1)) := by
  obtain ⟨a, b, hxe, ha, hb⟩ := L.exists_decomp_top hu
  obtain ⟨u', hval, hmem⟩ := L.exists_corner_move hdiv u (-b) (L.s 0)
  refine ⟨u', hmem, ?_⟩
  have huvw : (u : A) + -b * L.s 0 = a := by
    rw [hxe, neg_mul]; abel
  rw [hval, huvw]
  obtain ⟨hterm1, -, hterm3⟩ :=
    L.corner_terms_mem_span (k := k) hlo (by omega : (1 : ℤ) ≤ hi - 1)
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    ?_ ?_) ?_) hterm3
  · exact L.wrap_mem_span 0 0
      (L.span_degreeMonomials_mono le_rfl (by omega) ha)
  · exact L.wrap_mem_span 0 1 (Submodule.neg_mem _
      (L.span_degreeMonomials_mono (by omega) le_rfl hb))
  · exact hterm1

/-- One mirror corner move raises the bottom of the window by one. -/
theorem exists_bot_cut [Nontrivial A]
    (hdiv : ∀ x : A, x ≠ 0 → ∃ p q : A, p * x * q = 1)
    {lo hi : ℤ} (hlo : lo ≤ -2) (hhi : 1 ≤ hi) (u : Aˣ)
    (hu : (u : A) ∈ Submodule.span k (L.degreeMonomials lo hi)) :
    ∃ u' : Aˣ, u' * u⁻¹ ∈ stableUnits A ∧
      (u' : A) ∈ Submodule.span k (L.degreeMonomials (lo + 1) hi) := by
  obtain ⟨c, r, hxe, hc, hr⟩ := L.exists_decomp_bot hu
  obtain ⟨u', hval, hmem⟩ := L.exists_corner_move hdiv u (L.t 0) (-c)
  refine ⟨u', hmem, ?_⟩
  have huvw : (u : A) + L.t 0 * -c = r := by
    rw [hxe, mul_neg]; abel
  rw [hval, huvw]
  obtain ⟨hterm1, hterm2, hterm3⟩ :=
    L.corner_terms_mem_span (k := k)
      (by omega : lo + 1 ≤ -1) (by omega : (1 : ℤ) ≤ hi)
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    ?_ ?_) ?_) hterm3
  · exact L.wrap_mem_span 0 0
      (L.span_degreeMonomials_mono (by omega) le_rfl hr)
  · exact hterm2
  · exact L.wrap_mem_span 1 0 (Submodule.neg_mem _
      (L.span_degreeMonomials_mono le_rfl (by omega) hc))

/-- **Window reduction**: every unit with value in a finite degree
window is congruent modulo the diagonal class group to a unit with
degrees in `[-1, 1]`. -/
theorem exists_window_reduction [Nontrivial A]
    (hdiv : ∀ x : A, x ≠ 0 → ∃ p q : A, p * x * q = 1)
    {lo hi : ℤ} (u : Aˣ)
    (hu : (u : A) ∈ Submodule.span k (L.degreeMonomials lo hi)) :
    ∃ u' : Aˣ, u' * u⁻¹ ∈ stableUnits A ∧
      (u' : A) ∈ Submodule.span k (L.degreeMonomials (-1) 1) := by
  have hwide : (u : A) ∈ Submodule.span k
      (L.degreeMonomials (min lo (-1)) (max hi 1)) :=
    L.span_degreeMonomials_mono (min_le_left _ _) (le_max_left _ _) hu
  clear hu
  set lo' := min lo (-1) with hlo'
  set hi' := max hi 1 with hhi'
  have hlo : lo' ≤ -1 := min_le_right _ _
  have hhi : 1 ≤ hi' := le_max_right _ _
  clear_value lo' hi'
  clear hlo' hhi'
  -- first cut the top down to 1
  obtain ⟨u₁, hmem₁, hu₁⟩ : ∃ u' : Aˣ, u' * u⁻¹ ∈ stableUnits A ∧
      (u' : A) ∈ Submodule.span k (L.degreeMonomials lo' 1) := by
    obtain ⟨n, hn⟩ : ∃ n : ℕ, hi' = 1 + n :=
      ⟨(hi' - 1).toNat, by omega⟩
    subst hn
    clear hhi
    induction n generalizing u with
    | zero =>
        refine ⟨u, by rw [mul_inv_cancel]; exact one_mem _, ?_⟩
        rwa [show (1 : ℤ) + ((0 : ℕ) : ℤ) = 1 from by simp] at hwide
    | succ m ih =>
        obtain ⟨u₁, hmem₁, hu₁⟩ := L.exists_top_cut hdiv hlo
          (by omega) u hwide
        obtain ⟨u₂, hmem₂, hu₂⟩ := ih u₁ (by
          simp only [Nat.cast_add, Nat.cast_one] at hu₁
          rwa [show (1 : ℤ) + ((m : ℤ) + 1) - 1 = 1 + (m : ℤ) from by
            ring] at hu₁)
        refine ⟨u₂, ?_, hu₂⟩
        have := mul_mem hmem₂ hmem₁
        rwa [show u₂ * u₁⁻¹ * (u₁ * u⁻¹) = u₂ * u⁻¹ from by group]
          at this
  -- then raise the bottom up to -1
  obtain ⟨u₂, hmem₂, hu₂⟩ : ∃ u' : Aˣ, u' * u₁⁻¹ ∈ stableUnits A ∧
      (u' : A) ∈ Submodule.span k (L.degreeMonomials (-1) 1) := by
    obtain ⟨n, hn⟩ : ∃ n : ℕ, lo' = -1 - n :=
      ⟨(-1 - lo').toNat, by omega⟩
    subst hn
    clear hlo hwide
    induction n generalizing u₁ with
    | zero =>
        refine ⟨u₁, by rw [mul_inv_cancel]; exact one_mem _, ?_⟩
        rwa [show (-1 : ℤ) - ((0 : ℕ) : ℤ) = -1 from by simp] at hu₁
    | succ m ih =>
        obtain ⟨v₁, hvmem, hv₁⟩ := L.exists_bot_cut hdiv
          (by omega) (by omega) u₁ hu₁
        have hv₁u : v₁ * u⁻¹ ∈ stableUnits A := by
          have hchain := mul_mem hvmem hmem₁
          rwa [show v₁ * u₁⁻¹ * (u₁ * u⁻¹) = v₁ * u⁻¹ from by group]
            at hchain
        have hv₁' : (v₁ : A) ∈ Submodule.span k
            (L.degreeMonomials (-1 - (m : ℤ)) 1) := by
          simp only [Nat.cast_add, Nat.cast_one] at hv₁
          rwa [show (-1 : ℤ) - ((m : ℤ) + 1) + 1 = -1 - (m : ℤ) from by
            ring] at hv₁
        obtain ⟨v₂, hv2mem, hv₂⟩ := ih v₁ hv₁u hv₁'
        refine ⟨v₂, ?_, hv₂⟩
        have := mul_mem hv2mem hvmem
        rwa [show v₂ * v₁⁻¹ * (v₁ * u₁⁻¹) = v₂ * u₁⁻¹ from by group]
          at this
  refine ⟨u₂, ?_, hu₂⟩
  have := mul_mem hmem₂ hmem₁
  rwa [show u₂ * u₁⁻¹ * (u₁ * u⁻¹) = u₂ * u⁻¹ from by group] at this

end Windows

end LeavittFamily
end NonsoficGroupsExist
