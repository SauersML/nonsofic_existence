import NonsoficGroupsExist.Leavitt.LeavittWindowReduction

/-!
# Degree windows are multiplicative

The span of a degree window is closed under products with the windows
adding: monomials multiply by the prefix trichotomy — a collapse to a
longer `s`-word, a collapse to a longer `t`-word, or zero — and in
each case the degree of the product is the sum of the degrees.
-/

namespace NonsoficGroupsExist
namespace LeavittFamily

variable {A : Type*} [Ring A] (L : LeavittFamily A)
variable {k : Type*} [Field k] [Algebra k A]

/-- Monomial times window span. -/
theorem monomial_mul_mem_span {lo' hi' : ℤ} (a b : List (Fin 2))
    {y : A} (hy : y ∈ Submodule.span k (L.degreeMonomials lo' hi')) :
    L.wordS a * L.wordT b * y ∈ Submodule.span k
      (L.degreeMonomials
        ((a.length : ℤ) - b.length + lo')
        ((a.length : ℤ) - b.length + hi')) := by
  induction hy using Submodule.span_induction with
  | mem y hymem =>
      obtain ⟨c, d, hl, hh, rfl⟩ := hymem
      by_cases h1 : b <+: c
      · obtain ⟨e, rfl⟩ := h1
        have hcollapse : L.wordS a * L.wordT b *
            (L.wordS (b ++ e) * L.wordT d) =
            L.wordS (a ++ e) * L.wordT d := by
          rw [show L.wordS a * L.wordT b *
            (L.wordS (b ++ e) * L.wordT d) =
            L.wordS a * (L.wordT b * L.wordS (b ++ e)) * L.wordT d
            from by noncomm_ring, L.wordT_mul_wordS_append_left,
            ← L.wordS_append]
        rw [hcollapse]
        refine Submodule.subset_span ⟨a ++ e, d, ?_, ?_, rfl⟩
        · simp only [List.length_append] at hl hh ⊢
          push_cast at hl hh ⊢
          omega
        · simp only [List.length_append] at hl hh ⊢
          push_cast at hl hh ⊢
          omega
      · by_cases h2 : c <+: b
        · obtain ⟨f, rfl⟩ := h2
          have hcollapse : L.wordS a * L.wordT (c ++ f) *
              (L.wordS c * L.wordT d) =
              L.wordS a * L.wordT (d ++ f) := by
            rw [show L.wordS a * L.wordT (c ++ f) *
              (L.wordS c * L.wordT d) =
              L.wordS a * (L.wordT (c ++ f) * L.wordS c) * L.wordT d
              from by noncomm_ring, L.wordT_append_mul_wordS,
              show L.wordS a * L.wordT f * L.wordT d =
                L.wordS a * (L.wordT f * L.wordT d) from by
                  noncomm_ring, ← L.wordT_append]
          rw [hcollapse]
          refine Submodule.subset_span ⟨a, d ++ f, ?_, ?_, rfl⟩
          · simp only [List.length_append] at hl hh ⊢
            push_cast at hl hh ⊢
            omega
          · simp only [List.length_append] at hl hh ⊢
            push_cast at hl hh ⊢
            omega
        · have hzero : L.wordT b * L.wordS c = 0 :=
            L.wordT_mul_wordS_of_incomparable b c h1 h2
          rw [show L.wordS a * L.wordT b * (L.wordS c * L.wordT d) =
            L.wordS a * (L.wordT b * L.wordS c) * L.wordT d from by
              noncomm_ring, hzero]
          rw [show L.wordS a * (0 : A) * L.wordT d = 0 from by
            noncomm_ring]
          exact Submodule.zero_mem _
  | zero =>
      rw [mul_zero]
      exact Submodule.zero_mem _
  | add y₁ y₂ _ _ hy₁ hy₂ =>
      rw [mul_add]
      exact Submodule.add_mem _ hy₁ hy₂
  | smul r y _ hy =>
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ r hy

/-- **Windows multiply**: the product of window spans lands in the sum
window. -/
theorem window_mul_mem_span {lo hi lo' hi' : ℤ} {x y : A}
    (hx : x ∈ Submodule.span k (L.degreeMonomials lo hi))
    (hy : y ∈ Submodule.span k (L.degreeMonomials lo' hi')) :
    x * y ∈ Submodule.span k
      (L.degreeMonomials (lo + lo') (hi + hi')) := by
  induction hx using Submodule.span_induction with
  | mem x hxmem =>
      obtain ⟨a, b, hl, hh, rfl⟩ := hxmem
      have := L.monomial_mul_mem_span (k := k) a b hy
      refine L.span_degreeMonomials_mono ?_ ?_ this
      · omega
      · omega
  | zero =>
      rw [zero_mul]
      exact Submodule.zero_mem _
  | add x₁ x₂ _ _ hx₁ hx₂ =>
      rw [add_mul]
      exact Submodule.add_mem _ hx₁ hx₂
  | smul r x _ hx =>
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ r hx

end LeavittFamily
end NonsoficGroupsExist
