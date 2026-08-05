import NonsoficGroupsExist.LeavittDegreeZero
import NonsoficGroupsExist.FamilyDescent

/-!
# Graded spans and the elementary corner move

Groundwork for the Laurent half of the rose-graph `K₁` computation.
The balanced spans of `LeavittDegreeZero` are rewritten in length-based
form and shown to be monotone in the depth (padding by
`1 = s₀t₀ + s₁t₁`), positive-degree monomials factor one `s₀` off their
right end, and the two-by-two elementary move
`diag(u,1) ↦ [[u + vw, v],[w, 1]]` is realized inside the unit group of
the base ring through the depth-one corner picture: for all `v, w` the
unit `s₀(u+vw)t₀ + s₀vt₁ + s₁wt₀ + s₁t₁` is congruent to `u` modulo the
diagonal class group.
-/

namespace NonsoficGroupsExist
namespace LeavittFamily

open MatrixDiagonalization

variable {A : Type*} [Ring A] (L : LeavittFamily A)

/-- Length-based description of the balanced monomials. -/
theorem levelMonomials_eq (n : ℕ) :
    L.levelMonomials n = {x | ∃ a b : List (Fin 2),
      a.length = n ∧ b.length = n ∧ x = L.wordS a * L.wordT b} := by
  ext x
  constructor
  · rintro ⟨f, g, rfl⟩
    exact ⟨List.ofFn f, List.ofFn g, by simp, by simp, rfl⟩
  · rintro ⟨a, b, ha, hb, rfl⟩
    subst ha
    refine ⟨fun i ↦ a[i], fun i ↦ b[i]'(by rw [hb]; exact i.isLt), ?_⟩
    have hofa : List.ofFn (fun i : Fin a.length ↦ a[i]) = a := by
      apply List.ext_getElem <;> simp
    have hofb : List.ofFn (fun i : Fin a.length ↦
        b[i]'(by rw [hb]; exact i.isLt)) = b := by
      apply List.ext_getElem
      · simp [hb]
      · intro i h1 h2
        simp
    rw [hofa, hofb]

section Scalars

variable {k : Type*} [CommRing k] [Algebra k A]

/-- Padding: the balanced span at depth `n` sits inside depth `n+1`,
by inserting `1 = s₀t₀ + s₁t₁` between the words. -/
theorem span_levelMonomials_le_succ (n : ℕ) :
    Submodule.span k (L.levelMonomials n) ≤
      Submodule.span k (L.levelMonomials (n + 1)) := by
  rw [Submodule.span_le]
  intro x hx
  rw [levelMonomials_eq] at hx
  obtain ⟨a, b, ha, hb, rfl⟩ := hx
  have hsplit : L.wordS a * L.wordT b =
      L.wordS (a ++ [0]) * L.wordT (b ++ [0]) +
        L.wordS (a ++ [1]) * L.wordT (b ++ [1]) := by
    have h1 : ∀ i : Fin 2, L.wordS (a ++ [i]) * L.wordT (b ++ [i]) =
        L.wordS a * (L.s i * L.t i) * L.wordT b := by
      intro i
      rw [L.wordS_append, L.wordT_append]
      show L.wordS a * (L.s i * 1) * ((1 * L.t i) * L.wordT b) = _
      noncomm_ring
    rw [h1 0, h1 1, ← add_mul, ← mul_add, L.sum_s_mul_t, mul_one]
  rw [hsplit]
  refine Submodule.add_mem _ (Submodule.subset_span ?_)
    (Submodule.subset_span ?_) <;>
    rw [levelMonomials_eq] <;>
    exact ⟨_, _, by simp [ha], by simp [hb], rfl⟩

theorem span_levelMonomials_mono {m n : ℕ} (h : m ≤ n) :
    Submodule.span k (L.levelMonomials m) ≤
      Submodule.span k (L.levelMonomials n) := by
  induction n, h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact ih.trans (L.span_levelMonomials_le_succ n)

end Scalars

/-- A positive-degree monomial sheds one `s₀` on the right:
`s_α t_β = (s_α t_{0::β}) · s₀`. -/
theorem monomial_factor_s0 (a b : List (Fin 2)) :
    L.wordS a * L.wordT b =
      (L.wordS a * L.wordT (0 :: b)) * L.s 0 := by
  rw [L.wordT_cons]
  have ht : L.wordT b * L.t 0 * L.s 0 = L.wordT b := by
    rw [mul_assoc, t_mul_s, if_pos rfl, mul_one]
  rw [mul_assoc, mul_assoc]
  rw [← mul_assoc (L.wordT b), ht]

/-- A negative-degree monomial sheds one `t₀` on the left:
`s_α t_β = t₀ · (s_{0::α} t_β)`. -/
theorem monomial_factor_t0 (a b : List (Fin 2)) :
    L.wordS a * L.wordT b =
      L.t 0 * (L.wordS (0 :: a) * L.wordT b) := by
  rw [L.wordS_cons]
  rw [← mul_assoc, ← mul_assoc, t_mul_s, if_pos rfl, one_mul]

/-- **The elementary corner move inside the unit group**: for every
unit `u` and all `v, w`, the element
`s₀(u+vw)t₀ + s₀vt₁ + s₁wt₀ + s₁t₁` is a unit congruent to `u` modulo
the diagonal class group.  It is the depth-one corner picture of
`[[1,v],[0,1]]·diag(u,1)·[[1,0],[w,1]]`. -/
theorem exists_corner_move [Nontrivial A]
    (hdiv : ∀ x : A, x ≠ 0 → ∃ p q : A, p * x * q = 1)
    (u : Aˣ) (v w : A) :
    ∃ u' : Aˣ, (u' : A) =
      L.s 0 * ((u : A) + v * w) * L.t 0 + L.s 0 * v * L.t 1 +
        L.s 1 * w * L.t 0 + L.s 1 * L.t 1 ∧
      u' * u⁻¹ ∈ stableUnits A := by
  have hts : L.t 0 * L.s 0 = 1 := by rw [t_mul_s, if_pos rfl]
  have ht1s0 : L.t 1 * L.s 0 = 0 := by rw [t_mul_s, if_neg (by decide)]
  have ht0s1 : L.t 0 * L.s 1 = 0 := by rw [t_mul_s, if_neg (by decide)]
  have ht1s1 : L.t 1 * L.s 1 = 1 := by rw [t_mul_s, if_pos rfl]
  have hp1 : (1 : A) - L.s 0 * L.t 0 = L.s 1 * L.t 1 := by
    have h := L.sum_s_mul_t
    rw [← h]
    abel
  -- the two unipotent factors
  have hXmem : ∀ u₀ : Aˣ, (u₀ : A) = 1 + (L.s 0 * v) * L.t 1 →
      u₀ ∈ stableUnits A := fun u₀ h ↦
    mem_stableUnits_of_val_unipotent (L.s 0 * v) (L.t 1)
      (by rw [← mul_assoc, ht1s0, zero_mul]) h
  have hYmem : ∀ u₀ : Aˣ, (u₀ : A) = 1 + (L.s 1 * w) * L.t 0 →
      u₀ ∈ stableUnits A := fun u₀ h ↦
    mem_stableUnits_of_val_unipotent (L.s 1 * w) (L.t 0)
      (by rw [← mul_assoc, ht0s1, zero_mul]) h
  have hzX : L.s 0 * v * L.t 1 * (L.s 0 * v * L.t 1) = 0 := by
    rw [show L.s 0 * v * L.t 1 * (L.s 0 * v * L.t 1) =
      L.s 0 * v * (L.t 1 * L.s 0) * (v * L.t 1) from by noncomm_ring,
      ht1s0]
    noncomm_ring
  have hzY : L.s 1 * w * L.t 0 * (L.s 1 * w * L.t 0) = 0 := by
    rw [show L.s 1 * w * L.t 0 * (L.s 1 * w * L.t 0) =
      L.s 1 * w * (L.t 0 * L.s 1) * (w * L.t 0) from by noncomm_ring,
      ht0s1]
    noncomm_ring
  let X : Aˣ :=
    ⟨1 + L.s 0 * v * L.t 1, 1 - L.s 0 * v * L.t 1,
      by
        calc (1 + L.s 0 * v * L.t 1) * (1 - L.s 0 * v * L.t 1)
            = 1 - L.s 0 * v * L.t 1 * (L.s 0 * v * L.t 1) := by
              noncomm_ring
          _ = 1 := by rw [hzX, sub_zero],
      by
        calc (1 - L.s 0 * v * L.t 1) * (1 + L.s 0 * v * L.t 1)
            = 1 - L.s 0 * v * L.t 1 * (L.s 0 * v * L.t 1) := by
              noncomm_ring
          _ = 1 := by rw [hzX, sub_zero]⟩
  let Y : Aˣ :=
    ⟨1 + L.s 1 * w * L.t 0, 1 - L.s 1 * w * L.t 0,
      by
        calc (1 + L.s 1 * w * L.t 0) * (1 - L.s 1 * w * L.t 0)
            = 1 - L.s 1 * w * L.t 0 * (L.s 1 * w * L.t 0) := by
              noncomm_ring
          _ = 1 := by rw [hzY, sub_zero],
      by
        calc (1 - L.s 1 * w * L.t 0) * (1 + L.s 1 * w * L.t 0)
            = 1 - L.s 1 * w * L.t 0 * (L.s 1 * w * L.t 0) := by
              noncomm_ring
          _ = 1 := by rw [hzY, sub_zero]⟩
  set κ : Aˣ := pairKappaUnit (L.s 0) (L.t 0) hts u with hκ
  refine ⟨X * κ * Y, ?_, ?_⟩
  · have hκval : (κ : A) = L.s 0 * (u : A) * L.t 0 + L.s 1 * L.t 1 := by
      rw [hκ, pairKappaUnit_val, hp1]
    have h1 : L.s 0 * v * L.t 1 * (L.s 0 * (u : A) * L.t 0) = 0 := by
      rw [show L.s 0 * v * L.t 1 * (L.s 0 * (u : A) * L.t 0) =
        L.s 0 * v * (L.t 1 * L.s 0) * ((u : A) * L.t 0) from by
          noncomm_ring, ht1s0]
      noncomm_ring
    have h2 : L.s 0 * v * L.t 1 * (L.s 1 * L.t 1) = L.s 0 * v * L.t 1 := by
      rw [show L.s 0 * v * L.t 1 * (L.s 1 * L.t 1) =
        L.s 0 * v * (L.t 1 * L.s 1) * L.t 1 from by noncomm_ring,
        ht1s1]
      noncomm_ring
    have h3 : L.s 0 * (u : A) * L.t 0 * (L.s 1 * w * L.t 0) = 0 := by
      rw [show L.s 0 * (u : A) * L.t 0 * (L.s 1 * w * L.t 0) =
        L.s 0 * (u : A) * (L.t 0 * L.s 1) * (w * L.t 0) from by
          noncomm_ring, ht0s1]
      noncomm_ring
    have h4 : L.s 1 * L.t 1 * (L.s 1 * w * L.t 0) = L.s 1 * w * L.t 0 := by
      rw [show L.s 1 * L.t 1 * (L.s 1 * w * L.t 0) =
        L.s 1 * (L.t 1 * L.s 1) * (w * L.t 0) from by noncomm_ring,
        ht1s1]
      noncomm_ring
    have h5 : L.s 0 * v * L.t 1 * (L.s 1 * w * L.t 0) =
        L.s 0 * (v * w) * L.t 0 := by
      rw [show L.s 0 * v * L.t 1 * (L.s 1 * w * L.t 0) =
        L.s 0 * v * (L.t 1 * L.s 1) * (w * L.t 0) from by noncomm_ring,
        ht1s1]
      noncomm_ring
    show ((X : A) * (κ : A)) * (Y : A) = _
    rw [hκval]
    calc ((1 + L.s 0 * v * L.t 1) *
          (L.s 0 * (u : A) * L.t 0 + L.s 1 * L.t 1)) *
          (1 + L.s 1 * w * L.t 0)
        = (L.s 0 * (u : A) * L.t 0 + L.s 1 * L.t 1 +
            (L.s 0 * v * L.t 1 * (L.s 0 * (u : A) * L.t 0) +
              L.s 0 * v * L.t 1 * (L.s 1 * L.t 1))) *
            (1 + L.s 1 * w * L.t 0) := by noncomm_ring
      _ = (L.s 0 * (u : A) * L.t 0 + L.s 1 * L.t 1 + L.s 0 * v * L.t 1) *
            (1 + L.s 1 * w * L.t 0) := by rw [h1, h2, zero_add]
      _ = L.s 0 * (u : A) * L.t 0 + L.s 1 * L.t 1 + L.s 0 * v * L.t 1 +
            (L.s 0 * (u : A) * L.t 0 * (L.s 1 * w * L.t 0) +
              (L.s 1 * L.t 1 * (L.s 1 * w * L.t 0) +
                L.s 0 * v * L.t 1 * (L.s 1 * w * L.t 0))) := by
          noncomm_ring
      _ = L.s 0 * (u : A) * L.t 0 + L.s 1 * L.t 1 + L.s 0 * v * L.t 1 +
            (0 + (L.s 1 * w * L.t 0 + L.s 0 * (v * w) * L.t 0)) := by
          rw [h3, h4, h5]
      _ = L.s 0 * ((u : A) + v * w) * L.t 0 + L.s 0 * v * L.t 1 +
            L.s 1 * w * L.t 0 + L.s 1 * L.t 1 := by noncomm_ring
  · have hXm : X ∈ stableUnits A := hXmem X (by
      show (1 : A) + L.s 0 * v * L.t 1 = 1 + L.s 0 * v * L.t 1
      rw [mul_assoc])
    have hYm : Y ∈ stableUnits A := hYmem Y (by
      show (1 : A) + L.s 1 * w * L.t 0 = 1 + L.s 1 * w * L.t 0
      rw [mul_assoc])
    have hκm : κ * u⁻¹ ∈ stableUnits A :=
      pairKappaUnit_mul_inv_mem_stableUnits (L.s 0) (L.t 0) hts hdiv u
    have hconj : (u * Y * u⁻¹ : Aˣ) ∈ stableUnits A :=
      (stableUnits_normal (R := A)).conj_mem Y hYm u
    have hrw : X * κ * Y * u⁻¹ =
        X * ((κ * u⁻¹) * (u * Y * u⁻¹)) := by group
    rw [hrw]
    exact mul_mem hXm (mul_mem hκm hconj)

end LeavittFamily
end NonsoficGroupsExist
