import NonsoficGroupsExist.KOne.GradedIndependence
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Algebra.Polynomial.Monomial

/-!
# Graded independence over every field

Base change to the rational function field: the coefficient extension
`L_k(1,2) → L_{k(X)}(1,2)` is injective by simplicity and carries the
degree filtration to the degree filtration, so the graded independence
proved over infinite fields descends to arbitrary — in particular
finite — ground fields.
-/

namespace NonsoficGroupsExist
namespace BinaryLeavitt

variable (k : Type) [Field k]

noncomputable instance baseChangeAlgebra :
    Algebra k (BinaryLeavittAlgebra (RatFunc k)) :=
  RingHom.toAlgebra' ((algebraMap (RatFunc k)
      (BinaryLeavittAlgebra (RatFunc k))).comp (algebraMap k (RatFunc k)))
    (fun c x ↦ Algebra.commutes (algebraMap k (RatFunc k) c) x)

/-- Coefficient extension along `k → k(X)`. -/
noncomputable def baseChange :
    BinaryLeavittAlgebra k →ₐ[k] BinaryLeavittAlgebra (RatFunc k) :=
  lift (family (RatFunc k))

theorem baseChange_s (i : Fin 2) :
    baseChange k ((family k).s i) = (family (RatFunc k)).s i := by
  fin_cases i <;>
    simp [baseChange, family, LeavittFamily.s, s0, s1, t0, t1]

theorem baseChange_t (i : Fin 2) :
    baseChange k ((family k).t i) = (family (RatFunc k)).t i := by
  fin_cases i <;>
    simp [baseChange, family, LeavittFamily.t, s0, s1, t0, t1]

theorem baseChange_wordS (a : List (Fin 2)) :
    baseChange k ((family k).wordS a) =
      (family (RatFunc k)).wordS a := by
  induction a with
  | nil => simp
  | cons i a ih =>
      rw [LeavittFamily.wordS_cons, map_mul, ih, baseChange_s,
        LeavittFamily.wordS_cons]

theorem baseChange_wordT (b : List (Fin 2)) :
    baseChange k ((family k).wordT b) =
      (family (RatFunc k)).wordT b := by
  induction b with
  | nil => simp
  | cons i b ih =>
      rw [LeavittFamily.wordT_cons, map_mul, ih, baseChange_t,
        LeavittFamily.wordT_cons]

/-- Base change is injective, by simplicity of the source. -/
theorem baseChange_injective :
    Function.Injective (baseChange k) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hne
  obtain ⟨p, q, hpq⟩ := exists_mul_mul_eq_one k hne
  have h1 := congrArg (baseChange k) hpq
  rw [map_mul, map_mul, hx, mul_zero, zero_mul, map_one] at h1
  exact zero_ne_one h1

/-- Base change carries degree windows to degree windows. -/
theorem baseChange_mem_span_degree {lo hi : ℤ} {x : BinaryLeavittAlgebra k}
    (hx : x ∈ Submodule.span k ((family k).degreeMonomials lo hi)) :
    baseChange k x ∈ Submodule.span (RatFunc k)
      ((family (RatFunc k)).degreeMonomials lo hi) := by
  induction hx using Submodule.span_induction with
  | mem x hxmem =>
      obtain ⟨a, b, hl, hh, rfl⟩ := hxmem
      rw [map_mul, baseChange_wordS, baseChange_wordT]
      exact Submodule.subset_span ⟨a, b, hl, hh, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
      rw [Algebra.smul_def r x, map_mul, AlgHom.commutes]
      have h3 := Submodule.smul_mem (Submodule.span (RatFunc k)
        ((family (RatFunc k)).degreeMonomials lo hi))
        (algebraMap k (RatFunc k) r) hx
      rwa [Algebra.smul_def] at h3

noncomputable instance : Infinite (RatFunc k) :=
  Infinite.of_injective (algebraMap (Polynomial k) (RatFunc k))
    (IsFractionRing.injective _ _)

/-- **Graded independence over every field**: a vanishing finite sum
of pure-degree elements of the binary Leavitt algebra has all
components zero. -/
theorem graded_independence_all (D : Finset ℤ)
    (x : ℤ → BinaryLeavittAlgebra k)
    (hx : ∀ d ∈ D, x d ∈
      Submodule.span k ((family k).degreeMonomials d d))
    (hsum : ∑ d ∈ D, x d = 0) : ∀ d ∈ D, x d = 0 := by
  have hker := graded_independence (RatFunc k) D
    (fun d ↦ baseChange k (x d))
    (fun d hd ↦ baseChange_mem_span_degree k (hx d hd))
    (by rw [← map_sum, hsum, map_zero])
  intro d hd
  apply baseChange_injective k
  rw [map_zero]
  exact hker d hd

end BinaryLeavitt
end NonsoficGroupsExist
