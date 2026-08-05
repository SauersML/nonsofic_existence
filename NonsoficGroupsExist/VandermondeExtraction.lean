import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Polynomial.Roots

/-!
# Vandermonde extraction over an infinite field

If finitely many vectors satisfy `∑ c^d • v d = 0` for every unit `c`
of an infinite field — with integer exponents `d` — then each vector
vanishes: a coordinate functional turns the family of relations into a
polynomial with infinitely many roots, whose coefficients are the
coordinates.  This is the separation engine for the graded
independence of the Leavitt algebra.
-/

namespace NonsoficGroupsExist

open Module

theorem eq_zero_of_forall_units_zpow_smul {K V : Type*} [Field K]
    [Infinite K] [AddCommGroup V] [Module K V] (D : Finset ℤ)
    (v : ℤ → V)
    (h : ∀ c : Kˣ, ∑ d ∈ D, ((c ^ d : Kˣ) : K) • v d = 0) :
    ∀ d ∈ D, v d = 0 := by
  intro d₀ hd₀
  by_contra hne
  have hD : D.Nonempty := ⟨d₀, hd₀⟩
  set m := D.min' hD with hm
  set e : ℤ → ℕ := fun d ↦ (d - m).toNat with he
  have hs : LinearIndepOn K id ({v d₀} : Set V) :=
    (linearIndepOn_singleton_iff K).mpr hne
  set b := Basis.extend hs with hb
  have hmem : v d₀ ∈ hs.extend (Set.subset_univ _) :=
    Basis.subset_extend hs (Set.mem_singleton _)
  set i₀ : ↥(hs.extend (Set.subset_univ _)) := ⟨v d₀, hmem⟩ with hi₀
  set φ := b.coord i₀ with hφdef
  have hφ : φ (v d₀) = 1 := by
    have hbi : b i₀ = v d₀ := Basis.extend_apply_self hs i₀
    have h2 : φ (b i₀) = 1 := by
      rw [hφdef, Basis.coord_apply, Basis.repr_self,
        Finsupp.single_eq_same]
    rwa [congrArg φ hbi] at h2
  set p : Polynomial K :=
    ∑ d ∈ D, Polynomial.C (φ (v d)) * Polynomial.X ^ e d with hp
  have hroots : ∀ c : Kˣ, p.eval (c : K) = 0 := by
    intro c
    have h1 := congrArg φ (h c)
    rw [map_sum, map_zero] at h1
    simp only [map_smul] at h1
    have hzp : ∀ d ∈ D,
        ((c ^ d : Kˣ) : K) = (c : K) ^ m * (c : K) ^ e d := by
      intro d hd
      have hdm : m ≤ d := D.min'_le d hd
      have hcast : ((c ^ d : Kˣ) : K) = (c : K) ^ d := by
        norm_cast
      have hde : (c : K) ^ d = (c : K) ^ m * (c : K) ^ (e d : ℤ) := by
        rw [← zpow_add₀ (Units.ne_zero c)]
        congr 1
        simp only [he]
        omega
      rw [hcast, hde, zpow_natCast]
    have hS : (c : K) ^ m *
        (∑ d ∈ D, φ (v d) * (c : K) ^ e d) = 0 := by
      rw [Finset.mul_sum, ← h1]
      refine Finset.sum_congr rfl fun d hd ↦ ?_
      rw [smul_eq_mul, hzp d hd]
      ring
    have hSz : (∑ d ∈ D, φ (v d) * (c : K) ^ e d) = 0 :=
      (mul_eq_zero.mp hS).resolve_left
        (zpow_ne_zero m (Units.ne_zero c))
    rw [hp, Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    exact hSz
  have hp0 : p = 0 := by
    refine p.eq_zero_of_infinite_isRoot ?_
    have hinf : ({x : K | x ≠ 0}).Infinite := by
      have := (Set.infinite_univ (α := K)).sdiff (Set.finite_singleton 0)
      convert this using 1
      ext x
      simp
    refine hinf.mono fun x hx ↦ ?_
    exact hroots (Units.mk0 x hx)
  have hc0 : p.coeff (e d₀) = 0 := by rw [hp0, Polynomial.coeff_zero]
  have hcp : p.coeff (e d₀) = φ (v d₀) := by
    rw [hp, Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single d₀]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl,
        mul_one]
    · intro d hd hdne
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg,
        mul_zero]
      intro hee
      apply hdne
      have h1 : m ≤ d := D.min'_le d hd
      have h2 : m ≤ d₀ := D.min'_le d₀ hd₀
      simp only [he] at hee
      omega
    · intro hd
      exact absurd hd₀ hd
  rw [hcp, hφ] at hc0
  exact one_ne_zero hc0

end NonsoficGroupsExist
