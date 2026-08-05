import NonsoficGroupsExist.GaussianPositiveDefinite
import NonsoficGroupsExist.KazhdanGNS
import NonsoficGroupsExist.KazhdanFixedSpace
import NonsoficGroupsExist.HilbertCircumcenter

/-!
# Delorme's theorem: property (T) fixes affine isometric actions

The Delorme direction of the Delorme–Guichardet theorem: a group with
Kazhdan's property `(T)` fixes a point in every affine isometric action
on a real Hilbert space.  The proof is quantitative and factors through
an abstract boundedness principle: any nonnegative function `ψ`
vanishing at the identity whose Gaussians `exp (-t * ψ)` are all
positive-definite is bounded on a Kazhdan group
(`bounded_of_gaussian_isPositiveDefinite`).  Indeed the GNS
representation (`KazhdanGNS.representation`) of the small-`t` Gaussian
carries a cyclic vector whose displacement is controlled by `t` on the
Kazhdan set, so the Kazhdan spectral gap forces its moving component
below any threshold, which bounds the Gaussian below uniformly on the
group.  For a cocycle `b` the Gaussians of `ψ = ‖b ·‖ ^ 2` are
positive-definite (`GaussianPositiveDefinite`), so `b` is bounded, and a
bounded orbit has a fixed circumcenter
(`Circumcenter.exists_fixed_of_bounded_orbit`).  The abstract form is
stated separately because Shalom's finite-presentability argument
applies it to an ultralimit function that is not presented as a cocycle.
-/

namespace NonsoficGroupsExist
namespace Delorme

universe u v

variable {G : Type u} [Group G]

section Cocycle

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A cocycle for an orthogonal representation: the translation parts of
an affine isometric action `x ↦ π g x + b g`. -/
def IsCocycle (π : G →* (E ≃ₗᵢ[ℝ] E)) (b : G → E) : Prop :=
  ∀ g h : G, b (g * h) = b g + π g (b h)

namespace IsCocycle

variable {π : G →* (E ≃ₗᵢ[ℝ] E)} {b : G → E}

theorem apply_one (hb : IsCocycle π b) : b 1 = 0 := by
  have h := hb 1 1
  rw [one_mul] at h
  have h0 : b 1 + π 1 (b 1) = b 1 + 0 := by
    rw [add_zero]
    exact h.symm
  have h1 := add_left_cancel h0
  simpa using h1

theorem apply_inv (hb : IsCocycle π b) (g : G) :
    b g⁻¹ = -(π g⁻¹ (b g)) := by
  have h := hb g⁻¹ g
  rw [inv_mul_cancel, hb.apply_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-- The orbit-map identity feeding the Gaussian kernel. -/
theorem norm_inv_mul (hb : IsCocycle π b) (g h : G) :
    ‖b (g⁻¹ * h)‖ = ‖b h - b g‖ := by
  have hkey : b (g⁻¹ * h) = π g⁻¹ (b h - b g) := by
    rw [hb g⁻¹ h, hb.apply_inv g, map_sub]
    abel
  rw [hkey]
  exact (π g⁻¹).norm_map _

end IsCocycle

end Cocycle

section Bound

open KazhdanGNS KazhdanFixedSpace

/-- **The Gaussian boundedness principle.**  On a group with a Kazhdan
pair, any nonnegative function `ψ` vanishing at the identity all of
whose Gaussians `exp (-t * ψ)` are positive-definite is bounded: the GNS
cyclic vector of the small-`t` Gaussian is almost invariant on the
Kazhdan set, so its moving component is small, so the Gaussian is at
least `1 / 2` everywhere. -/
theorem bounded_of_gaussian_isPositiveDefinite
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, u} G Q ε)
    (ψ : G → ℝ) (hψ1 : ψ 1 = 0) (hψnn : ∀ g : G, 0 ≤ ψ g)
    (hpd : ∀ t : ℝ, 0 < t →
      KazhdanFiniteModel.IsPositiveDefinite
        (fun g ↦ Real.exp (-t * ψ g))) :
    ∃ R : ℝ, ∀ g : G, ψ g ≤ R := by
  classical
  have hε := hQ.1
  set B : ℝ := (∑ q ∈ Q, ψ q) + 1 with hB
  have hsumnn : 0 ≤ ∑ q ∈ Q, ψ q :=
    Finset.sum_nonneg fun q _ ↦ hψnn q
  have hBpos : 0 < B := by
    rw [hB]
    linarith
  have hBq : ∀ q ∈ Q, ψ q ≤ B := by
    intro q hq
    have hle := Finset.single_le_sum (f := fun q ↦ ψ q)
      (fun i _ ↦ hψnn i) hq
    rw [hB]
    linarith
  set t : ℝ := ε ^ 2 / (32 * B) with ht
  have htpos : 0 < t := by
    rw [ht]
    exact div_pos (pow_pos hε 2) (by linarith)
  -- The Gaussian positive-definite function and its GNS data.
  set p : PositiveDefiniteFunction G :=
    ⟨fun g ↦ Real.exp (-t * ψ g), hpd t htpos⟩ with hp
  have hpapply : ∀ g : G, p g = Real.exp (-t * ψ g) := fun g ↦ rfl
  set ρ := representation p with hρ
  set ξ := kernelVector p 1 with hξ
  have hξsq : inner ℝ ξ ξ = 1 := by
    rw [hξ, inner_kernelVector]
    show Real.exp (-t * ψ (1⁻¹ * 1)) = 1
    rw [inv_one, one_mul, hψ1]
    simp
  have hnormξsq : ‖ξ‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    exact hξsq
  -- Displacement of the cyclic vector.
  have hdisp : ∀ q : G, ‖ρ q ξ - ξ‖ ^ 2 = 2 - 2 * p q := by
    intro q
    have hρξ : ρ q ξ = kernelVector p q := by
      rw [hρ, hξ, representation_kernelVector, mul_one]
    have hinner : inner ℝ ξ (kernelVector p q) = p q := by
      rw [hξ, inner_kernelVector, inv_one, one_mul]
    have hkq : ‖kernelVector p q‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq, inner_kernelVector, inv_mul_cancel]
      show Real.exp (-t * ψ 1) = 1
      rw [hψ1]
      simp
    rw [norm_sub_rev, norm_sub_sq_real, hρξ, hinner, hnormξsq, hkq]
    ring
  have hdispQ : ∀ q ∈ Q, ‖ρ q ξ - ξ‖ ^ 2 ≤ 2 * t * B := by
    intro q hq
    rw [hdisp q]
    have hple : 1 - t * ψ q ≤ p q := by
      rw [hpapply q]
      have hexp := Real.add_one_le_exp (-t * ψ q)
      linarith
    have htB : t * ψ q ≤ t * B :=
      mul_le_mul_of_nonneg_left (hBq q hq) htpos.le
    linarith
  -- The moving component of the cyclic vector.
  set m := subgroupMovingProjection ρ ⊤ ξ with hm
  have hPfix : ∀ s : G,
      ρ s (fixedProjection ρ ⊤ ξ : HilbertSpace p) =
        (fixedProjection ρ ⊤ ξ : HilbertSpace p) :=
    fun s ↦ fixedProjection_mem ρ ⊤ ξ ⟨s, Subgroup.mem_top s⟩
  have hdecomp : ξ = (fixedProjection ρ ⊤ ξ : HilbertSpace p) + m := by
    rw [hm, subgroupMovingProjection_eq_sub_fixedProjection]
    abel
  have hsplit : ∀ q : G, ρ q m - m = ρ q ξ - ξ := by
    intro q
    conv_rhs => rw [hdecomp]
    rw [map_add, hPfix q]
    abel
  -- Kazhdan spectral gap on the moving subspace.
  have hmsq : ε ^ 2 * ‖m‖ ^ 2 ≤ 2 * t * B := by
    by_cases hm0 : m = 0
    · rw [hm0, norm_zero]
      have h2tB : 0 ≤ 2 * t * B :=
        mul_nonneg (mul_nonneg (by norm_num) htpos.le) hBpos.le
      nlinarith
    · have hmem : m ∈ movingSubspace ρ := by
        rw [hm]
        exact subgroupMovingProjection_mem ρ ⊤ ξ
      letI : CompleteSpace (movingSubspace ρ) :=
        (Submodule.isClosed_orthogonal _).completeSpace_coe
      set x : movingSubspace ρ := ⟨m, hmem⟩ with hx
      have hx0 : x ≠ 0 := by
        intro hc
        apply hm0
        have hval := congrArg Subtype.val hc
        simpa [hx] using hval
      obtain ⟨q, hq, hqmove⟩ :=
        IsKazhdanPair.exists_moved_mul_norm_of_noInvariant hQ
          (movingRepresentation ρ)
          (movingRepresentation_hasNoInvariantVectors ρ) x hx0
      have hxnorm : ‖x‖ = ‖m‖ := rfl
      have hcoe : ((movingRepresentation ρ q x - x : movingSubspace ρ) :
          HilbertSpace p) = ρ q m - m := by
        simp [hx]
      have htransfer : ‖movingRepresentation ρ q x - x‖ = ‖ρ q ξ - ξ‖ := by
        rw [show ‖movingRepresentation ρ q x - x‖ =
          ‖((movingRepresentation ρ q x - x : movingSubspace ρ) :
            HilbertSpace p)‖ from rfl, hcoe, hsplit q]
      rw [hxnorm, htransfer] at hqmove
      have hsq := mul_self_le_mul_self
        (mul_nonneg hε.le (norm_nonneg m)) hqmove
      have hd2 := hdispQ q hq
      nlinarith [norm_nonneg (ρ q ξ - ξ)]
  -- The moving component is below one quarter in square.
  have h2tB : 2 * t * B = ε ^ 2 / 16 := by
    rw [ht]
    field_simp
    ring
  have hm16 : ‖m‖ ^ 2 ≤ 1 / 16 := by
    rw [h2tB] at hmsq
    nlinarith [pow_pos hε 2]
  -- Uniform lower bound for the Gaussian.
  have hcross1 : ∀ g : G,
      inner ℝ (fixedProjection ρ ⊤ ξ : HilbertSpace p) (ρ g m) = 0 := by
    intro g
    apply Submodule.inner_right_of_mem_orthogonal
      (K := fixedSubspace ρ ⊤)
    · exact (fixedProjection ρ ⊤ ξ).property
    · apply map_mem_fixedSubspace_orthogonal_of_normal ρ ⊤ g
      rw [hm]
      exact subgroupMovingProjection_mem ρ ⊤ ξ
  have hcross2 : inner ℝ m
      (fixedProjection ρ ⊤ ξ : HilbertSpace p) = 0 := by
    rw [real_inner_comm]
    rw [hm]
    exact fixedProjection_inner_movingProjection ρ ⊤ ξ
  have hP : ‖(fixedProjection ρ ⊤ ξ : HilbertSpace p)‖ ^ 2 =
      1 - ‖m‖ ^ 2 := by
    have hpyth := norm_sq_fixedProjection_add_movingProjection ρ ⊤ ξ
    rw [hnormξsq, ← hm] at hpyth
    linarith
  have hlower : ∀ g : G, 1 - 2 * ‖m‖ ^ 2 ≤ p g := by
    intro g
    have hpgEq : p g = inner ℝ ξ (ρ g ξ) := by
      rw [hρ, hξ, representation_kernelVector, mul_one,
        inner_kernelVector, inv_one, one_mul]
    have hexpand : inner ℝ ξ (ρ g ξ) =
        ‖(fixedProjection ρ ⊤ ξ : HilbertSpace p)‖ ^ 2 +
          inner ℝ m (ρ g m) := by
      conv_lhs => rw [hdecomp]
      rw [map_add, hPfix g, inner_add_left, inner_add_right,
        inner_add_right, hcross1 g, hcross2,
        real_inner_self_eq_norm_sq]
      ring
    rw [hpgEq, hexpand, hP]
    have hcs := abs_real_inner_le_norm m (ρ g m)
    rw [(ρ g).norm_map] at hcs
    have hneg := neg_abs_le (inner ℝ m (ρ g m))
    nlinarith
  -- Invert the exponential.
  refine ⟨Real.log 2 / t, fun g ↦ ?_⟩
  have hpg : (1 : ℝ) / 2 ≤ Real.exp (-t * ψ g) := by
    have hlow := hlower g
    rw [hpapply g] at hlow
    linarith [hm16]
  have h12 : Real.exp (Real.log (1 / 2)) ≤ Real.exp (-t * ψ g) := by
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 1 / 2)]
    exact hpg
  have hlog := Real.exp_le_exp.mp h12
  rw [show Real.log (1 / 2 : ℝ) = -Real.log 2 from by
    rw [one_div, Real.log_inv]] at hlog
  rw [le_div_iff₀ htpos]
  nlinarith

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Delorme's boundedness estimate**: under a Kazhdan pair, every
isometric cocycle is bounded. -/
theorem norm_sq_cocycle_bounded_of_isKazhdanPair
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, u} G Q ε)
    (π : G →* (E ≃ₗᵢ[ℝ] E)) {b : G → E} (hb : IsCocycle π b) :
    ∃ R : ℝ, ∀ g : G, ‖b g‖ ^ 2 ≤ R := by
  apply bounded_of_gaussian_isPositiveDefinite hQ
    (fun g ↦ ‖b g‖ ^ 2)
  · rw [hb.apply_one, norm_zero]
    ring
  · exact fun g ↦ sq_nonneg _
  · exact fun t ht ↦
      GaussianKernel.isPositiveDefinite_exp_neg_norm_sq b
        (fun g h ↦ hb.norm_inv_mul g h) ht.le

end Bound

section FixedPoint

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Delorme's theorem, Kazhdan-pair form**: an affine isometric action
of a group with a Kazhdan pair on a complete real Hilbert space has a
fixed point. -/
theorem exists_fixed_point_of_isKazhdanPair [CompleteSpace E]
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, u} G Q ε)
    (π : G →* (E ≃ₗᵢ[ℝ] E)) {b : G → E} (hb : IsCocycle π b) :
    ∃ x : E, ∀ g : G, π g x + b g = x := by
  obtain ⟨R, hR⟩ := norm_sq_cocycle_bounded_of_isKazhdanPair hQ π hb
  set φ : G → E → E := fun g x ↦ π g x + b g with hφ
  have hiso : ∀ g, Isometry (φ g) := by
    intro g
    apply Isometry.of_dist_eq
    intro x y
    simp only [hφ, dist_eq_norm]
    rw [show π g x + b g - (π g y + b g) = π g (x - y) from by
      rw [map_sub]; abel, (π g).norm_map]
  have hmul : ∀ g h x, φ (g * h) x = φ g (φ h x) := by
    intro g h x
    simp only [hφ]
    rw [hb g h, map_mul π g h]
    have hcomp : (π g * π h) x = π g (π h x) := rfl
    rw [hcomp, map_add]
    abel
  have hone : ∀ x : E, φ 1 x = x := by
    intro x
    simp only [hφ]
    rw [hb.apply_one, map_one, add_zero]
    simp
  have hRnorm : ∀ g : G, ‖b g‖ ≤ max 1 R := by
    intro g
    rcases le_total ‖b g‖ 1 with h | h
    · exact h.trans (le_max_left _ _)
    · have hself : ‖b g‖ ≤ ‖b g‖ ^ 2 := by nlinarith
      exact (hself.trans (hR g)).trans (le_max_right _ _)
  have hbdd : Bornology.IsBounded (Set.range fun g ↦ φ g 0) := by
    apply (Metric.isBounded_closedBall (x := (0 : E))
      (r := max 1 R)).subset
    rintro y ⟨g, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have hval : φ g 0 = b g := by
      simp only [hφ]
      rw [map_zero, zero_add]
    rw [hval]
    exact hRnorm g
  obtain ⟨c, hc⟩ := Circumcenter.exists_fixed_of_bounded_orbit
    φ hiso hmul hone 0 hbdd
  exact ⟨c, fun g ↦ hc g⟩

/-- **Delorme's theorem**: a group with Kazhdan's property `(T)` fixes a
point in every affine isometric action on a complete real Hilbert
space. -/
theorem exists_fixed_point_of_hasKazhdanPropertyT [CompleteSpace E]
    (hT : HasKazhdanPropertyT.{u, u} G)
    (π : G →* (E ≃ₗᵢ[ℝ] E)) {b : G → E} (hb : IsCocycle π b) :
    ∃ x : E, ∀ g : G, π g x + b g = x := by
  obtain ⟨Q, ε, hQ⟩ := hT
  exact exists_fixed_point_of_isKazhdanPair hQ π hb

end FixedPoint

end Delorme
end NonsoficGroupsExist
