import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.FieldTheory.Finiteness

/-!
# Character masses of finite prime-exponent orthogonal actions

The characteristic-two Fourier machinery decomposes a real orthogonal
representation of an elementary abelian `2`-group into simultaneous `±1`
eigenspaces.  In odd characteristic the irreducible real pieces are rotation
planes, so sign eigenspaces do not exist; the correct replacement is the
family of character masses: the discrete Fourier coefficients of the
autocorrelation function `v ↦ ⟪z, ρ v z⟫` over the dual of the acting
`ZMod p`-vector space.  This file proves the four foundational facts of that
calculus, for every prime `p`:

* positivity — each mass is a genuine sum of two squared component norms;
* conservation — the masses of `z` sum to `‖z‖ ^ 2`;
* inversion — the autocorrelation is recovered from the masses;
* displacement — `‖ρ w z - z‖ ^ 2` is the mass-weighted sum of
  `2 * (1 - Re χ(w))`.

The displacement identity is what converts small generator displacement into
concentration of mass at characters vanishing on the generator, which is the
engine of the finite-stage relative-property-`(T)` argument.
-/

namespace NonsoficGroupsExist

namespace PrimeCharacterMass

open Finset

variable {p : ℕ} [Fact p.Prime]

instance (priority := 90) : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

/-- The standard complex character value of a `ZMod p` element. -/
noncomputable def weight (m : ZMod p) : ℂ := ZMod.stdAddChar m

theorem weight_zero : weight (0 : ZMod p) = 1 :=
  AddChar.map_zero_eq_one _

theorem weight_add (a b : ZMod p) :
    weight (a + b) = weight a * weight b :=
  AddChar.map_add_eq_mul _ a b

theorem weight_ne_one {m : ZMod p} (hm : m ≠ 0) : weight m ≠ 1 := by
  intro h
  apply hm
  apply ZMod.injective_stdAddChar (N := p)
  rw [show ZMod.stdAddChar (0 : ZMod p) = 1 from AddChar.map_zero_eq_one _]
  exact h

theorem norm_weight (m : ZMod p) : ‖weight m‖ = 1 := by
  rw [weight, ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

theorem conj_weight (m : ZMod p) :
    (starRingEnd ℂ) (weight m) = weight (-m) := by
  have hmul : weight m * weight (-m) = 1 := by
    rw [← weight_add, add_neg_cancel, weight_zero]
  have hinv : weight (-m) = (weight m)⁻¹ :=
    eq_inv_of_mul_eq_one_right hmul
  rw [hinv, Complex.inv_def, Complex.normSq_eq_norm_sq, norm_weight]
  simp

/-- The product of real parts, resolved through the character algebra. -/
theorem weight_re_mul_re (a b : ZMod p) :
    (weight a).re * (weight b).re =
      ((weight (a - b)).re + (weight (a + b)).re) / 2 := by
  have h1 : weight (a - b) = weight a * (starRingEnd ℂ) (weight b) := by
    rw [conj_weight, ← weight_add, sub_eq_add_neg]
  have h2 : weight (a + b) = weight a * weight b := weight_add a b
  rw [h1, h2]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The cosine-difference resolution used for the component expansion. -/
theorem weight_re_mul_re_add_im_mul_im (a b : ZMod p) :
    (weight a).re * (weight b).re + (weight a).im * (weight b).im =
      (weight (a - b)).re := by
  have h1 : weight (a - b) = weight a * (starRingEnd ℂ) (weight b) := by
    rw [conj_weight, ← weight_add, sub_eq_add_neg]
  rw [h1]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

variable {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Fintype V]
variable [DecidableEq V]

noncomputable instance : Fintype (Module.Dual (ZMod p) V) := by
  haveI : Finite (Module.Dual (ZMod p) V) :=
    Finite.of_injective (fun φ ↦ (φ : V → ZMod p)) DFunLike.coe_injective
  exact Fintype.ofFinite _

omit [DecidableEq V] in
/-- The dual of a finite `ZMod p`-vector space has the same cardinality. -/
theorem card_dual :
    Fintype.card (Module.Dual (ZMod p) V) = Fintype.card V := by
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  rw [Module.card_eq_pow_finrank (K := ZMod p)
      (V := Module.Dual (ZMod p) V),
    Module.card_eq_pow_finrank (K := ZMod p) (V := V),
    Subspace.dual_finrank_eq]

/-- Orthogonality over the dual: the character sum at a point detects
zero. -/
theorem sum_dual_weight (a : V) :
    ∑ φ : Module.Dual (ZMod p) V, weight (φ a) =
      if a = 0 then (Fintype.card V : ℂ) else 0 := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [weight_zero, card_dual]
  · rw [if_neg ha]
    obtain ⟨φ₀, hφ₀⟩ : ∃ φ₀ : Module.Dual (ZMod p) V, φ₀ a ≠ 0 := by
      by_contra hall
      push Not at hall
      exact ha ((Module.forall_dual_apply_eq_zero_iff (ZMod p) a).1 hall)
    have hreindex :
        ∑ φ : Module.Dual (ZMod p) V, weight ((φ + φ₀) a) =
          ∑ φ : Module.Dual (ZMod p) V, weight (φ a) :=
      Fintype.sum_equiv (Equiv.addRight φ₀) _ _ (fun φ ↦ rfl)
    have hshift :
        ∑ φ : Module.Dual (ZMod p) V, weight ((φ + φ₀) a) =
          (∑ φ : Module.Dual (ZMod p) V, weight (φ a)) * weight (φ₀ a) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro φ _
      rw [LinearMap.add_apply, weight_add]
    have hzero :
        (∑ φ : Module.Dual (ZMod p) V, weight (φ a)) *
          (1 - weight (φ₀ a)) = 0 := by
      rw [mul_sub, mul_one, ← hshift, hreindex, sub_self]
    rcases mul_eq_zero.1 hzero with h | h
    · exact h
    · exact absurd (sub_eq_zero.1 h).symm (weight_ne_one hφ₀)

/-- Real-part form of the dual orthogonality. -/
theorem sum_dual_weight_re (a : V) :
    ∑ φ : Module.Dual (ZMod p) V, (weight (φ a)).re =
      if a = 0 then (Fintype.card V : ℝ) else 0 := by
  have h := congrArg Complex.re (sum_dual_weight (p := p) a)
  rw [Complex.re_sum] at h
  rcases eq_or_ne a 0 with rfl | ha
  · simpa using h
  · simpa [ha] using h

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (ρ : V → (E ≃ₗᵢ[ℝ] E))

/-- The character mass of a vector at a dual functional: the Fourier
coefficient of the autocorrelation function of the orbit. -/
noncomputable def mass (χ : Module.Dual (ZMod p) V) (z : E) : ℝ :=
  (Fintype.card V : ℝ)⁻¹ *
    ∑ v : V, (weight (χ v)).re * inner ℝ z (ρ v z)

section Action

variable (hρ : ∀ v w : V, ρ (v + w) = ρ v * ρ w)

include hρ

omit [Module (ZMod p) V] [Fintype V] [DecidableEq V] in
theorem action_zero : ρ 0 = 1 := by
  have h := hρ 0 0
  rw [add_zero] at h
  calc
    ρ 0 = ρ 0 * ρ 0 * (ρ 0)⁻¹ := by group
    _ = ρ 0 * (ρ 0)⁻¹ := by rw [← h]
    _ = 1 := by group

omit [Module (ZMod p) V] [Fintype V] [DecidableEq V] in
theorem action_neg (v : V) : ρ (-v) = (ρ v)⁻¹ := by
  have h : ρ (-v) * ρ v = 1 := by
    rw [← hρ, neg_add_cancel, action_zero ρ hρ]
  exact eq_inv_of_mul_eq_one_left h

omit [Module (ZMod p) V] [Fintype V] [DecidableEq V] in
/-- The autocorrelation is an even function. -/
theorem autocorrelation_neg (z : E) (v : V) :
    inner ℝ z (ρ (-v) z) = inner ℝ z (ρ v z) := by
  calc
    inner ℝ z (ρ (-v) z) = inner ℝ (ρ v z) (ρ v (ρ (-v) z)) :=
      ((ρ v).inner_map_map z (ρ (-v) z)).symm
    _ = inner ℝ (ρ v z) z := by
      rw [show ρ v (ρ (-v) z) = (ρ v * ρ (-v)) z from rfl, ← hρ,
        add_neg_cancel, action_zero ρ hρ]
      rfl
    _ = inner ℝ z (ρ v z) := real_inner_comm _ _

omit [Module (ZMod p) V] [Fintype V] [DecidableEq V] in
/-- The two-point correlation depends only on the difference. -/
theorem inner_action_action (z : E) (v w : V) :
    inner ℝ (ρ v z) (ρ w z) = inner ℝ z (ρ (w - v) z) := by
  calc
    inner ℝ (ρ v z) (ρ w z) =
        inner ℝ (ρ (-v) (ρ v z)) (ρ (-v) (ρ w z)) :=
      ((ρ (-v)).inner_map_map _ _).symm
    _ = inner ℝ z (ρ (w - v) z) := by
      rw [show ρ (-v) (ρ v z) = (ρ (-v) * ρ v) z from rfl, ← hρ,
        neg_add_cancel, action_zero ρ hρ,
        show ρ (-v) (ρ w z) = (ρ (-v) * ρ w) z from rfl, ← hρ]
      rw [show -v + w = w - v by abel]
      rfl

omit [DecidableEq V] in
/-- **Positivity**: each mass is the squared norm of the cosine component
plus the squared norm of the sine component. -/
theorem mass_eq_norm_sq_add_norm_sq (χ : Module.Dual (ZMod p) V) (z : E) :
    mass ρ χ z =
      ‖(Fintype.card V : ℝ)⁻¹ •
          ∑ v : V, (weight (χ v)).re • ρ v z‖ ^ 2 +
        ‖(Fintype.card V : ℝ)⁻¹ •
          ∑ v : V, (weight (χ v)).im • ρ v z‖ ^ 2 := by
  have hcard : ((Fintype.card V : ℝ)) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hre : ‖(Fintype.card V : ℝ)⁻¹ •
      ∑ v : V, (weight (χ v)).re • ρ v z‖ ^ 2 =
    (Fintype.card V : ℝ)⁻¹ ^ 2 * ∑ v : V, ∑ w : V,
      (weight (χ v)).re * (weight (χ w)).re *
        inner ℝ z (ρ (w - v) z) := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      ← real_inner_self_eq_norm_sq, sum_inner]
    congr 1
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    rw [real_inner_smul_left, real_inner_smul_right,
      inner_action_action ρ hρ]
    ring
  have him : ‖(Fintype.card V : ℝ)⁻¹ •
      ∑ v : V, (weight (χ v)).im • ρ v z‖ ^ 2 =
    (Fintype.card V : ℝ)⁻¹ ^ 2 * ∑ v : V, ∑ w : V,
      (weight (χ v)).im * (weight (χ w)).im *
        inner ℝ z (ρ (w - v) z) := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      ← real_inner_self_eq_norm_sq, sum_inner]
    congr 1
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    rw [real_inner_smul_left, real_inner_smul_right,
      inner_action_action ρ hρ]
    ring
  rw [hre, him, ← mul_add, ← Finset.sum_add_distrib]
  have hinner : ∀ v : V, ((∑ w : V,
      (weight (χ v)).re * (weight (χ w)).re *
        inner ℝ z (ρ (w - v) z)) +
      ∑ w : V,
        (weight (χ v)).im * (weight (χ w)).im *
          inner ℝ z (ρ (w - v) z)) =
      ∑ u : V, (weight (χ u)).re * inner ℝ z (ρ u z) := by
    intro v
    rw [← Finset.sum_add_distrib]
    calc
      (∑ w : V, ((weight (χ v)).re * (weight (χ w)).re *
            inner ℝ z (ρ (w - v) z) +
          (weight (χ v)).im * (weight (χ w)).im *
            inner ℝ z (ρ (w - v) z))) =
          ∑ w : V, (weight (χ (v - w))).re *
            inner ℝ z (ρ (w - v) z) := by
        refine Finset.sum_congr rfl fun w _ ↦ ?_
        rw [map_sub χ v w, ← weight_re_mul_re_add_im_mul_im (χ v) (χ w)]
        ring
      _ = ∑ u : V, (weight (χ u)).re *
            inner ℝ z (ρ (v - u - v) z) :=
        (Fintype.sum_equiv (Equiv.subLeft v) _ _ (fun u ↦ by
          rw [Equiv.subLeft_apply]
          rw [show v - (v - u) = u by abel])).symm
      _ = ∑ u : V, (weight (χ u)).re * inner ℝ z (ρ u z) := by
        refine Finset.sum_congr rfl fun u _ ↦ ?_
        rw [show v - u - v = -u by abel, autocorrelation_neg ρ hρ]
  rw [Finset.sum_congr rfl fun v _ ↦ hinner v, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mass]
  field_simp

omit [DecidableEq V] in
theorem mass_nonneg (χ : Module.Dual (ZMod p) V) (z : E) :
    0 ≤ mass ρ χ z := by
  rw [mass_eq_norm_sq_add_norm_sq ρ hρ]
  positivity

/-- **Conservation**: the masses sum to the squared norm. -/
theorem sum_mass (z : E) :
    ∑ χ : Module.Dual (ZMod p) V, mass ρ χ z = ‖z‖ ^ 2 := by
  have hcard : ((Fintype.card V : ℝ)) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold mass
  rw [← Finset.mul_sum, Finset.sum_comm]
  rw [show (∑ v : V, ∑ χ : Module.Dual (ZMod p) V,
      (weight (χ v)).re * inner ℝ z (ρ v z)) =
    ∑ v : V, (if v = 0 then (Fintype.card V : ℝ) else 0) *
      inner ℝ z (ρ v z) from
    Finset.sum_congr rfl fun v _ ↦ by
      rw [← Finset.sum_mul, sum_dual_weight_re]]
  rw [show (∑ v : V, (if v = 0 then (Fintype.card V : ℝ) else 0) *
      inner ℝ z (ρ v z)) =
    ∑ v : V, (if v = 0 then
      (Fintype.card V : ℝ) * inner ℝ z (ρ v z) else 0) from
    Finset.sum_congr rfl fun v _ ↦ by
      by_cases hv : v = 0 <;> simp [hv]]
  rw [Finset.sum_ite_eq' Finset.univ (0 : V)
    (fun v ↦ (Fintype.card V : ℝ) * inner ℝ z (ρ v z))]
  simp only [Finset.mem_univ, if_true]
  rw [action_zero ρ hρ]
  rw [show inner ℝ z ((1 : E ≃ₗᵢ[ℝ] E) z) = ‖z‖ ^ 2 by
    rw [show (1 : E ≃ₗᵢ[ℝ] E) z = z from rfl,
      real_inner_self_eq_norm_sq]]
  field_simp

/-- **Inversion**: the autocorrelation is recovered from the masses. -/
theorem sum_weight_re_mass (z : E) (w : V) :
    ∑ χ : Module.Dual (ZMod p) V, (weight (χ w)).re * mass ρ χ z =
      inner ℝ z (ρ w z) := by
  have hcard : ((Fintype.card V : ℝ)) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold mass
  have h1 : ∀ χ : Module.Dual (ZMod p) V,
      (weight (χ w)).re * ((Fintype.card V : ℝ)⁻¹ *
          ∑ v : V, (weight (χ v)).re * inner ℝ z (ρ v z)) =
        (Fintype.card V : ℝ)⁻¹ *
          ∑ v : V, ((weight (χ w)).re * (weight (χ v)).re) *
            inner ℝ z (ρ v z) := by
    intro χ
    rw [mul_left_comm]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ ↦ by ring
  rw [Finset.sum_congr rfl fun χ _ ↦ h1 χ, ← Finset.mul_sum,
    Finset.sum_comm]
  have h2 : ∀ v : V,
      (∑ χ : Module.Dual (ZMod p) V,
        ((weight (χ w)).re * (weight (χ v)).re) * inner ℝ z (ρ v z)) =
      (((if w - v = 0 then (Fintype.card V : ℝ) else 0) +
        (if w + v = 0 then (Fintype.card V : ℝ) else 0)) / 2) *
          inner ℝ z (ρ v z) := by
    intro v
    rw [← Finset.sum_mul]
    congr 1
    rw [show (∑ χ : Module.Dual (ZMod p) V,
        (weight (χ w)).re * (weight (χ v)).re) =
      ∑ χ : Module.Dual (ZMod p) V,
        ((weight (χ (w - v))).re + (weight (χ (w + v))).re) / 2 from
      Finset.sum_congr rfl fun χ _ ↦ by
        rw [weight_re_mul_re, ← map_sub, ← map_add]]
    rw [← Finset.sum_div, Finset.sum_add_distrib,
      sum_dual_weight_re (p := p), sum_dual_weight_re (p := p)]
  rw [Finset.sum_congr rfl fun v _ ↦ h2 v]
  have h3 : ∀ v : V,
      (((if w - v = 0 then (Fintype.card V : ℝ) else 0) +
        (if w + v = 0 then (Fintype.card V : ℝ) else 0)) / 2) *
          inner ℝ z (ρ v z) =
      (if v = w then
          (Fintype.card V : ℝ) / 2 * inner ℝ z (ρ v z) else 0) +
        (if v = -w then
          (Fintype.card V : ℝ) / 2 * inner ℝ z (ρ v z) else 0) := by
    intro v
    have e1 : (w - v = 0) ↔ (v = w) := by
      rw [sub_eq_zero]
      exact eq_comm
    have e2 : (w + v = 0) ↔ (v = -w) := by
      rw [add_comm]
      exact add_eq_zero_iff_eq_neg
    by_cases hv : v = w
    · by_cases hv' : v = -w
      · rw [if_pos (e1.mpr hv), if_pos (e2.mpr hv'), if_pos hv,
          if_pos hv']
        ring
      · rw [if_pos (e1.mpr hv), if_neg (mt e2.mp hv'), if_pos hv,
          if_neg hv']
        ring
    · by_cases hv' : v = -w
      · rw [if_neg (mt e1.mp hv), if_pos (e2.mpr hv'), if_neg hv,
          if_pos hv']
        ring
      · rw [if_neg (mt e1.mp hv), if_neg (mt e2.mp hv'), if_neg hv,
          if_neg hv']
        ring
  rw [Finset.sum_congr rfl fun v _ ↦ h3 v, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (w : V)
      (fun v ↦ (Fintype.card V : ℝ) / 2 * inner ℝ z (ρ v z)),
    Finset.sum_ite_eq' Finset.univ (-w : V)
      (fun v ↦ (Fintype.card V : ℝ) / 2 * inner ℝ z (ρ v z))]
  simp only [Finset.mem_univ, if_true]
  rw [autocorrelation_neg ρ hρ]
  field_simp
  ring

/-- **Displacement identity**: the squared displacement under one group
element is the mass-weighted sum of `2 * (1 - Re χ(w))`.  Small displacement
therefore forces the mass to concentrate on characters vanishing at `w`. -/
theorem norm_action_sub_sq (z : E) (w : V) :
    ‖ρ w z - z‖ ^ 2 =
      ∑ χ : Module.Dual (ZMod p) V,
        2 * (1 - (weight (χ w)).re) * mass ρ χ z := by
  have hnorm : ‖ρ w z‖ = ‖z‖ := (ρ w).norm_map z
  have hexp : ‖ρ w z - z‖ ^ 2 =
      2 * ‖z‖ ^ 2 - 2 * inner ℝ z (ρ w z) := by
    rw [norm_sub_sq_real, hnorm, real_inner_comm]
    ring
  rw [hexp, ← sum_mass (p := p) ρ hρ z,
    ← sum_weight_re_mass (p := p) ρ hρ z w,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun χ _ ↦ by ring

end Action

end PrimeCharacterMass

end NonsoficGroupsExist
