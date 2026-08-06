import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Group.AddChar
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.FieldTheory.Finiteness
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Character masses of finite-field orthogonal actions

The characteristic-two Fourier machinery decomposes a real orthogonal
representation of an elementary abelian `2`-group into simultaneous `±1`
eigenspaces.  In odd characteristic the irreducible real pieces are rotation
planes, so sign eigenspaces do not exist; the correct replacement is the
family of character masses: the discrete Fourier coefficients of the
autocorrelation function `v ↦ ⟪z, ρ v z⟫` over the dual of the acting
vector space.  This file proves the foundational facts of that calculus over
an arbitrary finite coefficient field `K`, relative to one fixed nontrivial
complex additive character of `K`:

* positivity — each mass is a genuine sum of two squared component norms;
* conservation — the masses of `z` sum to `‖z‖ ^ 2`;
* inversion — the autocorrelation is recovered from the masses;
* displacement — `‖ρ w z - z‖ ^ 2` is the mass-weighted sum of
  `2 * (1 - Re χ(w))`;
* equivariance — masses are invariant under conjugating the action and
  transported functorially under automorphisms of the acting space;
* moving-mass control — a uniform angle gap converts one displacement into
  a bound on the total mass of any set of characters.

The displacement identity is what converts small generator displacement into
concentration of mass at characters vanishing on the generator, which is the
engine of the finite-stage relative-property-`(T)` argument.
-/

namespace NonsoficGroupsExist

namespace CharacterMass

open Finset

variable {K : Type*} [Field K] [Fintype K]
variable (ψ : AddChar K ℂ)

/-- Every value of a complex additive character of a finite group is a root
of unity, hence has norm one. -/
theorem norm_apply (c : K) : ‖ψ c‖ = 1 := by
  have hpow : ψ c ^ Fintype.card K = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero,
      AddChar.map_zero_eq_one]
  exact Complex.norm_eq_one_of_pow_eq_one hpow Fintype.card_ne_zero

theorem conj_apply (c : K) :
    (starRingEnd ℂ) (ψ c) = ψ (-c) := by
  have hmul : ψ c * ψ (-c) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have hinv : ψ (-c) = (ψ c)⁻¹ :=
    eq_inv_of_mul_eq_one_right hmul
  rw [hinv, Complex.inv_def, Complex.normSq_eq_norm_sq, norm_apply]
  simp

/-- The product of real parts, resolved through the character algebra. -/
theorem re_mul_re (a b : K) :
    (ψ a).re * (ψ b).re =
      ((ψ (a - b)).re + (ψ (a + b)).re) / 2 := by
  have h1 : ψ (a - b) = ψ a * (starRingEnd ℂ) (ψ b) := by
    rw [conj_apply, ← AddChar.map_add_eq_mul, sub_eq_add_neg]
  have h2 : ψ (a + b) = ψ a * ψ b := AddChar.map_add_eq_mul ψ a b
  rw [h1, h2]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The cosine-difference resolution used for the component expansion. -/
theorem re_mul_re_add_im_mul_im (a b : K) :
    (ψ a).re * (ψ b).re + (ψ a).im * (ψ b).im =
      (ψ (a - b)).re := by
  have h1 : ψ (a - b) = ψ a * (starRingEnd ℂ) (ψ b) := by
    rw [conj_apply, ← AddChar.map_add_eq_mul, sub_eq_add_neg]
  rw [h1]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem re_lt_one_of_ne_one {c : K} (hc : ψ c ≠ 1) : (ψ c).re < 1 := by
  rcases lt_or_eq_of_le
    ((Complex.re_le_norm (ψ c)).trans_eq (norm_apply ψ c)) with h | h
  · exact h
  · exfalso
    apply hc
    have hnormSq : (ψ c).re ^ 2 + (ψ c).im ^ 2 = 1 := by
      have := congrArg (· ^ 2) (norm_apply ψ c)
      rwa [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, one_pow,
        ← pow_two, ← pow_two] at this
    have him : (ψ c).im = 0 := by nlinarith
    apply Complex.ext
    · rw [h, Complex.one_re]
    · rw [him, Complex.one_im]

open Finset in
/-- The positive angle gap of a character: the least value of
`2 * (1 - Re ψ(c))` over the elements where `ψ` is nontrivial. -/
noncomputable def gap : ℝ :=
  if h : (Finset.univ.filter fun c : K ↦ ψ c ≠ 1).Nonempty then
    (Finset.univ.filter fun c : K ↦ ψ c ≠ 1).inf' h
      (fun c ↦ 2 * (1 - (ψ c).re))
  else 1

theorem gap_pos : 0 < gap ψ := by
  unfold gap
  split_ifs with h
  · rw [Finset.lt_inf'_iff]
    intro c hc
    have := re_lt_one_of_ne_one ψ (Finset.mem_filter.1 hc).2
    linarith
  · norm_num

theorem gap_le {c : K} (hc : ψ c ≠ 1) :
    gap ψ ≤ 2 * (1 - (ψ c).re) := by
  have hmem : c ∈ Finset.univ.filter fun c : K ↦ ψ c ≠ 1 :=
    Finset.mem_filter.2 ⟨Finset.mem_univ c, hc⟩
  unfold gap
  rw [dif_pos ⟨c, hmem⟩]
  exact Finset.inf'_le _ hmem

/-- A nontrivial character is nontrivial on some scalar multiple of every
nonzero element. -/
theorem exists_smul_ne_one (hψ : ψ ≠ 1) {c : K} (hc : c ≠ 0) :
    ∃ t : K, ψ (t * c) ≠ 1 := by
  by_contra hall
  push Not at hall
  apply hψ
  refine DFunLike.ext _ _ fun x ↦ ?_
  have := hall (x * c⁻¹)
  rw [mul_assoc, inv_mul_cancel₀ hc, mul_one] at this
  simp only [this, AddChar.one_apply]

variable {V : Type*} [AddCommGroup V] [Module K V] [Fintype V]
variable [DecidableEq V]

noncomputable instance : Fintype (Module.Dual K V) := by
  haveI : Finite (Module.Dual K V) :=
    Finite.of_injective (fun φ ↦ (φ : V → K)) DFunLike.coe_injective
  exact Fintype.ofFinite _

omit [DecidableEq V] in
/-- The dual of a finite vector space has the same cardinality. -/
theorem card_dual :
    Fintype.card (Module.Dual K V) = Fintype.card V := by
  haveI : Module.Finite K V := Module.Finite.of_finite
  rw [Module.card_eq_pow_finrank (K := K) (V := Module.Dual K V),
    Module.card_eq_pow_finrank (K := K) (V := V),
    Subspace.dual_finrank_eq]

/-- Orthogonality over the dual: for a nontrivial character, the dual
character sum at a point detects zero. -/
theorem sum_dual_apply (hψ : ψ ≠ 1) (a : V) :
    ∑ φ : Module.Dual K V, ψ (φ a) =
      if a = 0 then (Fintype.card V : ℂ) else 0 := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [card_dual]
  · rw [if_neg ha]
    obtain ⟨c, hc⟩ := AddChar.ne_one_iff.1 hψ
    obtain ⟨φ', hφ'⟩ := Module.Projective.exists_dual_eq_one K ha
    have hφ₀ : ψ ((c • φ') a) ≠ 1 := by
      rw [LinearMap.smul_apply, hφ', smul_eq_mul, mul_one]
      exact hc
    have hreindex :
        ∑ φ : Module.Dual K V, ψ ((φ + c • φ') a) =
          ∑ φ : Module.Dual K V, ψ (φ a) :=
      Fintype.sum_equiv (Equiv.addRight (c • φ')) _ _ (fun φ ↦ rfl)
    have hshift :
        ∑ φ : Module.Dual K V, ψ ((φ + c • φ') a) =
          (∑ φ : Module.Dual K V, ψ (φ a)) * ψ ((c • φ') a) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro φ _
      rw [LinearMap.add_apply, AddChar.map_add_eq_mul]
    have hzero :
        (∑ φ : Module.Dual K V, ψ (φ a)) *
          (1 - ψ ((c • φ') a)) = 0 := by
      rw [mul_sub, mul_one, ← hshift, hreindex, sub_self]
    rcases mul_eq_zero.1 hzero with h | h
    · exact h
    · exact absurd (sub_eq_zero.1 h).symm hφ₀

/-- Real-part form of the dual orthogonality. -/
theorem sum_dual_apply_re (hψ : ψ ≠ 1) (a : V) :
    ∑ φ : Module.Dual K V, (ψ (φ a)).re =
      if a = 0 then (Fintype.card V : ℝ) else 0 := by
  have h := congrArg Complex.re (sum_dual_apply ψ hψ a)
  rw [Complex.re_sum] at h
  rcases eq_or_ne a 0 with rfl | ha
  · simpa using h
  · simpa [ha] using h

omit [DecidableEq V] in
open Classical in
/-- Group-side orthogonality: the character sum of a dual functional over
the whole space detects the zero functional. -/
theorem sum_group_apply (hψ : ψ ≠ 1) (θ : Module.Dual K V) :
    ∑ v : V, ψ (θ v) =
      if θ = 0 then (Fintype.card V : ℂ) else 0 := by
  rcases eq_or_ne θ 0 with rfl | hθ
  · simp
  · rw [if_neg hθ]
    obtain ⟨v₀, hv₀⟩ : ∃ v₀ : V, θ v₀ ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hθ (LinearMap.ext fun v ↦ by
        rw [hall v, LinearMap.zero_apply])
    obtain ⟨t, ht⟩ := exists_smul_ne_one ψ hψ hv₀
    have hw₀ : ψ (θ (t • v₀)) ≠ 1 := by
      rwa [map_smul, smul_eq_mul]
    have hreindex : ∑ v : V, ψ (θ (v + t • v₀)) = ∑ v : V, ψ (θ v) :=
      Fintype.sum_equiv (Equiv.addRight (t • v₀)) _ _ (fun v ↦ rfl)
    have hshift : ∑ v : V, ψ (θ (v + t • v₀)) =
        (∑ v : V, ψ (θ v)) * ψ (θ (t • v₀)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro v _
      rw [map_add, AddChar.map_add_eq_mul]
    have hzero : (∑ v : V, ψ (θ v)) * (1 - ψ (θ (t • v₀))) = 0 := by
      rw [mul_sub, mul_one, ← hshift, hreindex, sub_self]
    rcases mul_eq_zero.1 hzero with h | h
    · exact h
    · exact absurd (sub_eq_zero.1 h).symm hw₀

omit [DecidableEq V] in
open Classical in
/-- Real-part form of the group-side orthogonality. -/
theorem sum_group_apply_re (hψ : ψ ≠ 1) (θ : Module.Dual K V) :
    ∑ v : V, (ψ (θ v)).re =
      if θ = 0 then (Fintype.card V : ℝ) else 0 := by
  have h := congrArg Complex.re (sum_group_apply ψ hψ θ)
  rw [Complex.re_sum] at h
  rcases eq_or_ne θ 0 with rfl | hθ
  · simp
  · simpa [hθ] using h

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (ρ : V → (E ≃ₗᵢ[ℝ] E))

/-- The character mass of a vector at a dual functional: the Fourier
coefficient of the autocorrelation function of the orbit. -/
noncomputable def mass (χ : Module.Dual K V) (z : E) : ℝ :=
  (Fintype.card V : ℝ)⁻¹ *
    ∑ v : V, (ψ (χ v)).re * inner ℝ z (ρ v z)

omit [Fintype K] [DecidableEq V] in
/-- **Equivariance under conjugation**: conjugating the action and the
vector by one isometry leaves every character mass unchanged. -/
theorem mass_conj (g : E ≃ₗᵢ[ℝ] E) (χ : Module.Dual K V) (z : E) :
    mass ψ (fun v ↦ g * ρ v * g⁻¹) χ (g z) = mass ψ ρ χ z := by
  unfold mass
  congr 1
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  congr 1
  have happly : (g * ρ v * g⁻¹) (g z) = g (ρ v z) := by
    change g (ρ v (g⁻¹ (g z))) = g (ρ v z)
    congr 1
    change ρ v (g.symm (g z)) = ρ v z
    rw [g.symm_apply_apply]
  rw [happly]
  exact g.inner_map_map z (ρ v z)

omit [DecidableEq V] in
/-- Negation symmetry of the masses: conjugate characters carry the same
mass. -/
theorem mass_neg (χ : Module.Dual K V) (z : E) :
    mass ψ ρ (-χ) z = mass ψ ρ χ z := by
  unfold mass
  congr 1
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  congr 1
  rw [LinearMap.neg_apply, ← conj_apply, Complex.conj_re]

omit [Fintype K] [DecidableEq V] in
/-- **Equivariance under automorphisms**: precomposing the action with a
linear automorphism of the acting space transports each mass to the mass at
the precomposed dual functional. -/
theorem mass_precomp (σ : V ≃ₗ[K] V) (χ : Module.Dual K V) (z : E) :
    mass ψ (fun v ↦ ρ (σ v)) χ z =
      mass ψ ρ (χ.comp (σ.symm : V →ₗ[K] V)) z := by
  unfold mass
  congr 1
  refine Fintype.sum_equiv σ.toEquiv _ _ fun v ↦ ?_
  congr 2
  rw [LinearMap.comp_apply]
  congr 1
  change χ v = χ (σ.symm (σ v))
  rw [σ.symm_apply_apply]

section Action

variable (hρ : ∀ v w : V, ρ (v + w) = ρ v * ρ w)

include hρ

omit [Module K V] [Fintype V] [DecidableEq V] in
theorem action_zero : ρ 0 = 1 := by
  have h := hρ 0 0
  rw [add_zero] at h
  calc
    ρ 0 = ρ 0 * ρ 0 * (ρ 0)⁻¹ := by group
    _ = ρ 0 * (ρ 0)⁻¹ := by rw [← h]
    _ = 1 := by group

omit [Module K V] [Fintype V] [DecidableEq V] in
theorem action_neg (v : V) : ρ (-v) = (ρ v)⁻¹ := by
  have h : ρ (-v) * ρ v = 1 := by
    rw [← hρ, neg_add_cancel, action_zero ρ hρ]
  exact eq_inv_of_mul_eq_one_left h

omit [Module K V] [Fintype V] [DecidableEq V] in
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

omit [Module K V] [Fintype V] [DecidableEq V] in
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
theorem mass_eq_norm_sq_add_norm_sq (χ : Module.Dual K V) (z : E) :
    mass ψ ρ χ z =
      ‖(Fintype.card V : ℝ)⁻¹ •
          ∑ v : V, (ψ (χ v)).re • ρ v z‖ ^ 2 +
        ‖(Fintype.card V : ℝ)⁻¹ •
          ∑ v : V, (ψ (χ v)).im • ρ v z‖ ^ 2 := by
  have hcard : ((Fintype.card V : ℝ)) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hre : ‖(Fintype.card V : ℝ)⁻¹ •
      ∑ v : V, (ψ (χ v)).re • ρ v z‖ ^ 2 =
    (Fintype.card V : ℝ)⁻¹ ^ 2 * ∑ v : V, ∑ w : V,
      (ψ (χ v)).re * (ψ (χ w)).re *
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
      ∑ v : V, (ψ (χ v)).im • ρ v z‖ ^ 2 =
    (Fintype.card V : ℝ)⁻¹ ^ 2 * ∑ v : V, ∑ w : V,
      (ψ (χ v)).im * (ψ (χ w)).im *
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
      (ψ (χ v)).re * (ψ (χ w)).re *
        inner ℝ z (ρ (w - v) z)) +
      ∑ w : V,
        (ψ (χ v)).im * (ψ (χ w)).im *
          inner ℝ z (ρ (w - v) z)) =
      ∑ u : V, (ψ (χ u)).re * inner ℝ z (ρ u z) := by
    intro v
    rw [← Finset.sum_add_distrib]
    calc
      (∑ w : V, ((ψ (χ v)).re * (ψ (χ w)).re *
            inner ℝ z (ρ (w - v) z) +
          (ψ (χ v)).im * (ψ (χ w)).im *
            inner ℝ z (ρ (w - v) z))) =
          ∑ w : V, (ψ (χ (v - w))).re *
            inner ℝ z (ρ (w - v) z) := by
        refine Finset.sum_congr rfl fun w _ ↦ ?_
        rw [map_sub χ v w, ← re_mul_re_add_im_mul_im ψ (χ v) (χ w)]
        ring
      _ = ∑ u : V, (ψ (χ u)).re *
            inner ℝ z (ρ (v - u - v) z) :=
        (Fintype.sum_equiv (Equiv.subLeft v) _ _ (fun u ↦ by
          rw [Equiv.subLeft_apply]
          rw [show v - (v - u) = u by abel])).symm
      _ = ∑ u : V, (ψ (χ u)).re * inner ℝ z (ρ u z) := by
        refine Finset.sum_congr rfl fun u _ ↦ ?_
        rw [show v - u - v = -u by abel, autocorrelation_neg ρ hρ]
  rw [Finset.sum_congr rfl fun v _ ↦ hinner v, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mass]
  field_simp

omit [DecidableEq V] in
theorem mass_nonneg (χ : Module.Dual K V) (z : E) :
    0 ≤ mass ψ ρ χ z := by
  rw [mass_eq_norm_sq_add_norm_sq ψ ρ hρ]
  positivity

omit [DecidableEq V] in
/-- The trivial-character mass is exactly the squared norm of the orbit
average. -/
theorem mass_zero_eq_norm_average_sq (z : E) :
    mass ψ ρ (0 : Module.Dual K V) z =
      ‖(Fintype.card V : ℝ)⁻¹ • ∑ v : V, ρ v z‖ ^ 2 := by
  rw [mass_eq_norm_sq_add_norm_sq ψ ρ hρ]
  simp

/-- **Conservation**: the masses sum to the squared norm. -/
theorem sum_mass (hψ : ψ ≠ 1) (z : E) :
    ∑ χ : Module.Dual K V, mass ψ ρ χ z = ‖z‖ ^ 2 := by
  have hcard : ((Fintype.card V : ℝ)) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold mass
  rw [← Finset.mul_sum, Finset.sum_comm]
  rw [show (∑ v : V, ∑ χ : Module.Dual K V,
      (ψ (χ v)).re * inner ℝ z (ρ v z)) =
    ∑ v : V, (if v = 0 then (Fintype.card V : ℝ) else 0) *
      inner ℝ z (ρ v z) from
    Finset.sum_congr rfl fun v _ ↦ by
      rw [← Finset.sum_mul, sum_dual_apply_re ψ hψ]]
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
theorem sum_apply_re_mass (hψ : ψ ≠ 1) (z : E) (w : V) :
    ∑ χ : Module.Dual K V, (ψ (χ w)).re * mass ψ ρ χ z =
      inner ℝ z (ρ w z) := by
  have hcard : ((Fintype.card V : ℝ)) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold mass
  have h1 : ∀ χ : Module.Dual K V,
      (ψ (χ w)).re * ((Fintype.card V : ℝ)⁻¹ *
          ∑ v : V, (ψ (χ v)).re * inner ℝ z (ρ v z)) =
        (Fintype.card V : ℝ)⁻¹ *
          ∑ v : V, ((ψ (χ w)).re * (ψ (χ v)).re) *
            inner ℝ z (ρ v z) := by
    intro χ
    rw [mul_left_comm]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ ↦ by ring
  rw [Finset.sum_congr rfl fun χ _ ↦ h1 χ, ← Finset.mul_sum,
    Finset.sum_comm]
  have h2 : ∀ v : V,
      (∑ χ : Module.Dual K V,
        ((ψ (χ w)).re * (ψ (χ v)).re) * inner ℝ z (ρ v z)) =
      (((if w - v = 0 then (Fintype.card V : ℝ) else 0) +
        (if w + v = 0 then (Fintype.card V : ℝ) else 0)) / 2) *
          inner ℝ z (ρ v z) := by
    intro v
    rw [← Finset.sum_mul]
    congr 1
    rw [show (∑ χ : Module.Dual K V,
        (ψ (χ w)).re * (ψ (χ v)).re) =
      ∑ χ : Module.Dual K V,
        ((ψ (χ (w - v))).re + (ψ (χ (w + v))).re) / 2 from
      Finset.sum_congr rfl fun χ _ ↦ by
        rw [re_mul_re, ← map_sub, ← map_add]]
    rw [← Finset.sum_div, Finset.sum_add_distrib,
      sum_dual_apply_re ψ hψ, sum_dual_apply_re ψ hψ]
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
theorem norm_action_sub_sq (hψ : ψ ≠ 1) (z : E) (w : V) :
    ‖ρ w z - z‖ ^ 2 =
      ∑ χ : Module.Dual K V,
        2 * (1 - (ψ (χ w)).re) * mass ψ ρ χ z := by
  have hnorm : ‖ρ w z‖ = ‖z‖ := (ρ w).norm_map z
  have hexp : ‖ρ w z - z‖ ^ 2 =
      2 * ‖z‖ ^ 2 - 2 * inner ℝ z (ρ w z) := by
    rw [norm_sub_sq_real, hnorm, real_inner_comm]
    ring
  rw [hexp, ← sum_mass ψ ρ hρ hψ z,
    ← sum_apply_re_mass ψ ρ hρ hψ z w,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun χ _ ↦ by ring

/-- **Moving-mass control**: any uniform positive angle gap over a set of
characters converts one displacement into a bound on the set's total
mass. -/
theorem mul_sum_mass_le_of_gap (hψ : ψ ≠ 1) (z : E) (w : V)
    (S : Finset (Module.Dual K V)) (δ : ℝ)
    (hδ : ∀ χ ∈ S, δ ≤ 2 * (1 - (ψ (χ w)).re)) :
    δ * ∑ χ ∈ S, mass ψ ρ χ z ≤ ‖ρ w z - z‖ ^ 2 := by
  have hterm : ∀ χ : Module.Dual K V,
      0 ≤ 2 * (1 - (ψ (χ w)).re) * mass ψ ρ χ z := by
    intro χ
    have hre : (ψ (χ w)).re ≤ 1 := by
      calc
        (ψ (χ w)).re ≤ ‖ψ (χ w)‖ := Complex.re_le_norm _
        _ = 1 := norm_apply _ _
    have h1 : 0 ≤ 2 * (1 - (ψ (χ w)).re) := by linarith
    exact mul_nonneg h1 (mass_nonneg ψ ρ hρ χ z)
  rw [norm_action_sub_sq ψ ρ hρ hψ, Finset.mul_sum]
  calc
    ∑ χ ∈ S, δ * mass ψ ρ χ z ≤
        ∑ χ ∈ S, 2 * (1 - (ψ (χ w)).re) * mass ψ ρ χ z :=
      Finset.sum_le_sum fun χ hχ ↦
        mul_le_mul_of_nonneg_right (hδ χ hχ) (mass_nonneg ψ ρ hρ χ z)
    _ ≤ ∑ χ : Module.Dual K V,
        2 * (1 - (ψ (χ w)).re) * mass ψ ρ χ z :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        fun χ _ _ ↦ hterm χ

open Classical in
/-- **Scalar-orbit moving-mass control**: the total mass of all characters
nonvanishing at `w` is bounded by the sum of the squared displacements of
the scalar multiples of `w`, at the character's positive gap constant.
Passing to the scalar orbit is what handles a nontrivial character whose
kernel is a proper subgroup of the coefficient field. -/
theorem gap_mul_sum_mass_ne_zero_le (hψ : ψ ≠ 1) (z : E) (w : V) :
    gap ψ * ∑ χ ∈ Finset.univ.filter
        (fun χ : Module.Dual K V ↦ χ w ≠ 0), mass ψ ρ χ z ≤
      ∑ t : K, ‖ρ (t • w) z - z‖ ^ 2 := by
  classical
  set A : Finset (Module.Dual K V) :=
    Finset.univ.filter fun χ : Module.Dual K V ↦ χ w ≠ 0 with hA
  have hsel : ∀ χ ∈ A, ∃ t : K, ψ (t * χ w) ≠ 1 := by
    intro χ hχ
    exact exists_smul_ne_one ψ hψ ((Finset.mem_filter.1 hχ).2)
  set tsel : Module.Dual K V → K := fun χ ↦
    if hχ : χ ∈ A then Classical.choose (hsel χ hχ) else 0 with htsel
  have htspec : ∀ χ ∈ A, ψ (χ (tsel χ • w)) ≠ 1 := by
    intro χ hχ
    rw [map_smul, smul_eq_mul]
    simp only [htsel]
    rw [dif_pos hχ]
    exact Classical.choose_spec (hsel χ hχ)
  have hpartition : ∑ χ ∈ A, mass ψ ρ χ z =
      ∑ t : K, ∑ χ ∈ A.filter (fun χ ↦ tsel χ = t), mass ψ ρ χ z :=
    (Finset.sum_fiberwise A tsel (fun χ ↦ mass ψ ρ χ z)).symm
  rw [hpartition, Finset.mul_sum]
  refine Finset.sum_le_sum fun t _ ↦ ?_
  have hsubset : A.filter (fun χ ↦ tsel χ = t) ⊆
      Finset.univ.filter
        (fun χ : Module.Dual K V ↦ ψ (χ (t • w)) ≠ 1) := by
    intro χ hχ
    obtain ⟨hχA, hχt⟩ := Finset.mem_filter.1 hχ
    refine Finset.mem_filter.2 ⟨Finset.mem_univ χ, ?_⟩
    rw [← hχt]
    exact htspec χ hχA
  calc
    gap ψ * ∑ χ ∈ A.filter (fun χ ↦ tsel χ = t), mass ψ ρ χ z ≤
        gap ψ * ∑ χ ∈ Finset.univ.filter
          (fun χ : Module.Dual K V ↦ ψ (χ (t • w)) ≠ 1),
            mass ψ ρ χ z :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hsubset
          fun χ _ _ ↦ mass_nonneg ψ ρ hρ χ z)
        (gap_pos ψ).le
    _ ≤ ‖ρ (t • w) z - z‖ ^ 2 :=
      mul_sum_mass_le_of_gap ψ ρ hρ hψ z (t • w) _ (gap ψ)
        fun χ hχ ↦ gap_le ψ (Finset.mem_filter.1 hχ).2


/-- **Summed mass continuity**: the total mass over any set of characters
is quadratically continuous in the vector, with the same constant as a
single mass.  The proof runs through the Cauchy--Schwarz inequality for
the positive-semidefinite symmetric bilinear form obtained by polarizing
the set mass, so no cardinality factor appears. -/
theorem abs_sum_mass_sub_sum_mass_le (hψ : ψ ≠ 1)
    (S : Finset (Module.Dual K V)) (z w : E) :
    |(∑ χ ∈ S, mass ψ ρ χ z) - ∑ χ ∈ S, mass ψ ρ χ w| ≤
      (‖z‖ + ‖w‖) * ‖z - w‖ := by
  set B : E → E → ℝ := fun u t ↦
    (Fintype.card V : ℝ)⁻¹ *
      ∑ χ ∈ S, ∑ v : V, (ψ (χ v)).re * inner ℝ u (ρ v t) with hB
  have hdiag : ∀ u : E, B u u = ∑ χ ∈ S, mass ψ ρ χ u := by
    intro u
    rw [hB]
    beta_reduce
    rw [Finset.mul_sum]
    rfl
  have hswap : ∀ (u t : E) (v : V),
      inner ℝ u (ρ v t) = inner ℝ t (ρ (-v) u) := by
    intro u t v
    calc
      inner ℝ u (ρ v t) = inner ℝ (ρ (-v) u) (ρ (-v) (ρ v t)) :=
        ((ρ (-v)).inner_map_map u (ρ v t)).symm
      _ = inner ℝ (ρ (-v) u) t := by
        rw [show ρ (-v) (ρ v t) = (ρ (-v) * ρ v) t from rfl, ← hρ,
          neg_add_cancel, action_zero ρ hρ]
        rfl
      _ = inner ℝ t (ρ (-v) u) := real_inner_comm _ _
  have hsymm : ∀ u t : E, B u t = B t u := by
    intro u t
    rw [hB]
    beta_reduce
    congr 1
    refine Finset.sum_congr rfl fun χ _ ↦ ?_
    calc
      (∑ v : V, (ψ (χ v)).re * inner ℝ u (ρ v t)) =
          ∑ v : V, (ψ (χ v)).re * inner ℝ t (ρ (-v) u) := by
        refine Finset.sum_congr rfl fun v _ ↦ ?_
        rw [hswap u t v]
      _ = ∑ v : V, (ψ (χ (-v))).re * inner ℝ t (ρ v u) :=
        Fintype.sum_equiv (Equiv.neg V) _ _ fun v ↦ by
          simp only [Equiv.neg_apply, neg_neg]
      _ = ∑ v : V, (ψ (χ v)).re * inner ℝ t (ρ v u) := by
        refine Finset.sum_congr rfl fun v _ ↦ ?_
        rw [map_neg, ← conj_apply, Complex.conj_re]
  have haddr : ∀ u t t' : E, B u (t + t') = B u t + B u t' := by
    intro u t t'
    rw [hB]
    beta_reduce
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun χ _ ↦ ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    rw [map_add, inner_add_right]
    ring
  have haddl : ∀ u u' t : E, B (u + u') t = B u t + B u' t := by
    intro u u' t
    rw [hsymm (u + u') t, haddr t u u', hsymm t u, hsymm t u']
  have hsmulr : ∀ (x : ℝ) (u t : E), B u (x • t) = x * B u t := by
    intro x u t
    rw [hB]
    beta_reduce
    rw [show (∑ χ ∈ S, ∑ v : V,
        (ψ (χ v)).re * inner ℝ u (ρ v (x • t))) =
      x * ∑ χ ∈ S, ∑ v : V, (ψ (χ v)).re * inner ℝ u (ρ v t) from by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun χ _ ↦ ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ ↦ ?_
      rw [map_smul, inner_smul_right]
      ring]
    ring
  have hsmull : ∀ (x : ℝ) (u t : E), B (x • u) t = x * B u t := by
    intro x u t
    rw [hsymm (x • u) t, hsmulr x t u, hsymm t u]
  have hpsd : ∀ u : E, 0 ≤ B u u := by
    intro u
    rw [hdiag u]
    exact Finset.sum_nonneg fun χ _ ↦ mass_nonneg ψ ρ hρ χ u
  have hle : ∀ u : E, B u u ≤ ‖u‖ ^ 2 := by
    intro u
    rw [hdiag u]
    calc
      (∑ χ ∈ S, mass ψ ρ χ u) ≤
          ∑ χ : Module.Dual K V, mass ψ ρ χ u :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
          fun χ _ _ ↦ mass_nonneg ψ ρ hρ χ u
      _ = ‖u‖ ^ 2 := sum_mass ψ ρ hρ hψ u
  have hcs : ∀ u t : E, B u t ^ 2 ≤ B u u * B t t := by
    intro u t
    have hquad : ∀ x : ℝ,
        0 ≤ B t t * (x * x) + 2 * B u t * x + B u u := by
      intro x
      have hexp : B (u + x • t) (u + x • t) =
          B t t * (x * x) + 2 * B u t * x + B u u := by
        rw [haddl u (x • t) (u + x • t), haddr u u (x • t),
          haddr (x • t) u (x • t), hsmulr x u t, hsmull x t u,
          hsmull x t (x • t), hsmulr x t t, hsymm t u]
        ring
      rw [← hexp]
      exact hpsd _
    have hdisc := discrim_le_zero hquad
    rw [discrim] at hdisc
    nlinarith [hdisc]
  have hdelta : B z z - B w w = B (z - w) (z + w) := by
    have h1 : z - w = z + (-1 : ℝ) • w := by
      rw [neg_one_smul]
      abel
    rw [h1, haddl z ((-1 : ℝ) • w) (z + w), haddr z z w,
      hsmull (-1) w (z + w), haddr w z w, hsymm w z]
    ring
  have hbound : |B (z - w) (z + w)| ≤ ‖z - w‖ * ‖z + w‖ := by
    have hsq : B (z - w) (z + w) ^ 2 ≤
        (‖z - w‖ * ‖z + w‖) ^ 2 := by
      calc
        B (z - w) (z + w) ^ 2 ≤ B (z - w) (z - w) * B (z + w) (z + w) :=
          hcs _ _
        _ ≤ ‖z - w‖ ^ 2 * ‖z + w‖ ^ 2 :=
          mul_le_mul (hle _) (hle _) (hpsd _) (by positivity)
        _ = (‖z - w‖ * ‖z + w‖) ^ 2 := by ring
    calc
      |B (z - w) (z + w)| = Real.sqrt (B (z - w) (z + w) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((‖z - w‖ * ‖z + w‖) ^ 2) :=
        Real.sqrt_le_sqrt hsq
      _ = ‖z - w‖ * ‖z + w‖ := by
        rw [Real.sqrt_sq (by positivity)]
  calc
    |(∑ χ ∈ S, mass ψ ρ χ z) - ∑ χ ∈ S, mass ψ ρ χ w| =
        |B (z - w) (z + w)| := by
      rw [← hdiag z, ← hdiag w, hdelta]
    _ ≤ ‖z - w‖ * ‖z + w‖ := hbound
    _ ≤ ‖z - w‖ * (‖z‖ + ‖w‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le z w) (norm_nonneg _)
    _ = (‖z‖ + ‖w‖) * ‖z - w‖ := by ring

end Action

omit [DecidableEq V] in
/-- **Mass continuity**: the mass at any character is quadratically
continuous in the vector.  This is the quantitative transport estimate: a
sheared event and the original event differ by at most the displacement
times the sum of the norms. -/
theorem abs_mass_sub_mass_le (χ : Module.Dual K V) (z z' : E) :
    |mass ψ ρ χ z - mass ψ ρ χ z'| ≤ (‖z‖ + ‖z'‖) * ‖z - z'‖ := by
  have hcardpos : (0 : ℝ) < (Fintype.card V : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hterm : ∀ v : V,
      |(ψ (χ v)).re * inner ℝ z (ρ v z) -
        (ψ (χ v)).re * inner ℝ z' (ρ v z')| ≤
      (‖z‖ + ‖z'‖) * ‖z - z'‖ := by
    intro v
    have hre : |(ψ (χ v)).re| ≤ 1 := by
      calc
        |(ψ (χ v)).re| ≤ ‖ψ (χ v)‖ := Complex.abs_re_le_norm _
        _ = 1 := norm_apply ψ _
    have hsplit : inner ℝ z (ρ v z) - inner ℝ z' (ρ v z') =
        inner ℝ (z - z') (ρ v z) + inner ℝ z' (ρ v (z - z')) := by
      rw [inner_sub_left, map_sub, inner_sub_right]
      ring
    have hbound : |inner ℝ z (ρ v z) - inner ℝ z' (ρ v z')| ≤
        (‖z‖ + ‖z'‖) * ‖z - z'‖ := by
      rw [hsplit]
      calc
        |inner ℝ (z - z') (ρ v z) + inner ℝ z' (ρ v (z - z'))| ≤
            |inner ℝ (z - z') (ρ v z)| +
              |inner ℝ z' (ρ v (z - z'))| := abs_add_le _ _
        _ ≤ ‖z - z'‖ * ‖ρ v z‖ + ‖z'‖ * ‖ρ v (z - z')‖ :=
          add_le_add (abs_real_inner_le_norm _ _)
            (abs_real_inner_le_norm _ _)
        _ = (‖z‖ + ‖z'‖) * ‖z - z'‖ := by
          rw [(ρ v).norm_map, (ρ v).norm_map]
          ring
    calc
      |(ψ (χ v)).re * inner ℝ z (ρ v z) -
          (ψ (χ v)).re * inner ℝ z' (ρ v z')| =
          |(ψ (χ v)).re| *
            |inner ℝ z (ρ v z) - inner ℝ z' (ρ v z')| := by
        rw [← abs_mul]
        congr 1
        ring
      _ ≤ 1 * ((‖z‖ + ‖z'‖) * ‖z - z'‖) := by
        apply mul_le_mul hre hbound (abs_nonneg _)
        norm_num
      _ = (‖z‖ + ‖z'‖) * ‖z - z'‖ := one_mul _
  calc
    |mass ψ ρ χ z - mass ψ ρ χ z'| =
        (Fintype.card V : ℝ)⁻¹ *
          |∑ v : V, ((ψ (χ v)).re * inner ℝ z (ρ v z) -
            (ψ (χ v)).re * inner ℝ z' (ρ v z'))| := by
      rw [mass, mass, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
        abs_of_pos (by positivity : (0 : ℝ) < (Fintype.card V : ℝ)⁻¹)]
    _ ≤ (Fintype.card V : ℝ)⁻¹ *
        ∑ v : V, |(ψ (χ v)).re * inner ℝ z (ρ v z) -
          (ψ (χ v)).re * inner ℝ z' (ρ v z')| :=
      mul_le_mul_of_nonneg_left
        (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (Fintype.card V : ℝ)⁻¹ *
        ∑ _v : V, (‖z‖ + ‖z'‖) * ‖z - z'‖ :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun v _ ↦ hterm v) (by positivity)
    _ = (‖z‖ + ‖z'‖) * ‖z - z'‖ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp

omit [DecidableEq V] in
open Classical in
/-- **Fiber covariance**: the mass of a pulled-back action at a coarse
character is the total mass over the dual-restriction fiber of that
character.  This is the exact Fourier transport law: a coarse mass is the
sum of precisely its fine extensions, with the conjugate fiber folded in by
the negation symmetry of the masses. -/
theorem sum_mass_fiber_comp
    {W : Type*} [AddCommGroup W] [Module K W] [Fintype W]
    (ρ : W → (E ≃ₗᵢ[ℝ] E)) (hρ : ∀ v w : W, ρ (v + w) = ρ v * ρ w)
    (hψ : ψ ≠ 1) (s : V →ₗ[K] W) (z : E) (χ : Module.Dual K V) :
    ∑ χ' ∈ Finset.univ.filter
        (fun χ' : Module.Dual K W ↦ χ'.comp s = χ),
      mass ψ ρ χ' z =
    mass ψ (fun v ↦ ρ (s v)) χ z := by
  have hcard : ((Fintype.card V : ℝ)) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hinner : ∀ χ' : Module.Dual K W,
      (Fintype.card V : ℝ)⁻¹ * ∑ v : V,
          (ψ (χ v)).re * (ψ ((χ'.comp s) v)).re =
        ((if χ'.comp s = χ then (1 : ℝ) else 0) +
          (if χ'.comp s = -χ then (1 : ℝ) else 0)) / 2 := by
    intro χ'
    rw [show (∑ v : V, (ψ (χ v)).re * (ψ ((χ'.comp s) v)).re) =
        ∑ v : V, ((ψ ((χ - χ'.comp s) v)).re +
          (ψ ((χ + χ'.comp s) v)).re) / 2 from
      Finset.sum_congr rfl fun v _ ↦ by
        rw [re_mul_re, ← LinearMap.sub_apply, ← LinearMap.add_apply]]
    rw [← Finset.sum_div, Finset.sum_add_distrib,
      sum_group_apply_re ψ hψ (χ - χ'.comp s),
      sum_group_apply_re ψ hψ (χ + χ'.comp s)]
    have e1 : (χ - χ'.comp s = 0) ↔ (χ'.comp s = χ) := by
      rw [sub_eq_zero]
      exact eq_comm
    have e2 : (χ + χ'.comp s = 0) ↔ (χ'.comp s = -χ) := by
      rw [add_comm]
      exact add_eq_zero_iff_eq_neg
    by_cases h1 : χ'.comp s = χ <;> by_cases h2 : χ'.comp s = -χ
    · rw [if_pos (e1.mpr h1), if_pos (e2.mpr h2), if_pos h1, if_pos h2]
      field_simp
    · rw [if_pos (e1.mpr h1), if_neg (mt e2.mp h2), if_pos h1,
        if_neg h2]
      field_simp
      ring
    · rw [if_neg (mt e1.mp h1), if_pos (e2.mpr h2), if_neg h1,
        if_pos h2]
      field_simp
      ring
    · rw [if_neg (mt e1.mp h1), if_neg (mt e2.mp h2), if_neg h1,
        if_neg h2]
      field_simp
      ring
  have hnegsum : (∑ χ' ∈ Finset.univ.filter
        (fun χ' : Module.Dual K W ↦ χ'.comp s = -χ),
      mass ψ ρ χ' z) =
    ∑ χ' ∈ Finset.univ.filter
        (fun χ' : Module.Dual K W ↦ χ'.comp s = χ),
      mass ψ ρ χ' z := by
    refine Finset.sum_nbij' (i := fun χ' ↦ -χ') (j := fun χ' ↦ -χ')
      ?_ ?_ ?_ ?_ ?_
    · intro χ' hχ'
      rw [Finset.mem_filter] at hχ' ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [show (-χ').comp s = -(χ'.comp s) from rfl, hχ'.2, neg_neg]
    · intro χ' hχ'
      rw [Finset.mem_filter] at hχ' ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [show (-χ').comp s = -(χ'.comp s) from rfl, hχ'.2]
    · intro χ' _
      simp
    · intro χ' _
      simp
    · intro χ' _
      exact (mass_neg ψ ρ χ' z).symm
  calc
    (∑ χ' ∈ Finset.univ.filter
        (fun χ' : Module.Dual K W ↦ χ'.comp s = χ),
      mass ψ ρ χ' z) =
        (∑ χ' ∈ Finset.univ.filter
            (fun χ' : Module.Dual K W ↦ χ'.comp s = χ),
          mass ψ ρ χ' z / 2) +
        ∑ χ' ∈ Finset.univ.filter
            (fun χ' : Module.Dual K W ↦ χ'.comp s = -χ),
          mass ψ ρ χ' z / 2 := by
      rw [← Finset.sum_div, ← Finset.sum_div, hnegsum]
      ring
    _ = ∑ χ' : Module.Dual K W,
        ((if χ'.comp s = χ then mass ψ ρ χ' z / 2 else 0) +
          (if χ'.comp s = -χ then mass ψ ρ χ' z / 2 else 0)) := by
      rw [Finset.sum_add_distrib, Finset.sum_filter, Finset.sum_filter]
    _ = ∑ χ' : Module.Dual K W,
        ((Fintype.card V : ℝ)⁻¹ * ∑ v : V,
          (ψ (χ v)).re * (ψ ((χ'.comp s) v)).re) * mass ψ ρ χ' z := by
      refine Finset.sum_congr rfl fun χ' _ ↦ ?_
      rw [hinner χ']
      by_cases h1 : χ'.comp s = χ <;> by_cases h2 : χ'.comp s = -χ
      · rw [if_pos h1, if_pos h2, if_pos h1, if_pos h2]
        ring
      · rw [if_pos h1, if_neg h2, if_pos h1, if_neg h2]
        ring
      · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2]
        ring
      · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]
        ring
    _ = (Fintype.card V : ℝ)⁻¹ * ∑ v : V,
        (ψ (χ v)).re * ∑ χ' : Module.Dual K W,
          (ψ (χ' (s v))).re * mass ψ ρ χ' z := by
      calc
        (∑ χ' : Module.Dual K W,
            ((Fintype.card V : ℝ)⁻¹ * ∑ v : V,
              (ψ (χ v)).re * (ψ ((χ'.comp s) v)).re) * mass ψ ρ χ' z) =
            ∑ χ' : Module.Dual K W, ∑ v : V,
              (Fintype.card V : ℝ)⁻¹ *
                ((ψ (χ v)).re *
                  ((ψ (χ' (s v))).re * mass ψ ρ χ' z)) := by
          refine Finset.sum_congr rfl fun χ' _ ↦ ?_
          calc
            ((Fintype.card V : ℝ)⁻¹ * ∑ v : V,
                (ψ (χ v)).re * (ψ ((χ'.comp s) v)).re) *
                mass ψ ρ χ' z =
                (∑ v : V, (ψ (χ v)).re * (ψ ((χ'.comp s) v)).re) *
                  ((Fintype.card V : ℝ)⁻¹ * mass ψ ρ χ' z) := by ring
            _ = ∑ v : V, ((ψ (χ v)).re * (ψ ((χ'.comp s) v)).re) *
                  ((Fintype.card V : ℝ)⁻¹ * mass ψ ρ χ' z) :=
              Finset.sum_mul _ _ _
            _ = ∑ v : V, (Fintype.card V : ℝ)⁻¹ *
                  ((ψ (χ v)).re *
                    ((ψ (χ' (s v))).re * mass ψ ρ χ' z)) := by
              refine Finset.sum_congr rfl fun v _ ↦ ?_
              rw [show (χ'.comp s) v = χ' (s v) from rfl]
              ring
        _ = ∑ v : V, ∑ χ' : Module.Dual K W,
              (Fintype.card V : ℝ)⁻¹ *
                ((ψ (χ v)).re *
                  ((ψ (χ' (s v))).re * mass ψ ρ χ' z)) :=
          Finset.sum_comm
        _ = (Fintype.card V : ℝ)⁻¹ * ∑ v : V,
              (ψ (χ v)).re * ∑ χ' : Module.Dual K W,
                (ψ (χ' (s v))).re * mass ψ ρ χ' z := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun v _ ↦ ?_
          rw [Finset.mul_sum, Finset.mul_sum]
    _ = mass ψ (fun v ↦ ρ (s v)) χ z := by
      rw [show mass ψ (fun v ↦ ρ (s v)) χ z =
          (Fintype.card V : ℝ)⁻¹ * ∑ v : V,
            (ψ (χ v)).re * inner ℝ z (ρ (s v) z) from rfl]
      congr 1
      refine Finset.sum_congr rfl fun v _ ↦ ?_
      rw [← sum_apply_re_mass ψ ρ hρ hψ z (s v)]


/-- **Positive control for the nontriviality hypotheses**: every finite
field admits a nontrivial complex additive character, obtained by pushing
a nonzero linear functional into the standard character of the prime
field. -/
theorem exists_addChar_ne_one (K : Type*) [Field K] [Fintype K] :
    ∃ ψ : AddChar K ℂ, ψ ≠ 1 := by
  classical
  set p := ringChar K with hp
  haveI hprime : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  haveI : NeZero p := ⟨hprime.1.ne_zero⟩
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual (ZMod p) K, φ 1 ≠ 0 := by
    by_contra hall
    push Not at hall
    exact one_ne_zero
      ((Module.forall_dual_apply_eq_zero_iff (ZMod p) (1 : K)).1 hall)
  refine ⟨(ZMod.stdAddChar (N := p)).compAddMonoidHom
    φ.toAddMonoidHom, fun hcontra ↦ hφ ?_⟩
  have happ : (ZMod.stdAddChar (N := p)).compAddMonoidHom
      φ.toAddMonoidHom (1 : K) = 1 := by
    rw [hcontra]
    exact AddChar.one_apply _
  rw [AddChar.compAddMonoidHom_apply] at happ
  have h0 : ZMod.stdAddChar (N := p) (0 : ZMod p) = 1 :=
    AddChar.map_zero_eq_one _
  exact ZMod.injective_stdAddChar (happ.trans h0.symm)

end CharacterMass

end NonsoficGroupsExist
