import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Complex.Norm

/-!
# Complexification of a real Hilbert space

The complexification `E ⊕ i E` of a real inner product space `E`, carried by
the `L²` product `E × E` so that the norm, completeness, and real inner
product come from mathlib.  The complex structure is `i · (a, b) = (-b, a)`
and the complex inner product is

$$\langle (a,b), (c,d) \rangle = (\langle a,c\rangle + \langle b,d\rangle)
  + i(\langle a,d\rangle - \langle b,c\rangle).$$

A real orthogonal representation complexifies to a unitary representation on
this space, the embedding `a ↦ (a, 0)` is isometric, and the real and
imaginary parts of an invariant vector are invariant.  This is the
`complexification` half of the standard equivalence between the real and the
complex-unitary formulations of Kazhdan's property `(T)`; the `realification`
half needs no construction at all.
-/

namespace NonsoficGroupsExist

universe v

open scoped InnerProductSpace

/-- The complexification `E ⊕ i E` of a real inner product space, carried by
the `L²` product `E × E`. -/
def Complexification (E : Type v) : Type v := WithLp 2 (E × E)

namespace Complexification

section Carrier

variable {E : Type v}

/-- The vector with real part `a` and imaginary part `b`. -/
def mk (a b : E) : Complexification E := WithLp.toLp 2 (a, b)

/-- The real part of a vector of the complexification. -/
def re (v : Complexification E) : E := (WithLp.ofLp (v : WithLp 2 (E × E))).1

/-- The imaginary part of a vector of the complexification. -/
def im (v : Complexification E) : E := (WithLp.ofLp (v : WithLp 2 (E × E))).2

@[simp] theorem re_mk (a b : E) : (mk a b).re = a := rfl
@[simp] theorem im_mk (a b : E) : (mk a b).im = b := rfl
@[simp] theorem mk_re_im (v : Complexification E) : mk v.re v.im = v := rfl

@[ext] theorem ext {v w : Complexification E} (hre : v.re = w.re)
    (him : v.im = w.im) : v = w := by
  rw [← mk_re_im v, ← mk_re_im w, hre, him]

end Carrier

noncomputable section Normed

variable {E : Type v} [NormedAddCommGroup E]

instance : NormedAddCommGroup (Complexification E) :=
  inferInstanceAs (NormedAddCommGroup (WithLp 2 (E × E)))

instance [CompleteSpace E] : CompleteSpace (Complexification E) :=
  inferInstanceAs (CompleteSpace (WithLp 2 (E × E)))

@[simp] theorem re_zero : (0 : Complexification E).re = 0 := rfl
@[simp] theorem im_zero : (0 : Complexification E).im = 0 := rfl
@[simp] theorem re_add (v w : Complexification E) : (v + w).re = v.re + w.re := rfl
@[simp] theorem im_add (v w : Complexification E) : (v + w).im = v.im + w.im := rfl
@[simp] theorem re_neg (v : Complexification E) : (-v).re = -v.re := rfl
@[simp] theorem im_neg (v : Complexification E) : (-v).im = -v.im := rfl
@[simp] theorem re_sub (v w : Complexification E) : (v - w).re = v.re - w.re := rfl
@[simp] theorem im_sub (v w : Complexification E) : (v - w).im = v.im - w.im := rfl

theorem eq_zero_iff {v : Complexification E} : v = 0 ↔ v.re = 0 ∧ v.im = 0 :=
  ⟨fun h ↦ ⟨by rw [h, re_zero], by rw [h, im_zero]⟩, fun h ↦ ext h.1 h.2⟩

/-- The `L²` norm of the complexification, in squared form. -/
theorem norm_sq (v : Complexification E) : ‖v‖ ^ 2 = ‖v.re‖ ^ 2 + ‖v.im‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 _

@[simp] theorem norm_mk_zero (a : E) : ‖mk a (0 : E)‖ = ‖a‖ :=
  WithLp.norm_toLp_fst 2 E E a

theorem norm_mk_sub_mk (a b : E) : ‖mk a (0 : E) - mk b (0 : E)‖ = ‖a - b‖ := by
  have hsub : mk a (0 : E) - mk b (0 : E) = mk (a - b) (0 : E) := by
    ext <;> simp
  rw [hsub, norm_mk_zero]

/-- Two vectors with the same norm-square have the same norm. -/
private theorem norm_eq_of_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ 2 = b ^ 2) : a = b :=
  ((sq_le_sq₀ ha hb).mp h.le).antisymm ((sq_le_sq₀ hb ha).mp h.ge)

end Normed

noncomputable section Complex

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

instance : InnerProductSpace ℝ (Complexification E) :=
  inferInstanceAs (InnerProductSpace ℝ (WithLp 2 (E × E)))

/-- Multiplication by a complex scalar: `(x + iy) · (a,b) = (xa - yb, ya + xb)`. -/
instance : SMul ℂ (Complexification E) :=
  ⟨fun c v ↦ mk (c.re • v.re - c.im • v.im) (c.im • v.re + c.re • v.im)⟩

@[simp] theorem re_smul (c : ℂ) (v : Complexification E) :
    (c • v).re = c.re • v.re - c.im • v.im := rfl

@[simp] theorem im_smul (c : ℂ) (v : Complexification E) :
    (c • v).im = c.im • v.re + c.re • v.im := rfl

instance : Module ℂ (Complexification E) where
  one_smul v := by ext <;> simp
  mul_smul c d v := by
    ext <;> simp [Complex.mul_re, Complex.mul_im, sub_smul, add_smul, smul_sub,
      smul_add, smul_smul] <;> abel
  smul_zero c := by ext <;> simp
  smul_add c v w := by ext <;> simp [smul_add] <;> abel
  add_smul c d v := by
    ext <;> simp [Complex.add_re, Complex.add_im, add_smul] <;> abel
  zero_smul v := by ext <;> simp

/-- Complex scalar multiplication scales the `L²` norm by the modulus. -/
theorem norm_smul_eq (c : ℂ) (v : Complexification E) : ‖c • v‖ = ‖c‖ * ‖v‖ := by
  refine norm_eq_of_sq (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ?_
  have hc : ‖c‖ ^ 2 = c.re * c.re + c.im * c.im := RCLike.norm_sq_eq_def
  rw [norm_sq, re_smul, im_smul, norm_sub_sq_real, norm_add_sq_real, mul_pow,
    hc, norm_sq]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_left,
    real_inner_smul_right]
  ring

instance : NormedSpace ℂ (Complexification E) where
  norm_smul_le c v := (norm_smul_eq c v).le

/-- The complex inner product of the complexification. -/
instance : Inner ℂ (Complexification E) :=
  ⟨fun v w ↦ ⟨⟪v.re, w.re⟫_ℝ + ⟪v.im, w.im⟫_ℝ, ⟪v.re, w.im⟫_ℝ - ⟪v.im, w.re⟫_ℝ⟩⟩

@[simp] theorem inner_re (v w : Complexification E) :
    (⟪v, w⟫_ℂ).re = ⟪v.re, w.re⟫_ℝ + ⟪v.im, w.im⟫_ℝ := rfl

@[simp] theorem inner_im (v w : Complexification E) :
    (⟪v, w⟫_ℂ).im = ⟪v.re, w.im⟫_ℝ - ⟪v.im, w.re⟫_ℝ := rfl

instance : InnerProductSpace ℂ (Complexification E) where
  norm_sq_eq_re_inner v := by
    rw [norm_sq]
    simp
  conj_inner_symm v w := by
    apply Complex.ext <;>
      simp [Complex.conj_re, Complex.conj_im, real_inner_comm v.re w.re,
        real_inner_comm v.im w.im, real_inner_comm v.im w.re,
        real_inner_comm v.re w.im]
  add_left v w z := by
    apply Complex.ext <;> simp [inner_add_left] <;> ring
  smul_left v w c := by
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, inner_sub_left, inner_add_left,
        real_inner_smul_left] <;> ring

/-- The complexification of a real linear isometry equivalence: it acts on
real and imaginary parts separately, and is complex-linear because the
complex structure is built from real scalars. -/
def map (f : E ≃ₗᵢ[ℝ] E) : Complexification E ≃ₗᵢ[ℂ] Complexification E where
  toFun v := mk (f v.re) (f v.im)
  invFun v := mk (f.symm v.re) (f.symm v.im)
  left_inv v := by ext <;> simp
  right_inv v := by ext <;> simp
  map_add' v w := by ext <;> simp
  map_smul' c v := by ext <;> simp
  norm_map' v := by
    show ‖mk (f v.re) (f v.im)‖ = ‖v‖
    refine norm_eq_of_sq (norm_nonneg _) (norm_nonneg _) ?_
    rw [norm_sq, norm_sq, re_mk, im_mk, f.norm_map, f.norm_map]

@[simp] theorem re_map (f : E ≃ₗᵢ[ℝ] E) (v : Complexification E) :
    (map f v).re = f v.re := rfl

@[simp] theorem im_map (f : E ≃ₗᵢ[ℝ] E) (v : Complexification E) :
    (map f v).im = f v.im := rfl

@[simp] theorem map_mk (f : E ≃ₗᵢ[ℝ] E) (a b : E) :
    map f (mk a b) = mk (f a) (f b) := rfl

variable {G : Type*} [Group G]

/-- The complexification of a real orthogonal representation. -/
def mapHom (ρ : G →* (E ≃ₗᵢ[ℝ] E)) :
    G →* (Complexification E ≃ₗᵢ[ℂ] Complexification E) where
  toFun g := map (ρ g)
  map_one' := by
    ext v <;> simp [map_one]
  map_mul' g h := by
    ext v <;> simp [map_mul]

@[simp] theorem mapHom_apply (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (g : G)
    (v : Complexification E) : mapHom ρ g v = mk (ρ g v.re) (ρ g v.im) := rfl

end Complex

end Complexification
end NonsoficGroupsExist
