import NonsoficGroupsExist.KazhdanGNS
import NonsoficGroupsExist.KazhdanComplex

/-!
# Universe reduction for Kazhdan's property `(T)`

`IsKazhdanPair.{u, v}` quantifies over real Hilbert spaces in `Type v`.  The
textbook definition of property `(T)` quantifies over *all* Hilbert spaces.
This module removes that restriction: a Kazhdan pair for representations on
spaces of the *same* universe as the group already controls representations on
spaces of every universe.

The reduction is the classical countable-orbit argument.  Given a
representation `ρ` on `E : Type w` with an almost invariant unit vector `x`,
the diagonal matrix coefficient `g ↦ ⟪x, ρ g x⟫` is a positive-definite
function on `G`, so its GNS representation lives on a Hilbert space built out
of `G` alone -- in `Type u`.  The map sending a free generator `(g, u)` of the
pre-GNS space to `u • ρ g x` preserves inner products, hence extends to an
isometric `G`-equivariant embedding of the GNS space into `E` carrying the
cyclic vector to `x`.  Almost invariance and nonvanishing therefore travel
both ways along this embedding, and the universe-`u` hypothesis applies.
-/

namespace NonsoficGroupsExist
namespace KazhdanUniverse

open KazhdanGNS
open KazhdanFiniteModel

universe u w

variable {G : Type u} [Group G]
variable {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The diagonal matrix coefficient of a vector in an orthogonal
representation. -/
noncomputable def coeff (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) : G → ℝ :=
  fun g ↦ inner ℝ x (ρ g x)

/-- Inner products of orbit vectors are values of the matrix coefficient. -/
theorem inner_orbit (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) (a b : G) :
    inner ℝ (ρ a x) (ρ b x) = coeff ρ x (a⁻¹ * b) := by
  have hb : ρ b x = (ρ a) ((ρ (a⁻¹ * b)) x) := by
    have hmul : ρ a * ρ (a⁻¹ * b) = ρ b := by rw [← map_mul]; simp
    conv_lhs => rw [← hmul]
    rfl
  rw [hb, (ρ a).inner_map_map]
  rfl

/-- The representation of a product acts by composition. -/
theorem apply_mul (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (t g : G) (v : E) :
    ρ (t * g) v = ρ t (ρ g v) := by
  rw [map_mul]; rfl

@[simp] theorem coeff_one (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    coeff ρ x 1 = ‖x‖ ^ 2 := by
  simp [coeff]

/-- Matrix coefficients of orthogonal representations are positive
definite. -/
theorem coeff_isPositiveDefinite (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    IsPositiveDefinite (coeff ρ x) := by
  constructor
  · intro g h
    rw [← inner_orbit ρ x g h, ← inner_orbit ρ x h g]
    exact real_inner_comm _ _
  · intro F c
    have key : ∑ i ∈ F, ∑ j ∈ F, c i * c j * coeff ρ x (i⁻¹ * j)
        = ‖∑ i ∈ F, c i • ρ i x‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq]
      simp_rw [sum_inner, inner_sum, real_inner_smul_left,
        real_inner_smul_right, inner_orbit]
      simp [mul_assoc]
    rw [key]
    positivity

/-- The matrix coefficient of a vector, bundled as a positive-definite
function so that it generates a GNS representation. -/
noncomputable def gnsFunction (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    PositiveDefiniteFunction G :=
  ⟨coeff ρ x, coeff_isPositiveDefinite ρ x⟩

@[simp] theorem gnsFunction_apply (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) (g : G) :
    gnsFunction ρ x g = inner ℝ x (ρ g x) := rfl

/-- The linear map from the pre-GNS space of `coeff ρ x` into `E` sending the
free generator indexed by `(g, u)` to `u • ρ g x`. -/
noncomputable def preCyclic (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    PreHilbertSpace (gnsFunction ρ x) →ₗ[ℝ] E :=
  Finsupp.linearCombination ℝ (fun i : G × ℝ ↦ i.2 • ρ i.1 x)

@[simp] theorem preCyclic_single (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E)
    (i : G × ℝ) (c : ℝ) :
    preCyclic ρ x (Finsupp.single i c) = (c * i.2) • ρ i.1 x := by
  simp [preCyclic, mul_smul]

/-- The generator map preserves inner products: this is exactly the statement
that the GNS inner product of `coeff ρ x` is the Gram form of the orbit of
`x`. -/
theorem inner_preCyclic (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    ∀ ff gg : PreHilbertSpace (gnsFunction ρ x),
      inner ℝ (preCyclic ρ x ff) (preCyclic ρ x gg) = inner ℝ ff gg := by
  intro ff
  induction ff using Finsupp.induction with
  | zero => intro gg; simp
  | single_add i c f _ _ ih =>
      intro gg
      rw [map_add, inner_add_left, inner_add_left, ih gg]
      congr 1
      induction gg using Finsupp.induction with
      | zero => simp
      | single_add j d g _ _ ih2 =>
          rw [map_add, inner_add_right, inner_add_right, ih2]
          congr 1
          rw [preCyclic_single, preCyclic_single, real_inner_smul_left,
            real_inner_smul_right, inner_orbit,
            inner_single (gnsFunction ρ x) i j c d]
          simp only [gnsFunction_apply, coeff]
          ring

/-- The generator map is norm preserving. -/
theorem norm_preCyclic (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E)
    (ff : PreHilbertSpace (gnsFunction ρ x)) :
    ‖preCyclic ρ x ff‖ = ‖ff‖ := by
  have h := inner_preCyclic ρ x ff ff
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  nlinarith [h, norm_nonneg (preCyclic ρ x ff), norm_nonneg ff]

/-- The generator map is `1`-Lipschitz, hence uniformly continuous, hence
extends to the completion. -/
theorem lipschitzWith_preCyclic (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    LipschitzWith 1 (preCyclic ρ x) := by
  apply LipschitzWith.of_dist_le_mul
  intro ff gg
  rw [dist_eq_norm, dist_eq_norm, ← map_sub, norm_preCyclic]
  simp

theorem uniformContinuous_preCyclic (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    UniformContinuous (preCyclic ρ x) :=
  (lipschitzWith_preCyclic ρ x).uniformContinuous

/-- The generator map intertwines left translation of the pre-GNS space with
the representation on `E`. -/
theorem preCyclic_preTranslation (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) (s : G) :
    ∀ ff : PreHilbertSpace (gnsFunction ρ x),
      preCyclic ρ x (preTranslationLinearEquiv (gnsFunction ρ x) s ff) =
        ρ s (preCyclic ρ x ff) := by
  intro ff
  induction ff using Finsupp.induction with
  | zero => simp
  | single_add i c f _ _ ih =>
      have h1 : preCyclic ρ x (preTranslationLinearEquiv (gnsFunction ρ x) s
            (Finsupp.single i c + f)) =
          (c * i.2) • ρ (s * i.1) x + ρ s (preCyclic ρ x f) := by
        rw [map_add, preTranslationLinearEquiv_single, map_add, ih,
          preCyclic_single]
        simp [leftIndexEquiv]
      have h2 : ρ s (preCyclic ρ x (Finsupp.single i c + f)) =
          (c * i.2) • ρ (s * i.1) x + ρ s (preCyclic ρ x f) := by
        rw [map_add, preCyclic_single, (ρ s).map_add, (ρ s).map_smul,
          apply_mul]
      rw [h1, h2]

section Complete

variable [CompleteSpace E]

/-- The isometric `G`-equivariant embedding of the GNS space of `coeff ρ x`
into `E`, obtained by extending the generator map to the completion. -/
noncomputable def cyclicMap (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    HilbertSpace (gnsFunction ρ x) → E :=
  UniformSpace.Completion.extension (preCyclic ρ x)

theorem continuous_cyclicMap (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    Continuous (cyclicMap ρ x) :=
  UniformSpace.Completion.continuous_extension

omit [CompleteSpace E] in
@[simp] theorem cyclicMap_coe (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E)
    (ff : PreHilbertSpace (gnsFunction ρ x)) :
    cyclicMap ρ x (UniformSpace.Completion.coe' ff) = preCyclic ρ x ff :=
  UniformSpace.Completion.extension_coe (uniformContinuous_preCyclic ρ x) ff

/-- The embedding is norm preserving. -/
theorem norm_cyclicMap (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E)
    (z : HilbertSpace (gnsFunction ρ x)) : ‖cyclicMap ρ x z‖ = ‖z‖ := by
  induction z using UniformSpace.Completion.induction_on with
  | hp =>
      exact isClosed_eq (continuous_norm.comp (continuous_cyclicMap ρ x))
        continuous_norm
  | ih ff =>
      rw [cyclicMap_coe, UniformSpace.Completion.norm_coe, norm_preCyclic]

theorem cyclicMap_add (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E)
    (z w : HilbertSpace (gnsFunction ρ x)) :
    cyclicMap ρ x (z + w) = cyclicMap ρ x z + cyclicMap ρ x w := by
  induction z, w using UniformSpace.Completion.induction_on₂ with
  | hp =>
      refine isClosed_eq ?_ ?_
      · exact (continuous_cyclicMap ρ x).comp continuous_add
      · exact ((continuous_cyclicMap ρ x).comp continuous_fst).add
          ((continuous_cyclicMap ρ x).comp continuous_snd)
  | ih ff gg =>
      rw [← UniformSpace.Completion.coe_add, cyclicMap_coe, cyclicMap_coe,
        cyclicMap_coe, map_add]

theorem cyclicMap_smul (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) (r : ℝ)
    (z : HilbertSpace (gnsFunction ρ x)) :
    cyclicMap ρ x (r • z) = r • cyclicMap ρ x z := by
  induction z using UniformSpace.Completion.induction_on with
  | hp =>
      refine isClosed_eq ?_ ?_
      · exact (continuous_cyclicMap ρ x).comp (continuous_const_smul r)
      · exact (continuous_const_smul r).comp (continuous_cyclicMap ρ x)
  | ih ff =>
      rw [← UniformSpace.Completion.coe_smul, cyclicMap_coe, cyclicMap_coe,
        map_smul]

/-- The embedding of the GNS space of `coeff ρ x` into `E`, bundled as a
linear isometry. -/
noncomputable def cyclicIsometry (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    HilbertSpace (gnsFunction ρ x) →ₗᵢ[ℝ] E where
  toFun := cyclicMap ρ x
  map_add' := cyclicMap_add ρ x
  map_smul' := cyclicMap_smul ρ x
  norm_map' := norm_cyclicMap ρ x

@[simp] theorem cyclicIsometry_apply (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E)
    (z : HilbertSpace (gnsFunction ρ x)) :
    cyclicIsometry ρ x z = cyclicMap ρ x z := rfl

theorem cyclicMap_sub (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E)
    (z w : HilbertSpace (gnsFunction ρ x)) :
    cyclicMap ρ x (z - w) = cyclicMap ρ x z - cyclicMap ρ x w :=
  (cyclicIsometry ρ x).map_sub z w

omit [CompleteSpace E] in
/-- The embedding sends the cyclic vector to the orbit of `x`. -/
@[simp] theorem cyclicMap_kernelVector (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E)
    (g : G) : cyclicMap ρ x (kernelVector (gnsFunction ρ x) g) = ρ g x := by
  change cyclicMap ρ x (UniformSpace.Completion.coe'
    (Finsupp.single (g, (1 : ℝ)) 1 :
      PreHilbertSpace (gnsFunction ρ x))) = ρ g x
  rw [cyclicMap_coe, preCyclic_single]
  simp

/-- The embedding intertwines the GNS representation with `ρ`. -/
theorem cyclicMap_representation (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) (s : G)
    (z : HilbertSpace (gnsFunction ρ x)) :
    cyclicMap ρ x (representation (gnsFunction ρ x) s z) =
      ρ s (cyclicMap ρ x z) := by
  induction z using UniformSpace.Completion.induction_on with
  | hp =>
      refine isClosed_eq ?_ ?_
      · exact (continuous_cyclicMap ρ x).comp
          (representation (gnsFunction ρ x) s).continuous
      · exact (ρ s).continuous.comp (continuous_cyclicMap ρ x)
  | ih ff =>
      have hrep : representation (gnsFunction ρ x) s =
          translationOperator (gnsFunction ρ x) s := rfl
      rw [hrep, translationOperator_coe, cyclicMap_coe, cyclicMap_coe,
        preCyclic_preTranslation]

/-- The embedding carries a nonzero vector to a nonzero vector. -/
theorem cyclicMap_ne_zero (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E)
    {z : HilbertSpace (gnsFunction ρ x)} (hz : z ≠ 0) :
    cyclicMap ρ x z ≠ 0 := by
  intro hcontra
  apply hz
  have := norm_cyclicMap ρ x z
  rw [hcontra, norm_zero] at this
  exact norm_eq_zero.mp this.symm

end Complete

section Ulift

universe v

variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A universe lift of a real inner product space is one again, with the same
inner product and the same norm. -/
instance : Inner ℝ (ULift.{w} F) := ⟨fun a b ↦ inner ℝ a.down b.down⟩

@[simp] theorem inner_ulift (a b : ULift.{w} F) :
    inner ℝ a b = inner ℝ a.down b.down := rfl

instance : InnerProductSpace ℝ (ULift.{w} F) where
  norm_sq_eq_re_inner a := by
    simpa [ULift.norm_def] using
      norm_sq_eq_re_inner (𝕜 := ℝ) (E := F) a.down
  conj_inner_symm a b := by
    simpa using real_inner_comm b.down a.down
  add_left a b c := by
    simpa using inner_add_left (𝕜 := ℝ) a.down b.down c.down
  smul_left a b r := by
    simpa using real_inner_smul_left a.down b.down r

/-- A linear isometry equivalence lifted to a higher universe. -/
def uliftEquiv (f : F ≃ₗᵢ[ℝ] F) : ULift.{w} F ≃ₗᵢ[ℝ] ULift.{w} F where
  toFun a := ULift.up (f a.down)
  invFun a := ULift.up (f.symm a.down)
  left_inv a := by simp
  right_inv a := by simp
  map_add' a b := by simp
  map_smul' r a := by simp
  norm_map' a := by simp [ULift.norm_def]

@[simp] theorem uliftEquiv_apply (f : F ≃ₗᵢ[ℝ] F) (a : ULift.{w} F) :
    uliftEquiv f a = ULift.up (f a.down) := rfl

/-- An orthogonal representation lifted to a higher universe. -/
def uliftHom (ρ : G →* (F ≃ₗᵢ[ℝ] F)) :
    G →* (ULift.{w} F ≃ₗᵢ[ℝ] ULift.{w} F) where
  toFun g := uliftEquiv (ρ g)
  map_one' := by ext a; simp [map_one]
  map_mul' g h := by ext a; simp [map_mul]

@[simp] theorem uliftHom_apply (ρ : G →* (F ≃ₗᵢ[ℝ] F)) (g : G)
    (a : ULift.{w} F) : uliftHom ρ g a = ULift.up (ρ g a.down) := rfl

end Ulift

end KazhdanUniverse

open KazhdanUniverse KazhdanGNS in
/-- **Universe reduction.**  A Kazhdan pair for representations on Hilbert
spaces in the universe of the group is a Kazhdan pair for representations on
Hilbert spaces in *every* universe: the cyclic subrepresentation generated by
an almost invariant vector is a GNS representation, which is built from the
group alone. -/
theorem IsKazhdanPair.liftUniverse {G : Type u} [Group G] {Q : Finset G}
    {ε : ℝ} (h : IsKazhdanPair.{u, u} G Q ε) : IsKazhdanPair.{u, w} G Q ε := by
  refine ⟨h.1, ?_⟩
  intro E _ _ _ ρ x hx hnear
  set p := gnsFunction ρ x with hp
  set δ : HilbertSpace p := kernelVector p 1 with hδ
  have hδx : cyclicMap ρ x δ = x := by
    rw [hδ, cyclicMap_kernelVector]
    simp
  have hδnorm : ‖δ‖ = 1 := by
    rw [← norm_cyclicMap ρ x δ, hδx, hx]
  have hδnear : ∀ q ∈ Q,
      ‖representation p q δ - δ‖ < ε := by
    intro q hq
    rw [← norm_cyclicMap ρ x (representation p q δ - δ), cyclicMap_sub,
      cyclicMap_representation, hδx]
    exact hnear q hq
  obtain ⟨y, hy0, hy⟩ := h.2 (HilbertSpace p) (representation p) δ hδnorm hδnear
  refine ⟨cyclicMap ρ x y, cyclicMap_ne_zero ρ x hy0, fun g ↦ ?_⟩
  rw [← cyclicMap_representation ρ x g y, hy g]

/-- **Universe reduction** for property `(T)`: the property at the universe of
the group implies it at every universe. -/
theorem HasKazhdanPropertyT.liftUniverse {G : Type u} [Group G]
    (h : HasKazhdanPropertyT.{u, u} G) : HasKazhdanPropertyT.{u, w} G := by
  obtain ⟨Q, a, hQ⟩ := h
  exact ⟨Q, a, hQ.liftUniverse⟩

open KazhdanUniverse in
/-- The converse reduction: a Kazhdan pair for representations on the larger
universe is one for representations on the universe of the group, by lifting
a representation along `ULift`. -/
theorem IsKazhdanPair.lowerUniverse {G : Type u} [Group G] {Q : Finset G}
    {ε : ℝ} (h : IsKazhdanPair.{u, max u w} G Q ε) :
    IsKazhdanPair.{u, u} G Q ε := by
  refine ⟨h.1, ?_⟩
  intro E _ _ _ ρ x hx hnear
  have hnear' : ∀ q ∈ Q,
      ‖uliftHom.{u, u, w} ρ q (ULift.up x) - ULift.up x‖ < ε := by
    intro q hq
    have : uliftHom.{u, u, w} ρ q (ULift.up x) - ULift.up x =
        ULift.up (ρ q x - x) := rfl
    rw [this, ULift.norm_up]
    exact hnear q hq
  obtain ⟨y, hy0, hy⟩ :=
    h.2 (ULift.{w} E) (uliftHom ρ) (ULift.up x) (by rw [ULift.norm_up]; exact hx)
      hnear'
  refine ⟨y.down, ?_, fun g ↦ ?_⟩
  · intro hcontra
    exact hy0 (by ext; simpa using hcontra)
  · have := hy g
    rw [uliftHom_apply] at this
    exact congrArg ULift.down this

/-- Property `(T)` does not depend on the universe of the representation
spaces. -/
theorem hasKazhdanPropertyT_universe_iff {G : Type u} [Group G] :
    HasKazhdanPropertyT.{u, u} G ↔ HasKazhdanPropertyT.{u, max u w} G := by
  constructor
  · exact fun h ↦ h.liftUniverse
  · rintro ⟨Q, a, hQ⟩
    exact ⟨Q, a, hQ.lowerUniverse⟩

/-- **Property `(T)` as formalized here is the textbook property `(T)`.**
The real orthogonal formulation restricted to Hilbert spaces in the universe
of the group is equivalent to the complex-unitary formulation on Hilbert
spaces of every universe. -/
theorem hasKazhdanPropertyT_iff_textbook {G : Type u} [Group G] :
    HasKazhdanPropertyT.{u, u} G ↔ HasKazhdanPropertyTComplex.{u, max u w} G := by
  rw [hasKazhdanPropertyT_universe_iff.{u, w}]
  exact hasKazhdanPropertyT_iff_complex

end NonsoficGroupsExist
