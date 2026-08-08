import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# The pinning interface: almost-containment and perturbed spectral gaps

Two elementary quantitative lemmas, the load-bearing bricks of any
"defect-localized commutant pinning" argument on the free-lamp families
(item 2 of `docs/AGENDA.md`), stated for finite-dimensional inner product
spaces over `ℝ` or `ℂ`.

* **Almost-containment rigidity** (`exists_mem_close_of_almost_le`): a
  subspace `δ`-almost contained in a subspace of the *same dimension* is
  `δ/(1-δ)`-almost equal to it: the orthogonal projection restricted to the
  first is injective by the defect bound, hence surjective by dimension,
  and minimality converts surjectivity into proximity.  This is the
  quantitative form of the co-Hopfian step driving `commutant_no_growth`
  and the finite-dimensional collapse: it is what lets an *approximate*
  commutant inherit the rigidity of exact ones.

* **Perturbed gap pinning** (`dist_le_defect_div_gap`,
  `dist_le_perturbed_defect_div_gap`): if an operator fixes a subspace and
  contracts its orthogonal complement by `1 - κ`, then every vector is
  within `defect/κ` of the subspace — where the defect may be measured
  against any `ε`-perturbation of the operator, at cost `ε‖v‖/κ`.  Sums of
  pointwise-close operator families are pointwise close
  (`sum_apply_dist_le`), so a spectral gap certified for an *exact*
  sub-action transfers to the almost-representations hyperlinear models
  actually provide, with no stability theorem consumed.

Together: wherever a model carries an exactly-acting core with a Kazhdan
gap, vectors almost-commuting with the core are pinned near its exact
commutant, and the equal-dimension rigidity transports the pinning along
conjugation.  What these lemmas do *not* provide — the genuinely open
part, stated as such in the agenda — is the localization of a model's
defect off such a core for the Kun--Thom pairs.
-/

namespace NonsoficGroupsExist

open Module

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- **Almost-containment rigidity.**  If `finrank V = finrank W` and every
`v ∈ V` is `δ‖v‖`-close to `W` with `0 ≤ δ < 1`, then every `w ∈ W` is
`(δ/(1-δ))‖w‖`-close to `V`. -/
theorem exists_mem_close_of_almost_le {V W : Submodule 𝕜 E}
    (hrank : finrank 𝕜 V = finrank 𝕜 W) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ < 1)
    (h : ∀ v ∈ V, ‖v - W.starProjection v‖ ≤ δ * ‖v‖) :
    ∀ w ∈ W, ∃ v ∈ V, ‖w - v‖ ≤ δ / (1 - δ) * ‖w‖ := by
  classical
  set f : V →ₗ[𝕜] E :=
    (W.starProjection : E →L[𝕜] E).toLinearMap.comp V.subtype with hf
  have hmem : ∀ v : V, f v ∈ W := fun v => W.starProjection_apply_mem _
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro v hv
    have hv0 : f v = 0 := hv
    have hb := h (v : E) v.2
    rw [show W.starProjection (v : E) = f v from rfl, hv0, sub_zero] at hb
    have hzero : ‖(v : E)‖ = 0 := by nlinarith [norm_nonneg (v : E)]
    have hcoe : (v : E) = 0 := norm_eq_zero.mp hzero
    simpa [Submodule.mem_bot] using Subtype.ext hcoe
  have hrange_le : LinearMap.range f ≤ W := by
    rintro _ ⟨v, rfl⟩
    exact hmem v
  have hrange_eq : LinearMap.range f = W := by
    refine Submodule.eq_of_le_of_finrank_le hrange_le ?_
    rw [LinearMap.finrank_range_of_inj hinj, hrank]
  intro w hw
  obtain ⟨v, hv⟩ : w ∈ LinearMap.range f := hrange_eq.symm ▸ hw
  refine ⟨(v : E), v.2, ?_⟩
  have hproj : W.starProjection (v : E) = w := hv
  have hb := h (v : E) v.2
  rw [hproj] at hb
  have h1δ : (0 : ℝ) < 1 - δ := by linarith
  have htri : ‖(v : E)‖ ≤ ‖(v : E) - w‖ + ‖w‖ := by
    have hh := norm_add_le ((v : E) - w) w
    simpa using hh
  have hvbound : ‖(v : E)‖ ≤ ‖w‖ / (1 - δ) := by
    rw [le_div_iff₀ h1δ]
    nlinarith
  have hfinal : ‖(v : E) - w‖ ≤ δ / (1 - δ) * ‖w‖ := by
    calc ‖(v : E) - w‖ ≤ δ * ‖(v : E)‖ := hb
      _ ≤ δ * (‖w‖ / (1 - δ)) := mul_le_mul_of_nonneg_left hvbound hδ0
      _ = δ / (1 - δ) * ‖w‖ := by ring
  rw [norm_sub_rev] at hfinal
  exact hfinal

/-- **Gap pinning.**  If `T` fixes `F` pointwise and contracts `Fᗮ` by
`1 - κ`, every vector is within `‖T v - v‖ / κ` of `F`. -/
theorem dist_le_defect_div_gap {F : Submodule 𝕜 E} {T : E →ₗ[𝕜] E} {κ : ℝ}
    (hκ : 0 < κ) (hfix : ∀ x ∈ F, T x = x)
    (hgap : ∀ x ∈ Fᗮ, ‖T x‖ ≤ (1 - κ) * ‖x‖) (v : E) :
    ‖v - F.starProjection v‖ ≤ ‖T v - v‖ / κ := by
  set p : E := v - F.starProjection v with hp
  have hpmem : p ∈ Fᗮ := F.sub_starProjection_mem_orthogonal v
  have hTv : T v - v = T p - p := by
    have hTfix : T (F.starProjection v) = F.starProjection v :=
      hfix _ (F.starProjection_apply_mem v)
    have hsplit : v = F.starProjection v + p := by
      rw [hp]
      abel
    calc T v - v
        = T (F.starProjection v + p) - (F.starProjection v + p) := by
          rw [← hsplit]
      _ = T p - p := by
          rw [map_add, hTfix]
          abel
  have hlow : κ * ‖p‖ ≤ ‖T p - p‖ := by
    have htri : ‖p‖ ≤ ‖p - T p‖ + ‖T p‖ := by
      have hh := norm_add_le (p - T p) (T p)
      simpa using hh
    have hgap' := hgap p hpmem
    have hrev : ‖p - T p‖ = ‖T p - p‖ := norm_sub_rev _ _
    nlinarith
  rw [hTv, le_div_iff₀ hκ]
  nlinarith

/-- **Gap pinning against a perturbed operator**: the defect may be
measured on any `ε`-close operator, at cost `ε‖v‖/κ`. -/
theorem dist_le_perturbed_defect_div_gap {F : Submodule 𝕜 E}
    {T T' : E →ₗ[𝕜] E} {κ ε : ℝ} (hκ : 0 < κ)
    (hfix : ∀ x ∈ F, T x = x)
    (hgap : ∀ x ∈ Fᗮ, ‖T x‖ ≤ (1 - κ) * ‖x‖)
    (hnear : ∀ x : E, ‖T x - T' x‖ ≤ ε * ‖x‖) (v : E) :
    ‖v - F.starProjection v‖ ≤ (‖T' v - v‖ + ε * ‖v‖) / κ := by
  have h1 := dist_le_defect_div_gap hκ hfix hgap v
  have htri : ‖T v - v‖ ≤ ‖T v - T' v‖ + ‖T' v - v‖ := by
    have hh := norm_add_le (T v - T' v) (T' v - v)
    simpa using hh
  have h2 : ‖T v - v‖ ≤ ‖T' v - v‖ + ε * ‖v‖ := by
    have := hnear v
    linarith
  have hdiv : ‖T v - v‖ / κ ≤ (‖T' v - v‖ + ε * ‖v‖) / κ :=
    div_le_div_of_nonneg_right h2 hκ.le
  linarith

omit [FiniteDimensional 𝕜 E] in
/-- Sums of pointwise-`ε`-close operator families are pointwise
`card·ε`-close: the transfer step for averaging operators. -/
theorem sum_apply_dist_le {ι : Type*} (s : Finset ι) (T T' : ι → E →ₗ[𝕜] E)
    {ε : ℝ} (h : ∀ i ∈ s, ∀ x : E, ‖T i x - T' i x‖ ≤ ε * ‖x‖) (x : E) :
    ‖(∑ i ∈ s, T i) x - (∑ i ∈ s, T' i) x‖ ≤ s.card * ε * ‖x‖ := by
  classical
  have hsum : (∑ i ∈ s, T i) x - (∑ i ∈ s, T' i) x
      = ∑ i ∈ s, (T i x - T' i x) := by
    simp [Finset.sum_sub_distrib]
  rw [hsum]
  calc ‖∑ i ∈ s, (T i x - T' i x)‖ ≤ ∑ i ∈ s, ‖T i x - T' i x‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _i ∈ s, ε * ‖x‖ := Finset.sum_le_sum fun i hi => h i hi x
    _ = s.card * ε * ‖x‖ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

end NonsoficGroupsExist
