import NonsoficGroupsExist.KunRounding
import NonsoficGroupsExist.FiniteGraph

/-!
# A finite layer threshold with controlled boundary

This is the deterministic coarea selection behind Kun's threshold rounding.
It is proved by peeling the least positive layer, so no measure-theoretic
integration is hidden in the argument.
-/

namespace NonsoficGroupsExist
namespace KunThreshold

open FiniteMultiGraph

/-- A nonnegative function bounded by `L` has a strict superlevel whose
boundary is at most its average edge variation over the interval `(0,L)`. -/
theorem exists_superlevel_boundary_mul_le_variation
    (X : FiniteMultiGraph) (g : X.vertex → ℝ) (L : ℝ)
    (hg : ∀ x, 0 ≤ g x) (hL : 0 < L) (hupper : ∀ x, g x ≤ L) :
    ∃ t : ℝ, 0 < t ∧ t < L ∧
      L * (X.boundaryCard (X.superlevel g t) : ℝ) ≤ X.edgeVariation g := by
  classical
  let U := X.superlevel g 0
  by_cases hU : U.Nonempty
  · let values := U.image g
    have hvalues : values.Nonempty := hU.image g
    let m := values.min' hvalues
    have hmMem : m ∈ values := Finset.min'_mem values hvalues
    obtain ⟨x₀, hx₀U, hx₀m⟩ := Finset.mem_image.mp hmMem
    have hx₀pos : 0 < g x₀ := by simpa [U, superlevel] using hx₀U
    have hmpos : 0 < m := by simpa [hx₀m] using hx₀pos
    have hm0 : 0 ≤ m := hmpos.le
    have hmUpper : m ≤ L := by simpa [hx₀m] using hupper x₀
    have hmin : ∀ x, 0 < g x → m ≤ g x := by
      intro x hx
      apply Finset.min'_le values (g x)
      exact Finset.mem_image.mpr
        ⟨x, by simpa [U, superlevel] using hx, rfl⟩
    let g' : X.vertex → ℝ := fun x ↦ peel m (g x)
    have hg' : ∀ x, 0 ≤ g' x := fun x ↦ peel_nonnegative _ _
    have hL' : 0 ≤ L - m := sub_nonneg.mpr hmUpper
    have hupper' : ∀ x, g' x ≤ L - m := by
      intro x
      dsimp [g', peel]
      exact max_le (sub_le_sub_right (hupper x) m) hL'
    have hlevels (t : ℝ) (ht : 0 ≤ t) :
        X.superlevel g' t = X.superlevel g (t + m) := by
      ext x
      simp [g', superlevel, peel, ht, lt_sub_iff_add_lt]
    have hsupportSubset : X.superlevel g' 0 ⊆ U := by
      intro x hx
      have hx' : 0 < g x - m := by
        simpa [g', superlevel, peel] using hx
      have hxpos : 0 < g x := hmpos.trans (sub_pos.mp hx')
      simpa [U, superlevel] using hxpos
    have hx₀Not : x₀ ∉ X.superlevel g' 0 := by
      simp [g', superlevel, peel, hx₀m]
    have hsupportNe : X.superlevel g' 0 ≠ U := by
      intro heq
      exact hx₀Not (heq.symm ▸ hx₀U)
    have hdecrease : (X.superlevel g' 0).card < U.card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
        ⟨hsupportSubset, hsupportNe⟩)
    have hdecomp : X.edgeVariation g =
        m * X.boundaryCard U + X.edgeVariation g' := by
      simpa [U, g'] using edgeVariation_eq_layer_add_peel X g m hg hm0 hmin
    by_cases hfirst :
        L * (X.boundaryCard U : ℝ) ≤ X.edgeVariation g
    · let t := m / 2
      have ht0 : 0 < t := by dsimp [t]; linarith
      have htL : t < L := by dsimp [t]; nlinarith
      have hlevel : X.superlevel g t = U := by
        ext x
        constructor
        · intro hx
          have : t < g x := by simpa [superlevel] using hx
          have : 0 < g x := ht0.trans this
          simpa [U, superlevel] using this
        · intro hx
          have hxpos : 0 < g x := by simpa [U, superlevel] using hx
          have hmx := hmin x hxpos
          have : t < g x := by dsimp [t]; linarith
          simpa [superlevel] using this
      refine ⟨t, ht0, htL, ?_⟩
      simpa [hlevel] using hfirst
    · have hbad : X.edgeVariation g <
          L * (X.boundaryCard U : ℝ) := lt_of_not_ge hfirst
      have hLpos : 0 < L - m := by
        by_contra h
        have hLm : L ≤ m := by linarith
        have hmL : m = L := le_antisymm hmUpper hLm
        rw [hmL] at hdecomp
        have hvar' : 0 ≤ X.edgeVariation g' :=
          Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
        nlinarith
      obtain ⟨t, ht0, htL, htbound⟩ :=
        exists_superlevel_boundary_mul_le_variation X g' (L - m)
          hg' hLpos hupper'
      have hscaledBad := mul_lt_mul_of_pos_left hbad hmpos
      have hratio : L * X.edgeVariation g' <
          (L - m) * X.edgeVariation g := by
        nlinarith
      have hboundary :
          L * (X.boundaryCard (X.superlevel g' t) : ℝ) <
            X.edgeVariation g := by
        have hmul := mul_le_mul_of_nonneg_left htbound hL.le
        have hprod :
            (L - m) *
                (L * (X.boundaryCard (X.superlevel g' t) : ℝ)) ≤
              L * X.edgeVariation g' := by
          nlinarith
        have : (L - m) *
              (L * (X.boundaryCard (X.superlevel g' t) : ℝ)) <
            (L - m) * X.edgeVariation g := hprod.trans_lt hratio
        by_contra hnot
        have hle : X.edgeVariation g ≤
            L * (X.boundaryCard (X.superlevel g' t) : ℝ) :=
          not_lt.mp hnot
        have hscaled := mul_le_mul_of_nonneg_left hle hLpos.le
        exact (not_lt_of_ge hscaled) this
      refine ⟨t + m, add_pos_of_pos_of_nonneg ht0 hm0, ?_, ?_⟩
      · linarith
      · rw [← hlevels t ht0.le]
        exact hboundary.le
  · have hgzero : ∀ x, g x = 0 := by
      intro x
      have hnot : ¬ 0 < g x := by
        intro hx
        exact hU ⟨x, by simpa [U, superlevel] using hx⟩
      exact le_antisymm (not_lt.mp hnot) (hg x)
    refine ⟨L / 2, by linarith, by linarith, ?_⟩
    have ht : ¬ L / 2 < 0 := not_lt_of_ge (by positivity)
    simp [superlevel, hgzero, ht, edgeVariation, boundaryCard, boundary]
termination_by (X.superlevel g 0).card
decreasing_by simpa [U] using hdecrease

/-- The part of `f` lying between thresholds `a` and `b`, shifted into the
interval `[0,b-a]`. -/
def clippedLayer (f : α → ℝ) (a b : ℝ) (x : α) : ℝ :=
  max (min (f x) b - a) 0

theorem clippedLayer_nonneg (f : α → ℝ) (a b : ℝ) (x : α) :
    0 ≤ clippedLayer f a b x := le_max_right _ _

theorem clippedLayer_le {f : α → ℝ} {a b : ℝ} (hab : a ≤ b) (x : α) :
    clippedLayer f a b x ≤ b - a := by
  exact max_le (sub_le_sub_right (min_le_right (f x) b) a)
    (sub_nonneg.mpr hab)

theorem abs_clippedLayer_sub_le (f : α → ℝ) (a b : ℝ) (x y : α) :
    |clippedLayer f a b x - clippedLayer f a b y| ≤ |f x - f y| := by
  calc
    |clippedLayer f a b x - clippedLayer f a b y| ≤
        |(min (f x) b - a) - (min (f y) b - a)| := by
      exact abs_max_sub_max_le_abs _ _ 0
    _ = |min (f x) b - min (f y) b| := by ring_nf
    _ ≤ |f x - f y| := by
      simpa using abs_min_sub_min_le_max (f x) b (f y) b

/-- Clipping cannot increase total edge variation. -/
theorem edgeVariation_clippedLayer_le
    (X : FiniteMultiGraph) (f : X.vertex → ℝ) (a b : ℝ) :
    X.edgeVariation (clippedLayer f a b) ≤ X.edgeVariation f := by
  unfold edgeVariation
  exact Finset.sum_le_sum fun e he ↦
    abs_clippedLayer_sub_le f a b (X.first e) (X.second e)

/-- Coarea threshold selection on an arbitrary open interval, retaining the
sharper variation of the clipped layer. -/
theorem exists_superlevel_boundary_mul_sub_le_clippedVariation
    (X : FiniteMultiGraph) (f : X.vertex → ℝ) (a b : ℝ)
    (hab : a < b) :
    ∃ t : ℝ, a < t ∧ t < b ∧
      (b - a) * (X.boundaryCard (X.superlevel f t) : ℝ) ≤
        X.edgeVariation (clippedLayer f a b) := by
  let g := clippedLayer f a b
  have hL : 0 < b - a := sub_pos.mpr hab
  obtain ⟨t, ht0, htL, htbound⟩ :=
    exists_superlevel_boundary_mul_le_variation X g (b - a)
      (clippedLayer_nonneg f a b) hL
      (clippedLayer_le hab.le)
  have hlevel : X.superlevel g t = X.superlevel f (a + t) := by
    ext x
    have hatb : a + t < b := by linarith
    simp only [g, clippedLayer, superlevel, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro hx
      have hraw : t < min (f x) b - a :=
        (lt_max_iff.mp hx).resolve_right (not_lt_of_ge ht0.le)
      have : a + t < min (f x) b := by linarith
      exact this.trans_le (min_le_left _ _)
    · intro hx
      have hmin : a + t < min (f x) b := lt_min hx hatb
      have hraw : t < min (f x) b - a := by linarith
      exact hraw.trans_le (le_max_left _ _)
  refine ⟨a + t, by linarith, by linarith, ?_⟩
  rw [← hlevel]
  exact htbound

/-- Coarea threshold selection on an arbitrary open interval. -/
theorem exists_superlevel_boundary_mul_sub_le_variation
    (X : FiniteMultiGraph) (f : X.vertex → ℝ) (a b : ℝ)
    (hab : a < b) :
    ∃ t : ℝ, a < t ∧ t < b ∧
      (b - a) * (X.boundaryCard (X.superlevel f t) : ℝ) ≤
        X.edgeVariation f := by
  obtain ⟨t, hat, htb, ht⟩ :=
    exists_superlevel_boundary_mul_sub_le_clippedVariation X f a b hab
  exact ⟨t, hat, htb,
    ht.trans (edgeVariation_clippedLayer_le X f a b)⟩

/-- Sum of squared differences across edge occurrences. -/
def edgeSquareVariation (X : FiniteMultiGraph) (f : X.vertex → ℝ) : ℝ :=
  ∑ e, (f (X.first e) - f (X.second e)) ^ 2

/-- Edges on which clipping above `a` can be nonzero. -/
noncomputable def activeEdges (X : FiniteMultiGraph) (f : X.vertex → ℝ)
    (a : ℝ) : Finset X.edge :=
  Finset.univ.filter fun e ↦ a < f (X.first e) ∨ a < f (X.second e)

theorem clippedLayer_eq_zero_of_le
    {f : α → ℝ} {a b : ℝ} {x : α} (hx : f x ≤ a) :
    clippedLayer f a b x = 0 := by
  simp [clippedLayer, min_le_of_left_le hx]

/-- Squared finite coarea estimate.  The factor counting active edge
occurrences is retained explicitly; the generator-graph degree estimate is
proved separately. -/
theorem exists_boundary_sq_mul_sub_sq_le
    (X : FiniteMultiGraph) (f : X.vertex → ℝ) (a b : ℝ)
    (hab : a < b) :
    ∃ t : ℝ, a < t ∧ t < b ∧
      (b - a) ^ 2 * (X.boundaryCard (X.superlevel f t) : ℝ) ^ 2 ≤
        (activeEdges X f a).card * edgeSquareVariation X f := by
  classical
  obtain ⟨t, hat, htb, ht⟩ :=
    exists_superlevel_boundary_mul_sub_le_clippedVariation X f a b hab
  let g := clippedLayer f a b
  let E := activeEdges X f a
  have hvariation : X.edgeVariation g =
      ∑ e ∈ E, |g (X.first e) - g (X.second e)| := by
    unfold edgeVariation
    apply Eq.symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro e _ he
    have hboth : f (X.first e) ≤ a ∧ f (X.second e) ≤ a := by
      simpa [E, activeEdges] using he
    have hfirst : f (X.first e) ≤ a := by
      exact hboth.1
    have hsecond : f (X.second e) ≤ a := by
      exact hboth.2
    simp [g, clippedLayer_eq_zero_of_le hfirst,
      clippedLayer_eq_zero_of_le hsecond]
  have hcoarea :
      (b - a) * (X.boundaryCard (X.superlevel f t) : ℝ) ≤
        X.edgeVariation g :=
    ht
  have hcoareaSq := (sq_le_sq₀ (by positivity)
    (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)).2
      (hvariation ▸ hcoarea)
  have hcauchy :
      (∑ e ∈ E, |g (X.first e) - g (X.second e)|) ^ 2 ≤
        (E.card : ℝ) *
          ∑ e ∈ E, |g (X.first e) - g (X.second e)| ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq E
      (fun _ ↦ (1 : ℝ))
      (fun e ↦ |g (X.first e) - g (X.second e)|)
  have hclipSq :
      ∑ e ∈ E, |g (X.first e) - g (X.second e)| ^ 2 ≤
        edgeSquareVariation X f := by
    unfold edgeSquareVariation
    calc
      ∑ e ∈ E, |g (X.first e) - g (X.second e)| ^ 2 ≤
          ∑ e ∈ E, (f (X.first e) - f (X.second e)) ^ 2 := by
        apply Finset.sum_le_sum
        intro e _
        have h := abs_clippedLayer_sub_le f a b (X.first e) (X.second e)
        have hs := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).2 h
        simpa [g, sq_abs] using hs
      _ ≤ ∑ e, (f (X.first e) - f (X.second e)) ^ 2 := by
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _) (fun _ _ _ ↦ sq_nonneg _)
  refine ⟨t, hat, htb, ?_⟩
  calc
    (b - a) ^ 2 * (X.boundaryCard (X.superlevel f t) : ℝ) ^ 2 =
        ((b - a) * (X.boundaryCard (X.superlevel f t) : ℝ)) ^ 2 := by ring
    _ ≤ (∑ e ∈ E, |g (X.first e) - g (X.second e)|) ^ 2 := hcoareaSq
    _ ≤ (E.card : ℝ) *
        ∑ e ∈ E, |g (X.first e) - g (X.second e)| ^ 2 := hcauchy
    _ ≤ (E.card : ℝ) * edgeSquareVariation X f := by
      gcongr

end KunThreshold
end NonsoficGroupsExist
