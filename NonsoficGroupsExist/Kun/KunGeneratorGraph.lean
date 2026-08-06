import NonsoficGroupsExist.Kun.KunThreshold
import NonsoficGroupsExist.Criterion.Criterion
import NonsoficGroupsExist.Matching.FiniteMarkov

/-!
# Generator-graph cut and variation identities

These identities connect the analytic finite Markov estimates to the actual
occurrence graph of a sofic approximation.  Generator labels remain distinct,
and fixed-point loops contribute neither to cuts nor to variation.
-/

namespace NonsoficGroupsExist
namespace KunGeneratorGraph

open KazhdanGNS
open KazhdanFiniteModel
open FiniteMultiGraph
open scoped symmDiff

variable {G : Type} [Group G]

/-- The occurrence boundary of the generator graph is exactly the directed
generator cut size used by the Markov estimate. -/
theorem boundaryCard_generatorGraph
    (Y : FiniteModel) (T : Finset G) (act : G → Equiv.Perm Y)
    (U : Finset Y) :
    (generatorGraph Y T act).boundaryCard U =
      generatorCutSize Y act T U := by
  classical
  let crosses : T → Y → Prop := fun t y ↦
    (y ∈ U ∧ act t.1 y ∉ U) ∨ (act t.1 y ∈ U ∧ y ∉ U)
  have hleft :
      (generatorGraph Y T act).boundaryCard U =
        (Finset.univ.filter fun p : T × Y ↦ crosses p.1 p.2).card := by
    unfold boundaryCard boundary
    dsimp only [generatorGraph]
    apply Finset.card_bij (fun e _ ↦ e.1)
    · intro e he
      have hecross : crosses e.1.1 e.1.2 := by
        simpa [crosses] using (Finset.mem_filter.mp he).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hecross⟩
    · intro e₁ _ e₂ _ heq
      exact Subtype.ext heq
    · intro p hp
      have hcross : crosses p.1 p.2 := (Finset.mem_filter.mp hp).2
      have hmove : act p.1.1 p.2 ≠ p.2 := by
        intro heq
        simp [crosses, heq] at hcross
      let e : (generatorGraph Y T act).edge :=
        ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmove⟩⟩
      refine ⟨e, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simpa [e, crosses] using hcross⟩
  have hpairs :
      (Finset.univ.filter fun p : T × Y ↦ crosses p.1 p.2).card =
        ∑ t : T, (Finset.univ.filter fun y : Y ↦ crosses t y).card := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter,
      Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have hper (t : T) :
      ((U.map (act t.1).toEmbedding) ∆ U).card =
        (Finset.univ.filter fun y : Y ↦ crosses t y).card := by
    apply Finset.card_bij (fun z _ ↦ (act t.1).symm z)
    · intro z hz
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simp only [Finset.mem_symmDiff] at hz
      simpa [crosses] using hz
    · intro z₁ _ z₂ _ h
      exact (act t.1).symm.injective h
    · intro y hy
      refine ⟨act t.1 y, ?_, (act t.1).symm_apply_apply y⟩
      have hycross : crosses t y := (Finset.mem_filter.mp hy).2
      simp only [Finset.mem_symmDiff]
      simpa [crosses] using hycross
  rw [hleft, hpairs, generatorCutSize]
  calc
    ∑ t : T, (Finset.univ.filter fun y : Y ↦ crosses t y).card =
        ∑ t : T, ((U.map (act t.1).toEmbedding) ∆ U).card := by
      apply Finset.sum_congr rfl
      intro t _
      exact (hper t).symm
    _ = ∑ s ∈ T, ((U.map (act s).toEmbedding) ∆ U).card := by
      simpa using Finset.sum_attach T
        (fun s ↦ ((U.map (act s).toEmbedding) ∆ U).card)

/-- Removing fixed-point loops does not change the total generator variation,
so the graph variation is the full label-by-vertex sum. -/
theorem edgeVariation_generatorGraph
    (Y : FiniteModel) (T : Finset G) (act : G → Equiv.Perm Y)
    (f : Y → ℝ) :
    (generatorGraph Y T act).edgeVariation f =
      ∑ t : T, ∑ y : Y, |f (act t.1 y) - f y| := by
  classical
  let arcs : Finset (T × Y) :=
    Finset.univ.filter fun p ↦ act p.1.1 p.2 ≠ p.2
  unfold edgeVariation
  dsimp only [generatorGraph]
  change (∑ a : ↑(Finset.univ.filter fun p : T × Y ↦
      act p.1.1 p.2 ≠ p.2), |f a.1.2 - f (act a.1.1.1 a.1.2)|) = _
  calc
    (∑ a : ↑(Finset.univ.filter fun p : T × Y ↦
        act p.1.1 p.2 ≠ p.2), |f a.1.2 - f (act a.1.1.1 a.1.2)|) =
        arcs.sum fun p ↦ |f p.2 - f (act p.1.1 p.2)| := by
      simpa [arcs] using Finset.sum_attach arcs
        (fun p : T × Y ↦ |f p.2 - f (act p.1.1 p.2)|)
    _ = ∑ p : T × Y, |f p.2 - f (act p.1.1 p.2)| := by
      apply Finset.sum_subset (Finset.subset_univ arcs)
      intro p _ hp
      have hfix : act p.1.1 p.2 = p.2 := by
        by_contra hmove
        exact hp (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmove⟩)
      simp [hfix]
    _ = ∑ t : T, ∑ y : Y, |f y - f (act t.1 y)| := by
      rw [Fintype.sum_prod_type]
    _ = ∑ t : T, ∑ y : Y, |f (act t.1 y) - f y| := by
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro y _
      exact abs_sub_comm _ _

/-- Squared generator-graph energy is the sum of the squared Hilbert
displacements of the individual permutation operators. -/
theorem edgeSquareVariation_generatorGraph_eq_sum_norm_sq
    (Y : FiniteModel) (T : Finset G) (act : G → Equiv.Perm Y)
    (f : EuclideanSpace ℝ Y) :
    KunThreshold.edgeSquareVariation (generatorGraph Y T act) f =
      ∑ t ∈ T, ‖permutationOperator (act t) f - f‖ ^ 2 := by
  classical
  let arcs : Finset (T × Y) :=
    Finset.univ.filter fun p ↦ act p.1.1 p.2 ≠ p.2
  unfold KunThreshold.edgeSquareVariation
  dsimp only [generatorGraph]
  change (∑ a : ↑(Finset.univ.filter fun p : T × Y ↦
      act p.1.1 p.2 ≠ p.2),
        (f a.1.2 - f (act a.1.1.1 a.1.2)) ^ 2) = _
  calc
    (∑ a : ↑(Finset.univ.filter fun p : T × Y ↦
        act p.1.1 p.2 ≠ p.2),
          (f a.1.2 - f (act a.1.1.1 a.1.2)) ^ 2) =
        arcs.sum fun p ↦ (f p.2 - f (act p.1.1 p.2)) ^ 2 := by
      simpa [arcs] using Finset.sum_attach arcs
        (fun p : T × Y ↦ (f p.2 - f (act p.1.1 p.2)) ^ 2)
    _ = ∑ p : T × Y, (f p.2 - f (act p.1.1 p.2)) ^ 2 := by
      apply Finset.sum_subset (Finset.subset_univ arcs)
      intro p _ hp
      have hfix : act p.1.1 p.2 = p.2 := by
        by_contra hmove
        exact hp (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmove⟩)
      simp [hfix]
    _ = ∑ t : T, ∑ y : Y, (f y - f (act t.1 y)) ^ 2 := by
      rw [Fintype.sum_prod_type]
    _ = ∑ t : T, ‖permutationOperator (act t.1) f - f‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro t _
      rw [EuclideanSpace.real_norm_sq_eq]
      let h : Y → ℝ := fun z ↦ (f z - f ((act t.1).symm z)) ^ 2
      have hreindex := Equiv.sum_comp (act t.1) h
      change (∑ y : Y, (f y - f (act t.1 y)) ^ 2) =
        ∑ y : Y, (f ((act t.1).symm y) - f y) ^ 2
      calc
        (∑ y : Y, (f y - f (act t.1 y)) ^ 2) =
            ∑ y : Y, (f (act t.1 y) - f y) ^ 2 := by
          apply Finset.sum_congr rfl
          intro y _
          ring
        _ = ∑ y : Y, (f y - f ((act t.1).symm y)) ^ 2 := by
          simpa [h] using hreindex
        _ = ∑ y : Y, (f ((act t.1).symm y) - f y) ^ 2 := by
          apply Finset.sum_congr rfl
          intro y _
          ring
    _ = ∑ t ∈ T, ‖permutationOperator (act t) f - f‖ ^ 2 := by
      simpa using Finset.sum_attach T
        (fun t ↦ ‖permutationOperator (act t) f - f‖ ^ 2)

omit [Group G] in
/-- The sum of squared permutation displacements is the Dirichlet form of
their average.  No symmetry or homomorphism law is required. -/
theorem sum_norm_permutationOperator_sub_sq_eq_average
    (Y : FiniteModel) (T : Finset G) (hT : T.Nonempty)
    (act : G → Equiv.Perm Y) (f : EuclideanSpace ℝ Y) :
    ∑ t ∈ T, ‖permutationOperator (act t) f - f‖ ^ 2 =
      2 * (T.card : ℝ) *
        inner ℝ (f - finiteModelAverage Y act T f) f := by
  have hcard : (T.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hT
  have hone (t : G) (ht : t ∈ T) :
      ‖permutationOperator (act t) f - f‖ ^ 2 =
        2 * inner ℝ f f -
          2 * inner ℝ (permutationOperator (act t) f) f := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right,
      (permutationOperator (act t)).inner_map_map]
    rw [real_inner_comm f (permutationOperator (act t) f)]
    ring
  calc
    ∑ t ∈ T, ‖permutationOperator (act t) f - f‖ ^ 2 =
        ∑ t ∈ T, (2 * inner ℝ f f -
          2 * inner ℝ (permutationOperator (act t) f) f) := by
      apply Finset.sum_congr rfl
      intro t ht
      exact hone t ht
    _ = 2 * (T.card : ℝ) *
        inner ℝ (f - finiteModelAverage Y act T f) f := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul]
      simp [finiteModelAverage, inner_sub_left, real_inner_smul_left,
        sum_inner]
      field_simp
      rw [mul_sub, Finset.mul_sum]
      ring

/-- Generator energy is bounded by the norm of one Markov displacement. -/
theorem edgeSquareVariation_generatorGraph_le_average_displacement
    (Y : FiniteModel) (T : Finset G) (hT : T.Nonempty)
    (act : G → Equiv.Perm Y) (f : EuclideanSpace ℝ Y) :
    KunThreshold.edgeSquareVariation (generatorGraph Y T act) f ≤
      2 * (T.card : ℝ) * ‖f‖ * ‖finiteModelAverage Y act T f - f‖ := by
  rw [edgeSquareVariation_generatorGraph_eq_sum_norm_sq,
    sum_norm_permutationOperator_sub_sq_eq_average Y T hT act f]
  have hinner := abs_real_inner_le_norm
    (f - finiteModelAverage Y act T f) f
  have hle : inner ℝ (f - finiteModelAverage Y act T f) f ≤
      ‖f - finiteModelAverage Y act T f‖ * ‖f‖ :=
    le_trans (le_abs_self _) hinner
  have hcard : 0 ≤ (T.card : ℝ) := by positivity
  calc
    2 * (T.card : ℝ) *
        inner ℝ (f - finiteModelAverage Y act T f) f ≤
      2 * (T.card : ℝ) *
        (‖f - finiteModelAverage Y act T f‖ * ‖f‖) := by gcongr
    _ = 2 * (T.card : ℝ) * ‖f‖ *
        ‖finiteModelAverage Y act T f - f‖ := by
      rw [norm_sub_rev]
      ring

/-- At most two label occurrences per generator can be charged to each
vertex above a threshold: once as a source and once as a target. -/
theorem activeEdges_generatorGraph_card_le
    (Y : FiniteModel) (T : Finset G) (act : G → Equiv.Perm Y)
    (f : Y → ℝ) (a : ℝ) :
    (KunThreshold.activeEdges (generatorGraph Y T act) f a).card ≤
      2 * T.card * ((generatorGraph Y T act).superlevel f a).card := by
  classical
  let A := (generatorGraph Y T act).superlevel f a
  let L : Finset (generatorGraph Y T act).edge :=
    Finset.univ.filter fun e ↦ a < f ((generatorGraph Y T act).first e)
  let R : Finset (generatorGraph Y T act).edge :=
    Finset.univ.filter fun e ↦ a < f ((generatorGraph Y T act).second e)
  have hactive :
      KunThreshold.activeEdges (generatorGraph Y T act) f a = L ∪ R := by
    ext e
    simp [KunThreshold.activeEdges, L, R]
  have hL : L.card ≤ T.card * A.card := by
    let φ : L → T × A := fun e ↦
      (e.1.1.1, ⟨e.1.1.2, by
        simpa [L, A, FiniteMultiGraph.superlevel] using
          (Finset.mem_filter.mp e.2).2⟩)
    have hφ : Function.Injective φ := by
      intro e e' he
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun p : T × A ↦ (p.1, (p.2 : Y))) he
    simpa [Fintype.card_coe] using Fintype.card_le_of_injective φ hφ
  have hR : R.card ≤ T.card * A.card := by
    let φ : R → T × A := fun e ↦
      (e.1.1.1, ⟨act e.1.1.1.1 e.1.1.2, by
        simpa [R, A, FiniteMultiGraph.superlevel] using
          (Finset.mem_filter.mp e.2).2⟩)
    have hφ : Function.Injective φ := by
      intro e e' he
      apply Subtype.ext
      apply Subtype.ext
      have ht : (e.1.1.1.1 : G) = e'.1.1.1.1 :=
        congrArg (fun p : T × A ↦ (p.1 : G)) he
      have hy : act e.1.1.1.1 e.1.1.2 = act e'.1.1.1.1 e'.1.1.2 :=
        congrArg (fun p : T × A ↦ (p.2 : Y)) he
      apply Prod.ext (Subtype.ext ht)
      have hy' : act e.1.1.1.1 e.1.1.2 = act e.1.1.1.1 e'.1.1.2 := by
        simpa [ht] using hy
      exact (act e.1.1.1.1).injective hy'
    simpa [Fintype.card_coe] using Fintype.card_le_of_injective φ hφ
  rw [hactive]
  calc
    (L ∪ R).card ≤ L.card + R.card := Finset.card_union_le L R
    _ ≤ 2 * (T.card * A.card) := by omega
    _ = 2 * T.card *
        ((generatorGraph Y T act).superlevel f a).card := by
      simp [A, Nat.mul_assoc]

/-- The active-edge count weighted by a positive threshold is controlled by
the total mass of a nonnegative function. -/
theorem threshold_mul_activeEdges_generatorGraph_card_le_mass
    (Y : FiniteModel) (T : Finset G) (act : G → Equiv.Perm Y)
    (f : Y → ℝ) (a : ℝ) (ha : 0 ≤ a) (hf : ∀ y, 0 ≤ f y) :
    a * (KunThreshold.activeEdges (generatorGraph Y T act) f a).card ≤
      2 * (T.card : ℝ) * ∑ y, f y := by
  have hactive := activeEdges_generatorGraph_card_le Y T act f a
  have hactiveReal :
      ((KunThreshold.activeEdges (generatorGraph Y T act) f a).card : ℝ) ≤
        2 * (T.card : ℝ) *
          ((generatorGraph Y T act).superlevel f a).card := by
    exact_mod_cast hactive
  have hmass :
      a * (((generatorGraph Y T act).superlevel f a).card : ℝ) ≤
        ∑ y, f y := by
    simpa [FiniteMultiGraph.superlevel] using
      threshold_mul_card_le_sum f hf ha
  calc
    a * (KunThreshold.activeEdges (generatorGraph Y T act) f a).card ≤
        a * (2 * (T.card : ℝ) *
          ((generatorGraph Y T act).superlevel f a).card) :=
      mul_le_mul_of_nonneg_left hactiveReal ha
    _ = 2 * (T.card : ℝ) *
        (a * ((generatorGraph Y T act).superlevel f a).card) := by ring
    _ ≤ 2 * (T.card : ℝ) * ∑ y, f y := by gcongr

/-- Kun's squared coarea bound specialized to an occurrence generator graph,
with the active-edge factor eliminated using finite mass. -/
theorem exists_generatorGraph_boundary_sq_mass_bound
    (Y : FiniteModel) (T : Finset G) (act : G → Equiv.Perm Y)
    (f : Y → ℝ) (a b : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (hf : ∀ y, 0 ≤ f y) :
    ∃ t : ℝ, a < t ∧ t < b ∧
      a * (b - a) ^ 2 *
          ((generatorGraph Y T act).boundaryCard
            ((generatorGraph Y T act).superlevel f t) : ℝ) ^ 2 ≤
        2 * (T.card : ℝ) * (∑ y, f y) *
          KunThreshold.edgeSquareVariation (generatorGraph Y T act) f := by
  obtain ⟨t, hat, htb, ht⟩ :=
    KunThreshold.exists_boundary_sq_mul_sub_sq_le
      (generatorGraph Y T act) f a b hab
  have henergy : 0 ≤
      KunThreshold.edgeSquareVariation (generatorGraph Y T act) f :=
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hmass := threshold_mul_activeEdges_generatorGraph_card_le_mass
    Y T act f a ha hf
  refine ⟨t, hat, htb, ?_⟩
  calc
    a * (b - a) ^ 2 *
        ((generatorGraph Y T act).boundaryCard
          ((generatorGraph Y T act).superlevel f t) : ℝ) ^ 2 =
      a * ((b - a) ^ 2 *
        ((generatorGraph Y T act).boundaryCard
          ((generatorGraph Y T act).superlevel f t) : ℝ) ^ 2) := by ring
    _ ≤ a *
        ((KunThreshold.activeEdges (generatorGraph Y T act) f a).card *
          KunThreshold.edgeSquareVariation (generatorGraph Y T act) f) := by
      gcongr
    _ = (a *
        (KunThreshold.activeEdges (generatorGraph Y T act) f a).card) *
          KunThreshold.edgeSquareVariation (generatorGraph Y T act) f := by ring
    _ ≤ (2 * (T.card : ℝ) * ∑ y, f y) *
        KunThreshold.edgeSquareVariation (generatorGraph Y T act) f :=
      mul_le_mul_of_nonneg_right hmass henergy
    _ = 2 * (T.card : ℝ) * (∑ y, f y) *
        KunThreshold.edgeSquareVariation (generatorGraph Y T act) f := by ring

/-- Finite Kun rounding in the form used for a Markov-smoothed indicator. -/
theorem exists_generatorGraph_boundary_sq_le_markov
    (Y : FiniteModel) (T : Finset G) (hT : T.Nonempty)
    (act : G → Equiv.Perm Y) (f : EuclideanSpace ℝ Y)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (hf : ∀ y, 0 ≤ f y) :
    ∃ t : ℝ, a < t ∧ t < b ∧
      a * (b - a) ^ 2 *
          ((generatorGraph Y T act).boundaryCard
            ((generatorGraph Y T act).superlevel f t) : ℝ) ^ 2 ≤
        4 * (T.card : ℝ) ^ 2 * (∑ y, f y) * ‖f‖ *
          ‖finiteModelAverage Y act T f - f‖ := by
  obtain ⟨t, hat, htb, ht⟩ :=
    exists_generatorGraph_boundary_sq_mass_bound
      Y T act f a b ha hab hf
  have henergy := edgeSquareVariation_generatorGraph_le_average_displacement
    Y T hT act f
  have hmass : 0 ≤ ∑ y, f y := Finset.sum_nonneg fun y _ ↦ hf y
  refine ⟨t, hat, htb, ht.trans ?_⟩
  calc
    2 * (T.card : ℝ) * (∑ y, f y) *
        KunThreshold.edgeSquareVariation (generatorGraph Y T act) f ≤
      2 * (T.card : ℝ) * (∑ y, f y) *
        (2 * (T.card : ℝ) * ‖f‖ *
          ‖finiteModelAverage Y act T f - f‖) := by
      gcongr
    _ = 4 * (T.card : ℝ) ^ 2 * (∑ y, f y) * ‖f‖ *
        ‖finiteModelAverage Y act T f - f‖ := by ring

end KunGeneratorGraph
end NonsoficGroupsExist
