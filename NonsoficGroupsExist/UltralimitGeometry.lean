import NonsoficGroupsExist.KazhdanFiniteModel

/-!
# Hyperreal geometry of bounded vector sequences

Shalom's finite-presentability argument runs a circumcenter estimate on
an ultralimit of pointed Hilbert spaces.  This module provides that
limit without constructing a Banach ultraproduct: a bounded sequence of
vectors `v : ∀ k, H k` receives the hyperreal seminorm
`seqNorm v := stdPart (ofSeq ‖v ·‖)`, and the parallelogram law,
triangle inequality, and the transfer principle
(`seqNorm v < r` forces `‖v k‖ < r` on a hyperfilter-large set) all
follow from the scalar `ArchimedeanClass.stdPart` calculus already used
by the sofic correlation limits.
-/

namespace NonsoficGroupsExist
namespace Ultralimit

set_option linter.unusedSectionVars false

open KazhdanFiniteModel

/-- Germ addition on hyperreal sequences. -/
theorem ofSeq_add (s t : ℕ → ℝ) :
    Hyperreal.ofSeq (fun k ↦ s k + t k) =
      Hyperreal.ofSeq s + Hyperreal.ofSeq t := by
  have h := map_add ofSeqRingHom s t
  rw [ofSeqRingHom_apply, ofSeqRingHom_apply, ofSeqRingHom_apply] at h
  exact h

/-- Germ multiplication on hyperreal sequences. -/
theorem ofSeq_mul (s t : ℕ → ℝ) :
    Hyperreal.ofSeq (fun k ↦ s k * t k) =
      Hyperreal.ofSeq s * Hyperreal.ofSeq t := by
  have h := map_mul ofSeqRingHom s t
  rw [ofSeqRingHom_apply, ofSeqRingHom_apply, ofSeqRingHom_apply] at h
  exact h

variable {H : ℕ → Type*} [∀ k, NormedAddCommGroup (H k)]
  [∀ k, InnerProductSpace ℝ (H k)]

/-- A sequence of vectors with uniformly bounded norms. -/
def IsBoundedSeq (v : ∀ k, H k) : Prop :=
  ∃ C : ℝ, ∀ k, ‖v k‖ ≤ C

theorem IsBoundedSeq.add {v w : ∀ k, H k} (hv : IsBoundedSeq v)
    (hw : IsBoundedSeq w) : IsBoundedSeq (fun k ↦ v k + w k) := by
  obtain ⟨C, hC⟩ := hv
  obtain ⟨D, hD⟩ := hw
  exact ⟨C + D, fun k ↦ (norm_add_le _ _).trans (add_le_add (hC k) (hD k))⟩

theorem IsBoundedSeq.neg {v : ∀ k, H k} (hv : IsBoundedSeq v) :
    IsBoundedSeq (fun k ↦ -v k) := by
  obtain ⟨C, hC⟩ := hv
  exact ⟨C, fun k ↦ by rw [norm_neg]; exact hC k⟩

theorem IsBoundedSeq.sub {v w : ∀ k, H k} (hv : IsBoundedSeq v)
    (hw : IsBoundedSeq w) : IsBoundedSeq (fun k ↦ v k - w k) := by
  obtain ⟨C, hC⟩ := hv
  obtain ⟨D, hD⟩ := hw
  exact ⟨C + D, fun k ↦ (norm_sub_le _ _).trans (add_le_add (hC k) (hD k))⟩

theorem IsBoundedSeq.smul {v : ∀ k, H k} (hv : IsBoundedSeq v) (c : ℝ) :
    IsBoundedSeq (fun k ↦ c • v k) := by
  obtain ⟨C, hC⟩ := hv
  refine ⟨|c| * C, fun k ↦ ?_⟩
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hC k) (abs_nonneg c)

theorem isBoundedSeq_zero : IsBoundedSeq (fun k ↦ (0 : H k)) :=
  ⟨0, fun k ↦ by simp⟩

/-- A real sequence trapped between two constants gives a finite
hyperreal. -/
theorem ofSeq_finite_of_bounds {s : ℕ → ℝ} {a b : ℝ}
    (h1 : ∀ k, a ≤ s k) (h2 : ∀ k, s k ≤ b) :
    0 ≤ ArchimedeanClass.mk (Hyperreal.ofSeq s) := by
  apply ArchimedeanClass.mk_nonneg_of_le_of_le_of_archimedean
    Hyperreal.coeRingHom (r := a) (s := b)
  · change Hyperreal.ofSeq (fun _ : ℕ ↦ a) ≤ Hyperreal.ofSeq s
    rw [Hyperreal.ofSeq_le_ofSeq]
    exact Filter.Eventually.of_forall h1
  · change Hyperreal.ofSeq s ≤ Hyperreal.ofSeq (fun _ : ℕ ↦ b)
    rw [Hyperreal.ofSeq_le_ofSeq]
    exact Filter.Eventually.of_forall h2

/-- Monotonicity of standard parts of finite hyperreals. -/
theorem stdPart_mono {x y : Hyperreal}
    (hx : 0 ≤ ArchimedeanClass.mk x) (hy : 0 ≤ ArchimedeanClass.mk y)
    (hxy : x ≤ y) :
    ArchimedeanClass.stdPart x ≤ ArchimedeanClass.stdPart y := by
  have hsub := ArchimedeanClass.stdPart_sub hy hx
  have hnn : (0 : ℝ) ≤ ArchimedeanClass.stdPart (y - x) := by
    apply ArchimedeanClass.le_stdPart_of_le Hyperreal.coeRingHom
      (by
        rw [sub_eq_add_neg]
        refine hyperreal_add_finite hy ?_
        rw [ArchimedeanClass.mk_neg]
        exact hx)
    rw [map_zero]
    exact sub_nonneg.mpr hxy
  rw [hsub] at hnn
  linarith

/-- Standard parts of real constants. -/
theorem stdPart_coe (r : ℝ) :
    ArchimedeanClass.stdPart ((r : Hyperreal)) = r := by
  have h1 : r ≤ ArchimedeanClass.stdPart ((r : Hyperreal)) := by
    apply ArchimedeanClass.le_stdPart_of_le Hyperreal.coeRingHom
      (hyperreal_coe_finite r)
    exact le_rfl
  have h2 : ArchimedeanClass.stdPart ((r : Hyperreal)) ≤ r := by
    apply ArchimedeanClass.stdPart_le_of_le Hyperreal.coeRingHom
      (hyperreal_coe_finite r)
    exact le_rfl
  linarith

/-- The hyperreal seminorm of a sequence of vectors: the standard part
of the germ of norms. -/
noncomputable def seqNorm (v : ∀ k, H k) : ℝ :=
  ArchimedeanClass.stdPart (Hyperreal.ofSeq fun k ↦ ‖v k‖)

/-- The squared hyperreal seminorm, as the standard part of the germ of
squared norms. -/
noncomputable def seqNormSq (v : ∀ k, H k) : ℝ :=
  ArchimedeanClass.stdPart (Hyperreal.ofSeq fun k ↦ ‖v k‖ ^ 2)

theorem ofSeq_norm_finite {v : ∀ k, H k} (hv : IsBoundedSeq v) :
    0 ≤ ArchimedeanClass.mk (Hyperreal.ofSeq fun k ↦ ‖v k‖) := by
  obtain ⟨C, hC⟩ := hv
  exact ofSeq_finite_of_bounds (fun k ↦ norm_nonneg _) hC

theorem ofSeq_norm_sq_finite {v : ∀ k, H k} (hv : IsBoundedSeq v) :
    0 ≤ ArchimedeanClass.mk (Hyperreal.ofSeq fun k ↦ ‖v k‖ ^ 2) := by
  obtain ⟨C, hC⟩ := hv
  refine ofSeq_finite_of_bounds (fun k ↦ sq_nonneg _) (b := C ^ 2)
    fun k ↦ ?_
  have h0 : 0 ≤ ‖v k‖ := norm_nonneg (v k)
  nlinarith [hC k]

theorem seqNorm_nonneg {v : ∀ k, H k} (hv : IsBoundedSeq v) :
    0 ≤ seqNorm v := by
  apply ArchimedeanClass.le_stdPart_of_le Hyperreal.coeRingHom
    (ofSeq_norm_finite hv)
  rw [map_zero]
  change Hyperreal.ofSeq (fun _ : ℕ ↦ (0 : ℝ)) ≤ _
  rw [Hyperreal.ofSeq_le_ofSeq]
  exact Filter.Eventually.of_forall fun k ↦ norm_nonneg _

/-- The squared seminorm is the square of the seminorm. -/
theorem seqNormSq_eq_sq {v : ∀ k, H k} (hv : IsBoundedSeq v) :
    seqNormSq v = seqNorm v ^ 2 := by
  have hmul : (Hyperreal.ofSeq fun k ↦ ‖v k‖ ^ 2) =
      (Hyperreal.ofSeq fun k ↦ ‖v k‖) *
        (Hyperreal.ofSeq fun k ↦ ‖v k‖) := by
    rw [← ofSeq_mul]
    apply congrArg Hyperreal.ofSeq
    funext k
    rw [pow_two]
  rw [seqNormSq, seqNorm, hmul,
    ArchimedeanClass.stdPart_mul (ofSeq_norm_finite hv)
      (ofSeq_norm_finite hv), pow_two]

theorem seqNorm_add_le {v w : ∀ k, H k} (hv : IsBoundedSeq v)
    (hw : IsBoundedSeq w) :
    seqNorm (fun k ↦ v k + w k) ≤ seqNorm v + seqNorm w := by
  have hle : (Hyperreal.ofSeq fun k ↦ ‖v k + w k‖) ≤
      (Hyperreal.ofSeq fun k ↦ ‖v k‖) +
        (Hyperreal.ofSeq fun k ↦ ‖w k‖) := by
    rw [← ofSeq_add, Hyperreal.ofSeq_le_ofSeq]
    exact Filter.Eventually.of_forall fun k ↦ norm_add_le _ _
  have hmono := stdPart_mono (ofSeq_norm_finite (hv.add hw))
    (hyperreal_add_finite (ofSeq_norm_finite hv) (ofSeq_norm_finite hw))
    hle
  rw [ArchimedeanClass.stdPart_add (ofSeq_norm_finite hv)
    (ofSeq_norm_finite hw)] at hmono
  exact hmono

theorem seqNorm_sub_rev (v w : ∀ k, H k) :
    seqNorm (fun k ↦ v k - w k) = seqNorm (fun k ↦ w k - v k) := by
  unfold seqNorm
  congr 1
  apply congrArg Hyperreal.ofSeq
  funext k
  rw [norm_sub_rev]

/-- Pointwise parallelogram law, passed to standard parts. -/
theorem seqNormSq_parallelogram {v w : ∀ k, H k} (hv : IsBoundedSeq v)
    (hw : IsBoundedSeq w) :
    seqNormSq (fun k ↦ v k + w k) + seqNormSq (fun k ↦ v k - w k) =
      2 * seqNormSq v + 2 * seqNormSq w := by
  have hconst : ((2 : ℝ) : Hyperreal) =
      Hyperreal.ofSeq (fun _ : ℕ ↦ (2 : ℝ)) := rfl
  have hpoint : (Hyperreal.ofSeq fun k ↦ ‖v k + w k‖ ^ 2) +
      (Hyperreal.ofSeq fun k ↦ ‖v k - w k‖ ^ 2) =
      ((2 : ℝ) : Hyperreal) * (Hyperreal.ofSeq fun k ↦ ‖v k‖ ^ 2) +
        ((2 : ℝ) : Hyperreal) *
          (Hyperreal.ofSeq fun k ↦ ‖w k‖ ^ 2) := by
    rw [hconst, ← ofSeq_add, ← ofSeq_mul, ← ofSeq_mul, ← ofSeq_add]
    apply congrArg Hyperreal.ofSeq
    funext k
    have hpar := parallelogram_law_with_norm ℝ (v k) (w k)
    nlinarith [hpar]
  have hfin2 : 0 ≤ ArchimedeanClass.mk ((2 : ℝ) : Hyperreal) :=
    hyperreal_coe_finite 2
  have hstep : seqNormSq (fun k ↦ v k + w k) +
      seqNormSq (fun k ↦ v k - w k) =
      ArchimedeanClass.stdPart
        ((Hyperreal.ofSeq fun k ↦ ‖v k + w k‖ ^ 2) +
          (Hyperreal.ofSeq fun k ↦ ‖v k - w k‖ ^ 2)) := by
    rw [ArchimedeanClass.stdPart_add (ofSeq_norm_sq_finite (hv.add hw))
      (ofSeq_norm_sq_finite (hv.sub hw))]
    rfl
  rw [hstep, hpoint,
    ArchimedeanClass.stdPart_add
      (hyperreal_mul_finite hfin2 (ofSeq_norm_sq_finite hv))
      (hyperreal_mul_finite hfin2 (ofSeq_norm_sq_finite hw)),
    ArchimedeanClass.stdPart_mul hfin2 (ofSeq_norm_sq_finite hv),
    ArchimedeanClass.stdPart_mul hfin2 (ofSeq_norm_sq_finite hw),
    stdPart_coe]
  rfl

/-- **Transfer**: a seminorm bound strictly below `r` holds at the level
of the sequences on a hyperfilter-large set of indices. -/
theorem eventually_norm_lt_of_seqNorm_lt {v : ∀ k, H k}
    (hv : IsBoundedSeq v) {r : ℝ} (h : seqNorm v < r) :
    ∀ᶠ k in ↑(Filter.hyperfilter ℕ), ‖v k‖ < r := by
  by_contra hcon
  have hnot : {k : ℕ | ‖v k‖ < r} ∉ Filter.hyperfilter ℕ := hcon
  have hmem : {k : ℕ | ‖v k‖ < r}ᶜ ∈ Filter.hyperfilter ℕ :=
    Ultrafilter.compl_mem_iff_notMem.mpr hnot
  have hmem' : {k : ℕ | r ≤ ‖v k‖} ∈ Filter.hyperfilter ℕ := by
    have hset : {k : ℕ | ‖v k‖ < r}ᶜ = {k : ℕ | r ≤ ‖v k‖} := by
      ext k
      simp [not_lt]
    rwa [hset] at hmem
  have hge : ((r : Hyperreal)) ≤ Hyperreal.ofSeq fun k ↦ ‖v k‖ := by
    change Hyperreal.ofSeq (fun _ : ℕ ↦ r) ≤ _
    rw [Hyperreal.ofSeq_le_ofSeq]
    exact hmem'
  have hstd := stdPart_mono (hyperreal_coe_finite r)
    (ofSeq_norm_finite hv) hge
  rw [stdPart_coe] at hstd
  exact absurd (lt_of_le_of_lt hstd h) (lt_irrefl r)

/-- Cofinite index sets are hyperfilter-large. -/
theorem eventually_le_id (C : ℕ) :
    ∀ᶠ k in ↑(Filter.hyperfilter ℕ), C ≤ k := by
  apply Filter.mem_hyperfilter_of_finite_compl
  have hsub : {k : ℕ | C ≤ k}ᶜ ⊆ Set.Iio C := by
    intro k hk
    simpa [Set.mem_Iio, not_le] using hk
  exact (Set.finite_Iio C).subset hsub

/-- A standard-part bound strictly below `r` holds eventually along the
hyperfilter, by the ultrafilter dichotomy. -/
theorem eventually_lt_of_stdPart_lt {s : ℕ → ℝ}
    (hfin : 0 ≤ ArchimedeanClass.mk (Hyperreal.ofSeq s)) {r : ℝ}
    (h : ArchimedeanClass.stdPart (Hyperreal.ofSeq s) < r) :
    ∀ᶠ k in ↑(Filter.hyperfilter ℕ), s k < r := by
  by_contra hcon
  have hnot : {k : ℕ | s k < r} ∉ Filter.hyperfilter ℕ := hcon
  have hmem : {k : ℕ | s k < r}ᶜ ∈ Filter.hyperfilter ℕ :=
    Ultrafilter.compl_mem_iff_notMem.mpr hnot
  have hmem' : {k : ℕ | r ≤ s k} ∈ Filter.hyperfilter ℕ := by
    have hset : {k : ℕ | s k < r}ᶜ = {k : ℕ | r ≤ s k} := by
      ext k
      simp [not_lt]
    rwa [hset] at hmem
  have hge : ((r : Hyperreal)) ≤ Hyperreal.ofSeq s := by
    change Hyperreal.ofSeq (fun _ : ℕ ↦ r) ≤ _
    rw [Hyperreal.ofSeq_le_ofSeq]
    exact hmem'
  have hle := ArchimedeanClass.le_stdPart_of_le Hyperreal.coeRingHom
    hfin hge
  linarith

/-- The mirror transfer: a standard part strictly above `r` forces the
sequence above `r` eventually along the hyperfilter. -/
theorem eventually_lt_stdPart_of_lt {s : ℕ → ℝ}
    (hfin : 0 ≤ ArchimedeanClass.mk (Hyperreal.ofSeq s)) {r : ℝ}
    (h : r < ArchimedeanClass.stdPart (Hyperreal.ofSeq s)) :
    ∀ᶠ k in ↑(Filter.hyperfilter ℕ), r < s k := by
  by_contra hcon
  have hnot : {k : ℕ | r < s k} ∉ Filter.hyperfilter ℕ := hcon
  have hmem : {k : ℕ | r < s k}ᶜ ∈ Filter.hyperfilter ℕ :=
    Ultrafilter.compl_mem_iff_notMem.mpr hnot
  have hmem' : {k : ℕ | s k ≤ r} ∈ Filter.hyperfilter ℕ := by
    have hset : {k : ℕ | r < s k}ᶜ = {k : ℕ | s k ≤ r} := by
      ext k
      simp [not_lt]
    rwa [hset] at hmem
  have hle' : Hyperreal.ofSeq s ≤ ((r : Hyperreal)) := by
    change _ ≤ Hyperreal.ofSeq (fun _ : ℕ ↦ r)
    rw [Hyperreal.ofSeq_le_ofSeq]
    exact hmem'
  have hle := ArchimedeanClass.stdPart_le_of_le Hyperreal.coeRingHom
    hfin hle'
  linarith

/-- **The exponential commutes with standard parts** of bounded
sequences: both bounds follow from eventual monotone comparison, and a
squeeze along `δ = 1/(n+1)` finishes. -/
theorem stdPart_exp {s : ℕ → ℝ} {a b : ℝ}
    (h1 : ∀ k, a ≤ s k) (h2 : ∀ k, s k ≤ b) :
    ArchimedeanClass.stdPart (Hyperreal.ofSeq fun k ↦ Real.exp (s k)) =
      Real.exp (ArchimedeanClass.stdPart (Hyperreal.ofSeq s)) := by
  have hfin := ofSeq_finite_of_bounds h1 h2
  have hfinExp : 0 ≤ ArchimedeanClass.mk
      (Hyperreal.ofSeq fun k ↦ Real.exp (s k)) :=
    ofSeq_finite_of_bounds (fun k ↦ (Real.exp_pos (s k)).le)
      (fun k ↦ Real.exp_le_exp.mpr (h2 k))
  set L := ArchimedeanClass.stdPart (Hyperreal.ofSeq s) with hL
  set X := ArchimedeanClass.stdPart
    (Hyperreal.ofSeq fun k ↦ Real.exp (s k)) with hX
  have hkey : ∀ δ : ℝ, 0 < δ →
      Real.exp (L - δ) ≤ X ∧ X ≤ Real.exp (L + δ) := by
    intro δ hδ
    have hup : ∀ᶠ k in ↑(Filter.hyperfilter ℕ), s k < L + δ :=
      eventually_lt_of_stdPart_lt hfin (by rw [← hL]; linarith)
    have hdown : ∀ᶠ k in ↑(Filter.hyperfilter ℕ), L - δ < s k :=
      eventually_lt_stdPart_of_lt hfin (by rw [← hL]; linarith)
    constructor
    · have hev : ∀ᶠ k in ↑(Filter.hyperfilter ℕ),
          Real.exp (L - δ) ≤ Real.exp (s k) := by
        filter_upwards [hdown] with k hk
        exact Real.exp_le_exp.mpr hk.le
      have hge : ((Real.exp (L - δ) : ℝ) : Hyperreal) ≤
          Hyperreal.ofSeq fun k ↦ Real.exp (s k) := by
        change Hyperreal.ofSeq (fun _ : ℕ ↦ Real.exp (L - δ)) ≤ _
        rw [Hyperreal.ofSeq_le_ofSeq]
        exact hev
      exact ArchimedeanClass.le_stdPart_of_le Hyperreal.coeRingHom
        hfinExp hge
    · have hev : ∀ᶠ k in ↑(Filter.hyperfilter ℕ),
          Real.exp (s k) ≤ Real.exp (L + δ) := by
        filter_upwards [hup] with k hk
        exact Real.exp_le_exp.mpr hk.le
      have hle : Hyperreal.ofSeq (fun k ↦ Real.exp (s k)) ≤
          ((Real.exp (L + δ) : ℝ) : Hyperreal) := by
        change _ ≤ Hyperreal.ofSeq (fun _ : ℕ ↦ Real.exp (L + δ))
        rw [Hyperreal.ofSeq_le_ofSeq]
        exact hev
      exact ArchimedeanClass.stdPart_le_of_le Hyperreal.coeRingHom
        hfinExp hle
  have htend1 : Filter.Tendsto
      (fun n : ℕ ↦ Real.exp (L + 1 / ((n : ℝ) + 1)))
      Filter.atTop (nhds (Real.exp L)) := by
    have h0 : Filter.Tendsto (fun n : ℕ ↦ L + 1 / ((n : ℝ) + 1))
        Filter.atTop (nhds L) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_add L
    exact (Real.continuous_exp.tendsto L).comp h0
  have htend2 : Filter.Tendsto
      (fun n : ℕ ↦ Real.exp (L - 1 / ((n : ℝ) + 1)))
      Filter.atTop (nhds (Real.exp L)) := by
    have h0 : Filter.Tendsto (fun n : ℕ ↦ L - 1 / ((n : ℝ) + 1))
        Filter.atTop (nhds L) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_sub L
    exact (Real.continuous_exp.tendsto L).comp h0
  have hXle : X ≤ Real.exp L := by
    refine ge_of_tendsto' htend1 fun n ↦ ?_
    exact (hkey (1 / ((n : ℝ) + 1)) (by positivity)).2
  have hXge : Real.exp L ≤ X := by
    refine le_of_tendsto' htend2 fun n ↦ ?_
    exact (hkey (1 / ((n : ℝ) + 1)) (by positivity)).1
  linarith

theorem seqNorm_neg (v : ∀ k, H k) :
    seqNorm (fun k ↦ -v k) = seqNorm v := by
  unfold seqNorm
  congr 1
  apply congrArg Hyperreal.ofSeq
  funext k
  rw [norm_neg]

/-- Sequences with pointwise equal norms have the same seminorm; in
particular pointwise isometric images do. -/
theorem seqNorm_congr_norm {H' : ℕ → Type*}
    [∀ k, NormedAddCommGroup (H' k)] [∀ k, InnerProductSpace ℝ (H' k)]
    {u : ∀ k, H k} {u' : ∀ k, H' k} (h : ∀ k, ‖u k‖ = ‖u' k‖) :
    seqNorm u = seqNorm u' := by
  unfold seqNorm
  congr 1
  apply congrArg Hyperreal.ofSeq
  funext k
  exact h k

/-- Scaling of the squared seminorm. -/
theorem seqNormSq_smul {v : ∀ k, H k} (hv : IsBoundedSeq v) (c : ℝ) :
    seqNormSq (fun k ↦ c • v k) = c ^ 2 * seqNormSq v := by
  have hconst : ((c ^ 2 : ℝ) : Hyperreal) =
      Hyperreal.ofSeq (fun _ : ℕ ↦ (c ^ 2 : ℝ)) := rfl
  have hpoint : (Hyperreal.ofSeq fun k ↦ ‖c • v k‖ ^ 2) =
      ((c ^ 2 : ℝ) : Hyperreal) *
        (Hyperreal.ofSeq fun k ↦ ‖v k‖ ^ 2) := by
    rw [hconst, ← ofSeq_mul]
    apply congrArg Hyperreal.ofSeq
    funext k
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [seqNormSq, hpoint,
    ArchimedeanClass.stdPart_mul (hyperreal_coe_finite (c ^ 2))
      (ofSeq_norm_sq_finite hv), stdPart_coe]
  rfl

section Center

variable {ι : Type*} [Nonempty ι]

/-- The covering radius of a sequence over an indexed orbit, in the
hyperreal seminorm. -/
noncomputable def orbitRadius (O : ι → ∀ k, H k) (v : ∀ k, H k) : ℝ :=
  sSup (Set.range fun i ↦ seqNorm (fun k ↦ v k - O i k))

/-- The optimal covering radius over all bounded sequences. -/
noncomputable def centerRadius (O : ι → ∀ k, H k) : ℝ :=
  sInf (orbitRadius O '' {v | IsBoundedSeq v})

variable {O : ι → ∀ k, H k} {D : ℝ}

set_option maxHeartbeats 1000000 in
theorem bddAbove_orbit_seqNorm (hOb : ∀ i, IsBoundedSeq (O i))
    (hOD : ∀ i, seqNorm (O i) ≤ D) {v : ∀ k, H k}
    (hv : IsBoundedSeq v) :
    BddAbove (Set.range fun i ↦ seqNorm (fun k ↦ v k - O i k)) := by
  refine ⟨seqNorm v + D, ?_⟩
  rintro r ⟨i, rfl⟩
  have htri : seqNorm (fun k ↦ v k - O i k) ≤
      seqNorm v + seqNorm (fun k ↦ -O i k) := by
    exact seqNorm_add_le hv (hOb i).neg
  rw [seqNorm_neg] at htri
  exact htri.trans (add_le_add_left (hOD i) _)

theorem le_orbitRadius (hOb : ∀ i, IsBoundedSeq (O i))
    (hOD : ∀ i, seqNorm (O i) ≤ D) {v : ∀ k, H k}
    (hv : IsBoundedSeq v) (i : ι) :
    seqNorm (fun k ↦ v k - O i k) ≤ orbitRadius O v :=
  le_csSup (bddAbove_orbit_seqNorm hOb hOD hv) (Set.mem_range_self i)

theorem orbitRadius_le {v : ∀ k, H k} {r : ℝ}
    (h : ∀ i, seqNorm (fun k ↦ v k - O i k) ≤ r) :
    orbitRadius O v ≤ r :=
  csSup_le (Set.range_nonempty _) (by rintro s ⟨i, rfl⟩; exact h i)

theorem orbitRadius_nonneg (hOb : ∀ i, IsBoundedSeq (O i))
    (hOD : ∀ i, seqNorm (O i) ≤ D) {v : ∀ k, H k}
    (hv : IsBoundedSeq v) :
    0 ≤ orbitRadius O v := by
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  exact (seqNorm_nonneg (hv.sub (hOb i))).trans
    (le_orbitRadius hOb hOD hv i)

theorem bddBelow_radius_image (hOb : ∀ i, IsBoundedSeq (O i))
    (hOD : ∀ i, seqNorm (O i) ≤ D) :
    BddBelow (orbitRadius O '' {v | IsBoundedSeq v}) := by
  refine ⟨0, ?_⟩
  rintro r ⟨v, hv, rfl⟩
  exact orbitRadius_nonneg hOb hOD hv

theorem centerRadius_le (hOb : ∀ i, IsBoundedSeq (O i))
    (hOD : ∀ i, seqNorm (O i) ≤ D) {v : ∀ k, H k}
    (hv : IsBoundedSeq v) :
    centerRadius O ≤ orbitRadius O v :=
  csInf_le (bddBelow_radius_image hOb hOD) ⟨v, hv, rfl⟩

/-- Near-optimal centers exist. -/
theorem exists_near_center (hOb : ∀ i, IsBoundedSeq (O i))
    (hOD : ∀ i, seqNorm (O i) ≤ D) {δ : ℝ} (hδ : 0 < δ) :
    ∃ v : ∀ k, H k, IsBoundedSeq v ∧
      orbitRadius O v < centerRadius O + δ := by
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  have hne : (orbitRadius O '' {v | IsBoundedSeq v}).Nonempty :=
    ⟨orbitRadius O (O i), O i, hOb i, rfl⟩
  have hlt : centerRadius O < centerRadius O + δ := by linarith
  obtain ⟨r, ⟨v, hv, rfl⟩, hrlt⟩ :=
    (csInf_lt_iff (bddBelow_radius_image hOb hOD) hne).mp hlt
  exact ⟨v, hv, hrlt⟩

/-- **The approximate-circumcenter estimate**: any two near-optimal
centers are close, quantitatively, by the parallelogram law applied
against every orbit point. -/
theorem seqNormSq_sub_le_of_near_center
    (hOb : ∀ i, IsBoundedSeq (O i)) (hOD : ∀ i, seqNorm (O i) ≤ D)
    {v w : ∀ k, H k} (hv : IsBoundedSeq v) (hw : IsBoundedSeq w)
    {ρ : ℝ} (hrv : orbitRadius O v ≤ ρ) (hrw : orbitRadius O w ≤ ρ) :
    seqNormSq (fun k ↦ v k - w k) ≤
      4 * (ρ ^ 2 - centerRadius O ^ 2) := by
  classical
  set mid : ∀ k, H k := fun k ↦ (2⁻¹ : ℝ) • (v k + w k) with hmid
  have hmidb : IsBoundedSeq mid := (hv.add hw).smul 2⁻¹
  set q : ℝ := seqNormSq (fun k ↦ v k - w k) with hq
  -- Parallelogram against each orbit point.
  have hkey : ∀ i : ι, 4 * seqNormSq (fun k ↦ mid k - O i k) + q ≤
      4 * ρ ^ 2 := by
    intro i
    have hpar := seqNormSq_parallelogram (v := fun k ↦ v k - O i k)
      (w := fun k ↦ w k - O i k) (hv.sub (hOb i)) (hw.sub (hOb i))
    have hsub : (fun k ↦ (v k - O i k) - (w k - O i k)) =
        fun k ↦ v k - w k := by
      funext k
      abel
    have hsum : (fun k ↦ (v k - O i k) + (w k - O i k)) =
        fun k ↦ (2 : ℝ) • (mid k - O i k) := by
      funext k
      show (v k - O i k) + (w k - O i k) =
        (2 : ℝ) • ((2⁻¹ : ℝ) • (v k + w k) - O i k)
      rw [smul_sub, smul_smul, show (2 : ℝ) * 2⁻¹ = 1 by norm_num,
        one_smul, two_smul]
      abel
    rw [hsub, hsum, seqNormSq_smul (hmidb.sub (hOb i)) 2, ← hq] at hpar
    have hva : seqNormSq (fun k ↦ v k - O i k) ≤ ρ ^ 2 := by
      rw [seqNormSq_eq_sq (hv.sub (hOb i))]
      have h1 := (le_orbitRadius hOb hOD hv i).trans hrv
      have h0 := seqNorm_nonneg (hv.sub (hOb i))
      nlinarith
    have hwa : seqNormSq (fun k ↦ w k - O i k) ≤ ρ ^ 2 := by
      rw [seqNormSq_eq_sq (hw.sub (hOb i))]
      have h1 := (le_orbitRadius hOb hOD hw i).trans hrw
      have h0 := seqNorm_nonneg (hw.sub (hOb i))
      nlinarith
    nlinarith [hpar, hva, hwa]
  -- The midpoint radius squeezes the optimal radius.
  have hB0 : 0 ≤ ρ ^ 2 - q / 4 := by
    obtain ⟨i⟩ := (inferInstance : Nonempty ι)
    have := hkey i
    have h0 : 0 ≤ seqNormSq (fun k ↦ mid k - O i k) := by
      rw [seqNormSq_eq_sq (hmidb.sub (hOb i))]
      exact sq_nonneg _
    nlinarith
  have hmidr : orbitRadius O mid ≤ Real.sqrt (ρ ^ 2 - q / 4) := by
    apply orbitRadius_le
    intro i
    have h1 := hkey i
    have h2 : seqNormSq (fun k ↦ mid k - O i k) ≤ ρ ^ 2 - q / 4 := by
      nlinarith
    rw [seqNormSq_eq_sq (hmidb.sub (hOb i))] at h2
    have h3 : Real.sqrt (seqNorm (fun k ↦ mid k - O i k) ^ 2) ≤
        Real.sqrt (ρ ^ 2 - q / 4) := Real.sqrt_le_sqrt h2
    rwa [Real.sqrt_sq (seqNorm_nonneg (hmidb.sub (hOb i)))] at h3
  have hcle : centerRadius O ≤ Real.sqrt (ρ ^ 2 - q / 4) :=
    (centerRadius_le hOb hOD hmidb).trans hmidr
  have hsq : centerRadius O ^ 2 ≤ ρ ^ 2 - q / 4 := by
    have h0 : 0 ≤ centerRadius O := by
      obtain ⟨i⟩ := (inferInstance : Nonempty ι)
      refine le_csInf ⟨orbitRadius O (O i), O i, hOb i, rfl⟩ ?_
      rintro r ⟨v, hv, rfl⟩
      exact orbitRadius_nonneg hOb hOD hv
    have hs := Real.sq_sqrt hB0
    nlinarith [mul_self_le_mul_self h0 hcle,
      Real.sqrt_nonneg (ρ ^ 2 - q / 4)]
  linarith

end Center

end Ultralimit
end NonsoficGroupsExist
