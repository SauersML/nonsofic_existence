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
      (hyperreal_sub_finite hy hx)
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
    Ultrafilter.compl_mem_iff_not_mem.mpr hnot
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

end Ultralimit
end NonsoficGroupsExist
