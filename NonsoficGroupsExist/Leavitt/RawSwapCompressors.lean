import NonsoficGroupsExist.Leavitt.RankFourCompressors

/-!
# The raw swap: compression without the order-two relation

`RankFourCompressors` builds its second compressor from the sign-corrected
involution `z = signCorrection · w`, where

  `w = x₁₄(s₁) · x₄₁(−t₁) · x₁₄(s₁)`

is the three-transvection word `rawInvolutionWord`.  The correction makes
`z² = 1`, and the binary commutator identity `[c, r] = −1` pays for it over
every coefficient ring.  This file proves that the correction is a
convenience, not a need: **the raw word already does everything the
compression argument uses**.

* `w` commutes with every compressed elementary core generator
  (`rawInvolutionWord_commutes_compressed_core`);
* `v = w · u` implements the same compression endomorphism as `u`
  (`rawSecondCompressor_conjugation`);
* conjugation by `w` carries core roots out of and into coordinate zero to
  last-row and last-column roots, up to a sign
  (`rawInvolutionWord_mul_lastRow`, `rawInvolutionWord_mul_lastColumn`),
  so the embedded core together with `{u, w·u}` generates all of `EL₄`
  (`coreEmbedding_rawCompressorSet_generate`).

No identity here involves `w⁻¹` on the matrix side: every conjugation
statement is phrased in mul-past form `w · x = y · w`, and inverses appear
only through subgroup closure.  The order of `w` in the group is never
mentioned — it is irrelevant, which is the point.

The compression–centralizer criterion consumes exactly these three
properties, so `rawCompressorSet` is a drop-in replacement for
`compressorSet`, valid over every coefficient ring with no `K₁` class, no
`GE` input, and no involution.
-/

namespace NonsoficGroupsExist
namespace RankFour

open scoped commutatorElement

variable {A : Type*} [Ring A]

/-- The sparse matrix value of the raw three-transvection word: the involution
block with the honest `−t₁` in the last row, no sign correction applied.  The
`(0,0)` entry is `1 − s₁t₁ = p₀`. -/
def rawInvolutionMatrix (L : LeavittFamily A) : Matrix Index Index A :=
  !![L.p0, 0, 0, L.s1;
     0, 1, 0, 0;
     0, 0, 1, 0;
     -L.t1, 0, 0, 0]

@[simp] theorem rawInvolutionWord_val (L : LeavittFamily A) :
    (↑(↑(rawInvolutionWord L) : (Matrix Index Index A)ˣ) :
        Matrix Index Index A) =
      rawInvolutionMatrix L := by
  have hcorner : 1 + -(L.s1 * L.t1) = L.s0 * L.t0 := by
    rw [← L.p0_add_s1t1]
    abel
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [rawInvolutionWord, rawInvolutionMatrix, transvection, elementaryUnit,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ, coreIndex,
      lastIndex, hcorner, LeavittFamily.p0, mul_add, add_mul, mul_assoc]

/-- The raw word commutes with every compressed elementary core generator:
the corner entries `s₀bt₀` are annihilated by `t₁` on the left and by `s₁` on
the right, exactly as for the sign-corrected involution, and the sign of the
last row never enters. -/
theorem rawInvolutionWord_commutes_compressed_coreTransvection
    (L : LeavittFamily A) (i j : Fin 3) (hij : i ≠ j) (a : A) :
    Commute (rawInvolutionWord L)
      (coreEmbedding (compressionEnd L (coreTransvection i j hij a))) := by
  rw [compressionEnd_coreTransvection, coreEmbedding_coreTransvection]
  apply Subtype.ext
  apply Units.ext
  ext r c
  fin_cases i <;> fin_cases j
  all_goals try simp at hij
  all_goals fin_cases r <;> fin_cases c
  all_goals
    simp [transvection, elementaryUnit, rawInvolutionWord_val,
      rawInvolutionMatrix, Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_succ, coreIndex, LeavittFamily.p0,
      mul_add, add_mul, mul_assoc]

/-- The generator calculation extends to the complete compressed core. -/
theorem rawInvolutionWord_commutes_compressed_core
    (L : LeavittFamily A) (g : Core A) :
    Commute (rawInvolutionWord L) (coreEmbedding (compressionEnd L g)) := by
  rcases g with ⟨g, hg⟩
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, j, hij, a, rfl⟩ := hx
      exact rawInvolutionWord_commutes_compressed_coreTransvection L i j hij a
  | one =>
      rw [show (⟨1, _⟩ : Core A) = 1 from Subtype.ext rfl, map_one, map_one]
      exact Commute.one_right _
  | mul x y hxmem hymem hx hy =>
      rw [show (⟨x * y, _⟩ : Core A) = ⟨x, hxmem⟩ * ⟨y, hymem⟩ from
        Subtype.ext rfl, map_mul, map_mul]
      exact hx.mul_right hy
  | inv x hxmem hx =>
      rw [show (⟨x⁻¹, _⟩ : Core A) = (⟨x, hxmem⟩ : Core A)⁻¹ from
        Subtype.ext rfl, map_inv, map_inv]
      exact hx.inv_right

/-- The raw second compressor `v = w · u`: the comb compressor preceded by
the raw swap, with no sign correction. -/
def rawSecondCompressor (L : LeavittFamily A) : Ambient A :=
  rawInvolutionWord L * compressor L

/-- The raw second word implements the same compression endomorphism as the
comb compressor itself. -/
theorem rawSecondCompressor_mul_coreEmbedding
    (L : LeavittFamily A) (g : Core A) :
    rawSecondCompressor L * coreEmbedding g =
      coreEmbedding (compressionEnd L g) * rawSecondCompressor L := by
  calc
    rawSecondCompressor L * coreEmbedding g =
        rawInvolutionWord L * (compressor L * coreEmbedding g) := by
      simp only [rawSecondCompressor, mul_assoc]
    _ = rawInvolutionWord L *
        (coreEmbedding (compressionEnd L g) * compressor L) := by
      rw [compressor_mul_coreEmbedding]
    _ = (coreEmbedding (compressionEnd L g) * rawInvolutionWord L) *
        compressor L := by
      rw [← mul_assoc, (rawInvolutionWord_commutes_compressed_core L g).eq]
    _ = coreEmbedding (compressionEnd L g) * rawSecondCompressor L := by
      simp only [rawSecondCompressor, mul_assoc]

theorem rawSecondCompressor_conjugation
    (L : LeavittFamily A) (g : Core A) :
    rawSecondCompressor L * coreEmbedding g * (rawSecondCompressor L)⁻¹ =
      coreEmbedding (compressionEnd L g) := by
  rw [rawSecondCompressor_mul_coreEmbedding]
  group

/-- Multiplying past the raw word carries a core root out of coordinate zero
to a last-row root, up to sign: `w · x₀ⱼ(s₁a) = x₄ⱼ(−a) · w`.  This is the
mul-past form of the conjugation identity; no inverse of `w` is computed. -/
theorem rawInvolutionWord_mul_lastRow (L : LeavittFamily A)
    (j : Fin 3) (hj : j ≠ 0) (a : A) :
    rawInvolutionWord L *
        coreEmbedding (coreTransvection 0 j hj.symm (L.s1 * a)) =
      transvection lastIndex (coreIndex j) (last_ne_core j) (-a) *
        rawInvolutionWord L := by
  rw [coreEmbedding_coreTransvection]
  apply Subtype.ext
  apply Units.ext
  ext r c
  fin_cases j
  · simp at hj
  · fin_cases r <;> fin_cases c <;>
      simp [transvection, elementaryUnit, rawInvolutionWord_val,
        rawInvolutionMatrix, Matrix.mul_apply, Matrix.one_apply,
        Fin.sum_univ_succ, coreIndex, lastIndex, mul_add, add_mul]
  · fin_cases r <;> fin_cases c <;>
      simp [transvection, elementaryUnit, rawInvolutionWord_val,
        rawInvolutionMatrix, Matrix.mul_apply, Matrix.one_apply,
        Fin.sum_univ_succ, coreIndex, lastIndex, mul_add, add_mul]

/-- Multiplying past the raw word carries a core root into coordinate zero to
a last-column root, up to sign: `w · xᵢ₀(a·t₁) = xᵢ₄(−a) · w`. -/
theorem rawInvolutionWord_mul_lastColumn (L : LeavittFamily A)
    (i : Fin 3) (hi : i ≠ 0) (a : A) :
    rawInvolutionWord L *
        coreEmbedding (coreTransvection i 0 hi (a * L.t1)) =
      transvection (coreIndex i) lastIndex (core_ne_last i) (-a) *
        rawInvolutionWord L := by
  rw [coreEmbedding_coreTransvection]
  apply Subtype.ext
  apply Units.ext
  ext r c
  fin_cases i
  · simp at hi
  · fin_cases r <;> fin_cases c <;>
      simp [transvection, elementaryUnit, rawInvolutionWord_val,
        rawInvolutionMatrix, Matrix.mul_apply, Matrix.one_apply,
        Fin.sum_univ_succ, coreIndex, lastIndex, mul_add, add_mul]
  · fin_cases r <;> fin_cases c <;>
      simp [transvection, elementaryUnit, rawInvolutionWord_val,
        rawInvolutionMatrix, Matrix.mul_apply, Matrix.one_apply,
        Fin.sum_univ_succ, coreIndex, lastIndex, mul_add, add_mul]

/-- The two-word raw compressor set `{u, w·u}`. -/
noncomputable def rawCompressorSet (L : LeavittFamily A) : Finset (Ambient A) := by
  classical
  exact {compressor L, rawSecondCompressor L}

theorem compressor_mem_rawCompressorSet (L : LeavittFamily A) :
    compressor L ∈ rawCompressorSet L := by
  classical
  simp [rawCompressorSet]

theorem rawSecondCompressor_mem_rawCompressorSet (L : LeavittFamily A) :
    rawSecondCompressor L ∈ rawCompressorSet L := by
  classical
  simp [rawCompressorSet]

/-- Every member of the raw two-word set implements the concrete compression
endomorphism. -/
theorem rawCompressorSet_conjugation (L : LeavittFamily A)
    (q : Ambient A) (hq : q ∈ rawCompressorSet L) (g : Core A) :
    coreEmbedding (compressionEnd L g) = q * coreEmbedding g * q⁻¹ := by
  classical
  simp only [rawCompressorSet, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl
  · exact (compressor_conjugation L g).symm
  · exact (rawSecondCompressor_conjugation L g).symm

/-- The embedded core together with the raw two-word set generates the
complete rank-four elementary group.  The signs produced by the raw
conjugation identities are absorbed by instantiating them at `−a`. -/
theorem coreEmbedding_rawCompressorSet_generate (L : LeavittFamily A) :
    Subgroup.closure
      (Set.range (coreEmbedding (A := A)) ∪
        (rawCompressorSet L : Set (Ambient A))) = ⊤ := by
  let H : Subgroup (Ambient A) := Subgroup.closure
    (Set.range (coreEmbedding (A := A)) ∪
      (rawCompressorSet L : Set (Ambient A)))
  have hcore (g : Core A) : coreEmbedding g ∈ H := by
    apply Subgroup.subset_closure
    exact Or.inl ⟨g, rfl⟩
  have hcompressor : compressor L ∈ H := by
    apply Subgroup.subset_closure
    exact Or.inr (compressor_mem_rawCompressorSet L)
  have hsecond : rawSecondCompressor L ∈ H := by
    apply Subgroup.subset_closure
    exact Or.inr (rawSecondCompressor_mem_rawCompressorSet L)
  have hraw : rawInvolutionWord L ∈ H := by
    have : rawSecondCompressor L * (compressor L)⁻¹ ∈ H :=
      H.mul_mem hsecond (H.inv_mem hcompressor)
    simpa [rawSecondCompressor] using this
  have hlastRow (j : Fin 3) (hj : j ≠ 0) (a : A) :
      transvection lastIndex (coreIndex j) (last_ne_core j) a ∈ H := by
    have hpast := rawInvolutionWord_mul_lastRow L j hj (-a)
    rw [neg_neg] at hpast
    have heq : transvection lastIndex (coreIndex j) (last_ne_core j) a =
        rawInvolutionWord L *
          coreEmbedding (coreTransvection 0 j hj.symm (L.s1 * -a)) *
            (rawInvolutionWord L)⁻¹ := by
      rw [hpast]
      group
    rw [heq]
    exact H.mul_mem (H.mul_mem hraw (hcore _)) (H.inv_mem hraw)
  have hlastColumn (i : Fin 3) (hi : i ≠ 0) (a : A) :
      transvection (coreIndex i) lastIndex (core_ne_last i) a ∈ H := by
    have hpast := rawInvolutionWord_mul_lastColumn L i hi (-a)
    rw [neg_neg] at hpast
    have heq : transvection (coreIndex i) lastIndex (core_ne_last i) a =
        rawInvolutionWord L *
          coreEmbedding (coreTransvection i 0 hi (-a * L.t1)) *
            (rawInvolutionWord L)⁻¹ := by
      rw [hpast]
      group
    rw [heq]
    exact H.mul_mem (H.mul_mem hraw (hcore _)) (H.inv_mem hraw)
  have hcommutator {x y z : Ambient A} (hx : x ∈ H) (hy : y ∈ H)
      (heq : ⁅x, y⁆ = z) : z ∈ H := by
    rw [← heq, commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)) (H.inv_mem hy)
  have hlastZero (a : A) :
      transvection lastIndex (coreIndex 0) (last_ne_core 0) a ∈ H := by
    apply hcommutator (x := transvection lastIndex (coreIndex 1) (last_ne_core 1) a)
      (y := coreEmbedding (coreTransvection 1 0 (by decide) 1))
      (hlastRow 1 (by decide) a) (hcore _)
    rw [coreEmbedding_coreTransvection]
    apply Subtype.ext
    change ⁅elementaryUnit lastIndex (coreIndex 1) (last_ne_core 1) a,
        elementaryUnit (coreIndex 1) (coreIndex 0)
          (coreIndex_injective.ne (by decide)) 1⁆ =
      elementaryUnit lastIndex (coreIndex 0) (last_ne_core 0) a
    simpa using elementaryUnit_commutator lastIndex (coreIndex 1) (coreIndex 0)
      (last_ne_core 1) (coreIndex_injective.ne (by decide)) (last_ne_core 0) a 1
  have hzeroLast (a : A) :
      transvection (coreIndex 0) lastIndex (core_ne_last 0) a ∈ H := by
    apply hcommutator (x := coreEmbedding (coreTransvection 0 1 (by decide) a))
      (y := transvection (coreIndex 1) lastIndex (core_ne_last 1) 1)
      (hcore _) (hlastColumn 1 (by decide) 1)
    rw [coreEmbedding_coreTransvection]
    apply Subtype.ext
    change ⁅elementaryUnit (coreIndex 0) (coreIndex 1)
          (coreIndex_injective.ne (by decide)) a,
        elementaryUnit (coreIndex 1) lastIndex (core_ne_last 1) 1⁆ =
      elementaryUnit (coreIndex 0) lastIndex (core_ne_last 0) a
    simpa using elementaryUnit_commutator (coreIndex 0) (coreIndex 1) lastIndex
      (coreIndex_injective.ne (by decide)) (core_ne_last 1) (core_ne_last 0) a 1
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  have hall (i j : Index) (hij : i ≠ j) (a : A) :
      transvection i j hij a ∈ H := by
    fin_cases i <;> fin_cases j
    all_goals try simp at hij
    · change transvection (coreIndex 0) (coreIndex 1)
        (coreIndex_injective.ne h01) a ∈ H
      rw [← coreEmbedding_coreTransvection (i := 0) (j := 1) (hij := h01)]
      exact hcore _
    · change transvection (coreIndex 0) (coreIndex 2)
        (coreIndex_injective.ne h02) a ∈ H
      rw [← coreEmbedding_coreTransvection (i := 0) (j := 2) (hij := h02)]
      exact hcore _
    · change transvection (coreIndex 0) lastIndex (core_ne_last 0) a ∈ H
      exact hzeroLast a
    · change transvection (coreIndex 1) (coreIndex 0)
        (coreIndex_injective.ne h10) a ∈ H
      rw [← coreEmbedding_coreTransvection (i := 1) (j := 0) (hij := h10)]
      exact hcore _
    · change transvection (coreIndex 1) (coreIndex 2)
        (coreIndex_injective.ne h12) a ∈ H
      rw [← coreEmbedding_coreTransvection (i := 1) (j := 2) (hij := h12)]
      exact hcore _
    · change transvection (coreIndex 1) lastIndex (core_ne_last 1) a ∈ H
      exact hlastColumn 1 h10 a
    · change transvection (coreIndex 2) (coreIndex 0)
        (coreIndex_injective.ne h20) a ∈ H
      rw [← coreEmbedding_coreTransvection (i := 2) (j := 0) (hij := h20)]
      exact hcore _
    · change transvection (coreIndex 2) (coreIndex 1)
        (coreIndex_injective.ne h21) a ∈ H
      rw [← coreEmbedding_coreTransvection (i := 2) (j := 1) (hij := h21)]
      exact hcore _
    · change transvection (coreIndex 2) lastIndex (core_ne_last 2) a ∈ H
      exact hlastColumn 2 h20 a
    · change transvection lastIndex (coreIndex 0) (last_ne_core 0) a ∈ H
      exact hlastZero a
    · change transvection lastIndex (coreIndex 1) (last_ne_core 1) a ∈ H
      exact hlastRow 1 h10 a
    · change transvection lastIndex (coreIndex 2) (last_ne_core 2) a ∈ H
      exact hlastRow 2 h20 a
  apply top_unique
  rintro ⟨g, hg⟩ -
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, j, hij, a, rfl⟩ := hx
      exact hall i j hij a
  | one => exact H.one_mem
  | mul x y _ _ hx hy => exact H.mul_mem hx hy
  | inv x _ hx => exact H.inv_mem hx

end RankFour
end NonsoficGroupsExist
