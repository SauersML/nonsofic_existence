import NonsoficGroupsExist.Leavitt.ElementaryStabilization
import NonsoficGroupsExist.Leavitt.LeavittMatrixCompression

/-!
# The explicit characteristic-free rank-four compressor words

Two compressor matrices over any ring carrying a binary Leavitt family are
defined here as literal words in elementary transvections, so their membership
in `EL₄` is proved without a characteristic or `K₁` assumption.  We use
`Fin 4`, with the first three coordinates forming the core;
`ElementaryStabilization` followed by reindexing embeds that core.

The matrix calculations below prove that the involution squares to one and
that conjugation by either compressor word implements `compressionEnd` on the
embedded core.  They also prove that the two words together with the core
generate the ambient elementary group.  The complementary non-LEF subgroup is
specialized to the universal binary Leavitt algebra and is supplied in
`UniversalRankFour`; `UniversalCompressionSetup` combines both parts.
-/

namespace NonsoficGroupsExist
namespace RankFour

open scoped commutatorElement

variable {A : Type*} [Ring A]

abbrev Index := Fin 4
abbrev Ambient (A : Type*) [Ring A] := elementaryGroup Index A
abbrev Core (A : Type*) [Ring A] := elementaryGroup (Fin 3) A

def coreIndex (i : Fin 3) : Index := Fin.castSucc i
def lastIndex : Index := 3

theorem coreIndex_injective : Function.Injective coreIndex := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun x : Index ↦ x.val) h

theorem last_ne_core (i : Fin 3) : lastIndex ≠ coreIndex i := by
  intro h
  have hval := congrArg Fin.val h
  simp [lastIndex, coreIndex] at hval
  omega

theorem core_ne_last (i : Fin 3) : coreIndex i ≠ lastIndex := by
  exact (last_ne_core i).symm

/-- An elementary transvection in the three-dimensional core. -/
def coreTransvection (i j : Fin 3) (hij : i ≠ j) (a : A) : Core A :=
  ⟨elementaryUnit i j hij a, elementaryUnit_mem i j hij a⟩

/-- An elementary transvection, corestricted to the elementary group. -/
def transvection (i j : Index) (hij : i ≠ j) (a : A) : Ambient A :=
  ⟨elementaryUnit i j hij a, elementaryUnit_mem i j hij a⟩

/-- The four-transvection factor `Uᵢ` in the pair of coordinates `(i,last)`. -/
def compressorPiece (L : LeavittFamily A) (i : Fin 3) : Ambient A :=
  transvection lastIndex (coreIndex i) (last_ne_core i) (L.t0 - 1) *
    transvection (coreIndex i) lastIndex (core_ne_last i) 1 *
      transvection lastIndex (coreIndex i) (last_ne_core i) (L.s0 - 1) *
        transvection (coreIndex i) lastIndex (core_ne_last i) (-L.t0)

/-- The sparse matrix represented by one compressor piece. -/
def compressorPieceMatrix (L : LeavittFamily A) (i : Fin 3) :
    Matrix Index Index A := fun r c ↦
  if r = coreIndex i then
    if c = coreIndex i then L.s0 else if c = lastIndex then L.p1 else 0
  else if r = lastIndex then
    if c = lastIndex then L.t0 else 0
  else if r = c then 1 else 0

@[simp] theorem compressorPiece_val (L : LeavittFamily A) (i : Fin 3) :
    (↑(↑(compressorPiece L i) : (Matrix Index Index A)ˣ) : Matrix Index Index A) =
      compressorPieceMatrix L i := by
  have hp1 : -L.p0 + 1 = L.p1 := by
    rw [← L.p0_add_p1]
    abel
  have hupper : -L.t0 + (L.t0 - L.s0 * L.t0) + 1 = L.p1 := by
    calc
      -L.t0 + (L.t0 - L.s0 * L.t0) + 1 = -L.p0 + 1 := by
        simp only [LeavittFamily.p0]
        abel
      _ = L.p1 := hp1
  have hcancel :
      L.t0 - 1 + (L.s0 - 1 + (1 - L.s0 - (L.t0 - 1))) = 0 := by
    abel
  ext r c
  fin_cases i <;> fin_cases r <;> fin_cases c <;>
    simp [compressorPiece, compressorPieceMatrix, transvection, elementaryUnit,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ, coreIndex, lastIndex,
      hupper, hcancel, mul_add, add_mul, mul_sub, sub_mul]

/-- The comb compressor `u = U₃ U₂ U₁`, as twelve explicit elementary
transvections. -/
def compressor (L : LeavittFamily A) : Ambient A :=
  compressorPiece L 2 * compressorPiece L 1 * compressorPiece L 0

/-- The sparse upper-triangular value of the complete compressor. -/
def compressorMatrix (L : LeavittFamily A) : Matrix Index Index A :=
  !![L.s0, 0, 0, L.p1;
     0, L.s0, 0, L.p1 * L.t0;
     0, 0, L.s0, L.p1 * L.t0 * L.t0;
     0, 0, 0, L.t0 * L.t0 * L.t0]

@[simp] theorem compressor_val (L : LeavittFamily A) :
    (↑(↑(compressor L) : (Matrix Index Index A)ˣ) : Matrix Index Index A) =
      compressorMatrix L := by
  change
    (↑(↑(compressorPiece L 2) : (Matrix Index Index A)ˣ) : Matrix Index Index A) *
        (↑(↑(compressorPiece L 1) : (Matrix Index Index A)ˣ) : Matrix Index Index A) *
          (↑(↑(compressorPiece L 0) : (Matrix Index Index A)ˣ) : Matrix Index Index A) =
      compressorMatrix L
  rw [compressorPiece_val, compressorPiece_val, compressorPiece_val]
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [compressorPieceMatrix, compressorMatrix, Matrix.mul_apply,
      Fin.sum_univ_succ, coreIndex, lastIndex, mul_assoc]

/-- The Whitehead word in the coordinate pair `(last, 0)`. -/
def lastWhiteheadWord (u : Aˣ) : Ambient A :=
  transvection lastIndex (coreIndex 0) (last_ne_core 0) (↑u : A) *
    transvection (coreIndex 0) lastIndex (core_ne_last 0) (-(↑u⁻¹ : A)) *
      transvection lastIndex (coreIndex 0) (last_ne_core 0) (↑u : A)

@[simp] theorem lastWhiteheadWord_val (u : Aˣ) :
    (↑(↑(lastWhiteheadWord u) : (Matrix Index Index A)ˣ) : Matrix Index Index A) =
      !![0, 0, 0, -(↑u⁻¹ : A);
         0, 1, 0, 0;
         0, 0, 1, 0;
         (↑u : A), 0, 0, 0] := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [lastWhiteheadWord, transvection, elementaryUnit,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ, coreIndex,
      lastIndex]

/-- The balanced Whitehead diagonal, with `u` in the last coordinate and
`u⁻¹` in coordinate zero. -/
def lastBalanced (u : Aˣ) : Ambient A :=
  lastWhiteheadWord u * lastWhiteheadWord (-1 : Aˣ)

@[simp] theorem lastBalanced_val (u : Aˣ) :
    (↑(↑(lastBalanced u) : (Matrix Index Index A)ˣ) : Matrix Index Index A) =
      !![(↑u⁻¹ : A), 0, 0, 0;
         0, 1, 0, 0;
         0, 0, 1, 0;
         0, 0, 0, (↑u : A)] := by
  change (↑(↑(lastWhiteheadWord u) : (Matrix Index Index A)ˣ) :
      Matrix Index Index A) *
      (↑(↑(lastWhiteheadWord (-1 : Aˣ)) : (Matrix Index Index A)ˣ) :
        Matrix Index Index A) = _
  rw [lastWhiteheadWord_val, lastWhiteheadWord_val]
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]

/-- Whitehead's commutator diagonal in the last coordinate. -/
def lastDiagonalCommutator (a b : Aˣ) : Ambient A :=
  lastBalanced a * lastBalanced b * lastBalanced ((b * a)⁻¹)

@[simp] theorem lastDiagonalCommutator_val (a b : Aˣ) :
    (↑(↑(lastDiagonalCommutator a b) : (Matrix Index Index A)ˣ) :
      Matrix Index Index A) =
      !![1, 0, 0, 0;
         0, 1, 0, 0;
         0, 0, 1, 0;
         0, 0, 0, (↑⁅a, b⁆ : A)] := by
  change (↑(↑(lastBalanced a) : (Matrix Index Index A)ˣ) :
      Matrix Index Index A) *
      (↑(↑(lastBalanced b) : (Matrix Index Index A)ˣ) :
        Matrix Index Index A) *
        (↑(↑(lastBalanced ((b * a)⁻¹)) : (Matrix Index Index A)ˣ) :
          Matrix Index Index A) = _
  rw [lastBalanced_val, lastBalanced_val, lastBalanced_val]
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, commutatorElement_def, mul_assoc]

/-- The elementary diagonal sign correction.  The Leavitt relations prove
that its last entry is `-1`; no `K₁` input is involved. -/
def signCorrection (L : LeavittFamily A) : Ambient A :=
  lastDiagonalCommutator L.cornerSign L.cornerSwap

@[simp] theorem signCorrection_val (L : LeavittFamily A) :
    (↑(↑(signCorrection L) : (Matrix Index Index A)ˣ) : Matrix Index Index A) =
      !![1, 0, 0, 0;
         0, 1, 0, 0;
         0, 0, 1, 0;
         0, 0, 0, -1] := by
  rw [signCorrection, lastDiagonalCommutator_val,
    L.cornerSign_commutator_cornerSwap]
  rfl

/-- The three-transvection word has the desired involution block except for
the last-row sign. -/
def rawInvolutionWord (L : LeavittFamily A) : Ambient A :=
  transvection (coreIndex 0) lastIndex (core_ne_last 0) L.s1 *
    transvection lastIndex (coreIndex 0) (last_ne_core 0) (-L.t1) *
      transvection (coreIndex 0) lastIndex (core_ne_last 0) L.s1

/-- The characteristic-free elementary involution word. -/
def involution (L : LeavittFamily A) : Ambient A :=
  signCorrection L * rawInvolutionWord L

/-- The sparse matrix value of the involution word. -/
def involutionMatrix (L : LeavittFamily A) : Matrix Index Index A :=
  !![L.p0, 0, 0, L.s1;
     0, 1, 0, 0;
     0, 0, 1, 0;
     L.t1, 0, 0, 0]

@[simp] theorem involution_val (L : LeavittFamily A) :
    (↑(↑(involution L) : (Matrix Index Index A)ˣ) : Matrix Index Index A) =
      involutionMatrix L := by
  have hcorner : 1 + -(L.s1 * L.t1) = L.s0 * L.t0 := by
    rw [← L.p0_add_s1t1]
    abel
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [involution, rawInvolutionWord, involutionMatrix, transvection, elementaryUnit,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ, coreIndex, lastIndex,
      hcorner, LeavittFamily.p0, mul_add, add_mul, mul_assoc]

/-- The compressor involution has order two in every characteristic. -/
theorem involution_sq (L : LeavittFamily A) :
    involution L * involution L = 1 := by
  apply Subtype.ext
  apply Units.ext
  change
    (↑(↑(involution L) : (Matrix Index Index A)ˣ) : Matrix Index Index A) *
      (↑(↑(involution L) : (Matrix Index Index A)ˣ) : Matrix Index Index A) = 1
  rw [involution_val]
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [involutionMatrix, Matrix.mul_apply, Fin.sum_univ_succ,
      LeavittFamily.p0, L.sum_range, mul_assoc]

/-- The second compressor `v = z u`. -/
def secondCompressor (L : LeavittFamily A) : Ambient A :=
  involution L * compressor L

/-- The coordinate equivalence used to reindex the block stabilization. -/
def stabilizationIndexEquiv : Fin 3 ⊕ Unit ≃ Index :=
  (Equiv.sumCongr (Equiv.refl (Fin 3)) finOneEquiv.symm).trans
    finSumFinEquiv

@[simp] theorem stabilizationIndexEquiv_inl (i : Fin 3) :
    stabilizationIndexEquiv (Sum.inl i) = coreIndex i := by
  rfl

/-- The actual upper-left embedding `EL₃(A) → EL₄(A)`. -/
noncomputable def coreEmbedding : Core A →* Ambient A :=
  (elementaryReindexEquiv (R := A) stabilizationIndexEquiv).toMonoidHom.comp
    (elementaryStabilization (ι := Fin 3) (κ := Unit) (R := A))

theorem coreEmbedding_injective : Function.Injective (coreEmbedding (A := A)) :=
  (elementaryReindexEquiv (R := A) stabilizationIndexEquiv).injective.comp
    elementaryStabilization_injective

@[simp] theorem coreEmbedding_coreTransvection (i j : Fin 3) (hij : i ≠ j) (a : A) :
    coreEmbedding (coreTransvection i j hij a) =
      transvection (coreIndex i) (coreIndex j) (coreIndex_injective.ne hij) a := by
  apply Subtype.ext
  change elementaryReindexUnitEquiv (R := A) stabilizationIndexEquiv
      (stabilizeUnit (κ := Unit) (elementaryUnit i j hij a)) =
    elementaryUnit (coreIndex i) (coreIndex j) (coreIndex_injective.ne hij) a
  rw [stabilizeUnit_elementaryUnit, elementaryReindexUnitEquiv_elementaryUnit]
  rfl

/-- The endomorphism induced by the compressed coefficient corner. -/
noncomputable def compressionEnd (L : LeavittFamily A) : Core A →* Core A :=
  L.elementaryCompressionEnd

theorem compressionEnd_injective (L : LeavittFamily A) :
    Function.Injective (compressionEnd L) :=
  L.elementaryCompressionEnd_injective

@[simp] theorem compressionEnd_coreTransvection (L : LeavittFamily A)
    (i j : Fin 3) (hij : i ≠ j) (a : A) :
    compressionEnd L (coreTransvection i j hij a) =
      coreTransvection i j hij (L.s0 * a * L.t0) := by
  apply Subtype.ext
  exact L.matrixCompression_elementaryUnit i j hij a

/-- On every elementary core generator, multiplication past the
compressor implements coefficient compression. -/
theorem compressor_mul_coreTransvection (L : LeavittFamily A)
    (i j : Fin 3) (hij : i ≠ j) (a : A) :
    compressor L * coreEmbedding (coreTransvection i j hij a) =
      coreEmbedding (compressionEnd L (coreTransvection i j hij a)) * compressor L := by
  rw [compressionEnd_coreTransvection, coreEmbedding_coreTransvection,
    coreEmbedding_coreTransvection]
  apply Subtype.ext
  apply Units.ext
  ext r c
  fin_cases i <;> fin_cases j
  all_goals try simp at hij
  all_goals fin_cases r <;> fin_cases c
  all_goals
    simp [transvection, elementaryUnit, compressorMatrix, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_succ, coreIndex, LeavittFamily.p1, mul_assoc]

/-- The generator calculation extends to every element of `EL₃(A)`. -/
theorem compressor_mul_coreEmbedding (L : LeavittFamily A)
    (g : Core A) :
    compressor L * coreEmbedding g = coreEmbedding (compressionEnd L g) * compressor L := by
  rcases g with ⟨g, hg⟩
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, j, hij, a, rfl⟩ := hx
      exact compressor_mul_coreTransvection L i j hij a
  | one =>
      change compressor L * coreEmbedding (1 : Core A) =
        coreEmbedding (compressionEnd L (1 : Core A)) * compressor L
      rw [map_one, map_one]
      rw [map_one]
      simp
  | mul x y hxmem hymem hx hy =>
      change compressor L * coreEmbedding (⟨x, hxmem⟩ * ⟨y, hymem⟩) =
        coreEmbedding (compressionEnd L (⟨x, hxmem⟩ * ⟨y, hymem⟩)) * compressor L
      rw [map_mul, map_mul]
      calc
        compressor L * (coreEmbedding ⟨x, hxmem⟩ * coreEmbedding ⟨y, hymem⟩) =
            (compressor L * coreEmbedding ⟨x, hxmem⟩) * coreEmbedding ⟨y, hymem⟩ := by
          group
        _ = (coreEmbedding (compressionEnd L ⟨x, hxmem⟩) * compressor L) *
            coreEmbedding ⟨y, hymem⟩ := by rw [hx]
        _ = coreEmbedding (compressionEnd L ⟨x, hxmem⟩) *
            (compressor L * coreEmbedding ⟨y, hymem⟩) := by group
        _ = coreEmbedding (compressionEnd L ⟨x, hxmem⟩) *
            (coreEmbedding (compressionEnd L ⟨y, hymem⟩) * compressor L) := by rw [hy]
        _ = (coreEmbedding (compressionEnd L ⟨x, hxmem⟩) *
            coreEmbedding (compressionEnd L ⟨y, hymem⟩)) * compressor L := by group
        _ = coreEmbedding
            (compressionEnd L ⟨x, hxmem⟩ * compressionEnd L ⟨y, hymem⟩) *
              compressor L := by rw [map_mul]
  | inv x hxmem hx =>
      change compressor L * coreEmbedding (⟨x, hxmem⟩⁻¹) =
        coreEmbedding (compressionEnd L (⟨x, hxmem⟩⁻¹)) * compressor L
      rw [map_inv, map_inv]
      calc
        compressor L * (coreEmbedding ⟨x, hxmem⟩)⁻¹ =
            (coreEmbedding (compressionEnd L ⟨x, hxmem⟩))⁻¹ *
              (coreEmbedding (compressionEnd L ⟨x, hxmem⟩) * compressor L) *
                (coreEmbedding ⟨x, hxmem⟩)⁻¹ := by group
        _ = (coreEmbedding (compressionEnd L ⟨x, hxmem⟩))⁻¹ *
              (compressor L * coreEmbedding ⟨x, hxmem⟩) *
                (coreEmbedding ⟨x, hxmem⟩)⁻¹ := by rw [hx]
        _ = (coreEmbedding (compressionEnd L ⟨x, hxmem⟩))⁻¹ * compressor L := by group

/-- Conjugation by the first explicit compressor is exactly the concrete
coefficient-compression endomorphism on the embedded core. -/
theorem compressor_conjugation (L : LeavittFamily A) (g : Core A) :
    compressor L * coreEmbedding g * (compressor L)⁻¹ =
      coreEmbedding (compressionEnd L g) := by
  rw [compressor_mul_coreEmbedding]
  group

/-- The involution commutes with every compressed elementary core generator. -/
theorem involution_commutes_compressed_coreTransvection
    (L : LeavittFamily A) (i j : Fin 3) (hij : i ≠ j) (a : A) :
    Commute (involution L)
      (coreEmbedding (compressionEnd L (coreTransvection i j hij a))) := by
  rw [compressionEnd_coreTransvection, coreEmbedding_coreTransvection]
  apply Subtype.ext
  apply Units.ext
  ext r c
  fin_cases i <;> fin_cases j
  all_goals try simp at hij
  all_goals fin_cases r <;> fin_cases c
  all_goals
    simp [transvection, elementaryUnit, involutionMatrix, Matrix.mul_apply,
      Matrix.one_apply, Fin.sum_univ_succ, coreIndex, LeavittFamily.p0,
      mul_add, add_mul, mul_assoc]

/-- The generator calculation extends to the complete compressed core. -/
theorem involution_commutes_compressed_core
    (L : LeavittFamily A) (g : Core A) :
    Commute (involution L) (coreEmbedding (compressionEnd L g)) := by
  rcases g with ⟨g, hg⟩
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, j, hij, a, rfl⟩ := hx
      exact involution_commutes_compressed_coreTransvection L i j hij a
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

/-- The second explicit word implements the same compression endomorphism. -/
theorem secondCompressor_mul_coreEmbedding
    (L : LeavittFamily A) (g : Core A) :
    secondCompressor L * coreEmbedding g =
      coreEmbedding (compressionEnd L g) * secondCompressor L := by
  calc
    secondCompressor L * coreEmbedding g =
        involution L * (compressor L * coreEmbedding g) := by
      simp only [secondCompressor, mul_assoc]
    _ = involution L *
        (coreEmbedding (compressionEnd L g) * compressor L) := by
      rw [compressor_mul_coreEmbedding]
    _ = (coreEmbedding (compressionEnd L g) * involution L) * compressor L := by
      rw [← mul_assoc, (involution_commutes_compressed_core L g).eq]
    _ = coreEmbedding (compressionEnd L g) * secondCompressor L := by
      simp only [secondCompressor, mul_assoc]

theorem secondCompressor_conjugation
    (L : LeavittFamily A) (g : Core A) :
    secondCompressor L * coreEmbedding g * (secondCompressor L)⁻¹ =
      coreEmbedding (compressionEnd L g) := by
  rw [secondCompressor_mul_coreEmbedding]
  group

/-- Conjugation by the involution turns a core root out of coordinate zero
into a last-row root. -/
theorem involution_conjugates_lastRow (L : LeavittFamily A)
    (j : Fin 3) (hj : j ≠ 0) (a : A) :
    involution L *
        coreEmbedding (coreTransvection 0 j hj.symm (L.s1 * a)) * involution L =
      transvection lastIndex (coreIndex j) (last_ne_core j) a := by
  rw [coreEmbedding_coreTransvection]
  apply Subtype.ext
  apply Units.ext
  ext r c
  fin_cases j
  · simp at hj
  · fin_cases r <;> fin_cases c <;>
      simp [transvection, elementaryUnit, involutionMatrix,
        Matrix.mul_apply, Fin.sum_univ_succ, coreIndex,
        lastIndex, mul_add, mul_assoc]
  · fin_cases r <;> fin_cases c <;>
      simp [transvection, elementaryUnit, involutionMatrix,
        Matrix.mul_apply, Fin.sum_univ_succ, coreIndex,
        lastIndex, mul_add, mul_assoc]

/-- Conjugation by the involution turns a core root into coordinate zero into
a last-column root. -/
theorem involution_conjugates_lastColumn (L : LeavittFamily A)
    (i : Fin 3) (hi : i ≠ 0) (a : A) :
    involution L *
        coreEmbedding (coreTransvection i 0 hi (a * L.t1)) * involution L =
      transvection (coreIndex i) lastIndex (core_ne_last i) a := by
  rw [coreEmbedding_coreTransvection]
  apply Subtype.ext
  apply Units.ext
  ext r c
  fin_cases i
  · simp at hi
  · fin_cases r <;> fin_cases c <;>
      simp [transvection, elementaryUnit, involutionMatrix,
        Matrix.mul_apply, Fin.sum_univ_succ, coreIndex,
        lastIndex, mul_add, mul_assoc]
  · fin_cases r <;> fin_cases c <;>
      simp [transvection, elementaryUnit, involutionMatrix,
        Matrix.mul_apply, Fin.sum_univ_succ, coreIndex,
        lastIndex, mul_add, mul_assoc]

/-- The two-element set of compressor words. -/
noncomputable def compressorSet (L : LeavittFamily A) : Finset (Ambient A) :=
  by
    classical
    exact {compressor L, secondCompressor L}

theorem compressor_mem (L : LeavittFamily A) : compressor L ∈ compressorSet L := by
  classical
  simp [compressorSet]

theorem secondCompressor_mem (L : LeavittFamily A) :
    secondCompressor L ∈ compressorSet L := by
  classical
  simp [compressorSet]

/-- Every member of the explicit two-word set implements the concrete
compression endomorphism. -/
theorem compressorSet_conjugation (L : LeavittFamily A)
    (q : Ambient A) (hq : q ∈ compressorSet L) (g : Core A) :
    coreEmbedding (compressionEnd L g) = q * coreEmbedding g * q⁻¹ := by
  classical
  simp only [compressorSet, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl
  · exact (compressor_conjugation L g).symm
  · exact (secondCompressor_conjugation L g).symm

/-- The embedded core together with the two explicit compressor words generates
the complete rank-four elementary group. -/
theorem coreEmbedding_compressorSet_generate (L : LeavittFamily A) :
    Subgroup.closure
      (Set.range (coreEmbedding (A := A)) ∪ (compressorSet L : Set (Ambient A))) = ⊤ := by
  let H : Subgroup (Ambient A) := Subgroup.closure
    (Set.range (coreEmbedding (A := A)) ∪ (compressorSet L : Set (Ambient A)))
  have hcore (g : Core A) : coreEmbedding g ∈ H := by
    apply Subgroup.subset_closure
    exact Or.inl ⟨g, rfl⟩
  have hcompressor : compressor L ∈ H := by
    apply Subgroup.subset_closure
    exact Or.inr (compressor_mem L)
  have hsecond : secondCompressor L ∈ H := by
    apply Subgroup.subset_closure
    exact Or.inr (secondCompressor_mem L)
  have hinvolution : involution L ∈ H := by
    have : secondCompressor L * (compressor L)⁻¹ ∈ H :=
      H.mul_mem hsecond (H.inv_mem hcompressor)
    simpa [secondCompressor] using this
  have hlastRow (j : Fin 3) (hj : j ≠ 0) (a : A) :
      transvection lastIndex (coreIndex j) (last_ne_core j) a ∈ H := by
    rw [← involution_conjugates_lastRow L j hj a]
    exact H.mul_mem (H.mul_mem hinvolution (hcore _)) hinvolution
  have hlastColumn (i : Fin 3) (hi : i ≠ 0) (a : A) :
      transvection (coreIndex i) lastIndex (core_ne_last i) a ∈ H := by
    rw [← involution_conjugates_lastColumn L i hi a]
    exact H.mul_mem (H.mul_mem hinvolution (hcore _)) hinvolution
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
