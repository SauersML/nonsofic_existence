import NonsoficGroupsExist.ElementaryStabilization
import NonsoficGroupsExist.LeavittMatrixCompression

/-!
# The explicit rank-four compressor words

Two candidate matrices from the proposed characteristic-two construction are
defined here as literal words in elementary transvections, so their membership
in `EL₄` is proved.  We use `Fin 4`, with the first three coordinates forming
the core; `ElementaryStabilization` followed by reindexing embeds that core.

The matrix calculations below prove that the involution squares to one and
that conjugation by either compressor word implements `compressionEnd` on the
embedded core.  The module does not prove that these words and the core
generate the ambient elementary group, or supply the required non-LEF subgroup
of the core.  Consequently `compressorSet` is not by itself a constructed
`CompressionSetup`.
-/

namespace NonsoficGroupsExist
namespace RankFour

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

theorem transvection_sq [CharP A 2] (i j : Index) (hij : i ≠ j) (a : A) :
    transvection i j hij a * transvection i j hij a = 1 := by
  apply Subtype.ext
  change elementaryUnit i j hij a * elementaryUnit i j hij a = 1
  rw [elementaryUnit_mul, CharTwo.add_self_eq_zero, elementaryUnit_zero]

/-- The four-transvection factor `Uᵢ` in the pair of coordinates `(i,last)`. -/
def compressorPiece (L : LeavittFamily A) (i : Fin 3) : Ambient A :=
  transvection lastIndex (coreIndex i) (last_ne_core i) (1 + L.t0) *
    transvection (coreIndex i) lastIndex (core_ne_last i) 1 *
      transvection lastIndex (coreIndex i) (last_ne_core i) (1 + L.s0) *
        transvection (coreIndex i) lastIndex (core_ne_last i) L.t0

/-- The sparse matrix represented by one candidate compressor piece. -/
def compressorPieceMatrix (L : LeavittFamily A) (i : Fin 3) :
    Matrix Index Index A := fun r c ↦
  if r = coreIndex i then
    if c = coreIndex i then L.s0 else if c = lastIndex then L.p1 else 0
  else if r = lastIndex then
    if c = lastIndex then L.t0 else 0
  else if r = c then 1 else 0

@[simp] theorem compressorPiece_val [CharP A 2] (L : LeavittFamily A) (i : Fin 3) :
    (↑(↑(compressorPiece L i) : (Matrix Index Index A)ˣ) : Matrix Index Index A) =
      compressorPieceMatrix L i := by
  have hone (a : A) : 1 + (1 + a) = a := CharTwo.add_cancel_left 1 a
  have hupper (a : A) : a + (a + L.s0 * L.t0) + 1 = L.s1 * L.t1 := by
    calc
      a + (a + L.s0 * L.t0) + 1 =
          (a + a) + (L.s0 * L.t0 + 1) := by abel
      _ = L.s1 * L.t1 := by
        rw [CharTwo.add_self_eq_zero, zero_add, L.s0t0_add_one]
  have hlower (a b : A) :
      1 + a + (1 + b + (1 + a + (b + 1))) = 0 := by
    calc
      1 + a + (1 + b + (1 + a + (b + 1))) =
          (1 + 1) + (1 + 1) + (a + a) + (b + b) := by abel
      _ = 0 := by simp only [CharTwo.add_self_eq_zero]
  have hdiag (a b : A) :
      a + a * a + (a + b + (a + a * a + (b + a))) = 0 := by
    calc
      a + a * a + (a + b + (a + a * a + (b + a))) =
          (a + a) + (a + a) + (a * a + a * a) + (b + b) := by abel
      _ = 0 := by simp only [CharTwo.add_self_eq_zero]
  ext r c
  fin_cases i <;> fin_cases r <;> fin_cases c <;>
    simp [compressorPiece, compressorPieceMatrix, transvection, elementaryUnit,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ, coreIndex, lastIndex,
      LeavittFamily.p1, mul_add, add_mul, hone, hupper, hlower, hdiag]

/-- The comb compressor `u = U₃ U₂ U₁`, as twelve explicit elementary
transvections. -/
def compressor (L : LeavittFamily A) : Ambient A :=
  compressorPiece L 2 * compressorPiece L 1 * compressorPiece L 0

/-- The sparse upper-triangular value of the complete candidate compressor. -/
def compressorMatrix (L : LeavittFamily A) : Matrix Index Index A :=
  !![L.s0, 0, 0, L.p1;
     0, L.s0, 0, L.p1 * L.t0;
     0, 0, L.s0, L.p1 * L.t0 * L.t0;
     0, 0, 0, L.t0 * L.t0 * L.t0]

@[simp] theorem compressor_val [CharP A 2] (L : LeavittFamily A) :
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

/-- The involution word `z = x₁ₙ(s₁) xₙ₁(t₁) x₁ₙ(s₁)`. -/
def involution (L : LeavittFamily A) : Ambient A :=
  transvection (coreIndex 0) lastIndex (core_ne_last 0) L.s1 *
    transvection lastIndex (coreIndex 0) (last_ne_core 0) L.t1 *
      transvection (coreIndex 0) lastIndex (core_ne_last 0) L.s1

/-- The sparse matrix value of the involution word. -/
def involutionMatrix (L : LeavittFamily A) : Matrix Index Index A :=
  !![L.p0, 0, 0, L.s1;
     0, 1, 0, 0;
     0, 0, 1, 0;
     L.t1, 0, 0, 0]

@[simp] theorem involution_val [CharP A 2] (L : LeavittFamily A) :
    (↑(↑(involution L) : (Matrix Index Index A)ˣ) : Matrix Index Index A) =
      involutionMatrix L := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [involution, involutionMatrix, transvection, elementaryUnit,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ, coreIndex, lastIndex,
      LeavittFamily.p0, mul_add, add_mul, mul_assoc, CharTwo.add_self_eq_zero]

/-- The candidate involution really has order two in characteristic two. -/
theorem involution_sq [CharP A 2] (L : LeavittFamily A) :
    involution L * involution L = 1 := by
  let x : Ambient A :=
    transvection (coreIndex 0) lastIndex (core_ne_last 0) L.s1
  let y : Ambient A :=
    transvection lastIndex (coreIndex 0) (last_ne_core 0) L.t1
  have hx : x * x = 1 := transvection_sq _ _ _ _
  have hy : y * y = 1 := transvection_sq _ _ _ _
  change (x * y * x) * (x * y * x) = 1
  calc
    (x * y * x) * (x * y * x) = x * y * (x * x) * y * x := by group
    _ = x * (y * y) * x := by rw [hx]; simp only [mul_one]; group
    _ = 1 := by rw [hy]; simpa using hx

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

/-- On every elementary core generator, multiplication past the candidate
compressor implements coefficient compression. -/
theorem compressor_mul_coreTransvection [CharP A 2] (L : LeavittFamily A)
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
theorem compressor_mul_coreEmbedding [CharP A 2] (L : LeavittFamily A)
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
theorem compressor_conjugation [CharP A 2] (L : LeavittFamily A) (g : Core A) :
    compressor L * coreEmbedding g * (compressor L)⁻¹ =
      coreEmbedding (compressionEnd L g) := by
  rw [compressor_mul_coreEmbedding]
  group

/-- The involution commutes with every compressed elementary core generator. -/
theorem involution_commutes_compressed_coreTransvection [CharP A 2]
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
theorem involution_commutes_compressed_core [CharP A 2]
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
theorem secondCompressor_mul_coreEmbedding [CharP A 2]
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

theorem secondCompressor_conjugation [CharP A 2]
    (L : LeavittFamily A) (g : Core A) :
    secondCompressor L * coreEmbedding g * (secondCompressor L)⁻¹ =
      coreEmbedding (compressionEnd L g) := by
  rw [secondCompressor_mul_coreEmbedding]
  group

/-- The two-element set of candidate compressor words. -/
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

end RankFour
end NonsoficGroupsExist
