import NonsoficGroupsExist.ElementaryStabilization
import NonsoficGroupsExist.LeavittMatrixCompression

/-!
# The explicit rank-four compressor words

The two matrices used in the characteristic-two spine are defined here as
literal words in elementary transvections.  Thus their membership in `EL₄` is
constructive, rather than a field of a setup structure.  We use the block
index `Fin 3 ⊕ Unit`; `ElementaryStabilization` identifies its upper-left
`Fin 3` block with the subgroup `EL₃`.
-/

namespace NonsoficGroupsExist
namespace RankFour

variable {A : Type*} [Ring A]

abbrev Index := Fin 3 ⊕ Unit
abbrev Ambient (A : Type*) [Ring A] := elementaryGroup Index A
abbrev Core (A : Type*) [Ring A] := elementaryGroup (Fin 3) A

def coreIndex (i : Fin 3) : Index := Sum.inl i
def lastIndex : Index := Sum.inr ()

theorem last_ne_core (i : Fin 3) : lastIndex ≠ coreIndex i := by simp [lastIndex, coreIndex]
theorem core_ne_last (i : Fin 3) : coreIndex i ≠ lastIndex := by simp [lastIndex, coreIndex]

/-- An elementary transvection, corestricted to the elementary group. -/
def transvection (i j : Index) (hij : i ≠ j) (a : A) : Ambient A :=
  ⟨elementaryUnit i j hij a, elementaryUnit_mem i j hij a⟩

/-- The four-transvection factor `Uᵢ` in the pair of coordinates `(i,last)`. -/
def compressorPiece (L : LeavittFamily A) (i : Fin 3) : Ambient A :=
  transvection lastIndex (coreIndex i) (last_ne_core i) (1 + L.t0) *
    transvection (coreIndex i) lastIndex (core_ne_last i) 1 *
      transvection lastIndex (coreIndex i) (last_ne_core i) (1 + L.s0) *
        transvection (coreIndex i) lastIndex (core_ne_last i) L.t0

/-- The comb compressor `u = U₃ U₂ U₁`, as twelve explicit elementary
transvections. -/
def compressor (L : LeavittFamily A) : Ambient A :=
  compressorPiece L 2 * compressorPiece L 1 * compressorPiece L 0

/-- The involution word `z = x₁ₙ(s₁) xₙ₁(t₁) x₁ₙ(s₁)`. -/
def involution (L : LeavittFamily A) : Ambient A :=
  transvection (coreIndex 0) lastIndex (core_ne_last 0) L.s1 *
    transvection lastIndex (coreIndex 0) (last_ne_core 0) L.t1 *
      transvection (coreIndex 0) lastIndex (core_ne_last 0) L.s1

/-- The second compressor `v = z u`. -/
def secondCompressor (L : LeavittFamily A) : Ambient A :=
  involution L * compressor L

/-- The actual upper-left embedding `EL₃(A) → EL₄(A)`. -/
noncomputable def coreEmbedding : Core A →* Ambient A :=
  elementaryStabilization (ι := Fin 3) (κ := Unit) (R := A)

theorem coreEmbedding_injective : Function.Injective (coreEmbedding (A := A)) :=
  elementaryStabilization_injective

/-- The endomorphism induced by the compressed coefficient corner. -/
noncomputable def compressionEnd (L : LeavittFamily A) : Core A →* Core A :=
  L.elementaryCompressionEnd

theorem compressionEnd_injective (L : LeavittFamily A) :
    Function.Injective (compressionEnd L) :=
  L.elementaryCompressionEnd_injective

/-- The two-element compressor set used by the criterion. -/
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
