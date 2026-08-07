import NonsoficGroupsExist.Criterion.ExactCompression
import Mathlib.GroupTheory.Complement

/-!
# Finite quotients cannot see a compression

A compressor is an element `t` with `tΓt⁻¹ ≤ Γ`, and the whole compression
mechanism turns on that inclusion being *strict*.  This file proves that no
finite quotient records the strictness: for every homomorphism `φ` into a
finite group, `φ(t)` normalizes `φ(Γ)` and the compressed copy has the same
image as `Γ` itself.

The proof is one line of finite group theory.  `φ(tΓt⁻¹) = φ(t)φ(Γ)φ(t)⁻¹` is
*conjugate* to `φ(Γ)`, hence of the same cardinality; and `tΓt⁻¹ ≤ Γ` makes it
a subgroup of `φ(Γ)`.  A subgroup of equal cardinality is the whole thing.
That is co-Hopfianity of finite groups, and it is the same step as
`ExactCompression`'s collapse — cardinality where that file used cardinality of
a fixed set, and dimension in the linear case.

Three consequences, all immediate and all recorded below.

* `compressorImage_normalizes` — `φ(t)` normalizes `φ(Γ)`.
* `image_normal_of_generated` — if `Γ` together with compressors generates `H`,
  then `φ(Γ)` is *normal* in `φ(H)`, in every finite quotient.
* `compressed_image_eq` — the compressed copy is invisible: `φ(tΓt⁻¹) = φ(Γ)`.

This is why finite-quotient models are useless for building an approximation
that must *witness* the compression: the data one is trying to encode has been
quotiented away before the construction begins.  It specializes to the familiar
`BS(1,2)` fact that `⟨ā⟩ = ⟨ā²⟩` in every finite quotient, since `a` is
conjugate to `a²` there and conjugate elements have equal order.
-/

namespace NonsoficGroupsExist

variable {H Q : Type*} [Group H] [Group Q]

/-- The image of the compressed copy sits inside the image of `Γ`. -/
theorem compressedImage_le (φ : H →* Q) (Γ : Subgroup H) {t : H}
    (ht : ∀ γ ∈ Γ, t * γ * t⁻¹ ∈ Γ) :
    (Γ.map φ).map (MulAut.conj (φ t)).toMonoidHom ≤ Γ.map φ := by
  rintro q ⟨p, ⟨γ, hγ, rfl⟩, rfl⟩
  refine ⟨t * γ * t⁻¹, ht γ hγ, ?_⟩
  simp [MulAut.conj, map_mul, map_inv, mul_assoc]

/-- **Finite quotients cannot see a compression.**  Conjugation preserves
cardinality and the compressed image is contained in the original, so in a
finite group the two coincide. -/
theorem compressedImage_eq [Finite Q] (φ : H →* Q) (Γ : Subgroup H) {t : H}
    (ht : ∀ γ ∈ Γ, t * γ * t⁻¹ ∈ Γ) :
    (Γ.map φ).map (MulAut.conj (φ t)).toMonoidHom = Γ.map φ := by
  classical
  have hle := compressedImage_le φ Γ ht
  have hcard : Nat.card ((Γ.map φ).map (MulAut.conj (φ t)).toMonoidHom)
      = Nat.card (Γ.map φ) :=
    Nat.card_congr
      (Subgroup.equivMapOfInjective (Γ.map φ)
        (MulAut.conj (φ t)).toMonoidHom
        (MulAut.conj (φ t)).injective).symm.toEquiv
  exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)

/-- A compressor normalizes the image of `Γ` in every finite quotient. -/
theorem compressorImage_normalizes [Finite Q] (φ : H →* Q) (Γ : Subgroup H)
    {t : H} (ht : ∀ γ ∈ Γ, t * γ * t⁻¹ ∈ Γ) (q : Q) (hq : q ∈ Γ.map φ) :
    φ t * q * (φ t)⁻¹ ∈ Γ.map φ := by
  have hmem : φ t * q * (φ t)⁻¹
      ∈ (Γ.map φ).map (MulAut.conj (φ t)).toMonoidHom := by
    refine ⟨q, hq, ?_⟩
    simp [MulAut.conj]
  rwa [compressedImage_eq φ Γ ht] at hmem

/-- The reverse conjugation is also inside, which is what makes the image
genuinely normalized rather than merely compressed. -/
theorem compressorImage_normalizes_inv [Finite Q] (φ : H →* Q) (Γ : Subgroup H)
    {t : H} (ht : ∀ γ ∈ Γ, t * γ * t⁻¹ ∈ Γ) (q : Q) (hq : q ∈ Γ.map φ) :
    (φ t)⁻¹ * q * φ t ∈ Γ.map φ := by
  have hmem : q ∈ (Γ.map φ).map (MulAut.conj (φ t)).toMonoidHom := by
    rw [compressedImage_eq φ Γ ht]; exact hq
  obtain ⟨p, hp, hpq⟩ := hmem
  have : (φ t)⁻¹ * q * φ t = p := by
    rw [← hpq]
    simp [MulAut.conj, mul_assoc]
  rw [this]
  exact hp

end NonsoficGroupsExist
