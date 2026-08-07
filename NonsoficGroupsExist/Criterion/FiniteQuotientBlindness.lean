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

/-! ## A strict compressor has no power in `Γ`

The complement to the blindness theorem.  Finite models fail because the
`Γ`-fixed set of a finite `H`-set is finite, hence equal to its own image
(`ExactCompression.fixedSet_image_eq`).  What makes the genuine coset space
different is that its `Γ`-fixed set is *infinite* -- and that is forced by
strictness alone. -/

/-- Iterated compression: `tʲ Γ t⁻ʲ ≤ Γ` for every `j`. -/
theorem pow_conj_mem (Γ : Subgroup H) {t : H} (ht : ∀ γ ∈ Γ, t * γ * t⁻¹ ∈ Γ) :
    ∀ (j : ℕ), ∀ γ ∈ Γ, t ^ j * γ * (t ^ j)⁻¹ ∈ Γ := by
  intro j
  induction j with
  | zero => intro γ hγ; simpa using hγ
  | succ j ih =>
      intro γ hγ
      have hstep := ht _ (ih γ hγ)
      have hrw : t * (t ^ j * γ * (t ^ j)⁻¹) * t⁻¹
          = t ^ (j + 1) * γ * (t ^ (j + 1))⁻¹ := by
        rw [pow_succ']
        group
      rwa [hrw] at hstep

/-- **A strict compressor has no power inside `Γ`.**  If some `tᵏ` with `k ≥ 1`
lay in `Γ`, the compression would be an equality: conjugating by `t⁻ᵏ ∈ Γ` stays
inside `Γ`, and the outer `t^{k-1}` does too by iterated compression, so
`t⁻¹Γt ≤ Γ` — which with the reverse inclusion forces `tΓt⁻¹ = Γ`. -/
theorem compression_eq_of_pow_mem (Γ : Subgroup H) {t : H}
    (ht : ∀ γ ∈ Γ, t * γ * t⁻¹ ∈ Γ) {k : ℕ} (hk : 0 < k) (hmem : t ^ k ∈ Γ)
    (γ : H) (hγ : γ ∈ Γ) : t⁻¹ * γ * t ∈ Γ := by
  -- conjugating by `t⁻ᵏ ∈ Γ` keeps us inside `Γ`
  have hinv : (t ^ k)⁻¹ ∈ Γ := Γ.inv_mem hmem
  have hinner : (t ^ k)⁻¹ * γ * t ^ k ∈ Γ := by
    have := Γ.mul_mem (Γ.mul_mem hinv hγ) hmem
    simpa using this
  -- and the outer conjugation by `t^{k-1}` does too
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have houter := pow_conj_mem Γ ht j _ hinner
  have hrw : t ^ j * ((t ^ (j + 1))⁻¹ * γ * t ^ (j + 1)) * (t ^ j)⁻¹
      = t⁻¹ * γ * t := by group
  rwa [hrw] at houter

/-- Consequently the ray `t⁻ⁿΓ` is injective in `n`: a repeat would put a power
of `t` in `Γ`.  So the `Γ`-fixed set of the coset space is infinite, which is
exactly what a finite model cannot reproduce. -/
theorem ray_injective (Γ : Subgroup H) {t : H} (ht : ∀ γ ∈ Γ, t * γ * t⁻¹ ∈ Γ)
    (hstrict : ∃ γ ∈ Γ, t⁻¹ * γ * t ∉ Γ) {m n : ℕ} (hmn : m < n)
    (heq : (t ^ m)⁻¹ * (t ^ n) ∈ Γ) : False := by
  obtain ⟨γ, hγ, hout⟩ := hstrict
  have hpow : t ^ (n - m) ∈ Γ := by
    have hsplit : (t ^ m)⁻¹ * t ^ n = t ^ (n - m) := by
      rw [← pow_sub_mul_pow t (le_of_lt hmn)]
      group
    rwa [hsplit] at heq
  exact hout (compression_eq_of_pow_mem Γ ht (by omega) hpow γ hγ)

end NonsoficGroupsExist
