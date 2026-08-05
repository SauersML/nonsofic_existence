import NonsoficGroupsExist.Kazhdan
import NonsoficGroupsExist.SoficTransfer
import Mathlib.Algebra.Group.End

/-!
# Algebraic compression interface

This packages equations `eq:gen` and `eq:cent` without identifying an abstract
subgroup with its ambient image.  The types `Γ` and `J` carry injective maps
into `G`; conjugation by every compressor is represented by an endomorphism of
`Γ`.  The distinguished compressed copy and the commuting copy therefore
give an injective homomorphism `Γ × J → G`, the precise subgroup on which the
localized sofic approximation is constructed in the manuscript.

This module defines the reusable interface used by the compression argument.
The universal binary-Leavitt construction supplies a closed inhabitant in
`UniversalCompressionSetup`; the fields below are abstract only at this
general interface boundary and leave no open premise in the headline theorem.
-/

namespace NonsoficGroupsExist

/-- The algebraic inputs of the local matching argument, with
finite generation and infinitude explicit. -/
structure CompressionSetup (G Γ J : Type*) [Group G] [Group Γ] [Group J] where
  embedΓ : Γ →* G
  embedΓ_injective : Function.Injective embedΓ
  embedJ : J →* Γ
  embedJ_injective : Function.Injective embedJ
  generatorsΓ : Finset Γ
  generatorsΓ_one : 1 ∈ generatorsΓ
  generatorsΓ_symmetric : ∀ g ∈ generatorsΓ, g⁻¹ ∈ generatorsΓ
  generatorsΓ_generate : Subgroup.closure (generatorsΓ : Set Γ) = ⊤
  generatorsJ : Finset J
  generatorsJ_symmetric : ∀ g ∈ generatorsJ, g⁻¹ ∈ generatorsJ
  generatorsJ_generate : Subgroup.closure (generatorsJ : Set J) = ⊤
  infiniteΓ : Infinite Γ
  compressors : Finset G
  distinguished : G
  distinguished_mem : distinguished ∈ compressors
  compressedEnd : ∀ q : G, q ∈ compressors → Γ →* Γ
  compressedEnd_spec : ∀ (q : G) (hq : q ∈ compressors) (g : Γ),
    embedΓ (compressedEnd q hq g) = q * embedΓ g * q⁻¹
  generates : Subgroup.closure (Set.range embedΓ ∪ (compressors : Set G)) = ⊤
  centralizes : ∀ (g : Γ) (j : J),
    Commute (distinguished * embedΓ g * distinguished⁻¹) (embedΓ (embedJ j))
  disjoint : ∀ (g : Γ) (j : J),
    distinguished * embedΓ g * distinguished⁻¹ = embedΓ (embedJ j) →
      g = 1 ∧ j = 1

namespace CompressionSetup

variable {G Γ J : Type*} [Group G] [Group Γ] [Group J]
variable (C : CompressionSetup G Γ J)

/-- The distinguished compressed embedding `Γ → G`. -/
def compressedEmbedding : Γ →* G :=
  (MulAut.conj C.distinguished).toMonoidHom.comp C.embedΓ

@[simp] theorem compressedEmbedding_apply (g : Γ) :
    C.compressedEmbedding g = C.distinguished * C.embedΓ g * C.distinguished⁻¹ := by
  simp [compressedEmbedding, MulAut.conj_apply]

/-- The commuting subgroup embedded into `G`. -/
def commutingEmbedding : J →* G := C.embedΓ.comp C.embedJ

@[simp] theorem commutingEmbedding_apply (j : J) :
    C.commutingEmbedding j = C.embedΓ (C.embedJ j) := rfl

/-- Multiplication identifies the two commuting copies with a copy of
`Γ × J` inside `G`. -/
def productEmbedding : Γ × J →* G where
  toFun p := C.compressedEmbedding p.1 * C.commutingEmbedding p.2
  map_one' := by simp
  map_mul' x y := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
    have hc := C.centralizes y.1 x.2
    calc
      C.compressedEmbedding x.1 * C.compressedEmbedding y.1 *
          (C.commutingEmbedding x.2 * C.commutingEmbedding y.2) =
          C.compressedEmbedding x.1 *
            (C.compressedEmbedding y.1 * C.commutingEmbedding x.2) *
              C.commutingEmbedding y.2 := by group
      _ = C.compressedEmbedding x.1 *
            (C.commutingEmbedding x.2 * C.compressedEmbedding y.1) *
              C.commutingEmbedding y.2 := by
            rw [show C.compressedEmbedding y.1 * C.commutingEmbedding x.2 =
                C.commutingEmbedding x.2 * C.compressedEmbedding y.1 from by
              simpa [compressedEmbedding, commutingEmbedding, MulAut.conj_apply] using hc.eq]
      _ = C.compressedEmbedding x.1 * C.commutingEmbedding x.2 *
            (C.compressedEmbedding y.1 * C.commutingEmbedding y.2) := by group

theorem productEmbedding_injective : Function.Injective C.productEmbedding := by
  rintro ⟨g, j⟩ ⟨g', j'⟩ h
  have hinter : C.compressedEmbedding (g'⁻¹ * g) =
      C.commutingEmbedding (j' * j⁻¹) := by
    rw [map_mul, map_inv, map_mul, map_inv]
    calc
      (C.compressedEmbedding g')⁻¹ * C.compressedEmbedding g =
          (C.compressedEmbedding g')⁻¹ *
              (C.compressedEmbedding g * C.commutingEmbedding j) *
                (C.commutingEmbedding j)⁻¹ := by group
      _ = (C.compressedEmbedding g')⁻¹ *
              (C.compressedEmbedding g' * C.commutingEmbedding j') *
                (C.commutingEmbedding j)⁻¹ := by
            rw [show C.compressedEmbedding g * C.commutingEmbedding j =
                C.compressedEmbedding g' * C.commutingEmbedding j' from h]
      _ = C.commutingEmbedding j' * (C.commutingEmbedding j)⁻¹ := by group
  have htrivial : g'⁻¹ * g = 1 ∧ j' * j⁻¹ = 1 := by
    apply C.disjoint
    simpa [compressedEmbedding_apply, commutingEmbedding_apply] using hinter
  apply Prod.ext
  · have hg : g' = g := inv_mul_eq_one.mp htrivial.1
    exact hg.symm
  · have hj : j' = j := mul_inv_eq_one.mp htrivial.2
    exact hj.symm

/-- The localized product lies inside the original `Γ` copy. -/
theorem productEmbedding_eq_embedΓ (p : Γ × J) :
    C.productEmbedding p =
      C.embedΓ (C.compressedEnd C.distinguished C.distinguished_mem p.1 *
        C.embedJ p.2) := by
  rw [map_mul, C.compressedEnd_spec]
  rfl

end CompressionSetup
end NonsoficGroupsExist
