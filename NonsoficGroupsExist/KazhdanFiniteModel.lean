import NonsoficGroupsExist.KazhdanOrthogonal
import NonsoficGroupsExist.Sofic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Hyperreal
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Finite permutation representations

This module turns an exact action on a finite set into its canonical
orthogonal representation on the real square-summable functions.  It is the
finite-dimensional representation used in the spectral part of Kun's
expander-decomposition argument.
-/

namespace NonsoficGroupsExist
namespace KazhdanFiniteModel

open scoped symmDiff
open KazhdanOrthogonal

universe u v

variable {G : Type u} [Group G]
variable {Y : Type v} [Fintype Y]

/-- The orthogonal operator on `ℓ²(Y)` induced by a permutation of `Y`. -/
noncomputable def permutationOperator (p : Equiv.Perm Y) :
    EuclideanSpace ℝ Y ≃ₗᵢ[ℝ] EuclideanSpace ℝ Y :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ p

@[simp] theorem permutationOperator_apply (p : Equiv.Perm Y)
    (x : EuclideanSpace ℝ Y) (y : Y) :
    permutationOperator p x y = x (p.symm y) := rfl

@[simp] theorem permutationOperator_one :
    permutationOperator (1 : Equiv.Perm Y) = 1 := by
  ext x y
  change x ((1 : Equiv.Perm Y).symm y) = x y
  rw [show (1 : Equiv.Perm Y).symm = 1 by rfl]
  rfl

@[simp] theorem permutationOperator_mul (p q : Equiv.Perm Y) :
    permutationOperator (p * q) = permutationOperator p * permutationOperator q := by
  ext x y
  change x ((p * q).symm y) = x (q.symm (p.symm y))
  rw [show (p * q).symm = q.symm * p.symm by rfl]
  rfl

/-- The real orthogonal representation induced by an exact finite
permutation action. -/
noncomputable def permutationRepresentation (σ : G →* Equiv.Perm Y) :
    G →* (EuclideanSpace ℝ Y ≃ₗᵢ[ℝ] EuclideanSpace ℝ Y) where
  toFun g := permutationOperator (σ g)
  map_one' := by simp
  map_mul' g h := by simp

@[simp] theorem permutationRepresentation_apply
    (σ : G →* Equiv.Perm Y) (g : G) (x : EuclideanSpace ℝ Y) (y : Y) :
    permutationRepresentation σ g x y = x ((σ g).symm y) := rfl

/-- Transitivity of an exact finite permutation action. -/
def IsTransitive (σ : G →* Equiv.Perm Y) : Prop :=
  ∀ x y : Y, ∃ g : G, σ g x = y

/-- In a transitive finite action, the invariant vectors in the permutation
representation are exactly the constant functions. -/
theorem invariant_iff_constant (σ : G →* Equiv.Perm Y)
    (htrans : IsTransitive σ) (x : EuclideanSpace ℝ Y) :
    (∀ g : G, permutationRepresentation σ g x = x) ↔
      ∀ a b : Y, x a = x b := by
  constructor
  · intro hinv a b
    obtain ⟨g, hg⟩ := htrans a b
    have h := congrArg (fun z : EuclideanSpace ℝ Y ↦ z b) (hinv g)
    have hpre : (σ g).symm b = a := by
      apply (σ g).injective
      simp [hg]
    simpa [permutationRepresentation_apply, hpre] using h
  · intro hconstant g
    ext y
    exact hconstant _ _

/-- The constant vector with prescribed value. -/
noncomputable def constantVector (c : ℝ) : EuclideanSpace ℝ Y :=
  WithLp.toLp 2 fun _ ↦ c

omit [Fintype Y] in
@[simp] theorem constantVector_apply (c : ℝ) (y : Y) :
    constantVector c y = c := rfl

/-- Permutation operators fix constant vectors. -/
@[simp] theorem permutationOperator_constantVector
    (p : Equiv.Perm Y) (c : ℝ) :
    permutationOperator p (constantVector c) = constantVector c := by
  ext y
  rfl

section

variable [DecidableEq Y]

/-- The characteristic vector of a finite subset, regarded as a vector in
`ℓ²(Y)`. -/
noncomputable def indicator (U : Finset Y) : EuclideanSpace ℝ Y := by
  exact WithLp.toLp 2 fun y ↦ if y ∈ U then 1 else 0

omit [Fintype Y] in
@[simp] theorem indicator_apply (U : Finset Y) (y : Y) :
    indicator U y = if y ∈ U then 1 else 0 := by
  rfl

/-- Permuting a characteristic vector gives the characteristic vector of
the permuted set. -/
theorem permutationOperator_indicator (p : Equiv.Perm Y) (U : Finset Y) :
    permutationOperator p (indicator U) = indicator (U.map p.toEmbedding) := by
  classical
  ext y
  simp [permutationOperator_apply, indicator_apply]

/-- The squared `ℓ²` norm of a characteristic vector is the cardinality of
its support. -/
theorem norm_indicator_sq (U : Finset Y) :
    ‖indicator U‖ ^ 2 = (U.card : ℝ) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [indicator_apply]

/-- The squared distance between two characteristic vectors counts their
symmetric difference. -/
theorem norm_indicator_sub_sq (U V : Finset Y) :
    ‖indicator U - indicator V‖ ^ 2 = ((U ∆ V).card : ℝ) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  classical
  rw [show ((U ∆ V).card : ℝ) =
      ∑ y : Y, if y ∈ U ∆ V then 1 else 0 by simp]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hyU : y ∈ U <;> by_cases hyV : y ∈ V <;>
    simp [indicator_apply, Finset.mem_symmDiff, hyU, hyV]

/-- The displacement of a characteristic vector under a permutation counts
the symmetric difference between the set and its image. -/
theorem norm_permutationOperator_indicator_sub_sq
    (p : Equiv.Perm Y) (U : Finset Y) :
    ‖permutationOperator p (indicator U) - indicator U‖ ^ 2 =
      (((U.map p.toEmbedding) ∆ U).card : ℝ) := by
  rw [permutationOperator_indicator, norm_indicator_sub_sq]

/-- Points on which two finite permutations disagree. -/
def permutationDisagreement (p q : Equiv.Perm Y) : Finset Y :=
  Finset.univ.filter fun y ↦ p y ≠ q y

@[simp] theorem mem_permutationDisagreement (p q : Equiv.Perm Y) (y : Y) :
    y ∈ permutationDisagreement p q ↔ p y ≠ q y := by
  simp [permutationDisagreement]

/-- Images of a set under two permutations can differ only through images
of points where the permutations disagree. -/
theorem symmDiff_image_subset_disagreement_images
    (p q : Equiv.Perm Y) (U : Finset Y) :
    (U.map p.toEmbedding) ∆ (U.map q.toEmbedding) ⊆
      (permutationDisagreement p q).map p.toEmbedding ∪
        (permutationDisagreement p q).map q.toEmbedding := by
  intro y hy
  rw [Finset.mem_symmDiff] at hy
  rcases hy with ⟨hp, hnq⟩ | ⟨hq, hnp⟩
  · rw [Finset.mem_map] at hp
    obtain ⟨x, hx, rfl⟩ := hp
    apply Finset.mem_union_left
    rw [Finset.mem_map]
    refine ⟨x, (mem_permutationDisagreement p q x).2 ?_, rfl⟩
    intro heq
    apply hnq
    exact Finset.mem_map.mpr ⟨x, hx, heq.symm⟩
  · rw [Finset.mem_map] at hq
    obtain ⟨x, hx, rfl⟩ := hq
    apply Finset.mem_union_right
    rw [Finset.mem_map]
    refine ⟨x, (mem_permutationDisagreement p q x).2 ?_, rfl⟩
    intro heq
    apply hnp
    exact Finset.mem_map.mpr ⟨x, hx, heq⟩

/-- Symmetric difference of images is at most twice the permutation
disagreement set. -/
theorem card_symmDiff_images_le_two_mul_disagreement
    (p q : Equiv.Perm Y) (U : Finset Y) :
    ((U.map p.toEmbedding) ∆ (U.map q.toEmbedding)).card ≤
      2 * (permutationDisagreement p q).card := by
  calc
    ((U.map p.toEmbedding) ∆ (U.map q.toEmbedding)).card ≤
        ((permutationDisagreement p q).map p.toEmbedding ∪
          (permutationDisagreement p q).map q.toEmbedding).card :=
      Finset.card_le_card (symmDiff_image_subset_disagreement_images p q U)
    _ ≤ ((permutationDisagreement p q).map p.toEmbedding).card +
        ((permutationDisagreement p q).map q.toEmbedding).card :=
      Finset.card_union_le _ _
    _ = 2 * (permutationDisagreement p q).card := by
      simp only [Finset.card_map]
      omega

/-- Hamming disagreement controls the squared `ℓ²` error made by replacing
one permutation operator with another on a characteristic vector. -/
theorem norm_permutationOperators_indicator_sub_sq_le
    (p q : Equiv.Perm Y) (U : Finset Y) :
    ‖permutationOperator p (indicator U) -
        permutationOperator q (indicator U)‖ ^ 2 ≤
      2 * (permutationDisagreement p q).card := by
  rw [permutationOperator_indicator, permutationOperator_indicator,
    norm_indicator_sub_sq]
  exact_mod_cast card_symmDiff_images_le_two_mul_disagreement p q U

/-- The characteristic vector after subtracting its global mean. -/
noncomputable def centeredIndicator (U : Finset Y) : EuclideanSpace ℝ Y :=
  indicator U - ((U.card : ℝ) / Fintype.card Y) • constantVector 1

@[simp] theorem centeredIndicator_apply (U : Finset Y) (y : Y) :
    centeredIndicator U y =
      (if y ∈ U then 1 else 0) - (U.card : ℝ) / Fintype.card Y := by
  simp [centeredIndicator]

/-- Centering does not change a characteristic vector's displacement under
a permutation. -/
theorem permutationOperator_centeredIndicator_sub
    (p : Equiv.Perm Y) (U : Finset Y) :
    permutationOperator p (centeredIndicator U) - centeredIndicator U =
      permutationOperator p (indicator U) - indicator U := by
  simp [centeredIndicator, map_sub, map_smul]

/-- Centering also cancels when comparing two permutation operators. -/
theorem permutationOperators_centeredIndicator_sub
    (p q : Equiv.Perm Y) (U : Finset Y) :
    permutationOperator p (centeredIndicator U) -
        permutationOperator q (centeredIndicator U) =
      permutationOperator p (indicator U) -
        permutationOperator q (indicator U) := by
  simp [centeredIndicator, map_sub, map_smul]

/-- Hamming disagreement controls operator replacement error on centered
characteristic vectors as well. -/
theorem norm_permutationOperators_centeredIndicator_sub_sq_le
    (p q : Equiv.Perm Y) (U : Finset Y) :
    ‖permutationOperator p (centeredIndicator U) -
        permutationOperator q (centeredIndicator U)‖ ^ 2 ≤
      2 * (permutationDisagreement p q).card := by
  rw [permutationOperators_centeredIndicator_sub]
  exact norm_permutationOperators_indicator_sub_sq_le p q U

/-- Exact variance formula for a centered characteristic vector. -/
theorem norm_centeredIndicator_sq [Nonempty Y] (U : Finset Y) :
    ‖centeredIndicator U‖ ^ 2 =
      (U.card : ℝ) * (1 - (U.card : ℝ) / Fintype.card Y) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  let a : ℝ := (U.card : ℝ) / Fintype.card Y
  have hpoint (y : Y) :
      (centeredIndicator U y) ^ 2 =
        if y ∈ U then (1 - a) ^ 2 else a ^ 2 := by
    by_cases hy : y ∈ U <;> simp [centeredIndicator_apply, a, hy]
  simp_rw [hpoint]
  have hcardNat : 0 < Fintype.card Y := Fintype.card_pos
  have hcard : (Fintype.card Y : ℝ) ≠ 0 := by exact_mod_cast hcardNat.ne'
  simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul]
  have hfilterU : (Finset.univ.filter fun y : Y ↦ y ∈ U) = U := by
    ext y
    simp
  rw [hfilterU]
  change (U.card : ℝ) * (1 - a) ^ 2 +
      ((Finset.univ.filter fun y : Y ↦ y ∉ U).card : ℝ) * a ^ 2 =
        (U.card : ℝ) * (1 - (U.card : ℝ) / Fintype.card Y)
  have hcomplement : (Finset.univ.filter fun y : Y ↦ y ∉ U).card =
      Fintype.card Y - U.card := by
    rw [← Finset.card_compl]
    congr
    ext y
    simp
  rw [hcomplement]
  have hUle : U.card ≤ Fintype.card Y := Finset.card_le_univ U
  rw [Nat.cast_sub hUle]
  dsimp [a]
  field_simp
  ring

/-- Centered characteristic vectors have normalized squared norm at most
one, uniformly over the finite model and the subset. -/
theorem norm_centeredIndicator_sq_div_card_le_one [Nonempty Y]
    (U : Finset Y) :
    ‖centeredIndicator U‖ ^ 2 / Fintype.card Y ≤ 1 := by
  rw [norm_centeredIndicator_sq]
  have hcardNat : 0 < Fintype.card Y := Fintype.card_pos
  have hcard : (0 : ℝ) < Fintype.card Y := by exact_mod_cast hcardNat
  have hUleNat : U.card ≤ Fintype.card Y := Finset.card_le_univ U
  have hUle : (U.card : ℝ) ≤ Fintype.card Y := by exact_mod_cast hUleNat
  have hdensityNonneg : (0 : ℝ) ≤ (U.card : ℝ) / Fintype.card Y := by
    positivity
  have hdensityLe : (U.card : ℝ) / Fintype.card Y ≤ 1 := by
    exact (div_le_one hcard).2 hUle
  have hrewrite :
      (U.card : ℝ) * (1 - (U.card : ℝ) / Fintype.card Y) /
          Fintype.card Y =
        ((U.card : ℝ) / Fintype.card Y) *
          (1 - (U.card : ℝ) / Fintype.card Y) := by
    field_simp
  rw [hrewrite]
  nlinarith [sq_nonneg ((U.card : ℝ) / Fintype.card Y)]

/-- A centered characteristic vector has coordinate sum zero. -/
theorem sum_centeredIndicator [Nonempty Y] (U : Finset Y) :
    ∑ y : Y, centeredIndicator U y = 0 := by
  have hcardNat : 0 < Fintype.card Y := Fintype.card_pos
  have hcard : (Fintype.card Y : ℝ) ≠ 0 := by exact_mod_cast hcardNat.ne'
  simp_rw [centeredIndicator_apply]
  rw [Finset.sum_sub_distrib]
  simp
  field_simp
  ring

/-- For a transitive action, centered characteristic vectors are orthogonal
to every invariant vector. -/
theorem centeredIndicator_mem_orthogonal [Nonempty Y]
    (σ : G →* Equiv.Perm Y) (htrans : IsTransitive σ) (U : Finset Y) :
    centeredIndicator U ∈
      (invariantSubmodule (permutationRepresentation σ))ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro x hx
  obtain ⟨y₀⟩ := ‹Nonempty Y›
  have hxinv : ∀ g : G, permutationRepresentation σ g x = x :=
    (mem_invariantSubmodule (permutationRepresentation σ) x).1 hx
  have hxconstant : ∀ y z : Y, x y = x z :=
    (invariant_iff_constant σ htrans x).1 hxinv
  rw [PiLp.inner_apply]
  calc
    (∑ y : Y, inner ℝ (x y) (centeredIndicator U y)) =
        ∑ y : Y, x y * centeredIndicator U y := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Real.inner_apply]
    _ = ∑ y : Y, x y₀ * centeredIndicator U y := by
      apply Finset.sum_congr rfl
      intro y _
      rw [hxconstant y y₀]
    _ = x y₀ * ∑ y : Y, centeredIndicator U y := by
      rw [Finset.mul_sum]
    _ = 0 := by rw [sum_centeredIndicator]; ring

/-- A nonempty subset of at most half the finite space has a nonzero centered
characteristic vector. -/
theorem centeredIndicator_ne_zero [Nonempty Y] (U : Finset Y)
    (hU : U.Nonempty) (hhalf : 2 * U.card ≤ Fintype.card Y) :
    centeredIndicator U ≠ 0 := by
  intro hzero
  have hnorm := norm_centeredIndicator_sq U
  rw [hzero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hnorm
  have hUposNat : 0 < U.card := Finset.card_pos.mpr hU
  have hUpos : (0 : ℝ) < U.card := by exact_mod_cast hUposNat
  have hcardPosNat : 0 < Fintype.card Y := Fintype.card_pos
  have hcardPos : (0 : ℝ) < Fintype.card Y := by exact_mod_cast hcardPosNat
  have hhalfReal : (2 : ℝ) * U.card ≤ Fintype.card Y := by
    exact_mod_cast hhalf
  have hdensity : (U.card : ℝ) / Fintype.card Y ≤ 1 / 2 := by
    rw [div_le_iff₀ hcardPos]
    linarith
  nlinarith

/-- A Kazhdan pair gives a uniform set-expansion estimate for every exact
transitive finite action. -/
theorem exists_symmDiff_lower_bound [Nonempty Y]
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, v} G Q ε)
    (σ : G →* Equiv.Perm Y) (htrans : IsTransitive σ)
    (U : Finset Y) (hU : U.Nonempty)
    (hhalf : 2 * U.card ≤ Fintype.card Y) :
    ∃ q ∈ Q, ε ^ 2 / 2 * U.card ≤
      (((U.map (σ q).toEmbedding) ∆ U).card : ℝ) := by
  have hxorth := centeredIndicator_mem_orthogonal σ htrans U
  have hxne := centeredIndicator_ne_zero U hU hhalf
  obtain ⟨q, hq, hmove⟩ :=
    exists_moved_mul_norm_of_mem_orthogonal hQ
      (permutationRepresentation σ) hxorth hxne
  refine ⟨q, hq, ?_⟩
  have hleftNonneg : 0 ≤ ε * ‖centeredIndicator U‖ :=
    mul_nonneg hQ.1.le (norm_nonneg _)
  have hrightNonneg :
      0 ≤ ‖permutationRepresentation σ q (centeredIndicator U) -
        centeredIndicator U‖ := norm_nonneg _
  have hmoveSq :=
    (sq_le_sq₀ hleftNonneg hrightNonneg).2 hmove
  have hdisp :
      ‖permutationRepresentation σ q (centeredIndicator U) -
          centeredIndicator U‖ ^ 2 =
        (((U.map (σ q).toEmbedding) ∆ U).card : ℝ) := by
    change ‖permutationOperator (σ q) (centeredIndicator U) -
      centeredIndicator U‖ ^ 2 = _
    rw [permutationOperator_centeredIndicator_sub,
      norm_permutationOperator_indicator_sub_sq]
  have hnorm := norm_centeredIndicator_sq U
  have hcardPosNat : 0 < Fintype.card Y := Fintype.card_pos
  have hcardPos : (0 : ℝ) < Fintype.card Y := by exact_mod_cast hcardPosNat
  have hhalfReal : (2 : ℝ) * U.card ≤ Fintype.card Y := by
    exact_mod_cast hhalf
  have hdensity : (U.card : ℝ) / Fintype.card Y ≤ 1 / 2 := by
    rw [div_le_iff₀ hcardPos]
    linarith
  have hnormLower : (U.card : ℝ) / 2 ≤ ‖centeredIndicator U‖ ^ 2 := by
    rw [hnorm]
    have hU : (0 : ℝ) ≤ U.card := by positivity
    nlinarith
  rw [hdisp] at hmoveSq
  have hεsq : 0 ≤ ε ^ 2 := sq_nonneg ε
  calc
    ε ^ 2 / 2 * U.card = ε ^ 2 * ((U.card : ℝ) / 2) := by ring
    _ ≤ ε ^ 2 * ‖centeredIndicator U‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hnormLower hεsq
    _ = (ε * ‖centeredIndicator U‖) ^ 2 := by ring
    _ ≤ (((U.map (σ q).toEmbedding) ∆ U).card : ℝ) := hmoveSq

/-- Summed generator form of the exact finite-action expansion estimate. -/
theorem sum_symmDiff_lower_bound [Nonempty Y]
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, v} G Q ε)
    (σ : G →* Equiv.Perm Y) (htrans : IsTransitive σ)
    (U : Finset Y) (hU : U.Nonempty)
    (hhalf : 2 * U.card ≤ Fintype.card Y) :
    ε ^ 2 / 2 * U.card ≤
      ∑ q ∈ Q, (((U.map (σ q).toEmbedding) ∆ U).card : ℝ) := by
  obtain ⟨q, hq, hbound⟩ :=
    exists_symmDiff_lower_bound hQ σ htrans U hU hhalf
  refine hbound.trans ?_
  exact Finset.single_le_sum
    (fun g _ ↦ Nat.cast_nonneg (((U.map (σ g).toEmbedding) ∆ U).card)) hq

/-- Generator-labelled boundary size of a subset in an exact finite action.
Each label is retained, so coincident permutations do not lose
multiplicity. -/
def actionBoundarySize (σ : G →* Equiv.Perm Y) (Q : Finset G)
    (U : Finset Y) : ℕ :=
  ∑ q ∈ Q, ((U.map (σ q).toEmbedding) ∆ U).card

/-- Uniform set expansion for an exact finite action, expressed with the
labelled boundary size. -/
def HasActionExpansion (σ : G →* Equiv.Perm Y) (Q : Finset G)
    (h : ℝ) : Prop :=
  ∀ U : Finset Y, U.Nonempty → 2 * U.card ≤ Fintype.card Y →
    h * U.card ≤ actionBoundarySize σ Q U

/-- Every exact transitive finite action of a group with Kazhdan pair
`(Q, ε)` has expansion constant `ε² / 2`. -/
theorem hasActionExpansion_of_kazhdanPair [Nonempty Y]
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, v} G Q ε)
    (σ : G →* Equiv.Perm Y) (htrans : IsTransitive σ) :
    HasActionExpansion σ Q (ε ^ 2 / 2) := by
  intro U hU hhalf
  have h := sum_symmDiff_lower_bound hQ σ htrans U hU hhalf
  simpa [actionBoundarySize] using h

/-- Concrete spectral-gap form for an exact finite permutation action: the
orbit average contracts every centered characteristic vector. -/
theorem norm_orbitAverage_centeredIndicator_le [Nonempty Y]
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, v} G Q ε)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S) (hεone : ε ≤ 1)
    (σ : G →* Equiv.Perm Y) (htrans : IsTransitive σ) (U : Finset Y) :
    ‖IsKazhdanPair.orbitAverage S (permutationRepresentation σ)
        (centeredIndicator U)‖ ≤
      (1 - ε ^ 2 / (4 * S.card)) * ‖centeredIndicator U‖ := by
  apply norm_orbitAverage_le_of_mem_orthogonal hQ S hQS hone hεone
    (permutationRepresentation σ)
  exact centeredIndicator_mem_orthogonal σ htrans U

omit [DecidableEq Y] in
/-- Pointwise formula for the orbit average in a finite permutation
representation. -/
theorem orbitAverage_permutationRepresentation_apply
    (S : Finset G) (σ : G →* Equiv.Perm Y)
    (x : EuclideanSpace ℝ Y) (y : Y) :
    IsKazhdanPair.orbitAverage S (permutationRepresentation σ) x y =
      ((S.card : ℝ)⁻¹) * ∑ q ∈ S, x ((σ q).symm y) := by
  classical
  simp [IsKazhdanPair.orbitAverage, permutationRepresentation_apply]

/-- The orbit of a point in an exact finite action. -/
noncomputable def orbitFinset (σ : G →* Equiv.Perm Y) (x : Y) : Finset Y := by
  classical
  exact Finset.univ.filter fun y ↦ ∃ g : G, σ g x = y

omit [DecidableEq Y] in
@[simp] theorem mem_orbitFinset (σ : G →* Equiv.Perm Y) (x y : Y) :
    y ∈ orbitFinset σ x ↔ ∃ g : G, σ g x = y := by
  classical
  simp [orbitFinset]

/-- Restriction of one action permutation to a chosen orbit. -/
noncomputable def orbitPermutation (σ : G →* Equiv.Perm Y) (x : Y) (g : G) :
    Equiv.Perm (orbitFinset σ x) where
  toFun y := ⟨σ g y.1, by
    rw [mem_orbitFinset]
    obtain ⟨h, hh⟩ := (mem_orbitFinset σ x y.1).1 y.2
    exact ⟨g * h, by simp [hh]⟩⟩
  invFun y := ⟨σ g⁻¹ y.1, by
    rw [mem_orbitFinset]
    obtain ⟨h, hh⟩ := (mem_orbitFinset σ x y.1).1 y.2
    exact ⟨g⁻¹ * h, by simp [hh]⟩⟩
  left_inv y := by
    apply Subtype.ext
    simp
  right_inv y := by
    apply Subtype.ext
    simp

/-- The exact action restricted to one of its finite orbits. -/
noncomputable def orbitAction (σ : G →* Equiv.Perm Y) (x : Y) :
    G →* Equiv.Perm (orbitFinset σ x) where
  toFun := orbitPermutation σ x
  map_one' := by
    ext y
    simp [orbitPermutation]
  map_mul' g h := by
    ext y
    simp [orbitPermutation]

omit [DecidableEq Y] in
/-- An action restricted to one orbit is transitive. -/
theorem orbitAction_transitive (σ : G →* Equiv.Perm Y) (x : Y) :
    IsTransitive (orbitAction σ x) := by
  intro y z
  obtain ⟨g, hg⟩ := (mem_orbitFinset σ x y.1).1 y.2
  obtain ⟨h, hh⟩ := (mem_orbitFinset σ x z.1).1 z.2
  refine ⟨h * g⁻¹, ?_⟩
  apply Subtype.ext
  change σ (h * g⁻¹) y.1 = z.1
  rw [← hg, ← hh]
  simp

/-- Every orbit of an exact finite action of a Kazhdan group is a uniform
expander, with the same constant for all finite actions and all orbits. -/
theorem orbitAction_hasExpansion
    {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, v} G Q ε)
    (σ : G →* Equiv.Perm Y) (x : Y) :
    HasActionExpansion (orbitAction σ x) Q (ε ^ 2 / 2) := by
  let x' : orbitFinset σ x :=
    ⟨x, (mem_orbitFinset σ x x).2 ⟨1, by simp⟩⟩
  letI : Nonempty (orbitFinset σ x) := ⟨x'⟩
  exact hasActionExpansion_of_kazhdanPair hQ (orbitAction σ x)
    (orbitAction_transitive σ x)

end

section SoficNormalization

variable {M : FiniteModel}

/-- The local disagreement cardinality is exactly the numerator in normalized
Hamming distance. -/
theorem hammingDistance_eq_permutationDisagreement_ratio
    (p q : Equiv.Perm M) :
    hammingDistance M p q =
      ((permutationDisagreement p q).card : ℝ) / Fintype.card M := rfl

/-- Normalized Hilbert error is bounded by twice normalized Hamming error. -/
theorem normalized_norm_permutationOperators_indicator_sub_sq_le
    [Nonempty M] (p q : Equiv.Perm M) (U : Finset M) :
    ‖permutationOperator p (indicator U) -
        permutationOperator q (indicator U)‖ ^ 2 / Fintype.card M ≤
      2 * hammingDistance M p q := by
  have h := norm_permutationOperators_indicator_sub_sq_le p q U
  have hcardNat : 0 < Fintype.card M := Fintype.card_pos
  have hcard : (0 : ℝ) < Fintype.card M := by exact_mod_cast hcardNat
  rw [hammingDistance_eq_permutationDisagreement_ratio]
  calc
    ‖permutationOperator p (indicator U) -
        permutationOperator q (indicator U)‖ ^ 2 / Fintype.card M ≤
        (2 * (permutationDisagreement p q).card : ℝ) / Fintype.card M :=
      div_le_div_of_nonneg_right h hcard.le
    _ = 2 * (((permutationDisagreement p q).card : ℝ) /
        Fintype.card M) := by ring

/-- The same normalized Hamming control for centered characteristic
vectors. -/
theorem normalized_norm_permutationOperators_centeredIndicator_sub_sq_le
    [Nonempty M] (p q : Equiv.Perm M) (U : Finset M) :
    ‖permutationOperator p (centeredIndicator U) -
        permutationOperator q (centeredIndicator U)‖ ^ 2 /
        Fintype.card M ≤
      2 * hammingDistance M p q := by
  rw [permutationOperators_centeredIndicator_sub]
  exact normalized_norm_permutationOperators_indicator_sub_sq_le p q U

/-- Approximate multiplicativity in a sofic approximation gives uniformly
vanishing normalized Hilbert error on every centered characteristic vector.
The subset may vary arbitrarily with the approximation index. -/
theorem sofic_multiplication_hilbert_error_eventually
    (A : SoficApproximation G) (g h : G) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ U : Finset (A.model n),
      ‖permutationOperator (A.map n (g * h)) (centeredIndicator U) -
          permutationOperator (A.map n g * A.map n h)
            (centeredIndicator U)‖ ^ 2 /
          Fintype.card (A.model n) < δ := by
  obtain ⟨Nerr, hNerr⟩ :=
    A.asymptoticallyMultiplicative g h (δ / 2) (half_pos hδ)
  obtain ⟨Ncard, hNcard⟩ := A.card_tendsToInfinity 1
  refine ⟨max Nerr Ncard, fun n hn U ↦ ?_⟩
  have hnerr : Nerr ≤ n := (le_max_left _ _).trans hn
  have hncard : Ncard ≤ n := (le_max_right _ _).trans hn
  have hcard : 0 < Fintype.card (A.model n) := by
    have := hNcard n hncard
    omega
  letI : Nonempty (A.model n) := Fintype.card_pos_iff.mp hcard
  have hbound :=
    normalized_norm_permutationOperators_centeredIndicator_sub_sq_le
      (A.map n (g * h)) (A.map n g * A.map n h) U
  have herr := hNerr n hnerr
  exact hbound.trans_lt (by linarith)

/-- A sofic approximation also respects the `g⁻¹h` displacement permutation:
the assigned permutation approaches `(map g)⁻¹ * map h`. -/
theorem sofic_inv_mul_close_eventually (A : SoficApproximation G)
    (g h : G) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N,
      hammingDistance (A.model n) (A.map n (g⁻¹ * h))
        ((A.map n g)⁻¹ * A.map n h) < ε := by
  have hthird : 0 < ε / 3 := by positivity
  obtain ⟨Nmul, hNmul⟩ :=
    A.asymptoticallyMultiplicative g⁻¹ h (ε / 3) hthird
  obtain ⟨Ninv, hNinv⟩ :=
    A.asymptoticallyMultiplicative g⁻¹ g (ε / 3) hthird
  obtain ⟨None, hNone⟩ := A.map_one_close (ε / 3) hthird
  refine ⟨max Nmul (max Ninv None), fun n hn ↦ ?_⟩
  have hnmul : Nmul ≤ n := by omega
  have hninv : Ninv ≤ n := by omega
  have hnone : None ≤ n := by omega
  have hmul := hNmul n hnmul
  have hinvMul := hNinv n hninv
  have hone := hNone n hnone
  simp only [inv_mul_cancel] at hinvMul
  have hinv : hammingDistance (A.model n) (A.map n g⁻¹)
      (A.map n g)⁻¹ < 2 * (ε / 3) := by
    have htri := hammingDistance_triangle (A.model n)
      (A.map n g⁻¹ * A.map n g) (A.map n 1) 1
    have hprod : hammingDistance (A.model n) (A.map n g⁻¹ * A.map n g) 1 <
        2 * (ε / 3) := by
      rw [hammingDistance_comm] at hinvMul
      linarith
    calc
      hammingDistance (A.model n) (A.map n g⁻¹) (A.map n g)⁻¹ =
          hammingDistance (A.model n)
            (A.map n g⁻¹ * A.map n g) ((A.map n g)⁻¹ * A.map n g) := by
        rw [hammingDistance_right_invariant]
      _ = hammingDistance (A.model n)
          (A.map n g⁻¹ * A.map n g) 1 := by simp
      _ < 2 * (ε / 3) := hprod
  have hright : hammingDistance (A.model n)
      (A.map n g⁻¹ * A.map n h) ((A.map n g)⁻¹ * A.map n h) <
      2 * (ε / 3) := by
    rw [hammingDistance_right_invariant]
    exact hinv
  have htri := hammingDistance_triangle (A.model n)
    (A.map n (g⁻¹ * h)) (A.map n g⁻¹ * A.map n h)
    ((A.map n g)⁻¹ * A.map n h)
  linarith

/-- Uniformize an eventually statement over a fixed finite index set. -/
theorem eventually_all_finset {ι : Type*} (s : Finset ι)
    (P : ι → ℕ → Prop)
    (hP : ∀ i ∈ s, ∃ N : ℕ, ∀ n ≥ N, P i n) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ i ∈ s, P i n := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨0, by simp⟩
  | @insert a s ha ih =>
      obtain ⟨Na, hNa⟩ := hP a (by simp)
      obtain ⟨Ns, hNs⟩ := ih fun i hi ↦ hP i (by simp [hi])
      refine ⟨max Na Ns, fun n hn i hi ↦ ?_⟩
      rw [Finset.mem_insert] at hi
      rcases hi with rfl | hi
      · exact hNa n ((le_max_left _ _).trans hn)
      · exact hNs n ((le_max_right _ _).trans hn) i hi

/-- The normalized Hilbert multiplicativity error is eventually uniform on
every prescribed finite multiplication table. -/
theorem sofic_multiplication_hilbert_error_on_finset_eventually
    (A : SoficApproximation G) (F : Finset G) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ g ∈ F, ∀ h ∈ F,
      ∀ U : Finset (A.model n),
        ‖permutationOperator (A.map n (g * h)) (centeredIndicator U) -
            permutationOperator (A.map n g * A.map n h)
              (centeredIndicator U)‖ ^ 2 /
            Fintype.card (A.model n) < δ := by
  obtain ⟨N, hN⟩ := eventually_all_finset (F.product F)
    (fun p n ↦ ∀ U : Finset (A.model n),
      ‖permutationOperator (A.map n (p.1 * p.2)) (centeredIndicator U) -
          permutationOperator (A.map n p.1 * A.map n p.2)
            (centeredIndicator U)‖ ^ 2 /
          Fintype.card (A.model n) < δ) (by
      intro p hp
      exact sofic_multiplication_hilbert_error_eventually
        A p.1 p.2 δ hδ)
  refine ⟨N, fun n hn g hg h hh U ↦ ?_⟩
  exact hN n hn (g, h) (Finset.mem_product.mpr ⟨hg, hh⟩) U

/-- Normalized matrix coefficient of a centered characteristic vector under
one permutation. -/
noncomputable def normalizedPermutationCorrelation (M : FiniteModel)
    (U : Finset M) (p : Equiv.Perm M) : ℝ :=
  inner ℝ (centeredIndicator U)
      (permutationOperator p (centeredIndicator U)) /
    Fintype.card M

/-- Normalized matrix coefficient of a centered characteristic vector in one
finite permutation model. -/
noncomputable def normalizedCorrelation (M : FiniteModel)
    (τ : G → Equiv.Perm M) (U : Finset M) (g : G) : ℝ :=
  normalizedPermutationCorrelation M U (τ g)

/-- Normalized Gram coefficient between two translated centered
characteristic vectors. -/
noncomputable def normalizedGramCorrelation (M : FiniteModel)
    (τ : G → Equiv.Perm M) (U : Finset M) (g h : G) : ℝ :=
  inner ℝ (permutationOperator (τ g) (centeredIndicator U))
      (permutationOperator (τ h) (centeredIndicator U)) /
    Fintype.card M

omit [Group G] in
/-- A Gram coefficient is exactly the coefficient of the relative
permutation `(τ g)⁻¹ τ h`. -/
theorem normalizedGramCorrelation_eq_relative (M : FiniteModel)
    (τ : G → Equiv.Perm M) (U : Finset M) (g h : G) :
    normalizedGramCorrelation M τ U g h =
      inner ℝ (centeredIndicator U)
          (permutationOperator ((τ g)⁻¹ * τ h) (centeredIndicator U)) /
        Fintype.card M := by
  unfold normalizedGramCorrelation
  let x := centeredIndicator U
  have hop :
      permutationOperator (τ g)
          (permutationOperator ((τ g)⁻¹ * τ h) x) =
        permutationOperator (τ h) x := by
    have hcomp := congrArg
      (fun e : EuclideanSpace ℝ M ≃ₗᵢ[ℝ] EuclideanSpace ℝ M ↦ e x)
      (permutationOperator_mul (τ g) ((τ g)⁻¹ * τ h)).symm
    simpa using hcomp
  have hinner :
    inner ℝ (permutationOperator (τ g) x) (permutationOperator (τ h) x) =
      inner ℝ x (permutationOperator ((τ g)⁻¹ * τ h) x) := by
    rw [← hop]
    exact (permutationOperator (τ g)).inner_map_map _ _
  exact congrArg (fun r : ℝ ↦ r / Fintype.card M) hinner

omit [Group G] in
/-- Every finite matrix of normalized Gram coefficients is positive
semidefinite. -/
theorem normalizedGramCorrelation_quadratic_nonneg
    {I : Type*} (F : Finset I) (c : I → ℝ)
    (M : FiniteModel) (τ : G → Equiv.Perm M) (U : Finset M)
    (a : I → G) :
    0 ≤ ∑ i ∈ F, ∑ j ∈ F,
      c i * c j * normalizedGramCorrelation M τ U (a i) (a j) := by
  classical
  by_cases hcard : Fintype.card M = 0
  · simp [normalizedGramCorrelation, hcard]
  · have hcardNat : 0 < Fintype.card M := Nat.pos_of_ne_zero hcard
    have hcardReal : (0 : ℝ) < Fintype.card M := by exact_mod_cast hcardNat
    let v : I → EuclideanSpace ℝ M := fun i ↦
      permutationOperator (τ (a i)) (centeredIndicator U)
    let z : EuclideanSpace ℝ M := ∑ i ∈ F, c i • v i
    have hz : 0 ≤ ‖z‖ ^ 2 := sq_nonneg _
    have hsum :
        (∑ i ∈ F, ∑ j ∈ F, c i * c j * inner ℝ (v i) (v j)) =
          ‖z‖ ^ 2 := by
      calc
        (∑ i ∈ F, ∑ j ∈ F, c i * c j * inner ℝ (v i) (v j)) =
            ∑ i ∈ F, inner ℝ (c i • v i) z := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [show z = ∑ j ∈ F, c j • v j by rfl, inner_sum]
          apply Finset.sum_congr rfl
          intro j hj
          rw [inner_smul_left, inner_smul_right]
          simp [mul_assoc]
        _ = inner ℝ z z := by
          rw [show z = ∑ i ∈ F, c i • v i by rfl, sum_inner]
        _ = ‖z‖ ^ 2 := real_inner_self_eq_norm_sq z
    unfold normalizedGramCorrelation
    calc
      0 ≤ ‖z‖ ^ 2 / Fintype.card M :=
        div_nonneg hz hcardReal.le
      _ = ∑ i ∈ F, ∑ j ∈ F,
          c i * c j *
            (inner ℝ (permutationOperator (τ (a i)) (centeredIndicator U))
              (permutationOperator (τ (a j)) (centeredIndicator U)) /
                Fintype.card M) := by
        rw [← hsum]
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [v]
        ring

omit [Group G] in
/-- Changing a permutation on a set of normalized Hamming size `d` changes
every normalized centered-indicator coefficient by at most `√(2d)`.  The
squared formulation avoids introducing square roots. -/
theorem abs_normalizedPermutationCorrelation_sub_sq_le
    [Nonempty M] (U : Finset M) (p q : Equiv.Perm M) :
    |normalizedPermutationCorrelation M U p -
        normalizedPermutationCorrelation M U q| ^ 2 ≤
      2 * hammingDistance M p q := by
  let x := centeredIndicator U
  let d := permutationOperator p x - permutationOperator q x
  have hcardNat : 0 < Fintype.card M := Fintype.card_pos
  have hcard : (0 : ℝ) < Fintype.card M := by exact_mod_cast hcardNat
  have hinner : |inner ℝ x d| ≤ ‖x‖ * ‖d‖ :=
    abs_real_inner_le_norm x d
  have hinnerSq : |inner ℝ x d| ^ 2 ≤ (‖x‖ * ‖d‖) ^ 2 := by
    have hright : 0 ≤ ‖x‖ * ‖d‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hleft : 0 ≤ |inner ℝ x d| := abs_nonneg _
    nlinarith
  have hx := norm_centeredIndicator_sq_div_card_le_one U
  have hd := normalized_norm_permutationOperators_centeredIndicator_sub_sq_le
    p q U
  change ‖d‖ ^ 2 / Fintype.card M ≤
      2 * hammingDistance M p q at hd
  have hquot :
      |inner ℝ x d| ^ 2 / (Fintype.card M : ℝ) ^ 2 ≤
        (‖x‖ ^ 2 / Fintype.card M) *
          (‖d‖ ^ 2 / Fintype.card M) := by
    calc
      |inner ℝ x d| ^ 2 / (Fintype.card M : ℝ) ^ 2 ≤
          (‖x‖ * ‖d‖) ^ 2 / (Fintype.card M : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hinnerSq (sq_nonneg _)
      _ = (‖x‖ ^ 2 / Fintype.card M) *
          (‖d‖ ^ 2 / Fintype.card M) := by ring
  have hproduct :
      (‖x‖ ^ 2 / Fintype.card M) *
          (‖d‖ ^ 2 / Fintype.card M) ≤
        2 * hammingDistance M p q := by
    calc
      (‖x‖ ^ 2 / Fintype.card M) *
          (‖d‖ ^ 2 / Fintype.card M) ≤
          1 * (‖d‖ ^ 2 / Fintype.card M) := by
        exact mul_le_mul_of_nonneg_right hx
          (div_nonneg (sq_nonneg _) hcard.le)
      _ ≤ 1 * (2 * hammingDistance M p q) := by
        exact mul_le_mul_of_nonneg_left hd zero_le_one
      _ = 2 * hammingDistance M p q := one_mul _
  change
    |inner ℝ x (permutationOperator p x) / Fintype.card M -
        inner ℝ x (permutationOperator q x) / Fintype.card M| ^ 2 ≤
      2 * hammingDistance M p q
  rw [← sub_div, abs_div, abs_of_pos hcard, div_pow]
  have hrewrite :
      inner ℝ x (permutationOperator p x) -
          inner ℝ x (permutationOperator q x) = inner ℝ x d := by
    simp [d, inner_sub_right]
  rw [hrewrite]
  exact hquot.trans hproduct

/-- In a sofic approximation, the coefficient assigned to `g⁻¹h`
approaches the Gram coefficient of the vectors translated by `g` and `h`.
This is the concrete bridge from approximate actions to a positive-definite
limiting function. -/
theorem sofic_relative_correlation_approaches_gram_eventually
    (A : SoficApproximation G) (U : ∀ n, Finset (A.model n))
    (g h : G) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N,
      |normalizedCorrelation (A.model n) (A.map n) (U n) (g⁻¹ * h) -
          normalizedGramCorrelation (A.model n) (A.map n) (U n) g h| < ε := by
  have hhalf : 0 < ε ^ 2 / 2 := by positivity
  obtain ⟨Nclose, hNclose⟩ :=
    sofic_inv_mul_close_eventually A g h (ε ^ 2 / 2) hhalf
  obtain ⟨Ncard, hNcard⟩ := A.card_tendsToInfinity 1
  refine ⟨max Nclose Ncard, fun n hn ↦ ?_⟩
  have hnclose : Nclose ≤ n := (le_max_left _ _).trans hn
  have hncard : Ncard ≤ n := (le_max_right _ _).trans hn
  have hcard : 0 < Fintype.card (A.model n) := by
    have := hNcard n hncard
    omega
  letI : Nonempty (A.model n) := Fintype.card_pos_iff.mp hcard
  have hclose := hNclose n hnclose
  have hsquare := abs_normalizedPermutationCorrelation_sub_sq_le
    (U n) (A.map n (g⁻¹ * h)) ((A.map n g)⁻¹ * A.map n h)
  have hsquare' :
      |normalizedCorrelation (A.model n) (A.map n) (U n) (g⁻¹ * h) -
          normalizedGramCorrelation (A.model n) (A.map n) (U n) g h| ^ 2 ≤
        2 * hammingDistance (A.model n) (A.map n (g⁻¹ * h))
          ((A.map n g)⁻¹ * A.map n h) := by
    rw [normalizedCorrelation,
      normalizedGramCorrelation_eq_relative,
      normalizedPermutationCorrelation]
    exact hsquare
  have habs :
      0 ≤ |normalizedCorrelation (A.model n) (A.map n) (U n) (g⁻¹ * h) -
          normalizedGramCorrelation (A.model n) (A.map n) (U n) g h| :=
    abs_nonneg _
  nlinarith

omit [Group G] in
/-- Every normalized centered-indicator coefficient lies in `[-1,1]`, even
for an empty finite model. -/
theorem abs_normalizedCorrelation_le_one (M : FiniteModel)
    (τ : G → Equiv.Perm M) (U : Finset M) (g : G) :
    |normalizedCorrelation M τ U g| ≤ 1 := by
  by_cases hcard : Fintype.card M = 0
  · haveI : IsEmpty M := Fintype.card_eq_zero_iff.mp hcard
    simp [normalizedCorrelation, normalizedPermutationCorrelation]
  · have hcardNat : 0 < Fintype.card M := Nat.pos_of_ne_zero hcard
    letI : Nonempty M := Fintype.card_pos_iff.mp hcardNat
    have hcardReal : (0 : ℝ) < Fintype.card M := by exact_mod_cast hcardNat
    have hinner := abs_real_inner_le_norm (centeredIndicator U)
      (permutationOperator (τ g) (centeredIndicator U))
    rw [(permutationOperator (τ g)).norm_map] at hinner
    have hnorm := norm_centeredIndicator_sq_div_card_le_one U
    rw [normalizedCorrelation, normalizedPermutationCorrelation, abs_div,
      abs_of_pos hcardReal]
    calc
      |inner ℝ (centeredIndicator U)
          (permutationOperator (τ g) (centeredIndicator U))| /
          Fintype.card M ≤
        (‖centeredIndicator U‖ * ‖centeredIndicator U‖) /
          Fintype.card M :=
        div_le_div_of_nonneg_right hinner hcardReal.le
      _ = ‖centeredIndicator U‖ ^ 2 / Fintype.card M := by ring
      _ ≤ 1 := hnorm

/-- Hyperreal matrix coefficient of a sequence of finite models. -/
noncomputable def correlationHyperreal (A : SoficApproximation G)
    (U : ∀ n, Finset (A.model n)) (g : G) : Hyperreal :=
  Hyperreal.ofSeq fun n ↦ normalizedCorrelation (A.model n) (A.map n) (U n) g

/-- The coefficient hyperreal is finite, so taking its standard part is
mathematically legitimate. -/
theorem correlationHyperreal_finite (A : SoficApproximation G)
    (U : ∀ n, Finset (A.model n)) (g : G) :
    0 ≤ ArchimedeanClass.mk (correlationHyperreal A U g) := by
  apply ArchimedeanClass.mk_nonneg_of_le_of_le_of_archimedean
    Hyperreal.coeRingHom (r := (-1 : ℝ)) (s := (1 : ℝ))
  · change Hyperreal.ofSeq (fun _ : ℕ ↦ (-1 : ℝ)) ≤
      Hyperreal.ofSeq (fun n ↦
        normalizedCorrelation (A.model n) (A.map n) (U n) g)
    rw [Hyperreal.ofSeq_le_ofSeq]
    exact Filter.Eventually.of_forall fun n ↦
      (abs_le.mp
        (abs_normalizedCorrelation_le_one (A.model n) (A.map n) (U n) g)).1
  · change Hyperreal.ofSeq (fun n ↦
        normalizedCorrelation (A.model n) (A.map n) (U n) g) ≤
      Hyperreal.ofSeq (fun _ : ℕ ↦ (1 : ℝ))
    rw [Hyperreal.ofSeq_le_ofSeq]
    exact Filter.Eventually.of_forall fun n ↦
      (abs_le.mp
        (abs_normalizedCorrelation_le_one (A.model n) (A.map n) (U n) g)).2

/-- Standard-part correlation associated to a sequence of subsets in a
sofic approximation. -/
noncomputable def limitingCorrelation (A : SoficApproximation G)
    (U : ∀ n, Finset (A.model n)) (g : G) : ℝ :=
  ArchimedeanClass.stdPart (correlationHyperreal A U g)

/-- The limiting correlation remains in the closed unit interval. -/
theorem abs_limitingCorrelation_le_one (A : SoficApproximation G)
    (U : ∀ n, Finset (A.model n)) (g : G) :
    |limitingCorrelation A U g| ≤ 1 := by
  have hfinite := correlationHyperreal_finite A U g
  have hlHyper : ((-1 : ℝ) : Hyperreal) ≤ correlationHyperreal A U g := by
    change Hyperreal.ofSeq (fun _ : ℕ ↦ (-1 : ℝ)) ≤
      Hyperreal.ofSeq (fun n ↦
        normalizedCorrelation (A.model n) (A.map n) (U n) g)
    rw [Hyperreal.ofSeq_le_ofSeq]
    exact Filter.Eventually.of_forall fun n ↦
      (abs_le.mp
        (abs_normalizedCorrelation_le_one (A.model n) (A.map n) (U n) g)).1
  have huHyper : correlationHyperreal A U g ≤ ((1 : ℝ) : Hyperreal) := by
    change Hyperreal.ofSeq (fun n ↦
        normalizedCorrelation (A.model n) (A.map n) (U n) g) ≤
      Hyperreal.ofSeq (fun _ : ℕ ↦ (1 : ℝ))
    rw [Hyperreal.ofSeq_le_ofSeq]
    exact Filter.Eventually.of_forall fun n ↦
      (abs_le.mp
        (abs_normalizedCorrelation_le_one (A.model n) (A.map n) (U n) g)).2
  apply abs_le.mpr
  exact ⟨ArchimedeanClass.le_stdPart_of_le Hyperreal.coeRingHom hfinite hlHyper,
    ArchimedeanClass.stdPart_le_of_le Hyperreal.coeRingHom hfinite huHyper⟩

end SoficNormalization

end KazhdanFiniteModel
end NonsoficGroupsExist
