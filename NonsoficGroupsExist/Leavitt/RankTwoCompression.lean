import NonsoficGroupsExist.Criterion.CriterionAssembly
import NonsoficGroupsExist.Kazhdan.KazhdanFiniteGeneration
import NonsoficGroupsExist.Criterion.Scheme
import NonsoficGroupsExist.Leavitt.ThompsonWitness
import NonsoficGroupsExist.Leavitt.ElementaryGroup
import Mathlib.Tactic.FinCases

/-!
# The rank-two compression theorem

Theorem `thm:2x2` of the manuscript: over a unital ring carrying a binary
Leavitt family, the compression--centralizer scheme already closes in rank
two, with `Γ` the full diagonal unit copy of `Aˣ`.  The compressor is
`u = !![s₀, p₁; 0, t₀]`, the involution is the two-by-two `z` block, and the
commuting non-LEF copy is the corner witness subgroup of `Aˣ`.  If `Aˣ` and
`GL₂(A) = EL₂(A)` have property `(T)`, then `GL₂(A)` is not sofic.  Finite
generation of `Aˣ` is derived from its Kazhdan pair, not assumed.
-/

namespace NonsoficGroupsExist

namespace LeavittFamily

variable {A : Type*} [Ring A] (L : LeavittFamily A)

/-! ### The diagonal unit embedding -/

/-- The diagonal unit `diag(u, 1)` of `GL₂(A)`. -/
def rankTwoDiagUnit (u : Aˣ) : (Matrix (Fin 2) (Fin 2) A)ˣ where
  val := !![(u : A), 0; 0, 1]
  inv := !![((u⁻¹ : Aˣ) : A), 0; 0, 1]
  val_inv := by
    rw [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  inv_val := by
    rw [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

@[simp] theorem rankTwoDiagUnit_val (u : Aˣ) :
    (rankTwoDiagUnit u : Matrix (Fin 2) (Fin 2) A) =
      !![(u : A), 0; 0, 1] := rfl

@[simp] theorem rankTwoDiagUnit_inv_val (u : Aˣ) :
    (((rankTwoDiagUnit u)⁻¹ : (Matrix (Fin 2) (Fin 2) A)ˣ) :
        Matrix (Fin 2) (Fin 2) A) =
      !![((u⁻¹ : Aˣ) : A), 0; 0, 1] := rfl

/-- The diagonal embedding `Aˣ →* GL₂(A)`. -/
def rankTwoDiagHom : Aˣ →* (Matrix (Fin 2) (Fin 2) A)ˣ where
  toFun := rankTwoDiagUnit
  map_one' := by
    apply Units.ext
    change !![((1 : Aˣ) : A), 0; 0, 1] = (1 : Matrix (Fin 2) (Fin 2) A)
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' u v := by
    apply Units.ext
    change !![((u * v : Aˣ) : A), 0; 0, 1] =
      !![(u : A), 0; 0, 1] * !![(v : A), 0; 0, 1]
    rw [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

@[simp] theorem rankTwoDiagHom_apply (u : Aˣ) :
    rankTwoDiagHom u = rankTwoDiagUnit u := rfl

theorem rankTwoDiagHom_injective :
    Function.Injective (rankTwoDiagHom (A := A)) := by
  intro u v huv
  apply Units.ext
  have h := congrArg
    (fun M : (Matrix (Fin 2) (Fin 2) A)ˣ ↦
      (M : Matrix (Fin 2) (Fin 2) A) 0 0) huv
  simpa using h

/-! ### The rank-two compressor and involution -/

/-- The rank-two comb compressor `!![s₀, p₁; 0, t₀]`, with its explicit
inverse. -/
def rankTwoCompressor : (Matrix (Fin 2) (Fin 2) A)ˣ where
  val := !![L.s0, L.p1; 0, L.t0]
  inv := !![L.t0, 0; L.p1, L.s0]
  val_inv := by
    have h1 : L.s0 * L.t0 + L.p1 = 1 := by
      rw [add_comm]
      exact L.p1_add_s0t0
    rw [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h1, L.t0_s0]
  inv_val := by
    rw [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [L.t0_s0]

@[simp] theorem rankTwoCompressor_val :
    (L.rankTwoCompressor : Matrix (Fin 2) (Fin 2) A) =
      !![L.s0, L.p1; 0, L.t0] := rfl

@[simp] theorem rankTwoCompressor_inv_val :
    ((L.rankTwoCompressor⁻¹ : (Matrix (Fin 2) (Fin 2) A)ˣ) :
        Matrix (Fin 2) (Fin 2) A) =
      !![L.t0, 0; L.p1, L.s0] := rfl

/-- The two-by-two involution `z` as a unit. -/
def rankTwoInvolution : (Matrix (Fin 2) (Fin 2) A)ˣ where
  val := L.z
  inv := L.z
  val_inv := L.z_sq
  inv_val := L.z_sq

@[simp] theorem rankTwoInvolution_val :
    (L.rankTwoInvolution : Matrix (Fin 2) (Fin 2) A) =
      !![L.p0, L.s1; L.t1, 0] := rfl

@[simp] theorem rankTwoInvolution_inv_val :
    ((L.rankTwoInvolution⁻¹ : (Matrix (Fin 2) (Fin 2) A)ˣ) :
        Matrix (Fin 2) (Fin 2) A) =
      !![L.p0, L.s1; L.t1, 0] := rfl

/-! ### The compression and centralizing identities -/

/-- Conjugation by the compressor sends `diag(a, 1)` to the compressed
diagonal `diag(p₁ + s₀at₀, 1)`. -/
theorem rankTwoCompressor_conj_diag (a : Aˣ) :
    L.rankTwoCompressor * rankTwoDiagHom a * L.rankTwoCompressor⁻¹ =
      rankTwoDiagHom (L.compressedHom a) := by
  apply Units.ext
  change !![L.s0, L.p1; 0, L.t0] * !![(a : A), 0; 0, 1] *
      !![L.t0, 0; L.p1, L.s0] =
    !![(L.compressedHom a : A), 0; 0, 1]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [compressedHom, compressedUnit, L.t0_s0, mul_assoc, add_comm]

/-- The involution centralizes every compressed diagonal. -/
theorem rankTwoInvolution_conj_compressed (a : Aˣ) :
    L.rankTwoInvolution * rankTwoDiagHom (L.compressedHom a) *
        L.rankTwoInvolution⁻¹ =
      rankTwoDiagHom (L.compressedHom a) := by
  apply Units.ext
  change !![L.p0, L.s1; L.t1, 0] * !![(L.compressedHom a : A), 0; 0, 1] *
      !![L.p0, L.s1; L.t1, 0] =
    !![(L.compressedHom a : A), 0; 0, 1]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [compressedHom, compressedUnit, p0, p1, mul_add,
      mul_assoc, L.t0_s1, L.t1_s1, add_comm]

/-! ### The two nilpotent diagonal units and the generation identities -/

/-- The unipotent unit `1 + p₀at₁`. -/
def rankTwoUpperNil (a : A) : Aˣ where
  val := 1 + L.p0 * a * L.t1
  inv := 1 - L.p0 * a * L.t1
  val_inv := by
    have hcore : L.t1 * (L.p0 * (a * L.t1)) = 0 := by
      rw [← mul_assoc, L.t1_mul_p0, zero_mul]
    noncomm_ring [hcore]
  inv_val := by
    have hcore : L.t1 * (L.p0 * (a * L.t1)) = 0 := by
      rw [← mul_assoc, L.t1_mul_p0, zero_mul]
    noncomm_ring [hcore]

/-- The unipotent unit `1 + s₁ap₀`. -/
def rankTwoLowerNil (a : A) : Aˣ where
  val := 1 + L.s1 * a * L.p0
  inv := 1 - L.s1 * a * L.p0
  val_inv := by
    have hcore : L.p0 * (L.s1 * (a * L.p0)) = 0 := by
      rw [← mul_assoc, L.p0_mul_s1, zero_mul]
    noncomm_ring [hcore]
  inv_val := by
    have hcore : L.p0 * (L.s1 * (a * L.p0)) = 0 := by
      rw [← mul_assoc, L.p0_mul_s1, zero_mul]
    noncomm_ring [hcore]

/-- The upper transvection written as a two-by-two literal. -/
theorem elementaryUnit_upper_val (b : A) :
    ((elementaryUnit (0 : Fin 2) 1 (by decide) b :
        (Matrix (Fin 2) (Fin 2) A)ˣ) : Matrix (Fin 2) (Fin 2) A) =
      !![1, b; 0, 1] := by
  change (1 : Matrix (Fin 2) (Fin 2) A) + Matrix.single 0 1 b = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The lower transvection written as a two-by-two literal. -/
theorem elementaryUnit_lower_val (b : A) :
    ((elementaryUnit (1 : Fin 2) 0 (by decide) b :
        (Matrix (Fin 2) (Fin 2) A)ˣ) : Matrix (Fin 2) (Fin 2) A) =
      !![1, 0; b, 1] := by
  change (1 : Matrix (Fin 2) (Fin 2) A) + Matrix.single 1 0 b = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Equation `eq:p0upper`: the involution turns the upper unipotent diagonal
into the upper transvection with coefficient `p₀a`. -/
theorem rankTwoInvolution_conj_upperNil (a : A) :
    L.rankTwoInvolution * rankTwoDiagHom (L.rankTwoUpperNil a) *
        L.rankTwoInvolution⁻¹ =
      elementaryUnit 0 1 (by decide) (L.p0 * a) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  rw [elementaryUnit_upper_val]
  change !![L.p0, L.s1; L.t1, 0] * !![1 + L.p0 * a * L.t1, 0; 0, 1] *
      !![L.p0, L.s1; L.t1, 0] = !![1, L.p0 * a; 0, 1]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [p0, mul_add, add_mul, mul_assoc,
      L.sum_range, L.t1_s1, add_comm]

/-- Equation `eq:p0lower`: the involution turns the lower unipotent diagonal
into the lower transvection with coefficient `ap₀`. -/
theorem rankTwoInvolution_conj_lowerNil (a : A) :
    L.rankTwoInvolution * rankTwoDiagHom (L.rankTwoLowerNil a) *
        L.rankTwoInvolution⁻¹ =
      elementaryUnit 1 0 (by decide) (a * L.p0) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  rw [elementaryUnit_lower_val]
  change !![L.p0, L.s1; L.t1, 0] * !![1 + L.s1 * a * L.p0, 0; 0, 1] *
      !![L.p0, L.s1; L.t1, 0] = !![1, 0; a * L.p0, 1]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [p0, mul_add, add_mul, mul_assoc,
      L.sum_range, L.t1_s1, add_comm]

/-- Conjugating an upper transvection by a diagonal unit multiplies its
coefficient on the left. -/
theorem rankTwoDiag_conj_upper (u : Aˣ) (b : A) :
    rankTwoDiagHom u * elementaryUnit 0 1 (by decide) b *
        (rankTwoDiagHom u)⁻¹ =
      elementaryUnit 0 1 (by decide) ((u : A) * b) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  rw [elementaryUnit_upper_val, elementaryUnit_upper_val]
  change !![(u : A), 0; 0, 1] * !![1, b; 0, 1] *
      !![((u⁻¹ : Aˣ) : A), 0; 0, 1] = !![1, (u : A) * b; 0, 1]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Conjugating a lower transvection by a diagonal unit multiplies its
coefficient by the inverse on the right. -/
theorem rankTwoDiag_conj_lower (u : Aˣ) (b : A) :
    rankTwoDiagHom u * elementaryUnit 1 0 (by decide) b *
        (rankTwoDiagHom u)⁻¹ =
      elementaryUnit 1 0 (by decide) (b * ((u⁻¹ : Aˣ) : A)) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  rw [elementaryUnit_lower_val, elementaryUnit_lower_val]
  change !![(u : A), 0; 0, 1] * !![1, 0; b, 1] *
      !![((u⁻¹ : Aˣ) : A), 0; 0, 1] = !![1, 0; b * ((u⁻¹ : Aˣ) : A), 1]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The corner swap moves the `p₀` upper coefficient block onto the `p₁`
block. -/
theorem cornerSwap_mul_upper_coeff (a : A) :
    (L.cornerSwap : A) * (L.p0 * (L.s0 * (L.t1 * a))) = L.p1 * a := by
  change (L.s0 * L.t1 + L.s1 * L.t0) * (L.p0 * (L.s0 * (L.t1 * a))) =
    L.p1 * a
  rw [L.p0_mul_s0_mul, add_mul]
  simp [p1, mul_assoc]

/-- The corner swap moves the `p₀` lower coefficient block onto the `p₁`
block. -/
theorem lower_coeff_mul_cornerSwap (a : A) :
    (a * (L.s1 * L.t0) * L.p0) * ((L.cornerSwap⁻¹ : Aˣ) : A) = a * L.p1 := by
  change (a * (L.s1 * L.t0) * L.p0) * (L.s0 * L.t1 + L.s1 * L.t0) = a * L.p1
  rw [mul_assoc (a * (L.s1 * L.t0)) L.p0, ← mul_assoc]
  rw [show a * (L.s1 * L.t0) * L.p0 = a * (L.s1 * L.t0) by
    rw [mul_assoc, L.s1t0_mul_p0]]
  rw [mul_assoc, mul_add, L.s1t0_mul_s0t1, L.s1t0_sq, add_zero]

/-- Every elementary transvection lies in a subgroup containing all diagonal
units and the involution. -/
theorem elementaryUnit_mem_of_diag_involution
    (S : Subgroup (Matrix (Fin 2) (Fin 2) A)ˣ)
    (hdiag : ∀ u : Aˣ, rankTwoDiagHom u ∈ S)
    (hz : L.rankTwoInvolution ∈ S) :
    ∀ (i j : Fin 2) (h : i ≠ j) (a : A), elementaryUnit i j h a ∈ S := by
  have hupper_p0 : ∀ c : A,
      elementaryUnit (0 : Fin 2) 1 (by decide) (L.p0 * c) ∈ S := by
    intro c
    rw [← L.rankTwoInvolution_conj_upperNil c]
    exact S.mul_mem (S.mul_mem hz (hdiag _)) (S.inv_mem hz)
  have hupper_p1 : ∀ c : A,
      elementaryUnit (0 : Fin 2) 1 (by decide) (L.p1 * c) ∈ S := by
    intro c
    have h2 := rankTwoDiag_conj_upper L.cornerSwap
      (L.p0 * (L.s0 * (L.t1 * c)))
    rw [L.cornerSwap_mul_upper_coeff] at h2
    rw [← h2]
    exact S.mul_mem (S.mul_mem (hdiag _) (hupper_p0 _)) (S.inv_mem (hdiag _))
  have hupper : ∀ a : A,
      elementaryUnit (0 : Fin 2) 1 (by decide) a ∈ S := by
    intro a
    have hmul := S.mul_mem (hupper_p0 a) (hupper_p1 a)
    rw [elementaryUnit_mul, show L.p0 * a + L.p1 * a = a by
      rw [← add_mul, L.p0_add_p1, one_mul]] at hmul
    exact hmul
  have hlower_p0 : ∀ c : A,
      elementaryUnit (1 : Fin 2) 0 (by decide) (c * L.p0) ∈ S := by
    intro c
    rw [← L.rankTwoInvolution_conj_lowerNil c]
    exact S.mul_mem (S.mul_mem hz (hdiag _)) (S.inv_mem hz)
  have hlower_p1 : ∀ c : A,
      elementaryUnit (1 : Fin 2) 0 (by decide) (c * L.p1) ∈ S := by
    intro c
    have h2 := rankTwoDiag_conj_lower L.cornerSwap
      (c * (L.s1 * L.t0) * L.p0)
    rw [L.lower_coeff_mul_cornerSwap] at h2
    rw [← h2]
    exact S.mul_mem (S.mul_mem (hdiag _) (hlower_p0 _)) (S.inv_mem (hdiag _))
  have hlower : ∀ a : A,
      elementaryUnit (1 : Fin 2) 0 (by decide) a ∈ S := by
    intro a
    have hmul := S.mul_mem (hlower_p0 a) (hlower_p1 a)
    rw [elementaryUnit_mul, show a * L.p0 + a * L.p1 = a by
      rw [← mul_add, L.p0_add_p1, mul_one]] at hmul
    exact hmul
  intro i j h a
  fin_cases i <;> fin_cases j
  · exact absurd rfl h
  · exact hupper a
  · exact hlower a
  · exact absurd rfl h

/-! ### The rank-two compression setup and the two-by-two theorem -/

/-- **Theorem `thm:2x2`**: over a countable nontrivial unital ring carrying a
binary Leavitt family, if `Aˣ` and the full rank-two unit group have property
`(T)` and every two-by-two invertible matrix is elementary, then `GL₂(A)` is
not sofic.  Finite generation of `Aˣ` is derived from its Kazhdan pair. -/
theorem rankTwo_not_isSofic
    (A : Type) [Ring A] [Nontrivial A] [Countable A]
    (L : LeavittFamily A)
    (hGE : elementaryGroup (Fin 2) A = ⊤)
    (hTG : HasKazhdanPropertyT.{0, 0} (Matrix (Fin 2) (Fin 2) A)ˣ)
    (hTΓ : HasKazhdanPropertyT.{0, 0} Aˣ) :
    ¬ IsSofic (Matrix (Fin 2) (Fin 2) A)ˣ := by
  classical
  haveI : Countable (Matrix (Fin 2) (Fin 2) A) :=
    Countable.of_equiv (Fin 2 → Fin 2 → A) Matrix.of
  haveI : Countable (Matrix (Fin 2) (Fin 2) A)ˣ :=
    Function.Injective.countable
      (Units.val_injective :
        Function.Injective
          (Units.val : (Matrix (Fin 2) (Fin 2) A)ˣ → Matrix (Fin 2) (Fin 2) A))
  haveI : Countable Aˣ :=
    Function.Injective.countable
      (Units.val_injective : Function.Injective (Units.val : Aˣ → A))
  obtain ⟨SΓ, hS1, hSsym, hSgen⟩ :=
    KazhdanFiniteGeneration.exists_symmetric_generating_finset Aˣ hTΓ
  haveI hJinf : Infinite L.cornerWitnessSubgroup := by
    rw [← not_finite_iff_infinite]
    intro hfin
    exact L.not_isLEF_cornerWitnessSubgroup (isLEF_of_finite _)
  haveI : Infinite Aˣ :=
    Infinite.of_injective L.cornerWitnessSubgroup.subtype
      L.cornerWitnessSubgroup.subtype_injective
  let C : CompressionSetup (Matrix (Fin 2) (Fin 2) A)ˣ Aˣ
      L.cornerWitnessSubgroup :=
    { embedΓ := rankTwoDiagHom
      embedΓ_injective := rankTwoDiagHom_injective
      embedJ := L.cornerWitnessSubgroup.subtype
      embedJ_injective := L.cornerWitnessSubgroup.subtype_injective
      generatorsΓ := SΓ
      generatorsΓ_one := hS1
      generatorsΓ_symmetric := hSsym
      generatorsΓ_generate := hSgen
      generatorsJ := L.cornerWitnessGenerators
      generatorsJ_generate := L.cornerWitnessGenerators_generate
      infiniteΓ := inferInstance
      compressors :=
        {L.rankTwoCompressor, L.rankTwoInvolution * L.rankTwoCompressor}
      distinguished := L.rankTwoCompressor
      distinguished_mem := Finset.mem_insert_self _ _
      compressedEnd := fun _ _ ↦ L.compressedHom
      compressedEnd_spec := by
        intro q hq a
        have hq' : q = L.rankTwoCompressor ∨
            q = L.rankTwoInvolution * L.rankTwoCompressor := by
          simpa using hq
        rcases hq' with rfl | rfl
        · exact (L.rankTwoCompressor_conj_diag a).symm
        · calc
            rankTwoDiagHom (L.compressedHom a) =
                L.rankTwoInvolution * rankTwoDiagHom (L.compressedHom a) *
                  L.rankTwoInvolution⁻¹ :=
              (L.rankTwoInvolution_conj_compressed a).symm
            _ = L.rankTwoInvolution *
                  (L.rankTwoCompressor * rankTwoDiagHom a *
                    L.rankTwoCompressor⁻¹) * L.rankTwoInvolution⁻¹ := by
              rw [L.rankTwoCompressor_conj_diag a]
            _ = L.rankTwoInvolution * L.rankTwoCompressor *
                  rankTwoDiagHom a *
                  (L.rankTwoInvolution * L.rankTwoCompressor)⁻¹ := by
              rw [mul_inv_rev]
              group
      generates := by
        apply top_unique
        rw [← hGE]
        rw [elementaryGroup]
        rw [Subgroup.closure_le]
        rintro _ ⟨i, j, hij, a, rfl⟩
        apply L.elementaryUnit_mem_of_diag_involution
        · intro u
          exact Subgroup.subset_closure (Or.inl ⟨u, rfl⟩)
        · have hu : L.rankTwoCompressor ∈ Subgroup.closure
              (Set.range rankTwoDiagHom ∪
                ({L.rankTwoCompressor,
                  L.rankTwoInvolution * L.rankTwoCompressor} :
                    Finset (Matrix (Fin 2) (Fin 2) A)ˣ)) :=
            Subgroup.subset_closure (Or.inr (by simp))
          have hv : L.rankTwoInvolution * L.rankTwoCompressor ∈
              Subgroup.closure
                (Set.range rankTwoDiagHom ∪
                  ({L.rankTwoCompressor,
                    L.rankTwoInvolution * L.rankTwoCompressor} :
                      Finset (Matrix (Fin 2) (Fin 2) A)ˣ)) :=
            Subgroup.subset_closure (Or.inr (by simp))
          have := mul_mem hv (inv_mem hu)
          simpa [mul_assoc] using this
      centralizes := by
        intro g j
        obtain ⟨w, hw⟩ := L.cornerWitnessSubgroup_le_cornerSubgroup j.2
        have hconj := L.rankTwoCompressor_conj_diag g
        change Commute
          (L.rankTwoCompressor * rankTwoDiagHom g * L.rankTwoCompressor⁻¹)
          (rankTwoDiagHom (j : Aˣ))
        rw [hconj, ← hw]
        change rankTwoDiagHom (L.compressedHom g) *
            rankTwoDiagHom (L.cornerHom w) =
          rankTwoDiagHom (L.cornerHom w) *
            rankTwoDiagHom (L.compressedHom g)
        rw [← map_mul, ← map_mul, L.compressedHom_commutes_cornerHom]
      disjoint := by
        intro g j hEq
        obtain ⟨w, hw⟩ := L.cornerWitnessSubgroup_le_cornerSubgroup j.2
        change L.rankTwoCompressor * rankTwoDiagHom g *
            L.rankTwoCompressor⁻¹ = rankTwoDiagHom (j : Aˣ) at hEq
        rw [L.rankTwoCompressor_conj_diag g] at hEq
        have h2 : L.compressedHom g = (j : Aˣ) :=
          rankTwoDiagHom_injective hEq
        rw [← hw] at h2
        obtain ⟨hg1, hw1⟩ := (L.compressedHom_eq_cornerHom_iff g w).1 h2
        refine ⟨hg1, ?_⟩
        apply Subtype.ext
        rw [← hw, hw1, map_one]
        rfl }
  exact not_isSofic_of_not_isLEF C hTG hTΓ L.not_isLEF_cornerWitnessSubgroup

end LeavittFamily

end NonsoficGroupsExist
