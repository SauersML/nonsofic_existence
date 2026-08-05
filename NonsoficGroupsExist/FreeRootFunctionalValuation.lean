import NonsoficGroupsExist.FreeAlgebraDegree
import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Kassabov valuations of dual functionals on degree stages

The characteristic-two Fourier development classifies the `±1` characters of
a finite degree stage by the least word degree at which they are detected.
Over an arbitrary coefficient field the characters of a stage are the
`K`-linear dual functionals, and detection means nonvanishing on a basis
word monomial.  This file defines that valuation and proves its basic
calculus: the valuation of a nonzero functional lies within the stage, the
sentinel value `n + 1` characterizes the zero functional, valuation zero is
exactly unit-coefficient detection, restriction to the previous stage
computes the valuation below the top layer, and every positive valuation
descends by exactly one along some generator-derived functional — the
leading-letter lemma.
-/

namespace NonsoficGroupsExist

namespace FreeRootFunctionalValuation

open FreeAlgebraDegree

variable (X : Type*) [Fintype X]
variable (K : Type*) [Field K]

/-- A dual functional is detected at a word degree if it is nonzero on some
basis monomial of that length inside the stage. -/
def HasDetectionAtDegree {n : ℕ}
    (φ : Module.Dual K (degreeLE X K n)) (d : ℕ) : Prop :=
  ∃ w : FreeMonoid X,
    freeWordLength X w = d ∧
    freeWordLength X w ≤ n ∧
    φ (wordMonomialInDegree X K n w) ≠ 0

/-- The least detected word degree, or `n + 1` if the functional vanishes on
all word monomials of the stage. -/
noncomputable def valuation {n : ℕ}
    (φ : Module.Dual K (degreeLE X K n)) : ℕ := by
  classical
  exact if h : ∃ d, HasDetectionAtDegree X K φ d then Nat.find h else n + 1

/-- If a detection exists, the valuation degree itself is detected. -/
theorem hasDetectionAtDegree_valuation {n : ℕ}
    (φ : Module.Dual K (degreeLE X K n))
    (h : ∃ d, HasDetectionAtDegree X K φ d) :
    HasDetectionAtDegree X K φ (valuation X K φ) := by
  classical
  unfold valuation
  split
  · exact Nat.find_spec _
  · contradiction

/-- The valuation is no larger than any detected degree. -/
theorem valuation_le_of_hasDetection {n : ℕ}
    (φ : Module.Dual K (degreeLE X K n))
    {d : ℕ} (hd : HasDetectionAtDegree X K φ d) :
    valuation X K φ ≤ d := by
  classical
  unfold valuation
  split
  · exact Nat.find_min' _ hd
  · rename_i hnone
    exact absurd (⟨d, hd⟩ : ∃ e, HasDetectionAtDegree X K φ e) hnone

/-- With no detected word, the valuation is the sentinel `n + 1`. -/
theorem valuation_eq_succ_of_not_exists {n : ℕ}
    (φ : Module.Dual K (degreeLE X K n))
    (h : ¬ ∃ d, HasDetectionAtDegree X K φ d) :
    valuation X K φ = n + 1 := by
  classical
  simp [valuation, h]

/-- Detected degrees below the valuation do not exist. -/
theorem not_hasDetection_of_lt_valuation {n : ℕ}
    (φ : Module.Dual K (degreeLE X K n))
    {d : ℕ} (hd : d < valuation X K φ) :
    ¬ HasDetectionAtDegree X K φ d := by
  intro hdet
  exact absurd (valuation_le_of_hasDetection X K φ hdet) (by omega)

/-- Every detected functional has valuation at most the stage. -/
theorem valuation_le_stage_of_exists {n : ℕ}
    (φ : Module.Dual K (degreeLE X K n))
    (h : ∃ d, HasDetectionAtDegree X K φ d) :
    valuation X K φ ≤ n := by
  obtain ⟨d, hd⟩ := h
  obtain ⟨w, hwd, hwn, hφ⟩ := hd
  exact (valuation_le_of_hasDetection X K φ ⟨w, hwd, hwn, hφ⟩).trans
    (hwd ▸ hwn)

/-- Every valuation is bounded by the stage sentinel. -/
theorem valuation_le_succ {n : ℕ}
    (φ : Module.Dual K (degreeLE X K n)) :
    valuation X K φ ≤ n + 1 := by
  by_cases h : ∃ d, HasDetectionAtDegree X K φ d
  · exact (valuation_le_stage_of_exists X K φ h).trans (Nat.le_succ n)
  · rw [valuation_eq_succ_of_not_exists X K φ h]

/-- A functional nonvanishing anywhere is detected on a supported basis
monomial, so its valuation lies within the stage. -/
theorem valuation_le_stage_of_ne_zero {n : ℕ}
    {φ : Module.Dual K (degreeLE X K n)} (hφ : φ ≠ 0) :
    valuation X K φ ≤ n := by
  classical
  obtain ⟨p, hp⟩ : ∃ p : degreeLE X K n, φ p ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hφ (LinearMap.ext fun p ↦ by rw [hall p, LinearMap.zero_apply])
  have hexpand := eq_sum_support_smul_degreeWordMonomial X K p
  have hφp := hp
  rw [hexpand, map_sum] at hφp
  obtain ⟨w, -, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero hφp
  rw [map_smul] at hw
  have hmono : φ (⟨wordMonomial X K w.1, wordMonomial_mem_degreeLE X K
      (((mem_degreeLE_iff X K p.1 n).1 p.2) w.1 w.2)⟩ :
        degreeLE X K n) ≠ 0 := by
    intro h0
    rw [h0] at hw
    simp at hw
  have hwn : freeWordLength X w.1 ≤ n :=
    ((mem_degreeLE_iff X K p.1 n).1 p.2) w.1 w.2
  apply valuation_le_stage_of_exists X K φ
  refine ⟨freeWordLength X w.1, w.1, rfl, hwn, ?_⟩
  rw [wordMonomialInDegree_of_le X K w.1 hwn]
  exact hmono

/-- The sentinel valuation characterizes the zero functional. -/
theorem valuation_eq_succ_iff {n : ℕ}
    (φ : Module.Dual K (degreeLE X K n)) :
    valuation X K φ = n + 1 ↔ φ = 0 := by
  constructor
  · intro hval
    by_contra hφ
    have := valuation_le_stage_of_ne_zero X K hφ
    omega
  · intro hφ
    apply valuation_eq_succ_of_not_exists
    rintro ⟨d, w, -, -, hw⟩
    rw [hφ] at hw
    simp at hw

/-- Valuation zero is exactly detection on the empty word. -/
theorem valuation_eq_zero_iff {n : ℕ}
    (φ : Module.Dual K (degreeLE X K n)) :
    valuation X K φ = 0 ↔
      φ (wordMonomialInDegree X K n 1) ≠ 0 := by
  constructor
  · intro hval
    have hExists : ∃ d, HasDetectionAtDegree X K φ d := by
      by_contra hnone
      have := valuation_eq_succ_of_not_exists X K φ hnone
      omega
    obtain ⟨w, hwd, hwn, hφ⟩ :=
      hval ▸ hasDetectionAtDegree_valuation X K φ hExists
    rwa [show w = 1 from (freeWordLength_eq_zero_iff X w).1 hwd] at hφ
  · intro hφ
    have hdet : HasDetectionAtDegree X K φ 0 :=
      ⟨1, (freeWordLength_eq_zero_iff X 1).2 rfl,
        by rw [(freeWordLength_eq_zero_iff X 1).2 rfl]; omega, hφ⟩
    have := valuation_le_of_hasDetection X K φ hdet
    omega

/-! ### Positive control -/

/-- The unit-coefficient functional: the coefficient of the empty word. -/
noncomputable def unitCoefficient (n : ℕ) :
    Module.Dual K (degreeLE X K n) :=
  (Finsupp.lapply (1 : FreeMonoid X)).comp
    ((MonoidAlgebra.coeffLinearEquiv K).toLinearMap.comp
      ((FreeAlgebra.equivMonoidAlgebraFreeMonoid
        (R := K) (X := X)).toLinearMap.comp (degreeLE X K n).subtype))

theorem unitCoefficient_wordMonomialInDegree_one (n : ℕ) :
    unitCoefficient X K n (wordMonomialInDegree X K n 1) = 1 := by
  unfold unitCoefficient
  simp only [LinearMap.comp_apply, Submodule.subtype_apply,
    wordMonomialInDegree_one_val]
  change ((FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := K) (X := X))
      (1 : FreeAlgebra K X)).coeff 1 = 1
  rw [map_one (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := K) (X := X))]
  change (1 : MonoidAlgebra K (FreeMonoid X)).coeff 1 = 1
  rw [MonoidAlgebra.one_def]
  exact Finsupp.single_eq_same

/-- **Positive control**: the unit-coefficient functional genuinely detects
the empty word, so the detection predicate is satisfiable at every stage. -/
theorem hasDetectionAtDegree_unitCoefficient (n : ℕ) :
    HasDetectionAtDegree X K (unitCoefficient X K n) 0 :=
  ⟨1, (freeWordLength_eq_zero_iff X 1).2 rfl,
    by rw [(freeWordLength_eq_zero_iff X 1).2 rfl]; omega,
    by rw [unitCoefficient_wordMonomialInDegree_one]; exact one_ne_zero⟩

/-! ### Stage restriction -/

/-- The inclusion of a degree stage into the next stage, as a linear map. -/
noncomputable def stageInclusion (n : ℕ) :
    degreeLE X K n →ₗ[K] degreeLE X K (n + 1) :=
  Submodule.inclusion (degreeLE_mono X K (Nat.le_succ n))

@[simp] theorem stageInclusion_apply (n : ℕ) (a : degreeLE X K n) :
    ((stageInclusion X K n a : degreeLE X K (n + 1)) : FreeAlgebra K X) =
      (a : FreeAlgebra K X) := rfl

/-- Restriction of a next-stage functional to the current stage. -/
noncomputable def restrictSucc {n : ℕ}
    (φ : Module.Dual K (degreeLE X K (n + 1))) :
    Module.Dual K (degreeLE X K n) :=
  φ.comp (stageInclusion X K n)

/-- The inclusion carries stage-`n` basis monomials to stage-`n+1` basis
monomials. -/
theorem stageInclusion_wordMonomialInDegree {n : ℕ} (w : FreeMonoid X)
    (hw : freeWordLength X w ≤ n) :
    stageInclusion X K n (wordMonomialInDegree X K n w) =
      wordMonomialInDegree X K (n + 1) w := by
  apply Subtype.ext
  rw [stageInclusion_apply,
    wordMonomialInDegree_of_le X K w hw,
    wordMonomialInDegree_of_le X K w (hw.trans (Nat.le_succ n))]

/-- Detections below the stage boundary transfer to the restriction. -/
theorem hasDetection_restrictSucc_of_hasDetection {n : ℕ}
    (φ : Module.Dual K (degreeLE X K (n + 1))) {d : ℕ} (hdn : d ≤ n)
    (hd : HasDetectionAtDegree X K φ d) :
    HasDetectionAtDegree X K (restrictSucc X K φ) d := by
  obtain ⟨w, hwd, hwn, hφ⟩ := hd
  refine ⟨w, hwd, hwd ▸ hdn, ?_⟩
  rw [restrictSucc, LinearMap.comp_apply,
    stageInclusion_wordMonomialInDegree X K w (hwd ▸ hdn)]
  exact hφ

/-- Detections of the restriction come from detections of the original. -/
theorem hasDetection_of_hasDetection_restrictSucc {n : ℕ}
    (φ : Module.Dual K (degreeLE X K (n + 1))) {d : ℕ}
    (hd : HasDetectionAtDegree X K (restrictSucc X K φ) d) :
    HasDetectionAtDegree X K φ d := by
  obtain ⟨w, hwd, hwn, hφ⟩ := hd
  refine ⟨w, hwd, hwn.trans (Nat.le_succ n), ?_⟩
  rwa [restrictSucc, LinearMap.comp_apply,
    stageInclusion_wordMonomialInDegree X K w hwn] at hφ

/-- Below the top layer, restriction computes the valuation exactly. -/
theorem valuation_restrictSucc_eq {n : ℕ}
    (φ : Module.Dual K (degreeLE X K (n + 1)))
    (hval : valuation X K φ ≤ n) :
    valuation X K (restrictSucc X K φ) = valuation X K φ := by
  have hExists : ∃ d, HasDetectionAtDegree X K φ d := by
    by_contra hnone
    have := valuation_eq_succ_of_not_exists X K φ hnone
    omega
  have hdet := hasDetectionAtDegree_valuation X K φ hExists
  have hdet' := hasDetection_restrictSucc_of_hasDetection X K φ hval hdet
  apply le_antisymm
  · exact valuation_le_of_hasDetection X K _ hdet'
  · by_contra hlt
    push Not at hlt
    obtain ⟨w, hwd, hwn, hφ⟩ :=
      hasDetectionAtDegree_valuation X K (restrictSucc X K φ)
        ⟨_, hdet'⟩
    exact not_hasDetection_of_lt_valuation X K φ
      (by omega : valuation X K (restrictSucc X K φ) < valuation X K φ)
      (hasDetection_of_hasDetection_restrictSucc X K φ ⟨w, hwd, hwn, hφ⟩)

/-! ### The leading-letter descent -/

/-- Left multiplication by a free generator, as a linear map into the next
stage. -/
noncomputable def generatorMulLinear (n : ℕ) (x : X) :
    degreeLE X K n →ₗ[K] degreeLE X K (n + 1) where
  toFun a := ⟨FreeAlgebra.ι K x * (a : FreeAlgebra K X),
    generator_mul_mem_degreeLE_succ X K x a.2⟩
  map_add' a b := by
    apply Subtype.ext
    change FreeAlgebra.ι K x * ((a : FreeAlgebra K X) + b) = _
    rw [mul_add]
    rfl
  map_smul' c a := by
    apply Subtype.ext
    change FreeAlgebra.ι K x * (c • (a : FreeAlgebra K X)) = _
    rw [mul_smul_comm]
    rfl

/-- The generator-derived functional of the leading-letter analysis. -/
noncomputable def leftDerived {n : ℕ}
    (φ : Module.Dual K (degreeLE X K (n + 1))) (x : X) :
    Module.Dual K (degreeLE X K n) :=
  φ.comp (generatorMulLinear X K n x)

/-- Generator multiplication carries a stage-`n` basis monomial to the
basis monomial of the extended word. -/
theorem generatorMulLinear_wordMonomialInDegree {n : ℕ} (x : X)
    (w : FreeMonoid X) (hw : freeWordLength X w ≤ n) :
    generatorMulLinear X K n x (wordMonomialInDegree X K n w) =
      wordMonomialInDegree X K (n + 1) (FreeMonoid.of x * w) := by
  have hlen : freeWordLength X (FreeMonoid.of x * w) =
      freeWordLength X w + 1 := by
    rw [freeWordLength_mul, freeWordLength_of]
    omega
  apply Subtype.ext
  change FreeAlgebra.ι K x *
      ((wordMonomialInDegree X K n w : degreeLE X K n) : FreeAlgebra K X) =
    ((wordMonomialInDegree X K (n + 1) (FreeMonoid.of x * w) :
        degreeLE X K (n + 1)) : FreeAlgebra K X)
  rw [wordMonomialInDegree_of_le X K w hw,
    wordMonomialInDegree_of_le X K (FreeMonoid.of x * w)
      (by omega : freeWordLength X (FreeMonoid.of x * w) ≤ n + 1)]
  change FreeAlgebra.ι K x * wordMonomial X K w = _
  rw [← wordMonomial_of X K x, wordMonomial_mul]

/-- Detections of the derived functional extend the word by the leading
letter. -/
theorem hasDetection_of_hasDetection_leftDerived {n : ℕ}
    (φ : Module.Dual K (degreeLE X K (n + 1))) (x : X) {d : ℕ}
    (hd : HasDetectionAtDegree X K (leftDerived X K φ x) d) :
    HasDetectionAtDegree X K φ (d + 1) := by
  obtain ⟨w, hwd, hwn, hφ⟩ := hd
  refine ⟨FreeMonoid.of x * w, ?_, ?_, ?_⟩
  · rw [freeWordLength_mul, freeWordLength_of]
    omega
  · rw [freeWordLength_mul, freeWordLength_of]
    omega
  · rwa [leftDerived, LinearMap.comp_apply,
      generatorMulLinear_wordMonomialInDegree X K x w hwn] at hφ

/-- **The leading-letter lemma**: a positive detected valuation descends by
exactly one along the generator-derived functional of the leading letter of
any witnessing word. -/
theorem exists_leftDerived_valuation_succ {n : ℕ}
    (φ : Module.Dual K (degreeLE X K (n + 1))) {d : ℕ}
    (hval : valuation X K φ = d + 1) (hd : d + 1 ≤ n + 1) :
    ∃ x : X, valuation X K (leftDerived X K φ x) = d := by
  have hExists : ∃ e, HasDetectionAtDegree X K φ e := by
    by_contra hnone
    have := valuation_eq_succ_of_not_exists X K φ hnone
    omega
  obtain ⟨w, hwd, hwn, hφ⟩ :=
    hval ▸ hasDetectionAtDegree_valuation X K φ hExists
  have hpos : 0 < freeWordLength X w := by omega
  obtain ⟨x, v, hword, hmono⟩ :=
    wordMonomial_eq_generator_mul_of_freeWordLength_pos X K w hpos
  have hvlen : freeWordLength X v + 1 = freeWordLength X w := by
    have := freeWordLength_mul X (FreeMonoid.of x) v
    rw [← hword] at this
    rw [this, freeWordLength_of]
    omega
  refine ⟨x, le_antisymm ?_ ?_⟩
  · apply valuation_le_of_hasDetection
    refine ⟨v, by omega, by omega, ?_⟩
    rw [leftDerived, LinearMap.comp_apply,
      generatorMulLinear_wordMonomialInDegree X K x v (by omega),
      show FreeMonoid.of x * v = w from hword.symm]
    exact hφ
  · by_contra hlt
    push Not at hlt
    have hdet' := hasDetectionAtDegree_valuation X K
      (leftDerived X K φ x)
      (by
        by_contra hnone
        have := valuation_eq_succ_of_not_exists X K _ hnone
        omega)
    have := hasDetection_of_hasDetection_leftDerived X K φ x hdet'
    exact not_hasDetection_of_lt_valuation X K φ
      (by omega : valuation X K (leftDerived X K φ x) + 1 <
        valuation X K φ) this

end FreeRootFunctionalValuation

end NonsoficGroupsExist
