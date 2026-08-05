import NonsoficGroupsExist.FreeAlgebraDegree
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Tactic.DeriveFintype

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

/-- Below its valuation, a functional vanishes on every stage basis
monomial. -/
theorem apply_wordMonomialInDegree_eq_zero_of_lt {n : ℕ}
    (φ : Module.Dual K (degreeLE X K n)) {w : FreeMonoid X}
    (hw : freeWordLength X w ≤ n)
    (hlt : freeWordLength X w < valuation X K φ) :
    φ (wordMonomialInDegree X K n w) = 0 := by
  by_contra hne
  exact not_hasDetection_of_lt_valuation X K φ hlt ⟨w, rfl, hw, hne⟩

/-- Negation preserves the valuation. -/
theorem valuation_neg {n : ℕ} (φ : Module.Dual K (degreeLE X K n)) :
    valuation X K (-φ) = valuation X K φ := by
  have h : ∀ ξ : Module.Dual K (degreeLE X K n), ∀ d : ℕ,
      HasDetectionAtDegree X K ξ d → HasDetectionAtDegree X K (-ξ) d := by
    rintro ξ d ⟨w, hwd, hwn, hξ⟩
    refine ⟨w, hwd, hwn, ?_⟩
    rw [LinearMap.neg_apply]
    exact neg_ne_zero.2 hξ
  have hle : ∀ ξ : Module.Dual K (degreeLE X K n),
      valuation X K (-ξ) ≤ valuation X K ξ := by
    intro ξ
    by_cases hξ : ∃ d, HasDetectionAtDegree X K ξ d
    · exact valuation_le_of_hasDetection X K (-ξ)
        (h ξ _ (hasDetectionAtDegree_valuation X K ξ hξ))
    · rw [valuation_eq_succ_of_not_exists X K ξ hξ]
      exact valuation_le_succ X K (-ξ)
  have h1 := hle φ
  have h2 := hle (-φ)
  rw [neg_neg] at h2
  omega

/-- **The min rule**: adding a functional of strictly larger valuation does
not change the valuation. -/
theorem valuation_add_of_lt {n : ℕ}
    (φ ξ : Module.Dual K (degreeLE X K n))
    (h : valuation X K φ < valuation X K ξ) :
    valuation X K (φ + ξ) = valuation X K φ := by
  have hφdet : ∃ d, HasDetectionAtDegree X K φ d := by
    by_contra hnone
    have h1 := valuation_eq_succ_of_not_exists X K φ hnone
    have h2 := valuation_le_succ X K ξ
    omega
  obtain ⟨w, hwd, hwn, hφw⟩ := hasDetectionAtDegree_valuation X K φ hφdet
  have hξw : ξ (wordMonomialInDegree X K n w) = 0 :=
    apply_wordMonomialInDegree_eq_zero_of_lt X K ξ hwn (by omega)
  have hdet : HasDetectionAtDegree X K (φ + ξ) (valuation X K φ) := by
    refine ⟨w, hwd, hwn, ?_⟩
    rw [LinearMap.add_apply, hξw, add_zero]
    exact hφw
  apply le_antisymm
  · exact valuation_le_of_hasDetection X K (φ + ξ) hdet
  · by_contra hlt
    push Not at hlt
    obtain ⟨u, hud, hun, hsum⟩ :=
      hasDetectionAtDegree_valuation X K (φ + ξ) ⟨_, hdet⟩
    have hφu : φ (wordMonomialInDegree X K n u) = 0 :=
      apply_wordMonomialInDegree_eq_zero_of_lt X K φ hun (by omega)
    have hξu : ξ (wordMonomialInDegree X K n u) = 0 :=
      apply_wordMonomialInDegree_eq_zero_of_lt X K ξ hun (by omega)
    rw [LinearMap.add_apply, hφu, hξu, add_zero] at hsum
    exact hsum rfl

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

/-- Restriction computes the valuation as a minimum with the stage
sentinel. -/
theorem valuation_restrictSucc_eq_min {n : ℕ}
    (φ : Module.Dual K (degreeLE X K (n + 1))) :
    valuation X K (restrictSucc X K φ) =
      min (valuation X K φ) (n + 1) := by
  by_cases hle : valuation X K φ ≤ n
  · rw [valuation_restrictSucc_eq X K φ hle]
    omega
  · have hnone : ¬ ∃ d, HasDetectionAtDegree X K (restrictSucc X K φ) d := by
      rintro ⟨d, hd⟩
      have hdn : d ≤ n := by
        obtain ⟨w, hwd, hwn, -⟩ := hd
        omega
      have := valuation_le_of_hasDetection X K φ
        (hasDetection_of_hasDetection_restrictSucc X K φ hd)
      omega
    rw [valuation_eq_succ_of_not_exists X K _ hnone]
    omega

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

/-- The derived functional commutes with stage restriction. -/
theorem leftDerived_restrictSucc {n : ℕ}
    (φ : Module.Dual K (degreeLE X K (n + 2))) (x : X) :
    leftDerived X K (restrictSucc X K φ) x =
      restrictSucc X K (leftDerived X K φ x) := by
  refine LinearMap.ext fun a ↦ ?_
  rfl

/-- Descent in the sentinel-free additive form. -/
theorem exists_leftDerived_valuation_add_one {n : ℕ}
    (φ : Module.Dual K (degreeLE X K (n + 1)))
    (hExists : ∃ d, HasDetectionAtDegree X K φ d)
    (hpos : 0 < valuation X K φ) :
    ∃ x : X,
      valuation X K (leftDerived X K φ x) + 1 = valuation X K φ := by
  have hle := valuation_le_stage_of_exists X K φ hExists
  obtain ⟨x, hx⟩ := exists_leftDerived_valuation_succ X K φ
    (show valuation X K φ = (valuation X K φ - 1) + 1 by omega)
    (by omega)
  exact ⟨x, by omega⟩

/-! ### The canonical leading-generator selector -/

/-- A fixed exhaustive enumeration of the finite free-generator alphabet. -/
noncomputable def generatorEnumeration : Fin (Fintype.card X) ≃ X :=
  (Fintype.equivFin X).symm

/-- All generator indices realizing the exact one-step valuation descent. -/
noncomputable def leadingGeneratorIndexSet {n : ℕ}
    (φ : Module.Dual K (degreeLE X K (n + 1))) :
    Finset (Fin (Fintype.card X)) :=
  Finset.univ.filter fun q ↦
    valuation X K (leftDerived X K φ (generatorEnumeration X q)) + 1 =
      valuation X K φ

theorem mem_leadingGeneratorIndexSet_iff {n : ℕ}
    (φ : Module.Dual K (degreeLE X K (n + 1)))
    (q : Fin (Fintype.card X)) :
    q ∈ leadingGeneratorIndexSet X K φ ↔
      valuation X K (leftDerived X K φ (generatorEnumeration X q)) + 1 =
        valuation X K φ := by
  simp [leadingGeneratorIndexSet]

/-- Away from the top-degree boundary, restriction preserves exactly the
set of generators realizing leading-term valuation descent. -/
theorem mem_leadingGeneratorIndexSet_restrictSucc_iff {n : ℕ}
    (φ : Module.Dual K (degreeLE X K (n + 2)))
    (hle : valuation X K φ ≤ n + 1)
    (q : Fin (Fintype.card X)) :
    q ∈ leadingGeneratorIndexSet X K (restrictSucc X K φ) ↔
      q ∈ leadingGeneratorIndexSet X K φ := by
  rw [mem_leadingGeneratorIndexSet_iff, mem_leadingGeneratorIndexSet_iff]
  have hφ : valuation X K (restrictSucc X K φ) = valuation X K φ :=
    valuation_restrictSucc_eq X K φ hle
  rw [hφ, leftDerived_restrictSucc X K φ (generatorEnumeration X q),
    valuation_restrictSucc_eq_min X K
      (leftDerived X K φ (generatorEnumeration X q))]
  constructor
  · intro h
    have := valuation_le_succ X K
      (leftDerived X K φ (generatorEnumeration X q))
    omega
  · intro h
    omega

theorem leadingGeneratorIndexSet_restrictSucc {n : ℕ}
    (φ : Module.Dual K (degreeLE X K (n + 2)))
    (hle : valuation X K φ ≤ n + 1) :
    leadingGeneratorIndexSet X K (restrictSucc X K φ) =
      leadingGeneratorIndexSet X K φ := by
  ext q
  exact mem_leadingGeneratorIndexSet_restrictSucc_iff X K φ hle q

/-- Positive detected valuation makes the leading-generator index set
nonempty. -/
theorem leadingGeneratorIndexSet_nonempty {n : ℕ}
    (φ : Module.Dual K (degreeLE X K (n + 1)))
    (hExists : ∃ d, HasDetectionAtDegree X K φ d)
    (hpos : 0 < valuation X K φ) :
    (leadingGeneratorIndexSet X K φ).Nonempty := by
  obtain ⟨x, hx⟩ :=
    exists_leftDerived_valuation_add_one X K φ hExists hpos
  refine ⟨(generatorEnumeration X).symm x, ?_⟩
  rw [mem_leadingGeneratorIndexSet_iff]
  simpa using hx

/-- The least enumerated leading generator, with `card X` as a total
sentinel when no generator realizes valuation descent. -/
noncomputable def leastLeadingGeneratorIndex {n : ℕ}
    (φ : Module.Dual K (degreeLE X K (n + 1))) : ℕ :=
  if h : (leadingGeneratorIndexSet X K φ).Nonempty then
    ((leadingGeneratorIndexSet X K φ).min' h).val
  else
    Fintype.card X

theorem leastLeadingGeneratorIndex_lt_card {n : ℕ}
    (φ : Module.Dual K (degreeLE X K (n + 1)))
    (h : (leadingGeneratorIndexSet X K φ).Nonempty) :
    leastLeadingGeneratorIndex X K φ < Fintype.card X := by
  rw [leastLeadingGeneratorIndex, dif_pos h]
  exact ((leadingGeneratorIndexSet X K φ).min' h).isLt

/-- The total least-index selector genuinely realizes valuation descent
whenever the leading-generator set is nonempty. -/
theorem leastLeadingGeneratorIndex_spec {n : ℕ}
    (φ : Module.Dual K (degreeLE X K (n + 1)))
    (h : (leadingGeneratorIndexSet X K φ).Nonempty) :
    valuation X K
        (leftDerived X K φ
          (generatorEnumeration X
            ⟨leastLeadingGeneratorIndex X K φ,
              leastLeadingGeneratorIndex_lt_card X K φ h⟩)) + 1 =
      valuation X K φ := by
  have hmem := Finset.min'_mem (leadingGeneratorIndexSet X K φ) h
  rw [mem_leadingGeneratorIndexSet_iff] at hmem
  simpa [leastLeadingGeneratorIndex, h] using hmem

/-- Below the top-degree boundary, the canonical least leading generator is
unchanged by restriction to the preceding stage. -/
theorem leastLeadingGeneratorIndex_restrictSucc {n : ℕ}
    (φ : Module.Dual K (degreeLE X K (n + 2)))
    (hle : valuation X K φ ≤ n + 1) :
    leastLeadingGeneratorIndex X K (restrictSucc X K φ) =
      leastLeadingGeneratorIndex X K φ := by
  unfold leastLeadingGeneratorIndex
  rw [leadingGeneratorIndexSet_restrictSucc X K φ hle]

/-! ### The valuation regions -/

/-- Kassabov's four nonzero valuation regions, together with the
all-trivial pair.  Keeping `zero` separate is essential: the argument
partitions the complement of `(0, 0)`, and the invariant Fourier component
must never be charged to region `B`. -/
inductive ValuationRegion
  | zero | A | B | C | D
  deriving DecidableEq, Fintype

/-- Classify an arbitrary pair of finite-stage dual functionals. -/
noncomputable def pairRegion {n : ℕ}
    (φ χ : Module.Dual K (degreeLE X K n)) : ValuationRegion :=
  let a := valuation X K φ
  let b := valuation X K χ
  if a = n + 1 ∧ b = n + 1 then .zero
  else if a = 0 ∨ b = 0 then .D
  else if b < a then .A
  else if a = b then .B
  else .C

theorem pairRegion_eq_zero_iff {n : ℕ}
    (φ χ : Module.Dual K (degreeLE X K n)) :
    pairRegion X K φ χ = .zero ↔
      valuation X K φ = n + 1 ∧ valuation X K χ = n + 1 := by
  constructor
  · intro h
    by_cases hz : valuation X K φ = n + 1 ∧ valuation X K χ = n + 1
    · exact hz
    · exfalso
      rw [pairRegion, if_neg hz] at h
      by_cases hd : valuation X K φ = 0 ∨ valuation X K χ = 0
      · rw [if_pos hd] at h
        cases h
      · rw [if_neg hd] at h
        by_cases hba : valuation X K χ < valuation X K φ
        · rw [if_pos hba] at h
          cases h
        · rw [if_neg hba] at h
          by_cases heq : valuation X K φ = valuation X K χ
          · rw [if_pos heq] at h
            cases h
          · rw [if_neg heq] at h
            cases h
  · intro h
    simp [pairRegion, h]

/-- Exact numerical data carried by membership in region `A`. -/
theorem pairRegion_A_data {n : ℕ}
    (φ χ : Module.Dual K (degreeLE X K n))
    (h : pairRegion X K φ χ = .A) :
      ¬(valuation X K φ = n + 1 ∧ valuation X K χ = n + 1) ∧
      valuation X K φ ≠ 0 ∧ valuation X K χ ≠ 0 ∧
      valuation X K χ < valuation X K φ := by
  by_cases hz : valuation X K φ = n + 1 ∧ valuation X K χ = n + 1
  · rw [pairRegion, if_pos hz] at h
    cases h
  · by_cases hd : valuation X K φ = 0 ∨ valuation X K χ = 0
    · rw [pairRegion, if_neg hz, if_pos hd] at h
      cases h
    · by_cases hba : valuation X K χ < valuation X K φ
      · exact ⟨hz, (not_or.mp hd).1, (not_or.mp hd).2, hba⟩
      · by_cases heq : valuation X K φ = valuation X K χ
        · rw [pairRegion, if_neg hz, if_neg hd, if_neg hba,
            if_pos heq] at h
          cases h
        · rw [pairRegion, if_neg hz, if_neg hd, if_neg hba,
            if_neg heq] at h
          cases h

/-- Exact numerical data carried by membership in region `B`. -/
theorem pairRegion_B_data {n : ℕ}
    (φ χ : Module.Dual K (degreeLE X K n))
    (h : pairRegion X K φ χ = .B) :
      ¬(valuation X K φ = n + 1 ∧ valuation X K χ = n + 1) ∧
      valuation X K φ ≠ 0 ∧ valuation X K χ ≠ 0 ∧
      valuation X K φ = valuation X K χ := by
  by_cases hz : valuation X K φ = n + 1 ∧ valuation X K χ = n + 1
  · rw [pairRegion, if_pos hz] at h
    cases h
  · by_cases hd : valuation X K φ = 0 ∨ valuation X K χ = 0
    · rw [pairRegion, if_neg hz, if_pos hd] at h
      cases h
    · by_cases hba : valuation X K χ < valuation X K φ
      · rw [pairRegion, if_neg hz, if_neg hd, if_pos hba] at h
        cases h
      · by_cases heq : valuation X K φ = valuation X K χ
        · exact ⟨hz, (not_or.mp hd).1, (not_or.mp hd).2, heq⟩
        · rw [pairRegion, if_neg hz, if_neg hd, if_neg hba,
            if_neg heq] at h
          cases h

/-- Exact numerical data carried by membership in region `C`. -/
theorem pairRegion_C_data {n : ℕ}
    (φ χ : Module.Dual K (degreeLE X K n))
    (h : pairRegion X K φ χ = .C) :
      ¬(valuation X K φ = n + 1 ∧ valuation X K χ = n + 1) ∧
      valuation X K φ ≠ 0 ∧ valuation X K χ ≠ 0 ∧
      valuation X K φ < valuation X K χ := by
  by_cases hz : valuation X K φ = n + 1 ∧ valuation X K χ = n + 1
  · rw [pairRegion, if_pos hz] at h
    cases h
  · by_cases hd : valuation X K φ = 0 ∨ valuation X K χ = 0
    · rw [pairRegion, if_neg hz, if_pos hd] at h
      cases h
    · by_cases hba : valuation X K χ < valuation X K φ
      · rw [pairRegion, if_neg hz, if_neg hd, if_pos hba] at h
        cases h
      · by_cases heq : valuation X K φ = valuation X K χ
        · rw [pairRegion, if_neg hz, if_neg hd, if_neg hba,
            if_pos heq] at h
          cases h
        · refine ⟨hz, (not_or.mp hd).1, (not_or.mp hd).2, ?_⟩
          omega

/-- Exact zero-coordinate alternative carried by membership in region
`D`. -/
theorem pairRegion_D_data {n : ℕ}
    (φ χ : Module.Dual K (degreeLE X K n))
    (h : pairRegion X K φ χ = .D) :
    valuation X K φ = 0 ∨ valuation X K χ = 0 := by
  by_cases hz : valuation X K φ = n + 1 ∧ valuation X K χ = n + 1
  · rw [pairRegion, if_pos hz] at h
    cases h
  · by_cases hd : valuation X K φ = 0 ∨ valuation X K χ = 0
    · exact hd
    · by_cases hba : valuation X K χ < valuation X K φ
      · rw [pairRegion, if_neg hz, if_neg hd, if_pos hba] at h
        cases h
      · by_cases heq : valuation X K φ = valuation X K χ
        · rw [pairRegion, if_neg hz, if_neg hd, if_neg hba,
            if_pos heq] at h
          cases h
        · rw [pairRegion, if_neg hz, if_neg hd, if_neg hba,
            if_neg heq] at h
          cases h

theorem pairRegion_eq_A_of_pos_of_lt {n : ℕ}
    (φ χ : Module.Dual K (degreeLE X K n))
    (hχ : 0 < valuation X K χ)
    (hlt : valuation X K χ < valuation X K φ) :
    pairRegion X K φ χ = .A := by
  have hz : ¬(valuation X K φ = n + 1 ∧ valuation X K χ = n + 1) := by
    omega
  have hd : ¬(valuation X K φ = 0 ∨ valuation X K χ = 0) := by omega
  rw [pairRegion, if_neg hz, if_neg hd, if_pos hlt]

theorem pairRegion_eq_B_of_data {n : ℕ}
    (φ χ : Module.Dual K (degreeLE X K n))
    (hz : ¬(valuation X K φ = n + 1 ∧ valuation X K χ = n + 1))
    (hφ : valuation X K φ ≠ 0) (hχ : valuation X K χ ≠ 0)
    (heq : valuation X K φ = valuation X K χ) :
    pairRegion X K φ χ = .B := by
  have hd : ¬(valuation X K φ = 0 ∨ valuation X K χ = 0) :=
    not_or.mpr ⟨hφ, hχ⟩
  have hba : ¬ valuation X K χ < valuation X K φ := by omega
  rw [pairRegion, if_neg hz, if_neg hd, if_neg hba, if_pos heq]

theorem pairRegion_eq_C_of_pos_of_lt {n : ℕ}
    (φ χ : Module.Dual K (degreeLE X K n))
    (hφ : 0 < valuation X K φ)
    (hlt : valuation X K φ < valuation X K χ) :
    pairRegion X K φ χ = .C := by
  have hz : ¬(valuation X K φ = n + 1 ∧ valuation X K χ = n + 1) := by
    omega
  have hd : ¬(valuation X K φ = 0 ∨ valuation X K χ = 0) := by omega
  have hba : ¬ valuation X K χ < valuation X K φ := by omega
  have heq : valuation X K φ ≠ valuation X K χ := by omega
  rw [pairRegion, if_neg hz, if_neg hd, if_neg hba, if_neg heq]

theorem pairRegion_eq_D_of_left_zero {n : ℕ}
    (φ χ : Module.Dual K (degreeLE X K n))
    (hφ : valuation X K φ = 0) :
    pairRegion X K φ χ = .D := by
  have hz : ¬(valuation X K φ = n + 1 ∧ valuation X K χ = n + 1) := by
    omega
  rw [pairRegion, if_neg hz, if_pos (Or.inl hφ)]

theorem pairRegion_eq_D_of_right_zero {n : ℕ}
    (φ χ : Module.Dual K (degreeLE X K n))
    (hχ : valuation X K χ = 0) :
    pairRegion X K φ χ = .D := by
  have hz : ¬(valuation X K φ = n + 1 ∧ valuation X K χ = n + 1) := by
    omega
  rw [pairRegion, if_neg hz, if_pos (Or.inr hχ)]


/-- **Region invariance under restriction away from the boundary**: when
neither valuation sits exactly at the top degree of the finer stage, the
pair region is unchanged by restriction to the preceding stage. -/
theorem pairRegion_restrictSucc_of_ne_top {n : ℕ}
    (φ χ : Module.Dual K (degreeLE X K (n + 1)))
    (h1 : valuation X K φ ≠ n + 1) (h2 : valuation X K χ ≠ n + 1) :
    pairRegion X K (restrictSucc X K φ) (restrictSucc X K χ) =
      pairRegion X K φ χ := by
  have hm1 := valuation_restrictSucc_eq_min X K φ
  have hm2 := valuation_restrictSucc_eq_min X K χ
  have hb1 := valuation_le_succ X K φ
  have hb2 := valuation_le_succ X K χ
  rcases hR : pairRegion X K φ χ with - | - | - | - | -
  · obtain ⟨hv1, hv2⟩ := (pairRegion_eq_zero_iff X K φ χ).1 hR
    exact (pairRegion_eq_zero_iff X K _ _).2 ⟨by omega, by omega⟩
  · obtain ⟨hz, hv1, hv2, hlt⟩ := pairRegion_A_data X K φ χ hR
    exact pairRegion_eq_A_of_pos_of_lt X K _ _ (by omega) (by omega)
  · obtain ⟨hz, hv1, hv2, heq⟩ := pairRegion_B_data X K φ χ hR
    exact pairRegion_eq_B_of_data X K _ _ (by omega) (by omega)
      (by omega) (by omega)
  · obtain ⟨hz, hv1, hv2, hlt⟩ := pairRegion_C_data X K φ χ hR
    exact pairRegion_eq_C_of_pos_of_lt X K _ _ (by omega) (by omega)
  · rcases pairRegion_D_data X K φ χ hR with hv | hv
    · exact pairRegion_eq_D_of_left_zero X K _ _ (by omega)
    · exact pairRegion_eq_D_of_right_zero X K _ _ (by omega)

end FreeRootFunctionalValuation

end NonsoficGroupsExist
