import NonsoficGroupsExist.FreeRootPlaneFourier

/-!
# Valuations of finite-stage free-root characters

Kassabov's noncommutative relative-property-`(T)` argument partitions pairs
of additive characters by the least free-word degree on which each character
is nontrivial.  This file defines that valuation directly on the finite degree
stages.  The value `n + 1` represents a character that is trivial throughout
stage `n`; every genuinely detected character has valuation at most `n`.
-/

namespace NonsoficGroupsExist

namespace FreeRootCharacterValuation

open FreeAlgebraDegree
open FreeRootPlaneFourier
open FreeRootFiltration
open FreeRootPlane

noncomputable section

variable (X : Type*) [Fintype X]

/-- A sign character is first detected at the specified word degree.  The
predicate itself does not assert minimality; minimality is imposed by
`characterValuation`. -/
def HasDetectionAtDegree {n : ℕ} (chi : degreeLE X n → ℝ) (d : ℕ) : Prop :=
  ∃ w : FreeMonoid X,
    freeWordLength X w = d ∧
    freeWordLength X w ≤ n ∧
    chi (wordMonomialInDegree X n w) = -1

/-- The least detected word degree, or `n + 1` if the character is trivial on
all word monomials in stage `n`. -/
noncomputable def characterValuation {n : ℕ} (chi : degreeLE X n → ℝ) : ℕ := by
  classical
  exact if h : ∃ d, HasDetectionAtDegree X chi d then Nat.find h else n + 1

/-- If a detection exists, the valuation degree itself is detected. -/
theorem hasDetectionAtDegree_characterValuation
    {n : ℕ} (chi : degreeLE X n → ℝ)
    (h : ∃ d, HasDetectionAtDegree X chi d) :
    HasDetectionAtDegree X chi (characterValuation X chi) := by
  classical
  unfold characterValuation
  split
  · exact Nat.find_spec _
  · contradiction

/-- The valuation is no larger than any detected degree. -/
theorem characterValuation_le_of_hasDetection
    {n : ℕ} (chi : degreeLE X n → ℝ)
    (h : ∃ d, HasDetectionAtDegree X chi d) {d : ℕ}
    (hd : HasDetectionAtDegree X chi d) :
    characterValuation X chi ≤ d := by
  classical
  unfold characterValuation
  split
  · exact Nat.find_min' _ hd
  · contradiction

/-- With no detected word, the valuation is the distinguished value `n+1`. -/
theorem characterValuation_eq_succ_of_not_exists
    {n : ℕ} (chi : degreeLE X n → ℝ)
    (h : ¬ ∃ d, HasDetectionAtDegree X chi d) :
    characterValuation X chi = n + 1 := by
  classical
  simp [characterValuation, h]

/-- Every detected finite-stage character has valuation at most the stage. -/
theorem characterValuation_le_stage_of_exists
    {n : ℕ} (chi : degreeLE X n → ℝ)
    (h : ∃ d, HasDetectionAtDegree X chi d) :
    characterValuation X chi ≤ n := by
  obtain ⟨d, hd⟩ := h
  have hExists : ∃ e, HasDetectionAtDegree X chi e := ⟨d, hd⟩
  obtain ⟨w, hwd, hwn, hchi⟩ := hd
  have hDetection : HasDetectionAtDegree X chi d := ⟨w, hwd, hwn, hchi⟩
  exact (characterValuation_le_of_hasDetection X chi hExists hDetection).trans
    (hwd ▸ hwn)

/-- Nontriviality on an arbitrary coefficient forces a word detection and
hence a valuation within the finite stage. -/
theorem characterValuation_le_stage_of_eq_neg_one
    {n : ℕ} (chi : degreeLE X n → ℝ)
    (hzero : chi 0 = 1)
    (hadd : ∀ a b, chi (a + b) = chi a * chi b)
    (hsign : ∀ a, chi a = 1 ∨ chi a = -1)
    (p : degreeLE X n) (hp : chi p = -1) :
    characterValuation X chi ≤ n := by
  obtain ⟨w, hw, hword⟩ :=
    exists_supported_word_of_additive_sign_character X chi hzero hadd hsign p hp
  have hwDegree := ((mem_degreeLE_iff X p.1 n).1 p.2) w hw
  have hdetect : HasDetectionAtDegree X chi (freeWordLength X w) := by
    refine ⟨w, rfl, hwDegree, ?_⟩
    simpa [wordMonomialInDegree_of_le X w hwDegree] using hword
  exact characterValuation_le_stage_of_exists X chi ⟨_, hdetect⟩

/-- For an additive sign character, the distinguished valuation `n+1` means
the character is genuinely trivial on every coefficient in the stage. -/
theorem eq_one_of_characterValuation_eq_succ
    {n : ℕ} (chi : degreeLE X n → ℝ)
    (hzero : chi 0 = 1)
    (hadd : ∀ a b, chi (a + b) = chi a * chi b)
    (hsign : ∀ a, chi a = 1 ∨ chi a = -1)
    (hval : characterValuation X chi = n + 1) (p : degreeLE X n) :
    chi p = 1 := by
  rcases hsign p with hp | hp
  · exact hp
  · have hle := characterValuation_le_stage_of_eq_neg_one
      X chi hzero hadd hsign p hp
    omega

/-- Valuation zero is exactly detection on the empty word (the unit
coefficient). -/
theorem characterValuation_eq_zero_iff
    {n : ℕ} (chi : degreeLE X n → ℝ) :
    characterValuation X chi = 0 ↔
      chi (wordMonomialInDegree X n 1) = -1 := by
  constructor
  · intro hval
    have hExists : ∃ d, HasDetectionAtDegree X chi d := by
      by_contra hnone
      have hs := characterValuation_eq_succ_of_not_exists X chi hnone
      omega
    have hdetect := hasDetectionAtDegree_characterValuation X chi hExists
    rw [hval] at hdetect
    obtain ⟨w, hwzero, _, hword⟩ := hdetect
    have hwone := (freeWordLength_eq_zero_iff X w).1 hwzero
    subst w
    exact hword
  · intro hone
    have hlen : freeWordLength X (1 : FreeMonoid X) = 0 :=
      (freeWordLength_eq_zero_iff X 1).2 rfl
    have hdetect : HasDetectionAtDegree X chi 0 :=
      ⟨1, hlen, by omega, hone⟩
    have hle := characterValuation_le_of_hasDetection X chi
      ⟨0, hdetect⟩ hdetect
    omega

/-- The character obtained by precomposing with left multiplication by one
free generator.  It lives one degree stage lower. -/
def leftDerivedCharacter {n : ℕ} (chi : degreeLE X (n + 1) → ℝ) (x : X) :
    degreeLE X n → ℝ :=
  fun a ↦ chi (generatorMulCoefficientSucc X x a)

theorem leftDerivedCharacter_zero
    {n : ℕ} (chi : degreeLE X (n + 1) → ℝ) (x : X)
    (hzero : chi 0 = 1) :
    leftDerivedCharacter X chi x 0 = 1 := by
  simp [leftDerivedCharacter, hzero]

theorem leftDerivedCharacter_add
    {n : ℕ} (chi : degreeLE X (n + 1) → ℝ) (x : X)
    (hadd : ∀ a b, chi (a + b) = chi a * chi b) (a b : degreeLE X n) :
    leftDerivedCharacter X chi x (a + b) =
      leftDerivedCharacter X chi x a * leftDerivedCharacter X chi x b := by
  change chi (generatorMulCoefficientSucc X x (a + b)) =
    chi (generatorMulCoefficientSucc X x a) *
      chi (generatorMulCoefficientSucc X x b)
  rw [generatorMulCoefficientSucc_add, hadd]

theorem leftDerivedCharacter_eq_one_or_neg_one
    {n : ℕ} (chi : degreeLE X (n + 1) → ℝ) (x : X)
    (hsign : ∀ a, chi a = 1 ∨ chi a = -1) (a : degreeLE X n) :
    leftDerivedCharacter X chi x a = 1 ∨
      leftDerivedCharacter X chi x a = -1 :=
  hsign _

/-- Kassabov's leading-letter claim: a positive nontrivial character
valuation admits a first generator whose derived character has valuation
exactly one smaller. -/
theorem exists_leftDerivedCharacter_valuation_succ
    {n : ℕ} (chi : degreeLE X (n + 1) → ℝ)
    (hExists : ∃ d, HasDetectionAtDegree X chi d)
    (hpos : 0 < characterValuation X chi) :
    ∃ x : X,
      characterValuation X (leftDerivedCharacter X chi x) + 1 =
        characterValuation X chi := by
  have hminimal := hasDetectionAtDegree_characterValuation X chi hExists
  obtain ⟨w, hwVal, hwStage, hwChi⟩ := hminimal
  have hwPos : 0 < freeWordLength X w := by omega
  obtain ⟨x, v, hwFactor, hvLength⟩ :=
    exists_of_mul_of_freeWordLength_pos X w hwPos
  have hvStage : freeWordLength X v ≤ n := by omega
  have hvChi : leftDerivedCharacter X chi x
      (wordMonomialInDegree X n v) = -1 := by
    unfold leftDerivedCharacter
    rw [generatorMulCoefficientSucc_wordMonomialInDegree X x n v hvStage]
    rw [← hwFactor]
    exact hwChi
  have hvDetect : HasDetectionAtDegree X (leftDerivedCharacter X chi x)
      (freeWordLength X v) := ⟨v, rfl, hvStage, hvChi⟩
  have hvExists : ∃ d,
      HasDetectionAtDegree X (leftDerivedCharacter X chi x) d :=
    ⟨_, hvDetect⟩
  let d := characterValuation X (leftDerivedCharacter X chi x)
  have hdLe : d ≤ freeWordLength X v :=
    characterValuation_le_of_hasDetection X
      (leftDerivedCharacter X chi x) hvExists hvDetect
  have hdDetect := hasDetectionAtDegree_characterValuation X
    (leftDerivedCharacter X chi x) hvExists
  obtain ⟨u, huVal, huStage, huChi⟩ := hdDetect
  have huProductStage :
      freeWordLength X (FreeMonoid.of x * u) ≤ n + 1 := by
    rw [freeWordLength_mul, freeWordLength_of]
    omega
  have huProductChi :
      chi (wordMonomialInDegree X (n + 1) (FreeMonoid.of x * u)) = -1 := by
    change chi (generatorMulCoefficientSucc X x
      (wordMonomialInDegree X n u)) = -1 at huChi
    rw [generatorMulCoefficientSucc_wordMonomialInDegree X x n u huStage]
      at huChi
    exact huChi
  have huProductDetect : HasDetectionAtDegree X chi (d + 1) := by
    refine ⟨FreeMonoid.of x * u, ?_, huProductStage, huProductChi⟩
    rw [freeWordLength_mul, freeWordLength_of, huVal]
    omega
  have hOriginalLe : characterValuation X chi ≤ d + 1 :=
    characterValuation_le_of_hasDetection X chi hExists huProductDetect
  refine ⟨x, ?_⟩
  dsimp [d] at hdLe hOriginalLe ⊢
  omega

/-- A fixed exhaustive enumeration of the finite free-generator alphabet. -/
noncomputable def generatorEnumeration :
    Fin (Fintype.card X) ≃ X :=
  (Fintype.equivFin X).symm

/-- All generator indices realizing the exact one-step valuation descent. -/
noncomputable def leadingGeneratorIndexSet
    {n : ℕ} (chi : degreeLE X (n + 1) → ℝ) :
    Finset (Fin (Fintype.card X)) :=
  Finset.univ.filter fun q ↦
    characterValuation X
        (leftDerivedCharacter X chi (generatorEnumeration X q)) + 1 =
      characterValuation X chi

theorem mem_leadingGeneratorIndexSet_iff
    {n : ℕ} (chi : degreeLE X (n + 1) → ℝ)
    (q : Fin (Fintype.card X)) :
    q ∈ leadingGeneratorIndexSet X chi ↔
      characterValuation X
          (leftDerivedCharacter X chi (generatorEnumeration X q)) + 1 =
        characterValuation X chi := by
  simp [leadingGeneratorIndexSet]

/-- Positive detected valuation makes the leading-generator index set
nonempty. -/
theorem leadingGeneratorIndexSet_nonempty
    {n : ℕ} (chi : degreeLE X (n + 1) → ℝ)
    (hExists : ∃ d, HasDetectionAtDegree X chi d)
    (hpos : 0 < characterValuation X chi) :
    (leadingGeneratorIndexSet X chi).Nonempty := by
  obtain ⟨x, hx⟩ :=
    exists_leftDerivedCharacter_valuation_succ X chi hExists hpos
  let q := (generatorEnumeration X).symm x
  refine ⟨q, ?_⟩
  rw [mem_leadingGeneratorIndexSet_iff]
  simpa [q] using hx

/-- The least enumerated leading generator, with `card X` as a total sentinel
when no generator realizes valuation descent. -/
noncomputable def leastLeadingGeneratorIndex
    {n : ℕ} (chi : degreeLE X (n + 1) → ℝ) : ℕ :=
  if h : (leadingGeneratorIndexSet X chi).Nonempty then
    ((leadingGeneratorIndexSet X chi).min' h).val
  else
    Fintype.card X

theorem leastLeadingGeneratorIndex_lt_card
    {n : ℕ} (chi : degreeLE X (n + 1) → ℝ)
    (h : (leadingGeneratorIndexSet X chi).Nonempty) :
    leastLeadingGeneratorIndex X chi < Fintype.card X := by
  rw [leastLeadingGeneratorIndex, dif_pos h]
  exact ((leadingGeneratorIndexSet X chi).min' h).isLt

/-- The total least-index selector genuinely realizes valuation descent
whenever the leading-generator set is nonempty. -/
theorem leastLeadingGeneratorIndex_spec
    {n : ℕ} (chi : degreeLE X (n + 1) → ℝ)
    (h : (leadingGeneratorIndexSet X chi).Nonempty) :
    characterValuation X
        (leftDerivedCharacter X chi
          (generatorEnumeration X
            ⟨leastLeadingGeneratorIndex X chi,
              leastLeadingGeneratorIndex_lt_card X chi h⟩)) + 1 =
      characterValuation X chi := by
  have hmem := Finset.min'_mem (leadingGeneratorIndexSet X chi) h
  rw [mem_leadingGeneratorIndexSet_iff] at hmem
  simpa [leastLeadingGeneratorIndex, h] using hmem

/-- Valuation of the first coefficient character of a finite plane sign
component. -/
noncomputable def firstCoefficientValuation
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool) : ℕ :=
  characterValuation X
    (firstCoefficientEigenvalue X i j k hij hik hjk n sign)

/-- Valuation of the second coefficient character of a finite plane sign
component. -/
noncomputable def secondCoefficientValuation
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool) : ℕ :=
  characterValuation X
    (secondCoefficientEigenvalue X i j k hij hik hjk n sign)

/-- Kassabov's four valuation regions.  Region `D` detects a constant term;
`A`, `B`, and `C` compare the two positive leading degrees. -/
inductive ValuationRegion
  | A | B | C | D
  deriving DecidableEq, Fintype

/-- Classify a finite-plane sign assignment by its two character valuations. -/
noncomputable def planeCharacterRegion
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool) :
    ValuationRegion :=
  let a := firstCoefficientValuation X i j k hij hik hjk n sign
  let b := secondCoefficientValuation X i j k hij hik hjk n sign
  if a = 0 ∨ b = 0 then .D
  else if b < a then .A
  else if a = b then .B
  else .C

/-- The finite set of sign assignments in one valuation region. -/
noncomputable def planeRegionSignSet
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (region : ValuationRegion) :
    Finset (Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool) :=
  Finset.univ.filter fun sign ↦
    planeCharacterRegion X i j k hij hik hjk n sign = region

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A nonzero Fourier component with a nontrivial plane character has at least
one genuinely detected coordinate valuation within the current stage. -/
theorem firstValuation_le_or_secondValuation_le_of_planeEigenvalue_eq_neg_one
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool)
    (z : E)
    (hv : planeComponent X i j k hij hik hjk n rho sign z ≠ 0)
    (g : Plane X i j k hij hik hjk n)
    (hg : planeEigenvalue X i j k hij hik hjk n sign g = -1) :
    firstCoefficientValuation X i j k hij hik hjk n sign ≤ n ∨
      secondCoefficientValuation X i j k hij hik hjk n sign ≤ n := by
  rcases exists_nontrivial_coefficient_of_planeEigenvalue_eq_neg_one
      X i j k hij hik hjk n rho sign z hv g hg with ⟨a, ha⟩ | ⟨b, hb⟩
  · left
    exact characterValuation_le_stage_of_eq_neg_one X
      (firstCoefficientEigenvalue X i j k hij hik hjk n sign)
      (firstCoefficientEigenvalue_zero_of_component_ne_zero
        X i j k hij hik hjk n rho sign z hv)
      (firstCoefficientEigenvalue_add_of_component_ne_zero
        X i j k hij hik hjk n rho sign z hv)
      (firstCoefficientEigenvalue_eq_one_or_neg_one
        X i j k hij hik hjk n sign) a ha
  · right
    exact characterValuation_le_stage_of_eq_neg_one X
      (secondCoefficientEigenvalue X i j k hij hik hjk n sign)
      (secondCoefficientEigenvalue_zero_of_component_ne_zero
        X i j k hij hik hjk n rho sign z hv)
      (secondCoefficientEigenvalue_add_of_component_ne_zero
        X i j k hij hik hjk n rho sign z hv)
      (secondCoefficientEigenvalue_eq_one_or_neg_one
        X i j k hij hik hjk n sign) b hb

end

end FreeRootCharacterValuation

end NonsoficGroupsExist
