import NonsoficGroupsExist.FreeRootPlaneFourier
import NonsoficGroupsExist.KazhdanFixedSpace

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
open FiniteInvolutionDecomposition

noncomputable section

variable (X : Type*) [Fintype X]

/-- A sign character is first detected at the specified word degree.  The
predicate itself does not assert minimality; minimality is imposed by
`characterValuation`. -/
def HasDetectionAtDegree {n : ℕ} (chi : degreeLE X (ZMod 2) n → ℝ) (d : ℕ) : Prop :=
  ∃ w : FreeMonoid X,
    freeWordLength X w = d ∧
    freeWordLength X w ≤ n ∧
    chi (wordMonomialInDegree X (ZMod 2) n w) = -1

/-- The least detected word degree, or `n + 1` if the character is trivial on
all word monomials in stage `n`. -/
noncomputable def characterValuation {n : ℕ} (chi : degreeLE X (ZMod 2) n → ℝ) : ℕ := by
  classical
  exact if h : ∃ d, HasDetectionAtDegree X chi d then Nat.find h else n + 1

/-- If a detection exists, the valuation degree itself is detected. -/
theorem hasDetectionAtDegree_characterValuation
    {n : ℕ} (chi : degreeLE X (ZMod 2) n → ℝ)
    (h : ∃ d, HasDetectionAtDegree X chi d) :
    HasDetectionAtDegree X chi (characterValuation X chi) := by
  classical
  unfold characterValuation
  split
  · exact Nat.find_spec _
  · contradiction

/-- The valuation is no larger than any detected degree. -/
theorem characterValuation_le_of_hasDetection
    {n : ℕ} (chi : degreeLE X (ZMod 2) n → ℝ)
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
    {n : ℕ} (chi : degreeLE X (ZMod 2) n → ℝ)
    (h : ¬ ∃ d, HasDetectionAtDegree X chi d) :
    characterValuation X chi = n + 1 := by
  classical
  simp [characterValuation, h]

/-- Every detected finite-stage character has valuation at most the stage. -/
theorem characterValuation_le_stage_of_exists
    {n : ℕ} (chi : degreeLE X (ZMod 2) n → ℝ)
    (h : ∃ d, HasDetectionAtDegree X chi d) :
    characterValuation X chi ≤ n := by
  obtain ⟨d, hd⟩ := h
  have hExists : ∃ e, HasDetectionAtDegree X chi e := ⟨d, hd⟩
  obtain ⟨w, hwd, hwn, hchi⟩ := hd
  have hDetection : HasDetectionAtDegree X chi d := ⟨w, hwd, hwn, hchi⟩
  exact (characterValuation_le_of_hasDetection X chi hExists hDetection).trans
    (hwd ▸ hwn)

/-- Every finite-stage valuation is bounded by the stage sentinel. -/
theorem characterValuation_le_succ
    {n : ℕ} (chi : degreeLE X (ZMod 2) n → ℝ) :
    characterValuation X chi ≤ n + 1 := by
  by_cases h : ∃ d, HasDetectionAtDegree X chi d
  · exact (characterValuation_le_stage_of_exists X chi h).trans
      (Nat.le_succ n)
  · rw [characterValuation_eq_succ_of_not_exists X chi h]

/-- Nontriviality on an arbitrary coefficient forces a word detection and
hence a valuation within the finite stage. -/
theorem characterValuation_le_stage_of_eq_neg_one
    {n : ℕ} (chi : degreeLE X (ZMod 2) n → ℝ)
    (hzero : chi 0 = 1)
    (hadd : ∀ a b, chi (a + b) = chi a * chi b)
    (hsign : ∀ a, chi a = 1 ∨ chi a = -1)
    (p : degreeLE X (ZMod 2) n) (hp : chi p = -1) :
    characterValuation X chi ≤ n := by
  obtain ⟨w, hw, hword⟩ :=
    exists_supported_word_of_additive_sign_character X chi hzero hadd hsign p hp
  have hwDegree := ((mem_degreeLE_iff X (ZMod 2) p.1 n).1 p.2) w hw
  have hdetect : HasDetectionAtDegree X chi (freeWordLength X w) := by
    refine ⟨w, rfl, hwDegree, ?_⟩
    simpa [wordMonomialInDegree_of_le X (ZMod 2) w hwDegree] using hword
  exact characterValuation_le_stage_of_exists X chi ⟨_, hdetect⟩

/-- For an additive sign character, the distinguished valuation `n+1` means
the character is genuinely trivial on every coefficient in the stage. -/
theorem eq_one_of_characterValuation_eq_succ
    {n : ℕ} (chi : degreeLE X (ZMod 2) n → ℝ)
    (hzero : chi 0 = 1)
    (hadd : ∀ a b, chi (a + b) = chi a * chi b)
    (hsign : ∀ a, chi a = 1 ∨ chi a = -1)
    (hval : characterValuation X chi = n + 1) (p : degreeLE X (ZMod 2) n) :
    chi p = 1 := by
  rcases hsign p with hp | hp
  · exact hp
  · have hle := characterValuation_le_stage_of_eq_neg_one
      X chi hzero hadd hsign p hp
    omega

/-- Valuation zero is exactly detection on the empty word (the unit
coefficient). -/
theorem characterValuation_eq_zero_iff
    {n : ℕ} (chi : degreeLE X (ZMod 2) n → ℝ) :
    characterValuation X chi = 0 ↔
      chi (wordMonomialInDegree X (ZMod 2) n 1) = -1 := by
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

/-- Restrict a character from degree `n+1` to the included degree-`n`
coefficient space. -/
def restrictCharacterSucc {n : ℕ} (chi : degreeLE X (ZMod 2) (n + 1) → ℝ) :
    degreeLE X (ZMod 2) n → ℝ :=
  fun a ↦ chi (coefficientSucc X a)

theorem hasDetectionAtDegree_of_restrictCharacterSucc
    {n d : ℕ} (chi : degreeLE X (ZMod 2) (n + 1) → ℝ)
    (h : HasDetectionAtDegree X (restrictCharacterSucc X chi) d) :
    HasDetectionAtDegree X chi d := by
  obtain ⟨w, hwd, hwn, hchi⟩ := h
  refine ⟨w, hwd, hwn.trans (Nat.le_succ n), ?_⟩
  unfold restrictCharacterSucc at hchi
  rw [coefficientSucc_wordMonomialInDegree X n w hwn] at hchi
  exact hchi

theorem hasDetectionAtDegree_restrictCharacterSucc
    {n d : ℕ} (chi : degreeLE X (ZMod 2) (n + 1) → ℝ)
    (h : HasDetectionAtDegree X chi d)
    (hdn : d ≤ n) :
    HasDetectionAtDegree X (restrictCharacterSucc X chi) d := by
  obtain ⟨w, hwd, _, hchi⟩ := h
  have hwn : freeWordLength X w ≤ n := hwd.trans_le hdn
  refine ⟨w, hwd, hwn, ?_⟩
  unfold restrictCharacterSucc
  rw [coefficientSucc_wordMonomialInDegree X n w hwn]
  exact hchi

/-- Restriction preserves every valuation that is at most the restricted
stage's sentinel `n+1`.  This includes a character first detected in degree
`n+1`, whose restriction is trivial and therefore has exactly that sentinel
value. -/
theorem characterValuation_restrictCharacterSucc_eq
    {n : ℕ} (chi : degreeLE X (ZMod 2) (n + 1) → ℝ)
    (hle : characterValuation X chi ≤ n + 1) :
    characterValuation X (restrictCharacterSucc X chi) =
      characterValuation X chi := by
  by_cases hvn : characterValuation X chi ≤ n
  · have hExists : ∃ d, HasDetectionAtDegree X chi d := by
      by_contra hnone
      have hsucc := characterValuation_eq_succ_of_not_exists X chi hnone
      omega
    have hdetect := hasDetectionAtDegree_characterValuation X chi hExists
    have hrestrict := hasDetectionAtDegree_restrictCharacterSucc X chi hdetect hvn
    have hRestrictExists : ∃ d,
        HasDetectionAtDegree X (restrictCharacterSucc X chi) d :=
      ⟨_, hrestrict⟩
    have hforward := characterValuation_le_of_hasDetection X
      (restrictCharacterSucc X chi) hRestrictExists hrestrict
    have hrestrictMinimal := hasDetectionAtDegree_characterValuation X
      (restrictCharacterSucc X chi) hRestrictExists
    have hbackDetection := hasDetectionAtDegree_of_restrictCharacterSucc
      X chi hrestrictMinimal
    have hback := characterValuation_le_of_hasDetection X chi hExists
      hbackDetection
    omega
  · have hval : characterValuation X chi = n + 1 := by omega
    have hnone : ¬ ∃ d,
        HasDetectionAtDegree X (restrictCharacterSucc X chi) d := by
      rintro ⟨d, hd⟩
      have hback := hasDetectionAtDegree_of_restrictCharacterSucc X chi hd
      have hExists : ∃ e, HasDetectionAtDegree X chi e := ⟨d, hback⟩
      have hleD := characterValuation_le_of_hasDetection X chi hExists hback
      obtain ⟨w, hwd, hwn, _⟩ := hd
      have : d ≤ n := hwd ▸ hwn
      omega
    rw [characterValuation_eq_succ_of_not_exists X
      (restrictCharacterSucc X chi) hnone, hval]

/-- In full generality, restriction truncates the one-extra-stage valuation
at the lower stage's sentinel. -/
theorem characterValuation_restrictCharacterSucc_eq_min
    {n : ℕ} (chi : degreeLE X (ZMod 2) (n + 1) → ℝ) :
    characterValuation X (restrictCharacterSucc X chi) =
      min (characterValuation X chi) (n + 1) := by
  by_cases hle : characterValuation X chi ≤ n + 1
  · rw [characterValuation_restrictCharacterSucc_eq X chi hle,
      min_eq_left hle]
  · have hval : characterValuation X chi = n + 2 := by
      have hbound := characterValuation_le_succ X chi
      omega
    have hnoneOriginal : ¬ ∃ d, HasDetectionAtDegree X chi d := by
      intro h
      have hstage := characterValuation_le_stage_of_exists X chi h
      omega
    have hnoneRestrict : ¬ ∃ d,
        HasDetectionAtDegree X (restrictCharacterSucc X chi) d := by
      rintro ⟨d, hd⟩
      exact hnoneOriginal ⟨d,
        hasDetectionAtDegree_of_restrictCharacterSucc X chi hd⟩
    rw [characterValuation_eq_succ_of_not_exists X
      (restrictCharacterSucc X chi) hnoneRestrict, hval]
    omega

/-- Pointwise multiplication of two real sign characters.  For additive
characters this is their group-law product in the dual coefficient group. -/
def characterProduct {n : ℕ} (chi psi : degreeLE X (ZMod 2) n → ℝ) :
    degreeLE X (ZMod 2) n → ℝ :=
  fun a ↦ chi a * psi a

theorem characterProduct_eq_one_or_neg_one
    {n : ℕ} (chi psi : degreeLE X (ZMod 2) n → ℝ)
    (hchi : ∀ a, chi a = 1 ∨ chi a = -1)
    (hpsi : ∀ a, psi a = 1 ∨ psi a = -1)
    (a : degreeLE X (ZMod 2) n) :
    characterProduct X chi psi a = 1 ∨
      characterProduct X chi psi a = -1 := by
  rcases hchi a with ha | ha <;> rcases hpsi a with hb | hb <;>
    simp [characterProduct, ha, hb]

/-- Below a character's least detected degree, every word monomial has value
`1`. -/
theorem eq_one_of_word_degree_lt_characterValuation
    {n : ℕ} (chi : degreeLE X (ZMod 2) n → ℝ)
    (hsign : ∀ a, chi a = 1 ∨ chi a = -1)
    (w : FreeMonoid X) (hwn : freeWordLength X w ≤ n)
    (hlt : freeWordLength X w < characterValuation X chi) :
    chi (wordMonomialInDegree X (ZMod 2) n w) = 1 := by
  rcases hsign (wordMonomialInDegree X (ZMod 2) n w) with hone | hneg
  · exact hone
  · have hdetect : HasDetectionAtDegree X chi (freeWordLength X w) :=
      ⟨w, rfl, hwn, hneg⟩
    have hle := characterValuation_le_of_hasDetection X chi
      ⟨_, hdetect⟩ hdetect
    omega

/-- If two sign characters have distinct valuations and the lower-valuation
character is genuinely detected, their product has exactly that lower
valuation.  Cancellation cannot occur before the other character starts. -/
theorem characterValuation_characterProduct_eq_left_of_lt
    {n : ℕ} (chi psi : degreeLE X (ZMod 2) n → ℝ)
    (hchi : ∀ a, chi a = 1 ∨ chi a = -1)
    (hpsi : ∀ a, psi a = 1 ∨ psi a = -1)
    (hChiExists : ∃ d, HasDetectionAtDegree X chi d)
    (hlt : characterValuation X chi < characterValuation X psi) :
    characterValuation X (characterProduct X chi psi) =
      characterValuation X chi := by
  have hchiDetect := hasDetectionAtDegree_characterValuation X chi hChiExists
  obtain ⟨w, hwVal, hwn, hwChi⟩ := hchiDetect
  have hwPsi : psi (wordMonomialInDegree X (ZMod 2) n w) = 1 :=
    eq_one_of_word_degree_lt_characterValuation X psi hpsi w hwn (by omega)
  have hproductDetect : HasDetectionAtDegree X (characterProduct X chi psi)
      (characterValuation X chi) := by
    refine ⟨w, hwVal, hwn, ?_⟩
    simp [characterProduct, hwChi, hwPsi]
  have hProductExists : ∃ d,
      HasDetectionAtDegree X (characterProduct X chi psi) d :=
    ⟨_, hproductDetect⟩
  have hupper := characterValuation_le_of_hasDetection X
    (characterProduct X chi psi) hProductExists hproductDetect
  have hproductMinimal := hasDetectionAtDegree_characterValuation X
    (characterProduct X chi psi) hProductExists
  obtain ⟨u, huVal, hun, huProduct⟩ := hproductMinimal
  have hlower : characterValuation X chi ≤
      characterValuation X (characterProduct X chi psi) := by
    by_contra hnot
    have huChi : chi (wordMonomialInDegree X (ZMod 2) n u) = 1 :=
      eq_one_of_word_degree_lt_characterValuation X chi hchi u hun (by omega)
    have huPsi : psi (wordMonomialInDegree X (ZMod 2) n u) = 1 :=
      eq_one_of_word_degree_lt_characterValuation X psi hpsi u hun (by omega)
    simp [characterProduct, huChi, huPsi] at huProduct
    exact (by norm_num : (1 : ℝ) ≠ -1) huProduct
  exact le_antisymm hupper hlower

theorem characterValuation_characterProduct_eq_right_of_lt
    {n : ℕ} (chi psi : degreeLE X (ZMod 2) n → ℝ)
    (hchi : ∀ a, chi a = 1 ∨ chi a = -1)
    (hpsi : ∀ a, psi a = 1 ∨ psi a = -1)
    (hPsiExists : ∃ d, HasDetectionAtDegree X psi d)
    (hlt : characterValuation X psi < characterValuation X chi) :
    characterValuation X (characterProduct X chi psi) =
      characterValuation X psi := by
  have h := characterValuation_characterProduct_eq_left_of_lt
    X psi chi hpsi hchi hPsiExists hlt
  have heq : characterProduct X chi psi = characterProduct X psi chi := by
    funext a
    simp [characterProduct, mul_comm]
  rw [heq]
  exact h

/-- The character obtained by precomposing with left multiplication by one
free generator.  It lives one degree stage lower. -/
def leftDerivedCharacter {n : ℕ} (chi : degreeLE X (ZMod 2) (n + 1) → ℝ) (x : X) :
    degreeLE X (ZMod 2) n → ℝ :=
  fun a ↦ chi (generatorMulCoefficientSucc X x a)

/-- Taking a generator-derived character commutes exactly with restriction by
one degree stage. -/
theorem leftDerivedCharacter_restrictCharacterSucc
    {n : ℕ} (chi : degreeLE X (ZMod 2) (n + 2) → ℝ) (x : X) :
    leftDerivedCharacter X (restrictCharacterSucc X chi) x =
      restrictCharacterSucc X (leftDerivedCharacter X chi x) := by
  funext a
  unfold leftDerivedCharacter restrictCharacterSucc
  congr 1

theorem leftDerivedCharacter_zero
    {n : ℕ} (chi : degreeLE X (ZMod 2) (n + 1) → ℝ) (x : X)
    (hzero : chi 0 = 1) :
    leftDerivedCharacter X chi x 0 = 1 := by
  simp [leftDerivedCharacter, hzero]

theorem leftDerivedCharacter_add
    {n : ℕ} (chi : degreeLE X (ZMod 2) (n + 1) → ℝ) (x : X)
    (hadd : ∀ a b, chi (a + b) = chi a * chi b) (a b : degreeLE X (ZMod 2) n) :
    leftDerivedCharacter X chi x (a + b) =
      leftDerivedCharacter X chi x a * leftDerivedCharacter X chi x b := by
  change chi (generatorMulCoefficientSucc X x (a + b)) =
    chi (generatorMulCoefficientSucc X x a) *
      chi (generatorMulCoefficientSucc X x b)
  rw [generatorMulCoefficientSucc_add, hadd]

theorem leftDerivedCharacter_eq_one_or_neg_one
    {n : ℕ} (chi : degreeLE X (ZMod 2) (n + 1) → ℝ) (x : X)
    (hsign : ∀ a, chi a = 1 ∨ chi a = -1) (a : degreeLE X (ZMod 2) n) :
    leftDerivedCharacter X chi x a = 1 ∨
      leftDerivedCharacter X chi x a = -1 :=
  hsign _

/-- Kassabov's leading-letter claim: a positive nontrivial character
valuation admits a first generator whose derived character has valuation
exactly one smaller. -/
theorem exists_leftDerivedCharacter_valuation_succ
    {n : ℕ} (chi : degreeLE X (ZMod 2) (n + 1) → ℝ)
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
      (wordMonomialInDegree X (ZMod 2) n v) = -1 := by
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
      chi (wordMonomialInDegree X (ZMod 2) (n + 1) (FreeMonoid.of x * u)) = -1 := by
    change chi (generatorMulCoefficientSucc X x
      (wordMonomialInDegree X (ZMod 2) n u)) = -1 at huChi
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
    {n : ℕ} (chi : degreeLE X (ZMod 2) (n + 1) → ℝ) :
    Finset (Fin (Fintype.card X)) :=
  Finset.univ.filter fun q ↦
    characterValuation X
        (leftDerivedCharacter X chi (generatorEnumeration X q)) + 1 =
      characterValuation X chi

theorem mem_leadingGeneratorIndexSet_iff
    {n : ℕ} (chi : degreeLE X (ZMod 2) (n + 1) → ℝ)
    (q : Fin (Fintype.card X)) :
    q ∈ leadingGeneratorIndexSet X chi ↔
      characterValuation X
          (leftDerivedCharacter X chi (generatorEnumeration X q)) + 1 =
        characterValuation X chi := by
  simp [leadingGeneratorIndexSet]

/-- Away from the top-degree boundary, restriction preserves exactly the set
of generators realizing leading-term valuation descent. -/
theorem mem_leadingGeneratorIndexSet_restrictCharacterSucc_iff
    {n : ℕ} (chi : degreeLE X (ZMod 2) (n + 2) → ℝ)
    (hle : characterValuation X chi ≤ n + 1)
    (q : Fin (Fintype.card X)) :
    q ∈ leadingGeneratorIndexSet X (restrictCharacterSucc X chi) ↔
      q ∈ leadingGeneratorIndexSet X chi := by
  rw [mem_leadingGeneratorIndexSet_iff,
    mem_leadingGeneratorIndexSet_iff]
  have hchi : characterValuation X (restrictCharacterSucc X chi) =
      characterValuation X chi :=
    characterValuation_restrictCharacterSucc_eq X chi
      (hle.trans (Nat.le_succ (n + 1)))
  have hderived : leftDerivedCharacter X (restrictCharacterSucc X chi)
      (generatorEnumeration X q) =
      restrictCharacterSucc X
        (leftDerivedCharacter X chi (generatorEnumeration X q)) :=
    leftDerivedCharacter_restrictCharacterSucc X chi
      (generatorEnumeration X q)
  rw [hchi, hderived]
  constructor
  · intro h
    have hmin := characterValuation_restrictCharacterSucc_eq_min X
      (leftDerivedCharacter X chi (generatorEnumeration X q))
    rw [hmin] at h
    have hbound := characterValuation_le_succ X
      (leftDerivedCharacter X chi (generatorEnumeration X q))
    omega
  · intro h
    have hderivedLe : characterValuation X
        (leftDerivedCharacter X chi (generatorEnumeration X q)) ≤ n + 1 := by
      omega
    rw [characterValuation_restrictCharacterSucc_eq X _ hderivedLe]
    exact h

theorem leadingGeneratorIndexSet_restrictCharacterSucc
    {n : ℕ} (chi : degreeLE X (ZMod 2) (n + 2) → ℝ)
    (hle : characterValuation X chi ≤ n + 1) :
    leadingGeneratorIndexSet X (restrictCharacterSucc X chi) =
      leadingGeneratorIndexSet X chi := by
  ext q
  exact mem_leadingGeneratorIndexSet_restrictCharacterSucc_iff X chi hle q

/-- Positive detected valuation makes the leading-generator index set
nonempty. -/
theorem leadingGeneratorIndexSet_nonempty
    {n : ℕ} (chi : degreeLE X (ZMod 2) (n + 1) → ℝ)
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
    {n : ℕ} (chi : degreeLE X (ZMod 2) (n + 1) → ℝ) : ℕ :=
  if h : (leadingGeneratorIndexSet X chi).Nonempty then
    ((leadingGeneratorIndexSet X chi).min' h).val
  else
    Fintype.card X

theorem leastLeadingGeneratorIndex_lt_card
    {n : ℕ} (chi : degreeLE X (ZMod 2) (n + 1) → ℝ)
    (h : (leadingGeneratorIndexSet X chi).Nonempty) :
    leastLeadingGeneratorIndex X chi < Fintype.card X := by
  rw [leastLeadingGeneratorIndex, dif_pos h]
  exact ((leadingGeneratorIndexSet X chi).min' h).isLt

/-- The total least-index selector genuinely realizes valuation descent
whenever the leading-generator set is nonempty. -/
theorem leastLeadingGeneratorIndex_spec
    {n : ℕ} (chi : degreeLE X (ZMod 2) (n + 1) → ℝ)
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

/-- Below the top-degree boundary, the canonical least leading generator is
unchanged by restriction to the preceding stage. -/
theorem leastLeadingGeneratorIndex_restrictCharacterSucc
    {n : ℕ} (chi : degreeLE X (ZMod 2) (n + 2) → ℝ)
    (hle : characterValuation X chi ≤ n + 1) :
    leastLeadingGeneratorIndex X (restrictCharacterSucc X chi) =
      leastLeadingGeneratorIndex X chi := by
  unfold leastLeadingGeneratorIndex
  rw [leadingGeneratorIndexSet_restrictCharacterSucc X chi hle]

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

/-- Kassabov's four nonzero valuation regions, together with the all-trivial
character pair.  Keeping `zero` separate is essential: the paper partitions
the complement of `(0,0)`, and the invariant Fourier component must never be
charged to region `B`. -/
inductive ValuationRegion
  | zero | A | B | C | D
  deriving DecidableEq, Fintype

/-- Classify an arbitrary pair of finite-stage characters. -/
noncomputable def characterPairRegion
    (n : ℕ) (chi psi : degreeLE X (ZMod 2) n → ℝ) :
    ValuationRegion :=
  let a := characterValuation X chi
  let b := characterValuation X psi
  if a = n + 1 ∧ b = n + 1 then .zero
  else if a = 0 ∨ b = 0 then .D
  else if b < a then .A
  else if a = b then .B
  else .C

theorem characterPairRegion_eq_zero_iff
    (n : ℕ) (chi psi : degreeLE X (ZMod 2) n → ℝ) :
    characterPairRegion X n chi psi = .zero ↔
      characterValuation X chi = n + 1 ∧
        characterValuation X psi = n + 1 := by
  constructor
  · intro h
    simp only [characterPairRegion] at h
    by_cases hz : characterValuation X chi = n + 1 ∧
        characterValuation X psi = n + 1
    · exact hz
    · rw [if_neg hz] at h
      by_cases hd : characterValuation X chi = 0 ∨
          characterValuation X psi = 0
      · rw [if_pos hd] at h
        cases h
      · rw [if_neg hd] at h
        by_cases hba : characterValuation X psi < characterValuation X chi
        · rw [if_pos hba] at h
          cases h
        · rw [if_neg hba] at h
          by_cases heq : characterValuation X chi = characterValuation X psi
          · rw [if_pos heq] at h
            cases h
          · rw [if_neg heq] at h
            cases h
  · intro h
    simp [characterPairRegion, h]

/-- Exact numerical data carried by membership in region `A`. -/
theorem characterPairRegion_A_data
    (n : ℕ) (chi psi : degreeLE X (ZMod 2) n → ℝ)
    (h : characterPairRegion X n chi psi = .A) :
      ¬(characterValuation X chi = n + 1 ∧
        characterValuation X psi = n + 1) ∧
      characterValuation X chi ≠ 0 ∧
      characterValuation X psi ≠ 0 ∧
      characterValuation X psi < characterValuation X chi := by
  by_cases hz : characterValuation X chi = n + 1 ∧
      characterValuation X psi = n + 1
  · rw [characterPairRegion, if_pos hz] at h
    cases h
  · by_cases hd : characterValuation X chi = 0 ∨
      characterValuation X psi = 0
    · rw [characterPairRegion, if_neg hz, if_pos hd] at h
      cases h
    · by_cases hba : characterValuation X psi < characterValuation X chi
      · exact ⟨hz, (not_or.mp hd).1, (not_or.mp hd).2, hba⟩
      · by_cases heq : characterValuation X chi = characterValuation X psi
        · rw [characterPairRegion, if_neg hz, if_neg hd, if_neg hba,
            if_pos heq] at h
          cases h
        · rw [characterPairRegion, if_neg hz, if_neg hd, if_neg hba,
            if_neg heq] at h
          cases h

/-- Exact numerical data carried by membership in region `B`. -/
theorem characterPairRegion_B_data
    (n : ℕ) (chi psi : degreeLE X (ZMod 2) n → ℝ)
    (h : characterPairRegion X n chi psi = .B) :
      ¬(characterValuation X chi = n + 1 ∧
        characterValuation X psi = n + 1) ∧
      characterValuation X chi ≠ 0 ∧
      characterValuation X psi ≠ 0 ∧
      characterValuation X chi = characterValuation X psi := by
  by_cases hz : characterValuation X chi = n + 1 ∧
      characterValuation X psi = n + 1
  · rw [characterPairRegion, if_pos hz] at h
    cases h
  · by_cases hd : characterValuation X chi = 0 ∨
      characterValuation X psi = 0
    · rw [characterPairRegion, if_neg hz, if_pos hd] at h
      cases h
    · by_cases hba : characterValuation X psi < characterValuation X chi
      · rw [characterPairRegion, if_neg hz, if_neg hd, if_pos hba] at h
        cases h
      · by_cases heq : characterValuation X chi = characterValuation X psi
        · exact ⟨hz, (not_or.mp hd).1, (not_or.mp hd).2, heq⟩
        · rw [characterPairRegion, if_neg hz, if_neg hd, if_neg hba,
            if_neg heq] at h
          cases h

/-- Exact numerical data carried by membership in region `C`. -/
theorem characterPairRegion_C_data
    (n : ℕ) (chi psi : degreeLE X (ZMod 2) n → ℝ)
    (h : characterPairRegion X n chi psi = .C) :
      ¬(characterValuation X chi = n + 1 ∧
        characterValuation X psi = n + 1) ∧
      characterValuation X chi ≠ 0 ∧
      characterValuation X psi ≠ 0 ∧
      characterValuation X chi < characterValuation X psi := by
  by_cases hz : characterValuation X chi = n + 1 ∧
      characterValuation X psi = n + 1
  · rw [characterPairRegion, if_pos hz] at h
    cases h
  · by_cases hd : characterValuation X chi = 0 ∨
      characterValuation X psi = 0
    · rw [characterPairRegion, if_neg hz, if_pos hd] at h
      cases h
    · by_cases hba : characterValuation X psi < characterValuation X chi
      · rw [characterPairRegion, if_neg hz, if_neg hd, if_pos hba] at h
        cases h
      · by_cases heq : characterValuation X chi = characterValuation X psi
        · rw [characterPairRegion, if_neg hz, if_neg hd, if_neg hba,
            if_pos heq] at h
          cases h
        · refine ⟨hz, (not_or.mp hd).1, (not_or.mp hd).2, ?_⟩
          omega

/-- Exact zero-coordinate alternative carried by membership in region `D`. -/
theorem characterPairRegion_D_data
    (n : ℕ) (chi psi : degreeLE X (ZMod 2) n → ℝ)
    (h : characterPairRegion X n chi psi = .D) :
    characterValuation X chi = 0 ∨ characterValuation X psi = 0 := by
  by_cases hz : characterValuation X chi = n + 1 ∧
      characterValuation X psi = n + 1
  · rw [characterPairRegion, if_pos hz] at h
    cases h
  · by_cases hd : characterValuation X chi = 0 ∨
      characterValuation X psi = 0
    · exact hd
    · by_cases hba : characterValuation X psi < characterValuation X chi
      · rw [characterPairRegion, if_neg hz, if_neg hd, if_pos hba] at h
        cases h
      · by_cases heq : characterValuation X chi = characterValuation X psi
        · rw [characterPairRegion, if_neg hz, if_neg hd, if_neg hba,
            if_pos heq] at h
          cases h
        · rw [characterPairRegion, if_neg hz, if_neg hd, if_neg hba,
            if_neg heq] at h
          cases h

theorem characterPairRegion_eq_A_of_pos_of_lt
    (n : ℕ) (chi psi : degreeLE X (ZMod 2) n → ℝ)
    (hpsi : 0 < characterValuation X psi)
    (hlt : characterValuation X psi < characterValuation X chi) :
    characterPairRegion X n chi psi = .A := by
  have hz : ¬(characterValuation X chi = n + 1 ∧
      characterValuation X psi = n + 1) := by omega
  have hd : ¬(characterValuation X chi = 0 ∨
      characterValuation X psi = 0) := by omega
  rw [characterPairRegion, if_neg hz, if_neg hd, if_pos hlt]

theorem characterPairRegion_eq_B_of_data
    (n : ℕ) (chi psi : degreeLE X (ZMod 2) n → ℝ)
    (hz : ¬(characterValuation X chi = n + 1 ∧
      characterValuation X psi = n + 1))
    (hchi : characterValuation X chi ≠ 0)
    (hpsi : characterValuation X psi ≠ 0)
    (heq : characterValuation X chi = characterValuation X psi) :
    characterPairRegion X n chi psi = .B := by
  have hd : ¬(characterValuation X chi = 0 ∨
      characterValuation X psi = 0) := not_or.mpr ⟨hchi, hpsi⟩
  have hba : ¬characterValuation X psi < characterValuation X chi := by omega
  rw [characterPairRegion, if_neg hz, if_neg hd, if_neg hba, if_pos heq]

theorem characterPairRegion_eq_C_of_pos_of_lt
    (n : ℕ) (chi psi : degreeLE X (ZMod 2) n → ℝ)
    (hchi : 0 < characterValuation X chi)
    (hlt : characterValuation X chi < characterValuation X psi) :
    characterPairRegion X n chi psi = .C := by
  have hz : ¬(characterValuation X chi = n + 1 ∧
      characterValuation X psi = n + 1) := by omega
  have hd : ¬(characterValuation X chi = 0 ∨
      characterValuation X psi = 0) := by omega
  have hba : ¬characterValuation X psi < characterValuation X chi := by omega
  have heq : characterValuation X chi ≠ characterValuation X psi := by omega
  rw [characterPairRegion, if_neg hz, if_neg hd, if_neg hba, if_neg heq]

theorem characterPairRegion_eq_D_of_left_zero
    (n : ℕ) (chi psi : degreeLE X (ZMod 2) n → ℝ)
    (hchi : characterValuation X chi = 0) :
    characterPairRegion X n chi psi = .D := by
  simp [characterPairRegion, hchi]

theorem characterPairRegion_eq_D_of_right_zero
    (n : ℕ) (chi psi : degreeLE X (ZMod 2) n → ℝ)
    (hpsi : characterValuation X psi = 0) :
    characterPairRegion X n chi psi = .D := by
  simp [characterPairRegion, hpsi]

/-- The dual action of the opposite adjacent shear on the first character:
restrict the original first character and multiply it by the generator-derived
second character. -/
def oppositeShearedFirstCharacter
    {n : ℕ} (chi psi : degreeLE X (ZMod 2) (n + 1) → ℝ) (x : X) :
    degreeLE X (ZMod 2) n → ℝ :=
  characterProduct X (restrictCharacterSucc X chi)
    (leftDerivedCharacter X psi x)

/-- The opposite adjacent shear leaves the second character unchanged, apart
from restriction to the lower degree stage. -/
def oppositeShearedSecondCharacter
    {n : ℕ} (psi : degreeLE X (ZMod 2) (n + 1) → ℝ) :
    degreeLE X (ZMod 2) n → ℝ :=
  restrictCharacterSucc X psi

/-- Kassabov's first valuation-transport claim at finite degree: if a
next-stage pair is in `A ∪ B` and `x` detects the leading part of the second
character, the opposite shear restricts to a pair in `C ∪ D`. -/
theorem oppositeShearedCharacterRegion_eq_C_or_D
    {n : ℕ} (chi psi : degreeLE X (ZMod 2) (n + 1) → ℝ) (x : X)
    (hchiSign : ∀ a, chi a = 1 ∨ chi a = -1)
    (hpsiSign : ∀ a, psi a = 1 ∨ psi a = -1)
    (hregion : characterPairRegion X (n + 1) chi psi = .A ∨
      characterPairRegion X (n + 1) chi psi = .B)
    (hdescent : characterValuation X (leftDerivedCharacter X psi x) + 1 =
      characterValuation X psi) :
    characterPairRegion X n
        (oppositeShearedFirstCharacter X chi psi x)
        (oppositeShearedSecondCharacter X psi) = .C ∨
      characterPairRegion X n
        (oppositeShearedFirstCharacter X chi psi x)
        (oppositeShearedSecondCharacter X psi) = .D := by
  have hdata :
      ¬(characterValuation X chi = n + 2 ∧
        characterValuation X psi = n + 2) ∧
      characterValuation X chi ≠ 0 ∧
      characterValuation X psi ≠ 0 ∧
      characterValuation X psi ≤ characterValuation X chi := by
    rcases hregion with hA | hB
    · obtain ⟨hz, hchi0, hpsi0, hlt⟩ :=
        characterPairRegion_A_data X (n + 1) chi psi hA
      exact ⟨by simpa [Nat.add_assoc] using hz, hchi0, hpsi0, hlt.le⟩
    · obtain ⟨hz, hchi0, hpsi0, heq⟩ :=
        characterPairRegion_B_data X (n + 1) chi psi hB
      exact ⟨by simpa [Nat.add_assoc] using hz, hchi0, hpsi0, heq.ge⟩
  obtain ⟨hnotBoth, _, _, hpsiLeChi⟩ := hdata
  have hchiBound : characterValuation X chi ≤ n + 2 :=
    characterValuation_le_succ X chi
  have hpsiStage : characterValuation X psi ≤ n + 1 := by
    by_contra hnot
    have hpsiEq : characterValuation X psi = n + 2 := by
      have := characterValuation_le_succ X psi
      omega
    have hchiEq : characterValuation X chi = n + 2 := by omega
    exact hnotBoth ⟨hchiEq, hpsiEq⟩
  have hderivedStage :
      characterValuation X (leftDerivedCharacter X psi x) ≤ n := by
    omega
  have hderivedExists : ∃ d,
      HasDetectionAtDegree X (leftDerivedCharacter X psi x) d := by
    by_contra hnone
    have hsentinel := characterValuation_eq_succ_of_not_exists X
      (leftDerivedCharacter X psi x) hnone
    omega
  have hsecondVal :
      characterValuation X (oppositeShearedSecondCharacter X psi) =
        characterValuation X psi := by
    exact characterValuation_restrictCharacterSucc_eq X psi hpsiStage
  have hfirstRestrictionVal :
      characterValuation X (restrictCharacterSucc X chi) =
        min (characterValuation X chi) (n + 1) :=
    characterValuation_restrictCharacterSucc_eq_min X chi
  have hpsiLeRestriction :
      characterValuation X psi ≤
        characterValuation X (restrictCharacterSucc X chi) := by
    rw [hfirstRestrictionVal]
    exact Nat.le_min.mpr ⟨hpsiLeChi, hpsiStage⟩
  have hderivedLtRestriction :
      characterValuation X (leftDerivedCharacter X psi x) <
        characterValuation X (restrictCharacterSucc X chi) := by
    omega
  have hproductVal :=
    characterValuation_characterProduct_eq_right_of_lt X
      (restrictCharacterSucc X chi) (leftDerivedCharacter X psi x)
      (fun a ↦ hchiSign _)
      (fun a ↦ leftDerivedCharacter_eq_one_or_neg_one X psi x hpsiSign a)
      hderivedExists hderivedLtRestriction
  have hfirstVal :
      characterValuation X (oppositeShearedFirstCharacter X chi psi x) =
        characterValuation X (leftDerivedCharacter X psi x) := by
    exact hproductVal
  by_cases hzero : characterValuation X
      (leftDerivedCharacter X psi x) = 0
  · right
    apply characterPairRegion_eq_D_of_left_zero
    rw [hfirstVal, hzero]
  · left
    apply characterPairRegion_eq_C_of_pos_of_lt
    · rw [hfirstVal]
      omega
    · rw [hfirstVal, hsecondVal]
      omega

/-- The dual action of the `i,j` adjacent shear leaves the first character
unchanged after restriction. -/
def forwardShearedFirstCharacter
    {n : ℕ} (chi : degreeLE X (ZMod 2) (n + 1) → ℝ) :
    degreeLE X (ZMod 2) n → ℝ :=
  restrictCharacterSucc X chi

/-- The same shear multiplies the restricted second character by the
generator-derived first character.  It is the coordinate swap of the
opposite-shear formula above. -/
def forwardShearedSecondCharacter
    {n : ℕ} (chi psi : degreeLE X (ZMod 2) (n + 1) → ℝ) (x : X) :
    degreeLE X (ZMod 2) n → ℝ :=
  oppositeShearedFirstCharacter X psi chi x

/-- Kassabov's symmetric valuation-transport claim: a pair in `C ∪ B`,
sheared using a leading generator of its first character, lands in `A ∪ D`. -/
theorem forwardShearedCharacterRegion_eq_A_or_D
    {n : ℕ} (chi psi : degreeLE X (ZMod 2) (n + 1) → ℝ) (x : X)
    (hchiSign : ∀ a, chi a = 1 ∨ chi a = -1)
    (hpsiSign : ∀ a, psi a = 1 ∨ psi a = -1)
    (hregion : characterPairRegion X (n + 1) chi psi = .C ∨
      characterPairRegion X (n + 1) chi psi = .B)
    (hdescent : characterValuation X (leftDerivedCharacter X chi x) + 1 =
      characterValuation X chi) :
    characterPairRegion X n
        (forwardShearedFirstCharacter X chi)
        (forwardShearedSecondCharacter X chi psi x) = .A ∨
      characterPairRegion X n
        (forwardShearedFirstCharacter X chi)
        (forwardShearedSecondCharacter X chi psi x) = .D := by
  have hswap : characterPairRegion X (n + 1) psi chi = .A ∨
      characterPairRegion X (n + 1) psi chi = .B := by
    rcases hregion with hC | hB
    · left
      obtain ⟨_, hchi0, _, hlt⟩ :=
        characterPairRegion_C_data X (n + 1) chi psi hC
      exact characterPairRegion_eq_A_of_pos_of_lt X (n + 1) psi chi
        (Nat.pos_of_ne_zero hchi0) hlt
    · right
      obtain ⟨hz, hchi0, hpsi0, heq⟩ :=
        characterPairRegion_B_data X (n + 1) chi psi hB
      apply characterPairRegion_eq_B_of_data X (n + 1) psi chi
      · intro hboth
        exact hz ⟨hboth.2, hboth.1⟩
      · exact hpsi0
      · exact hchi0
      · exact heq.symm
  have hout := oppositeShearedCharacterRegion_eq_C_or_D X psi chi x
    hpsiSign hchiSign hswap hdescent
  rcases hout with hC | hD
  · left
    obtain ⟨_, hq0, _, hlt⟩ := characterPairRegion_C_data X n
      (oppositeShearedFirstCharacter X psi chi x)
      (oppositeShearedSecondCharacter X chi) hC
    exact characterPairRegion_eq_A_of_pos_of_lt X n
      (forwardShearedFirstCharacter X chi)
      (forwardShearedSecondCharacter X chi psi x)
      (Nat.pos_of_ne_zero hq0) hlt
  · right
    rcases characterPairRegion_D_data X n
        (oppositeShearedFirstCharacter X psi chi x)
        (oppositeShearedSecondCharacter X chi) hD with hq | hr
    · exact characterPairRegion_eq_D_of_right_zero X n
        (forwardShearedFirstCharacter X chi)
        (forwardShearedSecondCharacter X chi psi x) hq
    · exact characterPairRegion_eq_D_of_left_zero X n
        (forwardShearedFirstCharacter X chi)
        (forwardShearedSecondCharacter X chi psi x) hr

/-- Every pair in `A ∪ B` has a genuine leading generator for its second
character; the total sentinel branch of `leastLeadingGeneratorIndex` is
therefore impossible on this region. -/
theorem secondLeadingGeneratorIndexSet_nonempty_of_A_or_B
    {n : ℕ} (chi psi : degreeLE X (ZMod 2) (n + 1) → ℝ)
    (hregion : characterPairRegion X (n + 1) chi psi = .A ∨
      characterPairRegion X (n + 1) chi psi = .B) :
    (leadingGeneratorIndexSet X psi).Nonempty := by
  have hdata :
      ¬(characterValuation X chi = n + 2 ∧
        characterValuation X psi = n + 2) ∧
      characterValuation X psi ≠ 0 ∧
      characterValuation X psi ≤ characterValuation X chi := by
    rcases hregion with hA | hB
    · obtain ⟨hz, _, hpsi0, hlt⟩ :=
        characterPairRegion_A_data X (n + 1) chi psi hA
      exact ⟨by simpa [Nat.add_assoc] using hz, hpsi0, hlt.le⟩
    · obtain ⟨hz, _, hpsi0, heq⟩ :=
        characterPairRegion_B_data X (n + 1) chi psi hB
      exact ⟨by simpa [Nat.add_assoc] using hz, hpsi0, heq.ge⟩
  obtain ⟨hnotBoth, hpsi0, hpsiLeChi⟩ := hdata
  have hchiBound : characterValuation X chi ≤ n + 2 :=
    characterValuation_le_succ X chi
  have hpsiStage : characterValuation X psi ≤ n + 1 := by
    by_contra hnot
    have hpsiEq : characterValuation X psi = n + 2 := by
      have := characterValuation_le_succ X psi
      omega
    have hchiEq : characterValuation X chi = n + 2 := by omega
    exact hnotBoth ⟨hchiEq, hpsiEq⟩
  have hExists : ∃ d, HasDetectionAtDegree X psi d := by
    by_contra hnone
    have hsentinel := characterValuation_eq_succ_of_not_exists X psi hnone
    omega
  exact leadingGeneratorIndexSet_nonempty X psi hExists
    (Nat.pos_of_ne_zero hpsi0)

/-- Symmetrically, every pair in `C ∪ B` has a genuine leading generator for
its first character. -/
theorem firstLeadingGeneratorIndexSet_nonempty_of_C_or_B
    {n : ℕ} (chi psi : degreeLE X (ZMod 2) (n + 1) → ℝ)
    (hregion : characterPairRegion X (n + 1) chi psi = .C ∨
      characterPairRegion X (n + 1) chi psi = .B) :
    (leadingGeneratorIndexSet X chi).Nonempty := by
  have hswap : characterPairRegion X (n + 1) psi chi = .A ∨
      characterPairRegion X (n + 1) psi chi = .B := by
    rcases hregion with hC | hB
    · left
      obtain ⟨_, hchi0, _, hlt⟩ :=
        characterPairRegion_C_data X (n + 1) chi psi hC
      exact characterPairRegion_eq_A_of_pos_of_lt X (n + 1) psi chi
        (Nat.pos_of_ne_zero hchi0) hlt
    · right
      obtain ⟨hz, hchi0, hpsi0, heq⟩ :=
        characterPairRegion_B_data X (n + 1) chi psi hB
      apply characterPairRegion_eq_B_of_data X (n + 1) psi chi
      · intro hboth
        exact hz ⟨hboth.2, hboth.1⟩
      · exact hpsi0
      · exact hchi0
      · exact heq.symm
  exact secondLeadingGeneratorIndexSet_nonempty_of_A_or_B X psi chi hswap

/-- Classify a finite-plane sign assignment by its two character valuations. -/
noncomputable def planeCharacterRegion
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool) :
    ValuationRegion :=
  characterPairRegion X n
    (firstCoefficientEigenvalue X i j k hij hik hjk n sign)
    (secondCoefficientEigenvalue X i j k hij hik hjk n sign)

/-- The finite set of sign assignments in one valuation region. -/
noncomputable def planeRegionSignSet
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (region : ValuationRegion) :
    Finset (Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool) :=
  Finset.univ.filter fun sign ↦
    planeCharacterRegion X i j k hij hik hjk n sign = region

/-- All finite-plane signs outside the all-trivial character region. -/
noncomputable def planeNonzeroRegionSignSet
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ) :
    Finset (Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool) :=
  Finset.univ.filter fun sign ↦
    planeCharacterRegion X i j k hij hik hjk n sign ≠ .zero

theorem planeNonzeroRegionSignSet_eq_union
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ) :
    planeNonzeroRegionSignSet X i j k hij hik hjk n =
      ((planeRegionSignSet X i j k hij hik hjk n .A ∪
          planeRegionSignSet X i j k hij hik hjk n .B) ∪
        planeRegionSignSet X i j k hij hik hjk n .C) ∪
      planeRegionSignSet X i j k hij hik hjk n .D := by
  classical
  ext sign
  simp only [planeNonzeroRegionSignSet, planeRegionSignSet,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  cases planeCharacterRegion X i j k hij hik hjk n sign <;> simp

theorem planeCharacterRegion_const_true_eq_zero
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ) :
    planeCharacterRegion X i j k hij hik hjk n (fun _ ↦ true) = .zero := by
  unfold planeCharacterRegion
  apply (characterPairRegion_eq_zero_iff X n _ _).2
  constructor
  · apply characterValuation_eq_succ_of_not_exists
    rintro ⟨d, w, _hwd, _hwn, hneg⟩
    simp [firstCoefficientEigenvalue, planeEigenvalue] at hneg
    norm_num at hneg
  · apply characterValuation_eq_succ_of_not_exists
    rintro ⟨d, w, _hwd, _hwn, hneg⟩
    simp [secondCoefficientEigenvalue, planeEigenvalue] at hneg
    norm_num at hneg

theorem sign_ne_const_true_of_mem_planeNonzeroRegionSignSet
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool)
    (hsign : sign ∈ planeNonzeroRegionSignSet X i j k hij hik hjk n) :
    sign ≠ fun _ ↦ true := by
  intro htrue
  subst sign
  simp only [planeNonzeroRegionSignSet, Finset.mem_filter, Finset.mem_univ,
    true_and] at hsign
  exact hsign (planeCharacterRegion_const_true_eq_zero
    X i j k hij hik hjk n)

/-- A binary assignment on an exhaustive finite plane is a genuine group
character exactly when its assigned eigenvalues are multiplicative.  This is
an algebraic validity condition, not a certificate containing any analytic or
target-region conclusion. -/
def IsPlaneCharacterSign
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool) : Prop :=
  ∀ g h : Plane X i j k hij hik hjk n,
    planeEigenvalue X i j k hij hik hjk n sign (g * h) =
      planeEigenvalue X i j k hij hik hjk n sign g *
        planeEigenvalue X i j k hij hik hjk n sign h

/-- The `q`-th least-leading-generator fiber of the next-stage `A ∪ B`
characters, using the second coefficient character as in Kassabov's claim. -/
noncomputable def planeABLeadingSignSet
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (q : Fin (Fintype.card X)) :
    Finset (Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool) :=
  Finset.univ.filter fun sign ↦
    (planeCharacterRegion X i j k hij hik hjk (n + 1) sign = .A ∨
      planeCharacterRegion X i j k hij hik hjk (n + 1) sign = .B) ∧
    leastLeadingGeneratorIndex X
      (secondCoefficientEigenvalue X i j k hij hik hjk (n + 1) sign) = q.val

/-- The symmetric least-leading-generator fiber of `C ∪ B`, using the first
coefficient character. -/
noncomputable def planeCBLeadingSignSet
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (q : Fin (Fintype.card X)) :
    Finset (Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool) :=
  Finset.univ.filter fun sign ↦
    (planeCharacterRegion X i j k hij hik hjk (n + 1) sign = .C ∨
      planeCharacterRegion X i j k hij hik hjk (n + 1) sign = .B) ∧
    leastLeadingGeneratorIndex X
      (firstCoefficientEigenvalue X i j k hij hik hjk (n + 1) sign) = q.val

theorem planeABLeadingSignSet_pairwise_disjoint
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ) :
    Pairwise (fun q r : Fin (Fintype.card X) ↦
      Disjoint (planeABLeadingSignSet X i j k hij hik hjk n q)
        (planeABLeadingSignSet X i j k hij hik hjk n r)) := by
  intro q r hqr
  rw [Finset.disjoint_left]
  intro sign hq hr
  simp only [planeABLeadingSignSet, Finset.mem_filter, Finset.mem_univ,
    true_and] at hq hr
  apply hqr
  apply Fin.ext
  exact hq.2.symm.trans hr.2

theorem planeCBLeadingSignSet_pairwise_disjoint
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ) :
    Pairwise (fun q r : Fin (Fintype.card X) ↦
      Disjoint (planeCBLeadingSignSet X i j k hij hik hjk n q)
        (planeCBLeadingSignSet X i j k hij hik hjk n r)) := by
  intro q r hqr
  rw [Finset.disjoint_left]
  intro sign hq hr
  simp only [planeCBLeadingSignSet, Finset.mem_filter, Finset.mem_univ,
    true_and] at hq hr
  apply hqr
  apply Fin.ext
  exact hq.2.symm.trans hr.2

/-- The least-generator fibers are an exact partition of all `A ∪ B` sign
assignments; no sentinel fiber remains on this region. -/
theorem biUnion_planeABLeadingSignSet
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ) :
    Finset.univ.biUnion (planeABLeadingSignSet X i j k hij hik hjk n) =
      planeRegionSignSet X i j k hij hik hjk (n + 1) .A ∪
        planeRegionSignSet X i j k hij hik hjk (n + 1) .B := by
  ext sign
  constructor
  · intro h
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at h
    obtain ⟨q, hq⟩ := h
    simp only [planeABLeadingSignSet, Finset.mem_filter, Finset.mem_univ,
      true_and] at hq
    have hregion := hq.1
    simpa [planeRegionSignSet] using hregion
  · intro h
    have hregion :
        planeCharacterRegion X i j k hij hik hjk (n + 1) sign = .A ∨
        planeCharacterRegion X i j k hij hik hjk (n + 1) sign = .B := by
      simpa [planeRegionSignSet] using h
    have hnonempty := secondLeadingGeneratorIndexSet_nonempty_of_A_or_B X
      (firstCoefficientEigenvalue X i j k hij hik hjk (n + 1) sign)
      (secondCoefficientEigenvalue X i j k hij hik hjk (n + 1) sign)
      hregion
    let q : Fin (Fintype.card X) :=
      ⟨leastLeadingGeneratorIndex X
          (secondCoefficientEigenvalue X i j k hij hik hjk (n + 1) sign),
        leastLeadingGeneratorIndex_lt_card X _ hnonempty⟩
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    refine ⟨q, ?_⟩
    simp only [planeABLeadingSignSet, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨hregion, rfl⟩

/-- The symmetric least-generator fibers exactly partition `C ∪ B`. -/
theorem biUnion_planeCBLeadingSignSet
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ) :
    Finset.univ.biUnion (planeCBLeadingSignSet X i j k hij hik hjk n) =
      planeRegionSignSet X i j k hij hik hjk (n + 1) .C ∪
        planeRegionSignSet X i j k hij hik hjk (n + 1) .B := by
  ext sign
  constructor
  · intro h
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at h
    obtain ⟨q, hq⟩ := h
    simp only [planeCBLeadingSignSet, Finset.mem_filter, Finset.mem_univ,
      true_and] at hq
    have hregion := hq.1
    simpa [planeRegionSignSet] using hregion
  · intro h
    have hregion :
        planeCharacterRegion X i j k hij hik hjk (n + 1) sign = .C ∨
        planeCharacterRegion X i j k hij hik hjk (n + 1) sign = .B := by
      simpa [planeRegionSignSet] using h
    have hnonempty := firstLeadingGeneratorIndexSet_nonempty_of_C_or_B X
      (firstCoefficientEigenvalue X i j k hij hik hjk (n + 1) sign)
      (secondCoefficientEigenvalue X i j k hij hik hjk (n + 1) sign)
      hregion
    let q : Fin (Fintype.card X) :=
      ⟨leastLeadingGeneratorIndex X
          (firstCoefficientEigenvalue X i j k hij hik hjk (n + 1) sign),
        leastLeadingGeneratorIndex_lt_card X _ hnonempty⟩
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    refine ⟨q, ?_⟩
    simp only [planeCBLeadingSignSet, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨hregion, rfl⟩

/-- Summation over `A ∪ B` is exactly summation over its disjoint canonical
leading-generator fibers. -/
theorem sum_planeABLeadingSignSet
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (f : (Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool) → ℝ) :
    ∑ sign ∈ (planeRegionSignSet X i j k hij hik hjk (n + 1) .A ∪
        planeRegionSignSet X i j k hij hik hjk (n + 1) .B), f sign =
      ∑ q : Fin (Fintype.card X),
        ∑ sign ∈ planeABLeadingSignSet X i j k hij hik hjk n q, f sign := by
  rw [← biUnion_planeABLeadingSignSet X i j k hij hik hjk n]
  have hpair :
      ((Finset.univ : Finset (Fin (Fintype.card X))) : Set _).PairwiseDisjoint
        (planeABLeadingSignSet X i j k hij hik hjk n) := by
    intro q _ r _ hqr
    exact planeABLeadingSignSet_pairwise_disjoint X i j k hij hik hjk n hqr
  exact Finset.sum_biUnion hpair

/-- The symmetric exact summation over the disjoint `C ∪ B` fibers. -/
theorem sum_planeCBLeadingSignSet
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (f : (Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool) → ℝ) :
    ∑ sign ∈ (planeRegionSignSet X i j k hij hik hjk (n + 1) .C ∪
        planeRegionSignSet X i j k hij hik hjk (n + 1) .B), f sign =
      ∑ q : Fin (Fintype.card X),
        ∑ sign ∈ planeCBLeadingSignSet X i j k hij hik hjk n q, f sign := by
  rw [← biUnion_planeCBLeadingSignSet X i j k hij hik hjk n]
  have hpair :
      ((Finset.univ : Finset (Fin (Fintype.card X))) : Set _).PairwiseDisjoint
        (planeCBLeadingSignSet X i j k hij hik hjk n) := by
    intro q _ r _ hqr
    exact planeCBLeadingSignSet_pairwise_disjoint X i j k hij hik hjk n hqr
  exact Finset.sum_biUnion hpair

/-- Every `A ∪ B` least-generator fiber is carried into `C ∪ D` by the
opposite shear indexed by that fiber. -/
theorem planeABLeadingSignSet_region_transport
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (q : Fin (Fintype.card X))
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool)
    (hsign : sign ∈ planeABLeadingSignSet X i j k hij hik hjk n q) :
    characterPairRegion X n
        (oppositeShearedFirstCharacter X
          (firstCoefficientEigenvalue X i j k hij hik hjk (n + 1) sign)
          (secondCoefficientEigenvalue X i j k hij hik hjk (n + 1) sign)
          (generatorEnumeration X q))
        (oppositeShearedSecondCharacter X
          (secondCoefficientEigenvalue X i j k hij hik hjk (n + 1) sign)) = .C ∨
      characterPairRegion X n
        (oppositeShearedFirstCharacter X
          (firstCoefficientEigenvalue X i j k hij hik hjk (n + 1) sign)
          (secondCoefficientEigenvalue X i j k hij hik hjk (n + 1) sign)
          (generatorEnumeration X q))
        (oppositeShearedSecondCharacter X
          (secondCoefficientEigenvalue X i j k hij hik hjk (n + 1) sign)) = .D := by
  simp only [planeABLeadingSignSet, Finset.mem_filter, Finset.mem_univ,
    true_and] at hsign
  obtain ⟨hregion, hindex⟩ := hsign
  have hnonempty := secondLeadingGeneratorIndexSet_nonempty_of_A_or_B X
    (firstCoefficientEigenvalue X i j k hij hik hjk (n + 1) sign)
    (secondCoefficientEigenvalue X i j k hij hik hjk (n + 1) sign)
    hregion
  let q0 : Fin (Fintype.card X) :=
    ⟨leastLeadingGeneratorIndex X
        (secondCoefficientEigenvalue X i j k hij hik hjk (n + 1) sign),
      leastLeadingGeneratorIndex_lt_card X _ hnonempty⟩
  have hq0 : q0 = q := by
    apply Fin.ext
    exact hindex
  have hdescent := leastLeadingGeneratorIndex_spec X
    (secondCoefficientEigenvalue X i j k hij hik hjk (n + 1) sign)
    hnonempty
  change characterValuation X
      (leftDerivedCharacter X
        (secondCoefficientEigenvalue X i j k hij hik hjk (n + 1) sign)
        (generatorEnumeration X q0)) + 1 =
    characterValuation X
      (secondCoefficientEigenvalue X i j k hij hik hjk (n + 1) sign) at hdescent
  rw [hq0] at hdescent
  exact oppositeShearedCharacterRegion_eq_C_or_D X
    (firstCoefficientEigenvalue X i j k hij hik hjk (n + 1) sign)
    (secondCoefficientEigenvalue X i j k hij hik hjk (n + 1) sign)
    (generatorEnumeration X q)
    (firstCoefficientEigenvalue_eq_one_or_neg_one
      X i j k hij hik hjk (n + 1) sign)
    (secondCoefficientEigenvalue_eq_one_or_neg_one
      X i j k hij hik hjk (n + 1) sign)
    hregion hdescent

/-- Every `C ∪ B` least-generator fiber is carried into `A ∪ D` by the
forward shear indexed by that fiber. -/
theorem planeCBLeadingSignSet_region_transport
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (q : Fin (Fintype.card X))
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool)
    (hsign : sign ∈ planeCBLeadingSignSet X i j k hij hik hjk n q) :
    characterPairRegion X n
        (forwardShearedFirstCharacter X
          (firstCoefficientEigenvalue X i j k hij hik hjk (n + 1) sign))
        (forwardShearedSecondCharacter X
          (firstCoefficientEigenvalue X i j k hij hik hjk (n + 1) sign)
          (secondCoefficientEigenvalue X i j k hij hik hjk (n + 1) sign)
          (generatorEnumeration X q)) = .A ∨
      characterPairRegion X n
        (forwardShearedFirstCharacter X
          (firstCoefficientEigenvalue X i j k hij hik hjk (n + 1) sign))
        (forwardShearedSecondCharacter X
          (firstCoefficientEigenvalue X i j k hij hik hjk (n + 1) sign)
          (secondCoefficientEigenvalue X i j k hij hik hjk (n + 1) sign)
          (generatorEnumeration X q)) = .D := by
  simp only [planeCBLeadingSignSet, Finset.mem_filter, Finset.mem_univ,
    true_and] at hsign
  obtain ⟨hregion, hindex⟩ := hsign
  have hnonempty := firstLeadingGeneratorIndexSet_nonempty_of_C_or_B X
    (firstCoefficientEigenvalue X i j k hij hik hjk (n + 1) sign)
    (secondCoefficientEigenvalue X i j k hij hik hjk (n + 1) sign)
    hregion
  let q0 : Fin (Fintype.card X) :=
    ⟨leastLeadingGeneratorIndex X
        (firstCoefficientEigenvalue X i j k hij hik hjk (n + 1) sign),
      leastLeadingGeneratorIndex_lt_card X _ hnonempty⟩
  have hq0 : q0 = q := by
    apply Fin.ext
    exact hindex
  have hdescent := leastLeadingGeneratorIndex_spec X
    (firstCoefficientEigenvalue X i j k hij hik hjk (n + 1) sign)
    hnonempty
  change characterValuation X
      (leftDerivedCharacter X
        (firstCoefficientEigenvalue X i j k hij hik hjk (n + 1) sign)
        (generatorEnumeration X q0)) + 1 =
    characterValuation X
      (firstCoefficientEigenvalue X i j k hij hik hjk (n + 1) sign) at hdescent
  rw [hq0] at hdescent
  exact forwardShearedCharacterRegion_eq_A_or_D X
    (firstCoefficientEigenvalue X i j k hij hik hjk (n + 1) sign)
    (secondCoefficientEigenvalue X i j k hij hik hjk (n + 1) sign)
    (generatorEnumeration X q)
    (firstCoefficientEigenvalue_eq_one_or_neg_one
      X i j k hij hik hjk (n + 1) sign)
    (secondCoefficientEigenvalue_eq_one_or_neg_one
      X i j k hij hik hjk (n + 1) sign)
    hregion hdescent

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem isPlaneCharacterSign_of_component_ne_zero
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool)
    (z : E) (hv : planeComponent X i j k hij hik hjk n rho sign z ≠ 0) :
    IsPlaneCharacterSign X i j k hij hik hjk n sign := by
  intro g h
  exact planeEigenvalue_mul_of_component_ne_zero X i j k hij hik hjk n
    rho sign z hv g h

/-- Invalid binary assignments carry zero Fourier mass in every orthogonal
representation and for every vector. -/
theorem planeComponent_eq_zero_of_not_isPlaneCharacterSign
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool)
    (z : E) (hinvalid : ¬ IsPlaneCharacterSign X i j k hij hik hjk n sign) :
    planeComponent X i j k hij hik hjk n rho sign z = 0 := by
  by_contra hv
  exact hinvalid (isPlaneCharacterSign_of_component_ne_zero
    X i j k hij hik hjk n rho sign z hv)

/-- The genuine multiplicative characters contained in an arbitrary finite
collection of plane signs. -/
noncomputable def planeValidSignSubset
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (signs : Finset (Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool)) :
    Finset (Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool) := by
  classical
  exact signs.filter (IsPlaneCharacterSign X i j k hij hik hjk n)

/-- Filtering an arbitrary finite collection of plane signs to the genuine
multiplicative characters preserves its Fourier mass exactly. -/
theorem sum_norm_planeSignSet_eq_filter_valid
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (signs : Finset (Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool))
    (z : E) :
    (∑ sign ∈ signs,
        ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2) =
      ∑ sign ∈ planeValidSignSubset X i j k hij hik hjk n signs,
        ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2 := by
  classical
  rw [planeValidSignSubset]
  induction signs using Finset.induction_on with
  | empty => simp
  | @insert sign signs hnot ih =>
      by_cases hvalid : IsPlaneCharacterSign X i j k hij hik hjk n sign
      · rw [Finset.filter_insert]
        simp [hnot, hvalid, ih]
      · have hzero := planeComponent_eq_zero_of_not_isPlaneCharacterSign
          X i j k hij hik hjk n rho sign z hvalid
        rw [Finset.filter_insert]
        simp [hnot, hvalid, hzero, ih]

/-- Ordinary plane restriction is exactly coefficient-character restriction
on the first root coordinate. -/
theorem firstCoefficientEigenvalue_succRestriction
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (fineSign : Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool) :
    firstCoefficientEigenvalue X i j k hij hik hjk n
        (fun q ↦ fineSign (planeSuccIndex X i j k hij hik hjk n q)) =
      restrictCharacterSucc X
        (firstCoefficientEigenvalue X i j k hij hik hjk (n + 1) fineSign) := by
  funext a
  rw [firstCoefficientEigenvalue, planeEigenvalue_succRestriction]
  have hsucc : planeSucc X i j k hij hik hjk n
      (firstCoordinate X i j k hij hik hjk n a) =
      firstCoordinate X i j k hij hik hjk (n + 1) (coefficientSucc X a) := by
    apply Subtype.ext
    rfl
  rw [hsucc]
  rfl

/-- Ordinary plane restriction is exactly coefficient-character restriction
on the second root coordinate. -/
theorem secondCoefficientEigenvalue_succRestriction
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (fineSign : Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool) :
    secondCoefficientEigenvalue X i j k hij hik hjk n
        (fun q ↦ fineSign (planeSuccIndex X i j k hij hik hjk n q)) =
      restrictCharacterSucc X
        (secondCoefficientEigenvalue X i j k hij hik hjk (n + 1) fineSign) := by
  funext b
  rw [secondCoefficientEigenvalue, planeEigenvalue_succRestriction]
  have hsucc : planeSucc X i j k hij hik hjk n
      (secondCoordinate X i j k hij hik hjk n b) =
      secondCoordinate X i j k hij hik hjk (n + 1) (coefficientSucc X b) := by
    apply Subtype.ext
    rfl
  rw [hsucc]
  rfl

/-- First-coordinate valuation under ordinary restriction is truncation at
the coarse sentinel. -/
theorem firstCoefficientValuation_succRestriction_eq_min
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (fineSign : Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool) :
    firstCoefficientValuation X i j k hij hik hjk n
        (fun q ↦ fineSign (planeSuccIndex X i j k hij hik hjk n q)) =
      min (firstCoefficientValuation X i j k hij hik hjk (n + 1) fineSign)
        (n + 1) := by
  unfold firstCoefficientValuation
  rw [firstCoefficientEigenvalue_succRestriction]
  exact characterValuation_restrictCharacterSucc_eq_min X _

/-- Second-coordinate valuation obeys the same exact truncation law. -/
theorem secondCoefficientValuation_succRestriction_eq_min
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (fineSign : Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool) :
    secondCoefficientValuation X i j k hij hik hjk n
        (fun q ↦ fineSign (planeSuccIndex X i j k hij hik hjk n q)) =
      min (secondCoefficientValuation X i j k hij hik hjk (n + 1) fineSign)
        (n + 1) := by
  unfold secondCoefficientValuation
  rw [secondCoefficientEigenvalue_succRestriction]
  exact characterValuation_restrictCharacterSucc_eq_min X _

/-- Away from characters first detected in the newly added top degree,
ordinary restriction preserves the valuation region exactly.  A still-trivial
fine character (valuation `n+2`) remains the coarse sentinel (`n+1`), so it is
correctly included in this stability statement. -/
theorem characterPairRegion_restrictCharacterSucc_eq_of_ne_top
    (n : ℕ) (chi psi : degreeLE X (ZMod 2) (n + 1) → ℝ)
    (hchi : characterValuation X chi ≠ n + 1)
    (hpsi : characterValuation X psi ≠ n + 1) :
    characterPairRegion X n (restrictCharacterSucc X chi)
        (restrictCharacterSucc X psi) =
      characterPairRegion X (n + 1) chi psi := by
  have hchiBound := characterValuation_le_succ X chi
  have hpsiBound := characterValuation_le_succ X psi
  by_cases hchiLe : characterValuation X chi ≤ n
  · have hchiRestrict :
        characterValuation X (restrictCharacterSucc X chi) =
          characterValuation X chi := by
      rw [characterValuation_restrictCharacterSucc_eq_min,
        min_eq_left (hchiLe.trans (Nat.le_succ n))]
    by_cases hpsiLe : characterValuation X psi ≤ n
    · have hpsiRestrict :
          characterValuation X (restrictCharacterSucc X psi) =
            characterValuation X psi := by
        rw [characterValuation_restrictCharacterSucc_eq_min,
          min_eq_left (hpsiLe.trans (Nat.le_succ n))]
      unfold characterPairRegion
      dsimp only
      rw [hchiRestrict, hpsiRestrict]
      have hcoarseZero : ¬ (characterValuation X chi = n + 1 ∧
          characterValuation X psi = n + 1) := by omega
      have hfineZero : ¬ (characterValuation X chi = n + 1 + 1 ∧
          characterValuation X psi = n + 1 + 1) := by omega
      rw [if_neg hcoarseZero, if_neg hfineZero]
    · have hpsiTop : characterValuation X psi = n + 2 := by omega
      have hpsiRestrict :
          characterValuation X (restrictCharacterSucc X psi) = n + 1 := by
        rw [characterValuation_restrictCharacterSucc_eq_min, hpsiTop]
        omega
      unfold characterPairRegion
      dsimp only
      rw [hchiRestrict, hpsiRestrict, hpsiTop]
      have hcoarseZero : ¬ (characterValuation X chi = n + 1 ∧
          n + 1 = n + 1) := by omega
      have hfineZero : ¬ (characterValuation X chi = n + 1 + 1 ∧
          n + 2 = n + 1 + 1) := by omega
      rw [if_neg hcoarseZero, if_neg hfineZero]
      by_cases hchiZero : characterValuation X chi = 0
      · simp [hchiZero]
      · have hcoarseLt : ¬ n + 1 < characterValuation X chi := by omega
        have hcoarseEq : characterValuation X chi ≠ n + 1 := by omega
        have hfineLt : ¬ n + 2 < characterValuation X chi := by omega
        have hfineEq : characterValuation X chi ≠ n + 2 := by omega
        simp [hchiZero, hcoarseLt, hcoarseEq, hfineLt, hfineEq]
  · have hchiTop : characterValuation X chi = n + 2 := by omega
    have hchiRestrict :
        characterValuation X (restrictCharacterSucc X chi) = n + 1 := by
      rw [characterValuation_restrictCharacterSucc_eq_min, hchiTop]
      omega
    by_cases hpsiLe : characterValuation X psi ≤ n
    · have hpsiRestrict :
          characterValuation X (restrictCharacterSucc X psi) =
            characterValuation X psi := by
        rw [characterValuation_restrictCharacterSucc_eq_min,
          min_eq_left (hpsiLe.trans (Nat.le_succ n))]
      unfold characterPairRegion
      dsimp only
      rw [hchiRestrict, hpsiRestrict, hchiTop]
      have hcoarseZero : ¬ (n + 1 = n + 1 ∧
          characterValuation X psi = n + 1) := by omega
      have hfineZero : ¬ (n + 2 = n + 1 + 1 ∧
          characterValuation X psi = n + 1 + 1) := by omega
      rw [if_neg hcoarseZero, if_neg hfineZero]
      by_cases hpsiZero : characterValuation X psi = 0
      · simp [hpsiZero]
      · have hcoarseLt : characterValuation X psi < n + 1 := by omega
        have hfineLt : characterValuation X psi < n + 2 := by omega
        simp [hpsiZero, hcoarseLt, hfineLt]
    · have hpsiTop : characterValuation X psi = n + 2 := by omega
      have hpsiRestrict :
          characterValuation X (restrictCharacterSucc X psi) = n + 1 := by
        rw [characterValuation_restrictCharacterSucc_eq_min, hpsiTop]
        omega
      unfold characterPairRegion
      dsimp only
      rw [hchiRestrict, hpsiRestrict, hchiTop, hpsiTop]
      simp

/-- Plane-region specialization of the preceding numerical stability lemma. -/
theorem planeCharacterRegion_succRestriction_eq_of_ne_top
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (fineSign : Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool)
    (hfirst : firstCoefficientValuation X i j k hij hik hjk (n + 1) fineSign ≠
      n + 1)
    (hsecond : secondCoefficientValuation X i j k hij hik hjk (n + 1) fineSign ≠
      n + 1) :
    planeCharacterRegion X i j k hij hik hjk n
        (fun q ↦ fineSign (planeSuccIndex X i j k hij hik hjk n q)) =
      planeCharacterRegion X i j k hij hik hjk (n + 1) fineSign := by
  unfold planeCharacterRegion
  rw [firstCoefficientEigenvalue_succRestriction,
    secondCoefficientEigenvalue_succRestriction]
  exact characterPairRegion_restrictCharacterSucc_eq_of_ne_top X n _ _
    hfirst hsecond

/-- Sign assignments whose first coefficient character is trivial throughout
the current finite stage. -/
noncomputable def planeFirstTrivialSignSet
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ) :
    Finset (Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool) :=
  Finset.univ.filter fun sign ↦
    firstCoefficientValuation X i j k hij hik hjk n sign = n + 1

/-- Sign assignments whose second coefficient character is trivial
throughout the current finite stage. -/
noncomputable def planeSecondTrivialSignSet
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ) :
    Finset (Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool) :=
  Finset.univ.filter fun sign ↦
    secondCoefficientValuation X i j k hij hik hjk n sign = n + 1

/-- Fine-stage signs whose first character is detected for the first time in
the top word degree. -/
noncomputable def planeFirstTopBoundarySignSet
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ) :
    Finset (Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool) :=
  Finset.univ.filter fun sign ↦
    firstCoefficientValuation X i j k hij hik hjk n sign = n

/-- Fine-stage signs whose second character is detected for the first time in
the top word degree. -/
noncomputable def planeSecondTopBoundarySignSet
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ) :
    Finset (Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool) :=
  Finset.univ.filter fun sign ↦
    secondCoefficientValuation X i j k hij hik hjk n sign = n

/-- Valid fine signs refining a union of two coarse valuation regions either
remain in the same region union or lie on one of the two new top-degree
layers. -/
theorem filter_valid_fineRestriction_regionUnion_subset
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (r s : ValuationRegion) :
    planeValidSignSubset X i j k hij hik hjk (n + 1)
      (fineRestrictionSignSet
        (Nat.card (Plane X i j k hij hik hjk (n + 1)))
        (Nat.card (Plane X i j k hij hik hjk n))
        (planeSuccIndex X i j k hij hik hjk n)
        (planeRegionSignSet X i j k hij hik hjk n r ∪
          planeRegionSignSet X i j k hij hik hjk n s)) ⊆
      (planeRegionSignSet X i j k hij hik hjk (n + 1) r ∪
          planeRegionSignSet X i j k hij hik hjk (n + 1) s) ∪
        (planeFirstTopBoundarySignSet X i j k hij hik hjk (n + 1) ∪
          planeSecondTopBoundarySignSet X i j k hij hik hjk (n + 1)) := by
  classical
  intro sign hsign
  rw [planeValidSignSubset] at hsign
  obtain ⟨hpre, _hvalid⟩ := Finset.mem_filter.mp hsign
  by_cases hfirst :
      firstCoefficientValuation X i j k hij hik hjk (n + 1) sign = n + 1
  · exact Finset.mem_union_right _
      (Finset.mem_union_left _ (by
        simpa [planeFirstTopBoundarySignSet] using hfirst))
  by_cases hsecond :
      secondCoefficientValuation X i j k hij hik hjk (n + 1) sign = n + 1
  · exact Finset.mem_union_right _
      (Finset.mem_union_right _ (by
        simpa [planeSecondTopBoundarySignSet] using hsecond))
  · have hstable := planeCharacterRegion_succRestriction_eq_of_ne_top
        X i j k hij hik hjk n sign hfirst hsecond
    have hcoarseRegions :
        planeCharacterRegion X i j k hij hik hjk n
              (fun q ↦ sign (planeSuccIndex X i j k hij hik hjk n q)) = r ∨
          planeCharacterRegion X i j k hij hik hjk n
              (fun q ↦ sign (planeSuccIndex X i j k hij hik hjk n q)) = s := by
      simpa [fineRestrictionSignSet, planeRegionSignSet] using hpre
    apply Finset.mem_union_left
      (planeFirstTopBoundarySignSet X i j k hij hik hjk (n + 1) ∪
        planeSecondTopBoundarySignSet X i j k hij hik hjk (n + 1))
    rcases hcoarseRegions with hr | hs
    · apply Finset.mem_union_left
        (planeRegionSignSet X i j k hij hik hjk (n + 1) s)
      simpa [planeRegionSignSet] using hstable.symm.trans hr
    · apply Finset.mem_union_right
        (planeRegionSignSet X i j k hij hik hjk (n + 1) r)
      simpa [planeRegionSignSet] using hstable.symm.trans hs

/-- Refining a first-coordinate-trivial stage splits exactly into the next
top-degree layer and the still-trivial next stage. -/
theorem fineRestriction_planeFirstTrivialSignSet
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) :
    fineRestrictionSignSet
        (Nat.card (Plane X i j k hij hik hjk (n + 1)))
        (Nat.card (Plane X i j k hij hik hjk n))
        (planeSuccIndex X i j k hij hik hjk n)
        (planeFirstTrivialSignSet X i j k hij hik hjk n) =
      planeFirstTopBoundarySignSet X i j k hij hik hjk (n + 1) ∪
        planeFirstTrivialSignSet X i j k hij hik hjk (n + 1) := by
  classical
  ext fineSign
  simp only [fineRestrictionSignSet, planeFirstTrivialSignSet,
    planeFirstTopBoundarySignSet, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_union]
  rw [firstCoefficientValuation_succRestriction_eq_min]
  have hbound := characterValuation_le_succ X
    (firstCoefficientEigenvalue X i j k hij hik hjk (n + 1) fineSign)
  change firstCoefficientValuation X i j k hij hik hjk (n + 1) fineSign ≤
    n + 2 at hbound
  omega

/-- The same exact refinement split for the second coordinate. -/
theorem fineRestriction_planeSecondTrivialSignSet
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) :
    fineRestrictionSignSet
        (Nat.card (Plane X i j k hij hik hjk (n + 1)))
        (Nat.card (Plane X i j k hij hik hjk n))
        (planeSuccIndex X i j k hij hik hjk n)
        (planeSecondTrivialSignSet X i j k hij hik hjk n) =
      planeSecondTopBoundarySignSet X i j k hij hik hjk (n + 1) ∪
        planeSecondTrivialSignSet X i j k hij hik hjk (n + 1) := by
  classical
  ext fineSign
  simp only [fineRestrictionSignSet, planeSecondTrivialSignSet,
    planeSecondTopBoundarySignSet, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_union]
  rw [secondCoefficientValuation_succRestriction_eq_min]
  have hbound := characterValuation_le_succ X
    (secondCoefficientEigenvalue X i j k hij hik hjk (n + 1) fineSign)
  change secondCoefficientValuation X i j k hij hik hjk (n + 1) fineSign ≤
    n + 2 at hbound
  omega

theorem planeFirstTopBoundarySignSet_disjoint_trivial
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) :
    Disjoint (planeFirstTopBoundarySignSet X i j k hij hik hjk n)
      (planeFirstTrivialSignSet X i j k hij hik hjk n) := by
  classical
  rw [Finset.disjoint_left]
  intro sign htop htrivial
  simp only [planeFirstTopBoundarySignSet, planeFirstTrivialSignSet,
    Finset.mem_filter, Finset.mem_univ, true_and] at htop htrivial
  omega

theorem planeSecondTopBoundarySignSet_disjoint_trivial
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) :
    Disjoint (planeSecondTopBoundarySignSet X i j k hij hik hjk n)
      (planeSecondTrivialSignSet X i j k hij hik hjk n) := by
  classical
  rw [Finset.disjoint_left]
  intro sign htop htrivial
  simp only [planeSecondTopBoundarySignSet, planeSecondTrivialSignSet,
    Finset.mem_filter, Finset.mem_univ, true_and] at htop htrivial
  omega

/-- Exact telescoping identity for first-coordinate trivial Fourier mass. -/
theorem sum_norm_planeFirstTrivialSignSet_sq
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    (∑ sign ∈ planeFirstTrivialSignSet X i j k hij hik hjk n,
        ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2) =
      (∑ sign ∈ planeFirstTopBoundarySignSet
          X i j k hij hik hjk (n + 1),
        ‖planeComponent X i j k hij hik hjk (n + 1) rho sign z‖ ^ 2) +
      ∑ sign ∈ planeFirstTrivialSignSet X i j k hij hik hjk (n + 1),
        ‖planeComponent X i j k hij hik hjk (n + 1) rho sign z‖ ^ 2 := by
  classical
  calc
    _ = ∑ sign ∈ fineRestrictionSignSet
          (Nat.card (Plane X i j k hij hik hjk (n + 1)))
          (Nat.card (Plane X i j k hij hik hjk n))
          (planeSuccIndex X i j k hij hik hjk n)
          (planeFirstTrivialSignSet X i j k hij hik hjk n),
        ‖planeComponent X i j k hij hik hjk (n + 1) rho sign z‖ ^ 2 :=
      (sum_norm_planeRestriction_sq X i j k hij hik hjk n rho
        (planeFirstTrivialSignSet X i j k hij hik hjk n) z).symm
    _ = ∑ sign ∈ (planeFirstTopBoundarySignSet
          X i j k hij hik hjk (n + 1) ∪
          planeFirstTrivialSignSet X i j k hij hik hjk (n + 1)),
        ‖planeComponent X i j k hij hik hjk (n + 1) rho sign z‖ ^ 2 := by
      rw [fineRestriction_planeFirstTrivialSignSet]
    _ = _ := Finset.sum_union
      (planeFirstTopBoundarySignSet_disjoint_trivial
        X i j k hij hik hjk (n + 1))

/-- Exact telescoping identity for second-coordinate trivial Fourier mass. -/
theorem sum_norm_planeSecondTrivialSignSet_sq
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    (∑ sign ∈ planeSecondTrivialSignSet X i j k hij hik hjk n,
        ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2) =
      (∑ sign ∈ planeSecondTopBoundarySignSet
          X i j k hij hik hjk (n + 1),
        ‖planeComponent X i j k hij hik hjk (n + 1) rho sign z‖ ^ 2) +
      ∑ sign ∈ planeSecondTrivialSignSet X i j k hij hik hjk (n + 1),
        ‖planeComponent X i j k hij hik hjk (n + 1) rho sign z‖ ^ 2 := by
  classical
  calc
    _ = ∑ sign ∈ fineRestrictionSignSet
          (Nat.card (Plane X i j k hij hik hjk (n + 1)))
          (Nat.card (Plane X i j k hij hik hjk n))
          (planeSuccIndex X i j k hij hik hjk n)
          (planeSecondTrivialSignSet X i j k hij hik hjk n),
        ‖planeComponent X i j k hij hik hjk (n + 1) rho sign z‖ ^ 2 :=
      (sum_norm_planeRestriction_sq X i j k hij hik hjk n rho
        (planeSecondTrivialSignSet X i j k hij hik hjk n) z).symm
    _ = ∑ sign ∈ (planeSecondTopBoundarySignSet
          X i j k hij hik hjk (n + 1) ∪
          planeSecondTrivialSignSet X i j k hij hik hjk (n + 1)),
        ‖planeComponent X i j k hij hik hjk (n + 1) rho sign z‖ ^ 2 := by
      rw [fineRestriction_planeSecondTrivialSignSet]
    _ = _ := Finset.sum_union
      (planeSecondTopBoundarySignSet_disjoint_trivial
        X i j k hij hik hjk (n + 1))

/-- Squared Fourier mass on signs whose first coefficient remains trivial at
stage `n`. -/
noncomputable def planeFirstTrivialMass
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (n : ℕ) : ℝ :=
  ∑ sign ∈ planeFirstTrivialSignSet X i j k hij hik hjk n,
    ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2

/-- The analogous second-coordinate trivial mass. -/
noncomputable def planeSecondTrivialMass
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (n : ℕ) : ℝ :=
  ∑ sign ∈ planeSecondTrivialSignSet X i j k hij hik hjk n,
    ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2

/-- First-coordinate mass newly detected in the top degree of stage `n`. -/
noncomputable def planeFirstTopBoundaryMass
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (n : ℕ) : ℝ :=
  ∑ sign ∈ planeFirstTopBoundarySignSet X i j k hij hik hjk n,
    ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2

/-- Second-coordinate mass newly detected in the top degree of stage `n`. -/
noncomputable def planeSecondTopBoundaryMass
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (n : ℕ) : ℝ :=
  ∑ sign ∈ planeSecondTopBoundarySignSet X i j k hij hik hjk n,
    ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2

/-- Squared Fourier mass in one Kassabov valuation region. -/
noncomputable def planeRegionMass
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (n : ℕ) (region : ValuationRegion) : ℝ :=
  ∑ sign ∈ planeRegionSignSet X i j k hij hik hjk n region,
    ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2

/-- Squared Fourier mass in the union of two valuation regions. -/
noncomputable def planeRegionUnionMass
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (n : ℕ) (r s : ValuationRegion) : ℝ :=
  ∑ sign ∈ (planeRegionSignSet X i j k hij hik hjk n r ∪
      planeRegionSignSet X i j k hij hik hjk n s),
    ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2

theorem planeRegionSignSet_disjoint
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (r s : ValuationRegion) (hrs : r ≠ s) :
    Disjoint (planeRegionSignSet X i j k hij hik hjk n r)
      (planeRegionSignSet X i j k hij hik hjk n s) := by
  classical
  rw [Finset.disjoint_left]
  intro sign hr hs
  simp only [planeRegionSignSet, Finset.mem_filter, Finset.mem_univ,
    true_and] at hr hs
  apply hrs
  exact hr.symm.trans hs

theorem planeRegionUnionMass_eq_add
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (n : ℕ) (r s : ValuationRegion) (hrs : r ≠ s) :
    planeRegionUnionMass X i j k hij hik hjk rho z n r s =
      planeRegionMass X i j k hij hik hjk rho z n r +
        planeRegionMass X i j k hij hik hjk rho z n s := by
  classical
  simpa [planeRegionUnionMass, planeRegionMass] using
    Finset.sum_union
      (planeRegionSignSet_disjoint X i j k hij hik hjk n r s hrs)

/-- The sum of all finite-stage Fourier components with nontrivial plane
character. -/
noncomputable def planeMovingPart
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (n : ℕ) : E :=
  ∑ sign ∈ planeNonzeroRegionSignSet X i j k hij hik hjk n,
    planeComponent X i j k hij hik hjk n rho sign z

/-- The moving-part norm is exactly the sum of the four nonzero valuation
region masses. -/
theorem norm_planeMovingPart_sq_eq_sum_regionMass
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (n : ℕ) :
    ‖planeMovingPart X i j k hij hik hjk rho z n‖ ^ 2 =
      planeRegionMass X i j k hij hik hjk rho z n .A +
        planeRegionMass X i j k hij hik hjk rho z n .B +
        planeRegionMass X i j k hij hik hjk rho z n .C +
        planeRegionMass X i j k hij hik hjk rho z n .D := by
  classical
  let A := planeRegionSignSet X i j k hij hik hjk n .A
  let B := planeRegionSignSet X i j k hij hik hjk n .B
  let C := planeRegionSignSet X i j k hij hik hjk n .C
  let D := planeRegionSignSet X i j k hij hik hjk n .D
  have hAB : Disjoint A B := by
    exact planeRegionSignSet_disjoint X i j k hij hik hjk n .A .B (by decide)
  have hAC : Disjoint A C := by
    exact planeRegionSignSet_disjoint X i j k hij hik hjk n .A .C (by decide)
  have hBC : Disjoint B C := by
    exact planeRegionSignSet_disjoint X i j k hij hik hjk n .B .C (by decide)
  have hAD : Disjoint A D := by
    exact planeRegionSignSet_disjoint X i j k hij hik hjk n .A .D (by decide)
  have hBD : Disjoint B D := by
    exact planeRegionSignSet_disjoint X i j k hij hik hjk n .B .D (by decide)
  have hCD : Disjoint C D := by
    exact planeRegionSignSet_disjoint X i j k hij hik hjk n .C .D (by decide)
  have hAB_C : Disjoint (A ∪ B) C := by
    rw [Finset.disjoint_left]
    intro sign hab hc
    rcases Finset.mem_union.mp hab with ha | hb
    · exact (Finset.disjoint_left.mp hAC) ha hc
    · exact (Finset.disjoint_left.mp hBC) hb hc
  have hABC_D : Disjoint ((A ∪ B) ∪ C) D := by
    rw [Finset.disjoint_left]
    intro sign habc hd
    rcases Finset.mem_union.mp habc with hab | hc
    · rcases Finset.mem_union.mp hab with ha | hb
      · exact (Finset.disjoint_left.mp hAD) ha hd
      · exact (Finset.disjoint_left.mp hBD) hb hd
    · exact (Finset.disjoint_left.mp hCD) hc hd
  unfold planeMovingPart
  change ‖∑ sign ∈ planeNonzeroRegionSignSet X i j k hij hik hjk n,
      iteratedPart rho (planeFamily X i j k hij hik hjk n) sign z‖ ^ 2 = _
  rw [norm_sum_iteratedPart_sq rho _ _
      (planeFamily_sq X i j k hij hik hjk n)
      (planeFamily_pairwise_commute X i j k hij hik hjk n)]
  change (∑ sign ∈ planeNonzeroRegionSignSet X i j k hij hik hjk n,
      ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2) = _
  rw [planeNonzeroRegionSignSet_eq_union]
  change (∑ sign ∈ ((A ∪ B) ∪ C) ∪ D,
      ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2) = _
  rw [Finset.sum_union hABC_D, Finset.sum_union hAB_C,
    Finset.sum_union hAB]
  rfl

theorem sign_eq_const_true_of_component_ne_zero_of_region_zero
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (n : ℕ)
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool)
    (hv : planeComponent X i j k hij hik hjk n rho sign z ≠ 0)
    (hzero : planeCharacterRegion X i j k hij hik hjk n sign = .zero) :
    sign = fun _ ↦ true := by
  let chi := firstCoefficientEigenvalue X i j k hij hik hjk n sign
  let psi := secondCoefficientEigenvalue X i j k hij hik hjk n sign
  have hvals : characterValuation X chi = n + 1 ∧
      characterValuation X psi = n + 1 := by
    exact (characterPairRegion_eq_zero_iff X n chi psi).mp hzero
  have hchiOne : ∀ a, chi a = 1 :=
    eq_one_of_characterValuation_eq_succ X chi
      (firstCoefficientEigenvalue_zero_of_component_ne_zero
        X i j k hij hik hjk n rho sign z hv)
      (firstCoefficientEigenvalue_add_of_component_ne_zero
        X i j k hij hik hjk n rho sign z hv)
      (firstCoefficientEigenvalue_eq_one_or_neg_one
        X i j k hij hik hjk n sign) hvals.1
  have hpsiOne : ∀ b, psi b = 1 :=
    eq_one_of_characterValuation_eq_succ X psi
      (secondCoefficientEigenvalue_zero_of_component_ne_zero
        X i j k hij hik hjk n rho sign z hv)
      (secondCoefficientEigenvalue_add_of_component_ne_zero
        X i j k hij hik hjk n rho sign z hv)
      (secondCoefficientEigenvalue_eq_one_or_neg_one
        X i j k hij hik hjk n sign) hvals.2
  funext q
  let g : Plane X i j k hij hik hjk n :=
    planeEnumeration X i j k hij hik hjk n q
  obtain ⟨a, b, hab⟩ := exists_coordinate_factorization
    X i j k hij hik hjk n g
  have hmul := planeEigenvalue_mul_of_component_ne_zero
    X i j k hij hik hjk n rho sign z hv
      (firstCoordinate X i j k hij hik hjk n a)
      (secondCoordinate X i j k hij hik hjk n b)
  have heig : planeEigenvalue X i j k hij hik hjk n sign g = 1 := by
    rw [← hab, hmul]
    change chi a * psi b = 1
    rw [hchiOne a, hpsiOne b, one_mul]
  unfold planeEigenvalue at heig
  simp only [g, Equiv.symm_apply_apply] at heig
  cases hq : sign q
  · norm_num [hq] at heig
  · rfl

theorem planeComponent_eq_zero_of_region_zero_of_sign_ne_true
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (n : ℕ)
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool)
    (hzero : planeCharacterRegion X i j k hij hik hjk n sign = .zero)
    (hne : sign ≠ fun _ ↦ true) :
    planeComponent X i j k hij hik hjk n rho sign z = 0 := by
  by_contra hv
  exact hne (sign_eq_const_true_of_component_ne_zero_of_region_zero
    X i j k hij hik hjk rho z n sign hv hzero)

theorem inner_planeComponent_eq_zero_of_fixed_of_mem_nonzero
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z y : E) (n : ℕ)
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool)
    (hsign : sign ∈ planeNonzeroRegionSignSet X i j k hij hik hjk n)
    (hy : y ∈ KazhdanFixedSpace.fixedSubspace rho
      (rootPlaneDegreeSubgroup X i j k hij hik hjk n)) :
    inner ℝ y (planeComponent X i j k hij hik hjk n rho sign z) = 0 := by
  have hne := sign_ne_const_true_of_mem_planeNonzeroRegionSignSet
    X i j k hij hik hjk n sign hsign
  have hexists : ∃ q, sign q = false := by
    by_contra hnone
    apply hne
    funext q
    cases hq : sign q
    · exact False.elim (hnone ⟨q, hq⟩)
    · rfl
  obtain ⟨q, hq⟩ := hexists
  have hyact : rho (planeFamily X i j k hij hik hjk n q) y = y :=
    (KazhdanFixedSpace.mem_fixedSubspace_iff rho
      (rootPlaneDegreeSubgroup X i j k hij hik hjk n) y).mp hy
      (planeFamily X i j k hij hik hjk n q)
      (planeEnumeration X i j k hij hik hjk n q).property
  have hvact := action_planeComponent X i j k hij hik hjk n rho sign z q
  simp [hq] at hvact
  have hiso := (rho (planeFamily X i j k hij hik hjk n q)).inner_map_map y
    (planeComponent X i j k hij hik hjk n rho sign z)
  rw [hyact, hvact] at hiso
  simp only [inner_neg_right] at hiso
  linarith

/-- The Fourier moving part lies in the orthogonal complement of the
stage-fixed subspace. -/
theorem planeMovingPart_mem_fixedSubspace_orthogonal
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (n : ℕ) :
    planeMovingPart X i j k hij hik hjk rho z n ∈
      (KazhdanFixedSpace.fixedSubspace rho
        (rootPlaneDegreeSubgroup X i j k hij hik hjk n))ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro y hy
  unfold planeMovingPart
  rw [inner_sum]
  apply Finset.sum_eq_zero
  intro sign hsign
  exact inner_planeComponent_eq_zero_of_fixed_of_mem_nonzero
    X i j k hij hik hjk rho z y n sign hsign hy

/-- The single all-positive Fourier component. -/
noncomputable def planeTrivialPart
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (n : ℕ) : E :=
  planeComponent X i j k hij hik hjk n rho (fun _ ↦ true) z

theorem planeTrivialPart_mem_fixedSubspace
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (n : ℕ) :
    planeTrivialPart X i j k hij hik hjk rho z n ∈
      KazhdanFixedSpace.fixedSubspace rho
        (rootPlaneDegreeSubgroup X i j k hij hik hjk n) := by
  rw [KazhdanFixedSpace.mem_fixedSubspace_iff]
  intro g hg
  obtain ⟨q, hq⟩ := exists_planeFamily_eq X i j k hij hik hjk n ⟨g, hg⟩
  have hq' : planeFamily X i j k hij hik hjk n q = g := by
    simpa using hq
  unfold planeTrivialPart
  rw [← hq']
  simpa using action_planeComponent X i j k hij hik hjk n rho
    (fun _ ↦ true) z q

theorem sum_planeRegionSignSet_zero_eq_trivialPart
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (n : ℕ) :
    (∑ sign ∈ planeRegionSignSet X i j k hij hik hjk n .zero,
        planeComponent X i j k hij hik hjk n rho sign z) =
      planeTrivialPart X i j k hij hik hjk rho z n := by
  classical
  unfold planeTrivialPart
  rw [Finset.sum_eq_single (fun _ ↦ true)]
  · intro sign hsign hne
    have hzero : planeCharacterRegion X i j k hij hik hjk n sign = .zero := by
      simpa [planeRegionSignSet] using hsign
    exact planeComponent_eq_zero_of_region_zero_of_sign_ne_true
      X i j k hij hik hjk rho z n sign hzero hne
  · simp [planeRegionSignSet, planeCharacterRegion_const_true_eq_zero]

/-- Exact fixed-plus-moving reconstruction at every finite stage. -/
theorem planeTrivialPart_add_movingPart
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (n : ℕ) :
    planeTrivialPart X i j k hij hik hjk rho z n +
      planeMovingPart X i j k hij hik hjk rho z n = z := by
  classical
  let nonzero := planeNonzeroRegionSignSet X i j k hij hik hjk n
  let zero := planeRegionSignSet X i j k hij hik hjk n .zero
  have hpartition : (Finset.univ : Finset
      (Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool)) =
      nonzero ∪ zero := by
    ext sign
    simp only [nonzero, zero, planeNonzeroRegionSignSet, planeRegionSignSet,
      Finset.mem_univ, Finset.mem_filter, true_and, Finset.mem_union]
    by_cases hzero : planeCharacterRegion X i j k hij hik hjk n sign = .zero
    · simp [hzero]
    · simp [hzero]
  have hdisjoint : Disjoint nonzero zero := by
    rw [Finset.disjoint_left]
    intro sign hn hz
    simp only [nonzero, planeNonzeroRegionSignSet, Finset.mem_filter,
      Finset.mem_univ, true_and] at hn
    simp only [zero, planeRegionSignSet, Finset.mem_filter,
      Finset.mem_univ, true_and] at hz
    exact hn hz
  have htotal := sum_planeComponent X i j k hij hik hjk n rho z
  change (∑ sign ∈ (Finset.univ : Finset
      (Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool)),
      planeComponent X i j k hij hik hjk n rho sign z) = z at htotal
  rw [hpartition, Finset.sum_union hdisjoint] at htotal
  rw [sum_planeRegionSignSet_zero_eq_trivialPart
    X i j k hij hik hjk rho z n] at htotal
  simpa [nonzero, planeMovingPart, add_comm] using htotal

/-- The Fourier moving part is the genuine orthogonal projection onto the
complement of the stage-fixed space. -/
theorem planeMovingPart_eq_subgroupMovingProjection [CompleteSpace E]
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (n : ℕ) :
    planeMovingPart X i j k hij hik hjk rho z n =
      KazhdanFixedSpace.subgroupMovingProjection rho
        (rootPlaneDegreeSubgroup X i j k hij hik hjk n) z := by
  let H := rootPlaneDegreeSubgroup X i j k hij hik hjk n
  let U := KazhdanFixedSpace.fixedSubspace rho H
  let fixed := planeTrivialPart X i j k hij hik hjk rho z n
  let moving := planeMovingPart X i j k hij hik hjk rho z n
  have hfixed : fixed ∈ U :=
    planeTrivialPart_mem_fixedSubspace X i j k hij hik hjk rho z n
  have hmoving : moving ∈ Uᗮ :=
    planeMovingPart_mem_fixedSubspace_orthogonal
      X i j k hij hik hjk rho z n
  have hreconstruct : fixed + moving = z :=
    planeTrivialPart_add_movingPart X i j k hij hik hjk rho z n
  have hres : z - fixed = moving := by
    rw [← hreconstruct]
    abel
  have hresOrth : z - fixed ∈ Uᗮ := by
    rw [hres]
    exact hmoving
  letI : CompleteSpace U :=
    (KazhdanFixedSpace.isClosed_fixedSubspace rho H).completeSpace_coe
  have hfixedProjection : (KazhdanFixedSpace.fixedProjection rho H z : E) =
      fixed := by
    change U.starProjection z = fixed
    exact U.eq_starProjection_of_mem_orthogonal hfixed hresOrth
  rw [KazhdanFixedSpace.subgroupMovingProjection_eq_sub_fixedProjection,
    hfixedProjection, hres]

/-- The finite Fourier moving parts converge to the genuine moving projection
for the join of the two full column-root subgroups.  Thus no mass can escape
through the increasing degree filtration. -/
theorem tendsto_planeMovingPart [CompleteSpace E]
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    Filter.Tendsto
      (fun n ↦ planeMovingPart X i j k hij hik hjk rho z n)
      Filter.atTop
      (nhds (KazhdanFixedSpace.subgroupMovingProjection rho
        (elementaryRootSubgroup i k hik ⊔
          elementaryRootSubgroup j k hjk) z)) := by
  have h := KazhdanFixedSpace.tendsto_subgroupMovingProjection_iSup rho
    (rootPlaneDegreeSubgroup X i j k hij hik hjk)
    (elementaryRootSubgroup i k hik ⊔ elementaryRootSubgroup j k hjk)
    (rootPlaneDegreeSubgroup_mono X i j k hij hik hjk)
    (iSup_rootPlaneDegreeSubgroup X i j k hij hik hjk) z
  simpa only [planeMovingPart_eq_subgroupMovingProjection
    X i j k hij hik hjk rho z] using h

/-- Squared moving mass converges to the squared norm of the full two-root
moving projection. -/
theorem tendsto_norm_planeMovingPart_sq [CompleteSpace E]
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    Filter.Tendsto
      (fun n ↦ ‖planeMovingPart X i j k hij hik hjk rho z n‖ ^ 2)
      Filter.atTop
      (nhds (‖KazhdanFixedSpace.subgroupMovingProjection rho
        (elementaryRootSubgroup i k hik ⊔
          elementaryRootSubgroup j k hjk) z‖ ^ 2)) := by
  exact (tendsto_planeMovingPart X i j k hij hik hjk rho z).norm.pow 2

private theorem sum_union_le_sum_add_sum
    {α : Type*} [DecidableEq α] (f : α → ℝ) (hf : ∀ x, 0 ≤ f x)
    (a b : Finset α) :
    (∑ x ∈ a ∪ b, f x) ≤ (∑ x ∈ a, f x) + ∑ x ∈ b, f x := by
  have hab : a ∪ b = a ∪ (b \ a) := by
    ext x
    simp
  have hdisjoint : Disjoint a (b \ a) := by
    rw [Finset.disjoint_left]
    intro x ha hba
    exact (Finset.mem_sdiff.mp hba).2 ha
  have hdiff : (∑ x ∈ b \ a, f x) ≤ ∑ x ∈ b, f x :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (fun x _ _ ↦ hf x)
  rw [hab, Finset.sum_union hdisjoint]
  simpa [add_comm] using add_le_add_left hdiff (∑ x ∈ a, f x)

/-- After one refinement, the mass over two coarse regions is supported on
the same two fine regions together with the two new top-degree layers. -/
theorem sum_norm_planeRegionUnion_sq_le_succ_union_topBoundarySignSets
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (r s : ValuationRegion)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    (∑ sign ∈ (planeRegionSignSet X i j k hij hik hjk n r ∪
          planeRegionSignSet X i j k hij hik hjk n s),
        ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2) ≤
      ∑ sign ∈
          ((planeRegionSignSet X i j k hij hik hjk (n + 1) r ∪
              planeRegionSignSet X i j k hij hik hjk (n + 1) s) ∪
            (planeFirstTopBoundarySignSet X i j k hij hik hjk (n + 1) ∪
              planeSecondTopBoundarySignSet X i j k hij hik hjk (n + 1))),
        ‖planeComponent X i j k hij hik hjk (n + 1) rho sign z‖ ^ 2 := by
  classical
  let coarse := planeRegionSignSet X i j k hij hik hjk n r ∪
    planeRegionSignSet X i j k hij hik hjk n s
  let fine := planeRegionSignSet X i j k hij hik hjk (n + 1) r ∪
    planeRegionSignSet X i j k hij hik hjk (n + 1) s
  let preimage := fineRestrictionSignSet
    (Nat.card (Plane X i j k hij hik hjk (n + 1)))
    (Nat.card (Plane X i j k hij hik hjk n))
    (planeSuccIndex X i j k hij hik hjk n) coarse
  let validPreimage := planeValidSignSubset X i j k hij hik hjk (n + 1) preimage
  let firstTop := planeFirstTopBoundarySignSet X i j k hij hik hjk (n + 1)
  let secondTop := planeSecondTopBoundarySignSet X i j k hij hik hjk (n + 1)
  let mass := fun sign :
      Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool ↦
    ‖planeComponent X i j k hij hik hjk (n + 1) rho sign z‖ ^ 2
  have hremove :
      (∑ sign ∈ preimage, mass sign) =
        ∑ sign ∈ validPreimage, mass sign := by
    simpa [validPreimage, mass] using
      sum_norm_planeSignSet_eq_filter_valid
        X i j k hij hik hjk (n + 1) rho preimage z
  have hsubset : validPreimage ⊆ fine ∪ (firstTop ∪ secondTop) := by
    simpa [validPreimage, preimage, coarse, fine, firstTop, secondTop] using
      filter_valid_fineRestriction_regionUnion_subset
        X i j k hij hik hjk n r s
  calc
    (∑ sign ∈ coarse,
        ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2) =
        ∑ sign ∈ preimage, mass sign :=
      (sum_norm_planeRestriction_sq X i j k hij hik hjk n rho coarse z).symm
    _ = ∑ sign ∈ validPreimage, mass sign := hremove
    _ ≤ ∑ sign ∈ fine ∪ (firstTop ∪ secondTop), mass sign :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun _ _ _ ↦ sq_nonneg _)

/-- Refining the mass in any union of two valuation regions changes the
region only on the two newly exposed top-degree character layers.  Invalid
binary assignments are discarded here using their proved zero Fourier
component; no character-validity premise is supplied by the caller. -/
theorem sum_norm_planeRegionUnion_sq_le_succ_add_topBoundaries
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (r s : ValuationRegion)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    (∑ sign ∈ (planeRegionSignSet X i j k hij hik hjk n r ∪
          planeRegionSignSet X i j k hij hik hjk n s),
        ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2) ≤
      (∑ sign ∈ (planeRegionSignSet X i j k hij hik hjk (n + 1) r ∪
            planeRegionSignSet X i j k hij hik hjk (n + 1) s),
          ‖planeComponent X i j k hij hik hjk (n + 1) rho sign z‖ ^ 2) +
        planeFirstTopBoundaryMass X i j k hij hik hjk rho z (n + 1) +
        planeSecondTopBoundaryMass X i j k hij hik hjk rho z (n + 1) := by
  classical
  let fine := planeRegionSignSet X i j k hij hik hjk (n + 1) r ∪
    planeRegionSignSet X i j k hij hik hjk (n + 1) s
  let firstTop := planeFirstTopBoundarySignSet X i j k hij hik hjk (n + 1)
  let secondTop := planeSecondTopBoundarySignSet X i j k hij hik hjk (n + 1)
  let mass := fun sign :
      Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool ↦
    ‖planeComponent X i j k hij hik hjk (n + 1) rho sign z‖ ^ 2
  calc
    _ ≤ ∑ sign ∈ fine ∪ (firstTop ∪ secondTop), mass sign := by
      simpa [fine, firstTop, secondTop, mass] using
        sum_norm_planeRegionUnion_sq_le_succ_union_topBoundarySignSets
          X i j k hij hik hjk n r s rho z
    _ ≤ (∑ sign ∈ fine, mass sign) +
          ∑ sign ∈ firstTop ∪ secondTop, mass sign :=
      sum_union_le_sum_add_sum mass (fun _ ↦ sq_nonneg _) fine
        (firstTop ∪ secondTop)
    _ ≤ (∑ sign ∈ fine, mass sign) +
          ((∑ sign ∈ firstTop, mass sign) +
            ∑ sign ∈ secondTop, mass sign) :=
      by
        have hexception : (∑ sign ∈ firstTop ∪ secondTop, mass sign) ≤
            (∑ sign ∈ firstTop, mass sign) +
              ∑ sign ∈ secondTop, mass sign :=
          sum_union_le_sum_add_sum mass (fun _ ↦ sq_nonneg _) firstTop secondTop
        simpa [add_comm] using add_le_add_left hexception
          (∑ sign ∈ fine, mass sign)
    _ = _ := by
      simp only [fine, firstTop, secondTop, mass,
        planeFirstTopBoundaryMass, planeSecondTopBoundaryMass]
      rw [add_assoc]

theorem planeFirstTrivialMass_step
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (n : ℕ) :
    planeFirstTrivialMass X i j k hij hik hjk rho z n =
      planeFirstTopBoundaryMass X i j k hij hik hjk rho z (n + 1) +
        planeFirstTrivialMass X i j k hij hik hjk rho z (n + 1) :=
  sum_norm_planeFirstTrivialSignSet_sq X i j k hij hik hjk n rho z

theorem planeSecondTrivialMass_step
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (n : ℕ) :
    planeSecondTrivialMass X i j k hij hik hjk rho z n =
      planeSecondTopBoundaryMass X i j k hij hik hjk rho z (n + 1) +
        planeSecondTrivialMass X i j k hij hik hjk rho z (n + 1) :=
  sum_norm_planeSecondTrivialSignSet_sq X i j k hij hik hjk n rho z

theorem planeFirstTopBoundaryMass_nonneg
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (n : ℕ) :
    0 ≤ planeFirstTopBoundaryMass X i j k hij hik hjk rho z n :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

theorem planeSecondTopBoundaryMass_nonneg
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (n : ℕ) :
    0 ≤ planeSecondTopBoundaryMass X i j k hij hik hjk rho z n :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

theorem planeFirstTrivialMass_nonneg
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (n : ℕ) :
    0 ≤ planeFirstTrivialMass X i j k hij hik hjk rho z n :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

theorem planeSecondTrivialMass_nonneg
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (n : ℕ) :
    0 ≤ planeSecondTrivialMass X i j k hij hik hjk rho z n :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

theorem antitone_planeFirstTrivialMass
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    Antitone (planeFirstTrivialMass X i j k hij hik hjk rho z) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [planeFirstTrivialMass_step X i j k hij hik hjk rho z n]
  exact le_add_of_nonneg_left
    (planeFirstTopBoundaryMass_nonneg X i j k hij hik hjk rho z (n + 1))

theorem antitone_planeSecondTrivialMass
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    Antitone (planeSecondTrivialMass X i j k hij hik hjk rho z) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [planeSecondTrivialMass_step X i j k hij hik hjk rho z n]
  exact le_add_of_nonneg_left
    (planeSecondTopBoundaryMass_nonneg X i j k hij hik hjk rho z (n + 1))

/-- First-coordinate top-degree boundary mass vanishes along the exhaustive
filtration.  This is a consequence of an actual nonnegative telescoping
identity, not an assumed boundary condition. -/
theorem tendsto_planeFirstTopBoundaryMass_succ_zero
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    Filter.Tendsto
      (fun n ↦ planeFirstTopBoundaryMass X i j k hij hik hjk rho z (n + 1))
      Filter.atTop (nhds 0) := by
  let mass := planeFirstTrivialMass X i j k hij hik hjk rho z
  have hanti : Antitone mass :=
    antitone_planeFirstTrivialMass X i j k hij hik hjk rho z
  have hbdd : BddBelow (Set.range mass) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact planeFirstTrivialMass_nonneg X i j k hij hik hjk rho z n
  let limit : ℝ := ⨅ n, mass n
  have hlimit : Filter.Tendsto mass Filter.atTop (nhds limit) :=
    tendsto_atTop_ciInf hanti hbdd
  have hlimitSucc : Filter.Tendsto (fun n ↦ mass (n + 1))
      Filter.atTop (nhds limit) :=
    (Filter.tendsto_add_atTop_iff_nat 1).2 hlimit
  have hdiff : Filter.Tendsto (fun n ↦ mass n - mass (n + 1))
      Filter.atTop (nhds 0) := by
    simpa using hlimit.sub hlimitSucc
  convert hdiff using 1
  funext n
  change planeFirstTopBoundaryMass X i j k hij hik hjk rho z (n + 1) =
    planeFirstTrivialMass X i j k hij hik hjk rho z n -
      planeFirstTrivialMass X i j k hij hik hjk rho z (n + 1)
  rw [planeFirstTrivialMass_step X i j k hij hik hjk rho z n]
  ring

/-- The symmetric second-coordinate top-degree boundary also vanishes. -/
theorem tendsto_planeSecondTopBoundaryMass_succ_zero
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    Filter.Tendsto
      (fun n ↦ planeSecondTopBoundaryMass X i j k hij hik hjk rho z (n + 1))
      Filter.atTop (nhds 0) := by
  let mass := planeSecondTrivialMass X i j k hij hik hjk rho z
  have hanti : Antitone mass :=
    antitone_planeSecondTrivialMass X i j k hij hik hjk rho z
  have hbdd : BddBelow (Set.range mass) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact planeSecondTrivialMass_nonneg X i j k hij hik hjk rho z n
  let limit : ℝ := ⨅ n, mass n
  have hlimit : Filter.Tendsto mass Filter.atTop (nhds limit) :=
    tendsto_atTop_ciInf hanti hbdd
  have hlimitSucc : Filter.Tendsto (fun n ↦ mass (n + 1))
      Filter.atTop (nhds limit) :=
    (Filter.tendsto_add_atTop_iff_nat 1).2 hlimit
  have hdiff : Filter.Tendsto (fun n ↦ mass n - mass (n + 1))
      Filter.atTop (nhds 0) := by
    simpa using hlimit.sub hlimitSucc
  convert hdiff using 1
  funext n
  change planeSecondTopBoundaryMass X i j k hij hik hjk rho z (n + 1) =
    planeSecondTrivialMass X i j k hij hik hjk rho z n -
      planeSecondTrivialMass X i j k hij hik hjk rho z (n + 1)
  rw [planeSecondTrivialMass_step X i j k hij hik hjk rho z n]
  ring

/-- The first-character opposite-shear formula needs only algebraic character
validity. -/
theorem firstCoefficientEigenvalue_oppositeConjugatedRestriction_of_valid
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : X) (n : ℕ)
    (fineSign : Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool)
    (hvalid : IsPlaneCharacterSign X i j k hij hik hjk (n + 1) fineSign)
    (a : degreeLE X (ZMod 2) n) :
    firstCoefficientEigenvalue X i j k hij hik hjk n
        (fun q ↦ fineSign
          (oppositeConjugatedPlaneSuccIndex X i j k hij hik hjk x n q)) a =
      oppositeShearedFirstCharacter X
        (firstCoefficientEigenvalue X i j k hij hik hjk (n + 1) fineSign)
        (secondCoefficientEigenvalue X i j k hij hik hjk (n + 1) fineSign)
        x a := by
  rw [firstCoefficientEigenvalue,
    planeEigenvalue_oppositeConjugatedRestriction]
  have hconj : oppositeConjugatedPlaneSucc X i j k hij hik hjk x n
      (firstCoordinate X i j k hij hik hjk n a) =
      generatorShearedFirstCoordinate X i j k hij hik hjk x n a := by
    apply Subtype.ext
    exact conjugate_firstCoordinate_opposite_generator
      X i j k hij hik hjk x n a
  rw [hconj, generatorShearedFirstCoordinate, hvalid]
  rfl

/-- On a nonzero fine Fourier component, restricting its sign assignment
along the opposite conjugated-plane map produces exactly the algebraic dual
shear of the first coefficient character. -/
theorem firstCoefficientEigenvalue_oppositeConjugatedRestriction
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : X) (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (fineSign : Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool)
    (z : E)
    (hv : planeComponent X i j k hij hik hjk (n + 1) rho fineSign z ≠ 0)
    (a : degreeLE X (ZMod 2) n) :
    firstCoefficientEigenvalue X i j k hij hik hjk n
        (fun q ↦ fineSign
          (oppositeConjugatedPlaneSuccIndex X i j k hij hik hjk x n q)) a =
      oppositeShearedFirstCharacter X
        (firstCoefficientEigenvalue X i j k hij hik hjk (n + 1) fineSign)
        (secondCoefficientEigenvalue X i j k hij hik hjk (n + 1) fineSign)
        x a := by
  exact firstCoefficientEigenvalue_oppositeConjugatedRestriction_of_valid
    X i j k hij hik hjk x n fineSign
      (isPlaneCharacterSign_of_component_ne_zero
        X i j k hij hik hjk (n + 1) rho fineSign z hv) a

/-- The second coefficient of the opposite-conjugated restriction is exactly
the restricted fine second character. -/
theorem secondCoefficientEigenvalue_oppositeConjugatedRestriction
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : X) (n : ℕ)
    (fineSign : Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool)
    (b : degreeLE X (ZMod 2) n) :
    secondCoefficientEigenvalue X i j k hij hik hjk n
        (fun q ↦ fineSign
          (oppositeConjugatedPlaneSuccIndex X i j k hij hik hjk x n q)) b =
      oppositeShearedSecondCharacter X
        (secondCoefficientEigenvalue X i j k hij hik hjk (n + 1) fineSign) b := by
  rw [secondCoefficientEigenvalue,
    planeEigenvalue_oppositeConjugatedRestriction]
  have hconj : oppositeConjugatedPlaneSucc X i j k hij hik hjk x n
      (secondCoordinate X i j k hij hik hjk n b) =
      secondCoordinate X i j k hij hik hjk (n + 1)
        (coefficientSucc X b) := by
    apply Subtype.ext
    exact conjugate_secondCoordinate_opposite_generator
      X i j k hij hik hjk x n b
  rw [hconj]
  rfl

/-- The first coefficient of the forward-conjugated restriction is the
ordinary restriction of the fine first character. -/
theorem firstCoefficientEigenvalue_forwardConjugatedRestriction
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : X) (n : ℕ)
    (fineSign : Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool)
    (a : degreeLE X (ZMod 2) n) :
    firstCoefficientEigenvalue X i j k hij hik hjk n
        (fun q ↦ fineSign
          (forwardConjugatedPlaneSuccIndex X i j k hij hik hjk x n q)) a =
      forwardShearedFirstCharacter X
        (firstCoefficientEigenvalue X i j k hij hik hjk (n + 1) fineSign) a := by
  rw [firstCoefficientEigenvalue,
    planeEigenvalue_forwardConjugatedRestriction]
  have hconj : forwardConjugatedPlaneSucc X i j k hij hik hjk x n
      (firstCoordinate X i j k hij hik hjk n a) =
      firstCoordinate X i j k hij hik hjk (n + 1)
        (coefficientSucc X a) := by
    apply Subtype.ext
    exact conjugate_firstCoordinate_generator X i j k hij hik hjk x n a
  rw [hconj]
  rfl

/-- The second-character forward-shear formula from algebraic character
validity alone. -/
theorem secondCoefficientEigenvalue_forwardConjugatedRestriction_of_valid
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : X) (n : ℕ)
    (fineSign : Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool)
    (hvalid : IsPlaneCharacterSign X i j k hij hik hjk (n + 1) fineSign)
    (b : degreeLE X (ZMod 2) n) :
    secondCoefficientEigenvalue X i j k hij hik hjk n
        (fun q ↦ fineSign
          (forwardConjugatedPlaneSuccIndex X i j k hij hik hjk x n q)) b =
      forwardShearedSecondCharacter X
        (firstCoefficientEigenvalue X i j k hij hik hjk (n + 1) fineSign)
        (secondCoefficientEigenvalue X i j k hij hik hjk (n + 1) fineSign)
        x b := by
  rw [secondCoefficientEigenvalue,
    planeEigenvalue_forwardConjugatedRestriction]
  have hconj : forwardConjugatedPlaneSucc X i j k hij hik hjk x n
      (secondCoordinate X i j k hij hik hjk n b) =
      generatorShearedSecondCoordinate X i j k hij hik hjk x n b := by
    apply Subtype.ext
    exact conjugate_secondCoordinate_generator X i j k hij hik hjk x n b
  rw [hconj, generatorShearedSecondCoordinate, hvalid]
  simp only [forwardShearedSecondCharacter, oppositeShearedFirstCharacter,
    characterProduct, restrictCharacterSucc, leftDerivedCharacter,
    firstCoefficientEigenvalue, secondCoefficientEigenvalue]
  rw [mul_comm]

/-- On a nonzero fine component, the second coefficient of the
forward-conjugated restriction is exactly the algebraic forward dual shear. -/
theorem secondCoefficientEigenvalue_forwardConjugatedRestriction
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : X) (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (fineSign : Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool)
    (z : E)
    (hv : planeComponent X i j k hij hik hjk (n + 1) rho fineSign z ≠ 0)
    (b : degreeLE X (ZMod 2) n) :
    secondCoefficientEigenvalue X i j k hij hik hjk n
        (fun q ↦ fineSign
          (forwardConjugatedPlaneSuccIndex X i j k hij hik hjk x n q)) b =
      forwardShearedSecondCharacter X
        (firstCoefficientEigenvalue X i j k hij hik hjk (n + 1) fineSign)
        (secondCoefficientEigenvalue X i j k hij hik hjk (n + 1) fineSign)
        x b := by
  exact secondCoefficientEigenvalue_forwardConjugatedRestriction_of_valid
    X i j k hij hik hjk x n fineSign
      (isPlaneCharacterSign_of_component_ne_zero
        X i j k hij hik hjk (n + 1) rho fineSign z hv) b

/-- Below the top-degree boundary, the second character of an opposite
conjugated restriction retains the source character's canonical leading
generator. -/
theorem leastLeadingGeneratorIndex_second_oppositeConjugatedRestriction
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : X) (n : ℕ)
    (fineSign : Fin (Nat.card (Plane X i j k hij hik hjk (n + 2))) → Bool)
    (hle : secondCoefficientValuation X i j k hij hik hjk (n + 2) fineSign ≤
      n + 1) :
    leastLeadingGeneratorIndex X
        (secondCoefficientEigenvalue X i j k hij hik hjk (n + 1)
          (fun r ↦ fineSign (oppositeConjugatedPlaneSuccIndex
            X i j k hij hik hjk x (n + 1) r))) =
      leastLeadingGeneratorIndex X
        (secondCoefficientEigenvalue X i j k hij hik hjk (n + 2) fineSign) := by
  have hcharacter : secondCoefficientEigenvalue X i j k hij hik hjk (n + 1)
      (fun r ↦ fineSign (oppositeConjugatedPlaneSuccIndex
        X i j k hij hik hjk x (n + 1) r)) =
      restrictCharacterSucc X
        (secondCoefficientEigenvalue X i j k hij hik hjk (n + 2) fineSign) := by
    funext b
    exact secondCoefficientEigenvalue_oppositeConjugatedRestriction
      X i j k hij hik hjk x (n + 1) fineSign b
  rw [hcharacter]
  exact leastLeadingGeneratorIndex_restrictCharacterSucc X _ hle

/-- Symmetrically, the first character of a forward-conjugated restriction
retains its canonical leading generator below the boundary. -/
theorem leastLeadingGeneratorIndex_first_forwardConjugatedRestriction
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : X) (n : ℕ)
    (fineSign : Fin (Nat.card (Plane X i j k hij hik hjk (n + 2))) → Bool)
    (hle : firstCoefficientValuation X i j k hij hik hjk (n + 2) fineSign ≤
      n + 1) :
    leastLeadingGeneratorIndex X
        (firstCoefficientEigenvalue X i j k hij hik hjk (n + 1)
          (fun r ↦ fineSign (forwardConjugatedPlaneSuccIndex
            X i j k hij hik hjk x (n + 1) r))) =
      leastLeadingGeneratorIndex X
        (firstCoefficientEigenvalue X i j k hij hik hjk (n + 2) fineSign) := by
  have hcharacter : firstCoefficientEigenvalue X i j k hij hik hjk (n + 1)
      (fun r ↦ fineSign (forwardConjugatedPlaneSuccIndex
        X i j k hij hik hjk x (n + 1) r)) =
      restrictCharacterSucc X
        (firstCoefficientEigenvalue X i j k hij hik hjk (n + 2) fineSign) := by
    funext a
    exact firstCoefficientEigenvalue_forwardConjugatedRestriction
      X i j k hij hik hjk x (n + 1) fineSign a
  rw [hcharacter]
  exact leastLeadingGeneratorIndex_restrictCharacterSucc X _ hle

/-- The interior of an `A ∪ B` leading fiber consists of characters detected
strictly below the top degree that will be lost on restriction. -/
noncomputable def planeABInteriorLeadingSignSet
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (q : Fin (Fintype.card X)) :
    Finset (Fin (Nat.card (Plane X i j k hij hik hjk (n + 2))) → Bool) :=
  (planeABLeadingSignSet X i j k hij hik hjk (n + 1) q).filter
    fun fineSign ↦
      secondCoefficientValuation X i j k hij hik hjk (n + 2) fineSign ≤ n + 1

/-- The algebraically valid characters in one interior `A ∪ B` fiber. -/
noncomputable def planeABValidInteriorLeadingSignSet
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (q : Fin (Fintype.card X)) :
    Finset (Fin (Nat.card (Plane X i j k hij hik hjk (n + 2))) → Bool) :=
  by
    classical
    exact (planeABInteriorLeadingSignSet X i j k hij hik hjk n q).filter
      (IsPlaneCharacterSign X i j k hij hik hjk (n + 2))

/-- Coarse sign characters obtained by the concrete opposite shear from one
interior leading fiber. -/
noncomputable def planeABOppositeInteriorImageSignSet
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (q : Fin (Fintype.card X)) :
    Finset (Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool) :=
  (planeABValidInteriorLeadingSignSet X i j k hij hik hjk n q).image
    fun fineSign r ↦ fineSign (oppositeConjugatedPlaneSuccIndex
      X i j k hij hik hjk (generatorEnumeration X q) (n + 1) r)

/-- Distinct least-leading-generator fibers have disjoint opposite-shear
images below the top-degree boundary. -/
theorem planeABOppositeInteriorImageSignSet_pairwise_disjoint
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ) :
    Pairwise (fun q r : Fin (Fintype.card X) ↦
      Disjoint (planeABOppositeInteriorImageSignSet
        X i j k hij hik hjk n q)
        (planeABOppositeInteriorImageSignSet X i j k hij hik hjk n r)) := by
  intro q r hqr
  rw [Finset.disjoint_left]
  intro coarseSign hq hr
  obtain ⟨fineQ, hfineQ, hcoarseQ⟩ := Finset.mem_image.mp hq
  obtain ⟨fineR, hfineR, hcoarseR⟩ := Finset.mem_image.mp hr
  simp only [planeABValidInteriorLeadingSignSet, Finset.mem_filter] at hfineQ hfineR
  obtain ⟨hfineQ, _⟩ := hfineQ
  obtain ⟨hfineR, _⟩ := hfineR
  simp only [planeABInteriorLeadingSignSet, Finset.mem_filter] at hfineQ hfineR
  obtain ⟨hqFiber, hqLe⟩ := hfineQ
  obtain ⟨hrFiber, hrLe⟩ := hfineR
  simp only [planeABLeadingSignSet, Finset.mem_filter, Finset.mem_univ,
    true_and] at hqFiber hrFiber
  have hleastQ :=
    leastLeadingGeneratorIndex_second_oppositeConjugatedRestriction
      X i j k hij hik hjk (generatorEnumeration X q) n fineQ hqLe
  have hleastR :=
    leastLeadingGeneratorIndex_second_oppositeConjugatedRestriction
      X i j k hij hik hjk (generatorEnumeration X r) n fineR hrLe
  have hindexQ : leastLeadingGeneratorIndex X
      (secondCoefficientEigenvalue X i j k hij hik hjk (n + 1) coarseSign) =
      q.val := by
    rw [← hcoarseQ]
    exact hleastQ.trans hqFiber.2
  have hindexR : leastLeadingGeneratorIndex X
      (secondCoefficientEigenvalue X i j k hij hik hjk (n + 1) coarseSign) =
      r.val := by
    rw [← hcoarseR]
    exact hleastR.trans hrFiber.2
  apply hqr
  apply Fin.ext
  exact hindexQ.symm.trans hindexR

/-- The below-boundary interior of a `C ∪ B` leading fiber. -/
noncomputable def planeCBInteriorLeadingSignSet
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (q : Fin (Fintype.card X)) :
    Finset (Fin (Nat.card (Plane X i j k hij hik hjk (n + 2))) → Bool) :=
  (planeCBLeadingSignSet X i j k hij hik hjk (n + 1) q).filter
    fun fineSign ↦
      firstCoefficientValuation X i j k hij hik hjk (n + 2) fineSign ≤ n + 1

/-- The algebraically valid characters in one interior `C ∪ B` fiber. -/
noncomputable def planeCBValidInteriorLeadingSignSet
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (q : Fin (Fintype.card X)) :
    Finset (Fin (Nat.card (Plane X i j k hij hik hjk (n + 2))) → Bool) :=
  by
    classical
    exact (planeCBInteriorLeadingSignSet X i j k hij hik hjk n q).filter
      (IsPlaneCharacterSign X i j k hij hik hjk (n + 2))

/-- Coarse sign characters obtained by the concrete forward shear from one
interior `C ∪ B` fiber. -/
noncomputable def planeCBForwardInteriorImageSignSet
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (q : Fin (Fintype.card X)) :
    Finset (Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool) :=
  (planeCBValidInteriorLeadingSignSet X i j k hij hik hjk n q).image
    fun fineSign r ↦ fineSign (forwardConjugatedPlaneSuccIndex
      X i j k hij hik hjk (generatorEnumeration X q) (n + 1) r)

/-- Distinct `C ∪ B` least-leading-generator fibers have disjoint
forward-shear images below the top-degree boundary. -/
theorem planeCBForwardInteriorImageSignSet_pairwise_disjoint
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ) :
    Pairwise (fun q r : Fin (Fintype.card X) ↦
      Disjoint (planeCBForwardInteriorImageSignSet
        X i j k hij hik hjk n q)
        (planeCBForwardInteriorImageSignSet X i j k hij hik hjk n r)) := by
  intro q r hqr
  rw [Finset.disjoint_left]
  intro coarseSign hq hr
  obtain ⟨fineQ, hfineQ, hcoarseQ⟩ := Finset.mem_image.mp hq
  obtain ⟨fineR, hfineR, hcoarseR⟩ := Finset.mem_image.mp hr
  simp only [planeCBValidInteriorLeadingSignSet, Finset.mem_filter] at hfineQ hfineR
  obtain ⟨hfineQ, _⟩ := hfineQ
  obtain ⟨hfineR, _⟩ := hfineR
  simp only [planeCBInteriorLeadingSignSet, Finset.mem_filter] at hfineQ hfineR
  obtain ⟨hqFiber, hqLe⟩ := hfineQ
  obtain ⟨hrFiber, hrLe⟩ := hfineR
  simp only [planeCBLeadingSignSet, Finset.mem_filter, Finset.mem_univ,
    true_and] at hqFiber hrFiber
  have hleastQ :=
    leastLeadingGeneratorIndex_first_forwardConjugatedRestriction
      X i j k hij hik hjk (generatorEnumeration X q) n fineQ hqLe
  have hleastR :=
    leastLeadingGeneratorIndex_first_forwardConjugatedRestriction
      X i j k hij hik hjk (generatorEnumeration X r) n fineR hrLe
  have hindexQ : leastLeadingGeneratorIndex X
      (firstCoefficientEigenvalue X i j k hij hik hjk (n + 1) coarseSign) =
      q.val := by
    rw [← hcoarseQ]
    exact hleastQ.trans hqFiber.2
  have hindexR : leastLeadingGeneratorIndex X
      (firstCoefficientEigenvalue X i j k hij hik hjk (n + 1) coarseSign) =
      r.val := by
    rw [← hcoarseR]
    exact hleastR.trans hrFiber.2
  apply hqr
  apply Fin.ext
  exact hindexQ.symm.trans hindexR

/-- Exact mass transport from one interior `A ∪ B` fiber into only its
concrete opposite-shear image set. -/
theorem sum_norm_planeABInteriorLeadingSignSet_sq_le_image
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (q : Fin (Fintype.card X))
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    ∑ fineSign ∈ planeABInteriorLeadingSignSet X i j k hij hik hjk n q,
        ‖planeComponent X i j k hij hik hjk (n + 2) rho fineSign z‖ ^ 2 ≤
      ∑ coarseSign ∈
          planeABOppositeInteriorImageSignSet X i j k hij hik hjk n q,
        ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign
          (rho (elementaryRoot j i hij.symm
            (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z)‖ ^ 2 := by
  let index := oppositeConjugatedPlaneSuccIndex X i j k hij hik hjk
    (generatorEnumeration X q) (n + 1)
  let image := planeABOppositeInteriorImageSignSet X i j k hij hik hjk n q
  have hmass :
      (∑ fineSign ∈ planeABInteriorLeadingSignSet X i j k hij hik hjk n q,
          ‖planeComponent X i j k hij hik hjk (n + 2) rho fineSign z‖ ^ 2) =
        ∑ fineSign ∈ planeABValidInteriorLeadingSignSet
            X i j k hij hik hjk n q,
          ‖planeComponent X i j k hij hik hjk (n + 2) rho fineSign z‖ ^ 2 := by
    classical
    rw [planeABValidInteriorLeadingSignSet]
    generalize planeABInteriorLeadingSignSet X i j k hij hik hjk n q = signs
    induction signs using Finset.induction_on with
    | empty => simp
    | @insert fineSign signs hnot ih =>
        by_cases hvalid : IsPlaneCharacterSign X i j k hij hik hjk (n + 2) fineSign
        · rw [Finset.filter_insert]
          simp [hnot, hvalid, ih]
        · have hzero := planeComponent_eq_zero_of_not_isPlaneCharacterSign
            X i j k hij hik hjk (n + 2) rho fineSign z hvalid
          rw [Finset.filter_insert]
          simp [hnot, hvalid, hzero, ih]
  have hsubset : planeABValidInteriorLeadingSignSet
        X i j k hij hik hjk n q ⊆
      fineRestrictionSignSet
        (Nat.card (Plane X i j k hij hik hjk (n + 2)))
        (Nat.card (Plane X i j k hij hik hjk (n + 1))) index image := by
    intro fineSign hmem
    simp only [fineRestrictionSignSet, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact Finset.mem_image.mpr ⟨fineSign, hmem, rfl⟩
  calc
    ∑ fineSign ∈ planeABInteriorLeadingSignSet X i j k hij hik hjk n q,
        ‖planeComponent X i j k hij hik hjk (n + 2) rho fineSign z‖ ^ 2 =
        ∑ fineSign ∈ planeABValidInteriorLeadingSignSet
            X i j k hij hik hjk n q,
          ‖planeComponent X i j k hij hik hjk (n + 2) rho fineSign z‖ ^ 2 :=
      hmass
    _ ≤
        ∑ fineSign ∈ fineRestrictionSignSet
          (Nat.card (Plane X i j k hij hik hjk (n + 2)))
          (Nat.card (Plane X i j k hij hik hjk (n + 1))) index image,
          ‖planeComponent X i j k hij hik hjk (n + 2) rho fineSign z‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun _ _ _ ↦ sq_nonneg _)
    _ = ∑ coarseSign ∈ image,
          ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign
            (rho (elementaryRoot j i hij.symm
              (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z)‖ ^ 2 :=
      sum_norm_oppositeConjugatedRestriction_sq X i j k hij hik hjk
        (generatorEnumeration X q) (n + 1) rho image z

/-- Exact mass transport from one interior `C ∪ B` fiber into only its
concrete forward-shear image set. -/
theorem sum_norm_planeCBInteriorLeadingSignSet_sq_le_image
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (q : Fin (Fintype.card X))
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    ∑ fineSign ∈ planeCBInteriorLeadingSignSet X i j k hij hik hjk n q,
        ‖planeComponent X i j k hij hik hjk (n + 2) rho fineSign z‖ ^ 2 ≤
      ∑ coarseSign ∈
          planeCBForwardInteriorImageSignSet X i j k hij hik hjk n q,
        ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign
          (rho (elementaryRoot i j hij
            (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z)‖ ^ 2 := by
  let index := forwardConjugatedPlaneSuccIndex X i j k hij hik hjk
    (generatorEnumeration X q) (n + 1)
  let image := planeCBForwardInteriorImageSignSet X i j k hij hik hjk n q
  have hmass :
      (∑ fineSign ∈ planeCBInteriorLeadingSignSet X i j k hij hik hjk n q,
          ‖planeComponent X i j k hij hik hjk (n + 2) rho fineSign z‖ ^ 2) =
        ∑ fineSign ∈ planeCBValidInteriorLeadingSignSet
            X i j k hij hik hjk n q,
          ‖planeComponent X i j k hij hik hjk (n + 2) rho fineSign z‖ ^ 2 := by
    classical
    rw [planeCBValidInteriorLeadingSignSet]
    generalize planeCBInteriorLeadingSignSet X i j k hij hik hjk n q = signs
    induction signs using Finset.induction_on with
    | empty => simp
    | @insert fineSign signs hnot ih =>
        by_cases hvalid : IsPlaneCharacterSign X i j k hij hik hjk (n + 2) fineSign
        · rw [Finset.filter_insert]
          simp [hnot, hvalid, ih]
        · have hzero := planeComponent_eq_zero_of_not_isPlaneCharacterSign
            X i j k hij hik hjk (n + 2) rho fineSign z hvalid
          rw [Finset.filter_insert]
          simp [hnot, hvalid, hzero, ih]
  have hsubset : planeCBValidInteriorLeadingSignSet
        X i j k hij hik hjk n q ⊆
      fineRestrictionSignSet
        (Nat.card (Plane X i j k hij hik hjk (n + 2)))
        (Nat.card (Plane X i j k hij hik hjk (n + 1))) index image := by
    intro fineSign hmem
    simp only [fineRestrictionSignSet, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact Finset.mem_image.mpr ⟨fineSign, hmem, rfl⟩
  calc
    ∑ fineSign ∈ planeCBInteriorLeadingSignSet X i j k hij hik hjk n q,
        ‖planeComponent X i j k hij hik hjk (n + 2) rho fineSign z‖ ^ 2 =
        ∑ fineSign ∈ planeCBValidInteriorLeadingSignSet
            X i j k hij hik hjk n q,
          ‖planeComponent X i j k hij hik hjk (n + 2) rho fineSign z‖ ^ 2 :=
      hmass
    _ ≤
        ∑ fineSign ∈ fineRestrictionSignSet
          (Nat.card (Plane X i j k hij hik hjk (n + 2)))
          (Nat.card (Plane X i j k hij hik hjk (n + 1))) index image,
          ‖planeComponent X i j k hij hik hjk (n + 2) rho fineSign z‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun _ _ _ ↦ sq_nonneg _)
    _ = ∑ coarseSign ∈ image,
          ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign
            (rho (elementaryRoot i j hij
              (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z)‖ ^ 2 :=
      sum_norm_forwardConjugatedRestriction_sq X i j k hij hik hjk
        (generatorEnumeration X q) (n + 1) rho image z

/-- Algebraic character validity is sufficient for the concrete opposite
conjugation to carry an `A ∪ B` leading fiber into `C ∪ D`. -/
theorem planeCharacterRegion_oppositeConjugatedRestriction_eq_C_or_D_of_valid
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (q : Fin (Fintype.card X))
    (fineSign : Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool)
    (hvalid : IsPlaneCharacterSign X i j k hij hik hjk (n + 1) fineSign)
    (hsign : fineSign ∈ planeABLeadingSignSet X i j k hij hik hjk n q) :
    planeCharacterRegion X i j k hij hik hjk n
        (fun r ↦ fineSign (oppositeConjugatedPlaneSuccIndex X i j k hij hik hjk
          (generatorEnumeration X q) n r)) = .C ∨
      planeCharacterRegion X i j k hij hik hjk n
        (fun r ↦ fineSign (oppositeConjugatedPlaneSuccIndex X i j k hij hik hjk
          (generatorEnumeration X q) n r)) = .D := by
  have hfirst : firstCoefficientEigenvalue X i j k hij hik hjk n
      (fun r ↦ fineSign (oppositeConjugatedPlaneSuccIndex X i j k hij hik hjk
        (generatorEnumeration X q) n r)) =
      oppositeShearedFirstCharacter X
        (firstCoefficientEigenvalue X i j k hij hik hjk (n + 1) fineSign)
        (secondCoefficientEigenvalue X i j k hij hik hjk (n + 1) fineSign)
        (generatorEnumeration X q) := by
    funext a
    exact firstCoefficientEigenvalue_oppositeConjugatedRestriction_of_valid
      X i j k hij hik hjk (generatorEnumeration X q) n fineSign hvalid a
  have hsecond : secondCoefficientEigenvalue X i j k hij hik hjk n
      (fun r ↦ fineSign (oppositeConjugatedPlaneSuccIndex X i j k hij hik hjk
        (generatorEnumeration X q) n r)) =
      oppositeShearedSecondCharacter X
        (secondCoefficientEigenvalue X i j k hij hik hjk (n + 1) fineSign) := by
    funext b
    exact secondCoefficientEigenvalue_oppositeConjugatedRestriction
      X i j k hij hik hjk (generatorEnumeration X q) n fineSign b
  unfold planeCharacterRegion
  rw [hfirst, hsecond]
  exact planeABLeadingSignSet_region_transport X i j k hij hik hjk n q
    fineSign hsign

/-- The exact concrete opposite conjugation carries every nonzero fine
component in an `A ∪ B` leading fiber to a coarse character in `C ∪ D`.
This closes the bridge from the matrix conjugation to the valuation transport
statement. -/
theorem planeCharacterRegion_oppositeConjugatedRestriction_eq_C_or_D
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (q : Fin (Fintype.card X))
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (fineSign : Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool)
    (z : E)
    (hv : planeComponent X i j k hij hik hjk (n + 1) rho fineSign z ≠ 0)
    (hsign : fineSign ∈ planeABLeadingSignSet X i j k hij hik hjk n q) :
    planeCharacterRegion X i j k hij hik hjk n
        (fun r ↦ fineSign (oppositeConjugatedPlaneSuccIndex X i j k hij hik hjk
          (generatorEnumeration X q) n r)) = .C ∨
      planeCharacterRegion X i j k hij hik hjk n
        (fun r ↦ fineSign (oppositeConjugatedPlaneSuccIndex X i j k hij hik hjk
          (generatorEnumeration X q) n r)) = .D := by
  exact planeCharacterRegion_oppositeConjugatedRestriction_eq_C_or_D_of_valid
    X i j k hij hik hjk n q fineSign
      (isPlaneCharacterSign_of_component_ne_zero
        X i j k hij hik hjk (n + 1) rho fineSign z hv) hsign

/-- Algebraic character validity is sufficient for the forward concrete
conjugation to carry a `C ∪ B` leading fiber into `A ∪ D`. -/
theorem planeCharacterRegion_forwardConjugatedRestriction_eq_A_or_D_of_valid
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (q : Fin (Fintype.card X))
    (fineSign : Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool)
    (hvalid : IsPlaneCharacterSign X i j k hij hik hjk (n + 1) fineSign)
    (hsign : fineSign ∈ planeCBLeadingSignSet X i j k hij hik hjk n q) :
    planeCharacterRegion X i j k hij hik hjk n
        (fun r ↦ fineSign (forwardConjugatedPlaneSuccIndex X i j k hij hik hjk
          (generatorEnumeration X q) n r)) = .A ∨
      planeCharacterRegion X i j k hij hik hjk n
        (fun r ↦ fineSign (forwardConjugatedPlaneSuccIndex X i j k hij hik hjk
          (generatorEnumeration X q) n r)) = .D := by
  have hfirst : firstCoefficientEigenvalue X i j k hij hik hjk n
      (fun r ↦ fineSign (forwardConjugatedPlaneSuccIndex X i j k hij hik hjk
        (generatorEnumeration X q) n r)) =
      forwardShearedFirstCharacter X
        (firstCoefficientEigenvalue X i j k hij hik hjk (n + 1) fineSign) := by
    funext a
    exact firstCoefficientEigenvalue_forwardConjugatedRestriction
      X i j k hij hik hjk (generatorEnumeration X q) n fineSign a
  have hsecond : secondCoefficientEigenvalue X i j k hij hik hjk n
      (fun r ↦ fineSign (forwardConjugatedPlaneSuccIndex X i j k hij hik hjk
        (generatorEnumeration X q) n r)) =
      forwardShearedSecondCharacter X
        (firstCoefficientEigenvalue X i j k hij hik hjk (n + 1) fineSign)
        (secondCoefficientEigenvalue X i j k hij hik hjk (n + 1) fineSign)
        (generatorEnumeration X q) := by
    funext b
    exact secondCoefficientEigenvalue_forwardConjugatedRestriction_of_valid
      X i j k hij hik hjk (generatorEnumeration X q) n fineSign hvalid b
  unfold planeCharacterRegion
  rw [hfirst, hsecond]
  exact planeCBLeadingSignSet_region_transport X i j k hij hik hjk n q
    fineSign hsign

/-- The symmetric concrete forward conjugation sends every nonzero fine
component in a `C ∪ B` leading fiber to `A ∪ D` at the coarse stage. -/
theorem planeCharacterRegion_forwardConjugatedRestriction_eq_A_or_D
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (q : Fin (Fintype.card X))
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (fineSign : Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool)
    (z : E)
    (hv : planeComponent X i j k hij hik hjk (n + 1) rho fineSign z ≠ 0)
    (hsign : fineSign ∈ planeCBLeadingSignSet X i j k hij hik hjk n q) :
    planeCharacterRegion X i j k hij hik hjk n
        (fun r ↦ fineSign (forwardConjugatedPlaneSuccIndex X i j k hij hik hjk
          (generatorEnumeration X q) n r)) = .A ∨
      planeCharacterRegion X i j k hij hik hjk n
        (fun r ↦ fineSign (forwardConjugatedPlaneSuccIndex X i j k hij hik hjk
          (generatorEnumeration X q) n r)) = .D := by
  exact planeCharacterRegion_forwardConjugatedRestriction_eq_A_or_D_of_valid
    X i j k hij hik hjk n q fineSign
      (isPlaneCharacterSign_of_component_ne_zero
        X i j k hij hik hjk (n + 1) rho fineSign z hv) hsign

/-- Every valid opposite-shear image below the top-degree boundary lies in
the coarse `C ∪ D` region. -/
theorem planeABOppositeInteriorImageSignSet_subset_C_union_D
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (q : Fin (Fintype.card X)) :
    planeABOppositeInteriorImageSignSet X i j k hij hik hjk n q ⊆
      planeRegionSignSet X i j k hij hik hjk (n + 1) .C ∪
        planeRegionSignSet X i j k hij hik hjk (n + 1) .D := by
  classical
  intro coarseSign hcoarse
  obtain ⟨fineSign, hfine, rfl⟩ := Finset.mem_image.mp hcoarse
  obtain ⟨hinterior, hvalid⟩ := Finset.mem_filter.mp hfine
  obtain ⟨hleading, _⟩ := Finset.mem_filter.mp hinterior
  have hregion :=
    planeCharacterRegion_oppositeConjugatedRestriction_eq_C_or_D_of_valid
      X i j k hij hik hjk (n + 1) q fineSign hvalid hleading
  simpa [planeRegionSignSet] using hregion

/-- Every valid forward-shear image below the top-degree boundary lies in
the coarse `A ∪ D` region. -/
theorem planeCBForwardInteriorImageSignSet_subset_A_union_D
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (q : Fin (Fintype.card X)) :
    planeCBForwardInteriorImageSignSet X i j k hij hik hjk n q ⊆
      planeRegionSignSet X i j k hij hik hjk (n + 1) .A ∪
        planeRegionSignSet X i j k hij hik hjk (n + 1) .D := by
  classical
  intro coarseSign hcoarse
  obtain ⟨fineSign, hfine, rfl⟩ := Finset.mem_image.mp hcoarse
  obtain ⟨hinterior, hvalid⟩ := Finset.mem_filter.mp hfine
  obtain ⟨hleading, _⟩ := Finset.mem_filter.mp hinterior
  have hregion :=
    planeCharacterRegion_forwardConjugatedRestriction_eq_A_or_D_of_valid
      X i j k hij hik hjk (n + 1) q fineSign hvalid hleading
  simpa [planeRegionSignSet] using hregion

/-- Because the valid opposite-shear images are pairwise disjoint, their
total nonnegative weight is bounded by the weight of the single `C ∪ D`
target region. -/
theorem sum_planeABOppositeInteriorImageSignSet_le_C_union_D
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (f : (Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool) → ℝ)
    (hf : ∀ sign, 0 ≤ f sign) :
    (∑ q : Fin (Fintype.card X),
        ∑ sign ∈ planeABOppositeInteriorImageSignSet
            X i j k hij hik hjk n q,
          f sign) ≤
      ∑ sign ∈ (planeRegionSignSet X i j k hij hik hjk (n + 1) .C ∪
          planeRegionSignSet X i j k hij hik hjk (n + 1) .D),
        f sign := by
  classical
  have hpair :
      ((Finset.univ : Finset (Fin (Fintype.card X))) : Set _).PairwiseDisjoint
        (planeABOppositeInteriorImageSignSet X i j k hij hik hjk n) := by
    intro q _ r _ hqr
    exact planeABOppositeInteriorImageSignSet_pairwise_disjoint
      X i j k hij hik hjk n hqr
  rw [← Finset.sum_biUnion hpair]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro sign hsign
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hsign
    obtain ⟨q, hq⟩ := hsign
    exact planeABOppositeInteriorImageSignSet_subset_C_union_D
      X i j k hij hik hjk n q hq
  · intro sign _ _
    exact hf sign

/-- The symmetric disjoint-image estimate into the single `A ∪ D` target
region. -/
theorem sum_planeCBForwardInteriorImageSignSet_le_A_union_D
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (f : (Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool) → ℝ)
    (hf : ∀ sign, 0 ≤ f sign) :
    (∑ q : Fin (Fintype.card X),
        ∑ sign ∈ planeCBForwardInteriorImageSignSet
            X i j k hij hik hjk n q,
          f sign) ≤
      ∑ sign ∈ (planeRegionSignSet X i j k hij hik hjk (n + 1) .A ∪
          planeRegionSignSet X i j k hij hik hjk (n + 1) .D),
        f sign := by
  classical
  have hpair :
      ((Finset.univ : Finset (Fin (Fintype.card X))) : Set _).PairwiseDisjoint
        (planeCBForwardInteriorImageSignSet X i j k hij hik hjk n) := by
    intro q _ r _ hqr
    exact planeCBForwardInteriorImageSignSet_pairwise_disjoint
      X i j k hij hik hjk n hqr
  rw [← Finset.sum_biUnion hpair]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro sign hsign
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hsign
    obtain ⟨q, hq⟩ := hsign
    exact planeCBForwardInteriorImageSignSet_subset_A_union_D
      X i j k hij hik hjk n q hq
  · intro sign _ _
    exact hf sign

/-- The full below-boundary `A ∪ B` mass is charged injectively to one copy
of the `C ∪ D` mass, up to the sum of the concrete adjacent-generator
displacements.  In particular, the target mass has no generator-cardinality
factor. -/
theorem sum_norm_planeABInteriorLeadingSignSet_sq_le_target_add_error
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    (∑ q : Fin (Fintype.card X),
        ∑ fineSign ∈ planeABInteriorLeadingSignSet
            X i j k hij hik hjk n q,
          ‖planeComponent X i j k hij hik hjk (n + 2) rho fineSign z‖ ^ 2) ≤
      (∑ coarseSign ∈
          (planeRegionSignSet X i j k hij hik hjk (n + 1) .C ∪
            planeRegionSignSet X i j k hij hik hjk (n + 1) .D),
          ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign z‖ ^ 2) +
        ∑ q : Fin (Fintype.card X),
          2 * ‖z‖ *
            ‖rho (elementaryRoot j i hij.symm
              (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z - z‖ := by
  classical
  let moved : Fin (Fintype.card X) → E := fun q ↦
    rho (elementaryRoot j i hij.symm
      (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z
  have hfiber :
      (∑ q : Fin (Fintype.card X),
          ∑ fineSign ∈ planeABInteriorLeadingSignSet
              X i j k hij hik hjk n q,
            ‖planeComponent X i j k hij hik hjk (n + 2) rho fineSign z‖ ^ 2) ≤
        ∑ q : Fin (Fintype.card X),
          ∑ coarseSign ∈ planeABOppositeInteriorImageSignSet
              X i j k hij hik hjk n q,
            ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign
              (moved q)‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro q _
    exact sum_norm_planeABInteriorLeadingSignSet_sq_le_image
      X i j k hij hik hjk n q rho z
  have hmoved :
      (∑ q : Fin (Fintype.card X),
          ∑ coarseSign ∈ planeABOppositeInteriorImageSignSet
              X i j k hij hik hjk n q,
            ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign
              (moved q)‖ ^ 2) ≤
        ∑ q : Fin (Fintype.card X),
          ((∑ coarseSign ∈ planeABOppositeInteriorImageSignSet
                X i j k hij hik hjk n q,
              ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign z‖ ^ 2) +
            2 * ‖z‖ * ‖moved q - z‖) := by
    apply Finset.sum_le_sum
    intro q _
    have hvariation := abs_sum_norm_planeComponent_sq_sub_le
      X i j k hij hik hjk (n + 1) rho
      (planeABOppositeInteriorImageSignSet X i j k hij hik hjk n q)
      (moved q) z
    have hdiff :
        (∑ coarseSign ∈ planeABOppositeInteriorImageSignSet
              X i j k hij hik hjk n q,
            ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign
              (moved q)‖ ^ 2) -
          (∑ coarseSign ∈ planeABOppositeInteriorImageSignSet
              X i j k hij hik hjk n q,
            ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign z‖ ^ 2) ≤
        (‖moved q‖ + ‖z‖) * ‖moved q - z‖ :=
      (le_abs_self _).trans hvariation
    rw [sub_le_iff_le_add] at hdiff
    have hnorm : ‖moved q‖ = ‖z‖ := by
      exact (rho (elementaryRoot j i hij.symm
        (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q)))).norm_map z
    calc
      _ ≤ (‖moved q‖ + ‖z‖) * ‖moved q - z‖ +
          ∑ coarseSign ∈ planeABOppositeInteriorImageSignSet
              X i j k hij hik hjk n q,
            ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign z‖ ^ 2 :=
        hdiff
      _ = (∑ coarseSign ∈ planeABOppositeInteriorImageSignSet
              X i j k hij hik hjk n q,
            ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign z‖ ^ 2) +
          2 * ‖z‖ * ‖moved q - z‖ := by
        rw [hnorm]
        ring
  have htarget :
      (∑ q : Fin (Fintype.card X),
          ∑ coarseSign ∈ planeABOppositeInteriorImageSignSet
              X i j k hij hik hjk n q,
            ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign z‖ ^ 2) ≤
        ∑ coarseSign ∈
            (planeRegionSignSet X i j k hij hik hjk (n + 1) .C ∪
              planeRegionSignSet X i j k hij hik hjk (n + 1) .D),
          ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign z‖ ^ 2 :=
    sum_planeABOppositeInteriorImageSignSet_le_C_union_D
      X i j k hij hik hjk n
      (fun coarseSign ↦
        ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign z‖ ^ 2)
      (fun _ ↦ sq_nonneg _)
  calc
    _ ≤ ∑ q : Fin (Fintype.card X),
          ∑ coarseSign ∈ planeABOppositeInteriorImageSignSet
              X i j k hij hik hjk n q,
            ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign
              (moved q)‖ ^ 2 := hfiber
    _ ≤ ∑ q : Fin (Fintype.card X),
          ((∑ coarseSign ∈ planeABOppositeInteriorImageSignSet
                X i j k hij hik hjk n q,
              ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign z‖ ^ 2) +
            2 * ‖z‖ * ‖moved q - z‖) := hmoved
    _ = (∑ q : Fin (Fintype.card X),
          ∑ coarseSign ∈ planeABOppositeInteriorImageSignSet
              X i j k hij hik hjk n q,
            ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign z‖ ^ 2) +
        ∑ q : Fin (Fintype.card X), 2 * ‖z‖ * ‖moved q - z‖ := by
      rw [Finset.sum_add_distrib]
    _ ≤ (∑ coarseSign ∈
          (planeRegionSignSet X i j k hij hik hjk (n + 1) .C ∪
            planeRegionSignSet X i j k hij hik hjk (n + 1) .D),
          ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign z‖ ^ 2) +
        ∑ q : Fin (Fintype.card X), 2 * ‖z‖ * ‖moved q - z‖ :=
      add_le_add htarget (le_refl _)
    _ = _ := by rfl

/-- The symmetric full below-boundary `C ∪ B` estimate charges its mass
injectively to one copy of `A ∪ D`, again with no cardinality factor on the
target mass. -/
theorem sum_norm_planeCBInteriorLeadingSignSet_sq_le_target_add_error
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    (∑ q : Fin (Fintype.card X),
        ∑ fineSign ∈ planeCBInteriorLeadingSignSet
            X i j k hij hik hjk n q,
          ‖planeComponent X i j k hij hik hjk (n + 2) rho fineSign z‖ ^ 2) ≤
      (∑ coarseSign ∈
          (planeRegionSignSet X i j k hij hik hjk (n + 1) .A ∪
            planeRegionSignSet X i j k hij hik hjk (n + 1) .D),
          ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign z‖ ^ 2) +
        ∑ q : Fin (Fintype.card X),
          2 * ‖z‖ *
            ‖rho (elementaryRoot i j hij
              (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z - z‖ := by
  classical
  let moved : Fin (Fintype.card X) → E := fun q ↦
    rho (elementaryRoot i j hij
      (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z
  have hfiber :
      (∑ q : Fin (Fintype.card X),
          ∑ fineSign ∈ planeCBInteriorLeadingSignSet
              X i j k hij hik hjk n q,
            ‖planeComponent X i j k hij hik hjk (n + 2) rho fineSign z‖ ^ 2) ≤
        ∑ q : Fin (Fintype.card X),
          ∑ coarseSign ∈ planeCBForwardInteriorImageSignSet
              X i j k hij hik hjk n q,
            ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign
              (moved q)‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro q _
    exact sum_norm_planeCBInteriorLeadingSignSet_sq_le_image
      X i j k hij hik hjk n q rho z
  have hmoved :
      (∑ q : Fin (Fintype.card X),
          ∑ coarseSign ∈ planeCBForwardInteriorImageSignSet
              X i j k hij hik hjk n q,
            ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign
              (moved q)‖ ^ 2) ≤
        ∑ q : Fin (Fintype.card X),
          ((∑ coarseSign ∈ planeCBForwardInteriorImageSignSet
                X i j k hij hik hjk n q,
              ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign z‖ ^ 2) +
            2 * ‖z‖ * ‖moved q - z‖) := by
    apply Finset.sum_le_sum
    intro q _
    have hvariation := abs_sum_norm_planeComponent_sq_sub_le
      X i j k hij hik hjk (n + 1) rho
      (planeCBForwardInteriorImageSignSet X i j k hij hik hjk n q)
      (moved q) z
    have hdiff :
        (∑ coarseSign ∈ planeCBForwardInteriorImageSignSet
              X i j k hij hik hjk n q,
            ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign
              (moved q)‖ ^ 2) -
          (∑ coarseSign ∈ planeCBForwardInteriorImageSignSet
              X i j k hij hik hjk n q,
            ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign z‖ ^ 2) ≤
        (‖moved q‖ + ‖z‖) * ‖moved q - z‖ :=
      (le_abs_self _).trans hvariation
    rw [sub_le_iff_le_add] at hdiff
    have hnorm : ‖moved q‖ = ‖z‖ := by
      exact (rho (elementaryRoot i j hij
        (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q)))).norm_map z
    calc
      _ ≤ (‖moved q‖ + ‖z‖) * ‖moved q - z‖ +
          ∑ coarseSign ∈ planeCBForwardInteriorImageSignSet
              X i j k hij hik hjk n q,
            ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign z‖ ^ 2 :=
        hdiff
      _ = (∑ coarseSign ∈ planeCBForwardInteriorImageSignSet
              X i j k hij hik hjk n q,
            ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign z‖ ^ 2) +
          2 * ‖z‖ * ‖moved q - z‖ := by
        rw [hnorm]
        ring
  have htarget :
      (∑ q : Fin (Fintype.card X),
          ∑ coarseSign ∈ planeCBForwardInteriorImageSignSet
              X i j k hij hik hjk n q,
            ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign z‖ ^ 2) ≤
        ∑ coarseSign ∈
            (planeRegionSignSet X i j k hij hik hjk (n + 1) .A ∪
              planeRegionSignSet X i j k hij hik hjk (n + 1) .D),
          ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign z‖ ^ 2 :=
    sum_planeCBForwardInteriorImageSignSet_le_A_union_D
      X i j k hij hik hjk n
      (fun coarseSign ↦
        ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign z‖ ^ 2)
      (fun _ ↦ sq_nonneg _)
  calc
    _ ≤ ∑ q : Fin (Fintype.card X),
          ∑ coarseSign ∈ planeCBForwardInteriorImageSignSet
              X i j k hij hik hjk n q,
            ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign
              (moved q)‖ ^ 2 := hfiber
    _ ≤ ∑ q : Fin (Fintype.card X),
          ((∑ coarseSign ∈ planeCBForwardInteriorImageSignSet
                X i j k hij hik hjk n q,
              ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign z‖ ^ 2) +
            2 * ‖z‖ * ‖moved q - z‖) := hmoved
    _ = (∑ q : Fin (Fintype.card X),
          ∑ coarseSign ∈ planeCBForwardInteriorImageSignSet
              X i j k hij hik hjk n q,
            ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign z‖ ^ 2) +
        ∑ q : Fin (Fintype.card X), 2 * ‖z‖ * ‖moved q - z‖ := by
      rw [Finset.sum_add_distrib]
    _ ≤ (∑ coarseSign ∈
          (planeRegionSignSet X i j k hij hik hjk (n + 1) .A ∪
            planeRegionSignSet X i j k hij hik hjk (n + 1) .D),
          ‖planeComponent X i j k hij hik hjk (n + 1) rho coarseSign z‖ ^ 2) +
        ∑ q : Fin (Fintype.card X), 2 * ‖z‖ * ‖moved q - z‖ :=
      add_le_add htarget (le_refl _)
    _ = _ := by rfl

/-- The omitted part of an `A ∪ B` leading fiber consists exactly of signs
whose second character is first detected in the fine stage's top degree. -/
noncomputable def planeABTopBoundaryLeadingSignSet
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (q : Fin (Fintype.card X)) :
    Finset (Fin (Nat.card (Plane X i j k hij hik hjk (n + 2))) → Bool) :=
  (planeABLeadingSignSet X i j k hij hik hjk (n + 1) q).filter
    fun sign ↦
      secondCoefficientValuation X i j k hij hik hjk (n + 2) sign = n + 2

/-- Symmetrically, the omitted `C ∪ B` part is the top-degree first-character
layer. -/
noncomputable def planeCBTopBoundaryLeadingSignSet
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (q : Fin (Fintype.card X)) :
    Finset (Fin (Nat.card (Plane X i j k hij hik hjk (n + 2))) → Bool) :=
  (planeCBLeadingSignSet X i j k hij hik hjk (n + 1) q).filter
    fun sign ↦
      firstCoefficientValuation X i j k hij hik hjk (n + 2) sign = n + 2

theorem secondCoefficientValuation_le_top_of_mem_planeABLeadingSignSet
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (q : Fin (Fintype.card X))
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk (n + 2))) → Bool)
    (hsign : sign ∈ planeABLeadingSignSet X i j k hij hik hjk (n + 1) q) :
    secondCoefficientValuation X i j k hij hik hjk (n + 2) sign ≤ n + 2 := by
  simp only [planeABLeadingSignSet, Finset.mem_filter, Finset.mem_univ,
    true_and] at hsign
  have hfirstBound := characterValuation_le_succ X
    (firstCoefficientEigenvalue X i j k hij hik hjk (n + 2) sign)
  have hsecondBound := characterValuation_le_succ X
    (secondCoefficientEigenvalue X i j k hij hik hjk (n + 2) sign)
  change firstCoefficientValuation X i j k hij hik hjk (n + 2) sign ≤
    n + 3 at hfirstBound
  change secondCoefficientValuation X i j k hij hik hjk (n + 2) sign ≤
    n + 3 at hsecondBound
  rcases hsign.1 with hA | hB
  · have hdata := characterPairRegion_A_data X (n + 2)
      (firstCoefficientEigenvalue X i j k hij hik hjk (n + 2) sign)
      (secondCoefficientEigenvalue X i j k hij hik hjk (n + 2) sign) hA
    exact Nat.le_of_lt_succ (hdata.2.2.2.trans_le hfirstBound)
  · have hdata := characterPairRegion_B_data X (n + 2)
      (firstCoefficientEigenvalue X i j k hij hik hjk (n + 2) sign)
      (secondCoefficientEigenvalue X i j k hij hik hjk (n + 2) sign) hB
    by_contra hnot
    have hsecond : secondCoefficientValuation X i j k hij hik hjk (n + 2) sign =
        n + 3 := by omega
    have hfirst : firstCoefficientValuation X i j k hij hik hjk (n + 2) sign =
        n + 3 := hdata.2.2.2.trans hsecond
    exact hdata.1 ⟨hfirst, hsecond⟩

theorem firstCoefficientValuation_le_top_of_mem_planeCBLeadingSignSet
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (q : Fin (Fintype.card X))
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk (n + 2))) → Bool)
    (hsign : sign ∈ planeCBLeadingSignSet X i j k hij hik hjk (n + 1) q) :
    firstCoefficientValuation X i j k hij hik hjk (n + 2) sign ≤ n + 2 := by
  simp only [planeCBLeadingSignSet, Finset.mem_filter, Finset.mem_univ,
    true_and] at hsign
  have hfirstBound := characterValuation_le_succ X
    (firstCoefficientEigenvalue X i j k hij hik hjk (n + 2) sign)
  have hsecondBound := characterValuation_le_succ X
    (secondCoefficientEigenvalue X i j k hij hik hjk (n + 2) sign)
  change firstCoefficientValuation X i j k hij hik hjk (n + 2) sign ≤
    n + 3 at hfirstBound
  change secondCoefficientValuation X i j k hij hik hjk (n + 2) sign ≤
    n + 3 at hsecondBound
  rcases hsign.1 with hC | hB
  · have hdata := characterPairRegion_C_data X (n + 2)
      (firstCoefficientEigenvalue X i j k hij hik hjk (n + 2) sign)
      (secondCoefficientEigenvalue X i j k hij hik hjk (n + 2) sign) hC
    exact Nat.le_of_lt_succ (hdata.2.2.2.trans_le hsecondBound)
  · have hdata := characterPairRegion_B_data X (n + 2)
      (firstCoefficientEigenvalue X i j k hij hik hjk (n + 2) sign)
      (secondCoefficientEigenvalue X i j k hij hik hjk (n + 2) sign) hB
    by_contra hnot
    have hfirst : firstCoefficientValuation X i j k hij hik hjk (n + 2) sign =
        n + 3 := by omega
    have hsecond : secondCoefficientValuation X i j k hij hik hjk (n + 2) sign =
        n + 3 := hdata.2.2.2.symm.trans hfirst
    exact hdata.1 ⟨hfirst, hsecond⟩

theorem planeABLeadingSignSet_eq_interior_union_topBoundary
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (q : Fin (Fintype.card X)) :
    planeABLeadingSignSet X i j k hij hik hjk (n + 1) q =
      planeABInteriorLeadingSignSet X i j k hij hik hjk n q ∪
        planeABTopBoundaryLeadingSignSet X i j k hij hik hjk n q := by
  classical
  ext sign
  simp only [planeABInteriorLeadingSignSet,
    planeABTopBoundaryLeadingSignSet, Finset.mem_filter, Finset.mem_union]
  constructor
  · intro hsign
    have hbound := secondCoefficientValuation_le_top_of_mem_planeABLeadingSignSet
      X i j k hij hik hjk n q sign hsign
    by_cases hle : secondCoefficientValuation X i j k hij hik hjk (n + 2) sign ≤
        n + 1
    · exact Or.inl ⟨hsign, hle⟩
    · exact Or.inr ⟨hsign, by omega⟩
  · rintro (⟨hsign, _⟩ | ⟨hsign, _⟩) <;> exact hsign

theorem planeCBLeadingSignSet_eq_interior_union_topBoundary
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (q : Fin (Fintype.card X)) :
    planeCBLeadingSignSet X i j k hij hik hjk (n + 1) q =
      planeCBInteriorLeadingSignSet X i j k hij hik hjk n q ∪
        planeCBTopBoundaryLeadingSignSet X i j k hij hik hjk n q := by
  classical
  ext sign
  simp only [planeCBInteriorLeadingSignSet,
    planeCBTopBoundaryLeadingSignSet, Finset.mem_filter, Finset.mem_union]
  constructor
  · intro hsign
    have hbound := firstCoefficientValuation_le_top_of_mem_planeCBLeadingSignSet
      X i j k hij hik hjk n q sign hsign
    by_cases hle : firstCoefficientValuation X i j k hij hik hjk (n + 2) sign ≤
        n + 1
    · exact Or.inl ⟨hsign, hle⟩
    · exact Or.inr ⟨hsign, by omega⟩
  · rintro (⟨hsign, _⟩ | ⟨hsign, _⟩) <;> exact hsign

theorem planeABInteriorLeadingSignSet_disjoint_topBoundary
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (q : Fin (Fintype.card X)) :
    Disjoint (planeABInteriorLeadingSignSet X i j k hij hik hjk n q)
      (planeABTopBoundaryLeadingSignSet X i j k hij hik hjk n q) := by
  classical
  rw [Finset.disjoint_left]
  intro sign hinterior htop
  simp only [planeABInteriorLeadingSignSet,
    planeABTopBoundaryLeadingSignSet, Finset.mem_filter] at hinterior htop
  omega

theorem planeCBInteriorLeadingSignSet_disjoint_topBoundary
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (q : Fin (Fintype.card X)) :
    Disjoint (planeCBInteriorLeadingSignSet X i j k hij hik hjk n q)
      (planeCBTopBoundaryLeadingSignSet X i j k hij hik hjk n q) := by
  classical
  rw [Finset.disjoint_left]
  intro sign hinterior htop
  simp only [planeCBInteriorLeadingSignSet,
    planeCBTopBoundaryLeadingSignSet, Finset.mem_filter] at hinterior htop
  omega

theorem planeABTopBoundaryLeadingSignSet_pairwise_disjoint
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) :
    Pairwise (fun q r : Fin (Fintype.card X) ↦
      Disjoint (planeABTopBoundaryLeadingSignSet X i j k hij hik hjk n q)
        (planeABTopBoundaryLeadingSignSet X i j k hij hik hjk n r)) := by
  intro q r hqr
  exact (planeABLeadingSignSet_pairwise_disjoint
    X i j k hij hik hjk (n + 1) hqr).mono
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)

theorem planeCBTopBoundaryLeadingSignSet_pairwise_disjoint
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) :
    Pairwise (fun q r : Fin (Fintype.card X) ↦
      Disjoint (planeCBTopBoundaryLeadingSignSet X i j k hij hik hjk n q)
        (planeCBTopBoundaryLeadingSignSet X i j k hij hik hjk n r)) := by
  intro q r hqr
  exact (planeCBLeadingSignSet_pairwise_disjoint
    X i j k hij hik hjk (n + 1) hqr).mono
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)

theorem sum_planeABLeadingSignSet_eq_interior_add_topBoundary
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (f : (Fin (Nat.card (Plane X i j k hij hik hjk (n + 2))) → Bool) → ℝ) :
    (∑ q : Fin (Fintype.card X),
        ∑ sign ∈ planeABLeadingSignSet X i j k hij hik hjk (n + 1) q,
          f sign) =
      (∑ q : Fin (Fintype.card X),
        ∑ sign ∈ planeABInteriorLeadingSignSet X i j k hij hik hjk n q,
          f sign) +
      ∑ q : Fin (Fintype.card X),
        ∑ sign ∈ planeABTopBoundaryLeadingSignSet X i j k hij hik hjk n q,
          f sign := by
  classical
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  rw [planeABLeadingSignSet_eq_interior_union_topBoundary]
  exact Finset.sum_union
    (planeABInteriorLeadingSignSet_disjoint_topBoundary
      X i j k hij hik hjk n q)

theorem sum_planeCBLeadingSignSet_eq_interior_add_topBoundary
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (f : (Fin (Nat.card (Plane X i j k hij hik hjk (n + 2))) → Bool) → ℝ) :
    (∑ q : Fin (Fintype.card X),
        ∑ sign ∈ planeCBLeadingSignSet X i j k hij hik hjk (n + 1) q,
          f sign) =
      (∑ q : Fin (Fintype.card X),
        ∑ sign ∈ planeCBInteriorLeadingSignSet X i j k hij hik hjk n q,
          f sign) +
      ∑ q : Fin (Fintype.card X),
        ∑ sign ∈ planeCBTopBoundaryLeadingSignSet X i j k hij hik hjk n q,
          f sign := by
  classical
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  rw [planeCBLeadingSignSet_eq_interior_union_topBoundary]
  exact Finset.sum_union
    (planeCBInteriorLeadingSignSet_disjoint_topBoundary
      X i j k hij hik hjk n q)

theorem sum_norm_planeABTopBoundaryLeadingSignSet_sq_le
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    (∑ q : Fin (Fintype.card X),
        ∑ sign ∈ planeABTopBoundaryLeadingSignSet
            X i j k hij hik hjk n q,
          ‖planeComponent X i j k hij hik hjk (n + 2) rho sign z‖ ^ 2) ≤
      planeSecondTopBoundaryMass X i j k hij hik hjk rho z (n + 2) := by
  classical
  have hpair :
      ((Finset.univ : Finset (Fin (Fintype.card X))) : Set _).PairwiseDisjoint
        (planeABTopBoundaryLeadingSignSet X i j k hij hik hjk n) := by
    intro q _ r _ hqr
    exact planeABTopBoundaryLeadingSignSet_pairwise_disjoint
      X i j k hij hik hjk n hqr
  rw [← Finset.sum_biUnion hpair]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro sign hsign
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hsign
    obtain ⟨q, hq⟩ := hsign
    simp only [planeABTopBoundaryLeadingSignSet, Finset.mem_filter] at hq
    simpa [planeSecondTopBoundarySignSet] using hq.2
  · intro _ _ _
    exact sq_nonneg _

theorem sum_norm_planeCBTopBoundaryLeadingSignSet_sq_le
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    (∑ q : Fin (Fintype.card X),
        ∑ sign ∈ planeCBTopBoundaryLeadingSignSet
            X i j k hij hik hjk n q,
          ‖planeComponent X i j k hij hik hjk (n + 2) rho sign z‖ ^ 2) ≤
      planeFirstTopBoundaryMass X i j k hij hik hjk rho z (n + 2) := by
  classical
  have hpair :
      ((Finset.univ : Finset (Fin (Fintype.card X))) : Set _).PairwiseDisjoint
        (planeCBTopBoundaryLeadingSignSet X i j k hij hik hjk n) := by
    intro q _ r _ hqr
    exact planeCBTopBoundaryLeadingSignSet_pairwise_disjoint
      X i j k hij hik hjk n hqr
  rw [← Finset.sum_biUnion hpair]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro sign hsign
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hsign
    obtain ⟨q, hq⟩ := hsign
    simp only [planeCBTopBoundaryLeadingSignSet, Finset.mem_filter] at hq
    simpa [planeFirstTopBoundarySignSet] using hq.2
  · intro _ _ _
    exact sq_nonneg _

/-- Full finite-stage `A ∪ B` estimate: the only term not controlled by the
fixed adjacent generators is the explicit second-coordinate top-degree layer,
which tends to zero by the telescoping theorem above. -/
theorem sum_norm_planeABRegion_sq_le_target_add_error_add_boundary
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    (∑ sign ∈ (planeRegionSignSet X i j k hij hik hjk (n + 2) .A ∪
          planeRegionSignSet X i j k hij hik hjk (n + 2) .B),
        ‖planeComponent X i j k hij hik hjk (n + 2) rho sign z‖ ^ 2) ≤
      ((∑ sign ∈
          (planeRegionSignSet X i j k hij hik hjk (n + 1) .C ∪
            planeRegionSignSet X i j k hij hik hjk (n + 1) .D),
          ‖planeComponent X i j k hij hik hjk (n + 1) rho sign z‖ ^ 2) +
        ∑ q : Fin (Fintype.card X),
          2 * ‖z‖ *
            ‖rho (elementaryRoot j i hij.symm
              (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z - z‖) +
        planeSecondTopBoundaryMass X i j k hij hik hjk rho z (n + 2) := by
  classical
  let componentMass := fun sign :
      Fin (Nat.card (Plane X i j k hij hik hjk (n + 2))) → Bool ↦
    ‖planeComponent X i j k hij hik hjk (n + 2) rho sign z‖ ^ 2
  calc
    _ = ∑ q : Fin (Fintype.card X),
          ∑ sign ∈ planeABLeadingSignSet X i j k hij hik hjk (n + 1) q,
            componentMass sign :=
      sum_planeABLeadingSignSet X i j k hij hik hjk (n + 1) componentMass
    _ = (∑ q : Fin (Fintype.card X),
          ∑ sign ∈ planeABInteriorLeadingSignSet X i j k hij hik hjk n q,
            componentMass sign) +
        ∑ q : Fin (Fintype.card X),
          ∑ sign ∈ planeABTopBoundaryLeadingSignSet X i j k hij hik hjk n q,
            componentMass sign :=
      sum_planeABLeadingSignSet_eq_interior_add_topBoundary
        X i j k hij hik hjk n componentMass
    _ ≤ ((∑ sign ∈
            (planeRegionSignSet X i j k hij hik hjk (n + 1) .C ∪
              planeRegionSignSet X i j k hij hik hjk (n + 1) .D),
            ‖planeComponent X i j k hij hik hjk (n + 1) rho sign z‖ ^ 2) +
          ∑ q : Fin (Fintype.card X),
            2 * ‖z‖ *
              ‖rho (elementaryRoot j i hij.symm
                (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z - z‖) +
          planeSecondTopBoundaryMass X i j k hij hik hjk rho z (n + 2) :=
      add_le_add
        (sum_norm_planeABInteriorLeadingSignSet_sq_le_target_add_error
          X i j k hij hik hjk n rho z)
        (sum_norm_planeABTopBoundaryLeadingSignSet_sq_le
          X i j k hij hik hjk n rho z)

/-- Symmetric full `C ∪ B` estimate with its explicit first-coordinate
top-degree boundary. -/
theorem sum_norm_planeCBRegion_sq_le_target_add_error_add_boundary
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    (∑ sign ∈ (planeRegionSignSet X i j k hij hik hjk (n + 2) .C ∪
          planeRegionSignSet X i j k hij hik hjk (n + 2) .B),
        ‖planeComponent X i j k hij hik hjk (n + 2) rho sign z‖ ^ 2) ≤
      ((∑ sign ∈
          (planeRegionSignSet X i j k hij hik hjk (n + 1) .A ∪
            planeRegionSignSet X i j k hij hik hjk (n + 1) .D),
          ‖planeComponent X i j k hij hik hjk (n + 1) rho sign z‖ ^ 2) +
        ∑ q : Fin (Fintype.card X),
          2 * ‖z‖ *
            ‖rho (elementaryRoot i j hij
              (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z - z‖) +
        planeFirstTopBoundaryMass X i j k hij hik hjk rho z (n + 2) := by
  classical
  let componentMass := fun sign :
      Fin (Nat.card (Plane X i j k hij hik hjk (n + 2))) → Bool ↦
    ‖planeComponent X i j k hij hik hjk (n + 2) rho sign z‖ ^ 2
  calc
    _ = ∑ q : Fin (Fintype.card X),
          ∑ sign ∈ planeCBLeadingSignSet X i j k hij hik hjk (n + 1) q,
            componentMass sign :=
      sum_planeCBLeadingSignSet X i j k hij hik hjk (n + 1) componentMass
    _ = (∑ q : Fin (Fintype.card X),
          ∑ sign ∈ planeCBInteriorLeadingSignSet X i j k hij hik hjk n q,
            componentMass sign) +
        ∑ q : Fin (Fintype.card X),
          ∑ sign ∈ planeCBTopBoundaryLeadingSignSet X i j k hij hik hjk n q,
            componentMass sign :=
      sum_planeCBLeadingSignSet_eq_interior_add_topBoundary
        X i j k hij hik hjk n componentMass
    _ ≤ ((∑ sign ∈
            (planeRegionSignSet X i j k hij hik hjk (n + 1) .A ∪
              planeRegionSignSet X i j k hij hik hjk (n + 1) .D),
            ‖planeComponent X i j k hij hik hjk (n + 1) rho sign z‖ ^ 2) +
          ∑ q : Fin (Fintype.card X),
            2 * ‖z‖ *
              ‖rho (elementaryRoot i j hij
                (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z - z‖) +
          planeFirstTopBoundaryMass X i j k hij hik hjk rho z (n + 2) :=
      add_le_add
        (sum_norm_planeCBInteriorLeadingSignSet_sq_le_target_add_error
          X i j k hij hik hjk n rho z)
        (sum_norm_planeCBTopBoundaryLeadingSignSet_sq_le
          X i j k hij hik hjk n rho z)

/-- Full `A ∪ B` estimate with source and target at the same finite stage.
The price of replacing the coarse target is exactly the two proved
top-degree boundary masses. -/
theorem planeABMass_le_sameStage_CDMass_add_errors
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    planeRegionUnionMass X i j k hij hik hjk rho z (n + 2) .A .B ≤
      planeRegionUnionMass X i j k hij hik hjk rho z (n + 2) .C .D +
        (∑ q : Fin (Fintype.card X),
          2 * ‖z‖ *
            ‖rho (elementaryRoot j i hij.symm
              (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z - z‖) +
        planeFirstTopBoundaryMass X i j k hij hik hjk rho z (n + 2) +
        2 * planeSecondTopBoundaryMass X i j k hij hik hjk rho z (n + 2) := by
  have hfull := sum_norm_planeABRegion_sq_le_target_add_error_add_boundary
    X i j k hij hik hjk n rho z
  have hrefine := sum_norm_planeRegionUnion_sq_le_succ_add_topBoundaries
    X i j k hij hik hjk (n + 1) .C .D rho z
  change planeRegionUnionMass X i j k hij hik hjk rho z (n + 2) .A .B ≤
    planeRegionUnionMass X i j k hij hik hjk rho z (n + 1) .C .D +
      (∑ q : Fin (Fintype.card X),
        2 * ‖z‖ *
          ‖rho (elementaryRoot j i hij.symm
            (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z - z‖) +
      planeSecondTopBoundaryMass X i j k hij hik hjk rho z (n + 2) at hfull
  change planeRegionUnionMass X i j k hij hik hjk rho z (n + 1) .C .D ≤
    planeRegionUnionMass X i j k hij hik hjk rho z (n + 2) .C .D +
      planeFirstTopBoundaryMass X i j k hij hik hjk rho z (n + 2) +
      planeSecondTopBoundaryMass X i j k hij hik hjk rho z (n + 2) at hrefine
  linarith

/-- Symmetric same-stage `C ∪ B` estimate. -/
theorem planeCBMass_le_sameStage_ADMass_add_errors
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    planeRegionUnionMass X i j k hij hik hjk rho z (n + 2) .C .B ≤
      planeRegionUnionMass X i j k hij hik hjk rho z (n + 2) .A .D +
        (∑ q : Fin (Fintype.card X),
          2 * ‖z‖ *
            ‖rho (elementaryRoot i j hij
              (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z - z‖) +
        2 * planeFirstTopBoundaryMass X i j k hij hik hjk rho z (n + 2) +
        planeSecondTopBoundaryMass X i j k hij hik hjk rho z (n + 2) := by
  have hfull := sum_norm_planeCBRegion_sq_le_target_add_error_add_boundary
    X i j k hij hik hjk n rho z
  have hrefine := sum_norm_planeRegionUnion_sq_le_succ_add_topBoundaries
    X i j k hij hik hjk (n + 1) .A .D rho z
  change planeRegionUnionMass X i j k hij hik hjk rho z (n + 2) .C .B ≤
    planeRegionUnionMass X i j k hij hik hjk rho z (n + 1) .A .D +
      (∑ q : Fin (Fintype.card X),
        2 * ‖z‖ *
          ‖rho (elementaryRoot i j hij
            (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z - z‖) +
      planeFirstTopBoundaryMass X i j k hij hik hjk rho z (n + 2) at hfull
  change planeRegionUnionMass X i j k hij hik hjk rho z (n + 1) .A .D ≤
    planeRegionUnionMass X i j k hij hik hjk rho z (n + 2) .A .D +
      planeFirstTopBoundaryMass X i j k hij hik hjk rho z (n + 2) +
      planeSecondTopBoundaryMass X i j k hij hik hjk rho z (n + 2) at hrefine
  linarith

/-- The part of region `D` detected on the first unit coefficient. -/
noncomputable def planeDFirstSignSet
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) :
    Finset (Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool) :=
  (planeRegionSignSet X i j k hij hik hjk n .D).filter fun sign ↦
    firstCoefficientValuation X i j k hij hik hjk n sign = 0

/-- The remaining part of `D`; its second unit coefficient is necessarily
detected. -/
noncomputable def planeDSecondSignSet
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) :
    Finset (Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool) :=
  (planeRegionSignSet X i j k hij hik hjk n .D).filter fun sign ↦
    firstCoefficientValuation X i j k hij hik hjk n sign ≠ 0

theorem planeRegionSignSet_D_eq_unit_split
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) :
    planeRegionSignSet X i j k hij hik hjk n .D =
      planeDFirstSignSet X i j k hij hik hjk n ∪
        planeDSecondSignSet X i j k hij hik hjk n := by
  classical
  ext sign
  simp only [planeDFirstSignSet, planeDSecondSignSet,
    Finset.mem_filter, Finset.mem_union]
  tauto

theorem planeDFirstSignSet_disjoint_planeDSecondSignSet
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) :
    Disjoint (planeDFirstSignSet X i j k hij hik hjk n)
      (planeDSecondSignSet X i j k hij hik hjk n) := by
  classical
  rw [Finset.disjoint_left]
  intro sign hfirst hsecond
  simp only [planeDFirstSignSet, planeDSecondSignSet,
    Finset.mem_filter] at hfirst hsecond
  exact hsecond.2 hfirst.2

theorem planeDFirstSignSet_subset_negative_unit
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) :
    planeDFirstSignSet X i j k hij hik hjk n ⊆
      negativePlaneSignSet X i j k hij hik hjk n
        (firstCoordinate X i j k hij hik hjk n
          (wordMonomialInDegree X (ZMod 2) n 1)) := by
  classical
  intro sign hsign
  simp only [planeDFirstSignSet, Finset.mem_filter] at hsign
  have hdetect := (characterValuation_eq_zero_iff X
    (firstCoefficientEigenvalue X i j k hij hik hjk n sign)).1 hsign.2
  simpa [negativePlaneSignSet, firstCoefficientEigenvalue] using hdetect

theorem planeDSecondSignSet_subset_negative_unit
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) :
    planeDSecondSignSet X i j k hij hik hjk n ⊆
      negativePlaneSignSet X i j k hij hik hjk n
        (secondCoordinate X i j k hij hik hjk n
          (wordMonomialInDegree X (ZMod 2) n 1)) := by
  classical
  intro sign hsign
  simp only [planeDSecondSignSet, Finset.mem_filter] at hsign
  have hregion : planeCharacterRegion X i j k hij hik hjk n sign = .D := by
    simpa [planeRegionSignSet] using hsign.1
  have hzero := characterPairRegion_D_data X n
    (firstCoefficientEigenvalue X i j k hij hik hjk n sign)
    (secondCoefficientEigenvalue X i j k hij hik hjk n sign) hregion
  have hsecond : secondCoefficientValuation X i j k hij hik hjk n sign = 0 :=
    hzero.resolve_left hsign.2
  have hdetect := (characterValuation_eq_zero_iff X
    (secondCoefficientEigenvalue X i j k hij hik hjk n sign)).1 hsecond
  simpa [negativePlaneSignSet, secondCoefficientEigenvalue] using hdetect

/-- Region `D` is controlled exactly by the two unit-coordinate
displacements. -/
theorem sum_norm_planeRegionSignSet_D_sq_le_unit_displacements
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    (∑ sign ∈ planeRegionSignSet X i j k hij hik hjk n .D,
        ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2) ≤
      (4 : ℝ)⁻¹ *
          ‖rho (firstCoordinate X i j k hij hik hjk n
            (wordMonomialInDegree X (ZMod 2) n 1)).1 z - z‖ ^ 2 +
        (4 : ℝ)⁻¹ *
          ‖rho (secondCoordinate X i j k hij hik hjk n
            (wordMonomialInDegree X (ZMod 2) n 1)).1 z - z‖ ^ 2 := by
  classical
  rw [planeRegionSignSet_D_eq_unit_split,
    Finset.sum_union
      (planeDFirstSignSet_disjoint_planeDSecondSignSet
        X i j k hij hik hjk n)]
  calc
    _ ≤ (∑ sign ∈ negativePlaneSignSet X i j k hij hik hjk n
            (firstCoordinate X i j k hij hik hjk n
              (wordMonomialInDegree X (ZMod 2) n 1)),
          ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2) +
        ∑ sign ∈ negativePlaneSignSet X i j k hij hik hjk n
            (secondCoordinate X i j k hij hik hjk n
              (wordMonomialInDegree X (ZMod 2) n 1)),
          ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2 :=
      add_le_add
        (Finset.sum_le_sum_of_subset_of_nonneg
          (planeDFirstSignSet_subset_negative_unit
            X i j k hij hik hjk n) (fun _ _ _ ↦ sq_nonneg _))
        (Finset.sum_le_sum_of_subset_of_nonneg
          (planeDSecondSignSet_subset_negative_unit
            X i j k hij hik hjk n) (fun _ _ _ ↦ sq_nonneg _))
    _ = _ := by
      rw [planeCharacterMass_eq_quarter_displacement,
        planeCharacterMass_eq_quarter_displacement]

/-- Under opposite unit conjugation, the first coefficient character becomes
the product of the two original characters. -/
theorem firstCoefficientEigenvalue_oppositeUnitConjugatedRestriction_of_valid
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool)
    (hvalid : IsPlaneCharacterSign X i j k hij hik hjk n sign) :
    firstCoefficientEigenvalue X i j k hij hik hjk n
        (fun q ↦ sign
          (oppositeUnitConjugatedPlaneIndex X i j k hij hik hjk n q)) =
      characterProduct X
        (firstCoefficientEigenvalue X i j k hij hik hjk n sign)
        (secondCoefficientEigenvalue X i j k hij hik hjk n sign) := by
  funext a
  rw [firstCoefficientEigenvalue,
    planeEigenvalue_oppositeUnitConjugatedRestriction]
  have hconj : oppositeUnitConjugatedPlane X i j k hij hik hjk n
      (firstCoordinate X i j k hij hik hjk n a) =
      firstCoordinate X i j k hij hik hjk n a *
        secondCoordinate X i j k hij hik hjk n a := by
    apply Subtype.ext
    change elementaryRoot j i hij.symm 1 * elementaryRoot i k hik a.1 *
        (elementaryRoot j i hij.symm 1)⁻¹ =
      elementaryRoot i k hik a.1 * elementaryRoot j k hjk a.1
    rw [elementaryRoot_conjugate, one_mul]
    exact (elementaryRoot_commute_of_ne j k i k hjk hik
      hik.symm hjk.symm _ _).eq
  rw [hconj, hvalid]
  rfl

/-- Opposite unit conjugation fixes the second coefficient character. -/
theorem secondCoefficientEigenvalue_oppositeUnitConjugatedRestriction
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool) :
    secondCoefficientEigenvalue X i j k hij hik hjk n
        (fun q ↦ sign
          (oppositeUnitConjugatedPlaneIndex X i j k hij hik hjk n q)) =
      secondCoefficientEigenvalue X i j k hij hik hjk n sign := by
  funext b
  rw [secondCoefficientEigenvalue,
    planeEigenvalue_oppositeUnitConjugatedRestriction]
  have hconj : oppositeUnitConjugatedPlane X i j k hij hik hjk n
      (secondCoordinate X i j k hij hik hjk n b) =
      secondCoordinate X i j k hij hik hjk n b := by
    apply Subtype.ext
    have hcomm := elementaryRoot_commute_of_ne j i j k hij.symm hjk
      hij hjk.symm (1 : FreeRing X) b.1
    change elementaryRoot j i hij.symm 1 * elementaryRoot j k hjk b.1 *
        (elementaryRoot j i hij.symm 1)⁻¹ = elementaryRoot j k hjk b.1
    rw [hcomm.eq]
    simp
  rw [hconj]
  rfl

/-- Forward unit conjugation fixes the first coefficient character. -/
theorem firstCoefficientEigenvalue_forwardUnitConjugatedRestriction
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool) :
    firstCoefficientEigenvalue X i j k hij hik hjk n
        (fun q ↦ sign
          (forwardUnitConjugatedPlaneIndex X i j k hij hik hjk n q)) =
      firstCoefficientEigenvalue X i j k hij hik hjk n sign := by
  funext a
  rw [firstCoefficientEigenvalue,
    planeEigenvalue_forwardUnitConjugatedRestriction]
  have hconj : forwardUnitConjugatedPlane X i j k hij hik hjk n
      (firstCoordinate X i j k hij hik hjk n a) =
      firstCoordinate X i j k hij hik hjk n a := by
    apply Subtype.ext
    have hcomm := elementaryRoot_commute_of_ne i j i k hij hik
      hij.symm hik.symm (1 : FreeRing X) a.1
    change elementaryRoot i j hij 1 * elementaryRoot i k hik a.1 *
        (elementaryRoot i j hij 1)⁻¹ = elementaryRoot i k hik a.1
    rw [hcomm.eq]
    simp
  rw [hconj]
  rfl

/-- Under forward unit conjugation, the second coefficient character becomes
the product of the two original characters. -/
theorem secondCoefficientEigenvalue_forwardUnitConjugatedRestriction_of_valid
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool)
    (hvalid : IsPlaneCharacterSign X i j k hij hik hjk n sign) :
    secondCoefficientEigenvalue X i j k hij hik hjk n
        (fun q ↦ sign
          (forwardUnitConjugatedPlaneIndex X i j k hij hik hjk n q)) =
      characterProduct X
        (firstCoefficientEigenvalue X i j k hij hik hjk n sign)
        (secondCoefficientEigenvalue X i j k hij hik hjk n sign) := by
  funext b
  rw [secondCoefficientEigenvalue,
    planeEigenvalue_forwardUnitConjugatedRestriction]
  have hconj : forwardUnitConjugatedPlane X i j k hij hik hjk n
      (secondCoordinate X i j k hij hik hjk n b) =
      firstCoordinate X i j k hij hik hjk n b *
        secondCoordinate X i j k hij hik hjk n b := by
    apply Subtype.ext
    change elementaryRoot i j hij 1 * elementaryRoot j k hjk b.1 *
        (elementaryRoot i j hij 1)⁻¹ =
      elementaryRoot i k hik b.1 * elementaryRoot j k hjk b.1
    rw [elementaryRoot_conjugate, one_mul]
  rw [hconj, hvalid]
  rfl

/-- The opposite unit shear sends every valid region-`A` sign into `B`. -/
theorem planeCharacterRegion_oppositeUnitConjugatedRestriction_eq_B_of_valid
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool)
    (hvalid : IsPlaneCharacterSign X i j k hij hik hjk n sign)
    (hA : planeCharacterRegion X i j k hij hik hjk n sign = .A) :
    planeCharacterRegion X i j k hij hik hjk n
        (fun q ↦ sign
          (oppositeUnitConjugatedPlaneIndex X i j k hij hik hjk n q)) = .B := by
  let chi := firstCoefficientEigenvalue X i j k hij hik hjk n sign
  let psi := secondCoefficientEigenvalue X i j k hij hik hjk n sign
  have hdata := characterPairRegion_A_data X n chi psi hA
  have hPsiExists : ∃ d, HasDetectionAtDegree X psi d := by
    by_contra hnone
    have hsentinel := characterValuation_eq_succ_of_not_exists X psi hnone
    have hchiBound := characterValuation_le_succ X chi
    omega
  have hproduct := characterValuation_characterProduct_eq_right_of_lt
    X chi psi
    (firstCoefficientEigenvalue_eq_one_or_neg_one X i j k hij hik hjk n sign)
    (secondCoefficientEigenvalue_eq_one_or_neg_one X i j k hij hik hjk n sign)
    hPsiExists hdata.2.2.2
  have hfirst := firstCoefficientEigenvalue_oppositeUnitConjugatedRestriction_of_valid
    X i j k hij hik hjk n sign hvalid
  have hsecond := secondCoefficientEigenvalue_oppositeUnitConjugatedRestriction
    X i j k hij hik hjk n sign
  unfold planeCharacterRegion
  rw [hfirst, hsecond]
  apply characterPairRegion_eq_B_of_data X n
  · intro hboth
    change characterValuation X (characterProduct X chi psi) = n + 1 ∧
      characterValuation X psi = n + 1 at hboth
    have hchiBound := characterValuation_le_succ X chi
    omega
  · rw [hproduct]
    exact hdata.2.2.1
  · exact hdata.2.2.1
  · exact hproduct

/-- The forward unit shear sends every valid region-`C` sign into `B`. -/
theorem planeCharacterRegion_forwardUnitConjugatedRestriction_eq_B_of_valid
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool)
    (hvalid : IsPlaneCharacterSign X i j k hij hik hjk n sign)
    (hC : planeCharacterRegion X i j k hij hik hjk n sign = .C) :
    planeCharacterRegion X i j k hij hik hjk n
        (fun q ↦ sign
          (forwardUnitConjugatedPlaneIndex X i j k hij hik hjk n q)) = .B := by
  let chi := firstCoefficientEigenvalue X i j k hij hik hjk n sign
  let psi := secondCoefficientEigenvalue X i j k hij hik hjk n sign
  have hdata := characterPairRegion_C_data X n chi psi hC
  have hChiExists : ∃ d, HasDetectionAtDegree X chi d := by
    by_contra hnone
    have hsentinel := characterValuation_eq_succ_of_not_exists X chi hnone
    have hpsiBound := characterValuation_le_succ X psi
    omega
  have hproduct := characterValuation_characterProduct_eq_left_of_lt
    X chi psi
    (firstCoefficientEigenvalue_eq_one_or_neg_one X i j k hij hik hjk n sign)
    (secondCoefficientEigenvalue_eq_one_or_neg_one X i j k hij hik hjk n sign)
    hChiExists hdata.2.2.2
  have hfirst := firstCoefficientEigenvalue_forwardUnitConjugatedRestriction
    X i j k hij hik hjk n sign
  have hsecond := secondCoefficientEigenvalue_forwardUnitConjugatedRestriction_of_valid
    X i j k hij hik hjk n sign hvalid
  unfold planeCharacterRegion
  rw [hfirst, hsecond]
  apply characterPairRegion_eq_B_of_data X n
  · intro hboth
    change characterValuation X chi = n + 1 ∧
      characterValuation X (characterProduct X chi psi) = n + 1 at hboth
    have hpsiBound := characterValuation_le_succ X psi
    omega
  · exact hdata.2.1
  · rw [hproduct]
    exact hdata.2.1
  · exact hproduct.symm

/-- The genuine multiplicative signs inside one valuation region. -/
noncomputable def planeValidRegionSignSet
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (region : ValuationRegion) :
    Finset (Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool) :=
  planeValidSignSubset X i j k hij hik hjk n
    (planeRegionSignSet X i j k hij hik hjk n region)

/-- Invalid binary assignments contribute zero, so every valuation region has
exactly the same mass after filtering to genuine multiplicative signs. -/
theorem sum_norm_planeRegionSignSet_eq_valid
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (region : ValuationRegion)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    (∑ sign ∈ planeRegionSignSet X i j k hij hik hjk n region,
        ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2) =
      ∑ sign ∈ planeValidRegionSignSet X i j k hij hik hjk n region,
        ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2 := by
  classical
  simpa [planeValidRegionSignSet] using
    sum_norm_planeSignSet_eq_filter_valid X i j k hij hik hjk n rho
      (planeRegionSignSet X i j k hij hik hjk n region) z

/-- Same-stage unit transport gives the quantitative `A → B` mass estimate
from Kassabov's argument. -/
theorem sum_norm_planeRegionSignSet_A_sq_le_B_add_unit_error
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    (∑ sign ∈ planeRegionSignSet X i j k hij hik hjk n .A,
        ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2) ≤
      (∑ sign ∈ planeRegionSignSet X i j k hij hik hjk n .B,
        ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2) +
      2 * ‖z‖ * ‖rho (elementaryRoot j i hij.symm 1) z - z‖ := by
  classical
  let source := planeRegionSignSet X i j k hij hik hjk n .A
  let validSource := source.filter
    (IsPlaneCharacterSign X i j k hij hik hjk n)
  let target := planeRegionSignSet X i j k hij hik hjk n .B
  let index := oppositeUnitConjugatedPlaneIndex X i j k hij hik hjk n
  let moved := rho (elementaryRoot j i hij.symm 1) z
  have hsubset : validSource ⊆ fineRestrictionSignSet
      (Nat.card (Plane X i j k hij hik hjk n))
      (Nat.card (Plane X i j k hij hik hjk n)) index target := by
    intro sign hsign
    obtain ⟨hsource, hvalid⟩ := Finset.mem_filter.mp hsign
    have hA : planeCharacterRegion X i j k hij hik hjk n sign = .A := by
      simpa [source, planeRegionSignSet] using hsource
    have hB :=
      planeCharacterRegion_oppositeUnitConjugatedRestriction_eq_B_of_valid
        X i j k hij hik hjk n sign hvalid hA
    simp only [fineRestrictionSignSet, Finset.mem_filter, Finset.mem_univ,
      true_and]
    simpa [index, target, planeRegionSignSet] using hB
  have htransport :
      (∑ sign ∈ source,
          ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2) ≤
        ∑ sign ∈ target,
          ‖planeComponent X i j k hij hik hjk n rho sign moved‖ ^ 2 := by
    calc
      _ = ∑ sign ∈ validSource,
          ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2 := by
        exact sum_norm_planeRegionSignSet_eq_valid
          X i j k hij hik hjk n .A rho z
      _ ≤ ∑ sign ∈ fineRestrictionSignSet
            (Nat.card (Plane X i j k hij hik hjk n))
            (Nat.card (Plane X i j k hij hik hjk n)) index target,
          ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun _ _ _ ↦ sq_nonneg _)
      _ = ∑ sign ∈ target,
          ‖planeComponent X i j k hij hik hjk n rho sign moved‖ ^ 2 :=
        sum_norm_oppositeUnitConjugatedRestriction_sq
          X i j k hij hik hjk n rho target z
  have hvariation := abs_sum_norm_planeComponent_sq_sub_le
    X i j k hij hik hjk n rho target moved z
  have hdiff :
      (∑ sign ∈ target,
          ‖planeComponent X i j k hij hik hjk n rho sign moved‖ ^ 2) -
        (∑ sign ∈ target,
          ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2) ≤
      (‖moved‖ + ‖z‖) * ‖moved - z‖ :=
    (le_abs_self _).trans hvariation
  rw [sub_le_iff_le_add] at hdiff
  have hnorm : ‖moved‖ = ‖z‖ :=
    (rho (elementaryRoot j i hij.symm 1)).norm_map z
  calc
    _ ≤ ∑ sign ∈ target,
          ‖planeComponent X i j k hij hik hjk n rho sign moved‖ ^ 2 := htransport
    _ ≤ (‖moved‖ + ‖z‖) * ‖moved - z‖ +
        ∑ sign ∈ target,
          ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2 := hdiff
    _ = (∑ sign ∈ target,
          ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2) +
        2 * ‖z‖ * ‖moved - z‖ := by rw [hnorm]; ring
    _ = _ := by rfl

/-- Symmetric quantitative `C → B` unit-shear estimate. -/
theorem sum_norm_planeRegionSignSet_C_sq_le_B_add_unit_error
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    (∑ sign ∈ planeRegionSignSet X i j k hij hik hjk n .C,
        ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2) ≤
      (∑ sign ∈ planeRegionSignSet X i j k hij hik hjk n .B,
        ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2) +
      2 * ‖z‖ * ‖rho (elementaryRoot i j hij 1) z - z‖ := by
  classical
  let source := planeRegionSignSet X i j k hij hik hjk n .C
  let validSource := source.filter
    (IsPlaneCharacterSign X i j k hij hik hjk n)
  let target := planeRegionSignSet X i j k hij hik hjk n .B
  let index := forwardUnitConjugatedPlaneIndex X i j k hij hik hjk n
  let moved := rho (elementaryRoot i j hij 1) z
  have hsubset : validSource ⊆ fineRestrictionSignSet
      (Nat.card (Plane X i j k hij hik hjk n))
      (Nat.card (Plane X i j k hij hik hjk n)) index target := by
    intro sign hsign
    obtain ⟨hsource, hvalid⟩ := Finset.mem_filter.mp hsign
    have hC : planeCharacterRegion X i j k hij hik hjk n sign = .C := by
      simpa [source, planeRegionSignSet] using hsource
    have hB :=
      planeCharacterRegion_forwardUnitConjugatedRestriction_eq_B_of_valid
        X i j k hij hik hjk n sign hvalid hC
    simp only [fineRestrictionSignSet, Finset.mem_filter, Finset.mem_univ,
      true_and]
    simpa [index, target, planeRegionSignSet] using hB
  have htransport :
      (∑ sign ∈ source,
          ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2) ≤
        ∑ sign ∈ target,
          ‖planeComponent X i j k hij hik hjk n rho sign moved‖ ^ 2 := by
    calc
      _ = ∑ sign ∈ validSource,
          ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2 := by
        exact sum_norm_planeRegionSignSet_eq_valid
          X i j k hij hik hjk n .C rho z
      _ ≤ ∑ sign ∈ fineRestrictionSignSet
            (Nat.card (Plane X i j k hij hik hjk n))
            (Nat.card (Plane X i j k hij hik hjk n)) index target,
          ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun _ _ _ ↦ sq_nonneg _)
      _ = ∑ sign ∈ target,
          ‖planeComponent X i j k hij hik hjk n rho sign moved‖ ^ 2 :=
        sum_norm_forwardUnitConjugatedRestriction_sq
          X i j k hij hik hjk n rho target z
  have hvariation := abs_sum_norm_planeComponent_sq_sub_le
    X i j k hij hik hjk n rho target moved z
  have hdiff :
      (∑ sign ∈ target,
          ‖planeComponent X i j k hij hik hjk n rho sign moved‖ ^ 2) -
        (∑ sign ∈ target,
          ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2) ≤
      (‖moved‖ + ‖z‖) * ‖moved - z‖ :=
    (le_abs_self _).trans hvariation
  rw [sub_le_iff_le_add] at hdiff
  have hnorm : ‖moved‖ = ‖z‖ :=
    (rho (elementaryRoot i j hij 1)).norm_map z
  calc
    _ ≤ ∑ sign ∈ target,
          ‖planeComponent X i j k hij hik hjk n rho sign moved‖ ^ 2 := htransport
    _ ≤ (‖moved‖ + ‖z‖) * ‖moved - z‖ +
        ∑ sign ∈ target,
          ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2 := hdiff
    _ = (∑ sign ∈ target,
          ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2) +
        2 * ‖z‖ * ‖moved - z‖ := by rw [hnorm]; ring
    _ = _ := by rfl

/-- Adding the two same-stage generator-shear inequalities cancels regions
`A` and `C`, leaving a direct bound for the diagonal region `B`. -/
theorem planeRegionMass_B_le_D_add_generatorErrors_add_boundaries
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    planeRegionMass X i j k hij hik hjk rho z (n + 2) .B ≤
      planeRegionMass X i j k hij hik hjk rho z (n + 2) .D +
        (2 : ℝ)⁻¹ *
          ((∑ q : Fin (Fintype.card X),
              2 * ‖z‖ *
                ‖rho (elementaryRoot j i hij.symm
                  (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z - z‖) +
            ∑ q : Fin (Fintype.card X),
              2 * ‖z‖ *
                ‖rho (elementaryRoot i j hij
                  (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z - z‖) +
        (3 : ℝ) / 2 *
          (planeFirstTopBoundaryMass X i j k hij hik hjk rho z (n + 2) +
            planeSecondTopBoundaryMass X i j k hij hik hjk rho z (n + 2)) := by
  have hab := planeABMass_le_sameStage_CDMass_add_errors
    X i j k hij hik hjk n rho z
  have hcb := planeCBMass_le_sameStage_ADMass_add_errors
    X i j k hij hik hjk n rho z
  rw [planeRegionUnionMass_eq_add X i j k hij hik hjk rho z (n + 2)
      .A .B (by decide),
    planeRegionUnionMass_eq_add X i j k hij hik hjk rho z (n + 2)
      .C .D (by decide)] at hab
  rw [planeRegionUnionMass_eq_add X i j k hij hik hjk rho z (n + 2)
      .C .B (by decide),
    planeRegionUnionMass_eq_add X i j k hij hik hjk rho z (n + 2)
      .A .D (by decide)] at hcb
  linarith

/-- Finite-stage Kassabov estimate for the total mass in all four nonzero
valuation regions.  Every term on the right is the displacement of an
explicit elementary generator, except the two boundary masses already proved
to converge to zero. -/
theorem sum_planeRegionMass_nonzero_le_explicit_errors
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    planeRegionMass X i j k hij hik hjk rho z (n + 2) .A +
        planeRegionMass X i j k hij hik hjk rho z (n + 2) .B +
        planeRegionMass X i j k hij hik hjk rho z (n + 2) .C +
        planeRegionMass X i j k hij hik hjk rho z (n + 2) .D ≤
      ‖rho (firstCoordinate X i j k hij hik hjk (n + 2)
          (wordMonomialInDegree X (ZMod 2) (n + 2) 1)).1 z - z‖ ^ 2 +
        ‖rho (secondCoordinate X i j k hij hik hjk (n + 2)
          (wordMonomialInDegree X (ZMod 2) (n + 2) 1)).1 z - z‖ ^ 2 +
        (3 : ℝ) / 2 *
          ((∑ q : Fin (Fintype.card X),
              2 * ‖z‖ *
                ‖rho (elementaryRoot j i hij.symm
                  (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z - z‖) +
            ∑ q : Fin (Fintype.card X),
              2 * ‖z‖ *
                ‖rho (elementaryRoot i j hij
                  (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z - z‖) +
        2 * ‖z‖ * ‖rho (elementaryRoot j i hij.symm 1) z - z‖ +
        2 * ‖z‖ * ‖rho (elementaryRoot i j hij 1) z - z‖ +
        (9 : ℝ) / 2 *
          (planeFirstTopBoundaryMass X i j k hij hik hjk rho z (n + 2) +
            planeSecondTopBoundaryMass X i j k hij hik hjk rho z (n + 2)) := by
  have hA := sum_norm_planeRegionSignSet_A_sq_le_B_add_unit_error
    X i j k hij hik hjk (n + 2) rho z
  have hC := sum_norm_planeRegionSignSet_C_sq_le_B_add_unit_error
    X i j k hij hik hjk (n + 2) rho z
  have hB := planeRegionMass_B_le_D_add_generatorErrors_add_boundaries
    X i j k hij hik hjk n rho z
  have hD := sum_norm_planeRegionSignSet_D_sq_le_unit_displacements
    X i j k hij hik hjk (n + 2) rho z
  change planeRegionMass X i j k hij hik hjk rho z (n + 2) .A ≤
    planeRegionMass X i j k hij hik hjk rho z (n + 2) .B +
      2 * ‖z‖ * ‖rho (elementaryRoot j i hij.symm 1) z - z‖ at hA
  change planeRegionMass X i j k hij hik hjk rho z (n + 2) .C ≤
    planeRegionMass X i j k hij hik hjk rho z (n + 2) .B +
      2 * ‖z‖ * ‖rho (elementaryRoot i j hij 1) z - z‖ at hC
  change planeRegionMass X i j k hij hik hjk rho z (n + 2) .D ≤
    (4 : ℝ)⁻¹ *
        ‖rho (firstCoordinate X i j k hij hik hjk (n + 2)
          (wordMonomialInDegree X (ZMod 2) (n + 2) 1)).1 z - z‖ ^ 2 +
      (4 : ℝ)⁻¹ *
        ‖rho (secondCoordinate X i j k hij hik hjk (n + 2)
          (wordMonomialInDegree X (ZMod 2) (n + 2) 1)).1 z - z‖ ^ 2 at hD
  linarith

/-- Limiting two-root relative Kazhdan estimate.  The finite Fourier boundary
terms disappear along the exhaustive free-word filtration, leaving only the
displacements of the explicit adjacent-root generators and the two unit
elements in the moving plane. -/
theorem norm_joinRootMovingProjection_sq_le_explicit_errors [CompleteSpace E]
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    ‖KazhdanFixedSpace.subgroupMovingProjection rho
        (elementaryRootSubgroup i k hik ⊔
          elementaryRootSubgroup j k hjk) z‖ ^ 2 ≤
      ‖rho (elementaryRoot i k hik 1) z - z‖ ^ 2 +
        ‖rho (elementaryRoot j k hjk 1) z - z‖ ^ 2 +
        (3 : ℝ) / 2 *
          ((∑ q : Fin (Fintype.card X),
              2 * ‖z‖ *
                ‖rho (elementaryRoot j i hij.symm
                  (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z - z‖) +
            ∑ q : Fin (Fintype.card X),
              2 * ‖z‖ *
                ‖rho (elementaryRoot i j hij
                  (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z - z‖) +
          2 * ‖z‖ * ‖rho (elementaryRoot j i hij.symm 1) z - z‖ +
          2 * ‖z‖ * ‖rho (elementaryRoot i j hij 1) z - z‖ := by
  let C : ℝ :=
    ‖rho (elementaryRoot i k hik 1) z - z‖ ^ 2 +
      ‖rho (elementaryRoot j k hjk 1) z - z‖ ^ 2 +
      (3 : ℝ) / 2 *
        ((∑ q : Fin (Fintype.card X),
            2 * ‖z‖ *
              ‖rho (elementaryRoot j i hij.symm
                (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z - z‖) +
          ∑ q : Fin (Fintype.card X),
            2 * ‖z‖ *
              ‖rho (elementaryRoot i j hij
                (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z - z‖) +
        2 * ‖z‖ * ‖rho (elementaryRoot j i hij.symm 1) z - z‖ +
        2 * ‖z‖ * ‖rho (elementaryRoot i j hij 1) z - z‖
  change
    ‖KazhdanFixedSpace.subgroupMovingProjection rho
        (elementaryRootSubgroup i k hik ⊔
          elementaryRootSubgroup j k hjk) z‖ ^ 2 ≤ C
  have hfinite (n : ℕ) :
      ‖planeMovingPart X i j k hij hik hjk rho z (n + 2)‖ ^ 2 ≤
        C + (9 : ℝ) / 2 *
          (planeFirstTopBoundaryMass X i j k hij hik hjk rho z (n + 2) +
            planeSecondTopBoundaryMass X i j k hij hik hjk rho z (n + 2)) := by
    rw [norm_planeMovingPart_sq_eq_sum_regionMass
      X i j k hij hik hjk rho z (n + 2)]
    have h := sum_planeRegionMass_nonzero_le_explicit_errors
      X i j k hij hik hjk n rho z
    simp only [firstCoordinate_val, secondCoordinate_val,
      wordMonomialInDegree_one_val] at h
    dsimp only [C]
    linarith
  have hleft : Filter.Tendsto
      (fun n ↦ ‖planeMovingPart X i j k hij hik hjk rho z (n + 2)‖ ^ 2)
      Filter.atTop
      (nhds (‖KazhdanFixedSpace.subgroupMovingProjection rho
        (elementaryRootSubgroup i k hik ⊔
          elementaryRootSubgroup j k hjk) z‖ ^ 2)) := by
    exact (Filter.tendsto_add_atTop_iff_nat 2).2
      (tendsto_norm_planeMovingPart_sq X i j k hij hik hjk rho z)
  have hfirst : Filter.Tendsto
      (fun n ↦ planeFirstTopBoundaryMass X i j k hij hik hjk rho z (n + 2))
      Filter.atTop (nhds 0) := by
    have h := (Filter.tendsto_add_atTop_iff_nat 1).2
      (tendsto_planeFirstTopBoundaryMass_succ_zero
        X i j k hij hik hjk rho z)
    simpa [Nat.add_assoc] using h
  have hsecond : Filter.Tendsto
      (fun n ↦ planeSecondTopBoundaryMass X i j k hij hik hjk rho z (n + 2))
      Filter.atTop (nhds 0) := by
    have h := (Filter.tendsto_add_atTop_iff_nat 1).2
      (tendsto_planeSecondTopBoundaryMass_succ_zero
        X i j k hij hik hjk rho z)
    simpa [Nat.add_assoc] using h
  have hscaled : Filter.Tendsto
      (fun n ↦ (9 : ℝ) / 2 *
        (planeFirstTopBoundaryMass X i j k hij hik hjk rho z (n + 2) +
          planeSecondTopBoundaryMass X i j k hij hik hjk rho z (n + 2)))
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul (hfirst.add hsecond))
  have hright : Filter.Tendsto
      (fun n ↦ C + (9 : ℝ) / 2 *
        (planeFirstTopBoundaryMass X i j k hij hik hjk rho z (n + 2) +
          planeSecondTopBoundaryMass X i j k hij hik hjk rho z (n + 2)))
      Filter.atTop (nhds C) := by
    simpa using tendsto_const_nhds.add hscaled
  exact le_of_tendsto_of_tendsto hleft hright
    (Filter.Eventually.of_forall hfinite)

/-- The squared mass of one `A ∪ B` leading-generator fiber is bounded by
the coarse `C ∪ D` mass after acting by its opposite adjacent generator.
No component is counted through a merely algebraic character map: the proof
uses the concrete conjugated-plane refinement. -/
theorem sum_norm_planeABLeadingSignSet_sq_le
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (q : Fin (Fintype.card X))
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    ∑ fineSign ∈ planeABLeadingSignSet X i j k hij hik hjk n q,
        ‖planeComponent X i j k hij hik hjk (n + 1) rho fineSign z‖ ^ 2 ≤
      ∑ coarseSign ∈
          (planeRegionSignSet X i j k hij hik hjk n .C ∪
            planeRegionSignSet X i j k hij hik hjk n .D),
        ‖planeComponent X i j k hij hik hjk n rho coarseSign
          (rho (elementaryRoot j i hij.symm
            (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z)‖ ^ 2 := by
  classical
  let fiber := planeABLeadingSignSet X i j k hij hik hjk n q
  let nonzeroFiber := fiber.filter fun fineSign ↦
    planeComponent X i j k hij hik hjk (n + 1) rho fineSign z ≠ 0
  let target := planeRegionSignSet X i j k hij hik hjk n .C ∪
    planeRegionSignSet X i j k hij hik hjk n .D
  let index := oppositeConjugatedPlaneSuccIndex X i j k hij hik hjk
    (generatorEnumeration X q) n
  have hremove :
      ∑ fineSign ∈ fiber,
          ‖planeComponent X i j k hij hik hjk (n + 1) rho fineSign z‖ ^ 2 =
        ∑ fineSign ∈ nonzeroFiber,
          ‖planeComponent X i j k hij hik hjk (n + 1) rho fineSign z‖ ^ 2 := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro fineSign hmem hnot
    have hzero : planeComponent X i j k hij hik hjk (n + 1) rho fineSign z = 0 := by
      by_contra hne
      exact hnot (Finset.mem_filter.mpr ⟨hmem, hne⟩)
    rw [hzero]
    simp
  have hsubset : nonzeroFiber ⊆ fineRestrictionSignSet
      (Nat.card (Plane X i j k hij hik hjk (n + 1)))
      (Nat.card (Plane X i j k hij hik hjk n)) index target := by
    intro fineSign hmem
    obtain ⟨hfiber, hne⟩ := Finset.mem_filter.mp hmem
    have hregion :=
      planeCharacterRegion_oppositeConjugatedRestriction_eq_C_or_D
        X i j k hij hik hjk n q rho fineSign z hne hfiber
    simp only [fineRestrictionSignSet, Finset.mem_filter, Finset.mem_univ,
      true_and]
    change (fun r ↦ fineSign (index r)) ∈ target
    simpa [target, planeRegionSignSet] using hregion
  calc
    ∑ fineSign ∈ planeABLeadingSignSet X i j k hij hik hjk n q,
        ‖planeComponent X i j k hij hik hjk (n + 1) rho fineSign z‖ ^ 2 =
        ∑ fineSign ∈ nonzeroFiber,
          ‖planeComponent X i j k hij hik hjk (n + 1) rho fineSign z‖ ^ 2 :=
      hremove
    _ ≤ ∑ fineSign ∈ fineRestrictionSignSet
          (Nat.card (Plane X i j k hij hik hjk (n + 1)))
          (Nat.card (Plane X i j k hij hik hjk n)) index target,
          ‖planeComponent X i j k hij hik hjk (n + 1) rho fineSign z‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun _ _ _ ↦ sq_nonneg _)
    _ = ∑ coarseSign ∈ target,
          ‖planeComponent X i j k hij hik hjk n rho coarseSign
            (rho (elementaryRoot j i hij.symm
              (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z)‖ ^ 2 :=
      sum_norm_oppositeConjugatedRestriction_sq X i j k hij hik hjk
        (generatorEnumeration X q) n rho target z

/-- Symmetrically, one `C ∪ B` leading-generator fiber is bounded by the
coarse `A ∪ D` mass after the corresponding forward adjacent action. -/
theorem sum_norm_planeCBLeadingSignSet_sq_le
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (q : Fin (Fintype.card X))
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    ∑ fineSign ∈ planeCBLeadingSignSet X i j k hij hik hjk n q,
        ‖planeComponent X i j k hij hik hjk (n + 1) rho fineSign z‖ ^ 2 ≤
      ∑ coarseSign ∈
          (planeRegionSignSet X i j k hij hik hjk n .A ∪
            planeRegionSignSet X i j k hij hik hjk n .D),
        ‖planeComponent X i j k hij hik hjk n rho coarseSign
          (rho (elementaryRoot i j hij
            (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z)‖ ^ 2 := by
  classical
  let fiber := planeCBLeadingSignSet X i j k hij hik hjk n q
  let nonzeroFiber := fiber.filter fun fineSign ↦
    planeComponent X i j k hij hik hjk (n + 1) rho fineSign z ≠ 0
  let target := planeRegionSignSet X i j k hij hik hjk n .A ∪
    planeRegionSignSet X i j k hij hik hjk n .D
  let index := forwardConjugatedPlaneSuccIndex X i j k hij hik hjk
    (generatorEnumeration X q) n
  have hremove :
      ∑ fineSign ∈ fiber,
          ‖planeComponent X i j k hij hik hjk (n + 1) rho fineSign z‖ ^ 2 =
        ∑ fineSign ∈ nonzeroFiber,
          ‖planeComponent X i j k hij hik hjk (n + 1) rho fineSign z‖ ^ 2 := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro fineSign hmem hnot
    have hzero : planeComponent X i j k hij hik hjk (n + 1) rho fineSign z = 0 := by
      by_contra hne
      exact hnot (Finset.mem_filter.mpr ⟨hmem, hne⟩)
    rw [hzero]
    simp
  have hsubset : nonzeroFiber ⊆ fineRestrictionSignSet
      (Nat.card (Plane X i j k hij hik hjk (n + 1)))
      (Nat.card (Plane X i j k hij hik hjk n)) index target := by
    intro fineSign hmem
    obtain ⟨hfiber, hne⟩ := Finset.mem_filter.mp hmem
    have hregion :=
      planeCharacterRegion_forwardConjugatedRestriction_eq_A_or_D
        X i j k hij hik hjk n q rho fineSign z hne hfiber
    simp only [fineRestrictionSignSet, Finset.mem_filter, Finset.mem_univ,
      true_and]
    change (fun r ↦ fineSign (index r)) ∈ target
    simpa [target, planeRegionSignSet] using hregion
  calc
    ∑ fineSign ∈ planeCBLeadingSignSet X i j k hij hik hjk n q,
        ‖planeComponent X i j k hij hik hjk (n + 1) rho fineSign z‖ ^ 2 =
        ∑ fineSign ∈ nonzeroFiber,
          ‖planeComponent X i j k hij hik hjk (n + 1) rho fineSign z‖ ^ 2 :=
      hremove
    _ ≤ ∑ fineSign ∈ fineRestrictionSignSet
          (Nat.card (Plane X i j k hij hik hjk (n + 1)))
          (Nat.card (Plane X i j k hij hik hjk n)) index target,
          ‖planeComponent X i j k hij hik hjk (n + 1) rho fineSign z‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun _ _ _ ↦ sq_nonneg _)
    _ = ∑ coarseSign ∈ target,
          ‖planeComponent X i j k hij hik hjk n rho coarseSign
            (rho (elementaryRoot i j hij
              (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) z)‖ ^ 2 :=
      sum_norm_forwardConjugatedRestriction_sq X i j k hij hik hjk
        (generatorEnumeration X q) n rho target z

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
