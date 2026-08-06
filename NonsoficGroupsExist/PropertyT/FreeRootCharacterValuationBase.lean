import NonsoficGroupsExist.PropertyT.FreeRootPlaneFourier
import NonsoficGroupsExist.Kazhdan.KazhdanFixedSpace

/-!
# Valuations of finite-stage free-root characters

Kassabov's noncommutative relative-property-`(T)` argument partitions pairs
of additive characters by the least free-word degree on which each character
is nontrivial.  This file defines that valuation directly on the finite degree
stages.  The value `n + 1` represents a character that is trivial throughout
stage `n`; every genuinely detected character has valuation at most `n`.

This half is the combinatorics: the valuation itself, the leading-generator
index sets, the least-index selector, and the `A`/`B`/`C`/`D` region
partition, all over a finite alphabet with no Hilbert space in sight.
`FreeRootCharacterValuation` continues with the analytic half, where those
regions are transported across an orthogonal representation.
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
  fun a ↦ chi (coefficientSucc X (ZMod 2) a)

theorem hasDetectionAtDegree_of_restrictCharacterSucc
    {n d : ℕ} (chi : degreeLE X (ZMod 2) (n + 1) → ℝ)
    (h : HasDetectionAtDegree X (restrictCharacterSucc X chi) d) :
    HasDetectionAtDegree X chi d := by
  obtain ⟨w, hwd, hwn, hchi⟩ := h
  refine ⟨w, hwd, hwn.trans (Nat.le_succ n), ?_⟩
  unfold restrictCharacterSucc at hchi
  rw [coefficientSucc_wordMonomialInDegree X (ZMod 2) n w hwn] at hchi
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
  rw [coefficientSucc_wordMonomialInDegree X (ZMod 2) n w hwn]
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
  fun a ↦ chi (generatorMulCoefficientSucc X (ZMod 2) x a)

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
  change chi (generatorMulCoefficientSucc X (ZMod 2) x (a + b)) =
    chi (generatorMulCoefficientSucc X (ZMod 2) x a) *
      chi (generatorMulCoefficientSucc X (ZMod 2) x b)
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
    rw [generatorMulCoefficientSucc_wordMonomialInDegree X (ZMod 2) x n v hvStage]
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
    change chi (generatorMulCoefficientSucc X (ZMod 2) x
      (wordMonomialInDegree X (ZMod 2) n u)) = -1 at huChi
    rw [generatorMulCoefficientSucc_wordMonomialInDegree X (ZMod 2) x n u huStage]
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
      (firstCoordinate X (ZMod 2) i j k hij hik hjk n a) =
      firstCoordinate X (ZMod 2) i j k hij hik hjk (n + 1) (coefficientSucc X (ZMod 2) a) := by
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
      (secondCoordinate X (ZMod 2) i j k hij hik hjk n b) =
      secondCoordinate X (ZMod 2) i j k hij hik hjk (n + 1) (coefficientSucc X (ZMod 2) b) := by
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
    X (ZMod 2) i j k hij hik hjk n g
  have hmul := planeEigenvalue_mul_of_component_ne_zero
    X i j k hij hik hjk n rho sign z hv
      (firstCoordinate X (ZMod 2) i j k hij hik hjk n a)
      (secondCoordinate X (ZMod 2) i j k hij hik hjk n b)
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
      (rootPlaneDegreeSubgroup X (ZMod 2) i j k hij hik hjk n)) :
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
      (rootPlaneDegreeSubgroup X (ZMod 2) i j k hij hik hjk n) y).mp hy
      (planeFamily X i j k hij hik hjk n q)
      (planeEnumeration X i j k hij hik hjk n q).property
  have hvact := action_planeComponent X i j k hij hik hjk n rho sign z q
  simp [hq] at hvact
  have hiso := (rho (planeFamily X i j k hij hik hjk n q)).inner_map_map y
    (planeComponent X i j k hij hik hjk n rho sign z)
  rw [hyact, hvact] at hiso
  simp only [inner_neg_right] at hiso
  linarith


end

end FreeRootCharacterValuation

end NonsoficGroupsExist
