import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Finsupp.Supported

/-!
# Finite degree stages of a free algebra over finite coefficients

Kassabov's relative-property-`(T)` argument filters a free associative
algebra by word degree.  This file constructs that filtration without any
choice of a polynomial normal form: it uses the canonical equivalence with
the monoid algebra of the free monoid.  For a finite alphabet the stages are
defined over an arbitrary commutative coefficient semiring; each stage is
finite whenever the coefficients are finite, and the stages exhaust the
whole free algebra.  Only the exact-support expansion at the end of the file
uses that every nonzero `ZMod 2` coefficient equals one.
-/

namespace NonsoficGroupsExist

namespace FreeAlgebraDegree

variable (X : Type*) [Fintype X]
variable (k : Type*) [CommSemiring k]

/-- Add one letter to the front of a list, as an embedding. -/
def consEmbedding (x : X) : List X ↪ List X where
  toFun := List.cons x
  inj' := fun _ _ h ↦ List.cons.inj h |>.2

/-- All words whose length is at most `n`. -/
noncomputable def listWordsLE : ℕ → Finset (List X)
  | 0 => {[]}
  | n + 1 => by
      classical
      exact listWordsLE n ∪
        (Finset.univ : Finset X).biUnion fun x ↦
          (listWordsLE n).map (consEmbedding X x)

@[simp] theorem mem_listWordsLE (w : List X) (n : ℕ) :
    w ∈ listWordsLE X n ↔ w.length ≤ n := by
  induction n generalizing w with
  | zero =>
      simp [listWordsLE]
  | succ n ih =>
      cases w with
      | nil =>
          have hnil : [] ∈ listWordsLE X n :=
            (ih []).2 (Nat.zero_le n)
          simp [listWordsLE, hnil]
      | cons x w =>
          simp [listWordsLE, ih, consEmbedding]
          omega

/-- Word length on the free monoid, transported from lists. -/
def freeWordLength (w : FreeMonoid X) : ℕ :=
  ((FreeMonoid.ofList (α := X)).symm w).length

/-- The finite set of free-monoid words of length at most `n`. -/
noncomputable def freeWordsLE (n : ℕ) : Finset (FreeMonoid X) :=
  (listWordsLE X n).map (FreeMonoid.ofList (α := X)).toEmbedding

@[simp] theorem mem_freeWordsLE (w : FreeMonoid X) (n : ℕ) :
    w ∈ freeWordsLE X n ↔ freeWordLength X w ≤ n := by
  simp [freeWordsLE, freeWordLength]

omit [Fintype X] in
/-- Free-word length is additive under multiplication. -/
theorem freeWordLength_mul (u v : FreeMonoid X) :
    freeWordLength X (u * v) =
      freeWordLength X u + freeWordLength X v := by
  let e := FreeMonoid.ofList (α := X)
  obtain ⟨a, rfl⟩ := e.surjective u
  obtain ⟨b, rfl⟩ := e.surjective v
  simp [freeWordLength, e]

omit [Fintype X] in
/-- The only free word of length zero is the identity word. -/
theorem freeWordLength_eq_zero_iff (w : FreeMonoid X) :
    freeWordLength X w = 0 ↔ w = 1 := by
  let e := FreeMonoid.ofList (α := X)
  obtain ⟨l, rfl⟩ := e.surjective w
  change l.length = 0 ↔ e l = 1
  rw [List.length_eq_zero_iff]
  constructor
  · intro hl
    subst l
    simp [e]
  · intro hl
    apply e.injective
    simpa [e] using hl

omit [Fintype X] in
@[simp] theorem freeWordLength_of (x : X) :
    freeWordLength X (FreeMonoid.of x) = 1 := by
  simp [freeWordLength]

/-- Polynomials supported on words of degree at most `n`. -/
noncomputable def degreeLE (n : ℕ) :
    Submodule k (FreeAlgebra k X) :=
  (MonoidAlgebra.supported k k
      (freeWordsLE X n : Set (FreeMonoid X))).comap
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid
      (R := k) (X := X)).toLinearMap

theorem mem_degreeLE_iff (p : FreeAlgebra k X) (n : ℕ) :
    p ∈ degreeLE X k n ↔
      ∀ w ∈ (FreeAlgebra.equivMonoidAlgebraFreeMonoid
        (R := k) (X := X) p).coeff.support,
        freeWordLength X w ≤ n := by
  rw [degreeLE, Submodule.mem_comap, MonoidAlgebra.mem_supported]
  change
    (∀ w ∈ (FreeAlgebra.equivMonoidAlgebraFreeMonoid
      (R := k) (X := X) p).coeff.support,
      w ∈ freeWordsLE X n) ↔ _
  simp only [mem_freeWordsLE]

/-- Every degree stage over finite coefficients is a finite additive
group. -/
noncomputable instance finite_degreeLE [Finite k] (n : ℕ) :
    Finite (degreeLE X k n) := by
  let S : Set (FreeMonoid X) := freeWordsLE X n
  let V := MonoidAlgebra.supported k k S
  let toV : degreeLE X k n → V := fun p ↦
    ⟨FreeAlgebra.equivMonoidAlgebraFreeMonoid
      (R := k) (X := X) p.1, p.2⟩
  letI : Fintype S := Fintype.ofFinset (freeWordsLE X n) (by
    intro w
    rfl)
  let e := MonoidAlgebra.supportedEquivFinsupp
    (R := k) (S := k) S
  let coeffs : V → S → k := fun p w ↦ e p w
  letI : Finite V := Finite.of_injective coeffs fun p q h ↦ by
    apply e.injective
    ext w
    exact congrFun h w
  exact Finite.of_injective toV fun a b h ↦ by
    apply Subtype.ext
    apply (FreeAlgebra.equivMonoidAlgebraFreeMonoid
      (R := k) (X := X)).injective
    exact congrArg Subtype.val h

/-- The degree stages are monotone. -/
theorem degreeLE_mono : Monotone (degreeLE X k) := by
  intro m n hmn p hp
  rw [mem_degreeLE_iff] at hp ⊢
  intro w hw
  exact (hp w hw).trans hmn

/-- Multiplication adds degree bounds. -/
theorem mul_mem_degreeLE {p q : FreeAlgebra k X} {m n : ℕ}
    (hp : p ∈ degreeLE X k m) (hq : q ∈ degreeLE X k n) :
    p * q ∈ degreeLE X k (m + n) := by
  classical
  rw [mem_degreeLE_iff] at hp hq ⊢
  intro w hw
  rw [map_mul] at hw
  have hmul := MonoidAlgebra.support_coeff_mul_subset
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid
      (R := k) (X := X) p)
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid
      (R := k) (X := X) q) hw
  rw [Finset.mem_mul] at hmul
  obtain ⟨u, hu, v, hv, huv⟩ := hmul
  rw [← huv, freeWordLength_mul]
  exact Nat.add_le_add (hp u hu) (hq v hv)

/-- A canonical free generator has degree one. -/
theorem generator_mem_degreeLE_one (x : X) :
    FreeAlgebra.ι k x ∈ degreeLE X k 1 := by
  rw [mem_degreeLE_iff]
  intro w hw
  simp [FreeAlgebra.equivMonoidAlgebraFreeMonoid] at hw
  rcases Finset.mem_singleton.mp
    (Finsupp.support_single_subset (Finsupp.mem_support_iff.mpr hw)) with rfl
  simp [freeWordLength]

/-- Left multiplication by a free generator advances the filtration by one
stage. -/
theorem generator_mul_mem_degreeLE_succ (x : X)
    {p : FreeAlgebra k X} {n : ℕ} (hp : p ∈ degreeLE X k n) :
    FreeAlgebra.ι k x * p ∈ degreeLE X k (n + 1) := by
  simpa [Nat.add_comm] using
    mul_mem_degreeLE X k (generator_mem_degreeLE_one X k x) hp

/-- Right multiplication by a free generator advances the filtration by one
stage. -/
theorem mul_generator_mem_degreeLE_succ (x : X)
    {p : FreeAlgebra k X} {n : ℕ} (hp : p ∈ degreeLE X k n) :
    p * FreeAlgebra.ι k x ∈ degreeLE X k (n + 1) := by
  exact mul_mem_degreeLE X k hp (generator_mem_degreeLE_one X k x)

omit [Fintype X] in
/-- The additive group of the free `ZMod 2` algebra has exponent two. -/
theorem add_self_eq_zero (p : FreeAlgebra (ZMod 2) X) : p + p = 0 := by
  calc
    p + p = (1 : ZMod 2) • p + (1 : ZMod 2) • p := by simp
    _ = ((1 : ZMod 2) + 1) • p := by rw [add_smul]
    _ = 0 := by
      rw [show (1 : ZMod 2) + 1 = 0 by decide, zero_smul]

/-- The canonical basis monomial belonging to a free word. -/
noncomputable def wordMonomial (w : FreeMonoid X) :
    FreeAlgebra k X :=
  (FreeAlgebra.equivMonoidAlgebraFreeMonoid
    (R := k) (X := X)).symm (MonoidAlgebra.single w 1)

theorem wordMonomial_mem_degreeLE {w : FreeMonoid X} {n : ℕ}
    (hw : freeWordLength X w ≤ n) : wordMonomial X k w ∈ degreeLE X k n := by
  rw [mem_degreeLE_iff]
  intro v hv
  simp [wordMonomial] at hv
  rcases Finset.mem_singleton.mp
    (Finsupp.support_single_subset (Finsupp.mem_support_iff.mpr hv)) with rfl
  exact hw

/-- A total degree-stage version of a word monomial. Words outside the stage
are sent to zero; on words of length at most `n` this is the genuine basis
monomial. -/
noncomputable def wordMonomialInDegree (n : ℕ) (w : FreeMonoid X) :
    degreeLE X k n :=
  if hw : freeWordLength X w ≤ n then
    ⟨wordMonomial X k w, wordMonomial_mem_degreeLE X k hw⟩
  else 0

@[simp] theorem wordMonomialInDegree_of_le {n : ℕ} (w : FreeMonoid X)
    (hw : freeWordLength X w ≤ n) :
    wordMonomialInDegree X k n w =
      ⟨wordMonomial X k w, wordMonomial_mem_degreeLE X k hw⟩ := by
  simp [wordMonomialInDegree, hw]

@[simp] theorem wordMonomialInDegree_of_not_le {n : ℕ} (w : FreeMonoid X)
    (hw : ¬ freeWordLength X w ≤ n) :
    wordMonomialInDegree X k n w = 0 := by
  simp [wordMonomialInDegree, hw]

omit [Fintype X] in
/-- Multiplication of basis monomials is free-word concatenation. -/
theorem wordMonomial_mul (u v : FreeMonoid X) :
    wordMonomial X k u * wordMonomial X k v = wordMonomial X k (u * v) := by
  apply (FreeAlgebra.equivMonoidAlgebraFreeMonoid
    (R := k) (X := X)).injective
  simp [wordMonomial]

omit [Fintype X] in
@[simp] theorem wordMonomial_one : wordMonomial X k 1 = 1 := by
  unfold wordMonomial
  rw [← MonoidAlgebra.one_def]
  exact (FreeAlgebra.equivMonoidAlgebraFreeMonoid
    (R := k) (X := X)).symm.map_one

/-- The empty-word monomial has coefficient value one in every finite degree
stage. -/
@[simp] theorem wordMonomialInDegree_one_val (n : ℕ) :
    (wordMonomialInDegree X k n 1).1 = 1 := by
  have hlen : freeWordLength X (1 : FreeMonoid X) ≤ n := by
    rw [(freeWordLength_eq_zero_iff X 1).2 rfl]
    exact Nat.zero_le n
  rw [wordMonomialInDegree_of_le X k 1 hlen]
  change wordMonomial X k 1 = 1
  exact wordMonomial_one X k

omit [Fintype X] in
/-- A length-zero basis monomial is the unit coefficient. -/
theorem wordMonomial_eq_one_of_freeWordLength_eq_zero
    (w : FreeMonoid X) (hw : freeWordLength X w = 0) :
    wordMonomial X k w = 1 := by
  rw [(freeWordLength_eq_zero_iff X w).1 hw, wordMonomial_one]

omit [Fintype X] in
/-- A one-letter basis monomial is the corresponding canonical free-algebra
generator. -/
theorem wordMonomial_of (x : X) :
    wordMonomial X k (FreeMonoid.of x) = FreeAlgebra.ι k x := by
  apply (FreeAlgebra.equivMonoidAlgebraFreeMonoid
    (R := k) (X := X)).injective
  simp [wordMonomial, FreeAlgebra.equivMonoidAlgebraFreeMonoid]

omit [Fintype X] in
/-- Every nonempty free word has a first letter and a tail, with the exact
length relation needed for induction over the degree filtration. -/
theorem exists_of_mul_of_freeWordLength_pos (w : FreeMonoid X)
    (hw : 0 < freeWordLength X w) :
    ∃ x : X, ∃ v : FreeMonoid X,
      w = FreeMonoid.of x * v ∧
      freeWordLength X v + 1 = freeWordLength X w := by
  let e := FreeMonoid.ofList (α := X)
  obtain ⟨l, rfl⟩ := e.surjective w
  cases l with
  | nil => simp [freeWordLength, e] at hw
  | cons x l =>
      refine ⟨x, e l, ?_, ?_⟩
      · simp [e]
      · simp [freeWordLength, e]

omit [Fintype X] in
/-- A positive-degree word monomial is a free generator times the monomial
of its tail. -/
theorem wordMonomial_eq_generator_mul_of_freeWordLength_pos
    (w : FreeMonoid X) (hw : 0 < freeWordLength X w) :
    ∃ x : X, ∃ v : FreeMonoid X,
      w = FreeMonoid.of x * v ∧
      wordMonomial X k w = FreeAlgebra.ι k x * wordMonomial X k v := by
  obtain ⟨x, v, hword, _⟩ := exists_of_mul_of_freeWordLength_pos X w hw
  refine ⟨x, v, hword, ?_⟩
  rw [hword, ← wordMonomial_mul X k (FreeMonoid.of x) v, wordMonomial_of]

omit [Fintype X] in
/-- Every free polynomial is the finite sum of its supported word terms. -/
theorem eq_sum_support_smul_wordMonomial (p : FreeAlgebra k X) :
    p = ∑ w ∈ (FreeAlgebra.equivMonoidAlgebraFreeMonoid
        (R := k) (X := X) p).coeff.support,
      ((FreeAlgebra.equivMonoidAlgebraFreeMonoid
        (R := k) (X := X) p).coeff w) • wordMonomial X k w := by
  apply (FreeAlgebra.equivMonoidAlgebraFreeMonoid
    (R := k) (X := X)).injective
  ext v
  simp [wordMonomial]
  have h := congrArg (fun f : FreeMonoid X →₀ k ↦ f v)
    (Finsupp.sum_single
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid
        (R := k) (X := X) p).coeff)
  simpa [Finsupp.sum] using h.symm

omit [Fintype X] in
/-- Over `ZMod 2`, every nonzero coefficient is one, so a free polynomial is
the sum of exactly the basis words in its support. -/
theorem eq_sum_support_wordMonomial (p : FreeAlgebra (ZMod 2) X) :
    p = ∑ w ∈ (FreeAlgebra.equivMonoidAlgebraFreeMonoid
        (R := ZMod 2) (X := X) p).coeff.support,
      wordMonomial X (ZMod 2) w := by
  calc
    p = ∑ w ∈ (FreeAlgebra.equivMonoidAlgebraFreeMonoid
          (R := ZMod 2) (X := X) p).coeff.support,
        ((FreeAlgebra.equivMonoidAlgebraFreeMonoid
          (R := ZMod 2) (X := X) p).coeff w) •
            wordMonomial X (ZMod 2) w :=
      eq_sum_support_smul_wordMonomial X (ZMod 2) p
    _ = ∑ w ∈ (FreeAlgebra.equivMonoidAlgebraFreeMonoid
          (R := ZMod 2) (X := X) p).coeff.support,
        wordMonomial X (ZMod 2) w := by
      apply Finset.sum_congr rfl
      intro w hw
      let c := (FreeAlgebra.equivMonoidAlgebraFreeMonoid
        (R := ZMod 2) (X := X) p).coeff w
      have hcoeff : c = 1 := by
        have hn : c ≠ 0 := by
          simpa using hw
        apply ZMod.val_injective
        have hc_lt : c.val < 2 := ZMod.val_lt c
        have hc_ne : c.val ≠ 0 := by
          intro hc
          apply hn
          apply ZMod.val_injective
          simpa using hc
        simp only [ZMod.val_one]
        omega
      simp [c, hcoeff]

/-- A degree-bounded free `ZMod 2` polynomial is the sum, inside its degree
submodule, of the basis words in its support. -/
theorem eq_sum_support_degreeWordMonomial {n : ℕ}
    (p : degreeLE X (ZMod 2) n) :
    let q := (FreeAlgebra.equivMonoidAlgebraFreeMonoid
      (R := ZMod 2) (X := X) p.1).coeff
    let term : {w // w ∈ q.support} → degreeLE X (ZMod 2) n := fun w ↦
      ⟨wordMonomial X (ZMod 2) w.1, wordMonomial_mem_degreeLE X (ZMod 2)
        (((mem_degreeLE_iff X (ZMod 2) p.1 n).1 p.2) w.1 w.2)⟩
    p = ∑ w, term w := by
  dsimp only
  apply Subtype.ext
  simp only [Submodule.coe_sum]
  change p.1 = ∑ w : {w // w ∈
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid
        (R := ZMod 2) (X := X) p.1).coeff.support},
    wordMonomial X (ZMod 2) w.1
  calc
    p.1 = ∑ w ∈ (FreeAlgebra.equivMonoidAlgebraFreeMonoid
          (R := ZMod 2) (X := X) p.1).coeff.support,
        wordMonomial X (ZMod 2) w := eq_sum_support_wordMonomial X p.1
    _ = ∑ w : {w // w ∈
        (FreeAlgebra.equivMonoidAlgebraFreeMonoid
          (R := ZMod 2) (X := X) p.1).coeff.support},
      wordMonomial X (ZMod 2) w.1 := (Finset.sum_attach _ _).symm

/-- A degree-bounded free polynomial is, inside its degree submodule, the
scalar combination of the basis words in its support. -/
theorem eq_sum_support_smul_degreeWordMonomial {n : ℕ}
    (p : degreeLE X k n) :
    let q := (FreeAlgebra.equivMonoidAlgebraFreeMonoid
      (R := k) (X := X) p.1).coeff
    let term : {w // w ∈ q.support} → degreeLE X k n := fun w ↦
      q w.1 • ⟨wordMonomial X k w.1, wordMonomial_mem_degreeLE X k
        (((mem_degreeLE_iff X k p.1 n).1 p.2) w.1 w.2)⟩
    p = ∑ w, term w := by
  dsimp only
  apply Subtype.ext
  rw [show (((∑ w : {w // w ∈ (FreeAlgebra.equivMonoidAlgebraFreeMonoid
      (R := k) (X := X) p.1).coeff.support},
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid
        (R := k) (X := X) p.1).coeff w.1 •
        (⟨wordMonomial X k w.1, wordMonomial_mem_degreeLE X k
          (((mem_degreeLE_iff X k p.1 n).1 p.2) w.1 w.2)⟩ :
            degreeLE X k n)) : degreeLE X k n) : FreeAlgebra k X) =
    ∑ w : {w // w ∈ (FreeAlgebra.equivMonoidAlgebraFreeMonoid
        (R := k) (X := X) p.1).coeff.support},
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid
        (R := k) (X := X) p.1).coeff w.1 • wordMonomial X k w.1 by
    rw [Submodule.coe_sum]
    exact Finset.sum_congr rfl fun w _ ↦ rfl]
  calc
    p.1 = ∑ w ∈ (FreeAlgebra.equivMonoidAlgebraFreeMonoid
          (R := k) (X := X) p.1).coeff.support,
        ((FreeAlgebra.equivMonoidAlgebraFreeMonoid
          (R := k) (X := X) p.1).coeff w) • wordMonomial X k w :=
      eq_sum_support_smul_wordMonomial X k p.1
    _ = ∑ w : {w // w ∈ (FreeAlgebra.equivMonoidAlgebraFreeMonoid
        (R := k) (X := X) p.1).coeff.support},
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid
        (R := k) (X := X) p.1).coeff w.1 • wordMonomial X k w.1 :=
      (Finset.sum_attach _ _).symm

/-- Every free polynomial lies in some finite degree stage. -/
theorem exists_mem_degreeLE (p : FreeAlgebra k X) :
    ∃ n, p ∈ degreeLE X k n := by
  let q := FreeAlgebra.equivMonoidAlgebraFreeMonoid
    (R := k) (X := X) p
  let n := ∑ w ∈ q.coeff.support, freeWordLength X w
  refine ⟨n, (mem_degreeLE_iff X k p n).2 ?_⟩
  intro w hw
  dsimp [n]
  exact Finset.single_le_sum
    (fun z hz ↦ Nat.zero_le (freeWordLength X z)) hw

/-- The finite degree stages exhaust the free algebra. -/
theorem iSup_degreeLE : ⨆ n, degreeLE X k n = ⊤ := by
  apply top_unique
  intro p hp
  obtain ⟨n, hn⟩ := exists_mem_degreeLE X k p
  exact Submodule.mem_iSup_of_mem n hn

end FreeAlgebraDegree

end NonsoficGroupsExist
