import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Finsupp.Supported

/-!
# Finite degree stages of a free characteristic-two algebra

Kassabov's relative-property-`(T)` argument filters a free associative
algebra by word degree.  This file constructs that filtration without any
choice of a polynomial normal form: it uses the canonical equivalence with
the monoid algebra of the free monoid.  For a finite alphabet, every stage is
finite over `ZMod 2`, and the stages exhaust the whole free algebra.
-/

namespace NonsoficGroupsExist

namespace FreeAlgebraDegree

variable (X : Type*) [Fintype X]

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

/-- Polynomials supported on words of degree at most `n`. -/
noncomputable def degreeLE (n : ℕ) :
    Submodule (ZMod 2) (FreeAlgebra (ZMod 2) X) :=
  (MonoidAlgebra.supported (ZMod 2) (ZMod 2)
      (freeWordsLE X n : Set (FreeMonoid X))).comap
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid
      (R := ZMod 2) (X := X)).toLinearMap

theorem mem_degreeLE_iff (p : FreeAlgebra (ZMod 2) X) (n : ℕ) :
    p ∈ degreeLE X n ↔
      ∀ w ∈ (FreeAlgebra.equivMonoidAlgebraFreeMonoid
        (R := ZMod 2) (X := X) p).coeff.support,
        freeWordLength X w ≤ n := by
  rw [degreeLE, Submodule.mem_comap, MonoidAlgebra.mem_supported]
  change
    (∀ w ∈ (FreeAlgebra.equivMonoidAlgebraFreeMonoid
      (R := ZMod 2) (X := X) p).coeff.support,
      w ∈ freeWordsLE X n) ↔ _
  simp only [mem_freeWordsLE]

/-- Every degree stage is a finite additive group. -/
noncomputable instance finite_degreeLE (n : ℕ) : Finite (degreeLE X n) := by
  let S : Set (FreeMonoid X) := freeWordsLE X n
  let V := MonoidAlgebra.supported (ZMod 2) (ZMod 2) S
  let toV : degreeLE X n → V := fun p ↦
    ⟨FreeAlgebra.equivMonoidAlgebraFreeMonoid
      (R := ZMod 2) (X := X) p.1, p.2⟩
  letI : Fintype S := Fintype.ofFinset (freeWordsLE X n) (by
    intro w
    rfl)
  let e := MonoidAlgebra.supportedEquivFinsupp
    (R := ZMod 2) (S := ZMod 2) S
  let coeffs : V → S → ZMod 2 := fun p w ↦ e p w
  letI : Finite V := Finite.of_injective coeffs fun p q h ↦ by
    apply e.injective
    ext w
    exact congrFun h w
  exact Finite.of_injective toV fun a b h ↦ by
    apply Subtype.ext
    apply (FreeAlgebra.equivMonoidAlgebraFreeMonoid
      (R := ZMod 2) (X := X)).injective
    exact congrArg Subtype.val h

/-- The degree stages are monotone. -/
theorem degreeLE_mono : Monotone (degreeLE X) := by
  intro m n hmn p hp
  rw [mem_degreeLE_iff] at hp ⊢
  intro w hw
  exact (hp w hw).trans hmn

/-- Multiplication adds degree bounds. -/
theorem mul_mem_degreeLE {p q : FreeAlgebra (ZMod 2) X} {m n : ℕ}
    (hp : p ∈ degreeLE X m) (hq : q ∈ degreeLE X n) :
    p * q ∈ degreeLE X (m + n) := by
  classical
  rw [mem_degreeLE_iff] at hp hq ⊢
  intro w hw
  rw [map_mul] at hw
  have hmul := MonoidAlgebra.support_coeff_mul_subset
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid
      (R := ZMod 2) (X := X) p)
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid
      (R := ZMod 2) (X := X) q) hw
  rw [Finset.mem_mul] at hmul
  obtain ⟨u, hu, v, hv, huv⟩ := hmul
  rw [← huv, freeWordLength_mul]
  exact Nat.add_le_add (hp u hu) (hq v hv)

/-- A canonical free generator has degree one. -/
theorem generator_mem_degreeLE_one (x : X) :
    FreeAlgebra.ι (ZMod 2) x ∈ degreeLE X 1 := by
  rw [mem_degreeLE_iff]
  intro w hw
  simp [FreeAlgebra.equivMonoidAlgebraFreeMonoid] at hw
  subst w
  simp [freeWordLength]

/-- Left multiplication by a free generator advances the filtration by one
stage. -/
theorem generator_mul_mem_degreeLE_succ (x : X)
    {p : FreeAlgebra (ZMod 2) X} {n : ℕ} (hp : p ∈ degreeLE X n) :
    FreeAlgebra.ι (ZMod 2) x * p ∈ degreeLE X (n + 1) := by
  simpa [Nat.add_comm] using
    mul_mem_degreeLE X (generator_mem_degreeLE_one X x) hp

/-- Right multiplication by a free generator advances the filtration by one
stage. -/
theorem mul_generator_mem_degreeLE_succ (x : X)
    {p : FreeAlgebra (ZMod 2) X} {n : ℕ} (hp : p ∈ degreeLE X n) :
    p * FreeAlgebra.ι (ZMod 2) x ∈ degreeLE X (n + 1) := by
  exact mul_mem_degreeLE X hp (generator_mem_degreeLE_one X x)

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
    FreeAlgebra (ZMod 2) X :=
  (FreeAlgebra.equivMonoidAlgebraFreeMonoid
    (R := ZMod 2) (X := X)).symm (MonoidAlgebra.single w 1)

theorem wordMonomial_mem_degreeLE {w : FreeMonoid X} {n : ℕ}
    (hw : freeWordLength X w ≤ n) : wordMonomial X w ∈ degreeLE X n := by
  rw [mem_degreeLE_iff]
  intro v hv
  simp [wordMonomial] at hv
  subst v
  exact hw

/-- A total degree-stage version of a word monomial. Words outside the stage
are sent to zero; on words of length at most `n` this is the genuine basis
monomial. -/
noncomputable def wordMonomialInDegree (n : ℕ) (w : FreeMonoid X) :
    degreeLE X n :=
  if hw : freeWordLength X w ≤ n then
    ⟨wordMonomial X w, wordMonomial_mem_degreeLE X hw⟩
  else 0

@[simp] theorem wordMonomialInDegree_of_le {n : ℕ} (w : FreeMonoid X)
    (hw : freeWordLength X w ≤ n) :
    wordMonomialInDegree X n w =
      ⟨wordMonomial X w, wordMonomial_mem_degreeLE X hw⟩ := by
  simp [wordMonomialInDegree, hw]

@[simp] theorem wordMonomialInDegree_of_not_le {n : ℕ} (w : FreeMonoid X)
    (hw : ¬ freeWordLength X w ≤ n) :
    wordMonomialInDegree X n w = 0 := by
  simp [wordMonomialInDegree, hw]

omit [Fintype X] in
/-- Multiplication of basis monomials is free-word concatenation. -/
theorem wordMonomial_mul (u v : FreeMonoid X) :
    wordMonomial X u * wordMonomial X v = wordMonomial X (u * v) := by
  apply (FreeAlgebra.equivMonoidAlgebraFreeMonoid
    (R := ZMod 2) (X := X)).injective
  simp [wordMonomial]

omit [Fintype X] in
@[simp] theorem wordMonomial_one : wordMonomial X 1 = 1 := by
  unfold wordMonomial
  rw [← MonoidAlgebra.one_def]
  exact (FreeAlgebra.equivMonoidAlgebraFreeMonoid
    (R := ZMod 2) (X := X)).symm.map_one

omit [Fintype X] in
/-- A length-zero basis monomial is the unit coefficient. -/
theorem wordMonomial_eq_one_of_freeWordLength_eq_zero
    (w : FreeMonoid X) (hw : freeWordLength X w = 0) :
    wordMonomial X w = 1 := by
  rw [(freeWordLength_eq_zero_iff X w).1 hw, wordMonomial_one]

omit [Fintype X] in
/-- A one-letter basis monomial is the corresponding canonical free-algebra
generator. -/
theorem wordMonomial_of (x : X) :
    wordMonomial X (FreeMonoid.of x) = FreeAlgebra.ι (ZMod 2) x := by
  apply (FreeAlgebra.equivMonoidAlgebraFreeMonoid
    (R := ZMod 2) (X := X)).injective
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
      wordMonomial X w = FreeAlgebra.ι (ZMod 2) x * wordMonomial X v := by
  obtain ⟨x, v, hword, _⟩ := exists_of_mul_of_freeWordLength_pos X w hw
  refine ⟨x, v, hword, ?_⟩
  rw [hword, ← wordMonomial_mul X (FreeMonoid.of x) v, wordMonomial_of]

omit [Fintype X] in
/-- Every free polynomial is the finite sum of its supported word terms. -/
theorem eq_sum_support_smul_wordMonomial (p : FreeAlgebra (ZMod 2) X) :
    p = ∑ w ∈ (FreeAlgebra.equivMonoidAlgebraFreeMonoid
        (R := ZMod 2) (X := X) p).coeff.support,
      ((FreeAlgebra.equivMonoidAlgebraFreeMonoid
        (R := ZMod 2) (X := X) p).coeff w) • wordMonomial X w := by
  apply (FreeAlgebra.equivMonoidAlgebraFreeMonoid
    (R := ZMod 2) (X := X)).injective
  ext v
  simp [wordMonomial]
  have h := congrArg (fun f : FreeMonoid X →₀ ZMod 2 ↦ f v)
    (Finsupp.sum_single
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid
        (R := ZMod 2) (X := X) p).coeff)
  simpa [Finsupp.sum] using h.symm

omit [Fintype X] in
/-- Over `ZMod 2`, every nonzero coefficient is one, so a free polynomial is
the sum of exactly the basis words in its support. -/
theorem eq_sum_support_wordMonomial (p : FreeAlgebra (ZMod 2) X) :
    p = ∑ w ∈ (FreeAlgebra.equivMonoidAlgebraFreeMonoid
        (R := ZMod 2) (X := X) p).coeff.support,
      wordMonomial X w := by
  calc
    p = ∑ w ∈ (FreeAlgebra.equivMonoidAlgebraFreeMonoid
          (R := ZMod 2) (X := X) p).coeff.support,
        ((FreeAlgebra.equivMonoidAlgebraFreeMonoid
          (R := ZMod 2) (X := X) p).coeff w) • wordMonomial X w :=
      eq_sum_support_smul_wordMonomial X p
    _ = ∑ w ∈ (FreeAlgebra.equivMonoidAlgebraFreeMonoid
          (R := ZMod 2) (X := X) p).coeff.support,
        wordMonomial X w := by
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

/-- A degree-bounded free polynomial is the sum, inside its degree submodule,
of the basis words in its support. -/
theorem eq_sum_support_degreeWordMonomial {n : ℕ} (p : degreeLE X n) :
    let q := (FreeAlgebra.equivMonoidAlgebraFreeMonoid
      (R := ZMod 2) (X := X) p.1).coeff
    let term : {w // w ∈ q.support} → degreeLE X n := fun w ↦
      ⟨wordMonomial X w.1, wordMonomial_mem_degreeLE X
        (((mem_degreeLE_iff X p.1 n).1 p.2) w.1 w.2)⟩
    p = ∑ w, term w := by
  dsimp only
  apply Subtype.ext
  simp only [Submodule.coe_sum]
  change p.1 = ∑ w : {w // w ∈
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid
        (R := ZMod 2) (X := X) p.1).coeff.support},
    wordMonomial X w.1
  calc
    p.1 = ∑ w ∈ (FreeAlgebra.equivMonoidAlgebraFreeMonoid
          (R := ZMod 2) (X := X) p.1).coeff.support,
        wordMonomial X w := eq_sum_support_wordMonomial X p.1
    _ = ∑ w : {w // w ∈
        (FreeAlgebra.equivMonoidAlgebraFreeMonoid
          (R := ZMod 2) (X := X) p.1).coeff.support},
      wordMonomial X w.1 := (Finset.sum_attach _ _).symm

/-- Every free polynomial lies in some finite degree stage. -/
theorem exists_mem_degreeLE (p : FreeAlgebra (ZMod 2) X) :
    ∃ n, p ∈ degreeLE X n := by
  let q := FreeAlgebra.equivMonoidAlgebraFreeMonoid
    (R := ZMod 2) (X := X) p
  let n := ∑ w ∈ q.coeff.support, freeWordLength X w
  refine ⟨n, (mem_degreeLE_iff X p n).2 ?_⟩
  intro w hw
  dsimp [n]
  exact Finset.single_le_sum
    (fun z hz ↦ Nat.zero_le (freeWordLength X z)) hw

/-- The finite degree stages exhaust the free algebra. -/
theorem iSup_degreeLE : ⨆ n, degreeLE X n = ⊤ := by
  apply top_unique
  intro p hp
  obtain ⟨n, hn⟩ := exists_mem_degreeLE X p
  exact Submodule.mem_iSup_of_mem n hn

end FreeAlgebraDegree

end NonsoficGroupsExist
