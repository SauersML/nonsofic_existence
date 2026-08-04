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
