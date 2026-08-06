import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.PUnit

/-!
# Verbal completeness and what it forces

Constructions of omnimonsters make verbal completeness generic and then read
off its consequences.  Only the second half is elementary, and it is the half
formalized here.

A group is verbally complete when every equation `v(x₁, …, x_m) = g` with `v` a
nontrivial element of a free group is solvable.  Three consequences follow by
choosing `v`:

* every nontrivial word map is surjective, which is the definition restated;
* the group is divisible -- take `v = X ^ n`;
* every element is a single commutator, i.e. the commutator width is one --
  take `v = ⁅X₁, X₂⁆`.

Combined with torsion-freeness and two conjugacy classes, the last of these is
what makes stable commutator length vanish: `cl (gⁿ) ≤ 1` for every `n`, so the
limit defining `scl` is zero.  Stable commutator length itself is not defined
in this library, so that statement appears here only in the form
`exists_commutatorElement_eq_pow`, which is the input any definition of it
would consume.

The two word choices need their words to be nontrivial in the free group, and
that is the only real work below: `X ^ n` is detected by the abelianization
`FreeGroup (Fin 1) → Multiplicative ℤ`, and `⁅X₁, X₂⁆` by evaluating in
`Equiv.Perm (Fin 3)`, where the commutator of two transpositions is a
three-cycle.
-/

namespace NonsoficGroupsExist.Monsters

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- A group is verbally complete when every equation given by a nontrivial
word has a solution. -/
def IsVerballyComplete (G : Type*) [Group G] : Prop :=
  ∀ (m : ℕ) (v : FreeGroup (Fin m)), v ≠ 1 → ∀ g : G,
    ∃ f : Fin m → G, FreeGroup.lift f v = g

/-- The definition is satisfiable: the trivial group is verbally complete.
This is a control on the definition, not an interesting example -- nontrivial
verbally complete groups are what a Baire-category argument over a
small-cancellation space produces, and that argument is not formalized
here. -/
theorem isVerballyComplete_punit : IsVerballyComplete PUnit.{1} :=
  fun _ _ _ g ↦ ⟨fun _ ↦ g, Subsingleton.elim _ _⟩

/-! ### The two words -/

/-- A nonzero power of a free generator is nontrivial: its image under the
abelianization `FreeGroup (Fin 1) → Multiplicative ℤ` is `n`. -/
theorem of_pow_ne_one {n : ℕ} (hn : n ≠ 0) :
    (FreeGroup.of (0 : Fin 1)) ^ n ≠ 1 := by
  intro hcon
  set φ := FreeGroup.lift (fun _ : Fin 1 ↦ Multiplicative.ofAdd (1 : ℤ)) with hφ
  have himage : φ ((FreeGroup.of (0 : Fin 1)) ^ n) = φ 1 := by rw [hcon]
  rw [map_pow, map_one, hφ, FreeGroup.lift_apply_of, ← ofAdd_nsmul,
    ofAdd_eq_one] at himage
  simp only [nsmul_eq_mul, mul_one, Nat.cast_eq_zero] at himage
  exact hn himage

/-- The commutator of two free generators is nontrivial: it evaluates to a
nonidentity permutation of three points. -/
theorem commutatorElement_of_ne_one :
    ⁅FreeGroup.of (0 : Fin 2), FreeGroup.of (1 : Fin 2)⁆ ≠ 1 := by
  intro hcon
  set φ := FreeGroup.lift (fun i : Fin 2 ↦
    if i = 0 then Equiv.swap (0 : Fin 3) 1 else Equiv.swap (1 : Fin 3) 2) with hφ
  have himage : φ ⁅FreeGroup.of (0 : Fin 2), FreeGroup.of (1 : Fin 2)⁆ = φ 1 := by
    rw [hcon]
  rw [map_commutatorElement, map_one, hφ, FreeGroup.lift_apply_of,
    FreeGroup.lift_apply_of] at himage
  revert himage
  decide

/-! ### Consequences -/

namespace IsVerballyComplete

variable (h : IsVerballyComplete G)
include h

/-- Every nontrivial word map is surjective. -/
theorem wordMap_surjective {m : ℕ} {v : FreeGroup (Fin m)} (hv : v ≠ 1) :
    Function.Surjective (fun f : Fin m → G ↦ FreeGroup.lift f v) :=
  fun g ↦ h m v hv g

/-- **Divisibility.**  A verbally complete group is divisible: every
element is an `n`-th power for every `n ≥ 1`. -/
theorem exists_pow_eq {n : ℕ} (hn : n ≠ 0) (g : G) : ∃ x : G, x ^ n = g := by
  obtain ⟨f, hf⟩ := h 1 ((FreeGroup.of (0 : Fin 1)) ^ n) (of_pow_ne_one hn) g
  exact ⟨f 0, by rwa [map_pow, FreeGroup.lift_apply_of] at hf⟩

/-- **Commutator width one.**  Every element of a verbally complete group is a
single commutator, so the commutator width is one and the group is perfect. -/
theorem exists_commutatorElement_eq (g : G) : ∃ x y : G, ⁅x, y⁆ = g := by
  obtain ⟨f, hf⟩ := h 2 ⁅FreeGroup.of (0 : Fin 2), FreeGroup.of (1 : Fin 2)⁆
    commutatorElement_of_ne_one g
  refine ⟨f 0, f 1, ?_⟩
  rwa [map_commutatorElement, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of] at hf

/-- Commutator length one is inherited by every power, which is the estimate a
stable commutator length would be computed from: `cl (gⁿ) ≤ 1` for all `n`, so
`scl g = 0`. -/
theorem exists_commutatorElement_eq_pow (g : G) (n : ℕ) :
    ∃ x y : G, ⁅x, y⁆ = g ^ n := h.exists_commutatorElement_eq (g ^ n)

end IsVerballyComplete

end NonsoficGroupsExist.Monsters
