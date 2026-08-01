import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Finset.Basic

/-!
# Local embeddability into finite groups

This file fixes the LEF vocabulary of Section `subsec:lef` and proves the one
technical fact needed to use it: a local embedding, being multiplicative on a
large enough finite set, evaluates fixed words correctly.  This is the
mechanism by which a relator of a finitely presented group is transported into
a finite group.
-/

namespace NonsoficGroupsExist

/-- A map that is multiplicative on a finite set and normalized at `1`. -/
structure LocalMultiplicativeOn {G H : Type*} [Group G] [Group H]
    (s : Finset G) (f : G → H) : Prop where
  map_one : f 1 = 1
  map_mul : ∀ x ∈ s, ∀ y ∈ s, f (x * y) = f x * f y

namespace LocalMultiplicativeOn

variable {G H : Type*} [Group G] [Group H]

theorem mono {s t : Finset G} {f : G → H} (h : LocalMultiplicativeOn t f)
    (hst : s ⊆ t) : LocalMultiplicativeOn s f where
  map_one := h.map_one
  map_mul x hx y hy := h.map_mul x (hst hx) y (hst hy)

theorem map_inv_of_mem {s : Finset G} {f : G → H} (h : LocalMultiplicativeOn s f)
    {x : G} (hx : x ∈ s) (hi : x⁻¹ ∈ s) : f x⁻¹ = (f x)⁻¹ := by
  have hm := h.map_mul x hx x⁻¹ hi
  rw [mul_inv_cancel, h.map_one] at hm
  exact eq_inv_of_mul_eq_one_right hm.symm

end LocalMultiplicativeOn

/-- Section `subsec:lef`: `J` is locally embeddable into finite groups. -/
def IsLEF (J : Type*) [Group J] : Prop :=
  ∀ s : Finset J, ∃ (n : ℕ) (f : J → Equiv.Perm (Fin n)),
    Set.InjOn f (s : Set J) ∧ LocalMultiplicativeOn s f

/-- Every fixed element of a free group has a finite control set outside of
which local multiplicativity already forces the value of the corresponding
word.  This is the free-group form of Lemma `lem:word`, used to transport
relators into local embeddings. -/
theorem exists_local_word_control {α : Type*} {G : Type*} [Group G]
    (φ : FreeGroup α →* G) (z : FreeGroup α) :
    ∃ s : Finset G, ∀ (H : Type) [Group H] (f : G → H),
      LocalMultiplicativeOn s f →
        FreeGroup.lift (fun a ↦ f (φ (FreeGroup.of a))) z = f (φ z) := by
  classical
  refine FreeGroup.induction_on z ?_ ?_ ?_ ?_
  · refine ⟨∅, ?_⟩
    intro H _ f hf
    simp [hf.map_one]
  · intro a
    refine ⟨∅, ?_⟩
    intro H _ f _
    simp
  · intro a _
    refine ⟨{φ (FreeGroup.of a), (φ (FreeGroup.of a))⁻¹}, ?_⟩
    intro H _ f hf
    simp only [map_inv, FreeGroup.lift_apply_of]
    exact (hf.map_inv_of_mem (by simp) (by simp)).symm
  · intro x y hx hy
    obtain ⟨sx, hx⟩ := hx
    obtain ⟨sy, hy⟩ := hy
    refine ⟨insert (φ x) (insert (φ y) (sx ∪ sy)), ?_⟩
    intro H _ f hf
    have hsx : sx ⊆ insert (φ x) (insert (φ y) (sx ∪ sy)) := by
      intro a ha
      simp [ha]
    have hsy : sy ⊆ insert (φ x) (insert (φ y) (sx ∪ sy)) := by
      intro a ha
      simp [ha]
    calc
      FreeGroup.lift (fun a ↦ f (φ (FreeGroup.of a))) (x * y) =
          FreeGroup.lift (fun a ↦ f (φ (FreeGroup.of a))) x *
            FreeGroup.lift (fun a ↦ f (φ (FreeGroup.of a))) y := map_mul _ _ _
      _ = f (φ x) * f (φ y) :=
        congrArg₂ (· * ·) (hx H f (hf.mono hsx)) (hy H f (hf.mono hsy))
      _ = f (φ x * φ y) := (hf.map_mul (φ x) (by simp) (φ y) (by simp)).symm
      _ = f (φ (x * y)) := by rw [map_mul]

end NonsoficGroupsExist
