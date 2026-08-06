import NonsoficGroupsExist.Leavitt.ElementaryGroup
import Mathlib.GroupTheory.Commutator.Basic

/-!
# Elementary groups of rank at least three are perfect

The single Steinberg identity

  `x_{ij}(a) = [x_{il}(a), x_{lj}(1)]`,   `l ∉ {i, j}`,

available as soon as a third coordinate exists, places every generating
transvection of `EL_n(R)` inside the commutator subgroup.  Hence
`EL_n(R)` is perfect for every ring `R` and every `n ≥ 3`.

Perfectness is what lets a copy of an elementary group be carried into
elementary groups of other ranks by Whitehead-style diagonal tricks, and it
is one of the clauses of the profile theorems: the nonsofic subgroups this
library constructs inside unit groups are images of `EL₄` of a subring, so
they are perfect as well — the image of a perfect group is perfect.
-/

namespace NonsoficGroupsExist

open scoped commutatorElement

variable {R : Type*} [Ring R]

/-- Each elementary transvection is a single commutator of transvections as
soon as a third coordinate exists. -/
theorem elementaryUnit_eq_commutator {n : ℕ} (hn : 2 < n)
    (i j : Fin n) (hij : i ≠ j) (a : R) :
    ∃ (l : Fin n) (hil : i ≠ l) (hlj : l ≠ j),
      elementaryUnit i j hij a =
        ⁅elementaryUnit i l hil a, elementaryUnit l j hlj 1⁆ := by
  obtain ⟨l, hli, hlj⟩ := Fin.exists_ne_and_ne_of_two_lt i j hn
  have hil : i ≠ l := hli.symm
  refine ⟨l, hil, hlj, ?_⟩
  rw [elementaryUnit_commutator i l j hil hlj hij a 1, mul_one]

/-- **Perfectness.**  `EL_n(R)` equals its own commutator subgroup for every
ring `R` and every `n ≥ 3`. -/
theorem elementaryGroup_commutator_eq_top (n : ℕ) (hn : 2 < n) :
    commutator (elementaryGroup (Fin n) R) = ⊤ := by
  apply top_unique
  rintro ⟨g, hg⟩ -
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, j, hij, a, rfl⟩ := hx
      obtain ⟨l, hil, hlj, hcomm⟩ :=
        elementaryUnit_eq_commutator hn i j hij a
      have hsub :
          (⟨elementaryUnit i j hij a, elementaryUnit_mem i j hij a⟩ :
              elementaryGroup (Fin n) R) =
            ⁅(⟨elementaryUnit i l hil a, elementaryUnit_mem i l hil a⟩ :
                elementaryGroup (Fin n) R),
              (⟨elementaryUnit l j hlj 1, elementaryUnit_mem l j hlj 1⟩ :
                elementaryGroup (Fin n) R)⁆ := by
        apply Subtype.ext
        exact hcomm
      rw [hsub]
      exact Subgroup.commutator_mem_commutator
        (Subgroup.mem_top _) (Subgroup.mem_top _)
  | one =>
      rw [show (⟨1, _⟩ : elementaryGroup (Fin n) R) = 1 from Subtype.ext rfl]
      exact (commutator (elementaryGroup (Fin n) R)).one_mem
  | mul x y hxmem hymem hx hy =>
      rw [show (⟨x * y, _⟩ : elementaryGroup (Fin n) R) =
          ⟨x, hxmem⟩ * ⟨y, hymem⟩ from Subtype.ext rfl]
      exact (commutator (elementaryGroup (Fin n) R)).mul_mem hx hy
  | inv x hxmem hx =>
      rw [show (⟨x⁻¹, _⟩ : elementaryGroup (Fin n) R) =
          (⟨x, hxmem⟩ : elementaryGroup (Fin n) R)⁻¹ from Subtype.ext rfl]
      exact (commutator (elementaryGroup (Fin n) R)).inv_mem hx

/-- The image of a perfect group is perfect: applied to a group with
`commutator = ⊤`, every homomorphic image again has `commutator = ⊤`.
Used to carry perfectness of `EL₄` of a subring onto the nonsofic
subgroups this library places inside unit groups. -/
theorem commutator_eq_top_of_surjective {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f)
    (hG : commutator G = ⊤) : commutator H = ⊤ := by
  have hmap : (commutator G).map f = commutator H := by
    rw [commutator, commutator, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective f hf]
  rw [← hmap, hG, Subgroup.map_top_of_surjective f hf]

end NonsoficGroupsExist
