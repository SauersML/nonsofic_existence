import NonsoficGroupsExist.ElementaryRoots

/-!
# Root-subgroup systems of type A₂

The six ordered roots of `A₂` are indexed by distinct pairs in `Fin 3`.
This file records the algebraic hypotheses used by the EJZ magic-graph
argument and proves them for elementary groups over every associative ring.
-/

namespace NonsoficGroupsExist

open scoped commutatorElement

/-- The six ordered roots of type `A₂`. -/
abbrev A2Root := {p : Fin 3 × Fin 3 // p.1 ≠ p.2}

/-- A strongly graded `A₂` root-subgroup system: the six subgroups generate,
non-addable roots commute, commutators of consecutive roots land in their sum
root, and every element of a sum root is such a commutator.  The final field is
the strong-grading hypothesis required by the EJZ Kazhdan-subset argument. -/
structure A2System (G : Type*) [Group G] where
  root : ∀ (i j : Fin 3), i ≠ j → Subgroup G
  generate : Subgroup.closure
    {g | ∃ (i j : Fin 3) (hij : i ≠ j), g ∈ root i j hij} = ⊤
  commute : ∀ (i j k l : Fin 3)
    (hij : i ≠ j) (hkl : k ≠ l), j ≠ k → l ≠ i →
      ∀ x ∈ root i j hij, ∀ y ∈ root k l hkl, Commute x y
  commutator_mem : ∀ (i j k : Fin 3)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k),
      ∀ x ∈ root i j hij, ∀ y ∈ root j k hjk,
        ⁅x, y⁆ ∈ root i k hik
  commutator_surjective : ∀ (i j k : Fin 3)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k),
      ∀ z ∈ root i k hik,
        ∃ x ∈ root i j hij, ∃ y ∈ root j k hjk, ⁅x, y⁆ = z

namespace A2System

variable {G : Type*} [Group G]

/-- A root subgroup indexed by the finite type of six ordered roots. -/
def rootAt (A : A2System G) (a : A2Root) : Subgroup G :=
  A.root a.1.1 a.1.2 a.2

/-- The union of the six root subgroups. -/
def rootSet (A : A2System G) : Set G :=
  {g | ∃ (i j : Fin 3) (hij : i ≠ j), g ∈ A.root i j hij}

theorem mem_rootSet_iff (A : A2System G) (g : G) :
    g ∈ A.rootSet ↔ ∃ a : A2Root, g ∈ A.rootAt a := by
  constructor
  · rintro ⟨i, j, hij, hg⟩
    exact ⟨⟨(i, j), hij⟩, hg⟩
  · rintro ⟨⟨⟨i, j⟩, hij⟩, hg⟩
    exact ⟨i, j, hij, hg⟩

theorem rootSet_generate (A : A2System G) :
    Subgroup.closure A.rootSet = ⊤ := A.generate

/-- Each root subgroup in an `A₂` system is abelian.  This is a consequence
of the non-addable-root commutation axiom, not an additional assumption. -/
theorem root_commute (A : A2System G) (i j : Fin 3) (hij : i ≠ j) :
    ∀ x ∈ A.root i j hij, ∀ y ∈ A.root i j hij, Commute x y := by
  exact A.commute i j i j hij hij hij.symm hij.symm

end A2System

/-- Elementary matrices in rank three form an `A₂` system, with every
axiom discharged by explicit matrix identities. -/
def elementaryA2System (R : Type*) [Ring R] :
    A2System (elementaryGroup (Fin 3) R) where
  root := fun i j hij ↦ elementaryRootSubgroup i j hij
  generate := by
    exact elementaryRootSet_generate
  commute := by
    intro i j k l hij hkl hjk hli x hx y hy
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact elementaryRoot_commute_of_ne i j k l hij hkl hjk hli a b
  commutator_mem := by
    intro i j k hij hjk hik x hx y hy
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a * b, (elementaryRoot_commutator i j k hij hjk hik a b).symm⟩
  commutator_surjective := by
    intro i j k hij hjk hik z hz
    obtain ⟨a, rfl⟩ := hz
    refine ⟨elementaryRoot i j hij a, ⟨a, rfl⟩,
      elementaryRoot j k hjk 1, ⟨1, rfl⟩, ?_⟩
    simpa using elementaryRoot_commutator i j k hij hjk hik a 1

end NonsoficGroupsExist
