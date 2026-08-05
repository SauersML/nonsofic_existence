import NonsoficGroupsExist.ElementaryRoots
import NonsoficGroupsExist.FreeAlgebraDegree

/-!
# Finite degree stages of elementary root subgroups

For the free characteristic-two algebra on a finite alphabet, this file sends
the finite additive degree filtration into each elementary root subgroup.  The
resulting root stages are genuine finite subgroups, are monotone, and exhaust
the entire root subgroup.  These are the finite groups used in the
finite-stage relative-property-`(T)` argument.
-/

namespace NonsoficGroupsExist

namespace FreeRootFiltration

open FreeAlgebraDegree

variable (X : Type*) [Fintype X]

abbrev FreeRing := FreeAlgebra (ZMod 2) X

/-- The root elements whose coefficients have word degree at most `n`. -/
noncomputable def rootDegreeSubgroup (i j : Fin 3) (hij : i ≠ j) (n : ℕ) :
    Subgroup (elementaryGroup (Fin 3) (FreeRing X)) where
  carrier := {g | ∃ a : FreeRing X,
    a ∈ degreeLE X (ZMod 2) n ∧ elementaryRoot i j hij a = g}
  one_mem' := ⟨0, (degreeLE X (ZMod 2) n).zero_mem, elementaryRoot_zero i j hij⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, (degreeLE X (ZMod 2) n).add_mem ha hb,
      (elementaryRoot_mul i j hij a b).symm⟩
  inv_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨-a, (degreeLE X (ZMod 2) n).neg_mem ha, elementaryRoot_neg i j hij a⟩

theorem mem_rootDegreeSubgroup_iff (i j : Fin 3) (hij : i ≠ j) (n : ℕ)
    (g : elementaryGroup (Fin 3) (FreeRing X)) :
    g ∈ rootDegreeSubgroup X i j hij n ↔
      ∃ a : FreeRing X,
        a ∈ degreeLE X (ZMod 2) n ∧ elementaryRoot i j hij a = g :=
  Iff.rfl

/-- Every degree-bounded root subgroup is finite. -/
noncomputable instance finite_rootDegreeSubgroup
    (i j : Fin 3) (hij : i ≠ j) (n : ℕ) :
    Finite (rootDegreeSubgroup X i j hij n) := by
  let f : degreeLE X (ZMod 2) n → rootDegreeSubgroup X i j hij n := fun a ↦
    ⟨elementaryRoot i j hij a.1, ⟨a.1, a.2, rfl⟩⟩
  exact Finite.of_surjective f (by
    rintro ⟨g, a, ha, hag⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    apply Subtype.ext
    exact hag)

/-- Root degree stages form an increasing sequence of subgroups. -/
theorem rootDegreeSubgroup_mono (i j : Fin 3) (hij : i ≠ j) :
    Monotone (rootDegreeSubgroup X i j hij) := by
  intro m n hmn g
  rintro ⟨a, ha, hag⟩
  exact ⟨a, degreeLE_mono X (ZMod 2) hmn ha, hag⟩

theorem rootDegreeSubgroup_le (i j : Fin 3) (hij : i ≠ j) (n : ℕ) :
    rootDegreeSubgroup X i j hij n ≤ elementaryRootSubgroup i j hij := by
  rintro g ⟨a, _, rfl⟩
  exact ⟨a, rfl⟩

/-- The finite degree stages exhaust the full elementary root subgroup. -/
theorem iSup_rootDegreeSubgroup (i j : Fin 3) (hij : i ≠ j) :
    ⨆ n, rootDegreeSubgroup X i j hij n = elementaryRootSubgroup i j hij := by
  apply le_antisymm
  · exact iSup_le (rootDegreeSubgroup_le X i j hij)
  · intro g hg
    obtain ⟨a, rfl⟩ := hg
    obtain ⟨n, hn⟩ := exists_mem_degreeLE X (ZMod 2) a
    exact (le_iSup (rootDegreeSubgroup X i j hij) n) ⟨a, hn, rfl⟩

end FreeRootFiltration

end NonsoficGroupsExist
