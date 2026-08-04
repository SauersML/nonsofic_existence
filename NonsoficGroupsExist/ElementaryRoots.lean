import NonsoficGroupsExist.ElementaryGroup

/-!
# Elementary root subgroups

This file packages the six additive root subgroups used in the
Ershov--Jaikin-Zapirain `A₂` argument.  The package contains no analytic
assumption: generation and all commutator relations are proved directly from
matrix multiplication.
-/

namespace NonsoficGroupsExist

open scoped commutatorElement

variable {I R : Type*} [Fintype I] [DecidableEq I] [Ring R]

/-- An elementary matrix bundled as an element of the elementary group. -/
def elementaryRoot (i j : I) (hij : i ≠ j) (a : R) : elementaryGroup I R :=
  ⟨elementaryUnit i j hij a, elementaryUnit_mem i j hij a⟩

@[simp] theorem elementaryRoot_val (i j : I) (hij : i ≠ j) (a : R) :
    (elementaryRoot i j hij a : (Matrix I I R)ˣ) = elementaryUnit i j hij a := rfl

@[simp] theorem elementaryRoot_zero (i j : I) (hij : i ≠ j) :
    elementaryRoot (R := R) i j hij 0 = 1 := by
  apply Subtype.ext
  exact elementaryUnit_zero i j hij

theorem elementaryRoot_mul (i j : I) (hij : i ≠ j) (a b : R) :
    elementaryRoot i j hij a * elementaryRoot i j hij b =
      elementaryRoot i j hij (a + b) := by
  apply Subtype.ext
  exact elementaryUnit_mul i j hij a b

/-- The additive elementary root subgroup `Xᵢⱼ`. -/
def elementaryRootSubgroup (i j : I) (hij : i ≠ j) :
    Subgroup (elementaryGroup I R) where
  carrier := Set.range (elementaryRoot i j hij)
  one_mem' := ⟨0, elementaryRoot_zero i j hij⟩
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, (elementaryRoot_mul i j hij a b).symm⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    refine ⟨-a, ?_⟩
    have hmul : elementaryRoot i j hij a * elementaryRoot i j hij (-a) = 1 := by
      rw [elementaryRoot_mul]
      simp
    have h := congrArg (fun z ↦ (elementaryRoot i j hij a)⁻¹ * z) hmul
    simpa using h

theorem mem_elementaryRootSubgroup_iff (i j : I) (hij : i ≠ j)
    (g : elementaryGroup I R) :
    g ∈ elementaryRootSubgroup i j hij ↔
      ∃ a : R, elementaryRoot i j hij a = g := Iff.rfl

/-- The union of all elementary root subgroups. -/
def elementaryRootSet (I R : Type*) [Fintype I] [DecidableEq I] [Ring R] :
    Set (elementaryGroup I R) :=
  {g | ∃ (i j : I) (hij : i ≠ j), g ∈ elementaryRootSubgroup i j hij}

theorem elementaryRoot_mem_set (i j : I) (hij : i ≠ j) (a : R) :
    elementaryRoot i j hij a ∈ elementaryRootSet I R :=
  ⟨i, j, hij, a, rfl⟩

/-- The root subgroups generate the elementary group. -/
theorem elementaryRootSet_generate :
    Subgroup.closure (elementaryRootSet I R) = ⊤ := by
  apply top_unique
  intro g _
  let H : Subgroup (elementaryGroup I R) :=
    Subgroup.closure (elementaryRootSet I R)
  have hle : elementaryGroup I R ≤ H.map (elementaryGroup I R).subtype := by
    change Subgroup.closure
      {z : (Matrix I I R)ˣ |
        ∃ (i j : I) (h : i ≠ j) (a : R), elementaryUnit i j h a = z} ≤ _
    rw [Subgroup.closure_le]
    rintro _ ⟨i, j, hij, a, rfl⟩
    exact ⟨elementaryRoot i j hij a,
      Subgroup.subset_closure (elementaryRoot_mem_set i j hij a), rfl⟩
  obtain ⟨x, hx, hxg⟩ := hle g.property
  have : x = g := Subtype.ext hxg
  simpa [H, this] using hx

/-- Root groups in non-addable positions commute. -/
theorem elementaryUnit_commute_of_ne
    (i j k l : I) (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hli : l ≠ i) (a b : R) :
    Commute (elementaryUnit i j hij a) (elementaryUnit k l hkl b) := by
  apply Units.ext
  change (1 + Matrix.single i j a) * (1 + Matrix.single k l b) =
    (1 + Matrix.single k l b) * (1 + Matrix.single i j a)
  have hxy : Matrix.single i j a * Matrix.single k l b = 0 :=
    Matrix.single_mul_single_of_ne (c := a) i j k hjk b
  have hyx : Matrix.single k l b * Matrix.single i j a = 0 :=
    Matrix.single_mul_single_of_ne (c := b) k l i hli a
  noncomm_ring [hxy, hyx]

theorem elementaryRoot_commute_of_ne
    (i j k l : I) (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hli : l ≠ i) (a b : R) :
    Commute (elementaryRoot i j hij a) (elementaryRoot k l hkl b) := by
  apply Subtype.ext
  exact (elementaryUnit_commute_of_ne i j k l hij hkl hjk hli a b).eq

/-- The Steinberg commutator relation, bundled inside the elementary group. -/
theorem elementaryRoot_commutator (i j k : I)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
    ⁅elementaryRoot i j hij a, elementaryRoot j k hjk b⁆ =
      elementaryRoot i k hik (a * b) := by
  apply Subtype.ext
  exact elementaryUnit_commutator i j k hij hjk hik a b

end NonsoficGroupsExist
