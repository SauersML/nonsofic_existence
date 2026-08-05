import NonsoficGroupsExist.FreeElementaryPropertyT
import NonsoficGroupsExist.ElementaryGroup
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.RingTheory.FiniteType

/-!
# Property `(T)` for rank three over finite-type characteristic-two algebras

Every finite-type `ZMod 2`-algebra is a quotient of a free algebra on a finite
type. The kernel-checked free-algebra theorem therefore descends to its
elementary rank-three group.
-/

namespace NonsoficGroupsExist

open FreeRootFiltration

noncomputable section

variable {R : Type} [Ring R] [Algebra (ZMod 2) R]
  [Algebra.FiniteType (ZMod 2) R]

/-- The characteristic-two, rank-three case of the
Ershov--Jaikin-Zapirain theorem needed throughout this development. -/
theorem finiteTypeElementaryThree_hasKazhdanPropertyT :
    HasKazhdanPropertyT.{0, 0} (elementaryGroup (Fin 3) R) := by
  obtain ⟨X, hX, f, hf⟩ :=
    (Algebra.FiniteType.iff_quotient_freeAlgebra'
      (R := ZMod 2) (A := R)).mp inferInstance
  letI : Fintype X := hX
  exact HasKazhdanPropertyT.of_surjective
    (elementaryGroupMap (ι := Fin 3) f.toRingHom)
    (elementaryGroupMap_surjective_of_surjective f.toRingHom hf)
    (FreeElementaryPropertyT.freeElementary_hasKazhdanPropertyT X)

/-- Over a finite field of characteristic two, every finite-type algebra has
Kazhdan elementary group in rank three.  This is the finite-field form needed
for the manuscript's characteristic-two panorama. -/
theorem finiteCharacteristicTwoElementaryThree_hasKazhdanPropertyT
    {k A : Type} [Field k] [Finite k] [CharP k 2]
    [Ring A] [Algebra k A] [Nontrivial A] [Algebra.FiniteType k A] :
    HasKazhdanPropertyT.{0, 0} (elementaryGroup (Fin 3) A) := by
  letI : Fintype k := Fintype.ofFinite k
  letI : Algebra (ZMod 2) k := ZMod.algebra k 2
  letI : CharP A 2 :=
    charP_of_injective_algebraMap (R := k)
      (RingHom.injective (algebraMap k A)) 2
  letI : Algebra (ZMod 2) A := ZMod.algebra A 2
  letI : IsScalarTower (ZMod 2) k A :=
    ZMod.instIsScalarTower 2 k A
  letI : Algebra.FiniteType (ZMod 2) k := by
    refine ⟨Finset.univ, ?_⟩
    simp
  have ht : IsScalarTower (ZMod 2) k A := inferInstance
  letI : Algebra.FiniteType (ZMod 2) A :=
    @Algebra.FiniteType.trans (ZMod 2) k A
      inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance ht inferInstance inferInstance
  exact finiteTypeElementaryThree_hasKazhdanPropertyT

/-- Elementary groups of rank at least three over finite-type algebras over a
finite characteristic-two field are finitely generated. -/
theorem finiteCharacteristicTwoElementary_finitelyGenerated
    {k A : Type} [Field k] [Finite k] [CharP k 2]
    [Ring A] [Algebra k A] [Nontrivial A] [Algebra.FiniteType k A]
    (n : ℕ) (hn : 2 < n) : Group.FG (elementaryGroup (Fin n) A) := by
  letI : Fintype k := Fintype.ofFinite k
  letI : Algebra (ZMod 2) k := ZMod.algebra k 2
  letI : CharP A 2 :=
    charP_of_injective_algebraMap (R := k)
      (RingHom.injective (algebraMap k A)) 2
  letI : Algebra (ZMod 2) A := ZMod.algebra A 2
  letI : IsScalarTower (ZMod 2) k A :=
    ZMod.instIsScalarTower 2 k A
  letI : Algebra.FiniteType (ZMod 2) k := by
    refine ⟨Finset.univ, ?_⟩
    simp
  have ht : IsScalarTower (ZMod 2) k A := inferInstance
  letI : Algebra.FiniteType (ZMod 2) A :=
    @Algebra.FiniteType.trans (ZMod 2) k A
      inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance ht inferInstance inferInstance
  exact elementaryGroup_finitelyGenerated n hn

end
end NonsoficGroupsExist
