import NonsoficGroupsExist.FreeRootActions

/-!
# Finite coefficient planes in the free elementary group

Two roots in a common column form the additive plane on which the adjacent
rank-two elementary group acts in Kassabov's relative-property-`(T)` proof.
Here the plane is built coefficient by coefficient.  Its finite degree stages
are finite subgroups, exhaust the join of the two full root subgroups, and are
carried one stage forward by each free-generator shear.
-/

namespace NonsoficGroupsExist

namespace FreeRootPlane

open FreeAlgebraDegree FreeRootFiltration

variable (X : Type*) [Fintype X]

/-- The finite coefficient plane in a common column, at degree `n`. -/
noncomputable def rootPlaneDegreeSubgroup
    (i j k : Fin 3) (_hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ) :
    Subgroup (elementaryGroup (Fin 3) (FreeRing X)) where
  carrier := {g | ∃ a : FreeRing X, a ∈ degreeLE X n ∧
    ∃ b : FreeRing X, b ∈ degreeLE X n ∧
      elementaryRoot i k hik a * elementaryRoot j k hjk b = g}
  one_mem' := ⟨0, (degreeLE X n).zero_mem, 0, (degreeLE X n).zero_mem, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
    refine ⟨a + c, (degreeLE X n).add_mem ha hc,
      b + d, (degreeLE X n).add_mem hb hd, ?_⟩
    rw [← elementaryRoot_mul i k hik a c,
      ← elementaryRoot_mul j k hjk b d]
    have hcomm := elementaryRoot_commute_of_ne i k j k hik hjk
      hjk.symm hik.symm c b
    calc
      (elementaryRoot i k hik a * elementaryRoot i k hik c) *
          (elementaryRoot j k hjk b * elementaryRoot j k hjk d) =
        elementaryRoot i k hik a *
          (elementaryRoot i k hik c * elementaryRoot j k hjk b) *
            elementaryRoot j k hjk d := by simp only [mul_assoc]
      _ = elementaryRoot i k hik a *
          (elementaryRoot j k hjk b * elementaryRoot i k hik c) *
            elementaryRoot j k hjk d := by rw [hcomm.eq]
      _ = (elementaryRoot i k hik a * elementaryRoot j k hjk b) *
          (elementaryRoot i k hik c * elementaryRoot j k hjk d) := by
        simp only [mul_assoc]
  inv_mem' := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    refine ⟨-a, (degreeLE X n).neg_mem ha,
      -b, (degreeLE X n).neg_mem hb, ?_⟩
    rw [elementaryRoot_neg, elementaryRoot_neg, mul_inv_rev]
    exact (elementaryRoot_commute_of_ne i k j k hik hjk
      hjk.symm hik.symm a b).inv_left.inv_right.eq

theorem mem_rootPlaneDegreeSubgroup_iff
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (g : elementaryGroup (Fin 3) (FreeRing X)) :
    g ∈ rootPlaneDegreeSubgroup X i j k hij hik hjk n ↔
      ∃ a : FreeRing X, a ∈ degreeLE X n ∧
      ∃ b : FreeRing X, b ∈ degreeLE X n ∧
        elementaryRoot i k hik a * elementaryRoot j k hjk b = g :=
  Iff.rfl

/-- Every coefficient-plane degree stage is finite. -/
noncomputable instance finite_rootPlaneDegreeSubgroup
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ) :
    Finite (rootPlaneDegreeSubgroup X i j k hij hik hjk n) := by
  let f : degreeLE X n × degreeLE X n →
      rootPlaneDegreeSubgroup X i j k hij hik hjk n := fun p ↦
    ⟨elementaryRoot i k hik p.1.1 * elementaryRoot j k hjk p.2.1,
      ⟨p.1.1, p.1.2, p.2.1, p.2.2, rfl⟩⟩
  exact Finite.of_surjective f (by
    rintro ⟨g, a, ha, b, hb, habg⟩
    refine ⟨(⟨a, ha⟩, ⟨b, hb⟩), ?_⟩
    apply Subtype.ext
    exact habg)

/-- Plane degree stages are monotone. -/
theorem rootPlaneDegreeSubgroup_mono
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Monotone (rootPlaneDegreeSubgroup X i j k hij hik hjk) := by
  intro m n hmn g
  rintro ⟨a, ha, b, hb, habg⟩
  exact ⟨a, degreeLE_mono X hmn ha, b, degreeLE_mono X hmn hb, habg⟩

/-- Every finite coefficient plane is abelian. -/
theorem rootPlaneDegreeSubgroup_commute
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ) :
    ∀ g ∈ rootPlaneDegreeSubgroup X i j k hij hik hjk n,
      ∀ h ∈ rootPlaneDegreeSubgroup X i j k hij hik hjk n,
        Commute g h := by
  rintro _ ⟨a, _, b, _, rfl⟩ _ ⟨c, _, d, _, rfl⟩
  have hAC := elementaryRoot_commute_of_ne i k i k hik hik
    hik.symm hik.symm a c
  have hAD := elementaryRoot_commute_of_ne i k j k hik hjk
    hjk.symm hik.symm a d
  have hBC := elementaryRoot_commute_of_ne j k i k hjk hik
    hik.symm hjk.symm b c
  have hBD := elementaryRoot_commute_of_ne j k j k hjk hjk
    hjk.symm hjk.symm b d
  exact (hAC.mul_right hAD).mul_left (hBC.mul_right hBD)

/-- Every element of a finite coefficient plane is an involution. -/
theorem rootPlaneDegreeSubgroup_sq
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ) :
    ∀ g ∈ rootPlaneDegreeSubgroup X i j k hij hik hjk n, g ^ 2 = 1 := by
  rintro _ ⟨a, _, b, _, rfl⟩
  have hcomm := elementaryRoot_commute_of_ne i k j k hik hjk
    hjk.symm hik.symm a b
  have hA : elementaryRoot i k hik a * elementaryRoot i k hik a = 1 := by
    rw [elementaryRoot_mul, add_self_eq_zero, elementaryRoot_zero]
  have hB : elementaryRoot j k hjk b * elementaryRoot j k hjk b = 1 := by
    rw [elementaryRoot_mul, add_self_eq_zero, elementaryRoot_zero]
  rw [pow_two]
  calc
    (elementaryRoot i k hik a * elementaryRoot j k hjk b) *
        (elementaryRoot i k hik a * elementaryRoot j k hjk b) =
      (elementaryRoot i k hik a * elementaryRoot i k hik a) *
        (elementaryRoot j k hjk b * elementaryRoot j k hjk b) := by
      rw [mul_assoc, ← mul_assoc (elementaryRoot j k hjk b), ← hcomm.eq]
      simp only [mul_assoc]
    _ = 1 := by rw [hA, hB]; simp

/-- The first coefficient coordinate inside a finite plane stage. -/
noncomputable def firstCoordinate
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (a : degreeLE X n) : rootPlaneDegreeSubgroup X i j k hij hik hjk n :=
  ⟨elementaryRoot i k hik a.1,
    ⟨a.1, a.2, 0, (degreeLE X n).zero_mem, by simp⟩⟩

/-- The second coefficient coordinate inside a finite plane stage. -/
noncomputable def secondCoordinate
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (b : degreeLE X n) : rootPlaneDegreeSubgroup X i j k hij hik hjk n :=
  ⟨elementaryRoot j k hjk b.1,
    ⟨0, (degreeLE X n).zero_mem, b.1, b.2, by simp⟩⟩

@[simp] theorem firstCoordinate_val
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (a : degreeLE X n) :
    (firstCoordinate X i j k hij hik hjk n a :
      elementaryGroup (Fin 3) (FreeRing X)) = elementaryRoot i k hik a.1 := rfl

@[simp] theorem secondCoordinate_val
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (b : degreeLE X n) :
    (secondCoordinate X i j k hij hik hjk n b :
      elementaryGroup (Fin 3) (FreeRing X)) = elementaryRoot j k hjk b.1 := rfl

theorem firstCoordinate_add
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (a b : degreeLE X n) :
    firstCoordinate X i j k hij hik hjk n (a + b) =
      firstCoordinate X i j k hij hik hjk n a *
        firstCoordinate X i j k hij hik hjk n b := by
  apply Subtype.ext
  exact (elementaryRoot_mul i k hik a.1 b.1).symm

theorem secondCoordinate_add
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (a b : degreeLE X n) :
    secondCoordinate X i j k hij hik hjk n (a + b) =
      secondCoordinate X i j k hij hik hjk n a *
        secondCoordinate X i j k hij hik hjk n b := by
  apply Subtype.ext
  exact (elementaryRoot_mul j k hjk a.1 b.1).symm

/-- Every plane element factors through its two coefficient coordinates. -/
theorem exists_coordinate_factorization
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (g : rootPlaneDegreeSubgroup X i j k hij hik hjk n) :
    ∃ a b : degreeLE X n,
      firstCoordinate X i j k hij hik hjk n a *
        secondCoordinate X i j k hij hik hjk n b = g := by
  obtain ⟨a, ha, b, hb, habg⟩ := g.2
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, Subtype.ext habg⟩

/-- The finite planes exhaust the join of the two full column roots. -/
theorem iSup_rootPlaneDegreeSubgroup
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ⨆ n, rootPlaneDegreeSubgroup X i j k hij hik hjk n =
      elementaryRootSubgroup i k hik ⊔ elementaryRootSubgroup j k hjk := by
  apply le_antisymm
  · apply iSup_le
    rintro n g ⟨a, _, b, _, rfl⟩
    exact (elementaryRootSubgroup i k hik ⊔
      elementaryRootSubgroup j k hjk).mul_mem
        ((show elementaryRootSubgroup i k hik ≤
          elementaryRootSubgroup i k hik ⊔ elementaryRootSubgroup j k hjk from
            le_sup_left) ⟨a, rfl⟩)
        ((show elementaryRootSubgroup j k hjk ≤
          elementaryRootSubgroup i k hik ⊔ elementaryRootSubgroup j k hjk from
            le_sup_right) ⟨b, rfl⟩)
  · apply sup_le
    · rintro g ⟨a, rfl⟩
      obtain ⟨n, hn⟩ := exists_mem_degreeLE X a
      apply (le_iSup (rootPlaneDegreeSubgroup X i j k hij hik hjk) n)
      exact ⟨a, hn, 0, (degreeLE X n).zero_mem, by simp⟩
    · rintro g ⟨b, rfl⟩
      obtain ⟨n, hn⟩ := exists_mem_degreeLE X b
      apply (le_iSup (rootPlaneDegreeSubgroup X i j k hij hik hjk) n)
      exact ⟨0, (degreeLE X n).zero_mem, b, hn, by simp⟩

/-- Regard a degree-`n` coefficient as a degree-`n+1` coefficient. -/
noncomputable def coefficientSucc {n : ℕ} (a : degreeLE X n) :
    degreeLE X (n + 1) :=
  ⟨a.1, degreeLE_mono X (Nat.le_succ n) a.2⟩

/-- Left multiplication by a free generator, as a coefficient in the next
degree stage. -/
noncomputable def generatorMulCoefficientSucc {n : ℕ} (x : X)
    (a : degreeLE X n) : degreeLE X (n + 1) :=
  ⟨FreeAlgebra.ι (ZMod 2) x * a.1,
    generator_mul_mem_degreeLE_succ X x a.2⟩

/-- The next-stage plane element obtained by shearing a pure second
coordinate by a free generator. -/
noncomputable def generatorShearedSecondCoordinate
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : X) (n : ℕ) (b : degreeLE X n) :
    rootPlaneDegreeSubgroup X i j k hij hik hjk (n + 1) :=
  firstCoordinate X i j k hij hik hjk (n + 1)
      (generatorMulCoefficientSucc X x b) *
    secondCoordinate X i j k hij hik hjk (n + 1)
      (coefficientSucc X b)

@[simp] theorem coefficientSucc_val {n : ℕ} (a : degreeLE X n) :
    (coefficientSucc X a).1 = a.1 := rfl

@[simp] theorem generatorMulCoefficientSucc_val {n : ℕ} (x : X)
    (a : degreeLE X n) :
    (generatorMulCoefficientSucc X x a).1 =
      FreeAlgebra.ι (ZMod 2) x * a.1 := rfl

/-- Generator multiplication of a bounded tail monomial is exactly the
bounded monomial of the word obtained by adjoining that generator on the
left. -/
theorem generatorMulCoefficientSucc_wordMonomialInDegree
    (x : X) (n : ℕ) (w : FreeMonoid X)
    (hw : freeWordLength X w ≤ n) :
    generatorMulCoefficientSucc X x (wordMonomialInDegree X n w) =
      wordMonomialInDegree X (n + 1) (FreeMonoid.of x * w) := by
  have hprod : freeWordLength X (FreeMonoid.of x * w) ≤ n + 1 := by
    rw [freeWordLength_mul, freeWordLength_of]
    omega
  apply Subtype.ext
  rw [generatorMulCoefficientSucc_val,
    wordMonomialInDegree_of_le X w hw,
    wordMonomialInDegree_of_le X (FreeMonoid.of x * w) hprod]
  change FreeAlgebra.ι (ZMod 2) x * wordMonomial X w =
    wordMonomial X (FreeMonoid.of x * w)
  rw [← wordMonomial_mul X (FreeMonoid.of x) w, wordMonomial_of]

/-- The exact adjacent-stage shear on the second plane coordinate.  This is
an equality of actual elementary matrices, not merely membership in the next
stage. -/
theorem conjugate_secondCoordinate_generator
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : X) (n : ℕ) (b : degreeLE X n) :
    elementaryRoot i j hij (FreeAlgebra.ι (ZMod 2) x) *
        (secondCoordinate X i j k hij hik hjk n b).1 *
        (elementaryRoot i j hij (FreeAlgebra.ι (ZMod 2) x))⁻¹ =
      (generatorShearedSecondCoordinate X i j k hij hik hjk x n b).1 := by
  exact FreeRootActions.conjugate_by_generator X i j k hij hjk hik x b.1

/-- The same adjacent shear fixes the first coordinate, viewed in the next
degree stage. -/
theorem conjugate_firstCoordinate_generator
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : X) (n : ℕ) (a : degreeLE X n) :
    elementaryRoot i j hij (FreeAlgebra.ι (ZMod 2) x) *
        (firstCoordinate X i j k hij hik hjk n a).1 *
        (elementaryRoot i j hij (FreeAlgebra.ι (ZMod 2) x))⁻¹ =
      (firstCoordinate X i j k hij hik hjk (n + 1)
        (coefficientSucc X a)).1 := by
  have hcomm := elementaryRoot_commute_of_ne i j i k hij hik
    hij.symm hik.symm (FreeAlgebra.ι (ZMod 2) x) a.1
  change elementaryRoot i j hij (FreeAlgebra.ι (ZMod 2) x) *
      elementaryRoot i k hik a.1 *
      (elementaryRoot i j hij (FreeAlgebra.ι (ZMod 2) x))⁻¹ =
    elementaryRoot i k hik a.1
  rw [hcomm.eq]
  simp

/-- Conjugation by an adjacent free-generator root sends the degree-`n`
plane into the degree-`n+1` plane. -/
theorem conjugate_generator_mem_succ
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : X) (n : ℕ)
    (g : elementaryGroup (Fin 3) (FreeRing X))
    (hg : g ∈ rootPlaneDegreeSubgroup X i j k hij hik hjk n) :
    elementaryRoot i j hij (FreeAlgebra.ι (ZMod 2) x) * g *
        (elementaryRoot i j hij (FreeAlgebra.ι (ZMod 2) x))⁻¹ ∈
      rootPlaneDegreeSubgroup X i j k hij hik hjk (n + 1) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hg
  let q := elementaryRoot i j hij (FreeAlgebra.ι (ZMod 2) x)
  have hqa : Commute q (elementaryRoot i k hik a) :=
    elementaryRoot_commute_of_ne i j i k hij hik hij.symm hik.symm _ _
  have hqaConj : q * elementaryRoot i k hik a * q⁻¹ =
      elementaryRoot i k hik a := by
    rw [hqa.eq]
    simp
  have hshift := elementaryRoot_conjugate i j k hij hjk hik
    (FreeAlgebra.ι (ZMod 2) x) b
  refine ⟨a + FreeAlgebra.ι (ZMod 2) x * b, ?_, b, ?_, ?_⟩
  · exact (degreeLE X (n + 1)).add_mem
      (degreeLE_mono X (Nat.le_succ n) ha)
      (generator_mul_mem_degreeLE_succ X x hb)
  · exact degreeLE_mono X (Nat.le_succ n) hb
  · rw [show q * (elementaryRoot i k hik a * elementaryRoot j k hjk b) * q⁻¹ =
        (q * elementaryRoot i k hik a * q⁻¹) *
          (q * elementaryRoot j k hjk b * q⁻¹) by group]
    rw [hqaConj, hshift]
    rw [← elementaryRoot_mul i k hik a
      (FreeAlgebra.ι (ZMod 2) x * b), mul_assoc]

end FreeRootPlane

end NonsoficGroupsExist
