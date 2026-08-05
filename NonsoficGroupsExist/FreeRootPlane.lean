import NonsoficGroupsExist.FreeRootActions
import Mathlib.Algebra.CharP.Algebra

/-!
# Finite coefficient planes in the free elementary group

Two roots in a common column form the additive plane on which the adjacent
rank-two elementary group acts in Kassabov's relative-property-`(T)` proof.
Here the plane is built coefficient by coefficient over an arbitrary
commutative coefficient ring.  Its degree stages are subgroups, finite over
finite coefficients, exhaust the join of the two full root subgroups, and are
carried one stage forward by each free-generator shear.
-/

namespace NonsoficGroupsExist

namespace FreeRootPlane

open FreeAlgebraDegree FreeRootFiltration

variable (X : Type*) [Fintype X]
variable (R : Type*) [CommRing R]

/-- The finite coefficient plane in a common column, at degree `n`. -/
noncomputable def rootPlaneDegreeSubgroup
    (i j k : Fin 3) (_hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ) :
    Subgroup (elementaryGroup (Fin 3) (FreeAlgebra R X)) where
  carrier := {g | ∃ a : FreeAlgebra R X, a ∈ degreeLE X R n ∧
    ∃ b : FreeAlgebra R X, b ∈ degreeLE X R n ∧
      elementaryRoot i k hik a * elementaryRoot j k hjk b = g}
  one_mem' := ⟨0, (degreeLE X R n).zero_mem, 0, (degreeLE X R n).zero_mem, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
    refine ⟨a + c, (degreeLE X R n).add_mem ha hc,
      b + d, (degreeLE X R n).add_mem hb hd, ?_⟩
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
    refine ⟨-a, (degreeLE X R n).neg_mem ha,
      -b, (degreeLE X R n).neg_mem hb, ?_⟩
    rw [elementaryRoot_neg, elementaryRoot_neg, mul_inv_rev]
    exact (elementaryRoot_commute_of_ne i k j k hik hjk
      hjk.symm hik.symm a b).inv_left.inv_right.eq

theorem mem_rootPlaneDegreeSubgroup_iff
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (g : elementaryGroup (Fin 3) (FreeAlgebra R X)) :
    g ∈ rootPlaneDegreeSubgroup X R i j k hij hik hjk n ↔
      ∃ a : FreeAlgebra R X, a ∈ degreeLE X R n ∧
      ∃ b : FreeAlgebra R X, b ∈ degreeLE X R n ∧
        elementaryRoot i k hik a * elementaryRoot j k hjk b = g :=
  Iff.rfl

/-- Every coefficient-plane degree stage is finite. -/
noncomputable instance finite_rootPlaneDegreeSubgroup [Finite R]
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ) :
    Finite (rootPlaneDegreeSubgroup X R i j k hij hik hjk n) := by
  let f : degreeLE X R n × degreeLE X R n →
      rootPlaneDegreeSubgroup X R i j k hij hik hjk n := fun p ↦
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
    Monotone (rootPlaneDegreeSubgroup X R i j k hij hik hjk) := by
  intro m n hmn g
  rintro ⟨a, ha, b, hb, habg⟩
  exact ⟨a, degreeLE_mono X R hmn ha, b, degreeLE_mono X R hmn hb, habg⟩

/-- Every finite coefficient plane is abelian. -/
theorem rootPlaneDegreeSubgroup_commute
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ) :
    ∀ g ∈ rootPlaneDegreeSubgroup X R i j k hij hik hjk n,
      ∀ h ∈ rootPlaneDegreeSubgroup X R i j k hij hik hjk n,
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

omit [Fintype X] in
/-- The free algebra inherits the characteristic of its coefficient ring. -/
instance charP_freeAlgebra (p : ℕ) [CharP R p] :
    CharP (FreeAlgebra R X) p :=
  charP_of_injective_algebraMap
    (FreeAlgebra.algebraMap_leftInverse (R := R) (X := X)).injective p

/-- Every element of a coefficient plane has exponent dividing the
characteristic. -/
theorem rootPlaneDegreeSubgroup_pow_char
    (p : ℕ) [CharP (FreeAlgebra R X) p]
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ) :
    ∀ g ∈ rootPlaneDegreeSubgroup X R i j k hij hik hjk n, g ^ p = 1 := by
  rintro _ ⟨a, _, b, _, rfl⟩
  have hcomm := elementaryRoot_commute_of_ne i k j k hik hjk
    hjk.symm hik.symm a b
  rw [hcomm.mul_pow, elementaryRoot_pow_char p i k hik a,
    elementaryRoot_pow_char p j k hjk b, one_mul]

/-- The first coefficient coordinate inside a finite plane stage. -/
noncomputable def firstCoordinate
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (a : degreeLE X R n) : rootPlaneDegreeSubgroup X R i j k hij hik hjk n :=
  ⟨elementaryRoot i k hik a.1,
    ⟨a.1, a.2, 0, (degreeLE X R n).zero_mem, by simp⟩⟩

/-- The second coefficient coordinate inside a finite plane stage. -/
noncomputable def secondCoordinate
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (b : degreeLE X R n) : rootPlaneDegreeSubgroup X R i j k hij hik hjk n :=
  ⟨elementaryRoot j k hjk b.1,
    ⟨0, (degreeLE X R n).zero_mem, b.1, b.2, by simp⟩⟩

@[simp] theorem firstCoordinate_val
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (a : degreeLE X R n) :
    (firstCoordinate X R i j k hij hik hjk n a :
      elementaryGroup (Fin 3) (FreeAlgebra R X)) = elementaryRoot i k hik a.1 := rfl

@[simp] theorem secondCoordinate_val
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (b : degreeLE X R n) :
    (secondCoordinate X R i j k hij hik hjk n b :
      elementaryGroup (Fin 3) (FreeAlgebra R X)) = elementaryRoot j k hjk b.1 := rfl

theorem firstCoordinate_add
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (a b : degreeLE X R n) :
    firstCoordinate X R i j k hij hik hjk n (a + b) =
      firstCoordinate X R i j k hij hik hjk n a *
        firstCoordinate X R i j k hij hik hjk n b := by
  apply Subtype.ext
  exact (elementaryRoot_mul i k hik a.1 b.1).symm

theorem secondCoordinate_add
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (a b : degreeLE X R n) :
    secondCoordinate X R i j k hij hik hjk n (a + b) =
      secondCoordinate X R i j k hij hik hjk n a *
        secondCoordinate X R i j k hij hik hjk n b := by
  apply Subtype.ext
  exact (elementaryRoot_mul j k hjk a.1 b.1).symm

/-- Every plane element factors through its two coefficient coordinates. -/
theorem exists_coordinate_factorization
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (g : rootPlaneDegreeSubgroup X R i j k hij hik hjk n) :
    ∃ a b : degreeLE X R n,
      firstCoordinate X R i j k hij hik hjk n a *
        secondCoordinate X R i j k hij hik hjk n b = g := by
  obtain ⟨a, ha, b, hb, habg⟩ := g.2
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, Subtype.ext habg⟩

/-- The finite planes exhaust the join of the two full column roots. -/
theorem iSup_rootPlaneDegreeSubgroup
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ⨆ n, rootPlaneDegreeSubgroup X R i j k hij hik hjk n =
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
      obtain ⟨n, hn⟩ := exists_mem_degreeLE X R a
      apply (le_iSup (rootPlaneDegreeSubgroup X R i j k hij hik hjk) n)
      exact ⟨a, hn, 0, (degreeLE X R n).zero_mem, by simp⟩
    · rintro g ⟨b, rfl⟩
      obtain ⟨n, hn⟩ := exists_mem_degreeLE X R b
      apply (le_iSup (rootPlaneDegreeSubgroup X R i j k hij hik hjk) n)
      exact ⟨0, (degreeLE X R n).zero_mem, b, hn, by simp⟩

/-- Regard a degree-`n` coefficient as a degree-`n+1` coefficient. -/
noncomputable def coefficientSucc {n : ℕ} (a : degreeLE X R n) :
    degreeLE X R (n + 1) :=
  ⟨a.1, degreeLE_mono X R (Nat.le_succ n) a.2⟩

/-- Left multiplication by a free generator, as a coefficient in the next
degree stage. -/
noncomputable def generatorMulCoefficientSucc {n : ℕ} (x : X)
    (a : degreeLE X R n) : degreeLE X R (n + 1) :=
  ⟨FreeAlgebra.ι R x * a.1,
    generator_mul_mem_degreeLE_succ X R x a.2⟩

/-- The next-stage plane element obtained by shearing a pure second
coordinate by a free generator. -/
noncomputable def generatorShearedSecondCoordinate
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : X) (n : ℕ) (b : degreeLE X R n) :
    rootPlaneDegreeSubgroup X R i j k hij hik hjk (n + 1) :=
  firstCoordinate X R i j k hij hik hjk (n + 1)
      (generatorMulCoefficientSucc X R x b) *
    secondCoordinate X R i j k hij hik hjk (n + 1)
      (coefficientSucc X R b)

/-- The opposite adjacent shear of a pure first coordinate.  Conjugation by
the `j,i` generator fixes the first coefficient and adds its left-generator
multiple to the second coefficient. -/
noncomputable def generatorShearedFirstCoordinate
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : X) (n : ℕ) (a : degreeLE X R n) :
    rootPlaneDegreeSubgroup X R i j k hij hik hjk (n + 1) :=
  firstCoordinate X R i j k hij hik hjk (n + 1)
      (coefficientSucc X R a) *
    secondCoordinate X R i j k hij hik hjk (n + 1)
      (generatorMulCoefficientSucc X R x a)

@[simp] theorem coefficientSucc_val {n : ℕ} (a : degreeLE X R n) :
    (coefficientSucc X R a).1 = a.1 := rfl

@[simp] theorem coefficientSucc_zero {n : ℕ} :
    coefficientSucc X R (0 : degreeLE X R n) = 0 := by
  rfl

@[simp] theorem generatorMulCoefficientSucc_val {n : ℕ} (x : X)
    (a : degreeLE X R n) :
    (generatorMulCoefficientSucc X R x a).1 =
      FreeAlgebra.ι R x * a.1 := rfl

@[simp] theorem generatorMulCoefficientSucc_zero {n : ℕ} (x : X) :
    generatorMulCoefficientSucc X R x (0 : degreeLE X R n) = 0 := by
  apply Subtype.ext
  simp

theorem generatorMulCoefficientSucc_add {n : ℕ} (x : X)
    (a b : degreeLE X R n) :
    generatorMulCoefficientSucc X R x (a + b) =
      generatorMulCoefficientSucc X R x a +
        generatorMulCoefficientSucc X R x b := by
  apply Subtype.ext
  simp [mul_add]

/-- Generator multiplication of a bounded tail monomial is exactly the
bounded monomial of the word obtained by adjoining that generator on the
left. -/
theorem generatorMulCoefficientSucc_wordMonomialInDegree
    (x : X) (n : ℕ) (w : FreeMonoid X)
    (hw : freeWordLength X w ≤ n) :
    generatorMulCoefficientSucc X R x (wordMonomialInDegree X R n w) =
      wordMonomialInDegree X R (n + 1) (FreeMonoid.of x * w) := by
  have hprod : freeWordLength X (FreeMonoid.of x * w) ≤ n + 1 := by
    rw [freeWordLength_mul, freeWordLength_of]
    omega
  apply Subtype.ext
  rw [generatorMulCoefficientSucc_val,
    wordMonomialInDegree_of_le X R w hw,
    wordMonomialInDegree_of_le X R (FreeMonoid.of x * w) hprod]
  change FreeAlgebra.ι R x * wordMonomial X R w =
    wordMonomial X R (FreeMonoid.of x * w)
  rw [← wordMonomial_mul X R (FreeMonoid.of x) w, wordMonomial_of]

/-- The filtration inclusion preserves every bounded basis monomial exactly. -/
theorem coefficientSucc_wordMonomialInDegree
    (n : ℕ) (w : FreeMonoid X) (hw : freeWordLength X w ≤ n) :
    coefficientSucc X R (wordMonomialInDegree X R n w) =
      wordMonomialInDegree X R (n + 1) w := by
  have hsucc : freeWordLength X w ≤ n + 1 := hw.trans (Nat.le_succ n)
  apply Subtype.ext
  rw [coefficientSucc_val, wordMonomialInDegree_of_le X R w hw,
    wordMonomialInDegree_of_le X R w hsucc]

/-- The exact adjacent-stage shear on the second plane coordinate.  This is
an equality of actual elementary matrices, not merely membership in the next
stage. -/
theorem conjugate_secondCoordinate_generator
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : X) (n : ℕ) (b : degreeLE X R n) :
    elementaryRoot i j hij (FreeAlgebra.ι R x) *
        (secondCoordinate X R i j k hij hik hjk n b).1 *
        (elementaryRoot i j hij (FreeAlgebra.ι R x))⁻¹ =
      (generatorShearedSecondCoordinate X R i j k hij hik hjk x n b).1 := by
  exact FreeRootActions.conjugate_by_generator X R i j k hij hjk hik x b.1

/-- The same adjacent shear fixes the first coordinate, viewed in the next
degree stage. -/
theorem conjugate_firstCoordinate_generator
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : X) (n : ℕ) (a : degreeLE X R n) :
    elementaryRoot i j hij (FreeAlgebra.ι R x) *
        (firstCoordinate X R i j k hij hik hjk n a).1 *
        (elementaryRoot i j hij (FreeAlgebra.ι R x))⁻¹ =
      (firstCoordinate X R i j k hij hik hjk (n + 1)
        (coefficientSucc X R a)).1 := by
  have hcomm := elementaryRoot_commute_of_ne i j i k hij hik
    hij.symm hik.symm (FreeAlgebra.ι R x) a.1
  change elementaryRoot i j hij (FreeAlgebra.ι R x) *
      elementaryRoot i k hik a.1 *
      (elementaryRoot i j hij (FreeAlgebra.ι R x))⁻¹ =
    elementaryRoot i k hik a.1
  rw [hcomm.eq]
  simp

/-- Conjugation by the opposite adjacent generator performs the exact shear
on a pure first-coordinate element. -/
theorem conjugate_firstCoordinate_opposite_generator
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : X) (n : ℕ) (a : degreeLE X R n) :
    elementaryRoot j i hij.symm (FreeAlgebra.ι R x) *
        (firstCoordinate X R i j k hij hik hjk n a).1 *
        (elementaryRoot j i hij.symm
          (FreeAlgebra.ι R x))⁻¹ =
      (generatorShearedFirstCoordinate X R i j k hij hik hjk x n a).1 := by
  change elementaryRoot j i hij.symm (FreeAlgebra.ι R x) *
      elementaryRoot i k hik a.1 *
      (elementaryRoot j i hij.symm (FreeAlgebra.ι R x))⁻¹ =
    elementaryRoot i k hik a.1 *
      elementaryRoot j k hjk (FreeAlgebra.ι R x * a.1)
  rw [FreeRootActions.conjugate_by_generator X R j i k hij.symm hik hjk]
  exact (elementaryRoot_commute_of_ne j k i k hjk hik
    hik.symm hjk.symm _ _).eq

/-- The opposite adjacent shear fixes the second coordinate, viewed in the
next degree stage. -/
theorem conjugate_secondCoordinate_opposite_generator
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : X) (n : ℕ) (b : degreeLE X R n) :
    elementaryRoot j i hij.symm (FreeAlgebra.ι R x) *
        (secondCoordinate X R i j k hij hik hjk n b).1 *
        (elementaryRoot j i hij.symm
          (FreeAlgebra.ι R x))⁻¹ =
      (secondCoordinate X R i j k hij hik hjk (n + 1)
        (coefficientSucc X R b)).1 := by
  have hcomm := elementaryRoot_commute_of_ne j i j k hij.symm hjk
    hij hjk.symm (FreeAlgebra.ι R x) b.1
  change elementaryRoot j i hij.symm (FreeAlgebra.ι R x) *
      elementaryRoot j k hjk b.1 *
      (elementaryRoot j i hij.symm (FreeAlgebra.ι R x))⁻¹ =
    elementaryRoot j k hjk b.1
  rw [hcomm.eq]
  simp

/-- Conjugation by an adjacent free-generator root sends the degree-`n`
plane into the degree-`n+1` plane. -/
theorem conjugate_generator_mem_succ
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : X) (n : ℕ)
    (g : elementaryGroup (Fin 3) (FreeAlgebra R X))
    (hg : g ∈ rootPlaneDegreeSubgroup X R i j k hij hik hjk n) :
    elementaryRoot i j hij (FreeAlgebra.ι R x) * g *
        (elementaryRoot i j hij (FreeAlgebra.ι R x))⁻¹ ∈
      rootPlaneDegreeSubgroup X R i j k hij hik hjk (n + 1) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hg
  let q := elementaryRoot i j hij (FreeAlgebra.ι R x)
  have hqa : Commute q (elementaryRoot i k hik a) :=
    elementaryRoot_commute_of_ne i j i k hij hik hij.symm hik.symm _ _
  have hqaConj : q * elementaryRoot i k hik a * q⁻¹ =
      elementaryRoot i k hik a := by
    rw [hqa.eq]
    simp
  have hshift := elementaryRoot_conjugate i j k hij hjk hik
    (FreeAlgebra.ι R x) b
  refine ⟨a + FreeAlgebra.ι R x * b, ?_, b, ?_, ?_⟩
  · exact (degreeLE X R (n + 1)).add_mem
      (degreeLE_mono X R (Nat.le_succ n) ha)
      (generator_mul_mem_degreeLE_succ X R x hb)
  · exact degreeLE_mono X R (Nat.le_succ n) hb
  · rw [show q * (elementaryRoot i k hik a * elementaryRoot j k hjk b) * q⁻¹ =
        (q * elementaryRoot i k hik a * q⁻¹) *
          (q * elementaryRoot j k hjk b * q⁻¹) by group]
    rw [hqaConj, hshift]
    rw [← elementaryRoot_mul i k hik a
      (FreeAlgebra.ι R x * b), mul_assoc]

/-- Conjugation by the opposite adjacent free-generator root sends the
degree-`n` plane into the degree-`n+1` plane.  This is the subgroup-level
counterpart of `conjugate_firstCoordinate_opposite_generator`; in
particular, it proves the bridge needed to re-index the entire Fourier
decomposition after the opposite shear. -/
theorem conjugate_opposite_generator_mem_succ
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : X) (n : ℕ)
    (g : elementaryGroup (Fin 3) (FreeAlgebra R X))
    (hg : g ∈ rootPlaneDegreeSubgroup X R i j k hij hik hjk n) :
    elementaryRoot j i hij.symm (FreeAlgebra.ι R x) * g *
        (elementaryRoot j i hij.symm (FreeAlgebra.ι R x))⁻¹ ∈
      rootPlaneDegreeSubgroup X R i j k hij hik hjk (n + 1) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hg
  let q := elementaryRoot j i hij.symm (FreeAlgebra.ι R x)
  refine ⟨a, degreeLE_mono X R (Nat.le_succ n) ha,
    FreeAlgebra.ι R x * a + b, ?_, ?_⟩
  · exact (degreeLE X R (n + 1)).add_mem
      (generator_mul_mem_degreeLE_succ X R x ha)
      (degreeLE_mono X R (Nat.le_succ n) hb)
  · symm
    have hfirst := conjugate_firstCoordinate_opposite_generator
      X R i j k hij hik hjk x n ⟨a, ha⟩
    change elementaryRoot j i hij.symm (FreeAlgebra.ι R x) *
        elementaryRoot i k hik a *
        (elementaryRoot j i hij.symm (FreeAlgebra.ι R x))⁻¹ =
      elementaryRoot i k hik a *
        elementaryRoot j k hjk (FreeAlgebra.ι R x * a) at hfirst
    have hsecond := conjugate_secondCoordinate_opposite_generator
      X R i j k hij hik hjk x n ⟨b, hb⟩
    change elementaryRoot j i hij.symm (FreeAlgebra.ι R x) *
        elementaryRoot j k hjk b *
        (elementaryRoot j i hij.symm (FreeAlgebra.ι R x))⁻¹ =
      elementaryRoot j k hjk b at hsecond
    rw [show q * (elementaryRoot i k hik a * elementaryRoot j k hjk b) * q⁻¹ =
        (q * elementaryRoot i k hik a * q⁻¹) *
          (q * elementaryRoot j k hjk b * q⁻¹) by group]
    dsimp [q]
    rw [hfirst, hsecond]
    change (elementaryRoot i k hik a *
        elementaryRoot j k hjk (FreeAlgebra.ι R x * a)) *
        elementaryRoot j k hjk b =
      elementaryRoot i k hik a *
        elementaryRoot j k hjk (FreeAlgebra.ι R x * a + b)
    rw [mul_assoc, ← elementaryRoot_mul]

/-- Conjugation by the forward adjacent unit root preserves every plane
degree stage. -/
theorem conjugate_unit_mem
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (g : elementaryGroup (Fin 3) (FreeAlgebra R X))
    (hg : g ∈ rootPlaneDegreeSubgroup X R i j k hij hik hjk n) :
    elementaryRoot i j hij 1 * g * (elementaryRoot i j hij 1)⁻¹ ∈
      rootPlaneDegreeSubgroup X R i j k hij hik hjk n := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hg
  let q := elementaryRoot i j hij (1 : FreeAlgebra R X)
  have hqa : Commute q (elementaryRoot i k hik a) :=
    elementaryRoot_commute_of_ne i j i k hij hik hij.symm hik.symm _ _
  have hqaConj : q * elementaryRoot i k hik a * q⁻¹ =
      elementaryRoot i k hik a := by
    rw [hqa.eq]
    simp
  have hshift := elementaryRoot_conjugate i j k hij hjk hik
    (1 : FreeAlgebra R X) b
  refine ⟨a + b, (degreeLE X R n).add_mem ha hb, b, hb, ?_⟩
  rw [show q * (elementaryRoot i k hik a * elementaryRoot j k hjk b) * q⁻¹ =
      (q * elementaryRoot i k hik a * q⁻¹) *
        (q * elementaryRoot j k hjk b * q⁻¹) by group]
  rw [hqaConj, hshift, one_mul]
  rw [← elementaryRoot_mul i k hik a b, mul_assoc]

/-- Conjugation by the opposite adjacent unit root also preserves every
plane stage. -/
theorem conjugate_opposite_unit_mem
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) (g : elementaryGroup (Fin 3) (FreeAlgebra R X))
    (hg : g ∈ rootPlaneDegreeSubgroup X R i j k hij hik hjk n) :
    elementaryRoot j i hij.symm 1 * g * (elementaryRoot j i hij.symm 1)⁻¹ ∈
      rootPlaneDegreeSubgroup X R i j k hij hik hjk n := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hg
  let q := elementaryRoot j i hij.symm (1 : FreeAlgebra R X)
  have hfirst := elementaryRoot_conjugate j i k hij.symm hik hjk
    (1 : FreeAlgebra R X) a
  have hsecondComm := elementaryRoot_commute_of_ne j i j k hij.symm hjk
    hij hjk.symm (1 : FreeAlgebra R X) b
  have hsecond : q * elementaryRoot j k hjk b * q⁻¹ =
      elementaryRoot j k hjk b := by
    dsimp [q]
    rw [hsecondComm.eq]
    simp
  have hcoordinates := elementaryRoot_commute_of_ne j k i k hjk hik
    hik.symm hjk.symm a a
  refine ⟨a, ha, a + b, (degreeLE X R n).add_mem ha hb, ?_⟩
  rw [show q * (elementaryRoot i k hik a * elementaryRoot j k hjk b) * q⁻¹ =
      (q * elementaryRoot i k hik a * q⁻¹) *
        (q * elementaryRoot j k hjk b * q⁻¹) by group]
  dsimp [q]
  rw [hfirst, one_mul, hsecond]
  rw [hcoordinates.eq, mul_assoc, ← elementaryRoot_mul]

end FreeRootPlane

end NonsoficGroupsExist
