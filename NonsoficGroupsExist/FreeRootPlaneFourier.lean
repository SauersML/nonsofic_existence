import NonsoficGroupsExist.FiniteInvolutionDecomposition
import NonsoficGroupsExist.FreeRootPlane
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Fourier components of a finite free-root plane

This file enumerates every element of a concrete finite root-plane stage and
applies the finite involution decomposition to that exhaustive family.  Thus
the sign components below simultaneously diagonalize the whole finite stage,
not merely a selected generating subset.
-/

namespace NonsoficGroupsExist

universe u

namespace FreeRootPlaneFourier

open FreeRootFiltration FreeRootPlane
open FiniteInvolutionDecomposition

noncomputable section

variable (X : Type*) [Fintype X]

abbrev Plane (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (n : ℕ) := rootPlaneDegreeSubgroup X i j k hij hik hjk n

/-- An exhaustive enumeration of a finite plane stage. -/
noncomputable def planeEnumeration
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ) :
    Fin (Nat.card (Plane X i j k hij hik hjk n)) ≃
      Plane X i j k hij hik hjk n :=
  (Finite.equivFin (Plane X i j k hij hik hjk n)).symm

/-- The enumerated stage elements, regarded in the ambient elementary group. -/
noncomputable def planeFamily
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ) :
    Fin (Nat.card (Plane X i j k hij hik hjk n)) →
      elementaryGroup (Fin 3) (FreeRing X) :=
  fun q ↦ (planeEnumeration X i j k hij hik hjk n q).1

theorem planeFamily_sq
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ) :
    ∀ q, planeFamily X i j k hij hik hjk n q ^ 2 = 1 := by
  intro q
  exact rootPlaneDegreeSubgroup_sq X i j k hij hik hjk n _
    (planeEnumeration X i j k hij hik hjk n q).2

theorem planeFamily_pairwise_commute
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ) :
    Pairwise (Function.onFun Commute
      (planeFamily X i j k hij hik hjk n)) := by
  intro q r _
  exact rootPlaneDegreeSubgroup_commute X i j k hij hik hjk n _
    (planeEnumeration X i j k hij hik hjk n q).2 _
    (planeEnumeration X i j k hij hik hjk n r).2

/-- Every stage element occurs in the enumeration. -/
theorem exists_planeFamily_eq
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (g : Plane X i j k hij hik hjk n) :
    ∃ q, planeFamily X i j k hij hik hjk n q = g.1 := by
  obtain ⟨q, hq⟩ := (planeEnumeration X i j k hij hik hjk n).surjective g
  exact ⟨q, congrArg Subtype.val hq⟩

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The simultaneous sign component associated to the exhaustive plane
enumeration. -/
noncomputable def planeComponent
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool) (z : E) : E :=
  iteratedPart rho (planeFamily X i j k hij hik hjk n) sign z

theorem sum_planeComponent
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E)) (z : E) :
    ∑ sign, planeComponent X i j k hij hik hjk n rho sign z = z :=
  sum_iteratedPart rho _ _ z

theorem sum_norm_planeComponent_sq
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E)) (z : E) :
    ∑ sign, ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2 = ‖z‖ ^ 2 :=
  sum_norm_iteratedPart_sq rho _ _
    (planeFamily_sq X i j k hij hik hjk n) z

/-- Every plane component has its prescribed sign under every element of the
finite plane stage. -/
theorem action_planeComponent
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool)
    (z : E) (q : Fin (Nat.card (Plane X i j k hij hik hjk n))) :
    rho (planeFamily X i j k hij hik hjk n q)
        (planeComponent X i j k hij hik hjk n rho sign z) =
      if sign q then planeComponent X i j k hij hik hjk n rho sign z
      else -planeComponent X i j k hij hik hjk n rho sign z :=
  action_iteratedPart rho _ _
    (planeFamily_sq X i j k hij hik hjk n)
    (planeFamily_pairwise_commute X i j k hij hik hjk n) sign z q

/-- The real `±1` value assigned by a binary sign choice to a plane element. -/
def planeEigenvalue
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool)
    (g : Plane X i j k hij hik hjk n) : ℝ :=
  if sign ((planeEnumeration X i j k hij hik hjk n).symm g) then 1 else -1

/-- An arbitrary stage element acts on a component by its assigned real
eigenvalue. -/
theorem action_planeComponent_element
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool)
    (z : E) (g : Plane X i j k hij hik hjk n) :
    rho g.1 (planeComponent X i j k hij hik hjk n rho sign z) =
      planeEigenvalue X i j k hij hik hjk n sign g •
        planeComponent X i j k hij hik hjk n rho sign z := by
  let q := (planeEnumeration X i j k hij hik hjk n).symm g
  have hq : planeFamily X i j k hij hik hjk n q = g.1 := by
    exact congrArg Subtype.val
      ((planeEnumeration X i j k hij hik hjk n).apply_symm_apply g)
  rw [← hq]
  have haction := action_planeComponent X i j k hij hik hjk n rho sign z q
  simpa [planeEigenvalue, q] using haction

/-- On every nonzero component, the assigned eigenvalue is multiplicative.
Thus inconsistent binary assignments necessarily have zero component. -/
theorem planeEigenvalue_mul_of_component_ne_zero
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool)
    (z : E)
    (hv : planeComponent X i j k hij hik hjk n rho sign z ≠ 0)
    (g h : Plane X i j k hij hik hjk n) :
    planeEigenvalue X i j k hij hik hjk n sign (g * h) =
      planeEigenvalue X i j k hij hik hjk n sign g *
        planeEigenvalue X i j k hij hik hjk n sign h := by
  let v := planeComponent X i j k hij hik hjk n rho sign z
  let lambda := planeEigenvalue X i j k hij hik hjk n sign
  have hg := action_planeComponent_element X i j k hij hik hjk n rho sign z g
  have hh := action_planeComponent_element X i j k hij hik hjk n rho sign z h
  have hgh := action_planeComponent_element X i j k hij hik hjk n rho sign z (g * h)
  have heq : lambda (g * h) • v = (lambda g * lambda h) • v := by
    calc
      lambda (g * h) • v = rho (g * h).1 v := hgh.symm
      _ = rho g.1 (rho h.1 v) := by
        change rho (g.1 * h.1) v = rho g.1 (rho h.1 v)
        rw [map_mul]
        rfl
      _ = rho g.1 (lambda h • v) := by rw [hh]
      _ = lambda h • rho g.1 v := by rw [map_smul]
      _ = lambda h • (lambda g • v) := by rw [hg]
      _ = (lambda g * lambda h) • v := by
        rw [smul_smul, mul_comm]
  have hzero : (lambda (g * h) - lambda g * lambda h) • v = 0 := by
    rw [sub_smul, heq, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right hv)

/-- On every nonzero component, the identity has eigenvalue `1`. -/
theorem planeEigenvalue_one_of_component_ne_zero
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool)
    (z : E)
    (hv : planeComponent X i j k hij hik hjk n rho sign z ≠ 0) :
    planeEigenvalue X i j k hij hik hjk n sign 1 = 1 := by
  let v := planeComponent X i j k hij hik hjk n rho sign z
  let lambda := planeEigenvalue X i j k hij hik hjk n sign
  have hone := action_planeComponent_element X i j k hij hik hjk n rho sign z
    (1 : Plane X i j k hij hik hjk n)
  have heq : lambda 1 • v = (1 : ℝ) • v := by
    rw [← hone]
    simp [v]
  have hzero : (lambda 1 - 1) • v = 0 := by
    rw [sub_smul, heq, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right hv)

/-- The character value on the first coefficient root. -/
def firstCoefficientEigenvalue
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool)
    (a : FreeAlgebraDegree.degreeLE X n) : ℝ :=
  planeEigenvalue X i j k hij hik hjk n sign
    (firstCoordinate X i j k hij hik hjk n a)

/-- The character value on the second coefficient root. -/
def secondCoefficientEigenvalue
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool)
    (b : FreeAlgebraDegree.degreeLE X n) : ℝ :=
  planeEigenvalue X i j k hij hik hjk n sign
    (secondCoordinate X i j k hij hik hjk n b)

/-- On a nonzero component, the first coefficient character converts
addition into multiplication of signs. -/
theorem firstCoefficientEigenvalue_add_of_component_ne_zero
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool)
    (z : E)
    (hv : planeComponent X i j k hij hik hjk n rho sign z ≠ 0)
    (a b : FreeAlgebraDegree.degreeLE X n) :
    firstCoefficientEigenvalue X i j k hij hik hjk n sign (a + b) =
      firstCoefficientEigenvalue X i j k hij hik hjk n sign a *
        firstCoefficientEigenvalue X i j k hij hik hjk n sign b := by
  rw [firstCoefficientEigenvalue, firstCoordinate_add]
  exact planeEigenvalue_mul_of_component_ne_zero X i j k hij hik hjk n
    rho sign z hv _ _

/-- On a nonzero component, the second coefficient character converts
addition into multiplication of signs. -/
theorem secondCoefficientEigenvalue_add_of_component_ne_zero
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool)
    (z : E)
    (hv : planeComponent X i j k hij hik hjk n rho sign z ≠ 0)
    (a b : FreeAlgebraDegree.degreeLE X n) :
    secondCoefficientEigenvalue X i j k hij hik hjk n sign (a + b) =
      secondCoefficientEigenvalue X i j k hij hik hjk n sign a *
        secondCoefficientEigenvalue X i j k hij hik hjk n sign b := by
  rw [secondCoefficientEigenvalue, secondCoordinate_add]
  exact planeEigenvalue_mul_of_component_ne_zero X i j k hij hik hjk n
    rho sign z hv _ _

/-- The first coefficient character sends zero to `1` on a nonzero
component. -/
theorem firstCoefficientEigenvalue_zero_of_component_ne_zero
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool)
    (z : E)
    (hv : planeComponent X i j k hij hik hjk n rho sign z ≠ 0) :
    firstCoefficientEigenvalue X i j k hij hik hjk n sign 0 = 1 := by
  have hcoord : firstCoordinate X i j k hij hik hjk n 0 = 1 := by
    apply Subtype.ext
    simp
  rw [firstCoefficientEigenvalue, hcoord]
  exact planeEigenvalue_one_of_component_ne_zero X i j k hij hik hjk n
    rho sign z hv

/-- The second coefficient character sends zero to `1` on a nonzero
component. -/
theorem secondCoefficientEigenvalue_zero_of_component_ne_zero
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool)
    (z : E)
    (hv : planeComponent X i j k hij hik hjk n rho sign z ≠ 0) :
    secondCoefficientEigenvalue X i j k hij hik hjk n sign 0 = 1 := by
  have hcoord : secondCoordinate X i j k hij hik hjk n 0 = 1 := by
    apply Subtype.ext
    simp
  rw [secondCoefficientEigenvalue, hcoord]
  exact planeEigenvalue_one_of_component_ne_zero X i j k hij hik hjk n
    rho sign z hv

end

end FreeRootPlaneFourier

end NonsoficGroupsExist
