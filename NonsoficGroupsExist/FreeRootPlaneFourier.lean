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

end

end FreeRootPlaneFourier

end NonsoficGroupsExist
