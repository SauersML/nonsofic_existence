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

/-- Include one finite plane stage into the next stage without changing its
ambient elementary-group element. -/
noncomputable def planeSucc
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ) :
    Plane X i j k hij hik hjk n → Plane X i j k hij hik hjk (n + 1) :=
  fun g ↦ ⟨g.1, rootPlaneDegreeSubgroup_mono X i j k hij hik hjk
    (Nat.le_succ n) g.2⟩

/-- The index of an included stage-`n` plane element in the exhaustive
enumeration of stage `n+1`. -/
noncomputable def planeSuccIndex
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ) :
    Fin (Nat.card (Plane X i j k hij hik hjk n)) →
      Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) :=
  fun q ↦ (planeEnumeration X i j k hij hik hjk (n + 1)).symm
    (planeSucc X i j k hij hik hjk n
      (planeEnumeration X i j k hij hik hjk n q))

theorem planeFamily_succIndex
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (q : Fin (Nat.card (Plane X i j k hij hik hjk n))) :
    planeFamily X i j k hij hik hjk n q =
      planeFamily X i j k hij hik hjk (n + 1)
        (planeSuccIndex X i j k hij hik hjk n q) := by
  change (planeEnumeration X i j k hij hik hjk n q).1 =
    ((planeEnumeration X i j k hij hik hjk (n + 1))
      ((planeEnumeration X i j k hij hik hjk (n + 1)).symm
        (planeSucc X i j k hij hik hjk n
          (planeEnumeration X i j k hij hik hjk n q)))).1
  rw [Equiv.apply_symm_apply]
  rfl

/-- Conjugate every stage-`n` plane element by a forward adjacent root and
regard the result as an element of the next plane stage. -/
noncomputable def forwardConjugatedPlaneSucc
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : X) (n : ℕ) :
    Plane X i j k hij hik hjk n → Plane X i j k hij hik hjk (n + 1) :=
  fun g ↦ ⟨elementaryRoot i j hij (FreeAlgebra.ι (ZMod 2) x) * g.1 *
      (elementaryRoot i j hij (FreeAlgebra.ι (ZMod 2) x))⁻¹,
    conjugate_generator_mem_succ X i j k hij hik hjk x n g.1 g.2⟩

/-- Conjugate every stage-`n` plane element by an opposite adjacent root and
regard the result as an element of the next plane stage. -/
noncomputable def oppositeConjugatedPlaneSucc
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : X) (n : ℕ) :
    Plane X i j k hij hik hjk n → Plane X i j k hij hik hjk (n + 1) :=
  fun g ↦ ⟨elementaryRoot j i hij.symm (FreeAlgebra.ι (ZMod 2) x) * g.1 *
      (elementaryRoot j i hij.symm (FreeAlgebra.ι (ZMod 2) x))⁻¹,
    conjugate_opposite_generator_mem_succ X i j k hij hik hjk x n g.1 g.2⟩

/-- The next-stage enumeration index of the forward conjugate of a coarse
plane element. -/
noncomputable def forwardConjugatedPlaneSuccIndex
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : X) (n : ℕ) :
    Fin (Nat.card (Plane X i j k hij hik hjk n)) →
      Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) :=
  fun q ↦ (planeEnumeration X i j k hij hik hjk (n + 1)).symm
    (forwardConjugatedPlaneSucc X i j k hij hik hjk x n
      (planeEnumeration X i j k hij hik hjk n q))

/-- The next-stage enumeration index of the opposite conjugate of a coarse
plane element. -/
noncomputable def oppositeConjugatedPlaneSuccIndex
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : X) (n : ℕ) :
    Fin (Nat.card (Plane X i j k hij hik hjk n)) →
      Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) :=
  fun q ↦ (planeEnumeration X i j k hij hik hjk (n + 1)).symm
    (oppositeConjugatedPlaneSucc X i j k hij hik hjk x n
      (planeEnumeration X i j k hij hik hjk n q))

theorem planeFamily_forwardConjugatedPlaneSuccIndex
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : X) (n : ℕ)
    (q : Fin (Nat.card (Plane X i j k hij hik hjk n))) :
    elementaryRoot i j hij (FreeAlgebra.ι (ZMod 2) x) *
        planeFamily X i j k hij hik hjk n q *
        (elementaryRoot i j hij (FreeAlgebra.ι (ZMod 2) x))⁻¹ =
      planeFamily X i j k hij hik hjk (n + 1)
        (forwardConjugatedPlaneSuccIndex X i j k hij hik hjk x n q) := by
  change _ = ((planeEnumeration X i j k hij hik hjk (n + 1))
    ((planeEnumeration X i j k hij hik hjk (n + 1)).symm
      (forwardConjugatedPlaneSucc X i j k hij hik hjk x n
        (planeEnumeration X i j k hij hik hjk n q)))).1
  rw [Equiv.apply_symm_apply]
  rfl

theorem planeFamily_oppositeConjugatedPlaneSuccIndex
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : X) (n : ℕ)
    (q : Fin (Nat.card (Plane X i j k hij hik hjk n))) :
    elementaryRoot j i hij.symm (FreeAlgebra.ι (ZMod 2) x) *
        planeFamily X i j k hij hik hjk n q *
        (elementaryRoot j i hij.symm (FreeAlgebra.ι (ZMod 2) x))⁻¹ =
      planeFamily X i j k hij hik hjk (n + 1)
        (oppositeConjugatedPlaneSuccIndex X i j k hij hik hjk x n q) := by
  change _ = ((planeEnumeration X i j k hij hik hjk (n + 1))
    ((planeEnumeration X i j k hij hik hjk (n + 1)).symm
      (oppositeConjugatedPlaneSucc X i j k hij hik hjk x n
        (planeEnumeration X i j k hij hik hjk n q)))).1
  rw [Equiv.apply_symm_apply]
  rfl

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

/-- A stage-`n` plane component is exactly the sum of all stage-`n+1`
components whose signs restrict along the concrete plane inclusion. -/
theorem planeComponent_eq_sum_succ_extensions
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool)
    (z : E) :
    planeComponent X i j k hij hik hjk n rho sign z =
      ∑ fineSign ∈ (Finset.univ.filter fun fineSign :
          Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool ↦
          sign = fun q ↦
            fineSign (planeSuccIndex X i j k hij hik hjk n q)),
        planeComponent X i j k hij hik hjk (n + 1) rho fineSign z := by
  exact iteratedPart_eq_sum_fine_extensions rho
    (Nat.card (Plane X i j k hij hik hjk (n + 1)))
    (Nat.card (Plane X i j k hij hik hjk n))
    (planeFamily X i j k hij hik hjk (n + 1))
    (planeFamily X i j k hij hik hjk n)
    (planeSuccIndex X i j k hij hik hjk n)
    (planeFamily_succIndex X i j k hij hik hjk n)
    (planeFamily_sq X i j k hij hik hjk (n + 1))
    (planeFamily_pairwise_commute X i j k hij hik hjk (n + 1))
    sign z

/-- Exact Fourier transport under a forward adjacent root.  The image of a
coarse component is the sum of precisely those next-stage components whose
signs restrict along the concrete conjugated-plane index map. -/
theorem map_planeComponent_forward_eq_sum_conjugated_extensions
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : X) (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool)
    (z : E) :
    rho (elementaryRoot i j hij (FreeAlgebra.ι (ZMod 2) x))
        (planeComponent X i j k hij hik hjk n rho sign z) =
      ∑ fineSign ∈ (Finset.univ.filter fun fineSign :
          Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool ↦
          sign = fun q ↦ fineSign
            (forwardConjugatedPlaneSuccIndex
              X i j k hij hik hjk x n q)),
        planeComponent X i j k hij hik hjk (n + 1) rho fineSign
          (rho (elementaryRoot i j hij (FreeAlgebra.ι (ZMod 2) x)) z) := by
  rw [planeComponent, map_iteratedPart]
  exact iteratedPart_eq_sum_fine_extensions rho
    (Nat.card (Plane X i j k hij hik hjk (n + 1)))
    (Nat.card (Plane X i j k hij hik hjk n))
    (planeFamily X i j k hij hik hjk (n + 1))
    (fun q ↦ elementaryRoot i j hij (FreeAlgebra.ι (ZMod 2) x) *
      planeFamily X i j k hij hik hjk n q *
      (elementaryRoot i j hij (FreeAlgebra.ι (ZMod 2) x))⁻¹)
    (forwardConjugatedPlaneSuccIndex X i j k hij hik hjk x n)
    (planeFamily_forwardConjugatedPlaneSuccIndex
      X i j k hij hik hjk x n)
    (planeFamily_sq X i j k hij hik hjk (n + 1))
    (planeFamily_pairwise_commute X i j k hij hik hjk (n + 1))
    sign _

/-- Exact Fourier transport under an opposite adjacent root. -/
theorem map_planeComponent_opposite_eq_sum_conjugated_extensions
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : X) (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool)
    (z : E) :
    rho (elementaryRoot j i hij.symm (FreeAlgebra.ι (ZMod 2) x))
        (planeComponent X i j k hij hik hjk n rho sign z) =
      ∑ fineSign ∈ (Finset.univ.filter fun fineSign :
          Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool ↦
          sign = fun q ↦ fineSign
            (oppositeConjugatedPlaneSuccIndex
              X i j k hij hik hjk x n q)),
        planeComponent X i j k hij hik hjk (n + 1) rho fineSign
          (rho (elementaryRoot j i hij.symm
            (FreeAlgebra.ι (ZMod 2) x)) z) := by
  rw [planeComponent, map_iteratedPart]
  exact iteratedPart_eq_sum_fine_extensions rho
    (Nat.card (Plane X i j k hij hik hjk (n + 1)))
    (Nat.card (Plane X i j k hij hik hjk n))
    (planeFamily X i j k hij hik hjk (n + 1))
    (fun q ↦ elementaryRoot j i hij.symm (FreeAlgebra.ι (ZMod 2) x) *
      planeFamily X i j k hij hik hjk n q *
      (elementaryRoot j i hij.symm (FreeAlgebra.ι (ZMod 2) x))⁻¹)
    (oppositeConjugatedPlaneSuccIndex X i j k hij hik hjk x n)
    (planeFamily_oppositeConjugatedPlaneSuccIndex
      X i j k hij hik hjk x n)
    (planeFamily_sq X i j k hij hik hjk (n + 1))
    (planeFamily_pairwise_commute X i j k hij hik hjk (n + 1))
    sign _

/-- Exact squared-mass transport for an arbitrary set of coarse signs under
the opposite conjugated refinement. -/
theorem sum_norm_oppositeConjugatedRestriction_sq
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : X) (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (coarseSigns :
      Finset (Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool))
    (z : E) :
    ∑ fineSign ∈ fineRestrictionSignSet
          (Nat.card (Plane X i j k hij hik hjk (n + 1)))
          (Nat.card (Plane X i j k hij hik hjk n))
          (oppositeConjugatedPlaneSuccIndex X i j k hij hik hjk x n)
          coarseSigns,
        ‖planeComponent X i j k hij hik hjk (n + 1) rho fineSign z‖ ^ 2 =
      ∑ coarseSign ∈ coarseSigns,
        ‖planeComponent X i j k hij hik hjk n rho coarseSign
          (rho (elementaryRoot j i hij.symm
            (FreeAlgebra.ι (ZMod 2) x)) z)‖ ^ 2 := by
  have hsq : elementaryRoot j i hij.symm
      (FreeAlgebra.ι (ZMod 2) x) ^ 2 = 1 := by
    have hadd : FreeAlgebra.ι (ZMod 2) x + FreeAlgebra.ι (ZMod 2) x =
        (0 : FreeRing X) := by
      calc
        FreeAlgebra.ι (ZMod 2) x + FreeAlgebra.ι (ZMod 2) x =
            (1 : ZMod 2) • FreeAlgebra.ι (ZMod 2) x +
              (1 : ZMod 2) • FreeAlgebra.ι (ZMod 2) x := by
          congr 1 <;> exact (one_smul (ZMod 2) _).symm
        _ = ((1 : ZMod 2) + 1) • FreeAlgebra.ι (ZMod 2) x := by
          rw [add_smul]
        _ = 0 := by
          have htwo : (1 : ZMod 2) + 1 = 0 := by
            rw [one_add_one_eq_two]
            exact CharTwo.two_eq_zero
          rw [htwo, zero_smul]
    rw [pow_two, elementaryRoot_mul, hadd, elementaryRoot_zero]
  exact sum_norm_fineRestriction_conjugated_sq rho
    (elementaryRoot j i hij.symm (FreeAlgebra.ι (ZMod 2) x))
    hsq
    (Nat.card (Plane X i j k hij hik hjk (n + 1)))
    (Nat.card (Plane X i j k hij hik hjk n))
    (planeFamily X i j k hij hik hjk (n + 1))
    (planeFamily X i j k hij hik hjk n)
    (oppositeConjugatedPlaneSuccIndex X i j k hij hik hjk x n)
    (planeFamily_oppositeConjugatedPlaneSuccIndex
      X i j k hij hik hjk x n)
    (planeFamily_sq X i j k hij hik hjk (n + 1))
    (planeFamily_pairwise_commute X i j k hij hik hjk (n + 1))
    coarseSigns z

/-- Exact squared-mass transport for an arbitrary set of coarse signs under
the forward conjugated refinement. -/
theorem sum_norm_forwardConjugatedRestriction_sq
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : X) (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (coarseSigns :
      Finset (Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool))
    (z : E) :
    ∑ fineSign ∈ fineRestrictionSignSet
          (Nat.card (Plane X i j k hij hik hjk (n + 1)))
          (Nat.card (Plane X i j k hij hik hjk n))
          (forwardConjugatedPlaneSuccIndex X i j k hij hik hjk x n)
          coarseSigns,
        ‖planeComponent X i j k hij hik hjk (n + 1) rho fineSign z‖ ^ 2 =
      ∑ coarseSign ∈ coarseSigns,
        ‖planeComponent X i j k hij hik hjk n rho coarseSign
          (rho (elementaryRoot i j hij
            (FreeAlgebra.ι (ZMod 2) x)) z)‖ ^ 2 := by
  have hsq : elementaryRoot i j hij
      (FreeAlgebra.ι (ZMod 2) x) ^ 2 = 1 := by
    have hadd : FreeAlgebra.ι (ZMod 2) x + FreeAlgebra.ι (ZMod 2) x =
        (0 : FreeRing X) := by
      calc
        FreeAlgebra.ι (ZMod 2) x + FreeAlgebra.ι (ZMod 2) x =
            (1 : ZMod 2) • FreeAlgebra.ι (ZMod 2) x +
              (1 : ZMod 2) • FreeAlgebra.ι (ZMod 2) x := by
          congr 1 <;> exact (one_smul (ZMod 2) _).symm
        _ = ((1 : ZMod 2) + 1) • FreeAlgebra.ι (ZMod 2) x := by
          rw [add_smul]
        _ = 0 := by
          have htwo : (1 : ZMod 2) + 1 = 0 := by
            rw [one_add_one_eq_two]
            exact CharTwo.two_eq_zero
          rw [htwo, zero_smul]
    rw [pow_two, elementaryRoot_mul, hadd, elementaryRoot_zero]
  exact sum_norm_fineRestriction_conjugated_sq rho
    (elementaryRoot i j hij (FreeAlgebra.ι (ZMod 2) x))
    hsq
    (Nat.card (Plane X i j k hij hik hjk (n + 1)))
    (Nat.card (Plane X i j k hij hik hjk n))
    (planeFamily X i j k hij hik hjk (n + 1))
    (planeFamily X i j k hij hik hjk n)
    (forwardConjugatedPlaneSuccIndex X i j k hij hik hjk x n)
    (planeFamily_forwardConjugatedPlaneSuccIndex
      X i j k hij hik hjk x n)
    (planeFamily_sq X i j k hij hik hjk (n + 1))
    (planeFamily_pairwise_commute X i j k hij hik hjk (n + 1))
    coarseSigns z

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

/-- Restricting a fine sign assignment along the forward conjugated index map
computes exactly the fine eigenvalue of the concretely conjugated element. -/
theorem planeEigenvalue_forwardConjugatedRestriction
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : X) (n : ℕ)
    (fineSign : Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool)
    (g : Plane X i j k hij hik hjk n) :
    planeEigenvalue X i j k hij hik hjk n
        (fun q ↦ fineSign
          (forwardConjugatedPlaneSuccIndex X i j k hij hik hjk x n q)) g =
      planeEigenvalue X i j k hij hik hjk (n + 1) fineSign
        (forwardConjugatedPlaneSucc X i j k hij hik hjk x n g) := by
  unfold planeEigenvalue forwardConjugatedPlaneSuccIndex
  simp only [Equiv.apply_symm_apply]

/-- The corresponding exact restriction formula for the opposite shear. -/
theorem planeEigenvalue_oppositeConjugatedRestriction
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : X) (n : ℕ)
    (fineSign : Fin (Nat.card (Plane X i j k hij hik hjk (n + 1))) → Bool)
    (g : Plane X i j k hij hik hjk n) :
    planeEigenvalue X i j k hij hik hjk n
        (fun q ↦ fineSign
          (oppositeConjugatedPlaneSuccIndex X i j k hij hik hjk x n q)) g =
      planeEigenvalue X i j k hij hik hjk (n + 1) fineSign
        (oppositeConjugatedPlaneSucc X i j k hij hik hjk x n g) := by
  unfold planeEigenvalue oppositeConjugatedPlaneSuccIndex
  simp only [Equiv.apply_symm_apply]

/-- The finite set of sign components on which a selected plane element has
eigenvalue `-1`. -/
noncomputable def negativePlaneSignSet
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (g : Plane X i j k hij hik hjk n) :
    Finset (Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool) :=
  Finset.univ.filter fun sign ↦
    planeEigenvalue X i j k hij hik hjk n sign g = -1

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

/-- The negative spectral projection for any finite-plane element has squared
norm exactly equal to the total mass of the components on which that element
has character value `-1`. -/
theorem norm_negativePart_sq_eq_planeCharacterMass
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (g : Plane X i j k hij hik hjk n) :
    ‖InvolutionSplitting.negativePart rho g.1 z‖ ^ 2 =
      ∑ sign ∈ negativePlaneSignSet X i j k hij hik hjk n g,
        ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2 := by
  let q := (planeEnumeration X i j k hij hik hjk n).symm g
  have hq : planeFamily X i j k hij hik hjk n q = g.1 := by
    exact congrArg Subtype.val
      ((planeEnumeration X i j k hij hik hjk n).apply_symm_apply g)
  rw [← hq]
  have hmass := norm_negativePart_sq_eq_sum_false rho _
    (planeFamily X i j k hij hik hjk n)
    (planeFamily_sq X i j k hij hik hjk n)
    (planeFamily_pairwise_commute X i j k hij hik hjk n) z q
  rw [hmass]
  apply Finset.sum_congr
  · ext sign
    simp only [negativePlaneSignSet, Finset.mem_filter,
      Finset.mem_univ, true_and]
    simp only [planeEigenvalue, q]
    cases sign ((planeEnumeration X i j k hij hik hjk n).symm g) <;> norm_num
  · intro sign _
    rfl

/-- Equivalently, the total mass of the characters detecting a plane element
is one quarter of that element's squared displacement. -/
theorem planeCharacterMass_eq_quarter_displacement
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) (g : Plane X i j k hij hik hjk n) :
    (∑ sign ∈ negativePlaneSignSet X i j k hij hik hjk n g,
        ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2) =
      (4 : ℝ)⁻¹ * ‖rho g.1 z - z‖ ^ 2 := by
  calc
    (∑ sign ∈ negativePlaneSignSet X i j k hij hik hjk n g,
        ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2) =
        ‖InvolutionSplitting.negativePart rho g.1 z‖ ^ 2 :=
      (norm_negativePart_sq_eq_planeCharacterMass
        X i j k hij hik hjk n rho z g).symm
    _ = (4 : ℝ)⁻¹ * ‖rho g.1 z - z‖ ^ 2 :=
      InvolutionSplitting.norm_negativePart_sq rho g.1 z

/-- Quantitative character-mass transport under one free-generator shear. The
mass of the sheared next-stage character event differs from the original pure
second-coordinate event only by the displacement of the vector under that
single elementary generator. -/
theorem abs_generatorShearedSecondCharacterMass_sub_le
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : X) (n : ℕ) (b : FreeAlgebraDegree.degreeLE X n)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    |(∑ sign ∈ negativePlaneSignSet X i j k hij hik hjk (n + 1)
          (generatorShearedSecondCoordinate X i j k hij hik hjk x n b),
        ‖planeComponent X i j k hij hik hjk (n + 1) rho sign z‖ ^ 2) -
      (∑ sign ∈ negativePlaneSignSet X i j k hij hik hjk n
          (secondCoordinate X i j k hij hik hjk n b),
        ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2)| ≤
      2 * ‖z‖ *
        ‖z - rho (elementaryRoot i j hij (FreeAlgebra.ι (ZMod 2) x)) z‖ := by
  rw [← norm_negativePart_sq_eq_planeCharacterMass X i j k hij hik hjk
      (n + 1) rho z
      (generatorShearedSecondCoordinate X i j k hij hik hjk x n b),
    ← norm_negativePart_sq_eq_planeCharacterMass X i j k hij hik hjk n rho z
      (secondCoordinate X i j k hij hik hjk n b)]
  have hc : (secondCoordinate X i j k hij hik hjk n b).1 ^ 2 = 1 :=
    rootPlaneDegreeSubgroup_sq X i j k hij hik hjk n _
      (secondCoordinate X i j k hij hik hjk n b).2
  have htransport :=
    InvolutionSplitting.abs_norm_negativePart_conjugate_sq_sub_le rho
      (elementaryRoot i j hij (FreeAlgebra.ι (ZMod 2) x)) hc z
  rw [conjugate_secondCoordinate_generator X i j k hij hik hjk x n b]
    at htransport
  exact htransport

/-- The symmetric character-mass transport estimate for the opposite shear.
It compares the next-stage sheared first-coordinate event with the original
pure first-coordinate event. -/
theorem abs_generatorShearedFirstCharacterMass_sub_le
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : X) (n : ℕ) (a : FreeAlgebraDegree.degreeLE X n)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) :
    |(∑ sign ∈ negativePlaneSignSet X i j k hij hik hjk (n + 1)
          (generatorShearedFirstCoordinate X i j k hij hik hjk x n a),
        ‖planeComponent X i j k hij hik hjk (n + 1) rho sign z‖ ^ 2) -
      (∑ sign ∈ negativePlaneSignSet X i j k hij hik hjk n
          (firstCoordinate X i j k hij hik hjk n a),
        ‖planeComponent X i j k hij hik hjk n rho sign z‖ ^ 2)| ≤
      2 * ‖z‖ *
        ‖z - rho (elementaryRoot j i hij.symm
          (FreeAlgebra.ι (ZMod 2) x)) z‖ := by
  rw [← norm_negativePart_sq_eq_planeCharacterMass X i j k hij hik hjk
      (n + 1) rho z
      (generatorShearedFirstCoordinate X i j k hij hik hjk x n a),
    ← norm_negativePart_sq_eq_planeCharacterMass X i j k hij hik hjk n rho z
      (firstCoordinate X i j k hij hik hjk n a)]
  have hc : (firstCoordinate X i j k hij hik hjk n a).1 ^ 2 = 1 :=
    rootPlaneDegreeSubgroup_sq X i j k hij hik hjk n _
      (firstCoordinate X i j k hij hik hjk n a).2
  have htransport :=
    InvolutionSplitting.abs_norm_negativePart_conjugate_sq_sub_le rho
      (elementaryRoot j i hij.symm (FreeAlgebra.ι (ZMod 2) x)) hc z
  rw [conjugate_firstCoordinate_opposite_generator
      X i j k hij hik hjk x n a] at htransport
  exact htransport

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

/-- A nontrivial additive sign character on a degree stage is detected by a
basis word in the support of any coefficient on which it is nontrivial.  This
is the exact bridge from arbitrary free polynomials to the word-by-word shear
argument. -/
theorem exists_supported_word_of_additive_sign_character
    {n : ℕ} (chi : FreeAlgebraDegree.degreeLE X n → ℝ)
    (hzero : chi 0 = 1)
    (hadd : ∀ a b, chi (a + b) = chi a * chi b)
    (hsign : ∀ a, chi a = 1 ∨ chi a = -1)
    (p : FreeAlgebraDegree.degreeLE X n) (hp : chi p = -1) :
    ∃ (w : FreeMonoid X)
      (hw : w ∈ (FreeAlgebra.equivMonoidAlgebraFreeMonoid
        (R := ZMod 2) (X := X) p.1).coeff.support),
      chi ⟨FreeAlgebraDegree.wordMonomial X w,
        FreeAlgebraDegree.wordMonomial_mem_degreeLE X
          (((FreeAlgebraDegree.mem_degreeLE_iff X p.1 n).1 p.2) w hw)⟩ =
        -1 := by
  classical
  let q := (FreeAlgebra.equivMonoidAlgebraFreeMonoid
    (R := ZMod 2) (X := X) p.1).coeff
  let term : {w // w ∈ q.support} →
      FreeAlgebraDegree.degreeLE X n := fun w ↦
    ⟨FreeAlgebraDegree.wordMonomial X w.1,
      FreeAlgebraDegree.wordMonomial_mem_degreeLE X
        (((FreeAlgebraDegree.mem_degreeLE_iff X p.1 n).1 p.2) w.1 w.2)⟩
  have hpsum : p = ∑ w, term w :=
    FreeAlgebraDegree.eq_sum_support_degreeWordMonomial X p
  by_contra hnone
  have hnone' : ∀ (w : FreeMonoid X)
      (hw : w ∈ (FreeAlgebra.equivMonoidAlgebraFreeMonoid
        (R := ZMod 2) (X := X) p.1).coeff.support),
      chi ⟨FreeAlgebraDegree.wordMonomial X w,
        FreeAlgebraDegree.wordMonomial_mem_degreeLE X
          (((FreeAlgebraDegree.mem_degreeLE_iff X p.1 n).1 p.2) w hw)⟩ ≠
        -1 := by
    intro w hw hneg
    exact hnone ⟨w, hw, hneg⟩
  have hterm : ∀ w, chi (term w) = 1 := by
    intro w
    rcases hsign (term w) with hw | hw
    · exact hw
    · exact False.elim (hnone' w.1 w.2 hw)
  have hmap : ∀ s : Finset {w // w ∈ q.support},
      chi (∑ w ∈ s, term w) = ∏ w ∈ s, chi (term w) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | @insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.prod_insert ha, hadd, ih]
  have htotal : chi (∑ w, term w) = ∏ w, chi (term w) := by
    simpa using hmap Finset.univ
  have hbad : (-1 : ℝ) = 1 := by
    calc
      (-1 : ℝ) = chi p := hp.symm
      _ = chi (∑ w, term w) := congrArg chi hpsum
      _ = ∏ w, chi (term w) := htotal
      _ = 1 := by simp [hterm]
  norm_num at hbad

/-- The first coefficient character is always sign-valued. -/
theorem firstCoefficientEigenvalue_eq_one_or_neg_one
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool)
    (a : FreeAlgebraDegree.degreeLE X n) :
    firstCoefficientEigenvalue X i j k hij hik hjk n sign a = 1 ∨
      firstCoefficientEigenvalue X i j k hij hik hjk n sign a = -1 := by
  unfold firstCoefficientEigenvalue planeEigenvalue
  split <;> simp

/-- The second coefficient character is always sign-valued. -/
theorem secondCoefficientEigenvalue_eq_one_or_neg_one
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool)
    (a : FreeAlgebraDegree.degreeLE X n) :
    secondCoefficientEigenvalue X i j k hij hik hjk n sign a = 1 ∨
      secondCoefficientEigenvalue X i j k hij hik hjk n sign a = -1 := by
  unfold secondCoefficientEigenvalue planeEigenvalue
  split <;> simp

/-- Nontriviality of the first coefficient character is witnessed on a
supported free word. -/
theorem exists_supported_word_of_firstCoefficientEigenvalue_eq_neg_one
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool)
    (z : E)
    (hv : planeComponent X i j k hij hik hjk n rho sign z ≠ 0)
    (a : FreeAlgebraDegree.degreeLE X n)
    (ha : firstCoefficientEigenvalue X i j k hij hik hjk n sign a = -1) :
    ∃ (w : FreeMonoid X)
      (hw : w ∈ (FreeAlgebra.equivMonoidAlgebraFreeMonoid
        (R := ZMod 2) (X := X) a.1).coeff.support),
      firstCoefficientEigenvalue X i j k hij hik hjk n sign
        ⟨FreeAlgebraDegree.wordMonomial X w,
          FreeAlgebraDegree.wordMonomial_mem_degreeLE X
            (((FreeAlgebraDegree.mem_degreeLE_iff X a.1 n).1 a.2) w hw)⟩ =
        -1 := by
  exact exists_supported_word_of_additive_sign_character X
    (firstCoefficientEigenvalue X i j k hij hik hjk n sign)
    (firstCoefficientEigenvalue_zero_of_component_ne_zero X i j k hij hik hjk n
      rho sign z hv)
    (firstCoefficientEigenvalue_add_of_component_ne_zero X i j k hij hik hjk n
      rho sign z hv)
    (firstCoefficientEigenvalue_eq_one_or_neg_one X i j k hij hik hjk n sign)
    a ha

/-- Nontriviality of the second coefficient character is witnessed on a
supported free word. -/
theorem exists_supported_word_of_secondCoefficientEigenvalue_eq_neg_one
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool)
    (z : E)
    (hv : planeComponent X i j k hij hik hjk n rho sign z ≠ 0)
    (a : FreeAlgebraDegree.degreeLE X n)
    (ha : secondCoefficientEigenvalue X i j k hij hik hjk n sign a = -1) :
    ∃ (w : FreeMonoid X)
      (hw : w ∈ (FreeAlgebra.equivMonoidAlgebraFreeMonoid
        (R := ZMod 2) (X := X) a.1).coeff.support),
      secondCoefficientEigenvalue X i j k hij hik hjk n sign
        ⟨FreeAlgebraDegree.wordMonomial X w,
          FreeAlgebraDegree.wordMonomial_mem_degreeLE X
            (((FreeAlgebraDegree.mem_degreeLE_iff X a.1 n).1 a.2) w hw)⟩ =
        -1 := by
  exact exists_supported_word_of_additive_sign_character X
    (secondCoefficientEigenvalue X i j k hij hik hjk n sign)
    (secondCoefficientEigenvalue_zero_of_component_ne_zero X i j k hij hik hjk n
      rho sign z hv)
    (secondCoefficientEigenvalue_add_of_component_ne_zero X i j k hij hik hjk n
      rho sign z hv)
    (secondCoefficientEigenvalue_eq_one_or_neg_one X i j k hij hik hjk n sign)
    a ha

/-- If a nonzero component has a nontrivial plane character, then one of its
two coefficient characters is already nontrivial. -/
theorem exists_nontrivial_coefficient_of_planeEigenvalue_eq_neg_one
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool)
    (z : E)
    (hv : planeComponent X i j k hij hik hjk n rho sign z ≠ 0)
    (g : Plane X i j k hij hik hjk n)
    (hg : planeEigenvalue X i j k hij hik hjk n sign g = -1) :
    (∃ a : FreeAlgebraDegree.degreeLE X n,
      firstCoefficientEigenvalue X i j k hij hik hjk n sign a = -1) ∨
    (∃ b : FreeAlgebraDegree.degreeLE X n,
      secondCoefficientEigenvalue X i j k hij hik hjk n sign b = -1) := by
  obtain ⟨a, b, hab⟩ := exists_coordinate_factorization X i j k hij hik hjk n g
  have hmul := planeEigenvalue_mul_of_component_ne_zero X i j k hij hik hjk n
    rho sign z hv
    (firstCoordinate X i j k hij hik hjk n a)
    (secondCoordinate X i j k hij hik hjk n b)
  rw [hab, hg] at hmul
  change (-1 : ℝ) =
    firstCoefficientEigenvalue X i j k hij hik hjk n sign a *
      secondCoefficientEigenvalue X i j k hij hik hjk n sign b at hmul
  have ha : firstCoefficientEigenvalue X i j k hij hik hjk n sign a = 1 ∨
      firstCoefficientEigenvalue X i j k hij hik hjk n sign a = -1 := by
    unfold firstCoefficientEigenvalue planeEigenvalue
    split <;> simp
  have hb : secondCoefficientEigenvalue X i j k hij hik hjk n sign b = 1 ∨
      secondCoefficientEigenvalue X i j k hij hik hjk n sign b = -1 := by
    unfold secondCoefficientEigenvalue planeEigenvalue
    split <;> simp
  rcases ha with ha | ha
  · right
    refine ⟨b, ?_⟩
    rcases hb with hb | hb
    · rw [ha, hb] at hmul
      norm_num at hmul
    · exact hb
  · exact Or.inl ⟨a, ha⟩

/-- A nontrivial plane character on a nonzero Fourier component is detected
on a single degree-bounded word monomial in one of the two root
coordinates. -/
theorem exists_word_coordinate_of_planeEigenvalue_eq_neg_one
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (n : ℕ)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (sign : Fin (Nat.card (Plane X i j k hij hik hjk n)) → Bool)
    (z : E)
    (hv : planeComponent X i j k hij hik hjk n rho sign z ≠ 0)
    (g : Plane X i j k hij hik hjk n)
    (hg : planeEigenvalue X i j k hij hik hjk n sign g = -1) :
    (∃ (w : FreeMonoid X)
      (hw : FreeAlgebraDegree.freeWordLength X w ≤ n),
      firstCoefficientEigenvalue X i j k hij hik hjk n sign
        ⟨FreeAlgebraDegree.wordMonomial X w,
          FreeAlgebraDegree.wordMonomial_mem_degreeLE X hw⟩ =
        -1) ∨
    (∃ (w : FreeMonoid X)
      (hw : FreeAlgebraDegree.freeWordLength X w ≤ n),
      secondCoefficientEigenvalue X i j k hij hik hjk n sign
        ⟨FreeAlgebraDegree.wordMonomial X w,
          FreeAlgebraDegree.wordMonomial_mem_degreeLE X hw⟩ =
        -1) := by
  rcases exists_nontrivial_coefficient_of_planeEigenvalue_eq_neg_one
      X i j k hij hik hjk n rho sign z hv g hg with ⟨a, ha⟩ | ⟨b, hb⟩
  · left
    obtain ⟨w, hw, hword⟩ :=
      exists_supported_word_of_firstCoefficientEigenvalue_eq_neg_one
        X i j k hij hik hjk n rho sign z hv a ha
    have hdegree :=
      ((FreeAlgebraDegree.mem_degreeLE_iff X a.1 n).1 a.2) w hw
    exact ⟨w, hdegree, hword⟩
  · right
    obtain ⟨w, hw, hword⟩ :=
      exists_supported_word_of_secondCoefficientEigenvalue_eq_neg_one
        X i j k hij hik hjk n rho sign z hv b hb
    have hdegree :=
      ((FreeAlgebraDegree.mem_degreeLE_iff X b.1 n).1 b.2) w hw
    exact ⟨w, hdegree, hword⟩

end

end FreeRootPlaneFourier

end NonsoficGroupsExist
