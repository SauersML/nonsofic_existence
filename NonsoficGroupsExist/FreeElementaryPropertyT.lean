import NonsoficGroupsExist.A2MagicHilbert
import NonsoficGroupsExist.ClassTwoNormalForm
import NonsoficGroupsExist.FreeRootCharacterValuation
import NonsoficGroupsExist.KazhdanControl
import Mathlib.Algebra.CharP.Algebra

/-!
# Property `(T)` for elementary groups over finite free characteristic-two rings

This module turns the limiting two-root Fourier estimate into a finite
Kazhdan pair.  The control set consists of the unit and every free generator
in each of the six elementary roots.
-/

namespace NonsoficGroupsExist
namespace FreeElementaryPropertyT

open FreeRootCharacterValuation
open FreeAlgebraDegree
open FreeRootFiltration
open scoped commutatorElement

noncomputable section

variable (X : Type*) [Fintype X]

omit [Fintype X] in
/-- An adjacent elementary root normalizes the plane formed by the two roots
with a common terminal index. -/
theorem elementaryRoot_mem_normalizer_columnPlane
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (a : FreeRing X) :
    elementaryRoot i j hij a ∈ Subgroup.normalizer
      (elementaryRootSubgroup i k hik ⊔
        elementaryRootSubgroup j k hjk :
          Subgroup (elementaryGroup (Fin 3) (FreeRing X))) := by
  let A := elementaryA2System (FreeRing X)
  let Xij : Subgroup (elementaryGroup (Fin 3) (FreeRing X)) :=
    elementaryRootSubgroup i j hij
  let Xjk : Subgroup (elementaryGroup (Fin 3) (FreeRing X)) :=
    elementaryRootSubgroup j k hjk
  let Xik : Subgroup (elementaryGroup (Fin 3) (FreeRing X)) :=
    elementaryRootSubgroup i k hik
  have hYX : ⁅Xij, Xjk⁆ ≤ Xik := by
    apply Subgroup.commutator_le.mpr
    intro x hx y hy
    exact A.commutator_mem i j k hij hjk hik x hx y hy
  have hYZ : ⁅Xij, Xik⁆ ≤ Xik := by
    apply Subgroup.commutator_le.mpr
    intro x hx y hy
    have hcomm : Commute x y :=
      A.commute i j i k hij hik hij.symm hik.symm x hx y hy
    rw [commutatorElement_eq_one_iff_commute.mpr hcomm]
    exact Xik.one_mem
  have hnormal : Xij ≤ Subgroup.normalizer (Xjk ⊔ Xik :
      Subgroup (elementaryGroup (Fin 3) (FreeRing X))) :=
    ClassTwoNormalForm.le_normalizer_sup Xjk Xij Xik hYX hYZ
  have hmem : elementaryRoot i j hij a ∈ Xij := ⟨a, rfl⟩
  simpa only [sup_comm] using hnormal hmem

/-- Coefficients used by the finite elementary control set. -/
noncomputable def controlCoefficient
    (q : Option (Fin (Fintype.card X))) : FreeRing X :=
  match q with
  | none => 1
  | some q => FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q)

/-- One member of the finite elementary control set. -/
noncomputable def controlElement
    (p : A2Root × Option (Fin (Fintype.card X))) :
    elementaryGroup (Fin 3) (FreeRing X) :=
  elementaryRoot p.1.1.1 p.1.1.2 p.1.2 (controlCoefficient X p.2)

/-- Unit and free-generator coefficients in every ordered elementary root. -/
noncomputable def controlSet :
    Finset (elementaryGroup (Fin 3) (FreeRing X)) := by
  classical
  exact (Finset.univ : Finset
    (A2Root × Option (Fin (Fintype.card X)))).image (controlElement X)

theorem controlElement_mem
    (p : A2Root × Option (Fin (Fintype.card X))) :
    controlElement X p ∈ controlSet X := by
  classical
  exact Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩

/-- The finite control set bounds the moving projection for either of the two
roots in a common-terminal-index plane. -/
theorem norm_columnPlaneMovingProjection_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeRing X) →* (E ≃ₗᵢ[ℝ] E))
    (z : E) {δ : ℝ} (hδ : 0 < δ)
    (hnear : ∀ s ∈ controlSet X, ‖rho s z - z‖ < δ) :
    ‖KazhdanFixedSpace.subgroupMovingProjection rho
        (elementaryRootSubgroup i k hik ⊔
          elementaryRootSubgroup j k hjk) z‖ ≤
      (6 * Fintype.card X + 6 : ℝ) * δ := by
  classical
  let H : Subgroup (elementaryGroup (Fin 3) (FreeRing X)) :=
    elementaryRootSubgroup i k hik ⊔ elementaryRootSubgroup j k hjk
  let w := KazhdanFixedSpace.subgroupMovingProjection rho H z
  have hnearControl (a : A2Root) (q : Option (Fin (Fintype.card X))) :
      ‖rho (controlElement X (a, q)) z - z‖ < δ :=
    hnear _ (controlElement_mem X (a, q))
  have hnormalIJ (a : FreeRing X) :
      elementaryRoot i j hij a ∈ Subgroup.normalizer H := by
    exact elementaryRoot_mem_normalizer_columnPlane X i j k hij hik hjk a
  have hnormalJI (a : FreeRing X) :
      elementaryRoot j i hij.symm a ∈ Subgroup.normalizer H := by
    simpa only [H, sup_comm] using
      elementaryRoot_mem_normalizer_columnPlane X j i k hij.symm hjk hik a
  have hnormalIK (a : FreeRing X) :
      elementaryRoot i k hik a ∈ Subgroup.normalizer H := by
    apply H.le_normalizer
    exact (show elementaryRootSubgroup i k hik ≤ H from le_sup_left) ⟨a, rfl⟩
  have hnormalJK (a : FreeRing X) :
      elementaryRoot j k hjk a ∈ Subgroup.normalizer H := by
    apply H.le_normalizer
    exact (show elementaryRootSubgroup j k hjk ≤ H from le_sup_right) ⟨a, rfl⟩
  have hmove_le (g : elementaryGroup (Fin 3) (FreeRing X))
      (hg : g ∈ Subgroup.normalizer H) :
      ‖rho g w - w‖ ≤ ‖rho g z - z‖ := by
    exact
      KazhdanFixedSpace.norm_subgroupMovingProjection_displacement_le_of_mem_normalizer
        rho H hg z
  have hwIK : ‖rho (elementaryRoot i k hik 1) w - w‖ ≤ δ :=
    (hmove_le _ (hnormalIK 1)).trans
      (hnearControl ⟨(i, k), hik⟩ none).le
  have hwJK : ‖rho (elementaryRoot j k hjk 1) w - w‖ ≤ δ :=
    (hmove_le _ (hnormalJK 1)).trans
      (hnearControl ⟨(j, k), hjk⟩ none).le
  have hwIJUnit : ‖rho (elementaryRoot i j hij 1) w - w‖ ≤ δ :=
    (hmove_le _ (hnormalIJ 1)).trans
      (hnearControl ⟨(i, j), hij⟩ none).le
  have hwJIUnit : ‖rho (elementaryRoot j i hij.symm 1) w - w‖ ≤ δ :=
    (hmove_le _ (hnormalJI 1)).trans
      (hnearControl ⟨(j, i), hij.symm⟩ none).le
  have hwIJ (q : Fin (Fintype.card X)) :
      ‖rho (elementaryRoot i j hij
        (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) w - w‖ ≤ δ :=
    (hmove_le _ (hnormalIJ _)).trans
      (hnearControl ⟨(i, j), hij⟩ (some q)).le
  have hwJI (q : Fin (Fintype.card X)) :
      ‖rho (elementaryRoot j i hij.symm
        (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) w - w‖ ≤ δ :=
    (hmove_le _ (hnormalJI _)).trans
      (hnearControl ⟨(j, i), hij.symm⟩ (some q)).le
  have hsumIJ :
      (∑ q : Fin (Fintype.card X),
          2 * ‖w‖ * ‖rho (elementaryRoot i j hij
            (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) w - w‖) ≤
        Fintype.card X * (2 * ‖w‖ * δ) := by
    calc
      _ ≤ ∑ _q : Fin (Fintype.card X), 2 * ‖w‖ * δ := by
        apply Finset.sum_le_sum
        intro q _
        exact mul_le_mul_of_nonneg_left (hwIJ q)
          (mul_nonneg (by norm_num) (norm_nonneg w))
      _ = Fintype.card X * (2 * ‖w‖ * δ) := by simp
  have hsumJI :
      (∑ q : Fin (Fintype.card X),
          2 * ‖w‖ * ‖rho (elementaryRoot j i hij.symm
            (FreeAlgebra.ι (ZMod 2) (generatorEnumeration X q))) w - w‖) ≤
        Fintype.card X * (2 * ‖w‖ * δ) := by
    calc
      _ ≤ ∑ _q : Fin (Fintype.card X), 2 * ‖w‖ * δ := by
        apply Finset.sum_le_sum
        intro q _
        exact mul_le_mul_of_nonneg_left (hwJI q)
          (mul_nonneg (by norm_num) (norm_nonneg w))
      _ = Fintype.card X * (2 * ‖w‖ * δ) := by simp
  have hwProjection :
      KazhdanFixedSpace.subgroupMovingProjection rho H w = w := by
    let U := KazhdanFixedSpace.fixedSubspace rho H
    letI : CompleteSpace U :=
      (KazhdanFixedSpace.isClosed_fixedSubspace rho H).completeSpace_coe
    change Uᗮ.starProjection w = w
    exact Uᗮ.starProjection_eq_self_iff.mpr
      (KazhdanFixedSpace.subgroupMovingProjection_mem rho H z)
  have hestimate :=
    norm_joinRootMovingProjection_sq_le_explicit_errors
      X i j k hij hik hjk rho w
  change ‖KazhdanFixedSpace.subgroupMovingProjection rho H w‖ ^ 2 ≤ _ at hestimate
  rw [hwProjection] at hestimate
  have hwIKsq :
      ‖rho (elementaryRoot i k hik 1) w - w‖ ^ 2 ≤ δ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hδ.le).2 hwIK
  have hwJKsq :
      ‖rho (elementaryRoot j k hjk 1) w - w‖ ^ 2 ≤ δ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hδ.le).2 hwJK
  have hwIJUnitTerm :
      2 * ‖w‖ * ‖rho (elementaryRoot i j hij 1) w - w‖ ≤
        2 * ‖w‖ * δ :=
    mul_le_mul_of_nonneg_left hwIJUnit
      (mul_nonneg (by norm_num) (norm_nonneg w))
  have hwJIUnitTerm :
      2 * ‖w‖ * ‖rho (elementaryRoot j i hij.symm 1) w - w‖ ≤
        2 * ‖w‖ * δ :=
    mul_le_mul_of_nonneg_left hwJIUnit
      (mul_nonneg (by norm_num) (norm_nonneg w))
  have hquadratic :
      ‖w‖ ^ 2 ≤ 2 * δ ^ 2 +
        (6 * Fintype.card X + 4 : ℝ) * ‖w‖ * δ := by
    have hcard : (0 : ℝ) ≤ Fintype.card X := by positivity
    nlinarith
  change ‖w‖ ≤ (6 * Fintype.card X + 6 : ℝ) * δ
  have hC : (1 : ℝ) ≤ 6 * Fintype.card X + 6 := by
    have hcard : (0 : ℝ) ≤ Fintype.card X := by positivity
    linarith
  by_cases hwδ : ‖w‖ ≤ δ
  · exact hwδ.trans (le_mul_of_one_le_left hδ.le hC)
  · have hδw : δ ≤ ‖w‖ := le_of_lt (lt_of_not_ge hwδ)
    have hw0 : 0 ≤ ‖w‖ := norm_nonneg w
    have hδ0 : 0 ≤ δ := hδ.le
    have hcard : (0 : ℝ) ≤ Fintype.card X := by positivity
    nlinarith

/-- The finite elementary control set uniformly controls displacement by the
union of all six root subgroups. -/
theorem controlSet_controls_rootSet :
    ControlsSubsetDisplacement
      (elementaryGroup (Fin 3) (FreeRing X))
      (controlSet X) (elementaryA2System (FreeRing X)).rootSet
      (12 * Fintype.card X + 13 : ℝ) := by
  intro E _ _ _ rho z _hz δ hδ hnear g hg
  obtain ⟨a, hga⟩ :=
    ((elementaryA2System (FreeRing X)).mem_rootSet_iff g).mp hg
  let i := a.1.1
  let k := a.1.2
  let j := a2ThirdIndex i k
  have hij : i ≠ j := (a2ThirdIndex_ne_left i k a.2).symm
  have hjk : j ≠ k := a2ThirdIndex_ne_right i k a.2
  let H : Subgroup (elementaryGroup (Fin 3) (FreeRing X)) :=
    elementaryRootSubgroup i k a.2 ⊔ elementaryRootSubgroup j k hjk
  have hprojection := norm_columnPlaneMovingProjection_le
    X i j k hij a.2 hjk rho z hδ hnear
  have hgH : g ∈ H := by
    exact (show elementaryRootSubgroup i k a.2 ≤ H from le_sup_left) hga
  have hdisplacement :=
    KazhdanFixedSpace.norm_displacement_le_two_mul_norm_subgroupMovingProjection_of_mem
      rho H hgH z
  calc
    ‖rho g z - z‖ ≤
        2 * ‖KazhdanFixedSpace.subgroupMovingProjection rho H z‖ :=
      hdisplacement
    _ ≤ 2 * ((6 * Fintype.card X + 6 : ℝ) * δ) := by
      exact mul_le_mul_of_nonneg_left hprojection (by norm_num)
    _ < (12 * Fintype.card X + 13 : ℝ) * δ := by
      have hcard : (0 : ℝ) ≤ Fintype.card X := by positivity
      nlinarith

/-- The explicit control set is a genuine finite Kazhdan pair. -/
theorem controlSet_isKazhdanPair :
    ∃ epsilon : ℝ,
      IsKazhdanPair (elementaryGroup (Fin 3) (FreeRing X))
        (controlSet X) epsilon := by
  obtain ⟨kappa, hkappa⟩ :=
    A2MagicHilbert.elementary_exists_rootSet_isKazhdan (FreeRing X) 2
      (by omega)
  let C : ℝ := 12 * Fintype.card X + 13
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  exact ⟨kappa / (2 * C),
    IsKazhdanSubset.to_pair_of_controls hkappa hC
      (controlSet_controls_rootSet X)⟩

/-- Elementary rank three over the finite free characteristic-two algebra has
Kazhdan's property `(T)`. -/
theorem freeElementary_hasKazhdanPropertyT :
    HasKazhdanPropertyT (elementaryGroup (Fin 3) (FreeRing X)) := by
  obtain ⟨epsilon, hpair⟩ := controlSet_isKazhdanPair X
  exact ⟨controlSet X, epsilon, hpair⟩

end
end FreeElementaryPropertyT
end NonsoficGroupsExist
