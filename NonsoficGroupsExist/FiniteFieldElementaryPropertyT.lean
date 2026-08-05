import NonsoficGroupsExist.A2MagicHilbert
import NonsoficGroupsExist.ClassTwoNormalForm
import NonsoficGroupsExist.FreeRootPlaneMass
import NonsoficGroupsExist.KazhdanControl

/-!
# Property `(T)` for elementary groups over finite free algebras

This module turns the limiting two-root moving-mass bound into a finite
Kazhdan pair over **every** finite coefficient field.  The control set
consists of every scalar multiple of the unit and every free generator, in
each of the six elementary roots.
-/

namespace NonsoficGroupsExist
namespace FiniteFieldElementaryPropertyT

open FreeRootPlaneMass
open FreeAlgebraDegree
open FreeRootFunctionalValuation
open scoped commutatorElement

noncomputable section

variable (X : Type*) [Fintype X]
variable (K : Type*) [Field K] [Fintype K]

omit [Fintype X] [Field K] [Fintype K] in
/-- An adjacent elementary root normalizes the plane formed by the two
roots with a common terminal index, over any coefficient ring. -/
theorem elementaryRoot_mem_normalizer_columnPlane
    {R : Type*} [Ring R]
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (a : R) :
    elementaryRoot i j hij a ∈ Subgroup.normalizer
      (elementaryRootSubgroup i k hik ⊔
        elementaryRootSubgroup j k hjk :
          Subgroup (elementaryGroup (Fin 3) R)) := by
  let A := elementaryA2System R
  let Xij : Subgroup (elementaryGroup (Fin 3) R) :=
    elementaryRootSubgroup i j hij
  let Xjk : Subgroup (elementaryGroup (Fin 3) R) :=
    elementaryRootSubgroup j k hjk
  let Xik : Subgroup (elementaryGroup (Fin 3) R) :=
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
      Subgroup (elementaryGroup (Fin 3) R)) :=
    ClassTwoNormalForm.le_normalizer_sup Xjk Xij Xik hYX hYZ
  have hmem : elementaryRoot i j hij a ∈ Xij := ⟨a, rfl⟩
  simpa only [sup_comm] using hnormal hmem

/-- Coefficients used by the finite elementary control set: every scalar
multiple of the unit, and every free generator. -/
def controlCoefficient (c : K ⊕ Fin (Fintype.card X)) : FreeAlgebra K X :=
  match c with
  | Sum.inl t => t • (1 : FreeAlgebra K X)
  | Sum.inr q => FreeAlgebra.ι K (generatorEnumeration X q)

/-- One member of the finite elementary control set. -/
def controlElement (p : A2Root × (K ⊕ Fin (Fintype.card X))) :
    elementaryGroup (Fin 3) (FreeAlgebra K X) :=
  elementaryRoot p.1.1.1 p.1.1.2 p.1.2 (controlCoefficient X K p.2)

/-- Scalar-unit and free-generator coefficients in every ordered
elementary root. -/
def controlSet : Finset (elementaryGroup (Fin 3) (FreeAlgebra K X)) := by
  classical
  exact (Finset.univ : Finset
    (A2Root × (K ⊕ Fin (Fintype.card X)))).image (controlElement X K)

theorem controlElement_mem (p : A2Root × (K ⊕ Fin (Fintype.card X))) :
    controlElement X K p ∈ controlSet X K := by
  classical
  exact Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩

/-- The finite control set bounds the moving projection for either of the
two roots in a common-terminal-index plane, at the character gap of any
nontrivial additive character. -/
theorem norm_columnPlaneMovingProjection_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (rho : elementaryGroup (Fin 3) (FreeAlgebra K X) →* (E ≃ₗᵢ[ℝ] E))
    (ψ : AddChar K ℂ) (hψ : ψ ≠ 1)
    (z : E) {δ : ℝ} (hδ : 0 < δ)
    (hnear : ∀ s ∈ controlSet X K, ‖rho s z - z‖ < δ) :
    ‖KazhdanFixedSpace.subgroupMovingProjection rho
        (elementaryRootSubgroup i k hik ⊔
          elementaryRootSubgroup j k hjk) z‖ ≤
      (8 * (CharacterMass.gap ψ)⁻¹ * Fintype.card K +
        6 * Fintype.card X + 4 : ℝ) * δ := by
  classical
  let H : Subgroup (elementaryGroup (Fin 3) (FreeAlgebra K X)) :=
    elementaryRootSubgroup i k hik ⊔ elementaryRootSubgroup j k hjk
  let w := KazhdanFixedSpace.subgroupMovingProjection rho H z
  have hnearControl : ∀ (a : A2Root) (c : K ⊕ Fin (Fintype.card X)),
      ‖rho (controlElement X K (a, c)) z - z‖ < δ :=
    fun a c ↦ hnear _ (controlElement_mem X K (a, c))
  have hnormalIJ : ∀ a : FreeAlgebra K X,
      elementaryRoot i j hij a ∈ Subgroup.normalizer H :=
    fun a ↦ elementaryRoot_mem_normalizer_columnPlane i j k hij hik hjk a
  have hnormalJI : ∀ a : FreeAlgebra K X,
      elementaryRoot j i hij.symm a ∈ Subgroup.normalizer H := by
    intro a
    simpa only [H, sup_comm] using
      elementaryRoot_mem_normalizer_columnPlane j i k hij.symm hjk hik a
  have hnormalIK : ∀ a : FreeAlgebra K X,
      elementaryRoot i k hik a ∈ Subgroup.normalizer H := by
    intro a
    apply H.le_normalizer
    exact (show elementaryRootSubgroup i k hik ≤ H from le_sup_left)
      ⟨a, rfl⟩
  have hnormalJK : ∀ a : FreeAlgebra K X,
      elementaryRoot j k hjk a ∈ Subgroup.normalizer H := by
    intro a
    apply H.le_normalizer
    exact (show elementaryRootSubgroup j k hjk ≤ H from le_sup_right)
      ⟨a, rfl⟩
  have hmove_le : ∀ g : elementaryGroup (Fin 3) (FreeAlgebra K X),
      g ∈ Subgroup.normalizer H →
        ‖rho g w - w‖ ≤ ‖rho g z - z‖ :=
    fun g hg ↦
      KazhdanFixedSpace.norm_subgroupMovingProjection_displacement_le_of_mem_normalizer
        rho H hg z
  have hwIK : ∀ t : K,
      ‖rho (elementaryRoot i k hik (t • (1 : FreeAlgebra K X))) w - w‖ ≤
        δ :=
    fun t ↦ (hmove_le _ (hnormalIK _)).trans
      (hnearControl ⟨(i, k), hik⟩ (Sum.inl t)).le
  have hwJK : ∀ t : K,
      ‖rho (elementaryRoot j k hjk (t • (1 : FreeAlgebra K X))) w - w‖ ≤
        δ :=
    fun t ↦ (hmove_le _ (hnormalJK _)).trans
      (hnearControl ⟨(j, k), hjk⟩ (Sum.inl t)).le
  have hwIJx : ∀ q : Fin (Fintype.card X),
      ‖rho (elementaryRoot i j hij
        (FreeAlgebra.ι K (generatorEnumeration X q))) w - w‖ ≤ δ :=
    fun q ↦ (hmove_le _ (hnormalIJ _)).trans
      (hnearControl ⟨(i, j), hij⟩ (Sum.inr q)).le
  have hwJIx : ∀ q : Fin (Fintype.card X),
      ‖rho (elementaryRoot j i hij.symm
        (FreeAlgebra.ι K (generatorEnumeration X q))) w - w‖ ≤ δ :=
    fun q ↦ (hmove_le _ (hnormalJI _)).trans
      (hnearControl ⟨(j, i), hij.symm⟩ (Sum.inr q)).le
  have hone : ((1 : K) • (1 : FreeAlgebra K X)) = 1 := one_smul _ _
  have hwIJ1 : ‖rho (elementaryRoot i j hij (1 : FreeAlgebra K X)) w -
      w‖ ≤ δ := by
    rw [← hone]
    exact (hmove_le _ (hnormalIJ _)).trans
      (hnearControl ⟨(i, j), hij⟩ (Sum.inl 1)).le
  have hwJI1 : ‖rho (elementaryRoot j i hij.symm
      (1 : FreeAlgebra K X)) w - w‖ ≤ δ := by
    rw [← hone]
    exact (hmove_le _ (hnormalJI _)).trans
      (hnearControl ⟨(j, i), hij.symm⟩ (Sum.inl 1)).le
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
      X K i j k hij hik hjk rho ψ hψ w
  change ‖KazhdanFixedSpace.subgroupMovingProjection rho H w‖ ^ 2 ≤ _
    at hestimate
  rw [hwProjection] at hestimate
  have hgap := CharacterMass.gap_pos ψ
  have hginv : (0 : ℝ) < (CharacterMass.gap ψ)⁻¹ := by positivity
  have hsumIK : (∑ t : K, ‖rho (elementaryRoot i k hik
      (t • (1 : FreeAlgebra K X))) w - w‖ ^ 2) ≤
      Fintype.card K * δ ^ 2 := by
    calc
      _ ≤ ∑ _t : K, δ ^ 2 :=
        Finset.sum_le_sum fun t _ ↦ by
          have := hwIK t
          nlinarith [norm_nonneg (rho (elementaryRoot i k hik
            (t • (1 : FreeAlgebra K X))) w - w)]
      _ = Fintype.card K * δ ^ 2 := by simp
  have hsumJK : (∑ t : K, ‖rho (elementaryRoot j k hjk
      (t • (1 : FreeAlgebra K X))) w - w‖ ^ 2) ≤
      Fintype.card K * δ ^ 2 := by
    calc
      _ ≤ ∑ _t : K, δ ^ 2 :=
        Finset.sum_le_sum fun t _ ↦ by
          have := hwJK t
          nlinarith [norm_nonneg (rho (elementaryRoot j k hjk
            (t • (1 : FreeAlgebra K X))) w - w)]
      _ = Fintype.card K * δ ^ 2 := by simp
  have hsumJIx : (∑ x : X, 2 * ‖w‖ *
      ‖rho (elementaryRoot j i hij.symm (FreeAlgebra.ι K x)) w - w‖) ≤
      Fintype.card X * (2 * ‖w‖ * δ) := by
    rw [show (∑ x : X, 2 * ‖w‖ *
        ‖rho (elementaryRoot j i hij.symm (FreeAlgebra.ι K x)) w - w‖) =
      ∑ q : Fin (Fintype.card X), 2 * ‖w‖ *
        ‖rho (elementaryRoot j i hij.symm
          (FreeAlgebra.ι K (generatorEnumeration X q))) w - w‖ from
      (Fintype.sum_equiv (generatorEnumeration X) _ _ fun q ↦ rfl).symm]
    calc
      _ ≤ ∑ _q : Fin (Fintype.card X), 2 * ‖w‖ * δ :=
        Finset.sum_le_sum fun q _ ↦
          mul_le_mul_of_nonneg_left (hwJIx q)
            (by positivity)
      _ = Fintype.card X * (2 * ‖w‖ * δ) := by simp
  have hsumIJx : (∑ x : X, 2 * ‖w‖ *
      ‖rho (elementaryRoot i j hij (FreeAlgebra.ι K x)) w - w‖) ≤
      Fintype.card X * (2 * ‖w‖ * δ) := by
    rw [show (∑ x : X, 2 * ‖w‖ *
        ‖rho (elementaryRoot i j hij (FreeAlgebra.ι K x)) w - w‖) =
      ∑ q : Fin (Fintype.card X), 2 * ‖w‖ *
        ‖rho (elementaryRoot i j hij
          (FreeAlgebra.ι K (generatorEnumeration X q))) w - w‖ from
      (Fintype.sum_equiv (generatorEnumeration X) _ _ fun q ↦ rfl).symm]
    calc
      _ ≤ ∑ _q : Fin (Fintype.card X), 2 * ‖w‖ * δ :=
        Finset.sum_le_sum fun q _ ↦
          mul_le_mul_of_nonneg_left (hwIJx q)
            (by positivity)
      _ = Fintype.card X * (2 * ‖w‖ * δ) := by simp
  have hunitJI : 2 * ‖w‖ * ‖rho (elementaryRoot j i hij.symm
      (1 : FreeAlgebra K X)) w - w‖ ≤ 2 * ‖w‖ * δ :=
    mul_le_mul_of_nonneg_left hwJI1 (by positivity)
  have hunitIJ : 2 * ‖w‖ * ‖rho (elementaryRoot i j hij
      (1 : FreeAlgebra K X)) w - w‖ ≤ 2 * ‖w‖ * δ :=
    mul_le_mul_of_nonneg_left hwIJ1 (by positivity)
  have hquadratic : ‖w‖ ^ 2 ≤
      8 * (CharacterMass.gap ψ)⁻¹ * Fintype.card K * δ ^ 2 +
        (6 * Fintype.card X + 4 : ℝ) * ‖w‖ * δ := by
    have hcardK : (0 : ℝ) ≤ Fintype.card K := by positivity
    have hcardX : (0 : ℝ) ≤ Fintype.card X := by positivity
    nlinarith [hestimate, hsumIK, hsumJK, hsumJIx, hsumIJx, hunitJI,
      hunitIJ, hginv]
  change ‖w‖ ≤ (8 * (CharacterMass.gap ψ)⁻¹ * Fintype.card K +
    6 * Fintype.card X + 4 : ℝ) * δ
  have hcardK1 : (1 : ℝ) ≤ Fintype.card K := by
    exact_mod_cast Fintype.card_pos
  have hcardX0 : (0 : ℝ) ≤ Fintype.card X := by positivity
  have hC1 : (1 : ℝ) ≤ 8 * (CharacterMass.gap ψ)⁻¹ * Fintype.card K +
      6 * Fintype.card X + 4 := by
    nlinarith [hginv]
  by_cases hwδ : ‖w‖ ≤ δ
  · exact hwδ.trans (le_mul_of_one_le_left hδ.le hC1)
  · have hδw : δ ≤ ‖w‖ := le_of_lt (lt_of_not_ge hwδ)
    have hwpos : 0 < ‖w‖ := lt_of_lt_of_le hδ hδw
    have hδsq : δ ^ 2 ≤ δ * ‖w‖ := by nlinarith
    have hfac : (0 : ℝ) ≤
        8 * (CharacterMass.gap ψ)⁻¹ * Fintype.card K := by positivity
    have hscaled := mul_le_mul_of_nonneg_left hδsq hfac
    have h2 : ‖w‖ * ‖w‖ ≤
        ((8 * (CharacterMass.gap ψ)⁻¹ * Fintype.card K +
          6 * Fintype.card X + 4 : ℝ) * δ) * ‖w‖ := by
      nlinarith [hquadratic]
    exact le_of_mul_le_mul_right h2 hwpos

/-- The finite elementary control set uniformly controls displacement by
the union of all six root subgroups. -/
theorem controlSet_controls_rootSet (ψ : AddChar K ℂ) (hψ : ψ ≠ 1) :
    ControlsSubsetDisplacement
      (elementaryGroup (Fin 3) (FreeAlgebra K X))
      (controlSet X K) (elementaryA2System (FreeAlgebra K X)).rootSet
      (2 * (8 * (CharacterMass.gap ψ)⁻¹ * Fintype.card K +
        6 * Fintype.card X + 4) + 1 : ℝ) := by
  intro E _ _ _ rho z _hz δ hδ hnear g hg
  obtain ⟨a, hga⟩ :=
    ((elementaryA2System (FreeAlgebra K X)).mem_rootSet_iff g).mp hg
  let i := a.1.1
  let k := a.1.2
  let j := a2ThirdIndex i k
  have hij : i ≠ j := (a2ThirdIndex_ne_left i k a.2).symm
  have hjk : j ≠ k := a2ThirdIndex_ne_right i k a.2
  let H : Subgroup (elementaryGroup (Fin 3) (FreeAlgebra K X)) :=
    elementaryRootSubgroup i k a.2 ⊔ elementaryRootSubgroup j k hjk
  have hprojection := norm_columnPlaneMovingProjection_le
    X K i j k hij a.2 hjk rho ψ hψ z hδ hnear
  have hgH : g ∈ H := by
    exact (show elementaryRootSubgroup i k a.2 ≤ H from le_sup_left) hga
  have hdisplacement :=
    KazhdanFixedSpace.norm_displacement_le_two_mul_norm_subgroupMovingProjection_of_mem
      rho H hgH z
  have hgap := CharacterMass.gap_pos ψ
  have hginv : (0 : ℝ) < (CharacterMass.gap ψ)⁻¹ := by positivity
  have hcardK : (0 : ℝ) ≤ Fintype.card K := by positivity
  have hcardX : (0 : ℝ) ≤ Fintype.card X := by positivity
  calc
    ‖rho g z - z‖ ≤
        2 * ‖KazhdanFixedSpace.subgroupMovingProjection rho H z‖ :=
      hdisplacement
    _ ≤ 2 * ((8 * (CharacterMass.gap ψ)⁻¹ * Fintype.card K +
        6 * Fintype.card X + 4 : ℝ) * δ) := by
      exact mul_le_mul_of_nonneg_left hprojection (by norm_num)
    _ < (2 * (8 * (CharacterMass.gap ψ)⁻¹ * Fintype.card K +
        6 * Fintype.card X + 4) + 1 : ℝ) * δ := by
      nlinarith

/-- The explicit control set is a genuine finite Kazhdan pair. -/
theorem controlSet_isKazhdanPair :
    ∃ epsilon : ℝ,
      IsKazhdanPair (elementaryGroup (Fin 3) (FreeAlgebra K X))
        (controlSet X K) epsilon := by
  obtain ⟨ψ, hψ⟩ := CharacterMass.exists_addChar_ne_one K
  have hprime : (ringChar K).Prime := CharP.char_is_prime K (ringChar K)
  obtain ⟨kappa, hkappa⟩ :=
    A2MagicHilbert.elementary_exists_rootSet_isKazhdan
      (FreeAlgebra K X) (ringChar K) hprime.pos
  have hgap := CharacterMass.gap_pos ψ
  have hginv : (0 : ℝ) < (CharacterMass.gap ψ)⁻¹ := by positivity
  have hcardK : (1 : ℝ) ≤ Fintype.card K := by
    exact_mod_cast Fintype.card_pos
  have hcardX : (0 : ℝ) ≤ Fintype.card X := by positivity
  set C : ℝ := 2 * (8 * (CharacterMass.gap ψ)⁻¹ * Fintype.card K +
    6 * Fintype.card X + 4) + 1 with hC
  have hCpos : 0 < C := by
    rw [hC]
    nlinarith
  exact ⟨kappa / (2 * C),
    IsKazhdanSubset.to_pair_of_controls hkappa hCpos
      (controlSet_controls_rootSet X K ψ hψ)⟩

/-- **Elementary rank three over the free algebra of every finite field
has Kazhdan's property `(T)`.** -/
theorem freeElementary_hasKazhdanPropertyT :
    HasKazhdanPropertyT (elementaryGroup (Fin 3) (FreeAlgebra K X)) := by
  obtain ⟨epsilon, hpair⟩ := controlSet_isKazhdanPair X K
  exact ⟨controlSet X K, epsilon, hpair⟩

end
end FiniteFieldElementaryPropertyT
end NonsoficGroupsExist
