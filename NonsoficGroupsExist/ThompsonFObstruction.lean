import NonsoficGroupsExist.LEF
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Group

/-!
# The Thompson-`F` two-relator obstruction to LEF

The two relations in this file are the standard two-generator relators for
Thompson's group `F`.  This file uses only the relators themselves; it does not
identify any concrete group with `F`, and it does not use an injectivity claim
for a map out of the presented group.

If two elements `a, b` of a group satisfy the two Thompson-`F` relations

  `[a b⁻¹, a⁻¹ b a] = 1`,  `[a b⁻¹, a⁻² b a²] = 1`

and do not commute, then the group is not LEF.

The reason is that in a *finite* group these two relations force `[a,b] = 1`:
setting `cₙ = a⁻ⁿ b aⁿ`, the relations propagate to `b⁻¹ cₙ b = cₙ₊₁` for all
`n ≥ 1`, and periodicity of `n ↦ aⁿ` closes the induction.
-/

namespace NonsoficGroupsExist
namespace ThompsonFObstruction

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- The conjugates `cₙ = a⁻ⁿ b aⁿ`. -/
def conjugateTerm (a b : G) (n : ℕ) : G := (a ^ n)⁻¹ * b * a ^ n

theorem conjugateTerm_succ (a b : G) (n : ℕ) :
    conjugateTerm a b (n + 1) = a⁻¹ * conjugateTerm a b n * a := by
  simp only [conjugateTerm, pow_succ, mul_inv_rev]
  group

theorem conjugation_shift (a u v w : G) (h : u⁻¹ * v * u = w) :
    (a⁻¹ * u * a)⁻¹ * (a⁻¹ * v * a) * (a⁻¹ * u * a) = a⁻¹ * w * a := by
  calc
    (a⁻¹ * u * a)⁻¹ * (a⁻¹ * v * a) * (a⁻¹ * u * a) =
        a⁻¹ * (u⁻¹ * v * u) * a := by group
    _ = a⁻¹ * w * a := by rw [h]

theorem conjugacy_relation_of_commute (a b : G) (n : ℕ)
    (h : Commute (a * b⁻¹) (conjugateTerm a b n)) :
    b⁻¹ * conjugateTerm a b n * b = conjugateTerm a b (n + 1) := by
  rw [conjugateTerm_succ]
  calc
    b⁻¹ * conjugateTerm a b n * b =
        a⁻¹ * ((a * b⁻¹) * conjugateTerm a b n) * b := by group
    _ = a⁻¹ * (conjugateTerm a b n * (a * b⁻¹)) * b := by rw [h.eq]
    _ = a⁻¹ * conjugateTerm a b n * a := by group

theorem conjugacy_relation_shift (a b u : G) (n : ℕ)
    (h : u⁻¹ * conjugateTerm a b n * u = conjugateTerm a b (n + 1)) :
    (a⁻¹ * u * a)⁻¹ * conjugateTerm a b (n + 1) * (a⁻¹ * u * a) =
      conjugateTerm a b (n + 2) := by
  rw [conjugateTerm_succ a b n, conjugateTerm_succ a b (n + 1)]
  exact conjugation_shift a u (conjugateTerm a b n) (conjugateTerm a b (n + 1)) h

theorem conjugacy_relation_step (a b : G) (n : ℕ)
    (hfirst : b⁻¹ * conjugateTerm a b 1 * b = conjugateTerm a b 2)
    (hprevious : b⁻¹ * conjugateTerm a b n * b = conjugateTerm a b (n + 1))
    (hcurrent : b⁻¹ * conjugateTerm a b (n + 1) * b = conjugateTerm a b (n + 2)) :
    b⁻¹ * conjugateTerm a b (n + 2) * b = conjugateTerm a b (n + 3) := by
  have hone : conjugateTerm a b 1 = a⁻¹ * b * a := by
    simp [conjugateTerm]
  have hshift :
      (conjugateTerm a b 1)⁻¹ * conjugateTerm a b (n + 1) * conjugateTerm a b 1 =
        conjugateTerm a b (n + 2) := by
    rw [hone]
    exact conjugacy_relation_shift a b b n hprevious
  have hdouble :
      (conjugateTerm a b 2)⁻¹ * conjugateTerm a b (n + 2) * conjugateTerm a b 2 =
        conjugateTerm a b (n + 3) := by
    rw [conjugateTerm_succ a b 1]
    exact conjugacy_relation_shift a b (conjugateTerm a b 1) (n + 1) hshift
  calc
    b⁻¹ * conjugateTerm a b (n + 2) * b =
        (b⁻¹ * conjugateTerm a b 1 * b)⁻¹ *
          (b⁻¹ * conjugateTerm a b (n + 1) * b) *
          (b⁻¹ * conjugateTerm a b 1 * b) := by
      rw [← hshift]; group
    _ = (conjugateTerm a b 2)⁻¹ * conjugateTerm a b (n + 2) * conjugateTerm a b 2 := by
      rw [hfirst, hcurrent]
    _ = conjugateTerm a b (n + 3) := hdouble

theorem conjugacy_relation_all (a b : G)
    (hfirst : b⁻¹ * conjugateTerm a b 1 * b = conjugateTerm a b 2)
    (hsecond : b⁻¹ * conjugateTerm a b 2 * b = conjugateTerm a b 3) (n : ℕ) :
    b⁻¹ * conjugateTerm a b (n + 1) * b = conjugateTerm a b (n + 2) := by
  induction n using Nat.twoStepInduction with
  | zero => exact hfirst
  | one => exact hsecond
  | more n hprevious hcurrent =>
      simpa [Nat.add_assoc] using
        conjugacy_relation_step a b (n + 1) hfirst hprevious hcurrent

/-- In a finite group the two standard Thompson-`F` relations force
commutation. -/
theorem finite_commute_of_two_relations {G : Type*} [Group G] [Finite G] (a b : G)
    (hfirst : Commute (a * b⁻¹) (a⁻¹ * b * a))
    (hsecond : Commute (a * b⁻¹) ((a ^ 2)⁻¹ * b * a ^ 2)) :
    Commute a b := by
  have hfirst' : b⁻¹ * conjugateTerm a b 1 * b = conjugateTerm a b 2 := by
    apply conjugacy_relation_of_commute a b 1
    simpa [conjugateTerm] using hfirst
  have hsecond' : b⁻¹ * conjugateTerm a b 2 * b = conjugateTerm a b 3 := by
    apply conjugacy_relation_of_commute a b 2
    simpa [conjugateTerm] using hsecond
  have hpositive : 0 < orderOf a := orderOf_pos a
  have hindex : orderOf a - 1 + 1 = orderOf a := Nat.sub_add_cancel hpositive
  have hnext : orderOf a - 1 + 2 = orderOf a + 1 := by omega
  have hperiod : conjugateTerm a b (orderOf a) = b := by
    simp [conjugateTerm, pow_orderOf_eq_one]
  have hconjugate : conjugateTerm a b (orderOf a + 1) = a⁻¹ * b * a := by
    rw [conjugateTerm_succ, hperiod]
  have hrelation := conjugacy_relation_all a b hfirst' hsecond' (orderOf a - 1)
  rw [hindex, hnext, hperiod, hconjugate] at hrelation
  have heq : b = a⁻¹ * b * a := by simpa using hrelation
  change a * b = b * a
  calc
    a * b = a * (a⁻¹ * b * a) := congrArg (fun z : G ↦ a * z) heq
    _ = b * a := by group

/-- The first standard Thompson-`F` relator, as an element of the free group on two
generators. -/
def relator₁ : FreeGroup (Fin 2) :=
  ⁅FreeGroup.of (0 : Fin 2) * (FreeGroup.of (1 : Fin 2))⁻¹,
    (FreeGroup.of (0 : Fin 2))⁻¹ * FreeGroup.of (1 : Fin 2) *
      FreeGroup.of (0 : Fin 2)⁆

/-- The second standard Thompson-`F` relator. -/
def relator₂ : FreeGroup (Fin 2) :=
  ⁅FreeGroup.of (0 : Fin 2) * (FreeGroup.of (1 : Fin 2))⁻¹,
    ((FreeGroup.of (0 : Fin 2)) ^ 2)⁻¹ * FreeGroup.of (1 : Fin 2) *
      (FreeGroup.of (0 : Fin 2)) ^ 2⁆

/-- The two-relator group underlying the obstruction. These are the standard
two-generator relators for Thompson's group `F`; no identification theorem is
needed by the non-LEF argument. -/
noncomputable abbrev Presented :=
  PresentedGroup ({relator₁, relator₂} : Set (FreeGroup (Fin 2)))

/-- The first distinguished generator of the two-relator presented group. -/
noncomputable def presentedA : Presented :=
  PresentedGroup.of (0 : Fin 2)

/-- The second distinguished generator of the two-relator presented group. -/
noncomputable def presentedB : Presented :=
  PresentedGroup.of (1 : Fin 2)

/-- The commutator of the two generators. -/
def generatorCommutator : FreeGroup (Fin 2) :=
  ⁅FreeGroup.of (0 : Fin 2), FreeGroup.of (1 : Fin 2)⁆

/-- Every finite image satisfying the two standard Thompson-`F` relators kills
the generator commutator. This is the finite-residual statement used by the
LEF obstruction, separated from the local-embedding bookkeeping. -/
theorem finite_image_generatorCommutator_eq_one
    {H : Type*} [Group H] [Finite H] (f : FreeGroup (Fin 2) →* H)
    (h₁ : f relator₁ = 1) (h₂ : f relator₂ = 1) :
    f generatorCommutator = 1 := by
  let a := f (FreeGroup.of (0 : Fin 2))
  let b := f (FreeGroup.of (1 : Fin 2))
  have hr₁ : Commute (a * b⁻¹) (a⁻¹ * b * a) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa [a, b, relator₁] using h₁
  have hr₂ : Commute (a * b⁻¹) ((a ^ 2)⁻¹ * b * a ^ 2) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa [a, b, relator₂] using h₂
  simpa [a, b, generatorCommutator] using
    (finite_commute_of_two_relations a b hr₁ hr₂).commutator_eq

/-- **Higman-free non-LEF criterion.**  A group containing two noncommuting
elements satisfying the two standard Thompson-`F` relations is not LEF. -/
theorem not_isLEF_of_two_relations {G : Type*} [Group G] (a b : G)
    (h₁ : Commute (a * b⁻¹) (a⁻¹ * b * a))
    (h₂ : Commute (a * b⁻¹) ((a ^ 2)⁻¹ * b * a ^ 2))
    (hne : ¬ Commute a b) : ¬ IsLEF G := by
  classical
  intro hlef
  set φ : FreeGroup (Fin 2) →* G := FreeGroup.lift ![a, b] with hφ
  set tracked : Finset (FreeGroup (Fin 2)) :=
    {relator₁, relator₂, generatorCommutator} with htracked
  have hcontrols : ∀ q : FreeGroup (Fin 2), ∃ s : Finset G,
      ∀ (H : Type) [Group H] (f : G → H), LocalMultiplicativeOn s f →
        FreeGroup.lift (fun i ↦ f (φ (FreeGroup.of i))) q = f (φ q) :=
    fun q ↦ exists_local_word_control φ q
  choose controls hcontrolspec using hcontrols
  set support : Finset G :=
    insert 1 (insert (φ generatorCommutator) (tracked.biUnion controls)) with hsupport
  obtain ⟨n, f, hinj, hlocal⟩ := hlef support
  set ψ : FreeGroup (Fin 2) →* Equiv.Perm (Fin n) :=
    FreeGroup.lift (fun i ↦ f (φ (FreeGroup.of i))) with hψ
  have hword : ∀ q ∈ tracked, ψ q = f (φ q) := by
    intro q hq
    apply hcontrolspec q (Equiv.Perm (Fin n)) f
    apply hlocal.mono
    intro z hz
    simp only [hsupport, Finset.mem_insert, Finset.mem_biUnion]
    exact Or.inr (Or.inr ⟨q, hq, hz⟩)
  have hφ₁ : φ relator₁ = 1 := by
    simpa [hφ, relator₁] using h₁.commutator_eq
  have hφ₂ : φ relator₂ = 1 := by
    simpa [hφ, relator₂] using h₂.commutator_eq
  have hψ₁ : ψ relator₁ = 1 := by
    rw [hword relator₁ (by simp [htracked]), hφ₁, hlocal.map_one]
  have hψ₂ : ψ relator₂ = 1 := by
    rw [hword relator₂ (by simp [htracked]), hφ₂, hlocal.map_one]
  have hf₁ : Commute (f a * (f b)⁻¹) ((f a)⁻¹ * f b * f a) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa [hψ, hφ, relator₁] using hψ₁
  have hf₂ : Commute (f a * (f b)⁻¹) (((f a) ^ 2)⁻¹ * f b * (f a) ^ 2) := by
    apply commutatorElement_eq_one_iff_commute.mp
    simpa [hψ, hφ, relator₂] using hψ₂
  have hψw : ψ generatorCommutator = 1 := by
    simpa [hψ, hφ, generatorCommutator] using
      (finite_commute_of_two_relations (f a) (f b) hf₁ hf₂).commutator_eq
  have hφw : φ generatorCommutator ≠ 1 := by
    intro hz
    apply hne
    apply commutatorElement_eq_one_iff_commute.mp
    simpa [hφ, generatorCommutator] using hz
  apply hφw
  apply hinj
  · simp [hsupport]
  · simp [hsupport]
  calc
    f (φ generatorCommutator) = ψ generatorCommutator :=
      (hword generatorCommutator (by simp [htracked])).symm
    _ = 1 := hψw
    _ = f 1 := hlocal.map_one.symm

end ThompsonFObstruction
end NonsoficGroupsExist
