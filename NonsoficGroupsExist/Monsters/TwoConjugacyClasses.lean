import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.IsPerfect
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Groups with exactly two conjugacy classes

Constructions of omnimonsters force their groups to have exactly two conjugacy
classes and then read off a long list of consequences.  The forcing is Baire
category over a relative small-cancellation space and is not formalized here;
the consequences are elementary and are.  Everything below takes
`HasTwoConjugacyClasses` as a hypothesis and derives, with no further input:

* simplicity, hence perfectness and a trivial centre;
* every element is conjugate to its inverse and to each of its nontrivial
  powers;
* every conjugation-invariant real function is constant off the identity, so
  every conjugation-invariant norm is bounded and stably zero;
* every homogeneous quasimorphism vanishes identically.

The quasimorphism argument is the only one with any content.  Homogeneous
quasimorphisms are conjugation invariant -- proved here from the defect bound
and homogeneity, with no limits, by applying the defect estimate to `xⁿ` and
using that the resulting bound is uniform in `n`.  Given that, two conjugacy
classes and the absence of 2-torsion give `q g = q (g ^ 2) = 2 q g`.

`hasTwoConjugacyClasses_perm_two` witnesses that the definition is satisfiable
at all; the group of order two is the only finite example, which is why the
sharper statements below carry an `Infinite` hypothesis rather than being
stated for every model of the definition.
-/

namespace NonsoficGroupsExist.Monsters

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- A group has exactly two conjugacy classes when it is nontrivial and any
two nonidentity elements are conjugate.  The class of the identity is the
second one. -/
def HasTwoConjugacyClasses (G : Type*) [Group G] : Prop :=
  Nontrivial G ∧ ∀ x y : G, x ≠ 1 → y ≠ 1 → IsConj x y

/-- The definition is satisfiable: the group of order two has exactly two
conjugacy classes.  Without a witness, every theorem below would be consistent
with the hypothesis being unsatisfiable. -/
theorem hasTwoConjugacyClasses_perm_two :
    HasTwoConjugacyClasses (Equiv.Perm (Fin 2)) := by
  refine ⟨inferInstance, fun x y hx hy ↦ ?_⟩
  have hxy : x = y := by
    revert hx hy
    revert x y
    decide
  exact hxy ▸ IsConj.refl x

/-! ### Conjugation-invariant functions and quasimorphisms

These definitions and the two lemmas about them are independent of the
two-conjugacy-class hypothesis; only their applications below use it. -/

/-- A real-valued function constant on conjugacy classes. -/
def IsConjInvariant (ν : G → ℝ) : Prop := ∀ x y : G, IsConj x y → ν x = ν y

/-- A quasimorphism with defect at most `D`. -/
def IsQuasimorphism (q : G → ℝ) (D : ℝ) : Prop :=
  ∀ x y : G, |q (x * y) - q x - q y| ≤ D

/-- The zero function is a quasimorphism with zero defect: the definition is
satisfiable. -/
theorem isQuasimorphism_zero :
    IsQuasimorphism (fun _ : G => (0 : ℝ)) 0 := fun _ _ => by simp

/-- Homogeneity, in the integral form that also fixes the value at the
identity and on inverses. -/
def IsHomogeneous (q : G → ℝ) : Prop := ∀ (n : ℤ) (x : G), q (x ^ n) = n * q x

/-- The zero function is homogeneous: the definition is satisfiable. -/
theorem isHomogeneous_zero : IsHomogeneous (fun _ : G => (0 : ℝ)) :=
  fun _ _ => by simp

/-- A homogeneous function vanishes at the identity. -/
theorem homogeneous_one {q : G → ℝ} (hq : IsHomogeneous q) : q 1 = 0 := by
  have h := hq 0 1
  simpa using h

/-- A homogeneous function sends inverses to negatives. -/
theorem homogeneous_inv {q : G → ℝ} (hq : IsHomogeneous q) (x : G) :
    q x⁻¹ = -q x := by
  have h := hq (-1) x
  simpa using h

/-- Conjugation moves a homogeneous quasimorphism by at most twice its
defect. -/
theorem conj_sub_le_of_quasimorphism {q : G → ℝ} {D : ℝ}
    (hq : IsQuasimorphism q D) (hh : IsHomogeneous q) (c x : G) :
    |q (c * x * c⁻¹) - q x| ≤ 2 * D := by
  have h1 : |q (c * (x * c⁻¹)) - q c - q (x * c⁻¹)| ≤ D := hq c (x * c⁻¹)
  have h2 : |q (x * c⁻¹) - q x - q c⁻¹| ≤ D := hq x c⁻¹
  have hassoc : c * x * c⁻¹ = c * (x * c⁻¹) := by group
  have hinv : q c⁻¹ = -q c := homogeneous_inv hh c
  have hsum :
      |(q (c * (x * c⁻¹)) - q c - q (x * c⁻¹)) + (q (x * c⁻¹) - q x - q c⁻¹)| ≤
        D + D := (abs_add_le _ _).trans (add_le_add h1 h2)
  have hrewrite :
      (q (c * (x * c⁻¹)) - q c - q (x * c⁻¹)) + (q (x * c⁻¹) - q x - q c⁻¹) =
        q (c * x * c⁻¹) - q x := by
    rw [hassoc, hinv]; ring
  rw [hrewrite] at hsum
  linarith [hsum]

/-- Homogeneous quasimorphisms are conjugation invariant.  The defect bound
applied to `xⁿ` gives `n |q (c x c⁻¹) - q x| ≤ 2D` for every `n`, and a bound
uniform in `n` on a multiple of a fixed real number forces that number to be
zero. -/
theorem isConjInvariant_of_quasimorphism {q : G → ℝ} {D : ℝ}
    (hq : IsQuasimorphism q D) (hh : IsHomogeneous q) : IsConjInvariant q := by
  have key : ∀ c x : G, q (c * x * c⁻¹) = q x := by
    intro c x
    have hbound : ∀ n : ℕ, (n : ℝ) * |q (c * x * c⁻¹) - q x| ≤ 2 * D := by
      intro n
      have hconj : (c * x * c⁻¹) ^ (n : ℤ) = c * x ^ (n : ℤ) * c⁻¹ := conj_zpow
      have hstep := conj_sub_le_of_quasimorphism hq hh c (x ^ (n : ℤ))
      have hexpand : q (c * x ^ (n : ℤ) * c⁻¹) - q (x ^ (n : ℤ)) =
          (n : ℝ) * (q (c * x * c⁻¹) - q x) := by
        rw [← hconj, hh (n : ℤ) (c * x * c⁻¹), hh (n : ℤ) x]
        push_cast
        ring
      rw [hexpand] at hstep
      calc (n : ℝ) * |q (c * x * c⁻¹) - q x|
          = |(n : ℝ) * (q (c * x * c⁻¹) - q x)| := by
            rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ))]
        _ ≤ 2 * D := hstep
    have habs : |q (c * x * c⁻¹) - q x| = 0 := by
      by_contra hne
      have hpos : 0 < |q (c * x * c⁻¹) - q x| :=
        lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne)
      obtain ⟨n, hn⟩ := exists_nat_gt (2 * D / |q (c * x * c⁻¹) - q x|)
      have hlt : 2 * D < (n : ℝ) * |q (c * x * c⁻¹) - q x| := by
        rw [div_lt_iff₀ hpos] at hn
        linarith
      exact absurd (hbound n) (not_le.2 hlt)
    have hzero : q (c * x * c⁻¹) - q x = 0 := abs_eq_zero.1 habs
    linarith
  intro x y hxy
  obtain ⟨c, hc⟩ := isConj_iff.1 hxy
  rw [← hc, key c x]

/-- The zero function is conjugation invariant, derived through the
quasimorphism machinery rather than by unfolding: the definition is
satisfiable, and the two witnesses above compose. -/
theorem isConjInvariant_zero : IsConjInvariant (fun _ : G => (0 : ℝ)) :=
  isConjInvariant_of_quasimorphism isQuasimorphism_zero isHomogeneous_zero

namespace HasTwoConjugacyClasses

variable (h : HasTwoConjugacyClasses G)
include h

/-- Nonidentity elements really are all conjugate; the projection is named so
the rest of the file can use it without unfolding the definition. -/
theorem isConj {x y : G} (hx : x ≠ 1) (hy : y ≠ 1) : IsConj x y := h.2 x y hx hy

theorem nontrivial : Nontrivial G := h.1

/-! ### Simplicity and its immediate companions -/

/-- **Simplicity.**  A group with exactly two conjugacy classes is simple:
a nontrivial normal subgroup contains a nonidentity element, hence -- being
closed under conjugation -- every nonidentity element. -/
theorem isSimpleGroup : IsSimpleGroup G := by
  haveI := h.nontrivial
  refine { eq_bot_or_eq_top_of_normal := fun N hN ↦ ?_ }
  by_cases hbot : N = ⊥
  · exact Or.inl hbot
  refine Or.inr (Subgroup.eq_top_iff' N |>.2 fun x ↦ ?_)
  obtain ⟨n, hnN, hn⟩ : ∃ n ∈ N, n ≠ 1 := by
    by_contra hcon
    refine hbot (Subgroup.eq_bot_iff_forall N |>.2 fun y hy ↦ ?_)
    by_contra hy1
    exact hcon ⟨y, hy, hy1⟩
  by_cases hx : x = 1
  · exact hx ▸ N.one_mem
  obtain ⟨c, hc⟩ := isConj_iff.1 (h.isConj hn hx)
  exact hc ▸ hN.conj_mem n hnN c

/-- The centre is trivial.  A central nonidentity element would be conjugate
to -- hence equal to -- every nonidentity element, leaving at most two
elements in the group. -/
theorem center_eq_bot [Infinite G] : Subgroup.center G = ⊥ := by
  refine Subgroup.eq_bot_iff_forall _ |>.2 fun z hz ↦ ?_
  by_contra hz1
  have hall : ∀ x : G, x ≠ 1 → x = z := by
    intro x hx
    obtain ⟨c, hc⟩ := isConj_iff.1 (h.isConj hz1 hx)
    have hcz : c * z = z * c := Subgroup.mem_center_iff.1 hz c
    have hcomm : c * z * c⁻¹ = z := by rw [hcz]; group
    exact hc.symm.trans hcomm
  have hsub : (Set.univ : Set G) ⊆ {1, z} := by
    intro x _
    by_cases hx : x = 1
    · exact Or.inl hx
    · exact Or.inr (hall x hx)
  have hfin : (Set.univ : Set G).Finite :=
    Set.Finite.subset ((Set.finite_singleton z).insert 1) hsub
  exact (Set.infinite_univ (α := G)) hfin

/-- An infinite group with exactly two conjugacy classes is perfect: its
commutator subgroup is normal, hence trivial or everything, and trivial would
make the group abelian and its centre everything. -/
theorem commutator_eq_top [Infinite G] : commutator G = ⊤ := by
  haveI := h.isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) inferInstance with
    hbot | htop
  · exfalso
    obtain ⟨x, hx⟩ := exists_ne (1 : G)
    have hcentral : x ∈ Subgroup.center G := by
      refine Subgroup.mem_center_iff.2 fun g ↦ ?_
      have hmem : ⁅g, x⁆ ∈ commutator G :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top x)
      have hone : ⁅g, x⁆ = 1 := Subgroup.mem_bot.1 (hbot ▸ hmem)
      exact commutatorElement_eq_one_iff_mul_comm.1 hone
    rw [h.center_eq_bot] at hcentral
    exact hx (Subgroup.mem_bot.1 hcentral)
  · exact htop

/-! ### Conjugacy of powers and inverses -/

/-- Every nonidentity element is conjugate to its inverse. -/
theorem isConj_inv {x : G} (hx : x ≠ 1) : IsConj x x⁻¹ :=
  h.isConj hx (inv_ne_one.2 hx)

/-- Every nonidentity element is conjugate to each of its nonidentity powers.
In a torsion-free group this is every nonzero power. -/
theorem isConj_zpow {x : G} {n : ℤ} (hx : x ≠ 1) (hxn : x ^ n ≠ 1) :
    IsConj x (x ^ n) := h.isConj hx hxn

/-! ### Conjugation-invariant functions -/

/-- A conjugation-invariant function takes a single value off the identity;
in particular every conjugation-invariant norm is bounded. -/
theorem conjInvariant_eq {ν : G → ℝ} (hν : IsConjInvariant ν) {x y : G}
    (hx : x ≠ 1) (hy : y ≠ 1) : ν x = ν y := hν x y (h.isConj hx hy)

/-- Every conjugation-invariant norm has vanishing stable norm: along the
powers of a fixed element of infinite order the value never changes, so
`ν (gⁿ) / n → 0`. -/
theorem tendsto_conjInvariant_div_atTop {ν : G → ℝ} (hν : IsConjInvariant ν)
    {g : G} (hg : g ≠ 1) (hpow : ∀ n : ℕ, 0 < n → g ^ n ≠ 1) :
    Filter.Tendsto (fun n : ℕ ↦ ν (g ^ n) / n) Filter.atTop (nhds 0) := by
  have hconst : ∀ n : ℕ, 0 < n → ν (g ^ n) = ν g := fun n hn ↦
    h.conjInvariant_eq hν (hpow n hn) hg
  refine Filter.Tendsto.congr' ?_ (tendsto_const_div_atTop_nhds_zero_nat (ν g))
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  rw [hconst n hn]

/-- **No homogeneous quasimorphisms.**  On a group with exactly two conjugacy
classes and no element of order two, every homogeneous quasimorphism is
identically zero: a nonidentity `g` is conjugate to `g ^ 2`, so
`q g = 2 q g`. -/
theorem homogeneousQuasimorphism_eq_zero {q : G → ℝ} {D : ℝ}
    (hq : IsQuasimorphism q D) (hh : IsHomogeneous q)
    (hsq : ∀ x : G, x ≠ 1 → x ^ (2 : ℤ) ≠ 1) (g : G) : q g = 0 := by
  by_cases hg : g = 1
  · rw [hg]; exact homogeneous_one hh
  have hinv := isConjInvariant_of_quasimorphism hq hh
  have hconj : q g = q (g ^ (2 : ℤ)) :=
    hinv g (g ^ (2 : ℤ)) (h.isConj_zpow hg (hsq g hg))
  rw [hh (2 : ℤ) g] at hconj
  push_cast at hconj
  linarith

/-! ### ICC -/

/-- **ICC.**  An infinite group with exactly two conjugacy
classes is ICC: the conjugacy class of any nonidentity element is the whole
complement of the identity, which is infinite. -/
theorem infinite_conjClass [Infinite G] {g : G} (hg : g ≠ 1) :
    {x : G | IsConj g x}.Infinite := by
  have hset : {x : G | IsConj g x} = ({1} : Set G)ᶜ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · rintro hconj rfl
      exact hg (isConj_one_left.1 hconj)
    · exact fun hx ↦ h.isConj hg hx
  rw [hset]
  exact Set.Finite.infinite_compl (Set.finite_singleton (1 : G))

end HasTwoConjugacyClasses

end NonsoficGroupsExist.Monsters
