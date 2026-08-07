import NonsoficGroupsExist.Sofic.Sofic
import NonsoficGroupsExist.Sofic.SoficPositiveControl
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.Pi

/-!
# Amplification: the separation constant in `IsSofic` is not a convention

`IsSofic` requires distinct elements of the test set to be separated to within
`1 - ε`, with the same `ε` that bounds the multiplicative error.  The textbook
alternative fixes the separation at some constant `δ > 0` -- typically `1/4`,
or `1/2` -- and lets only the multiplicative error shrink.  The two are
equivalent, so `¬ IsSofic` refutes every one of these conventions at once and
not merely the sharp one.

The mechanism is the tensor power.  `powerPerm k p` acts on `Fin k → Y`
coordinatewise by `p`; two such powers disagree at a tuple exactly when their
factors disagree at some coordinate, so the agreement set is a full product and

  `hammingDistance (powerPerm k p) (powerPerm k q) = 1 - (1 - hammingDistance p q) ^ k`

(`hammingDistance_powerPerm`).  Passing to a power drives a fixed separation
`δ` up to `1 - (1 - δ) ^ k`, which beats any prescribed `1 - ε` once `k` is
large, while it inflates a multiplicative error `d` only to
`1 - (1 - d) ^ k ≤ k * d`, which is repaired by asking the weak hypothesis for
accuracy `ε / k` in the first place.  The exponent depends on `δ` and `ε`
alone, so the argument is uniform in the test set.

Main results:

* `hammingDistance_powerPerm` -- the exact power law for the distance.
* `isSofic_of_isSoficWeak` -- a fixed positive separation suffices.
* `isSofic_iff_weak` -- the two definitions agree, for every `δ ∈ (0, 1)`.
* `isSofic_iff_weakLocal` -- and with no side condition at all once `δ` is
  allowed to depend on the test set, which is the form
  `Sofic.SoficUltraproduct` needs.

Nothing in the proof of the main results depends on this module; it is here to
close the last gap between the formalized `IsSofic` and the conventions in the
literature.
-/

namespace NonsoficGroupsExist

open Finset

/-! ## The tensor power of a permutation -/

section PowerPerm

variable {Y : Type*}

/-- `k` disjoint coordinates, each carrying the same permutation. -/
def powerPerm (k : ℕ) (p : Equiv.Perm Y) : Equiv.Perm (Fin k → Y) :=
  Equiv.piCongrRight fun _ ↦ p

@[simp] theorem powerPerm_apply (k : ℕ) (p : Equiv.Perm Y) (f : Fin k → Y) (i : Fin k) :
    powerPerm k p f i = p (f i) := rfl

/-- Taking powers is a homomorphism: the coordinates do not interact. -/
theorem powerPerm_mul (k : ℕ) (p q : Equiv.Perm Y) :
    powerPerm k (p * q) = powerPerm k p * powerPerm k q := by
  ext f i
  simp [powerPerm]

end PowerPerm

section PowerModel

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- Two powers disagree at a tuple exactly when their factors disagree at some
coordinate, so the agreement set is the full product of agreement sets. -/
theorem hammingDisagreement_powerPerm (k : ℕ) (p q : Equiv.Perm Y) :
    hammingDisagreement (powerPerm k p) (powerPerm k q) =
      (Fintype.piFinset fun _ : Fin k ↦ (hammingDisagreement p q)ᶜ)ᶜ := by
  classical
  ext f
  rw [mem_hammingDisagreement, Finset.mem_compl, Fintype.mem_piFinset]
  constructor
  · intro hne hall
    refine hne (funext fun i ↦ ?_)
    have h := hall i
    rw [Finset.mem_compl, mem_hammingDisagreement, not_not] at h
    exact h
  · intro hnall heq
    refine hnall fun i ↦ ?_
    rw [Finset.mem_compl, mem_hammingDisagreement, not_not]
    exact congrFun heq i

end PowerModel

/-- The model on `k` coordinates. -/
def powerModel (Y : FiniteModel) (k : ℕ) : FiniteModel :=
  ⟨Fin k → Y, inferInstance, inferInstance⟩

@[simp] theorem card_powerModel (Y : FiniteModel) (k : ℕ) :
    Fintype.card (powerModel Y k) = Fintype.card Y ^ k := by
  show Fintype.card (Fin k → Y) = _
  rw [Fintype.card_fun, Fintype.card_fin]

/-- **The power law.**  A tensor power turns a distance `d` into `1 - (1-d)^k`:
separation is driven towards `1`, while a small multiplicative error grows by a
factor of at most `k` (`one_sub_pow_le`). -/
theorem hammingDistance_powerPerm (Y : FiniteModel) (k : ℕ)
    (hY : 0 < Fintype.card Y) (p q : Equiv.Perm Y) :
    hammingDistance (powerModel Y k) (powerPerm k p) (powerPerm k q) =
      1 - (1 - hammingDistance Y p q) ^ k := by
  classical
  have hYR : (0 : ℝ) < Fintype.card Y := by exact_mod_cast hY
  have hle : (hammingDisagreement p q).card ≤ Fintype.card Y := Finset.card_le_univ _
  set A : Finset Y := (hammingDisagreement p q)ᶜ with hA
  have hAR : (A.card : ℝ) = (Fintype.card Y : ℝ) - (hammingDisagreement p q).card := by
    rw [hA, Finset.card_compl, Nat.cast_sub hle]
  -- the distance downstairs, written through the agreement set
  have hdist : hammingDistance Y p q = 1 - (A.card : ℝ) / Fintype.card Y := by
    rw [hammingDistance, hAR, sub_div, div_self (ne_of_gt hYR)]
    ring
  -- the distance upstairs, computed at the plain product type and transported
  -- to the bundled model by definitional equality
  have hpi : (Fintype.piFinset fun _ : Fin k ↦ A).card = A.card ^ k := by
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hpile : (Fintype.piFinset fun _ : Fin k ↦ A).card ≤ Fintype.card (Fin k → Y) :=
    Finset.card_le_univ _
  have hup : ((hammingDisagreement (powerPerm k p) (powerPerm k q)).card : ℝ)
      / (Fintype.card (Fin k → Y) : ℝ)
      = 1 - (A.card : ℝ) ^ k / (Fintype.card Y : ℝ) ^ k := by
    have hcardfun : Fintype.card (Fin k → Y) = Fintype.card Y ^ k := by
      rw [Fintype.card_fun, Fintype.card_fin]
    have hpow : (0 : ℝ) < (Fintype.card Y : ℝ) ^ k := pow_pos hYR k
    rw [hammingDisagreement_powerPerm, ← hA, Finset.card_compl, hpi,
      Nat.cast_sub (by rwa [hpi] at hpile), hcardfun]
    push_cast
    rw [sub_div, div_self (ne_of_gt hpow)]
  have hgoal : hammingDistance (powerModel Y k) (powerPerm k p) (powerPerm k q)
      = 1 - (A.card : ℝ) ^ k / (Fintype.card Y : ℝ) ^ k := hup
  rw [hgoal, hdist, sub_sub_cancel, div_pow]

/-! ## Models with a fixed separation constant -/

/-- A finite model in the textbook convention: the multiplicative error is
arbitrarily small, but the separation is only required to beat a constant `δ`
fixed in advance. -/
structure WeakSoficModel (G : Type*) [Group G] (F : Finset G) (δ ε : ℝ) where
  carrier : FiniteModel
  nonempty : 0 < Fintype.card carrier
  map : G → Equiv.Perm carrier
  multiplicative : ∀ g ∈ F, ∀ h ∈ F,
    hammingDistance carrier (map (g * h)) (map g * map h) ≤ ε
  separated : ∀ g ∈ F, ∀ h ∈ F, g ≠ h →
    δ ≤ hammingDistance carrier (map g) (map h)

/-- Soficity with the separation pinned at a constant `δ`. -/
def IsSoficWeak (G : Type*) [Group G] (δ : ℝ) : Prop :=
  ∀ (F : Finset G) (ε : ℝ), 0 < ε → Nonempty (WeakSoficModel G F δ ε)

/-- A closed weak model, so that `WeakSoficModel` is not a certificate nothing
is ever known to satisfy: the one-point model of the trivial group, exact on
both counts.  Separation is vacuous because the test set is a subsingleton. -/
def trivialWeakSoficModel (F : Finset PUnit) (δ : ℝ) : WeakSoficModel PUnit F δ 0 where
  carrier := ⟨PUnit, inferInstance, inferInstance⟩
  nonempty := by simp
  map := fun _ ↦ 1
  multiplicative := by
    intro g _ h _
    simp
  separated := by
    intro g _ h _ hne
    exact absurd (Subsingleton.elim g h) hne

/-- Bernoulli, in the form used for the multiplicative error: a distance `d` in
`[0,1]` inflates to at most `k * d` under a `k`-th power. -/
theorem one_sub_pow_le {d : ℝ} (hd1 : d ≤ 1) (k : ℕ) :
    1 - (1 - d) ^ k ≤ k * d := by
  have hbern : 1 + (k : ℝ) * (-d) ≤ (1 + -d) ^ k := one_add_mul_le_pow (by linarith) k
  have h : (1 : ℝ) + -d = 1 - d := by ring
  rw [h] at hbern
  linarith

variable {G : Type*} [Group G]

/-- **Amplification.**  A separation constant that does not shrink is enough:
the sharp definition follows by passing to a tensor power whose exponent
depends only on `δ` and the target accuracy. -/
theorem soficModel_of_weak {F : Finset G} {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (h : ∀ ε' : ℝ, 0 < ε' → Nonempty (WeakSoficModel G F δ ε')) :
    Nonempty (SoficModel G F ε) := by
  classical
  -- the exponent, fixed by `δ` and `ε` alone
  set r : ℝ := 1 - min δ 1 with hr
  have hr0 : 0 ≤ r := by
    have : min δ 1 ≤ 1 := min_le_right _ _
    simp only [hr]; linarith
  have hr1 : r < 1 := by
    have : 0 < min δ 1 := lt_min hδ one_pos
    simp only [hr]; linarith
  obtain ⟨k, hk⟩ : ∃ k : ℕ, r ^ k < ε := exists_pow_lt_of_lt_one hε hr1
  set K : ℕ := k + 1 with hK
  have hKpos : (0 : ℝ) < K := by positivity
  have hrK : r ^ K < ε := by
    calc r ^ K = r ^ k * r := by rw [hK, pow_succ]
      _ ≤ r ^ k * 1 := mul_le_mul_of_nonneg_left (le_of_lt hr1) (pow_nonneg hr0 k)
      _ = r ^ k := mul_one _
      _ < ε := hk
  -- a weak model accurate enough that its power still lands under `ε`
  obtain ⟨M⟩ := h (ε / K) (by positivity)
  have hMcard : 0 < Fintype.card M.carrier := M.nonempty
  refine ⟨{
    carrier := powerModel M.carrier K
    nonempty := ?_
    map := fun g ↦ powerPerm K (M.map g)
    multiplicative := ?_
    separated := ?_ }⟩
  · rw [card_powerModel]; exact pow_pos hMcard K
  · intro g hg h' hh'
    -- `powerPerm K a * powerPerm K b` and `powerPerm K (a * b)` are definitionally
    -- equal (structure eta for `Equiv`), so `show` crosses the bundled carrier
    show hammingDistance (powerModel M.carrier K) (powerPerm K (M.map (g * h')))
      (powerPerm K (M.map g * M.map h')) ≤ ε
    rw [hammingDistance_powerPerm M.carrier K hMcard]
    set d : ℝ := hammingDistance M.carrier (M.map (g * h')) (M.map g * M.map h')
    have hd1 : d ≤ 1 := hammingDistance_le_one _ _ _
    have hdε : d ≤ ε / K := M.multiplicative g hg h' hh'
    calc 1 - (1 - d) ^ K ≤ (K : ℝ) * d := one_sub_pow_le hd1 K
      _ ≤ (K : ℝ) * (ε / K) := mul_le_mul_of_nonneg_left hdε (le_of_lt hKpos)
      _ = ε := by field_simp
  · intro g hg h' hh' hne
    rw [hammingDistance_powerPerm M.carrier K hMcard]
    set d : ℝ := hammingDistance M.carrier (M.map g) (M.map h')
    have hd1 : d ≤ 1 := hammingDistance_le_one _ _ _
    have hdδ : δ ≤ d := M.separated g hg h' hh' hne
    have hsub0 : 0 ≤ 1 - d := by linarith
    have hsubr : 1 - d ≤ r := by
      have hmin : min δ 1 ≤ d := le_trans (min_le_left δ 1) hdδ
      simp only [hr]; linarith
    have hpow : (1 - d) ^ K ≤ r ^ K := by gcongr
    linarith [hrK]

/-- **Amplification**, in the form the hypothesis usually arrives in: `δ` may
depend on the test set.  This is what an injective homomorphism into a metric
ultraproduct supplies, since distinct elements are separated by an amount that
depends on the pair. -/
def IsSoficWeakLocal (G : Type*) [Group G] : Prop :=
  ∀ F : Finset G, ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → Nonempty (WeakSoficModel G F δ ε)

theorem isSofic_of_isSoficWeakLocal (h : IsSoficWeakLocal G) : IsSofic G := by
  intro F ε hε
  obtain ⟨δ, hδ, H⟩ := h F
  exact soficModel_of_weak hδ hε H

theorem isSofic_of_isSoficWeak {δ : ℝ} (hδ : 0 < δ) (h : IsSoficWeak G δ) :
    IsSofic G :=
  fun _ _ hε ↦ soficModel_of_weak hδ hε (fun _ hε' ↦ h _ _ hε')

/-- The sharp definition implies every weaker one. -/
theorem isSoficWeak_of_isSofic {δ : ℝ} (hδ : δ < 1) (h : IsSofic G) :
    IsSoficWeak G δ := by
  classical
  intro F ε hε
  obtain ⟨M⟩ := h F (min ε (1 - δ)) (lt_min hε (by linarith))
  refine ⟨{
    carrier := M.carrier
    nonempty := M.nonempty
    map := M.map
    multiplicative := fun g hg h' hh' ↦
      le_trans (M.multiplicative g hg h' hh') (min_le_left _ _)
    separated := ?_ }⟩
  intro g hg h' hh' hne
  have hsep := M.separated g hg h' hh' hne
  have hmin : min ε (1 - δ) ≤ 1 - δ := min_le_right _ _
  linarith

/-- **The two conventions agree.**  For every fixed separation constant in
`(0, 1)`, soficity in the textbook sense is soficity in the sense used
throughout this development. -/
theorem isSofic_iff_weak {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    IsSofic G ↔ IsSoficWeak G δ :=
  ⟨isSoficWeak_of_isSofic hδ1, isSofic_of_isSoficWeak hδ0⟩

/-- With `δ` allowed to depend on the test set, the equivalence carries no side
condition at all. -/
theorem isSofic_iff_weakLocal : IsSofic G ↔ IsSoficWeakLocal G := by
  refine ⟨fun h F ↦ ⟨1 / 2, by norm_num, fun ε hε ↦ ?_⟩, isSofic_of_isSoficWeakLocal⟩
  exact isSoficWeak_of_isSofic (by norm_num) h F ε hε

/-- The quarter-separation convention, spelled out. -/
theorem isSofic_iff_weak_quarter : IsSofic G ↔ IsSoficWeak G (1 / 4) :=
  isSofic_iff_weak (by norm_num) (by norm_num)

/-- Positive control for the test-set-local form. -/
theorem isSoficWeakLocal_of_finite (G : Type) [Group G] [Finite G] :
    IsSoficWeakLocal G :=
  isSofic_iff_weakLocal.mp (isSofic_of_finite G)

/-- Positive control, in the shape of `isSofic_of_finite`: the weak predicate is
satisfied, not merely refuted.  Without this, a theorem refuting `IsSoficWeak`
would be equally consistent with the predicate being unsatisfiable. -/
theorem isSoficWeak_of_finite (G : Type) [Group G] [Finite G] :
    IsSoficWeak G (1 / 4) :=
  isSoficWeak_of_isSofic (by norm_num) (isSofic_of_finite G)

end NonsoficGroupsExist
