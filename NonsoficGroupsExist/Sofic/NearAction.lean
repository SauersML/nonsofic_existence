import NonsoficGroupsExist.Sofic.SoficSequential
import Mathlib.Algebra.Group.End
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Pestov near actions and soficity

This file formalizes the near actions appearing in Theorem 5.2 and Open
Question 5.3 of Pestov's survey.  The measure is finitely additive on the full
power set.  A near action is represented by genuine permutations, with the
identity and multiplication laws required outside null sets.  This is the
standard representative-level presentation of a homomorphism into the group
of measure-preserving transformations modulo equality almost everywhere.

The first half of the Elek--Szabó characterization is proved below: a
countable sofic group admits an essentially free near action.  The action is
the disjoint union of a sequential sofic approximation and the measure is the
ultralimit of normalized counting measures on its fibres.
-/

namespace NonsoficGroupsExist

open Filter Set
open scoped Topology

universe u

/-! ## Full-power-set finitely additive probability measures -/

/-- A finitely additive probability measure defined on every subset of `X`.

The codomain is `ℝ`; nonnegativity is included explicitly.  Finite additivity
is stated for two disjoint sets, which is the form used throughout the
Elek--Szabó argument. -/
structure FullFinitelyAdditiveProbability (X : Type*) where
  measure : Set X → ℝ
  empty : measure ∅ = 0
  univ : measure Set.univ = 1
  nonnegative : ∀ A, 0 ≤ measure A
  union_of_disjoint : ∀ A B, Disjoint A B →
    measure (A ∪ B) = measure A + measure B

namespace FullFinitelyAdditiveProbability

variable {X : Type*} (m : FullFinitelyAdditiveProbability X)

instance : CoeFun (FullFinitelyAdditiveProbability X) (fun _ ↦ Set X → ℝ) :=
  ⟨FullFinitelyAdditiveProbability.measure⟩

@[simp] theorem empty_apply : m (∅ : Set X) = 0 := m.empty

@[simp] theorem univ_apply : m (Set.univ : Set X) = 1 := m.univ

theorem union_of_disjoint_apply {A B : Set X} (h : Disjoint A B) :
    m (A ∪ B) = m A + m B :=
  m.union_of_disjoint A B h

/-- Finite additivity implies monotonicity. -/
theorem mono {A B : Set X} (hAB : A ⊆ B) : m A ≤ m B := by
  have hdis : Disjoint A (B \ A) := Set.disjoint_sdiff_right
  have hunion : A ∪ (B \ A) = B := by
    rw [Set.union_sdiff_self]
    exact Set.union_eq_right.mpr hAB
  rw [← hunion, m.union_of_disjoint_apply hdis]
  exact le_add_of_nonneg_right (m.nonnegative _)

theorem le_one (A : Set X) : m A ≤ 1 := by
  simpa using m.mono (Set.subset_univ A)

theorem compl_add (A : Set X) : m Aᶜ + m A = 1 := by
  have hdis : Disjoint Aᶜ A := by
    rw [Set.disjoint_left]
    intro x hxA hxAc
    exact hxA hxAc
  have hunion : Aᶜ ∪ A = (Set.univ : Set X) := Set.compl_union_self A
  calc
    m Aᶜ + m A = m (Aᶜ ∪ A) := (m.union_of_disjoint_apply hdis).symm
    _ = m (Set.univ : Set X) := congrArg m hunion
    _ = 1 := m.univ

theorem compl_eq_one_sub (A : Set X) : m Aᶜ = 1 - m A := by
  linarith [m.compl_add A]

theorem eq_one_of_compl_eq_zero {A : Set X} (hA : m Aᶜ = 0) : m A = 1 := by
  linarith [m.compl_add A]

theorem compl_eq_zero_of_eq_one {A : Set X} (hA : m A = 1) : m Aᶜ = 0 := by
  linarith [m.compl_add A]

end FullFinitelyAdditiveProbability

/-! ## Near actions -/

/-- A measure-preserving near action represented by total permutations.

All maps are honest bijections and preserve the finitely additive measure.
The group laws hold almost everywhere, i.e. their failure sets have measure
zero.  Replacing representatives on null sets therefore does not change the
notion. -/
structure MeasurePreservingNearAction (G : Type u) [Group G] (X : Type*) where
  measure : FullFinitelyAdditiveProbability X
  act : G → Equiv.Perm X
  measure_preserving : ∀ g A, measure (act g '' A) = measure A
  identity_ae : measure {x | act 1 x ≠ x} = 0
  multiplicative_ae : ∀ g h,
    measure {x | act (g * h) x ≠ act g (act h x)} = 0

/-- An essentially free near action: each nonidentity group element has a
null fixed-point set. -/
structure EssentiallyFreeNearAction (G : Type u) [Group G] (X : Type*)
    extends MeasurePreservingNearAction G X where
  essentially_free : ∀ g, g ≠ 1 → measure {x | act g x = x} = 0

/-- Pestov's existence property.  The action space is an ordinary small type,
as in the countable disjoint-union construction used by Elek--Szabó. -/
def AdmitsEssentiallyFreeNearAction (G : Type u) [Group G] : Prop :=
  ∃ X : Type, Nonempty (EssentiallyFreeNearAction G X)

/-! ## The ultralimit measure of a sofic approximation -/

namespace SoficApproximation

variable {G : Type*} [Group G]

/-- The disjoint union of all finite carriers in a sequential approximation. -/
abbrev NearSpace (S : SoficApproximation G) := Σ n, S.model n

/-- Normalized counting density of a subset in the `n`-th fibre. -/
noncomputable def fiberFinset (S : SoficApproximation G)
    (A : Set S.NearSpace) (n : ℕ) : Finset (S.model n) := by
  classical
  exact Finset.univ.filter fun y : S.model n ↦ (⟨n, y⟩ : S.NearSpace) ∈ A

noncomputable def fiberDensity (S : SoficApproximation G)
    (A : Set S.NearSpace) (n : ℕ) : ℝ := by
  exact (S.fiberFinset A n).card / Fintype.card (S.model n)

theorem fiberDensity_nonnegative (S : SoficApproximation G)
    (A : Set S.NearSpace) (n : ℕ) : 0 ≤ S.fiberDensity A n := by
  classical
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem fiberDensity_le_one (S : SoficApproximation G)
    (A : Set S.NearSpace) (n : ℕ) : S.fiberDensity A n ≤ 1 := by
  classical
  by_cases hcard : Fintype.card (S.model n) = 0
  · simp [fiberDensity, hcard]
  · apply (div_le_one (by exact_mod_cast (Nat.pos_of_ne_zero hcard))).2
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)

/-- The fixed ultrafilter used for the near-action construction. -/
noncomputable def nearUltrafilter : Ultrafilter ℕ :=
  Ultrafilter.of Filter.cofinite

theorem nearUltrafilter_le_cofinite :
    ((nearUltrafilter : Ultrafilter ℕ) : Filter ℕ) ≤ Filter.cofinite :=
  Ultrafilter.of_le _

/-- Ultralimit of the fibre densities. -/
noncomputable def nearMean (S : SoficApproximation G) (A : Set S.NearSpace) : ℝ :=
  Filter.limUnder nearUltrafilter (S.fiberDensity A)

/-- Every fibre-density function has an ultralimit, because it takes values in
the compact interval `[0,1]`. -/
theorem tendsto_nearMean (S : SoficApproximation G) (A : Set S.NearSpace) :
    Tendsto (S.fiberDensity A) nearUltrafilter (𝓝 (S.nearMean A)) := by
  have hmem : ∀ᶠ n in nearUltrafilter, S.fiberDensity A n ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards with n
    exact ⟨S.fiberDensity_nonnegative A n, S.fiberDensity_le_one A n⟩
  obtain ⟨x, hx⟩ := isCompact_Icc.ultrafilter_le_nhds'
    (nearUltrafilter.map (S.fiberDensity A)) (Filter.mem_map.mpr hmem)
  exact tendsto_nhds_limUnder (by
    refine ⟨x, ?_⟩
    exact hx.2)

theorem nearMean_eq_of_eventuallyEq (S : SoficApproximation G)
    {A B : Set S.NearSpace}
    (h : ∀ᶠ n in nearUltrafilter, S.fiberDensity A n = S.fiberDensity B n) :
    S.nearMean A = S.nearMean B := by
  have hs : S.fiberDensity B =ᶠ[nearUltrafilter] S.fiberDensity A :=
    h.mono fun _ hn ↦ hn.symm
  exact tendsto_nhds_unique
    (S.tendsto_nearMean A)
    (Tendsto.congr' hs (S.tendsto_nearMean B))

theorem fiberDensity_empty (S : SoficApproximation G) (n : ℕ) :
    S.fiberDensity (∅ : Set S.NearSpace) n = 0 := by
  classical
  simp [fiberDensity, fiberFinset]

theorem fiberDensity_univ_of_card_pos (S : SoficApproximation G) (n : ℕ)
    (hn : 0 < Fintype.card (S.model n)) :
    S.fiberDensity (Set.univ : Set S.NearSpace) n = 1 := by
  classical
  simp [fiberDensity, fiberFinset, Nat.ne_of_gt hn]

/-- Fibre density is finitely additive before taking the ultralimit. -/
theorem fiberDensity_union_of_disjoint (S : SoficApproximation G)
    {A B : Set S.NearSpace} (hAB : Disjoint A B) (n : ℕ) :
    S.fiberDensity (A ∪ B) n = S.fiberDensity A n + S.fiberDensity B n := by
  classical
  let FA : Finset (S.model n) := S.fiberFinset A n
  let FB : Finset (S.model n) := S.fiberFinset B n
  have hdis : Disjoint FA FB := by
    rw [Finset.disjoint_left]
    intro y hyA hyB
    exact Set.disjoint_left.mp hAB
      (by simpa [FA, fiberFinset] using hyA)
      (by simpa [FB, fiberFinset] using hyB)
  have hfilter : S.fiberFinset (A ∪ B) n = FA ∪ FB := by
    ext y
    simp [fiberFinset, FA, FB]
  have hcard : (S.fiberFinset (A ∪ B) n).card =
      (S.fiberFinset A n).card + (S.fiberFinset B n).card := by
    rw [hfilter, Finset.card_union_of_disjoint hdis]
  have hcardR : ((S.fiberFinset (A ∪ B) n).card : ℝ) =
      ((S.fiberFinset A n).card : ℝ) + ((S.fiberFinset B n).card : ℝ) := by
    exact_mod_cast hcard
  simp only [fiberDensity]
  rw [hcardR]
  ring

theorem nearMean_mem_Icc (S : SoficApproximation G) (A : Set S.NearSpace) :
    S.nearMean A ∈ Set.Icc (0 : ℝ) 1 := by
  apply isClosed_Icc.mem_of_tendsto (S.tendsto_nearMean A)
  filter_upwards with n
  exact ⟨S.fiberDensity_nonnegative A n, S.fiberDensity_le_one A n⟩

/-- The full-power-set finitely additive probability obtained from normalized
counting measures along the fixed nonprincipal ultrafilter. -/
noncomputable def nearProbability (S : SoficApproximation G) :
    FullFinitelyAdditiveProbability S.NearSpace where
  measure := S.nearMean
  empty := by
    apply tendsto_nhds_unique (S.tendsto_nearMean ∅)
    apply Tendsto.congr' _
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) nearUltrafilter (𝓝 0))
    filter_upwards with n
    exact (S.fiberDensity_empty n).symm
  univ := by
    obtain ⟨N, hN⟩ := S.card_tendsToInfinity 1
    have hev : ∀ᶠ n in nearUltrafilter,
        S.fiberDensity (Set.univ : Set S.NearSpace) n = 1 :=
      Filter.Eventually.filter_mono nearUltrafilter_le_cofinite (by
        rw [Nat.cofinite_eq_atTop]
        exact Filter.eventually_atTop.mpr ⟨N, fun n hn ↦
          S.fiberDensity_univ_of_card_pos n
            (lt_of_lt_of_le Nat.zero_lt_one (hN n hn))⟩)
    apply tendsto_nhds_unique (S.tendsto_nearMean Set.univ)
    exact Tendsto.congr' (Filter.Eventually.mono hev fun _ hn ↦ hn.symm)
      tendsto_const_nhds
  nonnegative := fun A ↦ (S.nearMean_mem_Icc A).1
  union_of_disjoint := by
    intro A B hAB
    apply tendsto_nhds_unique (S.tendsto_nearMean (A ∪ B))
    have hadd := (S.tendsto_nearMean A).add (S.tendsto_nearMean B)
    apply Tendsto.congr' _ hadd
    filter_upwards with n
    exact (S.fiberDensity_union_of_disjoint hAB n).symm

/-- The coordinatewise permutation of the disjoint union associated with a
group element in a sequential sofic approximation. -/
def nearPerm (S : SoficApproximation G) (g : G) : Equiv.Perm S.NearSpace :=
  Equiv.sigmaCongrRight fun n ↦ S.map n g

@[simp] theorem nearPerm_apply (S : SoficApproximation G) (g : G)
    (x : S.NearSpace) : S.nearPerm g x = ⟨x.1, S.map x.1 g x.2⟩ := rfl

/-- Coordinatewise permutations preserve every fibre density exactly. -/
theorem fiberDensity_image_nearPerm (S : SoficApproximation G) (g : G)
    (A : Set S.NearSpace) (n : ℕ) :
    S.fiberDensity (S.nearPerm g '' A) n = S.fiberDensity A n := by
  classical
  let FA : Finset (S.model n) := S.fiberFinset A n
  let FB : Finset (S.model n) := S.fiberFinset (S.nearPerm g '' A) n
  have himage : FA.image (S.map n g) = FB := by
    ext y
    constructor
    · intro hy
      rw [Finset.mem_image] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      simp only [FB, fiberFinset, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_image]
      exact ⟨⟨n, x⟩, by simpa [FA, fiberFinset] using hx, rfl⟩
    · intro hy
      simp only [FB, fiberFinset, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_image] at hy
      obtain ⟨x, hxA, hxy⟩ := hy
      have htarget :
          S.nearPerm g ⟨n, (S.map n g)⁻¹ y⟩ = (⟨n, y⟩ : S.NearSpace) := by
        simp [nearPerm]
      have hxeq : x = (⟨n, (S.map n g)⁻¹ y⟩ : S.NearSpace) :=
        (S.nearPerm g).injective (hxy.trans htarget.symm)
      subst x
      refine Finset.mem_image.mpr ⟨(S.map n g)⁻¹ y, ?_, by simp⟩
      simpa [FA, fiberFinset] using hxA
  have hcard : FA.card = FB.card := by
    rw [← himage]
    exact (Finset.card_image_of_injective _ (S.map n g).injective).symm
  simp only [fiberDensity, FA, FB] at hcard ⊢
  rw [hcard]

theorem nearProbability_image_nearPerm (S : SoficApproximation G) (g : G)
    (A : Set S.NearSpace) :
    S.nearProbability (S.nearPerm g '' A) = S.nearProbability A := by
  apply S.nearMean_eq_of_eventuallyEq
  filter_upwards with n
  exact S.fiberDensity_image_nearPerm g A n

/-- An eventual statement at `atTop` holds along the fixed ultrafilter. -/
theorem eventuallyNear_of_eventuallyAtTop {p : ℕ → Prop}
    (h : ∀ᶠ n in Filter.atTop, p n) : ∀ᶠ n in nearUltrafilter, p n := by
  apply Filter.Eventually.filter_mono nearUltrafilter_le_cofinite
  rwa [Nat.cofinite_eq_atTop]

/-- If every positive threshold eventually bounds a fibre density, its
ultralimit is zero. -/
theorem nearMean_eq_zero_of_eventually_lt (S : SoficApproximation G)
    (A : Set S.NearSpace)
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in nearUltrafilter, S.fiberDensity A n < ε) :
    S.nearMean A = 0 := by
  have hzero : Tendsto (S.fiberDensity A) nearUltrafilter (𝓝 (0 : ℝ)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [h ε hε] with n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (S.fiberDensity_nonnegative A n)]
    exact hn
  exact tendsto_nhds_unique (S.tendsto_nearMean A) hzero

/-- The identity-law failure set of the coordinatewise maps. -/
def nearIdentityError (S : SoficApproximation G) : Set S.NearSpace :=
  {x | S.nearPerm 1 x ≠ x}

/-- The multiplication-law failure set for a pair of group elements. -/
def nearMultiplicationError (S : SoficApproximation G) (g h : G) :
    Set S.NearSpace :=
  {x | S.nearPerm (g * h) x ≠ S.nearPerm g (S.nearPerm h x)}

/-- The fixed-point set of a coordinatewise permutation. -/
def nearFixedPoints (S : SoficApproximation G) (g : G) : Set S.NearSpace :=
  {x | S.nearPerm g x = x}

theorem fiberDensity_nearIdentityError (S : SoficApproximation G) (n : ℕ) :
    S.fiberDensity S.nearIdentityError n =
      hammingDistance (S.model n) (S.map n 1) 1 := by
  classical
  simp [fiberDensity, fiberFinset, nearIdentityError, nearPerm,
    hammingDistance, hammingDisagreement]

theorem fiberDensity_nearMultiplicationError (S : SoficApproximation G)
    (g h : G) (n : ℕ) :
    S.fiberDensity (S.nearMultiplicationError g h) n =
      hammingDistance (S.model n) (S.map n (g * h))
        (S.map n g * S.map n h) := by
  classical
  simp [fiberDensity, fiberFinset, nearMultiplicationError, nearPerm,
    hammingDistance, hammingDisagreement, Equiv.Perm.mul_apply]

/-- Fixed points and moved points partition a nonempty finite fibre. -/
theorem fiberDensity_nearFixedPoints_add_hamming (S : SoficApproximation G)
    (g : G) (n : ℕ) (hn : 0 < Fintype.card (S.model n)) :
    S.fiberDensity (S.nearFixedPoints g) n +
      hammingDistance (S.model n) (S.map n g) 1 = 1 := by
  classical
  let fixed : Finset (S.model n) :=
    Finset.univ.filter fun y ↦ S.map n g y = y
  let moved : Finset (S.model n) :=
    Finset.univ.filter fun y ↦ S.map n g y ≠ y
  have hsum : fixed.card + moved.card = Fintype.card (S.model n) := by
    simpa [fixed, moved] using
      Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (S.model n)))
        (p := fun y ↦ S.map n g y = y)
  have hsumR : (fixed.card : ℝ) + (moved.card : ℝ) =
      Fintype.card (S.model n) := by
    exact_mod_cast hsum
  have hcardR : (Fintype.card (S.model n) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hn
  have hfixed : S.fiberFinset (S.nearFixedPoints g) n = fixed := by
    ext y
    simp [fiberFinset, nearFixedPoints, nearPerm, fixed]
  have hmoved : hammingDisagreement (S.map n g) 1 = moved := by
    ext y
    simp [hammingDisagreement, moved]
  rw [fiberDensity, hammingDistance, hfixed, hmoved]
  change (fixed.card : ℝ) / Fintype.card (S.model n) +
      (moved.card : ℝ) / Fintype.card (S.model n) = 1
  rw [← add_div, hsumR, div_self hcardR]

/-- A sequential sofic approximation gives an essentially free near action
on the disjoint union of its finite carriers. -/
noncomputable def toEssentiallyFreeNearAction (S : SoficApproximation G) :
    EssentiallyFreeNearAction G S.NearSpace where
  measure := S.nearProbability
  act := S.nearPerm
  measure_preserving := S.nearProbability_image_nearPerm
  identity_ae := by
    apply S.nearMean_eq_zero_of_eventually_lt S.nearIdentityError
    intro ε hε
    obtain ⟨N, hN⟩ := S.map_one_close ε hε
    apply eventuallyNear_of_eventuallyAtTop
    exact Filter.eventually_atTop.mpr ⟨N, fun n hn ↦ by
      rw [S.fiberDensity_nearIdentityError]
      exact hN n hn⟩
  multiplicative_ae := by
    intro g h
    apply S.nearMean_eq_zero_of_eventually_lt (S.nearMultiplicationError g h)
    intro ε hε
    obtain ⟨N, hN⟩ := S.asymptoticallyMultiplicative g h ε hε
    apply eventuallyNear_of_eventuallyAtTop
    exact Filter.eventually_atTop.mpr ⟨N, fun n hn ↦ by
      rw [S.fiberDensity_nearMultiplicationError]
      exact hN n hn⟩
  essentially_free := by
    intro g hg
    apply S.nearMean_eq_zero_of_eventually_lt (S.nearFixedPoints g)
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := S.asymptoticallyFaithful g hg ε hε
    obtain ⟨N₂, hN₂⟩ := S.card_tendsToInfinity 1
    apply eventuallyNear_of_eventuallyAtTop
    exact Filter.eventually_atTop.mpr ⟨max N₁ N₂, fun n hn ↦ by
      have hn₁ : N₁ ≤ n := (le_max_left _ _).trans hn
      have hn₂ : N₂ ≤ n := (le_max_right _ _).trans hn
      have hcard : 0 < Fintype.card (S.model n) :=
        lt_of_lt_of_le Nat.zero_lt_one (hN₂ n hn₂)
      have hpartition := S.fiberDensity_nearFixedPoints_add_hamming g n hcard
      have hfar := hN₁ n hn₁
      linarith⟩

end SoficApproximation

/-- **Sofic groups admit Pestov near actions.**  This direction of the
Elek--Szabó characterization is constructed from the repository's sequential
sofic approximation and contains no external assumption. -/
theorem admitsEssentiallyFreeNearAction_of_isSofic
    (G : Type*) [Group G] [Countable G] (hG : IsSofic G) :
    AdmitsEssentiallyFreeNearAction G := by
  obtain ⟨S⟩ := soficApproximation_of_isSofic hG
  exact ⟨S.NearSpace, ⟨S.toEssentiallyFreeNearAction⟩⟩

/-! ## Closed witnesses

The repository convention: every structure and Prop-valued certificate gets a
closed witness, so that none is a specification nothing satisfies.  The
trivial group acting on the one-point space with the point mass serves for
all three. -/

open scoped Classical in
/-- The point mass on the one-point space, as a finitely additive
probability measure on the full power set. -/
noncomputable def pointMassUnit : FullFinitelyAdditiveProbability Unit where
  measure A := if Unit.unit ∈ A then 1 else 0
  empty := by simp
  univ := by simp
  nonnegative A := by
    by_cases h : Unit.unit ∈ A <;> simp [h]
  union_of_disjoint A B hAB := by
    by_cases hA : Unit.unit ∈ A
    · have hB : Unit.unit ∉ B := fun hB => Set.disjoint_left.mp hAB hA hB
      simp [hA, hB]
    · by_cases hB : Unit.unit ∈ B <;> simp [hA, hB]

/-- A closed witness: the trivial group acts essentially freely on the
point. -/
noncomputable def trivialEssentiallyFreeNearAction :
    EssentiallyFreeNearAction Unit Unit where
  measure := pointMassUnit
  act _ := 1
  measure_preserving g A := by
    have himg : (1 : Equiv.Perm Unit) '' A = A := by
      simp
    rw [himg]
  identity_ae := by
    have hset : {x : Unit | (1 : Equiv.Perm Unit) x ≠ x} = ∅ := by
      ext x
      simp
    rw [hset]
    exact pointMassUnit.empty
  multiplicative_ae g h := by
    have hset : {x : Unit |
        (1 : Equiv.Perm Unit) x ≠ (1 : Equiv.Perm Unit)
          ((1 : Equiv.Perm Unit) x)} = ∅ := by
      ext x
      simp
    rw [hset]
    exact pointMassUnit.empty
  essentially_free g hg := absurd (Subsingleton.elim g 1) hg

/-- The Pestov existence property is satisfiable: a closed witness with no
propositional hypothesis. -/
theorem admitsEssentiallyFreeNearAction_trivial :
    AdmitsEssentiallyFreeNearAction Unit :=
  ⟨Unit, ⟨trivialEssentiallyFreeNearAction⟩⟩

end NonsoficGroupsExist
