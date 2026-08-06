import NonsoficGroupsExist.Sofic.Sofic
import Mathlib.SetTheory.Cardinal.Order

/-!
# Finite normalization of a sofic approximation

Lemma `lem:normalization` of the manuscript: a sofic approximation may be
replaced by one that assigns the identity permutation to `1` and exactly
inverse permutations to each inverse pair drawn from a prescribed finite
symmetric set, at the cost of a pointwise vanishing Hamming perturbation.

The normalized approximation itself is constructed here, not merely its error
bounds.  Three ingredients:

* `SoficApproximation.perturb` — replacing the assignment by a pointwise
  Hamming-close one preserves both defining properties, so the normalized
  assignment really is a sofic approximation on the same finite models;
* `involutionNormalize` — the restriction of a nearly involutive permutation
  to the invariant set on which it squares to the identity, extended by the
  identity, which is an exact involution differing from the original only at
  vertices where the original failed to be one;
* `halfOrbit` — one chosen representative of each pair `{g, g⁻¹}`, obtained
  from the well ordering of the ambient group.

Assembling them gives `SoficApproximation.normalize`, whose three properties
`normalize_map_one`, `normalize_map_inv` and `normalize_close` are the three
assertions of the lemma.
-/

namespace NonsoficGroupsExist

/-! ### Comparing permutations through their disagreement sets -/

theorem hammingDistance_le_of_subset (Y : FiniteModel) (p q r s : Equiv.Perm Y)
    (h : hammingDisagreement p q ⊆ hammingDisagreement r s) :
    hammingDistance Y p q ≤ hammingDistance Y r s := by
  unfold hammingDistance
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card h

namespace SoficApproximation

variable {G : Type*} [Group G]

/-! ### Perturbing an approximation -/

/-- A reassignment of permutations that is pointwise Hamming-close to a sofic
approximation, on the very same finite models. -/
def IsCloseTo (S : SoficApproximation G)
    (τ : (n : ℕ) → G → Equiv.Perm (S.model n)) : Prop :=
  ∀ (g : G) (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
    hammingDistance (S.model n) (S.map n g) (τ n g) < ε

/-- A pointwise Hamming-close reassignment of a sofic approximation is again a
sofic approximation.  Both defining properties are stable: an error of at most
`ε/4` per replaced letter changes approximate multiplicativity by at most
`3ε/4`, and asymptotic faithfulness by at most `ε/2`. -/
def perturb (S : SoficApproximation G)
    (τ : (n : ℕ) → G → Equiv.Perm (S.model n)) (hτ : S.IsCloseTo τ) :
    SoficApproximation G where
  model := S.model
  map := τ
  card_tendsToInfinity := S.card_tendsToInfinity
  asymptoticallyMultiplicative := by
    intro g h ε hε
    have hq : (0 : ℝ) < ε / 4 := by positivity
    obtain ⟨N₀, hN₀⟩ := S.asymptoticallyMultiplicative g h (ε / 4) hq
    obtain ⟨N₁, hN₁⟩ := hτ (g * h) (ε / 4) hq
    obtain ⟨N₂, hN₂⟩ := hτ g (ε / 4) hq
    obtain ⟨N₃, hN₃⟩ := hτ h (ε / 4) hq
    refine ⟨max (max N₀ N₁) (max N₂ N₃), fun n hn ↦ ?_⟩
    have h₀ := hN₀ n (le_trans (le_trans (le_max_left N₀ N₁) (le_max_left _ _)) hn)
    have h₁ := hN₁ n (le_trans (le_trans (le_max_right N₀ N₁) (le_max_left _ _)) hn)
    have h₂ := hN₂ n (le_trans (le_trans (le_max_left N₂ N₃) (le_max_right _ _)) hn)
    have h₃ := hN₃ n (le_trans (le_trans (le_max_right N₂ N₃) (le_max_right _ _)) hn)
    have hswap : hammingDistance (S.model n) (τ n (g * h)) (S.map n (g * h)) < ε / 4 := by
      rw [hammingDistance_comm]; exact h₁
    have hleft : hammingDistance (S.model n) (S.map n g * S.map n h)
        (τ n g * S.map n h) < ε / 4 := by
      rw [hammingDistance_right_invariant]; exact h₂
    have hright : hammingDistance (S.model n) (τ n g * S.map n h)
        (τ n g * τ n h) < ε / 4 := by
      rw [hammingDistance_left_invariant]; exact h₃
    have t₁ := hammingDistance_triangle (S.model n) (τ n (g * h))
      (S.map n (g * h)) (τ n g * τ n h)
    have t₂ := hammingDistance_triangle (S.model n) (S.map n (g * h))
      (S.map n g * S.map n h) (τ n g * τ n h)
    have t₃ := hammingDistance_triangle (S.model n) (S.map n g * S.map n h)
      (τ n g * S.map n h) (τ n g * τ n h)
    show hammingDistance (S.model n) (τ n (g * h)) (τ n g * τ n h) < ε
    linarith
  asymptoticallyFaithful := by
    intro g hg ε hε
    have hq : (0 : ℝ) < ε / 2 := by positivity
    obtain ⟨N₀, hN₀⟩ := S.asymptoticallyFaithful g hg (ε / 2) hq
    obtain ⟨N₁, hN₁⟩ := hτ g (ε / 2) hq
    refine ⟨max N₀ N₁, fun n hn ↦ ?_⟩
    have h₀ := hN₀ n ((le_max_left _ _).trans hn)
    have h₁ := hN₁ n ((le_max_right _ _).trans hn)
    have htri := hammingDistance_triangle (S.model n) (S.map n g) (τ n g) 1
    show 1 - ε < hammingDistance (S.model n) (τ n g) 1
    linarith

@[simp] theorem perturb_model (S : SoficApproximation G)
    (τ : (n : ℕ) → G → Equiv.Perm (S.model n)) (hτ : S.IsCloseTo τ) (n : ℕ) :
    (S.perturb τ hτ).model n = S.model n := rfl

@[simp] theorem perturb_map (S : SoficApproximation G)
    (τ : (n : ℕ) → G → Equiv.Perm (S.model n)) (hτ : S.IsCloseTo τ) (n : ℕ) (g : G) :
    (S.perturb τ hτ).map n g = τ n g := rfl

end SoficApproximation

/-! ### Exact involutions from nearly involutive permutations -/

section Involution

variable {Y : Type*} [DecidableEq Y]

/-- Retracting a permutation to the set where it squares to the identity gives
an involution: that set is invariant, and off it nothing moves. -/
theorem involutionNormalize_involutive (p : Equiv.Perm Y) :
    Function.Involutive (fun y ↦ if p (p y) = y then p y else y) := by
  intro y
  by_cases h : p (p y) = y
  · simp only [if_pos h, if_pos (congrArg p h)]
    exact h
  · simp only [if_neg h]

/-- The restriction of `p` to the invariant set where it squares to the
identity, extended by the identity elsewhere. -/
def involutionNormalize (p : Equiv.Perm Y) : Equiv.Perm Y :=
  Function.Involutive.toPerm _ (involutionNormalize_involutive p)

@[simp] theorem involutionNormalize_apply (p : Equiv.Perm Y) (y : Y) :
    involutionNormalize p y = if p (p y) = y then p y else y := rfl

theorem involutionNormalize_mul_self (p : Equiv.Perm Y) :
    involutionNormalize p * involutionNormalize p = 1 := by
  ext y
  exact involutionNormalize_involutive p y

theorem involutionNormalize_inv (p : Equiv.Perm Y) :
    (involutionNormalize p)⁻¹ = involutionNormalize p :=
  inv_eq_of_mul_eq_one_left (involutionNormalize_mul_self p)

theorem involutionNormalize_eq_of_sq (p : Equiv.Perm Y) {y : Y}
    (h : p (p y) = y) : involutionNormalize p y = p y := by
  simp [h]

end Involution

/-! ### One representative from each inverse pair -/

section HalfOrbit

variable {G : Type*} [Group G]

open Classical in
/-- One chosen element of each pair `{g, g⁻¹}`, taken from the well ordering of
`G`. -/
noncomputable def halfOrbit (g : G) : G :=
  if WellOrderingRel g g⁻¹ then g else g⁻¹

theorem halfOrbit_mem (g : G) : halfOrbit g = g ∨ halfOrbit g = g⁻¹ := by
  classical
  unfold halfOrbit
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The choice is constant on each inverse pair. -/
theorem halfOrbit_inv (g : G) : halfOrbit g⁻¹ = halfOrbit g := by
  classical
  rcases trichotomous_of (WellOrderingRel (α := G)) g g⁻¹ with h | h | h
  · unfold halfOrbit
    rw [if_pos h, inv_inv, if_neg (asymm_of _ h)]
  · exact congrArg halfOrbit h.symm
  · unfold halfOrbit
    rw [if_neg (asymm_of _ h), inv_inv, if_pos h]

end HalfOrbit

/-! ### The normalized approximation -/

namespace SoficApproximation

variable {G : Type*} [Group G] (S : SoficApproximation G)

open Classical in
/-- The permutation assigned to `g` by the normalized approximation: the
identity at `1`; the exact involution `involutionNormalize` at an involution of
the test set; the originally assigned permutation, or the inverse of the one
assigned to `g⁻¹`, according to which of `g` and `g⁻¹` is the chosen half-orbit
representative; and the original assignment off the test set. -/
noncomputable def normalizedMap (F : Finset G) (n : ℕ) (g : G) :
    Equiv.Perm (S.model n) :=
  if g = 1 then 1
  else if g ∉ F then S.map n g
  else if g * g = 1 then involutionNormalize (S.map n g)
  else if halfOrbit g = g then S.map n g
  else (S.map n g⁻¹)⁻¹

theorem normalizedMap_one (F : Finset G) (n : ℕ) :
    S.normalizedMap F n 1 = 1 := by
  rw [normalizedMap, if_pos rfl]

theorem normalizedMap_of_not_mem (F : Finset G) (n : ℕ) {g : G}
    (hg : g ≠ 1) (hF : g ∉ F) : S.normalizedMap F n g = S.map n g := by
  rw [normalizedMap, if_neg hg, if_pos hF]

theorem normalizedMap_of_involution (F : Finset G) (n : ℕ) {g : G}
    (hg : g ≠ 1) (hF : g ∈ F) (hsq : g * g = 1) :
    S.normalizedMap F n g = involutionNormalize (S.map n g) := by
  rw [normalizedMap, if_neg hg, if_neg (not_not_intro hF), if_pos hsq]

theorem normalizedMap_of_chosen (F : Finset G) (n : ℕ) {g : G}
    (hg : g ≠ 1) (hF : g ∈ F) (hsq : g * g ≠ 1) (hc : halfOrbit g = g) :
    S.normalizedMap F n g = S.map n g := by
  rw [normalizedMap, if_neg hg, if_neg (not_not_intro hF), if_neg hsq, if_pos hc]

theorem normalizedMap_of_not_chosen (F : Finset G) (n : ℕ) {g : G}
    (hg : g ≠ 1) (hF : g ∈ F) (hsq : g * g ≠ 1) (hc : halfOrbit g ≠ g) :
    S.normalizedMap F n g = (S.map n g⁻¹)⁻¹ := by
  rw [normalizedMap, if_neg hg, if_neg (not_not_intro hF), if_neg hsq, if_neg hc]

/-! #### The two error estimates feeding the construction -/

/-- The permutation assigned to `g⁻¹` is asymptotically the inverse of the one
assigned to `g`. -/
theorem inv_close (g : G) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N,
      hammingDistance (S.model n) (S.map n g) ((S.map n g⁻¹)⁻¹) < ε := by
  have hq : (0 : ℝ) < ε / 2 := by positivity
  obtain ⟨N₀, hN₀⟩ := S.asymptoticallyMultiplicative g⁻¹ g (ε / 2) hq
  obtain ⟨N₁, hN₁⟩ := S.map_one_close (ε / 2) hq
  refine ⟨max N₀ N₁, fun n hn ↦ ?_⟩
  have h₀ := hN₀ n ((le_max_left _ _).trans hn)
  have h₁ := hN₁ n ((le_max_right _ _).trans hn)
  rw [inv_mul_cancel] at h₀
  have hshift : hammingDistance (S.model n) (S.map n g) ((S.map n g⁻¹)⁻¹) =
      hammingDistance (S.model n) (S.map n g⁻¹ * S.map n g) 1 := by
    rw [← hammingDistance_left_invariant (S.model n) (S.map n g⁻¹)
      (S.map n g) ((S.map n g⁻¹)⁻¹), mul_inv_cancel]
  have hcomm := hammingDistance_comm (S.model n) (S.map n g⁻¹ * S.map n g) (S.map n 1)
  have htri := hammingDistance_triangle (S.model n)
    (S.map n g⁻¹ * S.map n g) (S.map n 1) 1
  rw [hshift]
  linarith

/-- The permutation assigned to an involution asymptotically squares to the
identity. -/
theorem sq_close {g : G} (hsq : g * g = 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N,
      hammingDistance (S.model n) (S.map n g * S.map n g) 1 < ε := by
  have hq : (0 : ℝ) < ε / 2 := by positivity
  obtain ⟨N₀, hN₀⟩ := S.asymptoticallyMultiplicative g g (ε / 2) hq
  obtain ⟨N₁, hN₁⟩ := S.map_one_close (ε / 2) hq
  refine ⟨max N₀ N₁, fun n hn ↦ ?_⟩
  have h₀ := hN₀ n ((le_max_left _ _).trans hn)
  have h₁ := hN₁ n ((le_max_right _ _).trans hn)
  rw [hsq] at h₀
  have hcomm := hammingDistance_comm (S.model n) (S.map n g * S.map n g) (S.map n 1)
  have htri := hammingDistance_triangle (S.model n)
    (S.map n g * S.map n g) (S.map n 1) 1
  linarith

/-- Every replaced letter stays Hamming-close to the original one. -/
theorem normalizedMap_close (F : Finset G) : S.IsCloseTo (S.normalizedMap F) := by
  classical
  intro g ε hε
  by_cases hg : g = 1
  · subst hg
    obtain ⟨N, hN⟩ := S.map_one_close ε hε
    exact ⟨N, fun n hn ↦ by rw [S.normalizedMap_one F n]; exact hN n hn⟩
  by_cases hF : g ∈ F
  · by_cases hsq : g * g = 1
    · obtain ⟨N, hN⟩ := S.sq_close hsq ε hε
      refine ⟨N, fun n hn ↦ ?_⟩
      rw [S.normalizedMap_of_involution F n hg hF hsq]
      refine lt_of_le_of_lt ?_ (hN n hn)
      apply hammingDistance_le_of_subset
      intro y hy
      simp only [mem_hammingDisagreement] at hy ⊢
      intro hfix
      exact hy (involutionNormalize_eq_of_sq _ (by simpa using hfix)).symm
    · by_cases hc : halfOrbit g = g
      · exact ⟨0, fun n _ ↦ by
          rw [S.normalizedMap_of_chosen F n hg hF hsq hc, hammingDistance_self]
          exact hε⟩
      · obtain ⟨N, hN⟩ := S.inv_close g ε hε
        exact ⟨N, fun n hn ↦ by
          rw [S.normalizedMap_of_not_chosen F n hg hF hsq hc]; exact hN n hn⟩
  · exact ⟨0, fun n _ ↦ by
      rw [S.normalizedMap_of_not_mem F n hg hF, hammingDistance_self]
      exact hε⟩

/-- **Lemma `lem:normalization`**: the normalized sofic approximation.  It has
the same finite models as `S`, is pointwise Hamming-close to it, assigns the
identity permutation to `1`, and assigns exactly inverse permutations to each
inverse pair of the finite symmetric set `F`. -/
noncomputable def normalize (F : Finset G) : SoficApproximation G :=
  S.perturb (S.normalizedMap F) (S.normalizedMap_close F)

@[simp] theorem normalize_model (F : Finset G) (n : ℕ) :
    (S.normalize F).model n = S.model n := rfl

@[simp] theorem normalize_map (F : Finset G) (n : ℕ) (g : G) :
    (S.normalize F).map n g = S.normalizedMap F n g := rfl

/-- The normalized approximation assigns the identity permutation to `1`. -/
theorem normalize_map_one (F : Finset G) (n : ℕ) :
    (S.normalize F).map n 1 = 1 := S.normalizedMap_one F n

/-- On a symmetric test set the normalized approximation assigns exactly
inverse permutations to inverse elements. -/
theorem normalize_map_inv (F : Finset G) (hF : ∀ g ∈ F, g⁻¹ ∈ F)
    (n : ℕ) {g : G} (hg : g ∈ F) :
    (S.normalize F).map n g⁻¹ = ((S.normalize F).map n g)⁻¹ := by
  show S.normalizedMap F n g⁻¹ = (S.normalizedMap F n g)⁻¹
  by_cases h1 : g = 1
  · subst h1
    rw [inv_one, S.normalizedMap_one F n, inv_one]
  have hinv1 : g⁻¹ ≠ 1 := fun h ↦ h1 (inv_eq_one.mp h)
  have hFinv : g⁻¹ ∈ F := hF g hg
  by_cases hsq : g * g = 1
  · have hgg : g⁻¹ = g := by
      rw [← mul_one g⁻¹, ← hsq, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [hgg, S.normalizedMap_of_involution F n h1 hg hsq, involutionNormalize_inv]
  · have hgne : g ≠ g⁻¹ := by
      intro h
      apply hsq
      calc g * g = g * g⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel g
    have hsqinv : g⁻¹ * g⁻¹ ≠ 1 := by
      intro h
      apply hgne
      have hg2 : g⁻¹ = g := by
        have hmul := congrArg (fun z ↦ z * g) h
        simpa [mul_assoc] using hmul
      exact hg2.symm
    rcases halfOrbit_mem g with hc | hc
    · have hcinv : halfOrbit g⁻¹ ≠ g⁻¹ := by
        rw [halfOrbit_inv, hc]
        exact hgne
      rw [S.normalizedMap_of_not_chosen F n hinv1 hFinv hsqinv hcinv,
        S.normalizedMap_of_chosen F n h1 hg hsq hc, inv_inv]
    · have hcg : halfOrbit g ≠ g := by
        rw [hc]
        exact fun h ↦ hgne h.symm
      have hcinv : halfOrbit g⁻¹ = g⁻¹ := by rw [halfOrbit_inv, hc]
      rw [S.normalizedMap_of_chosen F n hinv1 hFinv hsqinv hcinv,
        S.normalizedMap_of_not_chosen F n h1 hg hsq hcg, inv_inv]

/-- The normalized approximation is pointwise Hamming-close to the original
one. -/
theorem normalize_close (F : Finset G) (g : G) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N,
      hammingDistance (S.model n) (S.map n g) ((S.normalize F).map n g) < ε :=
  S.normalizedMap_close F g ε hε

/-- Lemma `lem:normalization` in existential form: a sofic approximation on the
same finite models, pointwise Hamming-close to `S`, exactly unital and exactly
inverse-compatible on `F`. -/
theorem exists_normalization (F : Finset G) (hF : ∀ g ∈ F, g⁻¹ ∈ F) :
    ∃ S' : SoficApproximation G, ∃ _ : ∀ n, S'.model n = S.model n,
      (∀ n, S'.map n 1 = 1) ∧
      (∀ n, ∀ g ∈ F, S'.map n g⁻¹ = (S'.map n g)⁻¹) ∧
      ∀ (g : G) (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
        hammingDistance (S.model n) (S.map n g) ((S.normalize F).map n g) < ε :=
  ⟨S.normalize F, fun _ ↦ rfl, S.normalize_map_one F,
    fun n _ hg ↦ S.normalize_map_inv F hF n hg, S.normalize_close F⟩

end SoficApproximation

end NonsoficGroupsExist
